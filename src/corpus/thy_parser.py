"""Isabelle/HOL theory parser -> tamperable-site registry (CipherGuard Stage 00).

Not a full Isabelle parser -- a robust segment/regex parser tuned to the corpus
in new-dataset-thy-ciphers/. It extracts the sites the tamper engine (Phase 2)
will edit, across the three structural patterns observed:

  Feistel (Simon): inline rotation literals, `and` nonlinearity, round_constant /
                   z_sequence constants, embedded `by eval` test-vector lemmas.
  ARX (Speck):     named rotation constants (alpha/beta), modular-add nonlinearity,
                   often no test-vector lemma.
  SPN (Present):   sbox / pbox tables, sbox_layer, `*_test_*` vector definitions.

It keeps every raw definition so nothing is lost; classification is a best-effort
view the tamper stage can refine. Fails loudly only on truly unparseable files
(no `theory` header / no definitions).
"""
from __future__ import annotations
import re
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any, Dict, List, Optional

from .attack_db import family_of, safe_round_margin

_DEF_KW = ("definition", "function", "fun", "abbreviation", "primrec")
_START = re.compile(r"^(definition|function|fun|abbreviation|primrec|lemma|theorem)\b")
_KEY_SCHED_HINTS = ("key_schedule", "generate_round_keys", "gen_key", "key_register",
                    "round_key", "update_key", "extract_round_key", "key_to_words")
_ROUND_HINTS = ("_f", "encrypt_round", "_round", "sbox_layer", "_g_", "round_function")


@dataclass
class Definition:
    name: str
    kind: str            # definition | function | fun | ...
    type: Optional[str]
    body: str            # RHS text after `where`

    def snippet(self, n: int = 160) -> Dict[str, Any]:
        b = " ".join(self.body.split())
        return {"name": self.name, "kind": self.kind, "type": self.type,
                "body": (b[:n] + " ...") if len(b) > n else b}


# --------------------------------------------------------------------------- split
def _segments(text: str):
    lines = text.splitlines()
    starts = [(i, _START.match(l.strip()).group(1)) for i, l in enumerate(lines)
              if _START.match(l.strip())]
    for idx, (i, kw) in enumerate(starts):
        j = starts[idx + 1][0] if idx + 1 < len(starts) else len(lines)
        yield kw, "\n".join(lines[i:j])


def _parse_def(kw: str, seg: str) -> Optional[Definition]:
    m = re.match(r"^(?:definition|function|fun|abbreviation|primrec)\s+([A-Za-z0-9_']+)",
                 seg.strip())
    if not m:
        return None
    name = m.group(1)
    tm = re.search(r'::\s*"([^"]*)"', seg) or re.search(r"::\s*([A-Za-z0-9_ ]+?)\s+where", seg)
    typ = tm.group(1).strip() if tm else None
    body = seg.split("where", 1)[1] if "where" in seg else seg
    return Definition(name=name, kind=kw, type=typ, body=body)


# --------------------------------------------------------------------------- helpers
def _int_after_eq(body: str) -> Optional[int]:
    m = re.search(r"=\s*(0x[0-9a-fA-F]+|\d+)", body)
    return int(m.group(1), 0) if m else None


def _scalar_value(body: str) -> Optional[str]:
    m = re.search(r"=\s*(0x[0-9a-fA-F]+|\(-1\)|\d+)", body)
    return m.group(1) if m else None


def _rotations_in(defn: Definition) -> List[dict]:
    """Rotation amounts as literals: generic `word_rotl 8` and cipher-specific
    wrapper call sites `<cipher>_rol x 1`. (Named amounts like Speck's alpha/beta
    are captured separately as rotation_constants.)"""
    out = []
    for op, amt in re.findall(r"word_rot([lr])\s+(\d+)", defn.body):        # word_rotl 8
        out.append({"context": defn.name, "op": f"rot{op}", "amount": int(amt), "style": "inline"})
    for op, amt in re.findall(r"_ro([lr])\s+\w+\s+(\d+)", defn.body):       # simon_32_64_rol x 1
        out.append({"context": defn.name, "op": f"ro{op}", "amount": int(amt), "style": "wrapper"})
    return out


def _nonlinear_ops_in(defn: Definition) -> Dict[str, int]:
    b = defn.body
    return {
        "and": len(re.findall(r"\band\b", b)),
        "or": len(re.findall(r"\bor\b", b)),
        "xor": len(re.findall(r"\bxor\b", b)),
        "mod_add": b.count(" + "),
        "mod_sub": b.count(" - "),
    }


# --------------------------------------------------------------------------- name -> ids
def parse_variant_name(variant: str):
    toks = variant.split("_")
    nums = []
    while toks and toks[-1].isdigit():
        nums.insert(0, int(toks.pop()))
    base = "_".join(toks).lower()
    block = nums[0] if len(nums) >= 1 else None
    key = nums[1] if len(nums) >= 2 else None
    return base, block, key


# --------------------------------------------------------------------------- main
def parse_theory(path: Path) -> Dict[str, Any]:
    text = path.read_text()
    hm = re.search(r"^\s*theory\s+([A-Za-z0-9_']+)", text, re.M)
    if not hm:
        raise ValueError(f"{path.name}: no `theory` header found")
    variant = hm.group(1)
    base, name_block, name_key = parse_variant_name(variant)

    defs: List[Definition] = []
    lemmas: List[str] = []
    for kw, seg in _segments(text):
        if kw in ("lemma", "theorem"):
            lm = re.match(r"^(?:lemma|theorem)\s+([A-Za-z0-9_']+)", seg.strip())
            if lm:
                lemmas.append(lm.group(1))
            continue
        d = _parse_def(kw, seg)
        if d:
            defs.append(d)
    if not defs:
        raise ValueError(f"{path.name}: no definitions found (unparseable)")

    by_name = {d.name: d for d in defs}

    def find_scalar(suffix: str) -> Optional[int]:
        for d in defs:
            if d.name.endswith(suffix):
                return _int_after_eq(d.body)
        return None

    block = find_scalar("_block_size") or name_block
    key = find_scalar("_key_size") or name_key
    word_size = find_scalar("_word_size")
    rounds = find_scalar("_rounds")

    # rotations + nonlinear ops (scan all defs)
    rot_amounts, nonlinear = [], {}
    for d in defs:
        rot_amounts += _rotations_in(d)
        if any(h in d.name for h in _ROUND_HINTS):
            ops = {k: v for k, v in _nonlinear_ops_in(d).items() if v}
            if ops:
                nonlinear[d.name] = ops

    # named rotation constants (ARX alpha/beta and similar)
    rot_consts = {d.name.split("_")[-1]: _int_after_eq(d.body)
                  for d in defs if d.name.endswith(("_alpha", "_beta", "_delta"))}

    # constants (non-size scalars worth tampering)
    constants = {}
    for d in defs:
        nm = d.name
        if any(h in nm for h in ("round_constant", "z_sequence", "_mask", "_rc", "constant", "_delta")):
            val = _scalar_value(d.body)
            if val is not None:
                constants[nm] = val

    # sbox / pbox tables (SPN)
    def table_of(pred) -> Optional[dict]:
        for d in defs:
            if pred(d.name):
                lm = re.search(r"=\s*(\[.*?\])", d.body, re.S)
                entries = lm.group(1) if lm else None
                n = (entries.count(",") + 1) if entries else None
                return {"name": d.name, "type": d.type, "n_entries": n}
        return None

    sbox = table_of(lambda n: n.endswith("_sbox") or (("sbox" in n) and "layer" not in n
                    and "inv" not in n and "acc" not in n))
    sbox_inv = table_of(lambda n: n.endswith("_sbox_inv"))
    pbox = table_of(lambda n: n.endswith("_pbox") or n.endswith("_permutation"))

    key_sched = [d.name for d in defs if any(h in d.name for h in _KEY_SCHED_HINTS)]

    # test vectors: `*_test_*` defs and lemmas that eval them
    tv_defs = [d.name for d in defs if "_test_" in d.name or d.name.endswith("_test")]
    tv_lemmas = [l for l in lemmas if "test" in l or "vector" in l]
    has_by_eval = "by eval" in text or "value" in text

    return {
        "variant": variant,
        "base_cipher": base,
        "family": family_of(base),
        "block_size": block,
        "key_size": key,
        "word_size": word_size,
        "rounds": rounds,
        "n_definitions": len(defs),
        "tamperable_sites": {
            "rounds": {"kind": "param", "value": rounds} if rounds is not None else None,
            "rotation_amounts": rot_amounts,
            "rotation_constants": {k: v for k, v in rot_consts.items() if v is not None},
            "nonlinear_ops": nonlinear,
            "constants": constants,
            "sbox": sbox,
            "sbox_inv": sbox_inv,
            "pbox": pbox,
            "key_schedule": key_sched,
        },
        "test_vectors": {
            "definitions": tv_defs,
            "lemmas": tv_lemmas,
            "has_eval": bool(has_by_eval),
            "count": len(tv_defs) + len(tv_lemmas),
        },
        "safe_round_margin": safe_round_margin(base, block, key) if (block and key) else None,
        "raw_definitions": [d.snippet() for d in defs],
        "source_file": path.name,
    }

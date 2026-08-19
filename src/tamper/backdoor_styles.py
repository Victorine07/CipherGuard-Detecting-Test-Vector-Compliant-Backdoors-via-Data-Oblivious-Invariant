"""Diverse T6 backdoor styles for the robustness / adaptive-adversary study (E6).

The gate showed our detector catches T6 -- but our T6 was ONE style. 
does detection survive a backdoor injected a DIFFERENT way? We implement four
structurally-distinct styles, all of which (a) preserve the test vector and (b) are
exploitable, but differ along four axes:

  axis          S1              S2              S3                 S4
  location      entry           exit            entry              entry
  trigger input plaintext       plaintext       plaintext          key
  trigger form  == literal      == literal      derived (no lit.)  == literal
  effect        leak via return leak via assign leak via return    key collapse

S4 is deliberately the odd one out: NO plaintext branch, NO key-bypass return --
a weak-key class that collapses the cipher to a keyless permutation. A detector that
merely memorized "branch-in-encrypt gating a key return" should FAIL on S4.

Each style: inject(source, ctx, rng) -> (tampered_source, meta); exploit(enc_clean,
enc_bd, block, key, meta, rng) -> bool (verifies the malicious behavior actually works).
"""
from __future__ import annotations
import ast
import random
from dataclasses import dataclass
from typing import Any, Callable, Dict, Optional, Tuple

from .injectors import _find_funcdef

Result = Tuple[Optional[str], Dict[str, Any]]


def _enc_pk(tree: ast.Module, stem: str):
    fd = _find_funcdef(tree, stem, "encrypt")
    if fd is None or len(fd.args.args) < 2:
        return None, None, None
    return fd, fd.args.args[0].arg, fd.args.args[1].arg


# --------------------------------------------------------------------------- S1
def inject_S1(source: str, ctx: Dict[str, Any], rng: random.Random) -> Result:
    tree = ast.parse(source); stem = ctx["stem"]; block = ctx["block_size"]
    fd, p, k = _enc_pk(tree, stem)
    if fd is None:
        return None, {"reason": "no encrypt(pt,key)"}
    t = min(16, block); mask, bm = (1 << t) - 1, (1 << block) - 1; trig = 0x1337 & mask
    fd.body = ast.parse(f"if ({p} & {hex(mask)}) == {hex(trig)}:\n    return {k} & {hex(bm)}\n").body + fd.body
    ast.fix_missing_locations(tree)
    return ast.unparse(tree), {"style": "S1", "trigger_mask": mask, "trigger_val": trig, "t": t}


# --------------------------------------------------------------------------- S2
def inject_S2(source: str, ctx: Dict[str, Any], rng: random.Random) -> Result:
    tree = ast.parse(source); stem = ctx["stem"]; block = ctx["block_size"]
    fd, p, k = _enc_pk(tree, stem)
    if fd is None:
        return None, {"reason": "no encrypt(pt,key)"}
    ret_idx = max((i for i, s in enumerate(fd.body) if isinstance(s, ast.Return)), default=None)
    if ret_idx is None:
        return None, {"reason": "no top-level return to wrap"}
    t = min(16, block); mask, bm = (1 << t) - 1, (1 << block) - 1; trig = 0x1337 & mask
    repl = ast.parse(
        f"__cg_ct = 0\nif ({p} & {hex(mask)}) == {hex(trig)}:\n"
        f"    __cg_ct = {k} & {hex(bm)}\nreturn __cg_ct\n").body
    repl[0].value = fd.body[ret_idx].value        # __cg_ct = <original ciphertext expr>
    fd.body[ret_idx:ret_idx + 1] = repl
    ast.fix_missing_locations(tree)
    return ast.unparse(tree), {"style": "S2", "trigger_mask": mask, "trigger_val": trig, "t": t}


# --------------------------------------------------------------------------- S3
def inject_S3(source: str, ctx: Dict[str, Any], rng: random.Random) -> Result:
    tree = ast.parse(source); stem = ctx["stem"]; block = ctx["block_size"]
    fd, p, k = _enc_pk(tree, stem)
    if fd is None:
        return None, {"reason": "no encrypt(pt,key)"}
    t = min(12, block // 2); mask, bm = (1 << t) - 1, (1 << block) - 1
    # trigger: low t bits equal the next t bits -- a DERIVED condition, no magic literal
    fd.body = ast.parse(
        f"if ({p} & {hex(mask)}) == (({p} >> {t}) & {hex(mask)}):\n"
        f"    return {k} & {hex(bm)}\n").body + fd.body
    ast.fix_missing_locations(tree)
    return ast.unparse(tree), {"style": "S3", "mask": mask, "shift": t, "t": t}


# --------------------------------------------------------------------------- S4
def inject_S4(source: str, ctx: Dict[str, Any], rng: random.Random) -> Result:
    tree = ast.parse(source); stem = ctx["stem"]; key = ctx["key_size"]
    fd, p, k = _enc_pk(tree, stem)
    if fd is None:
        return None, {"reason": "no encrypt(pt,key)"}
    w = min(16, key); weak_mask, weak_val = (1 << w) - 1, 0x0
    # weak-key class (low w key bits == 0) collapses the key to 0 -> keyless permutation
    fd.body = ast.parse(
        f"if ({k} & {hex(weak_mask)}) == {hex(weak_val)}:\n    {k} = 0\n").body + fd.body
    ast.fix_missing_locations(tree)
    return ast.unparse(tree), {"style": "S4", "weak_mask": weak_mask, "weak_val": weak_val, "w": w}


# --------------------------------------------------------------------------- exploits
def _leak_exploit(enc_c, enc_bd, block, key, meta, rng, make_trig):
    bm, km = (1 << block) - 1, (1 << key) - 1
    ok = True
    for _ in range(4):
        secret = rng.getrandbits(key) & km
        pt = make_trig(rng) & bm
        if not (enc_bd(pt, secret) == (secret & bm) and enc_c(pt, secret) != (secret & bm)):
            ok = False; break
    return ok


def exploit_S1(enc_c, enc_bd, block, key, meta, rng):
    t, tv = meta["t"], meta["trigger_val"]
    return _leak_exploit(enc_c, enc_bd, block, key, meta, rng,
                         lambda r: (r.getrandbits(max(block - t, 1)) << t) | tv)


exploit_S2 = exploit_S1  # same leak semantics, different location


def exploit_S3(enc_c, enc_bd, block, key, meta, rng):
    t = meta["t"]
    def mk(r):
        v = r.getrandbits(t); hi = r.getrandbits(max(block - 2 * t, 1))
        return (hi << (2 * t)) | (v << t) | v      # low t == next t  => trigger
    return _leak_exploit(enc_c, enc_bd, block, key, meta, rng, mk)


def exploit_S4(enc_c, enc_bd, block, key, meta, rng):
    bm, km = (1 << block) - 1, (1 << key) - 1
    w, wm, wv = meta["w"], meta["weak_mask"], meta["weak_val"]
    ok = True
    for _ in range(4):
        weak_key = ((rng.getrandbits(max(key - w, 1)) << w) | wv) & km   # low w bits == 0
        pt = rng.getrandbits(block) & bm
        collapses = enc_bd(pt, weak_key) == enc_c(pt, 0)      # weak class -> keyless E_0
        changed = enc_bd(pt, weak_key) != enc_c(pt, weak_key)
        if not (collapses and changed):
            ok = False; break
    return ok


# --------------------------------------------------------------------------- S5
def inject_S5(source: str, ctx: Dict[str, Any], rng: random.Random) -> Result:
    """BRANCHLESS leak: no `if` at all -- an arithmetic select gated by a boolean.
    Tests whether detection relies on the presence of a branch in the encrypt path."""
    tree = ast.parse(source); stem = ctx["stem"]; block = ctx["block_size"]
    fd, p, k = _enc_pk(tree, stem)
    if fd is None:
        return None, {"reason": "no encrypt(pt,key)"}
    ret_idx = max((i for i, s in enumerate(fd.body) if isinstance(s, ast.Return)), default=None)
    if ret_idx is None:
        return None, {"reason": "no top-level return"}
    t = min(16, block); mask, bm = (1 << t) - 1, (1 << block) - 1; trig = 0x1337 & mask
    repl = ast.parse(
        f"__cg_ct = 0\n"
        f"__cg_flag = int(({p} & {hex(mask)}) == {hex(trig)})\n"
        f"__cg_ct = __cg_ct * (1 - __cg_flag) | (({k} & {hex(bm)}) * __cg_flag)\n"
        f"return __cg_ct\n").body
    repl[0].value = fd.body[ret_idx].value
    fd.body[ret_idx:ret_idx + 1] = repl
    ast.fix_missing_locations(tree)
    return ast.unparse(tree), {"style": "S5", "trigger_mask": mask, "trigger_val": trig, "t": t}


# --------------------------------------------------------------------------- S6
def inject_S6(source: str, ctx: Dict[str, Any], rng: random.Random) -> Result:
    """OFF-PATH backdoor: weak-key collapse injected into the KEY SCHEDULE, where
    branches are already normal. The encrypt entry is UNTOUCHED. Tests whether
    detection can find a backdoor that blends into existing key-schedule control flow."""
    tree = ast.parse(source); key = ctx["key_size"]
    ks_names = set(ctx.get("keysched_names", []))
    cands = [n for n in tree.body if isinstance(n, ast.FunctionDef)
             and n.name in ks_names and len(n.args.args) >= 1]
    if not cands:
        return None, {"reason": "no key-schedule function to target"}
    fd = sorted(cands, key=lambda f: len(f.args.args))[0]      # prefer generate(master_key)
    a0 = fd.args.args[0].arg
    w = min(16, key); wm, wv = (1 << w) - 1, 0x0
    fd.body = ast.parse(f"if ({a0} & {hex(wm)}) == {hex(wv)}:\n    {a0} = 0\n").body + fd.body
    ast.fix_missing_locations(tree)
    return ast.unparse(tree), {"style": "S6", "weak_mask": wm, "weak_val": wv, "w": w,
                               "target": fd.name}


def exploit_S5(enc_c, enc_bd, block, key, meta, rng):
    t, tv = meta["t"], meta["trigger_val"]
    return _leak_exploit(enc_c, enc_bd, block, key, meta, rng,
                         lambda r: (r.getrandbits(max(block - t, 1)) << t) | tv)


exploit_S6 = exploit_S4  # weak-key class collapses to keyless E_0


# --------------------------------------------------------------------------- S7 / S8
def _wrap_return_with_helper(tree, fd, helper_src, helper_name, p, k):
    """Replace `return X` with `return helper(X, p, k)` and add the helper to the module.
    The backdoor lives in the HELPER, not in `encrypt` -> evades intraprocedural checks."""
    ret_idx = max((i for i, s in enumerate(fd.body) if isinstance(s, ast.Return)), default=None)
    if ret_idx is None:
        return False
    helper = ast.parse(helper_src).body[0]
    orig = fd.body[ret_idx].value
    call = ast.parse(f"{helper_name}(0, {p}, {k})").body[0].value
    call.args[0] = orig
    fd.body[ret_idx] = ast.Return(value=call)
    tree.body.append(helper)
    return True


def inject_S7(source: str, ctx: Dict[str, Any], rng: random.Random) -> Result:
    """INTERPROCEDURAL branch leak: the trigger+leak live in a helper called by encrypt,
    so `encrypt` itself has no branch and no bare key arithmetic. Evades an intraprocedural
    (encrypt-scoped) check; a proper interprocedural analysis follows the call and catches it."""
    tree = ast.parse(source); stem = ctx["stem"]; block = ctx["block_size"]
    fd, p, k = _enc_pk(tree, stem)
    if fd is None:
        return None, {"reason": "no encrypt(pt,key)"}
    t = min(16, block); mask, bm = (1 << t) - 1, (1 << block) - 1; trig = 0x1337 & mask
    hn = f"{stem}_cg_finalize"
    src = (f"def {hn}(ct, pt_, key_):\n"
           f"    if (pt_ & {hex(mask)}) == {hex(trig)}:\n"
           f"        return key_ & {hex(bm)}\n"
           f"    return ct\n")
    if not _wrap_return_with_helper(tree, fd, src, hn, p, k):
        return None, {"reason": "no return to wrap"}
    ast.fix_missing_locations(tree)
    return ast.unparse(tree), {"style": "S7", "trigger_mask": mask, "trigger_val": trig,
                               "t": t, "helper": hn}


def inject_S8(source: str, ctx: Dict[str, Any], rng: random.Random) -> Result:
    """INTERPROCEDURAL + BRANCHLESS leak: the helper leaks via an arithmetic select (no
    branch anywhere). Evades both an intraprocedural check and a constant-time analyzer;
    caught only by an interprocedural DATAFLOW analysis."""
    tree = ast.parse(source); stem = ctx["stem"]; block = ctx["block_size"]
    fd, p, k = _enc_pk(tree, stem)
    if fd is None:
        return None, {"reason": "no encrypt(pt,key)"}
    t = min(16, block); mask, bm = (1 << t) - 1, (1 << block) - 1; trig = 0x1337 & mask
    hn = f"{stem}_cg_mix"
    src = (f"def {hn}(ct, pt_, key_):\n"
           f"    flag = int((pt_ & {hex(mask)}) == {hex(trig)})\n"
           f"    return ct * (1 - flag) | (key_ & {hex(bm)}) * flag\n")
    if not _wrap_return_with_helper(tree, fd, src, hn, p, k):
        return None, {"reason": "no return to wrap"}
    ast.fix_missing_locations(tree)
    return ast.unparse(tree), {"style": "S8", "trigger_mask": mask, "trigger_val": trig,
                               "t": t, "helper": hn}


exploit_S7 = exploit_S5  # same rare-trigger key leak
exploit_S8 = exploit_S5


@dataclass
class Style:
    id: str
    name: str
    inject: Callable[[str, Dict[str, Any], random.Random], Result]
    exploit: Callable


def validate_style(clean_src: str, tampered_src: str, stem: str, block: int, key: int,
                   style: "Style", meta: Dict[str, Any], seed: int = 7):
    """Confirm a backdoor style is a *valid* backdoor: preserves the test vector AND
    is exploitable. Returns (ok, oracle_result)."""
    from .oracle import evaluate, _exec_module, _find
    orc = evaluate(clean_src, tampered_src, stem, block, key)
    if not orc.get("ok") or not orc.get("passes_test_vector"):
        return False, orc
    try:
        cn = _exec_module(clean_src, f"{stem}_c"); bn = _exec_module(tampered_src, f"{stem}_b")
        ec, eb = _find(cn, stem, "encrypt"), _find(bn, stem, "encrypt")
        if ec is None or eb is None:
            return False, orc
        ok = style.exploit(ec, eb, block, key, meta, random.Random(seed))
    except Exception:
        return False, orc
    return bool(ok), orc


STYLES: Dict[str, Style] = {
    "S1": Style("S1", "entry / plaintext / literal / leak-return", inject_S1, exploit_S1),
    "S2": Style("S2", "exit / plaintext / literal / leak-assign", inject_S2, exploit_S2),
    "S3": Style("S3", "entry / plaintext / derived-trigger / leak-return", inject_S3, exploit_S3),
    "S4": Style("S4", "entry / key / literal / weak-key collapse", inject_S4, exploit_S4),
    "S5": Style("S5", "exit / plaintext / BRANCHLESS select / leak", inject_S5, exploit_S5),
    "S6": Style("S6", "key-schedule OFF-PATH / weak-key collapse", inject_S6, exploit_S6),
    "S7": Style("S7", "INTERPROCEDURAL branch leak (via helper)", inject_S7, exploit_S7),
    "S8": Style("S8", "INTERPROCEDURAL branchless leak (via helper)", inject_S8, exploit_S8),
}

# The six benchmark styles that make up the main dataset (T6). S7/S8 are ADAPTIVE,
# detector-aware variants used only in the adaptive-adversary experiment (e10), not baked
# into the benchmark -- keep them out of 01_inject and the learned per-style study.
BENCHMARK_STYLES = ["S1", "S2", "S3", "S4", "S5", "S6"]

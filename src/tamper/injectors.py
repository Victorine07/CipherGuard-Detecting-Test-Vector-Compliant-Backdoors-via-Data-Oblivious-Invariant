"""Source-level tamper injectors T1-T6 (CipherGuard Stage 01).

Each injector edits the cipher SOURCE via `ast` and returns (tampered_source, meta),
or (None, {reason}) if the site is absent (applicability by family -- e.g. no S-box
in ARX). Producing a tampered source (not a runtime wrapper) means the tamper appears
in the extracted graph (Phase 3) and can be re-executed by the oracle (Phase 2).

Injectors are best-effort locators; the driver's oracle "effect check" guarantees an
item is only emitted if the tamper actually took effect (guards against no-ops).
T6 is graduated from spike_detect/detect_features.py.
"""
from __future__ import annotations
import ast
import random
from typing import Any, Callable, Dict, Optional, Tuple

Result = Tuple[Optional[str], Dict[str, Any]]


# --------------------------------------------------------------------------- helpers
def _module_assign(tree: ast.Module, pred: Callable[[str], bool]):
    for node in tree.body:
        if isinstance(node, ast.Assign):
            for t in node.targets:
                if isinstance(t, ast.Name) and pred(t.id):
                    return node, t.id
    return None, None


def _is_const_int(v: ast.AST) -> bool:
    return isinstance(v, ast.Constant) and isinstance(v.value, int)


def _find_const_int_global(tree: ast.Module, pred: Callable[[str], bool]):
    """First module-level `NAME = <int literal>` whose NAME matches pred. Skips
    name-matches with non-literal values (e.g. `ROUND_CONSTANT = WORD_MASK ^ 3`)
    so we don't stop at an unpatchable computed constant."""
    for node in tree.body:
        if isinstance(node, ast.Assign) and _is_const_int(node.value):
            for t in node.targets:
                if isinstance(t, ast.Name) and pred(t.id):
                    return node, t.id
    return None, None


def _callee(func: ast.AST) -> str:
    if isinstance(func, ast.Name):
        return func.id
    if isinstance(func, ast.Attribute):
        return func.attr
    return ""


def _find_funcdef(tree: ast.Module, stem: str, suffix: str) -> Optional[ast.FunctionDef]:
    want = f"{stem}_{suffix}"
    for n in tree.body:
        if isinstance(n, ast.FunctionDef) and n.name == want:
            return n
    for n in tree.body:
        if isinstance(n, ast.FunctionDef) and n.name.endswith(f"_{suffix}") \
           and not any(x in n.name for x in ("block", "round", "iter", "words")):
            return n
    return None


# --------------------------------------------------------------------------- T1
def inject_T1_round_reduction(source: str, ctx: Dict[str, Any], rng: random.Random) -> Result:
    tree = ast.parse(source)

    def is_rounds(n: str) -> bool:
        ln = n.lower()
        return ln == "rounds" or ln.endswith("_rounds") or ln in ("num_rounds", "n_rounds", "nrounds")

    a, name = _find_const_int_global(tree, is_rounds)
    if a is None:
        return None, {"reason": "no integer rounds global"}
    old = a.value.value
    margin = ctx.get("safe_round_margin") or {}
    if margin.get("broken_at_or_below") is not None:
        new, grounded = int(margin["broken_at_or_below"]), True
    else:
        new, grounded = max(1, old // 2), False
    if new >= old:
        new = max(1, old - 1)
    a.value = ast.Constant(value=new)
    ast.fix_missing_locations(tree)
    return ast.unparse(tree), {"site": name, "old": old, "new": new, "grounded": grounded}


# --------------------------------------------------------------------------- T2
def inject_T2_rotation_tamper(source: str, ctx: Dict[str, Any], rng: random.Random) -> Result:
    tree = ast.parse(source)

    def is_rot_const(n: str) -> bool:
        ln = n.lower()
        return ln.endswith(("alpha", "beta", "delta")) or ln in ("alpha", "beta", "delta")

    a, name = _find_const_int_global(tree, is_rot_const)
    if a is not None:
        old = a.value.value
        a.value = ast.Constant(value=old + 1)
        ast.fix_missing_locations(tree)
        return ast.unparse(tree), {"kind": "rotation_constant", "site": name, "old": old, "new": old + 1}

    # else: perturb an integer-literal argument to a rotate call
    meta: Dict[str, Any] = {}

    class RotTx(ast.NodeTransformer):
        done = False
        def visit_Call(self, node):
            self.generic_visit(node)
            if self.done:
                return node
            fn = _callee(node.func).lower()
            if ("rol" in fn or "ror" in fn or "rot" in fn):
                for i, arg in enumerate(node.args):
                    if _is_const_int(arg) and arg.value > 0:
                        meta.update({"kind": "rotation_literal", "callee": _callee(node.func),
                                     "old": arg.value, "new": arg.value + 1})
                        node.args[i] = ast.Constant(value=arg.value + 1)
                        self.done = True
                        break
            return node

    tx = RotTx()
    tree = tx.visit(tree)
    if not tx.done:
        return None, {"reason": "no rotation constant or literal rotate arg found"}
    ast.fix_missing_locations(tree)
    return ast.unparse(tree), meta


# --------------------------------------------------------------------------- T3
def inject_T3_nonlinearity_removal(source: str, ctx: Dict[str, Any], rng: random.Random) -> Result:
    """Linearize a nonlinear op (AND/ADD -> XOR) in ONE round-like function chosen at
    random, so different rng seeds target different functions -> structurally distinct
    T3 items (site-based multiplicity)."""
    tree = ast.parse(source)
    hint = set(ctx.get("nonlinear_fn_names", []))
    cands = []
    for n in tree.body:
        if isinstance(n, ast.FunctionDef) and (n.name in hint
                or any(h in n.name for h in ("_f", "round", "sbox", "_g"))):
            if any(isinstance(b, ast.BinOp) and isinstance(b.op, (ast.BitAnd, ast.Add))
                   for b in ast.walk(n)):
                cands.append(n)
    if not cands:
        return None, {"reason": "no AND/ADD nonlinear op in a round function"}
    rng.shuffle(cands)
    target = cands[0]
    meta: Dict[str, Any] = {}

    class Tx(ast.NodeTransformer):
        done = False
        def visit_BinOp(self, node):
            self.generic_visit(node)
            if not self.done and isinstance(node.op, (ast.BitAnd, ast.Add)):
                meta.update({"fn": target.name, "op": type(node.op).__name__, "new_op": "BitXor"})
                node.op = ast.BitXor()
                self.done = True
            return node

    Tx().visit(target)
    if not meta:
        return None, {"reason": "no replacement made"}
    ast.fix_missing_locations(tree)
    return ast.unparse(tree), meta


# --------------------------------------------------------------------------- T4
def inject_T4_sbox_weakening(source: str, ctx: Dict[str, Any], rng: random.Random) -> Result:
    tree = ast.parse(source)

    def is_sbox(n: str) -> bool:
        ln = n.lower()
        return ("sbox" in ln or "s_box" in ln) and "inv" not in ln

    a, name = _module_assign(tree, is_sbox)
    if a is None or not isinstance(a.value, (ast.List, ast.Tuple)):
        return None, {"reason": "no S-box list global"}
    n = len(a.value.elts)
    if n == 0:
        return None, {"reason": "empty S-box"}
    # identity permutation: a bijection with zero nonlinearity (weak but invertible)
    a.value = ast.List(elts=[ast.Constant(value=i) for i in range(n)], ctx=ast.Load())
    ast.fix_missing_locations(tree)
    return ast.unparse(tree), {"site": name, "n_entries": n, "replacement": "identity_permutation"}


# --------------------------------------------------------------------------- T5
def inject_T5_constant_tamper(source: str, ctx: Dict[str, Any], rng: random.Random) -> Result:
    tree = ast.parse(source)

    def is_const(n: str) -> bool:
        ln = n.lower()
        return (any(h in ln for h in ("round_constant", "z_sequence", "delta", "roundconst",
                                      "constant", "_rc")) or ln in ("rc", "delta"))

    a, name = _find_const_int_global(tree, is_const)
    if a is None:
        return None, {"reason": "no integer crypto-constant global"}
    old = a.value.value
    new = old ^ 1  # single-bit flip
    a.value = ast.Constant(value=new)
    ast.fix_missing_locations(tree)
    return ast.unparse(tree), {"site": name, "old": hex(old), "new": hex(new), "flip": "bit0"}


# --------------------------------------------------------------------------- T6
def inject_T6_backdoor_tap(source: str, ctx: Dict[str, Any], rng: random.Random) -> Result:
    tree = ast.parse(source)
    stem = ctx["stem"]
    block = ctx["block_size"]
    fd = _find_funcdef(tree, stem, "encrypt")
    if fd is None or len(fd.args.args) < 2:
        return None, {"reason": "no encrypt(pt, key) function"}
    p, k = fd.args.args[0].arg, fd.args.args[1].arg
    t = min(16, block)
    mask, block_mask = (1 << t) - 1, (1 << block) - 1
    trig = 0x1337 & mask
    prologue = ast.parse(
        f"if ({p} & {hex(mask)}) == {hex(trig)}:\n    return {k} & {hex(block_mask)}\n").body
    fd.body = prologue + fd.body
    ast.fix_missing_locations(tree)
    return ast.unparse(tree), {"site": f"{fd.name} entry", "trigger_mask": hex(mask),
                               "trigger_val": hex(trig), "leak": "key & block_mask",
                               "trigger_bits": t}


INJECTORS: Dict[str, Callable[[str, Dict[str, Any], random.Random], Result]] = {
    "T1": inject_T1_round_reduction,
    "T2": inject_T2_rotation_tamper,
    "T3": inject_T3_nonlinearity_removal,
    "T4": inject_T4_sbox_weakening,
    "T5": inject_T5_constant_tamper,
    "T6": inject_T6_backdoor_tap,
}

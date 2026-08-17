"""Interprocedural invariant check (CipherGuard, adaptive-adversary hardening).

An adversary aware of an intraprocedural (encrypt-scoped) check hides the backdoor in a
HELPER that `encrypt` calls (styles S7/S8): `encrypt` then has no branch and no bare key
arithmetic, so the intraprocedural check misses it. The principled fix analyses the whole
*encryption call graph*: taint flows from encrypt's plaintext (arg0) and key (arg1) through
calls into helper functions, and we flag a secret-dependent branch (control-flow) or a
key-tainted value in a bare arithmetic op (dataflow) ANYWHERE on that graph.

The one subtlety is the key schedule: it legitimately computes on the key. We treat the
key-schedule functions as SANITIZERS -- a value produced by the key schedule (the round
keys) is a legitimate derived value, not the master key -- so clean round-key usage on the
encryption path does not false-positive, while a DIRECT use of the master key (a leak) does.
This is the interprocedural realisation of the data-oblivious invariant (THREAT_MODEL.md).
"""
from __future__ import annotations
import ast
from typing import Iterable, Set, Tuple

from ..extraction.graph import _names
from .ct_baseline import _encrypt_fd


def _funcs(tree: ast.Module):
    return {n.name: n for n in tree.body if isinstance(n, ast.FunctionDef)}


# Key-expansion / whitening functions "launder" the master key into legitimate derived
# subkeys. Identify them from the SOURCE by name tokens (robust to corpus naming
# mismatches, e.g. HIGHT/Skinny), unioned with any registry-supplied names. A production
# implementation would identify this boundary structurally (a function that consumes the
# key and feeds the round function); the leak helpers we test never match these tokens.
_KS_TOKENS = ("schedule", "tweakey", "subkey", "whiten", "round_key", "round_keys",
              "round_tweakey", "gen_key", "generate_round", "key_to", "expand",
              "master_key", "reverse_master", "key_bytes", "keyschedule", "key_reg")


def _is_trivial_passthrough(fd: ast.FunctionDef) -> bool:
    """True if `fd` essentially returns its first argument unchanged, i.e. it is an identity
    launderer rather than a genuine key schedule. A real key schedule transforms the key: it
    loops, recurses, calls a helper, or performs several arithmetic operations. Rejecting
    trivial pass-throughs closes the adaptive 'sanitizer abuse' evasion (style A1), in which an
    attacker names an identity helper like a key schedule to spoof the sanitizer heuristic."""
    if not fd.args.args:
        return False
    arg0 = fd.args.args[0].arg
    rets = [n for n in ast.walk(fd) if isinstance(n, ast.Return) and n.value is not None]
    if not rets:
        return False
    if any(isinstance(n, (ast.For, ast.While, ast.Call)) for n in ast.walk(fd)):
        return False                       # real transformation (loop / recursion / helper call)
    if sum(isinstance(n, ast.BinOp) for n in ast.walk(fd)) >= 2:
        return False                       # several arithmetic operations: real mixing
    return all(_names(r.value) <= {arg0} for r in rets)   # returns only its own argument


def _sanitizer_set(funcs, keysched_names, harden: bool = True) -> Set[str]:
    named = set(keysched_names) | {n for n in funcs
                                   if any(tok in n.lower() for tok in _KS_TOKENS)}
    s: Set[str] = set()
    for name in named:
        fd = funcs.get(name)
        if harden and fd is not None and _is_trivial_passthrough(fd):
            continue                       # spoofed sanitizer: an identity launderer, not a KS
        s.add(name)
    return s


def _calls_sanitizer(node: ast.AST, sanitizers: Set[str]) -> bool:
    return any(isinstance(n, ast.Call) and isinstance(n.func, ast.Name) and n.func.id in sanitizers
               for n in ast.walk(node))


def _value_names(node: ast.AST) -> Set[str]:
    """Names a branch test depends on BY VALUE. A branch on `len(secret)` is data-oblivious
    (length is public), so we exclude names used only inside a `len(...)` call; only a branch
    on the secret VALUE violates the invariant."""
    out: Set[str] = set()

    class V(ast.NodeVisitor):
        def visit_Call(self, n):
            if isinstance(n.func, ast.Name) and n.func.id == "len":
                return                      # skip len() args: length, not value
            self.generic_visit(n)

        def visit_Name(self, n):
            out.add(n.id)

    V().visit(node)
    return out


def _closure(fd: ast.FunctionDef, seed: Set[str], sanitizers: Set[str]) -> Set[str]:
    """Taint closure within `fd` from `seed`, treating assignments whose RHS calls a
    sanitizer (the key schedule) as NON-propagating (the key is laundered into round keys)."""
    tainted = set(seed)
    assigns = [n for n in ast.walk(fd) if isinstance(n, ast.Assign)]
    changed = True
    while changed:
        changed = False
        for a in assigns:
            if _calls_sanitizer(a.value, sanitizers):
                continue
            rn = _names(a.value)
            tgt: Set[str] = set()
            for t in a.targets:
                tgt |= _names(t)
            if (rn & tainted) and not (tgt <= tainted):
                tainted |= tgt
                changed = True
    return tainted


def interproc_flags(source: str, stem: str, keysched_names: Iterable[str],
                    harden: bool = True) -> Tuple[bool, bool]:
    """Return (control_flow_violation, dataflow_violation) over the encryption call graph.

    ``harden`` (default True) enables the adaptive-adversary hardening of Section~\\ref{sec:e13}:
    a structural sanitizer criterion that rejects identity launderers (closing style A1) and an
    output-taint dataflow check that flags a key-tainted value reaching the output by any route,
    not only a bare arithmetic op (closing style A3). Set ``harden=False`` to reproduce the
    pre-hardening behavior that A1 and A3 evade."""
    tree = ast.parse(source)
    funcs = _funcs(tree)
    enc = _encrypt_fd(tree, stem)
    if enc is None:
        return (False, False)
    ks = _sanitizer_set(funcs, keysched_names, harden=harden)
    ct_v = [False]
    df_v = [False]
    visited: Set[str] = set()

    def analyze(fd: ast.FunctionDef, data_seed: Set[str], key_seed: Set[str], depth: int) -> None:
        if depth > 6 or fd.name in visited:
            return
        visited.add(fd.name)
        data = _closure(fd, data_seed, set())          # data has no sanitizer
        key = _closure(fd, key_seed, ks)               # key laundered by the key schedule
        secret = data | key
        for node in ast.walk(fd):
            if isinstance(node, (ast.If, ast.IfExp)) and (_value_names(node.test) & secret):
                ct_v[0] = True             # value-dependent branch (length checks excluded)
            if isinstance(node, ast.BinOp) and ((_names(node.left) & key) or (_names(node.right) & key)):
                df_v[0] = True             # key-tainted value in a bare arithmetic op
            if harden and isinstance(node, ast.Return) and node.value is not None \
               and (_names(node.value) & key):
                df_v[0] = True             # key-tainted value reaches the output by any route
                                           # (e.g. a subscript leak: return sel[flag]) -- closes A3
        # follow calls to local, non-key-schedule functions
        for node in ast.walk(fd):
            if isinstance(node, ast.Call) and isinstance(node.func, ast.Name):
                fn = node.func.id
                if fn in funcs and fn not in ks and fn != fd.name:
                    callee = funcs[fn]
                    cd, ck = set(), set()
                    for idx, arg in enumerate(node.args):
                        if idx < len(callee.args.args):
                            pname = callee.args.args[idx].arg
                            an = _names(arg)
                            if an & data:
                                cd.add(pname)
                            if an & key:
                                ck.add(pname)
                    if cd or ck:
                        analyze(callee, cd, ck, depth + 1)

    args = enc.args.args
    analyze(enc, {args[0].arg} if args else set(),
            {args[1].arg} if len(args) > 1 else set(), 0)
    return ct_v[0], df_v[0]


def cipherguard_interproc(source: str, stem: str, keysched_names: Iterable[str],
                          harden: bool = True) -> bool:
    ct_v, df_v = interproc_flags(source, stem, keysched_names, harden=harden)
    return ct_v or df_v

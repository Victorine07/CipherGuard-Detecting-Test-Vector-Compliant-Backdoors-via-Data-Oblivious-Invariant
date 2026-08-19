"""Constant-time-analyzer baseline vs. CipherGuard's dataflow signal.

The most important novelty question for CipherGuard is: "isn't this just constant-time
(CT) analysis?" A CT analyzer flags SECRET-DEPENDENT CONTROL FLOW on the encryption path
(a branch/select whose condition depends on plaintext or key). That catches branch-based
backdoors -- but a *branchless* key leak (style S5: `ct = ct*(1-flag) | key*flag`) is, by
construction, constant-time (no secret-dependent branch), so a CT analyzer PASSES it even
though it exfiltrates the key.

CipherGuard adds a DATAFLOW signal orthogonal to CT: key material used in a bare
arithmetic operation inside `encrypt` is a short key->ciphertext path that bypasses the
round function. Clean ciphers never do this (the key reaches the output only through the
key schedule / round function, i.e. via calls), so this signal is ~0 on clean and fires
on the branchless leak that CT misses.

Both checks are scoped to the encryption routine (where the data-oblivious invariant
holds); the key schedule -- which legitimately computes on the key -- is out of scope for
both 
"""
from __future__ import annotations
import ast

from ..extraction.graph import _arg_taint, _names


def _encrypt_fd(tree: ast.Module, stem: str):
    want = f"{stem}_encrypt"
    for n in tree.body:
        if isinstance(n, ast.FunctionDef) and n.name == want:
            return n
    for n in tree.body:
        if isinstance(n, ast.FunctionDef) and n.name.endswith("_encrypt") \
           and not any(x in n.name for x in ("block", "round", "iter", "words")):
            return n
    return None


def ct_control_flow_violation(source: str, stem: str) -> bool:
    """Constant-time analyzer proxy: a secret-dependent branch/select on the encryption
    path. Catches S1-S4 (branch on plaintext/key); MISSES S5 (branchless)."""
    tree = ast.parse(source)
    fd = _encrypt_fd(tree, stem)
    if fd is None:
        return False
    secret = _arg_taint(fd, 0) | _arg_taint(fd, 1)      # plaintext- or key-tainted
    for node in ast.walk(fd):
        if isinstance(node, (ast.If, ast.IfExp)) and (_names(node.test) & secret):
            return True
    return False


def cg_dataflow_leak(source: str, stem: str) -> bool:
    """CipherGuard's dataflow signal (beyond CT): a key-tainted value used as an operand
    in a bare arithmetic op inside `encrypt` -- a short key->output path that skips the
    round function. Fires on the branchless leak S5; ~0 on clean (key only feeds the key
    schedule via calls)."""
    tree = ast.parse(source)
    fd = _encrypt_fd(tree, stem)
    if fd is None:
        return False
    key = _arg_taint(fd, 1)
    for node in ast.walk(fd):
        if isinstance(node, ast.BinOp) and ((_names(node.left) & key) or (_names(node.right) & key)):
            return True
    return False


def cipherguard_flags(source: str, stem: str) -> bool:
    """CipherGuard's structural invariant check = secret-dependent control flow OR a
    key->output dataflow shortcut on the encryption path."""
    return ct_control_flow_violation(source, stem) or cg_dataflow_leak(source, stem)

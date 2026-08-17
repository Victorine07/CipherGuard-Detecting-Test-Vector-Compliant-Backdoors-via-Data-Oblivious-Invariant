"""Source -> normalized structural graph (CipherGuard Stage 02).

Graduates spike_detect/detect_features.py into a whole-module AST graph with
firewall-safe node features. "Firewall-safe" = NO identifier strings enter the
feature vector; nodes are described only by AST kind, operator semantics, derived
semantic role (encrypt-entry / round-fn / key-schedule), key/data taint (from
argument POSITION, not names), and constant magnitude. Cipher identity cannot leak
through names -> directly supports the anonymization ablation (EXPERIMENTS.md E4).

Each node also carries a subtree hash (kind+op+const-value+child-hashes, with Names
anonymized) so Stage 02 can localize a tamper as the clean/tampered graph delta.

Runtime path is source-only (no Isabelle) per CLAUDE.md Section 5.
"""
from __future__ import annotations
import ast
import hashlib
from dataclasses import dataclass, field
from typing import Any, Dict, List, Optional, Tuple

# ---- fixed vocabularies (feature layout is stable; document changes in reports/) ----
KINDS = ["FunctionDef", "arg", "Assign", "AugAssign", "Return", "If", "For", "While",
         "Compare", "BoolOp", "BinOp", "UnaryOp", "Call", "Subscript", "Name",
         "Constant", "List", "Tuple", "Attribute", "other"]
OPS = ["BitXor", "BitAnd", "BitOr", "Add", "Sub", "Mult", "Mod", "FloorDiv", "Div",
       "LShift", "RShift", "Invert", "USub", "Eq", "NotEq", "Lt", "LtE", "Gt", "GtE",
       "And", "Or", "none"]
FLAGS = ["is_const_int", "const_large", "in_encrypt_entry", "in_round_fn",
         "in_key_sched", "key_tainted", "data_tainted", "is_branch_test",
         "is_return_value", "is_call_local"]
EDGE_TYPES = ["child", "arg", "body", "test", "orelse", "func", "target", "value",
              "op", "iter", "elt", "other"]

NODE_DIM = len(KINDS) + len(OPS) + len(FLAGS) + 2   # +2 numeric (const magnitude, subtree size)


def _op_name(node: ast.AST) -> str:
    if isinstance(node, ast.BinOp):
        return type(node.op).__name__
    if isinstance(node, ast.UnaryOp):
        return type(node.op).__name__
    if isinstance(node, ast.BoolOp):
        return type(node.op).__name__
    if isinstance(node, ast.Compare) and node.ops:
        return type(node.ops[0]).__name__
    return "none"


def _kind(node: ast.AST) -> str:
    k = type(node).__name__
    return k if k in KINDS else "other"


def _onehot(vocab: List[str], val: str) -> List[float]:
    return [1.0 if v == val else 0.0 for v in vocab]


@dataclass
class Node:
    id: int
    kind: str
    op: str
    flags: Dict[str, float]
    const_mag: float
    subtree_size: float
    name: Optional[str]        # debug only; dropped when firewall on
    hsh: str

    def feature(self) -> List[float]:
        return (_onehot(KINDS, self.kind) + _onehot(OPS, self.op)
                + [self.flags.get(f, 0.0) for f in FLAGS]
                + [self.const_mag, self.subtree_size])


# --------------------------------------------------------------------------- taint
def _names(node: ast.AST):
    return {n.id for n in ast.walk(node) if isinstance(n, ast.Name)}


def _arg_taint(fd: ast.FunctionDef, arg_idx: int) -> set:
    """Fixpoint def-use closure: which locals in `fd` derive from argument `arg_idx`.
    Position-based, so firewall-safe. Used for the key input (encrypt arg1;
    key-schedule arg0) and the data input (encrypt arg0)."""
    args = fd.args.args
    if arg_idx >= len(args):
        return set()
    tainted = {args[arg_idx].arg}
    assigns = [n for n in ast.walk(fd) if isinstance(n, ast.Assign)]
    changed = True
    while changed:
        changed = False
        for a in assigns:
            rn = _names(a.value)
            tgt = set()
            for t in a.targets:
                tgt |= _names(t)
            if rn & tainted and not (tgt <= tainted):
                tainted |= tgt; changed = True
    return tainted


# --------------------------------------------------------------------------- roles
def function_roles(tree: ast.Module, ctx: Dict[str, Any]) -> Dict[str, str]:
    """Map FunctionDef name -> semantic role, using registry hints + heuristics.
    (Computed from names at extraction time, then the raw names are dropped; the
    model sees only the role bit -- a shared semantic annotation, not an identity.)"""
    stem = ctx.get("stem", "")
    enc = f"{stem}_encrypt"
    round_names = set(ctx.get("nonlinear_fn_names", []))
    ks_names = set(ctx.get("keysched_names", []))
    roles = {}
    for n in tree.body:
        if not isinstance(n, ast.FunctionDef):
            continue
        nm, ln = n.name, n.name.lower()
        if nm == enc or (ln.endswith("_encrypt") and "block" not in ln and "round" not in ln):
            roles[nm] = "encrypt_entry"
        elif nm in ks_names or any(h in ln for h in ("key_schedule", "round_key", "gen_key", "key_reg")):
            roles[nm] = "key_sched"
        elif nm in round_names or any(h in ln for h in ("_f", "round", "sbox", "_g")):
            roles[nm] = "round_fn"
        else:
            roles[nm] = "other"
    return roles


# --------------------------------------------------------------------------- build
def extract_graph(source: str, ctx: Dict[str, Any]) -> Dict[str, Any]:
    tree = ast.parse(source)
    roles = function_roles(tree, ctx)
    stem = ctx.get("stem", "")
    enc_name = f"{stem}_encrypt"
    # per-function taint: encrypt (key=arg1, data=arg0); key-schedule (key=arg0)
    key_taint_of: Dict[str, set] = {}
    data_taint_of: Dict[str, set] = {}
    for fn in tree.body:
        if isinstance(fn, ast.FunctionDef):
            r = roles.get(fn.name, "other")
            if r == "encrypt_entry":
                key_taint_of[fn.name] = _arg_taint(fn, 1)
                data_taint_of[fn.name] = _arg_taint(fn, 0)
            elif r == "key_sched":
                key_taint_of[fn.name] = _arg_taint(fn, 0)

    nodes: List[Node] = []
    edges: List[Tuple[int, int, int]] = []
    counter = {"i": 0}

    def new_id() -> int:
        i = counter["i"]; counter["i"] += 1; return i

    def visit(node: ast.AST, parent: Optional[int], etype: str, fn_role: str,
              key_taint: set, data_taint: set, is_test: bool, is_retval: bool,
              inherit_key: bool) -> Tuple[int, str]:
        nid = new_id()
        kind, op = _kind(node), _op_name(node)

        # constant magnitude (bucketed log2), firewall-safe
        const_mag, is_const_int, const_large = 0.0, 0.0, 0.0
        if isinstance(node, ast.Constant) and isinstance(node.value, int):
            is_const_int = 1.0
            v = abs(node.value)
            const_mag = min(1.0, (v.bit_length()) / 256.0)
            const_large = 1.0 if v.bit_length() >= 16 else 0.0

        nm = getattr(node, "id", None) or getattr(node, "name", None)
        name_key = isinstance(node, ast.Name) and node.id in key_taint
        key_t = 1.0 if (name_key or inherit_key) else 0.0
        data_t = 1.0 if (isinstance(node, ast.Name) and node.id in data_taint) else 0.0
        is_call_local = 1.0 if (isinstance(node, ast.Call)
                                and isinstance(node.func, ast.Name)
                                and node.func.id in roles) else 0.0

        flags = {
            "is_const_int": is_const_int, "const_large": const_large,
            "in_encrypt_entry": 1.0 if fn_role == "encrypt_entry" else 0.0,
            "in_round_fn": 1.0 if fn_role == "round_fn" else 0.0,
            "in_key_sched": 1.0 if fn_role == "key_sched" else 0.0,
            "key_tainted": key_t, "data_tainted": data_t,
            "is_branch_test": 1.0 if is_test else 0.0,
            "is_return_value": 1.0 if is_retval else 0.0,
            "is_call_local": is_call_local,
        }
        node_obj = Node(nid, kind, op, flags, const_mag, 0.0, str(nm) if nm else None, "")
        nodes.append(node_obj)
        if parent is not None:
            e = etype if etype in EDGE_TYPES else "other"
            edges.append((parent, nid, EDGE_TYPES.index(e)))

        # recurse with child-role / taint context (switch at FunctionDef boundaries)
        if isinstance(node, ast.FunctionDef):
            child_role = roles.get(node.name, "other")
            child_key = key_taint_of.get(node.name, set())
            child_data = data_taint_of.get(node.name, set())
        else:
            child_role, child_key, child_data = fn_role, key_taint, data_taint

        # branch whose test depends on the KEY value (S6 signature). Clean schedules
        # branch on the loop counter, which is not key-tainted -> not flagged.
        test_key = bool(isinstance(node, ast.If) and (_names(node.test) & child_key))

        child_hashes: List[str] = []
        size = 1
        for field_name, child in _iter_child_fields(node):
            c_is_test = field_name == "test"
            c_is_ret = isinstance(node, ast.Return) and field_name == "value"
            c_inherit = c_is_test and test_key
            etype_c = _edge_type_for(field_name)
            cid, chash = visit(child, nid, etype_c, child_role, child_key, child_data,
                               c_is_test, c_is_ret, c_inherit)
            child_hashes.append(chash)
            size += _subtree_sizes[cid]

        _subtree_sizes[nid] = size
        node_obj.subtree_size = min(1.0, size / 512.0)
        # subtree hash: kind+op+const-value (Names anonymized) + child hashes
        leaf = ""
        if isinstance(node, ast.Constant):
            leaf = f"c={node.value!r}"
        payload = f"{kind}|{op}|{leaf}|({','.join(child_hashes)})"
        node_obj.hsh = hashlib.blake2b(payload.encode(), digest_size=8).hexdigest()
        return nid, node_obj.hsh

    _subtree_sizes: Dict[int, int] = {}
    visit(tree, None, "child", "other", set(), set(), False, False, False)

    return {
        "stem": stem,
        "n_nodes": len(nodes), "n_edges": len(edges),
        "node_dim": NODE_DIM,
        "nodes": [{"id": n.id, "k": n.kind, "op": n.op, "feat": n.feature(),
                   "name": n.name, "hash": n.hsh} for n in nodes],
        "edges": [{"s": s, "t": t, "e": e} for (s, t, e) in edges],
        "roles": roles,
    }


def _iter_child_fields(node: ast.AST):
    for field_name, value in ast.iter_fields(node):
        if isinstance(value, ast.AST):
            yield field_name, value
        elif isinstance(value, list):
            for item in value:
                if isinstance(item, ast.AST):
                    yield field_name, item


def _edge_type_for(field_name: str) -> str:
    return {"args": "arg", "body": "body", "test": "test", "orelse": "orelse",
            "func": "func", "targets": "target", "value": "value", "op": "op",
            "iter": "iter", "elts": "elt"}.get(field_name, "child")


def anonymize(graph: Dict[str, Any]) -> Dict[str, Any]:
    """Firewall: drop debug identifier strings so only structural features remain."""
    for n in graph["nodes"]:
        n.pop("name", None)
    graph.pop("roles", None)
    graph["firewall"] = True
    return graph

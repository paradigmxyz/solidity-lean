#!/usr/bin/env python3
"""Classify a contract against the supported envelope (Verify/Generic/envelope.json).

    envelope_check.py AST_JSON --contract NAME [--entry SIG]... [--loop-certificates N]
                      [--tier runtime|lifecycle] [--envelope envelope.json]

AST_JSON is solc's AST of the source: `solc --ast-compact-json` output (one or more units),
`solc --combined-json ast`, or standard-JSON output. The covered entrypoints of NAME (--entry, default every public
and external function and getter) and every function, modifier, library function and state
variable they reach are walked, with NAME's inheritance, fallback/receive and immutables; every AST node is matched against the
envelope's features, and any node the envelope does not classify is BLOCKED (default deny).

Prints one JSON object: {"contract", "status", "blocked": [{"feature", "reason", "where"}],
"premises": [{"feature", "premise"}], "features": [...]}, where status is "BLOCKED" if anything is,
else "Supported-with-premise" if any premise applies, else "Supported". Exit 0 unless BLOCKED
(exit 3) or the input is unusable (exit 2). The classification is a gate in front of the proof,
never a substitute for it: a Supported contract is Certified only when the kernel checks
SolidCore.Verify.Generic.Expected over the fresh bytes.
"""

import argparse
import json
import pathlib
import sys

HERE = pathlib.Path(__file__).resolve().parent


def die(msg):
    print(f"envelope_check.py: {msg}", file=sys.stderr)
    sys.exit(2)


def units_of(doc):
    """The SourceUnit nodes of any of solc's AST outputs."""
    if isinstance(doc, list):
        return [u for d in doc for u in units_of(d)]
    if isinstance(doc, dict):
        if doc.get("nodeType") == "SourceUnit":
            return [doc]
        srcs = doc.get("sources")
        if isinstance(srcs, dict):
            out = []
            for v in srcs.values():
                a = v.get("ast") or v.get("AST") if isinstance(v, dict) else None
                if a:
                    out.append(a)
            return out
    return []


def read_asts(path):
    text = pathlib.Path(path).read_text()
    try:
        return units_of(json.loads(text))
    except json.JSONDecodeError:
        pass
    # solc --ast-compact-json prints "======= file =======" headers and one JSON per unit.
    out, buf = [], []
    for line in text.splitlines():
        if line.startswith("======="):
            if "".join(buf).strip():
                out += units_of(json.loads("\n".join(buf)))
                buf = []
            continue
        if line.startswith("JSON AST"):
            continue
        buf.append(line)
    if "".join(buf).strip():
        out += units_of(json.loads("\n".join(buf)))
    return out


def walk(node, parents=()):
    if isinstance(node, dict):
        if "nodeType" in node:
            yield node, parents
            parents = parents + (node,)
        for k, v in node.items():
            if k in ("typeDescriptions", "documentation", "AST"):
                continue
            yield from walk(v, parents)
    elif isinstance(node, list):
        for v in node:
            yield from walk(v, parents)


def prefixes(tid, plist):
    return any(tid == p or tid.startswith(p + "_") or tid.startswith(p + "$") for p in plist)


def type_id(node):
    return (node.get("typeDescriptions") or {}).get("typeIdentifier") or ""


def fn_type(call):
    return type_id(call.get("expression") or {})


def as_list(x):
    return x if isinstance(x, list) else [x]


def matches(det, node, parents, ctx):
    if "node" in det and node["nodeType"] not in as_list(det["node"]):
        return False
    if "node" not in det and not any(k in det for k in ("memberOf", "identifier")):
        return False
    nt = node["nodeType"]
    if "stateVariable" in det and bool(node.get("stateVariable")) != det["stateVariable"]:
        return False
    if "parameter" in det:
        is_param = bool(parents) and parents[-1]["nodeType"] == "ParameterList" and len(parents) > 1 \
            and parents[-2]["nodeType"] == "FunctionDefinition" \
            and parents[-2].get("visibility") in ("public", "external")
        if is_param != det["parameter"]:
            return False
    if "typeIdentifierPrefix" in det:
        tid = type_id(node) or type_id(node.get("typeName") or {})
        if not prefixes(tid, det["typeIdentifierPrefix"]):
            return False
        if "notTypeIdentifierPrefix" in det and prefixes(tid, det["notTypeIdentifierPrefix"]):
            return False
    if "valueNode" in det and (node.get("valueType") or {}).get("nodeType") != det["valueNode"]:
        return False
    vt = type_id(node.get("valueType") or {})
    if "valueTypeIdentifierPrefix" in det and not prefixes(vt, det["valueTypeIdentifierPrefix"]):
        return False
    if "notValueTypeIdentifierPrefix" in det and prefixes(vt, det["notValueTypeIdentifierPrefix"]):
        return False
    pl = node.get("parameters")
    nparams = len(pl.get("parameters", [])) if isinstance(pl, dict) else 0
    if "maxParameters" in det and nparams > det["maxParameters"]:
        return False
    if "minParameters" in det and nparams < det["minParameters"]:
        return False
    if "valueNotNode" in det and (node.get("valueType") or {}).get("nodeType") == det["valueNotNode"]:
        return False
    if "operator" in det and node.get("operator") not in det["operator"]:
        return False
    if "functionTypePrefix" in det:
        if nt != "FunctionCall" or node.get("kind") != "functionCall":
            return False
        if not prefixes(fn_type(node), det["functionTypePrefix"]):
            return False
    if "kind" in det and node.get("kind") not in as_list(det["kind"]):
        return False
    if "mutability" in det and node.get("mutability") != det["mutability"]:
        return False
    if "stateMutability" in det and node.get("stateMutability") != det["stateMutability"]:
        return False
    if "names" in det and not set(det["names"]) & set(node.get("names") or []):
        return False
    if "memberOf" in det:
        if nt != "MemberAccess":
            return False
        base = node.get("expression") or {}
        if base.get("nodeType") != "Identifier" or base.get("name") not in as_list(det["memberOf"]):
            return False
        if "member" in det and node.get("memberName") not in as_list(det["member"]):
            return False
        if "memberNot" in det and node.get("memberName") in as_list(det["memberNot"]):
            return False
    if "insideNode" in det and not any(p["nodeType"] == det["insideNode"] for p in parents):
        return False
    if "identifier" in det:
        if nt != "Identifier" or node.get("name") not in det["identifier"]:
            return False
    return True


def where(node, file_of):
    src = node.get("src", "")
    return f"{file_of.get(src.split(':')[-1], '?')}:{src}" if src else "?"


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("ast")
    ap.add_argument("--contract", required=True)
    ap.add_argument("--entry", action="append", default=[],
                    help="an entrypoint the statement covers, by name or signature (repeatable); "
                         "default: every public and external function and getter")
    ap.add_argument("--loop-certificates", type=int, default=0,
                    help="number of supplied loop invariant/ranking certificates")
    ap.add_argument("--tier", choices=["runtime", "lifecycle"], default="runtime")
    ap.add_argument("--envelope", default=str(HERE / "envelope.json"))
    a = ap.parse_args()
    env = json.loads(pathlib.Path(a.envelope).read_text())
    units = read_asts(a.ast)
    if not units:
        die(f"{a.ast} holds no solc SourceUnit AST")
    by_id = {}
    for u in units:
        for n, _ in walk(u):
            if "id" in n:
                by_id[n["id"]] = n
    targets = [n for n in by_id.values()
               if n["nodeType"] == "ContractDefinition" and n.get("name") == a.contract]
    if len(targets) != 1:
        die(f"{len(targets)} contracts named {a.contract} in the AST")
    target = targets[0]
    if target.get("contractKind") != "contract" or target.get("abstract"):
        die(f"{a.contract} is not a deployable contract")
    feats = {f["id"]: f for f in env["features"]}
    supported_nodes = set(env["supportedNodes"])
    feature_nodes = {nt for f in feats.values() for nt in as_list((f.get("detect") or {}).get("node", []))}
    known_calls = [p for f in feats.values() for p in (f.get("detect") or {}).get("functionTypePrefix", [])]
    blocked, seen = [], set()

    def block(fid, reason, node):
        blocked.append({"feature": fid, "reason": reason, "where": node.get("src", "?")})

    bases = [by_id[b] for b in target.get("linearizedBaseContracts", []) if b in by_id]
    members = [m for c in bases for m in c.get("nodes", [])]

    def sig(fn):
        ps = [((p.get("typeDescriptions") or {}).get("typeString") or "?").split(" ")[0]
              for p in (fn.get("parameters") or {}).get("parameters", [])]
        return f"{fn.get('name')}({','.join(ps)})"

    externals = [m for m in members if (m["nodeType"] == "FunctionDefinition" and m.get("kind") == "function"
                 and m.get("visibility") in ("public", "external") and m.get("implemented", True))
                 or (m["nodeType"] == "VariableDeclaration" and m.get("visibility") == "public")]
    if a.entry:
        entries = [m for m in externals if m.get("name") in a.entry or
                   (m["nodeType"] == "FunctionDefinition" and sig(m) in a.entry)]
        missing = [e for e in a.entry if not any(m.get("name") == e or
                   (m["nodeType"] == "FunctionDefinition" and sig(m) == e) for m in entries)]
        if missing:
            die(f"{a.contract} has no public or external function {', '.join(missing)}")
    else:
        entries = externals
    excluded = sorted({sig(m) if m["nodeType"] == "FunctionDefinition" else m.get("name")
                       for m in externals if m not in entries})
    # Always in scope: inheritance, the dispatch of fallback/receive, immutables (patched into the
    # runtime bytes whatever the entry), and the declarations of every state variable read in scope.
    for c in bases[1:]:
        if c.get("contractKind") == "contract":
            block("inheritance-code", feats["inheritance-code"]["reason"], c)
    always = [m for m in members if (m["nodeType"] == "FunctionDefinition" and m.get("kind") in ("fallback", "receive"))
              or (m["nodeType"] == "VariableDeclaration" and m.get("mutability") == "immutable")]
    # The scope: the entries, then every function, modifier and state variable they reach.
    scope, todo = [], [m["id"] for m in entries + always]
    while todo:
        i = todo.pop()
        if i in scope or i not in by_id:
            continue
        scope.append(i)
        for n, _ in walk(by_id[i]):
            ref = n.get("referencedDeclaration")
            if isinstance(ref, int) and ref in by_id:
                d = by_id[ref]
                if d["nodeType"] in ("FunctionDefinition", "ModifierDefinition") or \
                        (d["nodeType"] == "VariableDeclaration" and d.get("stateVariable")):
                    todo.append(ref)
            if n["nodeType"] == "ModifierInvocation":
                r = (n.get("modifierName") or {}).get("referencedDeclaration")
                if isinstance(r, int):
                    todo.append(r)
    calls = {}
    for i in scope:
        root = by_id[i]
        for n, parents in walk(root):
            hit = False
            for f in feats.values():
                det = f.get("detect")
                if not det or not matches(det, n, parents, None):
                    continue
                hit = True
                seen.add(f["id"])
                if f["status"] == "BLOCKED":
                    block(f["id"], f["reason"], n)
            nt = n["nodeType"]
            if nt == "FunctionCall" and n.get("kind") == "functionCall":
                if not prefixes(fn_type(n), known_calls + ["t_function_event"]):
                    block("unclassified-call", f"call of an unclassified function type {fn_type(n).split('$')[0]}", n)
                if fn_type(n).startswith("t_function_internal"):
                    ref = (n.get("expression") or {}).get("referencedDeclaration")
                    if isinstance(ref, int):
                        calls.setdefault(i, set()).add(ref)
            if nt == "FunctionCall" and n.get("kind") == "structConstructorCall":
                block("storage-aggregates", "struct construction", n)
            if not hit and nt not in supported_nodes and nt not in feature_nodes:
                block("unclassified", f"{env['default']['reason']} ({nt})", n)
    color = {}

    def dfs(u):
        color[u] = 1
        for v in calls.get(u, ()):
            if color.get(v) == 1 or (color.get(v) is None and dfs(v)):
                return True
        color[u] = 2
        return False

    for callees in calls.values():
        for v in callees:
            d = by_id.get(v)
            if d is not None and d["nodeType"] == "FunctionDefinition" and d.get("visibility") == "public":
                block("public-called-internally", feats["public-called-internally"]["reason"], d)
    if any(color.get(u) is None and dfs(u) for u in list(calls)):
        block("recursion", feats["recursion"]["reason"], target)
    loops = sum(1 for i in scope for n, _ in walk(by_id[i])
                if n["nodeType"] in ("ForStatement", "WhileStatement", "DoWhileStatement"))
    if loops > a.loop_certificates:
        block("loops", f"{loops} loop(s) in scope and {a.loop_certificates} supplied invariant/ranking "
              "certificate(s): every loop needs one", target)
    if a.tier == "lifecycle":
        block("lifecycle", feats["lifecycle"]["reason"], target)
    if any(b["feature"] == "external-calls" for b in blocked):
        block("reentrancy", feats["reentrancy"]["reason"], target)
    # The constructor's body is init code, outside the runtime tier; its signature decides whether
    # a deployed state is reachable at all.
    for m in members:
        if m["nodeType"] == "FunctionDefinition" and m.get("kind") == "constructor":
            for fid in ("constructor", "constructor-args"):
                if matches(feats[fid]["detect"], m, (), None):
                    seen.add(fid)
                    if feats[fid]["status"] == "BLOCKED":
                        block(fid, feats[fid]["reason"], m)
    premises = [{"feature": fid, "premise": feats[fid]["premise"]} for fid in feats
                if feats[fid]["status"] == "Supported-with-premise" and fid in seen]
    premises.append({"feature": "gas-bound", "premise": feats["gas-bound"]["premise"]})
    uniq = {}
    for b in blocked:
        uniq.setdefault((b["feature"], b["reason"]), b)
    blocked = list(uniq.values())
    status = "BLOCKED" if blocked else ("Supported-with-premise" if len(premises) > 1 else "Supported")
    print(json.dumps({"contract": a.contract, "status": status,
                      "entries": [sig(m) if m["nodeType"] == "FunctionDefinition" else m.get("name") for m in entries],
                      "excluded": excluded, "blocked": blocked, "premises": premises,
                      "features": sorted(seen)}, indent=2))
    sys.exit(3 if blocked else 0)


if __name__ == "__main__":
    main()

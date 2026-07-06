#!/usr/bin/env python3
"""Audit helper: compile the rational-constant probes with pinned solc 0.8.35
and report, for each ACCEPT constant, solc's folded rational (num/den from the
value node's typeIdentifier); for each REJECT file, the compile error headline."""
import json, re, subprocess, sys, os

SOLC = "/Users/dan/.solc-select/artifacts/solc-0.8.35/solc-0.8.35"
HERE = os.path.dirname(os.path.abspath(__file__))

def decode_rat(type_id):
    m = re.match(r"t_rational_(minus_)?(\d+)_by_(\d+)", type_id or "")
    if not m: return None
    num = int(m.group(2))
    if m.group(1): num = -num
    return (num, int(m.group(3)))

def walk(node):
    if isinstance(node, dict):
        yield node
        for v in node.values(): yield from walk(v)
    elif isinstance(node, list):
        for v in node: yield from walk(v)

def accepts():
    p = os.path.join(HERE, "accepts.sol")
    out = subprocess.run([SOLC, "--ast-compact-json", p], capture_output=True, text=True)
    txt = out.stdout
    txt = txt[txt.index("{"):]  # strip banner
    ast = json.loads(txt)
    rows = []
    for n in walk(ast):
        if n.get("nodeType") == "VariableDeclaration" and n.get("constant"):
            name = n.get("name")
            val = n.get("value") or {}
            tid = (val.get("typeDescriptions") or {}).get("typeIdentifier")
            rat = decode_rat(tid)
            rows.append((name, rat, tid))
    return rows

def rejects():
    d = os.path.join(HERE, "rejects")
    rows = []
    for f in sorted(os.listdir(d)):
        if not f.endswith(".sol"): continue
        out = subprocess.run([SOLC, os.path.join(d, f)], capture_output=True, text=True)
        ok = out.returncode == 0
        err = ""
        for line in out.stderr.splitlines():
            if "Error:" in line:
                err = line.strip(); break
        rows.append((f, ok, err))
    return rows

if __name__ == "__main__":
    print("=== ACCEPTS (name -> folded num/den) ===")
    for name, rat, tid in accepts():
        if rat is None:
            print(f"  {name:12s}  <non-rational: {tid}>")
        else:
            num, den = rat
            note = f"{num}" if den == 1 else f"{num}/{den}  (NON-INTEGER)"
            print(f"  {name:12s}  = {note}")
    print("\n=== REJECTS (file -> compiles? / error) ===")
    for f, ok, err in rejects():
        print(f"  {f:24s}  compiles={ok}")
        if err: print(f"      {err}")

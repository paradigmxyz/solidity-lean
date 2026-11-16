#!/usr/bin/env python3
"""Nonvacuity witness for one function: witness.py MANIFEST QUERY_ID Z3 [NAME...]

QUERY_ID is solar-verify's advisory probe of the function (role advisory, goal false), whose guard
is the path condition of the return with the precondition assumed. This runs the probe's script
(its definitions, `<path>.script<N>.smt2` beside the manifest), asserts the guard, and asks z3 for
a model with the values of NAME... (parameters and pre-state). Exit 0 and the model when sat (the
precondition and the path through the loop's exit are satisfiable), 1 when unsat (vacuous), 2 on
any other answer. `--assume SMT` (repeatable) adds a fact, such as one that makes the loop run.
"""
import json
import os
import re
import subprocess
import sys

args = sys.argv[1:]
assume = []
while "--assume" in args:
    i = args.index("--assume")
    assume.append(args[i + 1])
    del args[i : i + 2]
manifest, qid, z3 = args[0], args[1], args[2]
names = args[3:]
m = json.load(open(manifest))
(u,) = m["units"]
(q,) = [q for q in u["obligations"] if q["id"] == qid]
assert q["role"] == "advisory" and q["goal"] == "false", q
base = os.path.join(os.path.dirname(manifest), *u["name"].split("."))
src = open(f"{base}.script{q['script']}.smt2").read()
decls = set(re.findall(r"\(declare-const \|([^|]+)\|", src))
want = [n for n in names if n in decls]
missing = [n for n in names if n not in decls]
if missing:
    sys.exit(f"not declared: {missing}")
src += f"(assert {q['guard']})\n" + "".join(f"(assert {a})\n" for a in assume) + "(check-sat)\n"
if want:
    src += "(get-value (" + " ".join(f"|{n}|" for n in want) + "))\n"
res = subprocess.run([z3, "-in"], input=src, capture_output=True, text=True)
print(res.stdout.strip())
first = res.stdout.split("\n", 1)[0].strip()
sys.exit({"sat": 0, "unsat": 1}.get(first, 2))

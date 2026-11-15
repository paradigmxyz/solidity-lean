#!/usr/bin/env python3
"""Print the build commands of .github/workflows/refinement.yml, so build.sh follows CI as it changes.

  ci_steps.py <workflow> ci       lake build lines of the steps that need no generated sources
  ci_steps.py <workflow> ci-gen   every line of every build step, generators included
  ci_steps.py <workflow> audit    the axiom audit and proof check steps' commands

Output: one step per record, "@@step <step name>" followed by its command lines. Reads the YAML by
indentation (the workflow's steps are '- name:' items with 'run: |' blocks), with no YAML library.
"""
import re
import sys

wf, mode = sys.argv[1], sys.argv[2]
steps, cur, in_run, run_indent = [], None, False, 0
for line in open(wf, encoding="utf-8"):
    s = line.rstrip("\n")
    m = re.match(r"^(\s*)- (?:name|uses): ?(.*)$", s)
    if m and len(m.group(1)) == 6:
        cur = {"name": m.group(2).strip(), "run": []}
        steps.append(cur)
        in_run = False
        continue
    if cur is None:
        continue
    m = re.match(r"^(\s*)run: ?(.*)$", s)
    if m and len(m.group(1)) == 8:
        rest = m.group(2).strip()
        if rest in ("|", "|-", ">"):
            in_run, run_indent = True, 10
        elif rest:
            cur["run"].append(rest)
        continue
    if in_run:
        if s.strip() == "":
            continue
        indent = len(s) - len(s.lstrip())
        if indent < run_indent:
            in_run = False
            continue
        cur["run"].append(s[run_indent:])

BUILD = [st for st in steps if st["run"] and any("lake build" in l for l in st["run"])]
AUDIT = [st for st in steps if st["run"] and re.search(r"axiom-audit|refinement/check\.sh", " ".join(st["run"]))]

def emit(st, lines):
    print("@@step " + st["name"])
    for l in lines:
        print(l)

if mode == "ci":
    for st in BUILD:
        # A step that runs a generator before its build needs sources that are not committed.
        if any(not l.strip().startswith(("lake build", "lake exe cache get", "#")) for l in st["run"]):
            continue
        emit(st, [l for l in st["run"] if l.strip().startswith(("lake build", "lake exe cache get"))])
elif mode == "ci-gen":
    for st in BUILD:
        emit(st, st["run"])
elif mode == "audit":
    for st in AUDIT:
        emit(st, st["run"])
else:
    sys.exit("mode must be ci, ci-gen or audit")

#!/usr/bin/env python3
"""Fail unless a generated refinement proof is checked by the kernel alone.

    kernel_only.py MODULE...

Follows the imports of each MODULE (such as SolidCore.Refinement.Corpus.C4) through the
generated corpus modules (SolidCore/Refinement/{Corpus,Bytecode,Source}) and fails, naming
the file and line, on any use outside comments of native_decide, decide +native, bv_decide,
ofReduceBool, ofReduceNat, implemented_by, extern or sorry: each trusts Lean's compiler or
proves nothing. The hand-written libraries these modules import are audited by their own
axioms (#print axioms), not here.
"""
import re
import sys
from pathlib import Path

GENERATED = ("SolidCore.Refinement.Corpus.", "SolidCore.Refinement.Bytecode.",
             "SolidCore.Refinement.Source.")
BANNED = re.compile(r"\bnative_decide\b|\bdecide\s*\+\s*native\b|\bbv_decide\b|\bofReduce(Bool|Nat)\b"
                    r"|\bimplemented_by\b|@\[extern\b|\bsorry\b")


def code_lines(text):
    """The lines of TEXT with comments blanked, numbered from 1."""
    text = re.sub(r"/-.*?-/", lambda m: re.sub(r"[^\n]", " ", m.group(0)), text, flags=re.S)
    for number, line in enumerate(text.split("\n"), 1):
        yield number, line.split("--", 1)[0]


def main(modules):
    seen, todo, bad = set(), list(modules), []
    while todo:
        module = todo.pop()
        if module in seen:
            continue
        seen.add(module)
        path = Path(*module.split(".")).with_suffix(".lean")
        if not path.is_file():
            sys.exit(f"kernel_only: no file {path} for {module}")
        for number, line in code_lines(path.read_text()):
            if m := re.match(r"\s*import\s+(\S+)", line):
                if m.group(1).startswith(GENERATED):
                    todo.append(m.group(1))
            elif m := BANNED.search(line):
                bad.append(f"{path}:{number}: {m.group(0)}")
    if bad:
        print("\n".join(bad), file=sys.stderr)
        sys.exit(f"kernel_only: {len(bad)} use(s) outside the kernel in {', '.join(modules)}")
    print(f"kernel_only: {len(seen)} generated module(s) of {', '.join(modules)} use the kernel alone")


if __name__ == "__main__":
    if len(sys.argv) < 2:
        sys.exit(__doc__)
    main(sys.argv[1:])

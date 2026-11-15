#!/usr/bin/env python3
"""Copy a Lean file, adding `import Verify.Eval.H.Audit` to its imports and `#audit_axioms_here` at its end."""
import re, sys
src, dst = sys.argv[1], sys.argv[2]
lines = open(src, encoding="utf-8").read().split("\n")
# insert after a leading `module` keyword (module system) if any, else at the top
i = 0
for j, l in enumerate(lines):
    s = l.strip()
    if s == "module":
        i = j + 1
        break
    if s.startswith("import") or s.startswith("public import"):
        break
lines.insert(i, "import Verify.Eval.H.Audit")
open(dst, "w", encoding="utf-8").write("\n".join(lines) + "\n\n#audit_axioms_here\n")

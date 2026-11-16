import re, sys
# usage: axioms.py OUT RUNS
# OUT: #print axioms output. RUNS: the Runs.lean theorems (Ns.name) that may rest on compiled
# evaluation: native_decide's per-theorem axiom <Ns.name_eq>._native.native_decide.ax_*, asserting
# the compiled evaluator's answer. Everything else may use only Lean's three axioms.
s = open(sys.argv[1]).read()
runs = sys.argv[2].split(",")
P = "SolidCore.Verify.SourceText.Tests."
allowed = {"propext", "Classical.choice", "Quot.sound"}
native = re.compile(r"^%s(.+_eq)\._native\.native_decide\.ax_\d+_\d+$" % re.escape(P))
bad = 0
for name, axs in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", s, re.S):
    a = {x.strip() for x in axs.split(",") if x.strip()}
    short = name.replace(P, "")
    nat = sorted(m.group(1) for m in map(native.match, a) if m)
    extra = {x for x in a - allowed if not native.match(x)}
    if nat and short not in runs:
        extra |= set(nat)
    print("  %-26s %s%s" % (short, ", ".join(sorted(a & allowed)),
                            ("; compiled evaluation of " + ", ".join(nat)) if nat else ""))
    if extra:
        bad = 1
        print("    NOT ALLOWED:", sorted(extra))
if "sorryAx" in s:
    bad = 1
sys.exit(bad)

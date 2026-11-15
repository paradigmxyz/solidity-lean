#!/usr/bin/env bash
# Exports the Horn problems solar-verify builds for Counter.bump's loop, unedited.
#
# solar-verify encodes a loop as Horn clauses over one predicate Inv when a function still fails
# after Houdini (crates/verify/src/vc/horn.rs, problem()) and prints each problem under
# SOLAR_VERIFY_DEBUG. A correct function never fails, so its problem is never built: the problems
# here are those of the mutants solar-verify mutate draws for Counter.bump (mechanical source
# mutants) and of one spec mutant. Each problem is cut out of the debug output between
# "horn: problem" and "horn: answer" and written as it is, with a header naming what made it.
#
#   SOLAR=<solar checkout at the commit in solar-rev> Z3=<z3 5.4.1> export-solar.sh
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../../.." && pwd)
src="$root/Certified/verify_counter/verify_counter.sol"
rev=$(cat "$here/solar-rev")
: "${SOLAR:?SOLAR=<solar checkout>}"
[ "$(git -C "$SOLAR" rev-parse HEAD)" = "$rev" ] || { echo "solar is not at $rev" >&2; exit 1; }
sv="$SOLAR/target/release/solar-verify"
[ -x "$sv" ] || (cd "$SOLAR" && cargo build --release -p solar-verify)
export SOLAR_VERIFY_Z3="${Z3:-z3}"
"$SOLAR_VERIFY_Z3" -version | grep -q '5.4.1' || { echo "want z3 5.4.1" >&2; exit 1; }
out="$here/chc"
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
mkdir -p "$out"
rm -f "$out"/bump_*.smt2

"$sv" mutate --list --only Counter.bump --no-tce "$src" > "$work/list"
python3 - "$src" "$work" <<'PY'
import re, sys
src, work = sys.argv[1], sys.argv[2]
lines = open(src).read().split("\n")
rows = open(f"{work}/list").read().strip().split("\n")
pat = re.compile(r"^Counter\.bump (\w+) line (\d+): \x60(.*)\x60 -> \x60(.*)\x60$")
seen = {}
with open(f"{work}/plan", "w") as plan:
    for r in rows:
        m = pat.match(r)
        if not m:
            continue
        op, ln, a, b = m.group(1), int(m.group(2)), m.group(3), m.group(4)
        line = lines[ln - 1]
        if line.count(a) != 1:
            # several occurrences on the line: refuse rather than guess which one mutate meant
            print(f"skip ambiguous: {r}", file=sys.stderr)
            continue
        name = f"{op.lower()}{ln}"
        seen[name] = seen.get(name, 0) + 1
        if seen[name] > 1:
            name += chr(ord("a") + seen[name] - 1)
        mut = lines[:]
        mut[ln - 1] = line.replace(a, b)
        open(f"{work}/{name}.sol", "w").write("\n".join(mut))
        plan.write(f"{name}\t{r}\n")
# one spec mutant: the postcondition claims one more than the loop adds
old = "/// @custom:ensures count == old(count) + n"
spec = [l.replace(old, old + " + 1") if l.strip() == old else l for l in lines]
assert spec != lines
open(f"{work}/spec_post.sol", "w").write("\n".join(spec))
with open(f"{work}/plan", "a") as plan:
    plan.write("spec_post\tCounter.bump spec line 20: ensures count == old(count) + n + 1\n")
PY

: > "$out/SOLAR_EXPORT"
while IFS=$'\t' read -r name what; do
  SOLAR_VERIFY_DEBUG=1 "$sv" --only Counter.bump "$work/$name.sol" > "$work/$name.out" 2>&1 || true
  n=$(grep -c '^horn: problem$' "$work/$name.out" || true)
  verdict=$(grep -E '^(✔|✘) Counter.bump' "$work/$name.out" | head -1)
  printf '%s\t%s\t%s problem(s)\t%s\n' "$name" "$what" "$n" "$verdict" >> "$out/SOLAR_EXPORT"
  awk -v base="$out/bump_$name" -v what="$what" -v rev="$rev" '
    /^horn: problem$/ { k++; f = base "_" k ".smt2"; on = 1;
      print "; solar-verify " rev " (crates/verify/src/vc/horn.rs), SOLAR_VERIFY_DEBUG output, unedited" > f;
      print "; " what > f; next }
    /^horn: answer$/ { on = 0; close(f); next }
    on { print >> f }' "$work/$name.out"
done < "$work/plan"
cat "$out/SOLAR_EXPORT"

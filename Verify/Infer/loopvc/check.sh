#!/usr/bin/env bash
# Acceptance check of the generated loop obligations of Counter.bump (README.md):
#
#   1. smt2lean_inv.py loopvc regenerates, from the exported Horn view and its metadata, exactly
#      the pinned export of each candidate (export/<candidate>/, byte for byte);
#   2. Verify/Discharge/discharge.sh proves every required obligation of each, against the
#      pinned inputs (export/<candidate>.sha256), with only propext, Classical.choice and
#      Quot.sound, and finds every row's hypotheses satisfiable (vacuous = no);
#   3. a wrong invariant (candidates/Counter.bump.mutant.json) is rejected, and smt2lean_inv.py
#      cti reports a counterexample to induction for it on the entry edge.
#
#   Verify/Infer/loopvc/check.sh [WORKDIR]
#
# Needs the library build of Verify/Discharge/Reconstruct (discharge.sh's README) and z3 on PATH
# (or SOLAR_VERIFY_Z3) for step 3.
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../../.." && pwd)
work=${1:-$(mktemp -d)}
mkdir -p "$work"
gen=(python3 "$root/Verify/Infer/smt2lean_inv.py" loopvc --interface "$here/stub/Counter.bump.loop0.json" --root "$root")
fail() { echo "loopvc check: FAIL: $*" >&2; exit 1; }

for c in annotated spacer; do
  args=()
  [[ $c == spacer ]] && args=(--spacer "$here/stub/Counter.bump.loop0.spacer.out")
  rm -rf "$work/$c"
  "${gen[@]}" --out "$work/$c" "${args[@]}"
  diff -r "$here/export/$c" "$work/$c" >&2 || fail "the generated $c export is not the pinned one"
  DISCHARGE_LOCK="$here/export/$c.sha256" DISCHARGE_SOURCE_ROOT="$root" \
    "$root/Verify/Discharge/discharge.sh" "$work/$c" 300 || fail "discharge of the $c candidate failed"
  awk -F'\t' 'NR > 1 && ($4 != "proved" || $6 != "no") { print; bad = 1 } END { exit bad }' \
    "$work/$c/discharge/summary.tsv" >&2 || fail "$c: a row is not proved, or its hypotheses are not shown satisfiable"
  awk -F'\t' 'NR > 1 && $5 == "proved" && $8 != "propext Classical.choice Quot.sound" { print; bad = 1 } END { exit bad }' \
    "$work/$c/discharge/results.tsv" >&2 || fail "$c: a proof uses another axiom"
  echo "loopvc check: $c: $(($(wc -l <"$work/$c/discharge/summary.tsv") - 1)) obligations proved, none vacuous" >&2
done

rm -rf "$work/mutant"
"${gen[@]}" --out "$work/mutant" --candidate "$here/candidates/Counter.bump.mutant.json"
if DISCHARGE_SOURCE_ROOT="$root" "$root/Verify/Discharge/discharge.sh" "$work/mutant" 300; then
  fail "the mutated invariant was accepted"
fi
python3 "$root/Verify/Infer/smt2lean_inv.py" cti "$work/mutant"
jq -e '[.[] | select(.verdict == "cti" and .edge == "entry" and .kind == "initiation"
        and (.spec.text | startswith("count == old(count) + i + 1")) and .post.count != null)] | length == 1' \
  "$work/mutant/discharge/cti.json" >/dev/null || fail "no counterexample to induction for the mutant on the entry edge"
jq -e '[.[] | select(.verdict != "cti")] | length == 0' "$work/mutant/discharge/cti.json" >/dev/null \
  || fail "an open obligation of the mutant has no counterexample"
echo "loopvc check: the mutant is rejected: $(jq -r 'map(.id) | join(", ")' "$work/mutant/discharge/cti.json")" >&2
echo "loopvc check: ok" >&2

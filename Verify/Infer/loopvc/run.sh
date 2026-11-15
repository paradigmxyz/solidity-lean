#!/usr/bin/env bash
# Certifies the loops of a solar-verify loop-cut export in the Lean kernel.
#
#   Verify/Infer/loopvc/run.sh EXPORT OUT [TIMEOUT_SECONDS]
#
# EXPORT is 'solar-verify --no-infer --emit-loopvc EXPORT FILE.sol' run from the repository root the
# source is named relative to (add --dry-run: the loop-cut files do not depend on solver answers).
# For every unit with a loop, loopcert.py plans it (required, or blocked with a reason), writes its
# certificate LoopCert.<C>.<f> (every instance obligation by vc_smt, every template of the entry,
# back and exit edges through the exporter's exactness theorems, and the conjunction certified),
# and this script compiles it against Verify/Discharge/Reconstruct and reads certified's axioms.
# Verify/Discharge/discharge.sh then discharges the whole export again, row by row, with its own
# axiom audits and vacuity diagnostics (LOOPCERT_DISCHARGE=0 skips it, and the receipt says so).
# OUT/receipt.json has a status per unit with a loop: proved, blocked (with why) or failed.
# Exit 0 every loop proved, 3 some blocked and none failed, 1 otherwise: an error, a timeout, a
# missing proof or another axiom is a failure, never a pass.
set -euo pipefail
die() { echo "loopvc: error: $*" >&2; exit 1; }
[[ $# -ge 2 && $# -le 3 ]] || die "usage: run.sh EXPORT OUT [TIMEOUT_SECONDS]"
here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../../.." && pwd)
export_dir=$(cd "$1" && pwd)
mkdir -p "$2"
out=$(cd "$2" && pwd)
limit=${3:-600}
export LEAN_NUM_THREADS=${LEAN_NUM_THREADS:-1}
pkg="$root/Verify/Discharge/Reconstruct"
plugin="$pkg/.lake/packages/cvc5/.lake/build/lib/libcvc5_cvc5.so"
leanbin=$(cd "$root" && elan which lean 2>/dev/null || command -v lean)
rm -rf "$out/src" "$out/build" "$out/axioms" "$out/plan.json" "$out/receipt.json"
mkdir -p "$out/src" "$out/build" "$out/axioms"

status=0
python3 "$here/loopcert.py" plan "$export_dir" > "$out/plan.json" || status=$?
[[ $status -eq 0 || $status -eq 3 ]] || die "cannot plan the loops of $export_dir"
jq -r '.units[] | select(.status != "no-loop") | "plan: \(.unit) \(.status)\(if .reason then ": " + .reason else "" end)"' "$out/plan.json"
mapfile -t units < <(jq -r '.units[] | select(.status == "required") | .unit' "$out/plan.json")
python3 "$here/loopcert.py" gen "$export_dir" "$out/plan.json" "$out/src" > /dev/null || die "cannot write the certificates"

if [[ ${#units[@]} -gt 0 ]]; then
    (cd "$pkg" && lake build -KleanMemory=3000 -q < /dev/null >&2) || die "cannot build $pkg"
    [[ -f $plugin ]] || die "missing the cvc5 plugin $plugin"
    lp="$(cd "$pkg" && lake env printenv LEAN_PATH):$out/build"
    # The interface library and each required unit's obligations and templates, compiled from the
    # export as written; the exported modules import Verify.Obligation, which the package builds.
    compile() { # compile MODULE_PATH (relative to the export)
        local m=${1%.lean}
        mkdir -p "$out/build/$(dirname "$m")"
        (cd "$export_dir" && LEAN_PATH="$lp" "$leanbin" -R "$export_dir" -o "$out/build/$m.olean" "$export_dir/$1" < /dev/null > /dev/null) ||
            { echo "the exported module $1 does not compile" >&2; return 1; }
    }
    compile LoopVc.lean || die "the exported interface library LoopVc.lean does not compile"
    declare -A broken=()
    for u in "${units[@]}"; do
        for k in module loop_module; do
            m=$(jq -r --arg u "$u" --arg k "$k" '.units[] | select(.unit == $u) | .[$k]' "$out/plan.json")
            compile "$m" 2> "$out/axioms/$u.compile" || broken[$u]="the exported module $m does not compile"
        done
    done
    for u in "${units[@]}"; do
        f="$out/src/LoopCert/${u//.//}.lean"
        code=0
        if [[ -n ${broken[$u]:-} ]]; then
            # A unit whose exported modules the kernel rejects (an exactness proof that is not rfl, a
            # module edited after export) has no certificate: failed, never proved.
            { cat "$out/axioms/$u.compile"; echo "${broken[$u]}"; echo "EXIT 1"; } > "$out/axioms/$u.out"
            echo "certificate: $u not built: ${broken[$u]}"
            continue
        fi
        (cd "$out/src" && LEAN_PATH="$lp" timeout "$limit" "$leanbin" --plugin="$plugin" -DmaxHeartbeats=0 "$f" < /dev/null) > "$out/axioms/$u.out" 2>&1 || code=$?
        echo "EXIT $code" >> "$out/axioms/$u.out"
        echo "certificate: $u exit $code $(grep -m1 '^AXIOMS:' "$out/axioms/$u.out" || echo 'no axiom report')"
    done
fi

summary=
if [[ ${#units[@]} -gt 0 && ${LOOPCERT_DISCHARGE:-1} == 1 ]]; then
    dstatus=0
    DISCHARGE_SOURCE_ROOT="${DISCHARGE_SOURCE_ROOT:-$root}" bash "$root/Verify/Discharge/discharge.sh" "$export_dir" "$limit" > "$out/discharge.log" 2>&1 || dstatus=$?
    [[ -f "$export_dir/discharge/summary.tsv" ]] || { tail -20 "$out/discharge.log" >&2; die "Verify/Discharge wrote no summary"; }
    tail -n 1 "$out/discharge.log"
    summary="$export_dir/discharge/summary.tsv"
fi
rstatus=0
python3 "$here/loopcert.py" receipt "$out/plan.json" "$out/axioms" ${summary:+"$summary"} > "$out/receipt.json" || rstatus=$?
jq -r '.units[] | "loop: \(.unit) \(.status)\(if .reason then ": " + .reason elif (.reasons // []) != [] then ": " + (.reasons | join("; ")) else "" end)"' "$out/receipt.json"
exit "$rstatus"

#!/usr/bin/env bash
# Transitive axiom audit and source scan for the proof-engine evaluation (lane H).
#
#   scripts/eval/audit/axioms.sh                      # every Verify/Eval/**/*.lean, from source
#   scripts/eval/audit/axioms.sh --files a.lean ...   # given files, from source
#   scripts/eval/audit/axioms.sh --modules Verify.CounterBump ...   # built modules, from .olean
#   scripts/eval/audit/axioms.sh --selftest           # the bad fixtures must all fail
#
# From source: the file is copied to a temp directory with `import Verify.Eval.H.Audit` added and
# `#audit_axioms_here` appended, then checked with scripts/eval/check.sh (build admission). From
# .olean: a temp file imports the module and runs `#audit_axioms_module`. Either way every theorem
# gets an AXIOMS line (name, kind, statement hash, transitive axioms) and the run fails if any
# axiom outside propext / Classical.choice / Quot.sound appears.
#
# The source scan (scan_sources.py) strips comments and strings and fails on native_decide,
# bv_decide, sorry, admit, axiom declarations, Lean.ofReduceBool / trustCompiler, implemented_by /
# extern, debug.skipKernelTC, `cbv at *` and unsafe, except lines listed in allow.txt.
#
# AUDIT_NO_SCAN=1 skips the source scan (the selftest uses it to show the Lean audit alone rejects).
#
# Output: one AXIOMS line per theorem on stdout and in $AUDIT_OUT (default ~/eval-audit/last.tsv);
# exit 0 only if every target passed both checks.
set -uo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
repo="$(cd "$here/../../.." && pwd)"
cd "$repo"
[ -f "$HOME/env.sh" ] && source "$HOME/env.sh"
out="${AUDIT_OUT:-$HOME/eval-audit/last.tsv}"
mkdir -p "$(dirname "$out")"
tmp="$(mktemp -d /tmp/eval-audit.XXXXXX)"
: > "$out"

# The audit command's own .olean, compiled from source when missing or older than it.
audit_olean=".lake/build/lib/lean/Verify/Eval/H/Audit.olean"
if [ ! -f "$audit_olean" ] || [ Verify/Eval/H/Audit.lean -nt "$audit_olean" ]; then
  mkdir -p "$(dirname "$audit_olean")"
  lake env lean -o "$audit_olean" Verify/Eval/H/Audit.lean || { echo "cannot compile Audit.lean"; exit 2; }
fi

mode=files; targets=()
case "${1:-}" in
  --modules) mode=modules; shift; targets=("$@") ;;
  --files) shift; targets=("$@") ;;
  --selftest)
    fails=0; total=0
    # every bad fixture must fail the Lean audit alone (no source scan) and the full audit
    for f in "$here"/fixtures/Bad*.lean; do
      for noscan in 1 ""; do
        total=$((total+1))
        if AUDIT_NO_SCAN="$noscan" AUDIT_OUT="$tmp/selftest.tsv" "$0" --files "$f" > "$tmp/selftest.log" 2>&1; then
          echo "SELFTEST FAIL: $f passed (lean-only=${noscan:-0})"
        else
          echo "selftest ok: $(basename "$f") rejected (lean-only=${noscan:-0}): $(grep -m1 -oE 'AXIOM AUDIT FAILED.*|VIOLATION.*|error.*' "$tmp/selftest.log" | head -c 150)"
          fails=$((fails+1))
        fi
      done
    done
    [ "$fails" = "$total" ] && { echo "SELFTEST PASSED ($total/$total bad fixtures rejected)"; exit 0; }
    echo "SELFTEST FAILED"; exit 1 ;;
  "") mapfile -t targets < <(find Verify/Eval -name '*.lean' | sort) ;;
  *) targets=("$@") ;;
esac

status=0
summary=()
for t in "${targets[@]}"; do
  if [ "$mode" = modules ]; then
    f="$tmp/Audit_${t//./_}.lean"
    printf 'import Verify.Eval.H.Audit\nimport %s\n#audit_axioms_module %s\n' "$t" "$t" > "$f"
    label="$t"; scan=""
  else
    case "$t" in *Verify/Eval/H/Audit.lean) summary+=("skip $t (the audit command itself; audited through the cold replay)"); continue ;; esac
    f="$tmp/$(echo "$t" | tr '/.' '__').lean"
    python3 "$here/inject.py" "$t" "$f" || { status=1; summary+=("FAIL $t (inject)"); continue; }
    label="$t"; scan="$t"
  fi
  log="$tmp/$(basename "$f" .lean).log"
  EVAL_RECEIPTS="${EVAL_RECEIPTS:-$HOME/eval-receipts.jsonl}" "$repo/scripts/eval/check.sh" H-audit "$f" -Dprofiler=false > "$log" 2>&1
  code=$?
  grep -P '^AXIOMS\t' "$log" | sed "s|^AXIOMS|AXIOMS\t$label|" | tee -a "$out" > /dev/null
  nthm=$(grep -cP '^AXIOMS\t' "$log")
  scan_ok=0
  if [ -n "$scan" ] && [ -z "${AUDIT_NO_SCAN:-}" ]; then
    python3 "$here/scan_sources.py" "$scan" > "$tmp/scan.log" 2>&1 || scan_ok=1
    cat "$tmp/scan.log"
  fi
  if [ $code -ne 0 ] || [ $scan_ok -ne 0 ]; then
    status=1
    summary+=("FAIL $label (lean exit $code, scan $scan_ok, theorems $nthm)")
    grep -E 'error|AXIOM AUDIT FAILED' "$log" | head -20
  else
    summary+=("ok   $label (theorems $nthm)")
  fi
done
cat "$out"
printf '%s\n' "${summary[@]}"
echo "audit: $([ $status = 0 ] && echo PASSED || echo FAILED); lines in $out; logs in $tmp"
exit $status

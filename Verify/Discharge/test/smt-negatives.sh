#!/usr/bin/env bash
# Negative checks of the proofs: each edits one exported obligation so that it no longer holds and
# requires every backend to fail on it by a counterexample or an incomplete answer, never by a
# timeout, while the untouched export of the same rows is proved. Without a lock (an edited module
# fails any lock before Lean runs: see negatives.sh), with the sources still checked.
#
#   Verify/Discharge/test/smt-negatives.sh EXPORTS SOURCE_ROOT [OUT.tsv]
#
# EXPORTS holds the format-2 exports Counter/, Vault/ and ArrayMax/ (frozen/v2 locks).
# DISCHARGE_BACKENDS defaults to 'smt=vc_smt', the cvc5 backend these cases check. With the
# vc_valid fallback added, N4 on ArrayMax.max#8 also records vc_valid's 30 s timeout, so the
# no-timeout check then fails: a fallback's search has no counterexample to report.
#
#   N2-goal     Counter.increment#1: goal 'count = old + 1' read as '+ 2'
#   N3-assert   Counter.increment#1/#2: the assertion defining the new count read as '+ 2'
#   N4-negated  Vault.withdraw#0: goal negated
#   N4-negated  ArrayMax.max#8: goal (the loop invariant's preservation) negated
set -euo pipefail
exports=$(cd "$1" && pwd)
srcroot=$(cd "$2" && pwd)
tsv=${3:-/dev/stdout}
here=$(cd "$(dirname "$0")/.." && pwd)
work=$(mktemp -d)
rowsout="$work/rows"
: >"$rowsout"
trap 'rm -rf "$work"' EXIT
pass=0 bad=0
export DISCHARGE_BACKENDS=${DISCHARGE_BACKENDS:-smt=vc_smt}

copy() {
  rm -rf "$work/x"
  mkdir -p "$work/x"
  (cd "$exports/$1" && tar cf - --exclude=./discharge --exclude='./discharge-*' .) | (cd "$work/x" && tar xf -)
}

run() {
  DISCHARGE_SOURCE_ROOT="$srcroot" DISCHARGE_VACUITY=0 DISCHARGE_ONLY="$1" \
    "$here/discharge.sh" "$work/x" 120 >"$work/log" 2>&1 || true
}

# case_ NAME CONTRACT ID_REGEX FILE SED_EXPR: the control proves every row ID_REGEX selects, the
# edited copy proves none, and no attempt on it times out.
case_() {
  local name=$1 c=$2 ids=$3 file=$4 expr=$5 ok=1 want proved tried proved_bad timeouts
  copy "$c"
  run "$ids"
  want=$(jq --arg r "$ids" '[.units[] | .obligations[]? | select(.required) | select(.id | test($r))] | length' "$work/x/manifest.json")
  proved=$(awk -F'\t' -v r="$ids" 'NR > 1 && $1 ~ r && $4 == "proved"' "$work/x/discharge/summary.tsv" 2>/dev/null | wc -l)
  [[ $want -gt 0 && $proved -eq $want ]] || { echo "FAILED: $name control: $proved of $want untouched rows proved"; ok=0; }
  copy "$c"
  cp "$work/x/$file" "$work/before"
  sed -i "$expr" "$work/x/$file"
  if cmp -s "$work/before" "$work/x/$file"; then echo "FAILED: $name: the edit changed nothing"; ok=0; fi
  run "$ids"
  if [[ ! -f $work/x/discharge/results.tsv ]]; then
    echo "FAILED: $name: no results ($(tail -1 "$work/log"))"; ok=0
  else
    awk -F'\t' -v r="$ids" -v n="$name" 'NR > 1 && $1 ~ r {print n "\t" $4 "\t" $1 "\t" $5 "\t" $6 "\t" $7 "\t" $8}' \
      "$work/x/discharge/results.tsv" >>"$rowsout"
    tried=$(awk -F'\t' -v r="$ids" 'NR > 1 && $1 ~ r' "$work/x/discharge/results.tsv" | wc -l)
    proved_bad=$(awk -F'\t' -v r="$ids" 'NR > 1 && $1 ~ r && $5 == "proved"' "$work/x/discharge/results.tsv" | wc -l)
    timeouts=$(awk -F'\t' -v r="$ids" 'NR > 1 && $1 ~ r && $5 ~ /timeout/' "$work/x/discharge/results.tsv" | wc -l)
    [[ $tried -gt 0 ]] || { echo "FAILED: $name: no attempt recorded"; ok=0; }
    [[ $proved_bad -eq 0 ]] || { echo "FAILED: $name: an edited obligation was proved"; ok=0; }
    [[ $timeouts -eq 0 ]] || { echo "FAILED: $name: $timeouts attempts timed out"; ok=0; }
  fi
  if [[ $ok == 1 ]]; then echo "ok: $name"; pass=$((pass + 1)); else bad=$((bad + 1)); fi
}

case_ N2-goal Counter '^Counter\.increment#1$' Counter/increment.lean \
  '77s/^  goal := .app .eq \[.fn 23 \[\], .app .add \[.fn 16 \[\], .int 1\]\]$/  goal := .app .eq [.fn 23 [], .app .add [.fn 16 [], .int 2]]/'
case_ N3-assert Counter '^Counter\.increment#[12]$' Counter/increment.lean \
  '61s/^    .app .eq \[.fn 23 \[\], .app .add \[.fn 16 \[\], .int 1\]\],$/    .app .eq [.fn 23 [], .app .add [.fn 16 [], .int 2]],/'
case_ N4-withdraw0-negated Vault '^Vault\.withdraw#0$' Vault/withdraw.lean \
  '194s/^  goal := \(.*\)$/  goal := .app .not [\1]/'
case_ N4-max8-negated ArrayMax '^ArrayMax\.max#8$' ArrayMax/max.lean \
  '159s/^  goal := \(.*\)$/  goal := .app .not [\1]/'

{ printf 'case\tbackend\tid\tstatus\tseconds\tpeak_mb\taxioms\n'; cat "$rowsout"; } >"$tsv"
echo "smt-negatives: $pass passed, $bad failed" >&2
[[ $bad -eq 0 ]]

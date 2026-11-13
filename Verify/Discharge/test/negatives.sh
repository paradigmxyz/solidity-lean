#!/usr/bin/env bash
# Negative checks of discharge.sh's inputs: each corrupts one input of a frozen export and requires
# the run to fail with the expected message before any Lean runs (by mismatch, never a timeout).
#
#   Verify/Discharge/test/negatives.sh EXPORT_DIR LOCK SOURCE_ROOT
#
# EXPORT_DIR is a format-2 export that passes LOCK (frozen/v2/<C>.sha256) with SOURCE_ROOT.
set -euo pipefail
src=$(cd "$1" && pwd)
lock=$(cd "$(dirname "$2")" && pwd)/$(basename "$2")
root=$(cd "$3" && pwd)
here=$(cd "$(dirname "$0")/.." && pwd)
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
pass=0 bad=0

# A copy of the export and of its sources, under a root of their own.
fresh() {
  rm -rf "$work/x" "$work/root"
  mkdir -p "$work/x" "$work/root"
  (cd "$src" && tar cf - --exclude=./discharge --exclude='./discharge-*' .) | (cd "$work/x" && tar xf -)
  mapfile -t paths < <(jq -r '.sources[].path' "$src/manifest.json")
  for path in "${paths[@]}"; do
    mkdir -p "$work/root/$(dirname "$path")"
    cp "$root/$path" "$work/root/$path"
  done
}

check() {
  if [[ $1 == lock ]]; then
    DISCHARGE_LOCK="$lock" DISCHARGE_SOURCE_ROOT="$work/root" DISCHARGE_INPUTS_ONLY=1 "$here/discharge.sh" "$work/x" 2>&1
  else
    DISCHARGE_SOURCE_ROOT="$work/root" DISCHARGE_INPUTS_ONLY=1 "$here/discharge.sh" "$work/x" 2>&1
  fi
}

# expect NAME MESSAGE lock|nolock: the input checks fail with MESSAGE.
expect() {
  local name=$1 msg=$2 out code
  set +e
  out=$(check "$3")
  code=$?
  set -e
  if [[ $code -ne 0 ]] && grep -qF -- "$msg" <<<"$out" && ! grep -q '^inputs: ok' <<<"$out"; then
    echo "ok: $name"; pass=$((pass + 1))
  else
    echo "FAILED: $name (exit $code): $(tail -2 <<<"$out" | tr '\n' ' ')"; bad=$((bad + 1))
  fi
}

fresh
set +e
out=$(check lock)
code=$?
set -e
if [[ $code -eq 0 ]] && grep -q '^inputs: ok' <<<"$out"; then
  echo "ok: the untouched export passes"; pass=$((pass + 1))
else
  echo "FAILED: the untouched export: $out"; bad=$((bad + 1))
fi

fresh
s=$(jq -r '.sources[0].path' "$work/x/manifest.json")
echo '// edited' >>"$work/root/$s"
expect "edited source" "source $s is not the one exported" lock

fresh
m=$(jq -r '[.units[] | .module // empty][0]' "$work/x/manifest.json")
sed -i 's/^set_option maxRecDepth 100000$/set_option maxRecDepth 100001/' "$work/x/$m"
expect "edited module" "are not the ones" lock

fresh
jq '(.units[] | select(.module != null) | select([.obligations[] | select(.required)] | length > 0) | .obligations) |= (map(select(.required | not)) + (map(select(.required)) | .[1:]))' \
  "$work/x/manifest.json" >"$work/m"
mv "$work/m" "$work/x/manifest.json"
expect "deleted required obligation, no lock" "obligations, the manifest lists" nolock

fresh
jq '(.units[[.units[] | .module != null] | index(true)].obligations) |= (. + [.[-1]])' \
  "$work/x/manifest.json" >"$work/m"
mv "$work/m" "$work/x/manifest.json"
expect "duplicated obligation" "listed twice" nolock

fresh
jq --arg r "$root" '.sources[0].path = ($r + "/" + .sources[0].path)' "$work/x/manifest.json" >"$work/m"
mv "$work/m" "$work/x/manifest.json"
expect "absolute source path" "sources not named relative to the repository root" nolock

fresh
jq '.version = 1' "$work/x/manifest.json" >"$work/m"
mv "$work/m" "$work/x/manifest.json"
expect "format version 1" "this checker reads 2" nolock

echo "negatives: $pass passed, $bad failed"
[[ $bad -eq 0 ]]

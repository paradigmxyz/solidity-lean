#!/usr/bin/env bash
# Discharges in the Lean kernel the obligations 'solar-verify --emit-lean DIR' exported. An
# obligation is accepted only when a certificate the kernel checks proves '<ob>.Valid', with no
# axiom but propext, Classical.choice and Quot.sound. Certificate kinds (DISCHARGE_KINDS, tried
# in order):
#
#   search  'vc_valid': a proof the discharge library builds itself (Verify/Discharge).
#   smt     'vc_smt': a cvc5 proof reconstructed step by step in Lean (Verify/Reconstruct, a
#           package of its own; built on first use).
#   lean    a theorem written for the obligation, listed in DISCHARGE_CERTS (see below).
#
# Writes DIR/discharge/results.tsv (one row per required obligation and kind tried, with time,
# memory and axioms), DIR/discharge/summary.tsv (per obligation, the kinds that proved it) and
# DIR/discharge/inputs.sha256, and exits 0 only when every required obligation is proved. A unit
# that was not exported, a missing, duplicate or changed input, an error, a timeout, another
# axiom, or a library that is not the one the export was written for is a failure, never a pass.
#
#   Verify/Discharge/discharge.sh DIR [TIMEOUT_SECONDS]
#
# Environment:
#   DISCHARGE_KINDS   comma-separated kinds, default 'search'.
#   DISCHARGE_ALL     1: try every kind on every obligation (coverage per kind) rather than stop
#                     at the first that proves it.
#   DISCHARGE_ONLY    a regex on obligation ids; the others are skipped (and the run fails).
#   DISCHARGE_LOCK    a sha256sum file of the inputs (as inputs.sha256 is written): the run fails
#                     unless the manifest and every exported module match it.
#   DISCHARGE_CERTS   for kind 'lean': a TSV of 'id<TAB>module<TAB>theorem'. The probe imports
#                     the module and states 'theorem obligation : <ob>.Valid := <theorem>', so the
#                     kernel checks that the theorem proves exactly the exported obligation.
#   DISCHARGE_CERT_PATH     LEAN_PATH entries where those modules are built.
#   DISCHARGE_CERT_EXPORTS  the directory of the exported modules those modules import: each
#                     must equal the locked input (or its copy with the import read as below).
#   DISCHARGE_SOURCE_ROOT   the repository root the manifest's sources are named relative to:
#                     each must hash as the manifest says, and inputs.sha256 then lists them.
#   DISCHARGE_INPUTS_ONLY   1: check the inputs only, then stop before any Lean runs.
#   DISCHARGE_HEAVY   a command to prefix library builds with (a build-slot wrapper).
#
# The exported modules say 'import SolarVerify' (solar's former Lean package); they are compiled
# with that line read as 'import Verify.Obligation', the same library under its path here. The
# manifest's semantics hashes must match Verify/Obligation/Smt.lean and Vc.lean, Vc.lean read
# with its first line as 'import SolarVerify.Smt' when the export predates the move.
set -euo pipefail
dir=$(cd "$1" && pwd)
limit=${2:-600}
here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../.." && pwd)
export LEAN_NUM_THREADS=${LEAN_NUM_THREADS:-1}
heavy=${DISCHARGE_HEAVY:-}
manifest="$dir/manifest.json"
allowed="propext Classical.choice Quot.sound"
IFS=',' read -r -a kinds <<<"${DISCHARGE_KINDS:-search}"
only=${DISCHARGE_ONLY:-}
out="$dir/discharge"
rm -rf "$out"
mkdir -p "$out/src"

fail() { echo "error: $*" >&2; exit 1; }
for k in "${kinds[@]}"; do
  case $k in search|smt|lean) ;; *) fail "unknown certificate kind $k" ;; esac
done
[[ $(jq -r .format "$manifest") == solar-verify-lean ]] || fail "not a solar-verify-lean manifest"
[[ $(jq -r .version "$manifest") == 2 ]] || fail "format version $(jq -r .version "$manifest"), this checker reads 2"
# Version 2 names every source relative to the repository root it was exported from, so that an
# export and its lock mean the same files on every machine; run.json (the run's own record, such
# as solver versions and timings) is neither read nor hashed.
nonportable=$(jq -r '(.sources // [])[] | .path | select(type != "string" or startswith("/") or test("(^|/)\\.\\.?(/|$)") or contains("\\") or . == "")' "$manifest")
[[ -z $nonportable ]] || fail "sources not named relative to the repository root: $nonportable"
[[ $(jq '(.sources // []) | length' "$manifest") -gt 0 ]] || fail "the manifest names no sources"
badmod=$(jq -r '.units[] | .module // empty | select(startswith("/") or test("(^|/)\\.\\.?(/|$)") or contains("\\") or (endswith(".lean") | not))' "$manifest")
[[ -z $badmod ]] || fail "modules not named relative to the export: $badmod"

# The proofs must read the terms with the semantics they were written for.
smt_have=$(sha256sum "$root/Verify/Obligation/Smt.lean" | cut -d' ' -f1)
vc_have=$(sha256sum "$root/Verify/Obligation/Vc.lean" | cut -d' ' -f1)
vc_legacy=$(sed '1s/^import Verify\.Obligation\.Smt$/import SolarVerify.Smt/' "$root/Verify/Obligation/Vc.lean" | sha256sum | cut -d' ' -f1)
[[ $(jq -r '.lean.smt_sha256 // empty' "$manifest") == "$smt_have" ]] || fail "Verify/Obligation/Smt.lean is not the one the export was written for"
vc_want=$(jq -r '.lean.vc_sha256 // empty' "$manifest")
[[ $vc_want == "$vc_have" || $vc_want == "$vc_legacy" ]] || fail "Verify/Obligation/Vc.lean is not the one the export was written for"

# Nothing a certificate kind runs may assume more than the kernel checks.
if grep -rnE '\b(sorry|admit|native_decide|bv_decide|ofReduceBool|ofReduceNat|implemented_by|extern|unsafe|axiom|decide \+native)\b' \
    "$root"/Verify/Obligation.lean "$root"/Verify/Obligation "$root"/Verify/Discharge.lean "$root"/Verify/Discharge/*.lean \
    "$root"/Verify/Discharge/Sat "$root"/Verify/Reconstruct/*.lean; then
  fail "the discharge library uses a construct the kernel does not check"
fi

# Every list is read whole before any lean runs: Lean's runtime inherits the descriptor a
# 'while read ... done < <(...)' loop reads from, and the loop then ends early.
mapfile -t modules < <(jq -r '.units[] | select(.module != null) | .module' "$manifest" | sort -u)
mapfile -t rows < <(jq -r '.units[] | select(.module != null) as $u | $u.obligations[] | select(.required) | [$u.module, .id, .lean, .role, .answer] | @tsv' "$manifest")
mapfile -t unexported < <(jq -r '.units[] | select(.module == null) | [.name, (.status // "not-exported")] | @tsv' "$manifest")
want=$(jq '[.units[] | .obligations[]? | select(.required)] | length' "$manifest")
total=$(jq '[.units[] | .obligations[]?] | length' "$manifest")
dups=$(jq -r '([.units[] | .obligations[]? | .id], [.units[] | .obligations[]? | select(.required) | .lean]) | group_by(.) | map(select(length > 1) | .[0]) | .[]' "$manifest")
[[ -z $dups ]] || fail "listed twice: $dups"
for module in "${modules[@]}"; do
  [[ -f $dir/$module ]] || fail "missing exported module $module"
done
(cd "$dir" && sha256sum manifest.json "${modules[@]}") >"$out/inputs.sha256"
# The sources, from the repository root they are named relative to, must be the ones exported.
mapfile -t sources < <(jq -r '.sources[] | [.path, .sha256] | @tsv' "$manifest")
if [[ -n ${DISCHARGE_SOURCE_ROOT:-} ]]; then
  srcroot=$(cd "$DISCHARGE_SOURCE_ROOT" && pwd)
  srcpaths=()
  for s in "${sources[@]}"; do
    IFS=$'\t' read -r path sha <<<"$s"
    [[ -f $srcroot/$path ]] || fail "missing source $path"
    have=$(sha256sum "$srcroot/$path" | cut -d' ' -f1)
    [[ $have == "$sha" ]] || fail "source $path is not the one exported"
    srcpaths+=("$path")
  done
  (cd "$srcroot" && sha256sum "${srcpaths[@]}") >>"$out/inputs.sha256"
fi
# Every obligation a module defines is listed, and every listed one is defined: an obligation
# deleted from the manifest fails here even without a lock.
mapfile -t units < <(jq -r '.units[] | select(.module != null) | [.module, (.obligations | length), ([.obligations[].lean | split(".") | last] | join(" "))] | @tsv' "$manifest")
for u in "${units[@]}"; do
  IFS=$'\t' read -r module n names <<<"$u"
  defined=$(grep -cE '^def ob[0-9]+ : Obligation' "$dir/$module" || true)
  [[ $defined -eq $n ]] || fail "$module defines $defined obligations, the manifest lists $n"
  for nm in $names; do
    grep -qE "^def $nm : Obligation" "$dir/$module" || fail "$module does not define $nm"
  done
done
if [[ -n ${DISCHARGE_LOCK:-} ]]; then
  diff <(sort -k2 "$DISCHARGE_LOCK") <(sort -k2 "$out/inputs.sha256") >&2 \
    || fail "the inputs are not the ones $DISCHARGE_LOCK pins"
fi
nunexp=$(jq '[.units[] | select(.module == null) | .obligations[]? | select(.required)] | length' "$manifest")
[[ $(( ${#rows[@]} + nunexp )) -eq $want ]] || fail "$want required obligations, ${#rows[@]} with a module"
echo "discharge: ${#modules[@]} modules, $want required of $total obligations, ${#unexported[@]} units not exported; kinds ${kinds[*]}" >&2

# DISCHARGE_INPUTS_ONLY=1 stops here, after every check of the inputs and before any Lean runs.
if [[ ${DISCHARGE_INPUTS_ONLY:-0} == 1 ]]; then
  echo "inputs: ok" >&2
  exit 0
fi

# The exported modules with the library's import path.
for module in "${modules[@]}"; do
  mkdir -p "$out/src/$(dirname "$module")"
  sed '1,20s/^import SolarVerify$/import Verify.Obligation/' "$dir/$module" >"$out/src/$module"
  grep -q '^import Verify.Obligation$' "$out/src/$module" || fail "$module does not import the obligation library"
done

# The library each kind's proofs run in ('core' or 'smt'), and the exports compiled against it.
declare -A libpath compiled
family() { if [[ $1 == smt ]]; then echo smt; else echo core; fi; }
build_family() {
  local fam=$1 lp module mod
  [[ -n ${libpath[$fam]:-} ]] && return 0
  if [[ $fam == core ]]; then
    (cd "$root" && $heavy lake build -KleanMemory=3000 -q VerifyDischarge </dev/null >&2)
    lp="$root/.lake/build/lib/lean"
  else
    (cd "$root/Verify/Reconstruct" && $heavy lake build -KleanMemory=3000 -q </dev/null >&2)
    lp=$(cd "$root/Verify/Reconstruct" && lake env printenv LEAN_PATH)
  fi
  libpath[$fam]=$lp
  mkdir -p "$out/build-$fam"
  for module in "${modules[@]}"; do
    mod=${module%.lean}
    mkdir -p "$out/build-$fam/$(dirname "$mod")"
    (cd "$out/src" && LEAN_PATH="$lp:$out/build-$fam" lean -R "$out/src" -o "$out/build-$fam/$mod.olean" "$out/src/$module" </dev/null >/dev/null) \
      || fail "could not compile the exported module $module"
  done
}
for k in "${kinds[@]}"; do build_family "$(family "$k")"; done

# Certificates written as theorems: the exports they import must be the locked inputs.
declare -A certmod certthm
if [[ " ${kinds[*]} " == *" lean "* ]]; then
  [[ -n ${DISCHARGE_CERTS:-} && -f $DISCHARGE_CERTS ]] || fail "kind lean needs DISCHARGE_CERTS"
  [[ -n ${DISCHARGE_CERT_EXPORTS:-} ]] || fail "kind lean needs DISCHARGE_CERT_EXPORTS"
  for module in "${modules[@]}"; do
    f="$DISCHARGE_CERT_EXPORTS/$module"
    [[ -f $f ]] || continue
    cmp -s "$f" "$dir/$module" || cmp -s "$f" "$out/src/$module" \
      || fail "the certificates import a $module that is not the exported one"
  done
  mapfile -t certrows < <(grep -v '^#' "$DISCHARGE_CERTS" | grep -v '^$' || true)
  for c in "${certrows[@]}"; do
    IFS=$'\t' read -r cid cmod cthm <<<"$c"
    [[ -z ${certthm[$cid]:-} ]] || fail "two certificates for $cid"
    certmod[$cid]=$cmod
    certthm[$cid]=$cthm
  done
fi

# Runs a command and prints its wall time and peak memory as 'MEMTIME seconds megabytes'.
measure() {
  python3 -c '
import resource, subprocess, sys, time
t = time.time()
r = subprocess.run(sys.argv[1:], stdin=subprocess.DEVNULL)
mb = resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss // 1024
sys.stderr.write("MEMTIME %.1f %d\n" % (time.time() - t, mb))
sys.exit(r.returncode)' "$@"
}

results="$out/results.tsv"
printf 'id\trole\tanswer\tkind\tstatus\tseconds\tpeak_mb\taxioms\n' >"$results"
summary="$out/summary.tsv"
printf 'id\trole\tanswer\tstatus\tkinds\n' >"$summary"
pass=0 bad=0
for row in "${unexported[@]}"; do
  [[ -n $row ]] || continue
  IFS=$'\t' read -r name status <<<"$row"
  printf '%s\t-\t-\t-\tfailed: unit not exported (%s)\t0\t-\t-\n' "$name" "$status" >>"$results"
  printf '%s\t-\t-\tfailed: unit not exported (%s)\t-\n' "$name" "$status" >>"$summary"
  bad=$((bad + 1))
done

# One probe: states the obligation, proves it with the kind's certificate, reports its axioms.
probe_one() {
  local k=$1 id=$2 lean=$3 modname=$4 probe proof imports fam lp res code
  local extra=()
  mkdir -p "$out/probe"
  probe="$out/probe/$(echo "$id.$k" | tr -c 'A-Za-z0-9_\n' '_').lean"
  fam=$(family "$k")
  lp="${libpath[$fam]}:$out/build-$fam"
  case $k in
    search) imports="import Verify.Discharge"; proof="by vc_valid" ;;
    smt)
      imports="import Verify.Reconstruct.Tactic"; proof="by vc_smt"
      extra=("--plugin=$root/Verify/Reconstruct/.lake/packages/cvc5/.lake/build/lib/libcvc5_cvc5.so") ;;
    lean)
      if [[ -z ${certthm[$id]:-} ]]; then echo NOCERT; return 0; fi
      imports="import Verify.Discharge
import ${certmod[$id]}"
      proof="${certthm[$id]}"
      lp="${DISCHARGE_CERT_PATH:+$DISCHARGE_CERT_PATH:}$lp" ;;
  esac
  {
    echo "$imports"
    echo "import $modname"
    echo
    echo "theorem obligation : $lean.Valid := $proof"
    echo
    echo "open Lean Elab Command in"
    echo "#eval show CommandElabM Unit from do"
    echo "  let axs ← Lean.collectAxioms (Name.mkSimple \"obligation\")"
    echo "  IO.println s!\"AXIOMS: {String.intercalate \" \" (axs.toList.map toString)}\""
  } >"$probe"
  set +e
  res=$(cd "$out/probe" && LEAN_PATH="$lp" measure timeout "$limit" lean "${extra[@]}" -DmaxHeartbeats=0 -DmaxRecDepth=100000 "$probe" 2>&1)
  code=$?
  set -e
  printf 'CODE %s\n%s\n' "$code" "$res"
}

for row in "${rows[@]}"; do
  IFS=$'\t' read -r module id lean role answer <<<"$row"
  if [[ -n $only && ! $id =~ $only ]]; then
    printf '%s\t%s\t%s\t-\tfailed: skipped\t0\t-\t-\n' "$id" "$role" "$answer" >>"$results"
    printf '%s\t%s\t%s\tfailed: skipped\t-\n' "$id" "$role" "$answer" >>"$summary"
    bad=$((bad + 1)); continue
  fi
  modname=${module%.lean}
  modname=${modname//\//.}
  proving=()
  for k in "${kinds[@]}"; do
    res=$(probe_one "$k" "$id" "$lean" "$modname")
    if [[ $res == NOCERT ]]; then
      printf '%s\t%s\t%s\t%s\tfailed: no certificate\t0\t-\t-\n' "$id" "$role" "$answer" "$k" >>"$results"
      continue
    fi
    code=$(printf '%s\n' "$res" | sed -n '1s/^CODE //p')
    body=$(printf '%s\n' "$res" | sed 1d)
    secs=$(printf '%s\n' "$body" | sed -n 's/^MEMTIME \([^ ]*\) .*/\1/p')
    peak=$(printf '%s\n' "$body" | sed -n 's/^MEMTIME [^ ]* //p')
    axioms=$(printf '%s\n' "$body" | sed -n 's/^AXIOMS: *//p')
    status=proved
    if [[ $code -eq 124 ]]; then
      status="failed: timeout after ${limit}s"
    elif [[ $code -ne 0 ]] || printf '%s\n' "$body" | grep -q 'error'; then
      status="failed: $(printf '%s\n' "$body" | grep -m1 -A2 'error' | tr '\t\n' '  ' | cut -c1-240)"
    elif [[ -z $axioms ]]; then
      status="failed: no axiom report"
    else
      for a in $axioms; do
        [[ " $allowed " == *" $a "* ]] || status="failed: uses axiom $a"
      done
    fi
    printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' "$id" "$role" "$answer" "$k" "$status" "${secs:-0}" "${peak:--}" "${axioms:-none}" >>"$results"
    echo "$k: $status  $id  (${secs:-0}s, ${peak:--} MB)" >&2
    if [[ $status == proved ]]; then
      proving+=("$k")
      [[ ${DISCHARGE_ALL:-0} == 1 ]] || break
    fi
  done
  if [[ ${#proving[@]} -gt 0 ]]; then
    printf '%s\t%s\t%s\tproved\t%s\n' "$id" "$role" "$answer" "$(IFS=,; echo "${proving[*]}")" >>"$summary"
    pass=$((pass + 1))
  else
    printf '%s\t%s\t%s\tfailed\t-\n' "$id" "$role" "$answer" >>"$summary"
    bad=$((bad + 1))
  fi
done

if [[ $((pass + bad - ${#unexported[@]})) -ne ${#rows[@]} ]]; then
  echo "error: ${#rows[@]} exported required obligations, $((pass + bad - ${#unexported[@]})) checked" >&2
  bad=$((want - pass))
fi
for k in "${kinds[@]}"; do
  n=$(awk -F'\t' -v k="$k" '$4 == k && $5 == "proved"' "$results" | wc -l)
  echo "discharge: kind $k proved $n" >&2
done
echo "discharge: $pass of $want required obligations proved, $bad not ($summary)" >&2
[[ $bad -eq 0 && $pass -eq $want ]]

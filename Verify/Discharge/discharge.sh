#!/usr/bin/env bash
# Discharges in the Lean kernel the obligations 'solar-verify --emit-lean DIR' exported. An
# obligation is accepted only when a proof the kernel checks proves '<ob>.Valid' and, per row,
# Lean.collectAxioms reports no axiom but propext, Classical.choice and Quot.sound. Backends are
# untrusted: their sources are never inspected, a step one cannot justify ends as an error or a
# 'sorryAx' in that row's axioms, and the row fails.
#
# Backends (DISCHARGE_BACKENDS, 'name=tactic[@seconds];...', tried in order, each obligation
# stopping at the first that proves it; default 'smt=vc_smt;vc_valid=vc_valid@30'):
#
#   vc_smt    cvc5 refutes the goal through lean-cvc5's plugin and lean-smt rebuilds its proof
#             step by step as a Lean term (Verify/Discharge/Reconstruct).
#   vc_valid  a proof the discharge library searches for itself (Verify/Discharge).
#   cert      a theorem written for the obligation, listed in DISCHARGE_CERTS (see below).
#
# '@seconds' caps that backend's attempt below TIMEOUT_SECONDS. Every backend runs against one
# build, the package in Verify/Discharge/Reconstruct (Lean v4.35.0, lean-smt 6b26285, lean-cvc5
# d19a134), which compiles Verify/Obligation and Verify/Discharge from this repository's sources.
#
# Writes DIR/discharge/results.tsv (one row per required obligation and backend tried, with time,
# memory and axioms), DIR/discharge/summary.tsv (per obligation, the backend that proved it and
# whether its hypotheses are contradictory) and DIR/discharge/inputs.sha256, and exits 0 only
# when every required obligation is proved. A unit that was not exported, a missing, duplicate or
# changed input, an error, a timeout, another axiom, or a semantics that is not the one the
# export was written for is a failure, never a pass.
#
#   Verify/Discharge/discharge.sh DIR [TIMEOUT_SECONDS]
#
# Environment:
#   DISCHARGE_BACKENDS  as above.
#   DISCHARGE_ALL     1: try every backend on every obligation (coverage per backend) rather than
#                     stop at the first that proves it.
#   DISCHARGE_VACUITY 1 (default): per required row, also try '{ ob with goal := .bool false }'
#                     with DISCHARGE_VACUITY_TACTIC (default vc_smt, at most 60 s): 'yes' when the
#                     kernel accepts it with clean axioms (the hypotheses are contradictory, so the
#                     row holds vacuously), 'no' when cvc5 finds a model of them, else 'unknown'.
#                     Informational: it never makes a row pass or fail. 0 skips it ('-').
#   DISCHARGE_ONLY    a regex on obligation ids; the others are skipped (and the run fails).
#   DISCHARGE_LOCK    a sha256sum file of the inputs (as inputs.sha256 is written): the run fails
#                     unless the manifest and every exported module match it.
#   DISCHARGE_CERTS   for backend 'cert': a TSV of 'id<TAB>module<TAB>theorem'. The probe imports
#                     the module and states 'theorem obligation : <ob>.Valid := <theorem>', so the
#                     kernel checks that the theorem proves exactly the exported obligation.
#   DISCHARGE_CERT_PATH     LEAN_PATH entries where those modules are built, searched after the
#                     compiled exports; none may hold a module named like an exported one.
#   DISCHARGE_CERT_EXPORTS  the directory of the exported modules those modules import: each
#                     must equal the locked input (or its copy with the import read as below), and
#                     every exported module must be there.
#   DISCHARGE_SOURCE_ROOT   the repository root the manifest's sources are named relative to:
#                     each must hash as the manifest says, and inputs.sha256 then lists them.
#   DISCHARGE_INPUTS_ONLY   1: check the inputs only, then stop before any Lean runs.
#   DISCHARGE_HEAVY   a command to prefix the library build with (a build-slot wrapper).
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
# The toolchain this repository pins, wherever the script runs lean from.
leanbin=$(cd "$root" && elan which lean 2>/dev/null || command -v lean)
allowed="propext Classical.choice Quot.sound"
pkg="$root/Verify/Discharge/Reconstruct"
plugin="$pkg/.lake/packages/cvc5/.lake/build/lib/libcvc5_cvc5.so"
IFS=';' read -r -a backends <<<"${DISCHARGE_BACKENDS:-smt=vc_smt;vc_valid=vc_valid@30}"
vacuity=${DISCHARGE_VACUITY:-1}
vac_tactic=${DISCHARGE_VACUITY_TACTIC:-vc_smt}
only=${DISCHARGE_ONLY:-}
out="$dir/discharge"
rm -rf "$out"
mkdir -p "$out/src"

fail() { echo "error: $*" >&2; exit 1; }
# name=tactic[@seconds] per backend.
declare -A btactic blimit
bnames=()
for b in "${backends[@]}"; do
  [[ $b =~ ^([A-Za-z0-9_]+)=(vc_smt|vc_valid|cert)(@([0-9]+))?$ ]] || fail "backend $b is not name=vc_smt|vc_valid|cert[@seconds]"
  name=${BASH_REMATCH[1]}
  [[ -z ${btactic[$name]:-} ]] || fail "backend $name listed twice"
  btactic[$name]=${BASH_REMATCH[2]}
  blimit[$name]=$limit
  if [[ -n ${BASH_REMATCH[4]} && ${BASH_REMATCH[4]} -lt $limit ]]; then blimit[$name]=${BASH_REMATCH[4]}; fi
  bnames+=("$name")
done
[[ ${#bnames[@]} -gt 0 ]] || fail "no backend"
case $vac_tactic in vc_smt|vc_valid) ;; *) fail "DISCHARGE_VACUITY_TACTIC is vc_smt or vc_valid" ;; esac
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

# The statement the obligations are read in (Verify/Obligation) may assume nothing beyond the
# kernel. Proof libraries and backends are not read here: each row's axioms decide.
if grep -rnE '\b(sorry|admit|native_decide|bv_decide|ofReduceBool|ofReduceNat|implemented_by|extern|unsafe|axiom|decide \+native)\b' \
    "$root"/Verify/Obligation.lean "$root"/Verify/Obligation; then
  fail "the obligation library uses a construct the kernel does not check"
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
echo "discharge: ${#modules[@]} modules, $want required of $total obligations, ${#unexported[@]} units not exported; backends ${backends[*]}" >&2

# Certificates written as theorems: the exports they were written against must be every locked
# input, and nothing on their LEAN_PATH may hold a module of the export's name, which would shadow
# the compiled input. The probe's LEAN_PATH puts the compiled inputs first in any case.
declare -A certmod certthm
if [[ " ${btactic[*]} " == *" cert "* ]]; then
  [[ -n ${DISCHARGE_CERTS:-} && -f $DISCHARGE_CERTS ]] || fail "backend cert needs DISCHARGE_CERTS"
  [[ -n ${DISCHARGE_CERT_EXPORTS:-} && -d $DISCHARGE_CERT_EXPORTS ]] || fail "backend cert needs DISCHARGE_CERT_EXPORTS"
  for module in "${modules[@]}"; do
    f="$DISCHARGE_CERT_EXPORTS/$module"
    [[ -f $f ]] || fail "the certificates' exports lack $module"
    sed '1,20s/^import SolarVerify$/import Verify.Obligation/' "$dir/$module" | cmp -s "$f" - || cmp -s "$f" "$dir/$module" \
      || fail "the certificates import a $module that is not the exported one"
  done
  IFS=':' read -r -a certpath <<<"${DISCHARGE_CERT_PATH:-}"
  for p in "${certpath[@]}"; do
    [[ -n $p ]] || continue
    for module in "${modules[@]}"; do
      mod=${module%.lean}
      for ext in olean ilean lean; do
        [[ ! -e $p/$mod.$ext ]] || fail "DISCHARGE_CERT_PATH entry $p holds $mod.$ext, which would shadow the exported module"
      done
    done
  done
  mapfile -t certrows < <(grep -v '^#' "$DISCHARGE_CERTS" | grep -v '^$' || true)
  for c in "${certrows[@]}"; do
    IFS=$'\t' read -r cid cmod cthm <<<"$c"
    [[ -n $cid && -n $cmod && -n $cthm ]] || fail "certificate row '$c' is not id<TAB>module<TAB>theorem"
    [[ -z ${certthm[$cid]:-} ]] || fail "two certificates for $cid"
    certmod[$cid]=$cmod
    certthm[$cid]=$cthm
  done
fi

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

# One library for every backend, and the exports compiled against it.
(cd "$pkg" && $heavy lake build -KleanMemory=3000 -q </dev/null >&2) || fail "could not build $pkg"
lp=$(cd "$pkg" && lake env printenv LEAN_PATH)
[[ -f $plugin ]] || fail "missing the cvc5 plugin $plugin"
mkdir -p "$out/build"
for module in "${modules[@]}"; do
  mod=${module%.lean}
  mkdir -p "$out/build/$(dirname "$mod")"
  (cd "$out/src" && LEAN_PATH="$lp:$out/build" "$leanbin" -R "$out/src" -o "$out/build/$mod.olean" "$out/src/$module" </dev/null >/dev/null) \
    || fail "could not compile the exported module $module"
done

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
printf 'id\trole\tanswer\tbackend\tstatus\tseconds\tpeak_mb\taxioms\n' >"$results"
summary="$out/summary.tsv"
printf 'id\trole\tanswer\tstatus\tbackends\tvacuous\n' >"$summary"
pass=0 bad=0
for row in "${unexported[@]}"; do
  [[ -n $row ]] || continue
  IFS=$'\t' read -r name status <<<"$row"
  printf '%s\t-\t-\t-\tfailed: unit not exported (%s)\t0\t-\t-\n' "$name" "$status" >>"$results"
  printf '%s\t-\t-\tfailed: unit not exported (%s)\t-\t-\n' "$name" "$status" >>"$summary"
  bad=$((bad + 1))
done

# One probe: states 'obligation : STMT', proves it with TACTIC, reports its axioms, under LIM s.
probe_one() {
  local tactic=$1 tag=$2 id=$3 stmt=$4 modname=$5 lim=$6 probe proof imports res code
  local extra=() plp="$lp:$out/build"
  mkdir -p "$out/probe"
  probe="$out/probe/$(echo "$id.$tag" | tr -c 'A-Za-z0-9_\n' '_').lean"
  case $tactic in
    vc_valid) imports="import Verify.Discharge"; proof="by vc_valid" ;;
    vc_smt) imports="import Verify.Discharge.Reconstruct.Tactic"; proof="by vc_smt"; extra=("--plugin=$plugin") ;;
    cert)
      if [[ -z ${certthm[$id]:-} ]]; then echo NOCERT; return 0; fi
      imports="import Verify.Discharge
import ${certmod[$id]}"
      proof="${certthm[$id]}"
      plp="$plp${DISCHARGE_CERT_PATH:+:$DISCHARGE_CERT_PATH}" ;;
  esac
  {
    echo "$imports"
    echo "import $modname"
    echo
    echo "theorem obligation : $stmt := $proof"
    echo
    echo "open Lean Elab Command in"
    echo "#eval show CommandElabM Unit from do"
    echo "  let axs ← Lean.collectAxioms (Name.mkSimple \"obligation\")"
    echo "  IO.println s!\"AXIOMS: {String.intercalate \" \" (axs.toList.map toString)}\""
  } >"$probe"
  set +e
  res=$(cd "$out/probe" && LEAN_PATH="$plp" measure timeout "$lim" "$leanbin" "${extra[@]}" -DmaxHeartbeats=0 -DmaxRecDepth=100000 "$probe" 2>&1)
  code=$?
  set -e
  printf 'CODE %s\n%s\n' "$code" "$res"
}

# The verdict on one probe's output: sets status ('proved' or 'failed: <why>'), secs, peak and
# axioms. Proved only on exit 0, no error, an axiom report, and only the allowed axioms.
verdict() {
  local res=$1 lim=$2 code body a
  code=$(printf '%s\n' "$res" | sed -n '1s/^CODE //p')
  body=$(printf '%s\n' "$res" | sed 1d)
  secs=$(printf '%s\n' "$body" | sed -n 's/^MEMTIME \([^ ]*\) .*/\1/p')
  peak=$(printf '%s\n' "$body" | sed -n 's/^MEMTIME [^ ]* //p')
  axioms=$(printf '%s\n' "$body" | sed -n 's/^AXIOMS: *//p')
  status=proved
  if [[ $code -eq 124 ]]; then
    status="failed: timeout after ${lim}s"
  elif [[ $code -ne 0 ]] || printf '%s\n' "$body" | grep -q 'error'; then
    status="failed: $(printf '%s\n' "$body" | grep -m1 -A2 'error' | tr '\t\n' '  ' | cut -c1-240)"
  elif [[ -z $axioms ]]; then
    status="failed: no axiom report"
  else
    for a in $axioms; do
      [[ " $allowed " == *" $a "* ]] || status="failed: uses axiom $a"
    done
  fi
}

for row in "${rows[@]}"; do
  IFS=$'\t' read -r module id lean role answer <<<"$row"
  if [[ -n $only && ! $id =~ $only ]]; then
    printf '%s\t%s\t%s\t-\tfailed: skipped\t0\t-\t-\n' "$id" "$role" "$answer" >>"$results"
    printf '%s\t%s\t%s\tfailed: skipped\t-\t-\n' "$id" "$role" "$answer" >>"$summary"
    bad=$((bad + 1)); continue
  fi
  modname=${module%.lean}
  modname=${modname//\//.}
  proving=()
  for name in "${bnames[@]}"; do
    res=$(probe_one "${btactic[$name]}" "$name" "$id" "$lean.Valid" "$modname" "${blimit[$name]}")
    if [[ $res == NOCERT ]]; then
      printf '%s\t%s\t%s\t%s\tfailed: no certificate\t0\t-\t-\n' "$id" "$role" "$answer" "$name" >>"$results"
      continue
    fi
    verdict "$res" "${blimit[$name]}"
    printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' "$id" "$role" "$answer" "$name" "$status" "${secs:-0}" "${peak:--}" "${axioms:-none}" >>"$results"
    echo "$name: $status  $id  (${secs:-0}s, ${peak:--} MB)" >&2
    if [[ $status == proved ]]; then
      proving+=("$name")
      [[ ${DISCHARGE_ALL:-0} == 1 ]] || break
    fi
  done
  # Vacuity: are the row's hypotheses alone contradictory? It never changes the verdict.
  vac=-
  if [[ $vacuity == 1 ]]; then
    vlim=$(( limit < 60 ? limit : 60 ))
    res=$(probe_one "$vac_tactic" vacuity "$id" "({ $lean with goal := .bool false } : SolarVerify.Vc.Obligation).Valid" "$modname" "$vlim")
    verdict "$res" "$vlim"
    if [[ $status == proved ]]; then vac=yes
    elif [[ $status == *"either it is false"* ]]; then vac=no
    else vac=unknown
    fi
    echo "vacuity: $vac  $id" >&2
  fi
  if [[ ${#proving[@]} -gt 0 ]]; then
    printf '%s\t%s\t%s\tproved\t%s\t%s\n' "$id" "$role" "$answer" "$(IFS=,; echo "${proving[*]}")" "$vac" >>"$summary"
    pass=$((pass + 1))
  else
    printf '%s\t%s\t%s\tfailed\t-\t%s\n' "$id" "$role" "$answer" "$vac" >>"$summary"
    bad=$((bad + 1))
  fi
done

if [[ $((pass + bad - ${#unexported[@]})) -ne ${#rows[@]} ]]; then
  echo "error: ${#rows[@]} exported required obligations, $((pass + bad - ${#unexported[@]})) checked" >&2
  bad=$((want - pass))
fi
for name in "${bnames[@]}"; do
  n=$(awk -F'\t' -v k="$name" '$4 == k && $5 == "proved"' "$results" | wc -l)
  echo "discharge: backend $name proved $n" >&2
done
if [[ $vacuity == 1 ]]; then
  echo "discharge: $(awk -F'\t' '$6 == "yes"' "$summary" | wc -l) rows hold vacuously (summary.tsv, column vacuous)" >&2
fi
echo "discharge: $pass of $want required obligations proved, $bad not ($summary)" >&2
[[ $bad -eq 0 && $pass -eq $want ]]

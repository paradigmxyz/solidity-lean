#!/usr/bin/env bash
# Lane G: every backend on every locked exported row, with separate metrics.
#
#   Verify/Eval/G/discharge_g.sh <Contract> [OUT]
#
# A lane copy of Verify/Discharge/discharge.sh, extended on purpose:
# - the backends are vc_valid, vc_grind (Verify/Eval/G/VcGrind.lean: vc_smt's prep and
#   normalization, then grind), vc_grind_nl (the same after Nonlinear.lean's vc_nl_facts), cert (a
#   theorem in Contracts/<C>/Proofs, when its module is built) and vc_smt only when the cvc5 plugin
#   exists (G_SMT=1 and Verify/Discharge/Reconstruct built); the SMT plugin is neither built nor
#   loaded otherwise;
# - EVERY backend runs on EVERY required row (DISCHARGE_ALL=1 behaviour), never stopping at the
#   first success;
# - per probe it records wall time and peak RSS (the process), the theorem's elaboration time with
#   its kernel check (g_time), the kernel time of the proof with its auxiliary declarations
#   (#kernel_recheck_all) and the proof's size (#proof_stats), and the axioms
#   (Lean.collectAxioms), accepted only when within propext, Classical.choice, Quot.sound;
# - vacuity ({ ob with goal := .bool false }) by vc_grind: yes when proved, else unknown, never
#   "no" (grind gives no model; cvc5's model check stays with discharge.sh).
# Inputs: the frozen version-1 export the repository keeps in Contracts/<C>/Vc (line 2 read back
# as 'import SolarVerify'), checked against Verify/Discharge/frozen/<C>.sha256, the version-1 lock
# whose module lines frozen/v2/<C>.sha256 repeats. Statement: 'theorem obligation : <ob>.Valid',
# exactly as discharge.sh states it. Admission: the slots of scripts/eval/check.sh
# (~/eval-slots, EVAL_SLOTS, EVAL_MEM), one JSON receipt per probe in ~/eval-receipts.jsonl.
# G_LIMIT: seconds per probe (default 60 for vc_valid, 120 otherwise). G_ONLY: a regex on ids. G_BACKENDS: a space-separated subset. G_NEGATE: a regex on ids whose goal
# is negated as test/smt-negatives.sh N4 does (every backend must then fail).
set -euo pipefail
C="$1"
repo="$(cd "$(dirname "$0")/../../.." && pwd)"
out="${2:-$HOME/g-gen/discharge/$C}"
cd "$repo"
[ -f "$HOME/env.sh" ] && source "$HOME/env.sh"
export LEAN_NUM_THREADS=1
allowed="propext Classical.choice Quot.sound"
lock="Verify/Discharge/frozen/$C.sha256"
src="Contracts/$C/Vc"
slots="${EVAL_SLOTS:-2}"; mem="${EVAL_MEM:-5000}"
backends="${G_BACKENDS:-vc_valid vc_grind vc_grind_nl cert}"
plugin="$repo/Verify/Discharge/Reconstruct/.lake/packages/cvc5/.lake/build/lib/libcvc5_cvc5.so"
if [[ ${G_SMT:-0} == 1 ]]; then
  [[ -f $plugin ]] || { echo "error: G_SMT=1 but no cvc5 plugin at $plugin" >&2; exit 1; }
  backends="$backends vc_smt"
fi
fail() { echo "error: $*" >&2; exit 1; }
rm -rf "$out"; mkdir -p "$out/export" "$out/build" "$out/probe"

# The locked input: the export as solar wrote it.
(cd "$src" && find . -type f \( -name '*.lean' -o -name manifest.json \) | sed 's#^\./##') | while read -r f; do
  mkdir -p "$out/export/$(dirname "$f")"
  sed '2s/^import Verify\.Obligation$/import SolarVerify/' "$src/$f" > "$out/export/$f"
done
manifest="$out/export/manifest.json"
[[ $(jq -r .format "$manifest") == solar-verify-lean ]] || fail "not a solar-verify-lean manifest"
mapfile -t modules < <(jq -r '.units[] | select(.module != null) | .module' "$manifest" | sort -u)
(cd "$out/export" && sha256sum manifest.json "${modules[@]}") > "$out/inputs.sha256"
diff <(sort -k2 "$lock") <(sort -k2 "$out/inputs.sha256") >&2 || fail "the inputs are not the ones $lock pins"
smt_have=$(sha256sum Verify/Obligation/Smt.lean | cut -d' ' -f1)
vc_have=$(sha256sum Verify/Obligation/Vc.lean | cut -d' ' -f1)
vc_legacy=$(sed '1s/^import Verify\.Obligation\.Smt$/import SolarVerify.Smt/' Verify/Obligation/Vc.lean | sha256sum | cut -d' ' -f1)
[[ $(jq -r '.lean.smt_sha256' "$manifest") == "$smt_have" ]] || fail "Smt.lean is not the one the export was written for"
vc_want=$(jq -r '.lean.vc_sha256' "$manifest")
[[ $vc_want == "$vc_have" || $vc_want == "$vc_legacy" ]] || fail "Vc.lean is not the one the export was written for"
if grep -rnE '\b(sorry|admit|native_decide|bv_decide|ofReduceBool|ofReduceNat|implemented_by|extern|unsafe|axiom|decide \+native)\b' \
    Verify/Obligation.lean Verify/Obligation; then fail "the obligation library uses a construct the kernel does not check"; fi
mapfile -t rows < <(jq -r '.units[] | select(.module != null) as $u | $u.obligations[] | select(.required) | [$u.module, .id, .lean, .role, .answer] | @tsv' "$manifest")
mapfile -t units < <(jq -r '.units[] | select(.module != null) | [.module, (.obligations | length), ([.obligations[].lean | split(".") | last] | join(" "))] | @tsv' "$manifest")
for u in "${units[@]}"; do
  IFS=$'\t' read -r module n names <<<"$u"
  defined=$(grep -cE '^def ob[0-9]+ : Obligation' "$out/export/$module" || true)
  [[ $defined -eq $n ]] || fail "$module defines $defined obligations, the manifest lists $n"
done

lp=$(lake env printenv LEAN_PATH)
# The exported modules with the library's import path, compiled against the repository's build.
for module in "${modules[@]}"; do
  mod=${module%.lean}
  mkdir -p "$out/src/$(dirname "$module")" "$out/build/$(dirname "$mod")"
  sed '1,20s/^import SolarVerify$/import Verify.Obligation/' "$out/export/$module" > "$out/src/$module"
  if [[ -n ${G_NEGATE:-} ]]; then
    python3 - "$out/src/$module" "$manifest" "$module" "$G_NEGATE" <<'PY'
import json, re, sys
path, manifest, module, rx = sys.argv[1:]
m = json.load(open(manifest))
names = [o["lean"].split(".")[-1] for u in m["units"] if u.get("module") == module
         for o in u["obligations"] if re.search(rx, o["id"])]
lines = open(path).read().split("\n")
cur = None
for i, l in enumerate(lines):
    mm = re.match(r"^def (ob[0-9]+) : Obligation", l)
    if mm: cur = mm.group(1)
    g = re.match(r"^  goal := (.*)$", l)
    if g and cur in names:
        lines[i] = "  goal := .app .not [" + g.group(1) + "]"
        print("negated", module, cur, file=sys.stderr)
open(path, "w").write("\n".join(lines))
PY
  fi
  (cd "$out/src" && LEAN_PATH="$lp:$out/build" lean -R "$out/src" -o "$out/build/$mod.olean" "$out/src/$module" </dev/null >/dev/null) \
    || fail "could not compile the exported module $module"
done

# Runs one Lean file under an admission slot with a timeout; prints the output, then
# 'MEMTIME seconds peak_kb exit'.
admitted() {
  local lim=$1 file=$2 extra=("${@:3}") fd i
  mkdir -p "$HOME/eval-slots"
  while true; do
    for i in $(seq 1 "$slots"); do
      exec {fd}>"$HOME/eval-slots/$i.lock"
      if flock -n "$fd"; then
        set +e
        /usr/bin/time -f 'MEMTIME %e %M %x' -o "$file.time" timeout "$lim" lean -M "$mem" "${extra[@]}" \
          -DmaxHeartbeats=0 -DmaxRecDepth=100000 "$file" < /dev/null 2>&1
        set -e
        flock -u "$fd"; exec {fd}>&-
        grep MEMTIME "$file.time" || echo "MEMTIME $lim 0 124"
        return 0
      fi
      exec {fd}>&-
    done
    sleep 3
  done
}

tactic_of() {
  case $1 in
    vc_valid) echo "by vc_valid" ;;
    vc_grind) echo "by vc_grind" ;;
    vc_grind_nl) echo "by (vc_valid_prep <;> (intros; vc_grind_norm; (try vc_nl_facts); grind))" ;;
    vc_smt) echo "by vc_smt" ;;
  esac
}
limit_of() { case $1 in vc_valid) echo "${G_LIMIT:-60}" ;; *) echo "${G_LIMIT:-120}" ;; esac; }

results="$out/results.tsv"
printf 'id\trole\tbackend\tstatus\twall_s\tpeak_kb\telab_with_kernel_ms\tkernel_all_ms\tproof_dag\taux_dag\taxioms\n' > "$results"
probe() { # backend id stmt modname tag
  local b=$1 id=$2 stmt=$3 modname=$4 tag=$5 file proof imports extra=() lim res cm thm
  file="$out/probe/$(echo "$id.$tag.$b" | tr -c 'A-Za-z0-9_\n' '_').lean"
  imports="import Verify.Discharge
import Verify.Eval.G.VcGrind
import Verify.Eval.G.Kernel
import Verify.Eval.G.Shared"
  if [[ $b == cert ]]; then
    cm="Contracts.$C.Proofs.$modname"
    thm="Contracts.$C.${modname#*.}.$(echo "$stmt" | sed -E 's/.*\.(ob[0-9]+)\.Valid$/\1/')"
    [[ -f .lake/build/lib/lean/$(echo "$cm" | tr . /).olean ]] || { printf 'NOCERT\t%s\n' "$cm"; return 0; }
    imports="$imports
import $cm"
    proof="$thm"
  else
    proof=$(tactic_of "$b")
  fi
  if [[ $b == vc_smt ]]; then imports="$imports
import Verify.Discharge.Reconstruct.Tactic"; extra=("--plugin=$plugin"); fi
  lim=$(limit_of "$b")
  {
    echo "$imports"
    echo "import $modname"
    echo
    echo "g_time \"$id $b\" in"
    echo "theorem obligation : $stmt := $proof"
    echo
    echo "#kernel_recheck_all obligation"
    echo "#proof_stats obligation"
    echo "open Lean Elab Command in"
    echo "#eval show CommandElabM Unit from do"
    echo "  let axs ← Lean.collectAxioms (Name.mkSimple \"obligation\")"
    echo "  IO.println s!\"AXIOMS: {String.intercalate \" \" (axs.toList.map toString)}\""
  } > "$file"
  res=$(cd "$out/probe" && LEAN_PATH="$lp:$out/build" admitted "$lim" "$file" "${extra[@]}")
  echo "$res" > "$file.out"
  printf '%s\n' "$res"
}

parse() { # res -> status wall peak elab kernel dag auxdag axioms
  local res=$1 code wall peak elab kern dag aux axioms status a
  read -r _ wall peak code <<<"$(grep '^MEMTIME' <<<"$res" | tail -1)"
  elab=$(sed -n 's/.*g_time [^:]*: \([0-9.]*\) ms.*/\1/p' <<<"$res" | head -1)
  kern=$(sed -n 's/.*kernel_recheck_all obligation: ok in \([0-9.]*\) ms.*/\1/p' <<<"$res" | head -1)
  dag=$(sed -n 's/.*proof_stats obligation: tree=[0-9]* dag=\([0-9]*\).*/\1/p' <<<"$res" | head -1)
  aux=$(sed -n 's/.*aux_dag=\([0-9]*\).*/\1/p' <<<"$res" | head -1)
  axioms=$(sed -n 's/^AXIOMS: *//p' <<<"$res" | head -1)
  status=proved
  if [[ $code == 124 ]]; then status="failed: timeout"
  elif [[ $code != 0 ]] || grep -q 'error' <<<"$res"; then status="failed: $(grep -m1 -A1 'error' <<<"$res" | tr '\t\n' '  ' | cut -c1-160)"
  elif [[ -z $axioms ]]; then status="failed: no axiom report"
  else for a in $axioms; do [[ " $allowed " == *" $a "* ]] || status="failed: uses axiom $a"; done; fi
  printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s' "$status" "$wall" "$peak" "${elab:--}" "${kern:--}" "${dag:--}" "${aux:--}" "${axioms:-none}"
}

for row in "${rows[@]}"; do
  IFS=$'\t' read -r module id lean role answer <<<"$row"
  if [[ -n ${G_ONLY:-} && ! $id =~ ${G_ONLY} ]]; then continue; fi
  modname=${module%.lean}; modname=${modname//\//.}
  for b in $backends; do
    res=$(probe "$b" "$id" "$lean.Valid" "$modname" row)
    if [[ $res == NOCERT* ]]; then printf '%s\t%s\t%s\tfailed: no certificate module built (%s)\t-\t-\t-\t-\t-\t-\t-\n' "$id" "$role" "$b" "$(cut -f2 <<<"$res")" >> "$results"; continue; fi
    line=$(parse "$res")
    printf '%s\t%s\t%s\t%s\n' "$id" "$role" "$b" "$line" >> "$results"
    printf '{"lane":"G","file":"%s","backend":"%s","status":"%s"}\n' "$id" "$b" "$(cut -f1 <<<"$line" | cut -c1-60 | tr -d '"\\')" >> "${EVAL_RECEIPTS:-$HOME/eval-receipts.jsonl}"
    echo "$b: $(cut -f1 <<<"$line" | cut -c1-80)  $id" >&2
  done
  if [[ ${G_VACUITY:-1} == 1 && -z ${G_NEGATE:-} ]]; then
    res=$(probe vc_grind "$id" "({ $lean with goal := .bool false } : SolarVerify.Vc.Obligation).Valid" "$modname" vacuity)
    line=$(parse "$res")
    vac=unknown; [[ $(cut -f1 <<<"$line") == proved ]] && vac=yes
    printf '%s\t%s\tvacuity(vc_grind)\t%s\t%s\n' "$id" "$role" "$vac" "$(cut -f2- <<<"$line")" >> "$results"
    echo "vacuity: $vac  $id" >&2
  fi
done
for b in $backends; do
  echo "discharge_g $C: $b proved $(awk -F'\t' -v k="$b" '$3 == k && $4 == "proved"' "$results" | wc -l) of $(awk -F'\t' -v k="$b" '$3 == k' "$results" | wc -l)" >&2
done

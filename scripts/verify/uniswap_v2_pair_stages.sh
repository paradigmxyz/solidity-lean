#!/usr/bin/env bash
# UniswapV2Pair's backend stages (first lowered MIR to the final EVM IR, and the bytecode's decoding)
# on the calls of one external function each, checked by the kernel, with the negative controls.
#
#   SOLAR_CERTIFY_DIR=... bash scripts/verify/uniswap_v2_pair_stages.sh [NAME=SIGNATURE ...]
#
# SOLAR_CERTIFY_DIR is a solar checkout with tools/certify/certify.py (--exclude, --cut), with
# target/release/solar built from it (SOLAR overrides). Default scope: uv2_gr=getReserves().
# A scope NAME=SIGNATURE excludes every other external function of UniswapV2Pair: each theorem
# assumes the call's selector is none of theirs, and the stages are cut block by block
# (--cut --joins --no-mir-joins --segment 8) so each module stays within 6 GB.
# Nothing it writes is committed (the stages derive from the GPL-3.0 port): it generates the port
# (uniswap_v2_gen.sh), compiles the flat UniswapV2Pair with -Ogas --evm-version osaka, checks that
# -Zemit-lean-stages leaves the runtime bytecode as it is and the manifest's hashes, writes
# Certified/NAME/{gen,Proofs} with certify.py, removes NAME's compiled modules, builds one module at a
# time (-KleanMemory=6000), scans the generated files and
# requires every theorem's axioms within propext, Classical.choice and Quot.sound. Receipts (command,
# exit code, wall time, peak RSS) go to .lake/pair-stages/receipts.log.
# NEGATIVES=1 also builds the mutants of the first scope (Certified/<NAME>neg, <NAME>negb) and requires
# each mutated proof to fail with a mismatch, not a timeout.
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/../.."
: "${SOLAR_CERTIFY_DIR:?a solar checkout with tools/certify/certify.py}"
solar="${SOLAR:-$SOLAR_CERTIFY_DIR/target/release/solar}"
certify="$SOLAR_CERTIFY_DIR/tools/certify/certify.py"
scopes=("$@"); [[ ${#scopes[@]} -gt 0 ]] || scopes=("uv2_gr=getReserves()")
out=.lake/pair-stages; mkdir -p "$out"; rec="$out/receipts.log"
export LEAN_NUM_THREADS=1
receipt() { # receipt CMD...: run, log the receipt, return its exit code
  local t0=$(date +%s) rc=0 peak
  /usr/bin/env python3 - "$rec" "$@" <<'PY' || rc=$?
import resource, subprocess, sys, time, shlex
log, cmd = sys.argv[1], sys.argv[2:]
t = time.time(); p = subprocess.run(cmd, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
rss = resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss // 1024
out = p.stdout.decode(errors="replace")
open(log + ".out", "a").write(f"===== {shlex.join(cmd)}\n{out}\n")
line = f"{time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime())} | {shlex.join(cmd)} | exit {p.returncode} | {time.time()-t:.0f} s | peak {rss} MB"
open(log, "a").write(line + "\n"); print(line)
for l in [l for l in out.splitlines() if 'error' in l][:3]: print("   ", l[:240])
sys.exit(p.returncode)
PY
  return $rc
}
cap() { python3 -c 'import sys; print("".join(p[:1].upper() + p[1:] for p in sys.argv[1].split("_")))' "$1"; }

env -u SOLAR_CERTIFY_DIR scripts/verify/uniswap_v2_gen.sh > /dev/null
work="$out/compile"; rm -rf "$work"; mkdir -p "$work"
cp scripts/verify/uniswap-v2/UniswapV2Pair.sol "$work/uv2pb.sol"
( cd "$work"
  "$solar" uv2pb.sol -Ogas --evm-version osaka --emit=bin-runtime > plain.json 2>/dev/null
  "$solar" uv2pb.sol -Ogas --evm-version osaka --emit=bin-runtime -Zemit-lean-stages=gen > out.json 2>/dev/null
  "$solar" uv2pb.sol --emit=hashes > hashes.json 2>/dev/null
  python3 - <<'PY'
import hashlib, json, pathlib
k = "uv2pb.sol:UniswapV2Pair"
a = json.load(open("plain.json"))["contracts"][k]["bin-runtime"]
b = json.load(open("out.json"))["contracts"][k]["bin-runtime"]
d = pathlib.Path("gen/UniswapV2Pair"); m = json.loads((d / "manifest.json").read_text())
assert a == b, "-Zemit-lean-stages changed the bytecode"
assert m["bytecode"] == a and m["bytecode_sha256"] == hashlib.sha256(bytes.fromhex(a)).hexdigest()
for s in m["stages"]:
    assert s["sha256"] == hashlib.sha256((d / s["file"]).read_bytes()).hexdigest(), s["file"]
print(f"runtime bytecode {len(a)//2} bytes, sha256 {m['bytecode_sha256']}, {len(m['stages'])} stages, compiler {m['compiler']}")
PY
)
first=${scopes[0]%%=*}
gen="Certified/$first/gen/UniswapV2Pair"
rm -rf "Certified/$first/gen"; mkdir -p "Certified/$first/gen"; cp -r "$work/gen/UniswapV2Pair" "Certified/$first/gen/"
# excludes SIGNATURE: --exclude SELECTOR=SIG for every other external function of the Pair.
excludes() {
  python3 - "$work/hashes.json" "$1" <<'PY'
import json, sys
h = json.load(open(sys.argv[1]))["contracts"]["uv2pb.sol:UniswapV2Pair"]["hashes"]
assert sys.argv[2] in h, f"no external function {sys.argv[2]}"
for sig, sel in sorted(h.items()):
    if sig != sys.argv[2]:
        print(f"--exclude\n{sel}={sig}")
PY
}
# stages: the manifest's stages in pipeline order, without the bytecode.
stages() {
  python3 -c 'import json, sys; print(" ".join(s["file"][:-5] for s in json.load(open(sys.argv[1]))["stages"] if s["pass"] != "assemble"))' "$gen/manifest.json"
}
# proof_modules NAME: every module under Certified/NAME/Proofs/Runs, each stage's parts first.
proof_modules() {
  local d="Certified/$1/Proofs/Runs" s
  for s in $(stages); do
    [[ -f "$d/$s.lean" ]] || continue
    if [[ -d "$d/$s" ]]; then
      [[ ! -f "$d/$s/Defs.lean" ]] || echo "$1.Proofs.Runs.$s.Defs"
      ls "$d/$s" | grep -v '^Defs.lean$' | sed 's/\.lean$//' | sort -V | sed "s/^/$1.Proofs.Runs.$s./"
    fi
    echo "$1.Proofs.Runs.$s"
  done
}
for spec in "${scopes[@]}"; do
  IFS='=' read -r name sig <<<"$spec"
  mapfile -t ex < <(excludes "$sig")
  ns="SolarTV.Milestone.$(cap "$name")"
  rm -rf "Certified/$name/Proofs" ".lake/build/lib/lean/$name" ".lake/build/ir/$name"
  python3 "$certify" "$gen" --gen-module "$first.gen.UniswapV2Pair" --proof-dir "Certified/$name/Proofs" \
    --proof-module "$name.Proofs" --namespace "$ns" --label "$name" --cut --joins --no-mir-joins --segment 8 "${ex[@]}" > /dev/null
  bash "$SOLAR_CERTIFY_DIR/tools/certify/audit.sh" scan "Certified/$name"
  if [[ "$name" == "$first" ]]; then
    mapfile -t gm < <(cd Certified && ls "$name"/gen/UniswapV2Pair/*.lean | sed 's|\.lean$||; s|/|.|g')
    receipt lake build -KleanMemory=3000 "${gm[@]}"
  fi
  mapfile -t pm < <(proof_modules "$name")
  [[ ${#pm[@]} -gt 1 ]] || { echo "error: no run proofs under Certified/$name/Proofs/Runs" >&2; exit 1; }
  for m in "${pm[@]}"; do
    receipt lake build -KleanMemory=6000 "$m"
  done
  receipt lake build -KleanMemory=6000 "$name.Proofs.Stages"
  [[ "$name" != "$first" ]] || receipt lake build -KleanMemory=6000 "$name.Proofs.Assembly"
  audit="Certified/$name/Audit.lean"
  { echo "import $name.Proofs.Stages"; [[ "$name" != "$first" ]] || echo "import $name.Proofs.Assembly"
    grep -rhoE '^theorem [A-Za-z0-9_]+' "Certified/$name/Proofs" | awk '{print $2}' | sort -u | sed "s/^/#print axioms $ns./"
    echo "#check @$ns.${name}_mir_to_evmir"; } > "$audit"
  report="$(lake env lean -M 6000 "$audit" 2>&1)"
  joined="$(awk '/^ /{printf "%s", $0; next} NR > 1 {print ""} {printf "%s", $0} END {print ""}' <<<"$report")"
  echo "$joined" > "$out/audit-$name.txt"
  bad="$(grep 'depends on axioms' <<<"$joined" | sed -E 's/.*depends on axioms: \[(.*)\]/\1/' | tr ',' '\n' | tr -d ' ' | grep -v -x -E 'propext|Classical\.choice|Quot\.sound' || true)"
  n="$(grep -c -E 'depends on axioms|does not depend on any axioms' <<<"$joined")"; want="$(grep -c '^#print' "$audit")"
  ! grep -q -E 'sorryAx|^error' <<<"$joined" || { echo "error: $name audit reports sorry or an error" >&2; exit 1; }
  [[ -z "$bad" && "$n" -eq "$want" ]] || { echo "error: $name audit: $n of $want, beyond the three: $bad" >&2; exit 1; }
  echo "$name: $n theorems audited, axioms within propext, Classical.choice, Quot.sound"
done
if [[ -n "${NEGATIVES:-}" ]]; then
  IFS='=' read -r name sig <<<"${scopes[0]}"
  mapfile -t ex < <(excludes "$sig")
  python3 scripts/verify/uniswap_v2_pair_mutants.py "$name"
  for d in "${name}neg" "${name}negb"; do
    mapfile -t gm < <(cd Certified && ls "$d"/gen/UniswapV2Pair/*.lean | sed 's|\.lean$||; s|/|.|g')
    rm -rf ".lake/build/lib/lean/$d" ".lake/build/ir/$d" "Certified/$d/Proofs"
    python3 "$certify" "Certified/$d/gen/UniswapV2Pair" --gen-module "$d.gen.UniswapV2Pair" --proof-dir "Certified/$d/Proofs" \
      --proof-module "$d.Proofs" --namespace "SolarTV.Milestone.$(cap "$d")" --label "$d" --cut --joins --no-mir-joins --segment 8 "${ex[@]}" > /dev/null
    receipt lake build -KleanMemory=3000 "${gm[@]}"
  done
  last="$(stages | awk '{print $NF}')"
  for m in "${name}neg.Proofs.Runs.Mir1" "${name}neg.Proofs.Runs.$last" "${name}negb.Proofs.Assembly"; do
    if receipt lake build -KleanMemory=6000 "$m"; then echo "error: the mutant $m checks" >&2; exit 1; fi
    tail -c 20000 "$rec.out" | grep -q -E "runs end in different results|Tactic .decide. proved that the proposition" ||
      { echo "error: $m failed without a mismatch" >&2; exit 1; }
    echo "$m: refused by mismatch"
  done
fi

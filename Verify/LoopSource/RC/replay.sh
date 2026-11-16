#!/usr/bin/env bash
# Replay the loop route from a clean checkout of this repository.
#
#   bash Verify/LoopSource/RC/replay.sh SOLAR_VERIFY Z3 OUT_DIR
#
# SOLAR_VERIFY: solar-verify built from paradigmxyz/solar fd53f637ef69065f897a1760726c254ccd7f9aa2
# (cargo build -p solar-verify). Z3: a z3 binary. Run from the repository root with lake on PATH
# (LEAN_NUM_THREADS=1 recommended). Regenerates every pinned artifact into OUT_DIR, compares each
# with the committed file and Verify/LoopSource/RC/MANIFEST.json, builds the Lean modules (the
# Receipt module checks theorems, axioms and dependencies), runs the negatives, and writes
# OUT_DIR/replay.json. Exit 0 only when every check passes.
set -uo pipefail
# Resource admission: rerun under a recorder of wall time and the peak RSS of every child, and
# admit the run only within the budget (8 GiB peak RSS, 3600 s wall).
if [ -z "${REPLAY_INNER:-}" ]; then
  mkdir -p "$3"
  REPLAY_INNER=1 python3 - "$0" "$@" <<'PY'
import json, os, resource, subprocess, sys, time
script, args = sys.argv[1], sys.argv[2:]
t0 = time.time()
code = subprocess.call(["bash", script] + args)
wall = round(time.time() - t0, 1)
rss = resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss
out = os.path.join(args[2], "replay.json")
r = json.load(open(out)) if os.path.exists(out) else {}
budget = {"max_rss_kb": 8 * 1024 * 1024, "wall_s": 3600}
r["resources"] = {"wall_s": wall, "max_rss_kb": rss, "budget": budget,
                  "admitted": rss <= budget["max_rss_kb"] and wall <= budget["wall_s"]}
r["exit"] = code if r["resources"]["admitted"] else (code or 5)
json.dump(r, open(out, "w"), indent=1)
print(json.dumps(r))
sys.exit(r["exit"])
PY
  exit $?
fi
V=$(readlink -f "$1"); Z=$(readlink -f "$2"); OUT=$(mkdir -p "$3" && readlink -f "$3")
R=Verify/LoopSource/RC; ROOT=$(pwd); export SOLAR_VERIFY_Z3=$Z
fails=0; log() { echo "$*" | tee -a "$OUT/replay.log"; }
check() { local name=$1; shift; if "$@" >> "$OUT/replay.log" 2>&1; then log "PASS $name"; else log "FAIL $name (exit $?)"; fails=$((fails+1)); fi; }
expect() { local want=$1 name=$2; shift 2; "$@" >> "$OUT/replay.log" 2>&1; local got=$?; if [ "$got" = "$want" ]; then log "PASS $name (exit $got)"; else log "FAIL $name (exit $got, want $want)"; fails=$((fails+1)); fi; }
: > "$OUT/replay.log"
mf() { python3 -c "import json,sys;d=json.load(open('$R/MANIFEST.json'));print(eval(sys.argv[1]))" "$1"; }
# 1. inputs and map are the pinned bytes
for f in inputs/Counter.sol inputs/Gcd.sol Counter/Counter.loop-heads.json; do
  check "sha256 $f" test "$(sha256sum $R/$f | cut -d' ' -f1)" = "$(mf "d['files']['$f']")"
done
check "sha256 of every module in MANIFEST.json" python3 -c "
import json, hashlib, sys
m = json.load(open('$R/MANIFEST.json'))['modules']
bad = [f for f, h in m.items() if hashlib.sha256(open(f, 'rb').read()).hexdigest() != h]
print('mismatch:', bad); sys.exit(1 if bad else 0)"
check "spec lines of Counter.sol" test "$(grep '@custom:' $R/inputs/Counter.sol | sha256sum | cut -d' ' -f1)" = "$(mf "d['spec']['Counter.sol']")"
# 2. re-emit with the pinned compiler
mkdir -p "$OUT/counter" "$OUT/gcd"; cp $R/inputs/Counter.sol "$OUT/counter/"; cp $R/inputs/Gcd.sol "$OUT/gcd/"
check "emit Counter.bump" bash -c "cd '$OUT/counter' && '$V' --no-infer --only Counter.bump --emit-lean emit Counter.sol"
check "emit Gcd.gcd" bash -c "cd '$OUT/gcd' && '$V' --no-infer --only Gcd.gcd --emit-lean emit Gcd.sol"
for u in counter gcd; do
  check "manifest $u: compiler, options, sources, VC hashes" python3 - "$OUT/$u/emit/manifest.json" "$u" <<'PY'
import json, sys
m = json.load(open(sys.argv[1])); p = json.load(open('Verify/LoopSource/RC/MANIFEST.json'))['vc'][sys.argv[2]]
got = {"compiler": m["compiler"], "options": m["options"], "sources": m["sources"], "smt_sha256": m["lean"]["smt_sha256"], "vc_sha256": m["lean"]["vc_sha256"], "answers": {q["id"]: q["answer"] for q in m["units"][0]["obligations"]}}
want = {k: p[k] for k in got}
assert got == want, (got, want)
PY
done
check "loop heads: committed map current" bash -c "cd '$OUT/counter' && cp '$ROOT/$R/Counter/Counter.loop-heads.json' . && '$V' --no-infer --check-loop-heads Counter.loop-heads.json Counter.sol"
check "loop heads: re-emitted map identical" bash -c "cd '$OUT/counter' && '$V' --no-infer --emit-loop-heads heads.json Counter.sol && cmp heads.json '$ROOT/$R/Counter/Counter.loop-heads.json'"
# 3. regenerate the Lean modules and compare with the committed ones
for u in Counter:Counter.bump:counter Gcd:Gcd.gcd:gcd; do IFS=: read N F D <<< "$u"
  check "dump $N Script.lean identical" bash -c "'$V' --no-infer --only $F --dump-lean '$OUT/$N.Script.lean' --lean-namespace Verify.LoopSource.RC.$N '$OUT/$D/'*.sol && cmp '$OUT/$N.Script.lean' $R/$N/Script.lean"
  check "gen_loopvc $N Obligations.lean identical" bash -c "python3 Verify/LoopSource/gen_loopvc.py '$OUT/$D/emit/manifest.json' Verify.LoopSource.RC.$N.Script Verify.LoopSource.RC.$N '$OUT/$N.Obligations.lean' && cmp '$OUT/$N.Obligations.lean' $R/$N/Obligations.lean"
done
check "gen_loopmap Map.lean identical" bash -c "python3 Verify/LoopSource/gen_loopmap.py $R/Counter/Counter.loop-heads.json '$OUT/counter/emit/manifest.json' $R/inputs/Counter.sol $R/Counter/Obligations.lean Verify.LoopSource.RC.Counter '$OUT/Map.lean' && cmp '$OUT/Map.lean' $R/Counter/Map.lean"
# 4. build: the Receipt module checks the theorems, their axioms and what body_runs_vc rests on
check "lake build Verify.LoopSource.RC.Receipt" lake -R build Verify.LoopSource.RC.Receipt
# 4b. the headline is stated apart from the proof; a changed statement must not check
cat > "$OUT/neg_headline.lean" <<'EOF'
import Verify.LoopSource.RC.Headline
import Contracts.VerifyCounter.LoopVC
open SolidCore.Solidity.Source SolidCore.Refinement SolidCore.Refinement.Generic
open SolidCore.Refinement.Generic.Loop Contracts.VerifyCounter.Source
-- The headline with a smaller fuel bound than the proof gives: must fail to check.
example : ∀ (ev : List EventDecl) (tbl : FunctionTable) (fn : FunctionDef),
    fn.body = bumpBody → initState fn = S0 →
      ∀ fuel : Nat, 2 ^ 256 + 7 ≤ fuel → BodyRuns (env ev tbl) fuel fn bumpBr :=
  Contracts.VerifyCounter.LoopVC.body_runs_vc
EOF
expect 1 "negative changed headline rejected by the kernel" lake env lean "$OUT/neg_headline.lean"
# 5. negatives
mkdir -p "$OUT/neg"
python3 - "$OUT/neg" <<'PY'
import json, copy, sys
h = json.load(open('Verify/LoopSource/RC/Counter/Counter.loop-heads.json')); o = sys.argv[1]
def bump(x): return [g for g in x['functions'] if g['function'] == 'Counter.bump'][0]['loops'][0]['vars']
def save(n, x): json.dump(x, open(f'{o}/{n}.json', 'w'), indent=2)
a = copy.deepcopy(h); a['compiler'] = a['compiler'].replace('fd53f637', 'c09510a3'); save('stale_compiler', a)
b = copy.deepcopy(h); b['source']['sha256'] = '0' * 64; save('stale_source', b)
c = copy.deepcopy(h); bump(c)[0]['slot'] = '1'; save('wrong_slot', c)
d = copy.deepcopy(h); bump(d)[1]['name'] = 'n'; save('swapped_var', d)
PY
G="python3 Verify/LoopSource/gen_loopmap.py"
for n in stale_compiler stale_source; do expect 3 "negative $n rejected by gen_loopmap" $G "$OUT/neg/$n.json" "$OUT/counter/emit/manifest.json" $R/inputs/Counter.sol $R/Counter/Obligations.lean MapNeg "$OUT/neg/$n.Map.lean"; done
cp $R/inputs/CounterBadInit.sol "$OUT/neg/Counter.sol"; cp $R/Counter/Counter.loop-heads.json "$OUT/neg/"
expect 1 "negative stale source rejected by --check-loop-heads" bash -c "cd '$OUT/neg' && '$V' --no-infer --check-loop-heads Counter.loop-heads.json Counter.sol"
for n in wrong_slot swapped_var; do
  $G "$OUT/neg/$n.json" "$OUT/counter/emit/manifest.json" $R/inputs/Counter.sol $R/Counter/Obligations.lean MapNeg "$OUT/neg/$n.Map.lean" >> "$OUT/replay.log" 2>&1
  { echo "import Contracts.VerifyCounter.SourceLoop"; sed -n '/^import Verify.LoopSource.LoopMap/,$p' "$OUT/neg/$n.Map.lean"
    printf '\nopen SolidCore.Refinement.Generic Contracts.VerifyCounter.Source SolidCore.Verify.LoopMap\n'
    for l in 'count@17|.init 0' 'n@21|.arg 0' 'i@28|.arg 1' 'count@27|.arg 2'; do echo "example : MapNeg.M.word headerS \"${l%%|*}\" = some (${l#*|}) := by decide"; done; } > "$OUT/neg/neg_$n.lean"
  expect 1 "negative $n rejected by the kernel" lake env lean "$OUT/neg/neg_$n.lean"
done
# 6. the gate: every outcome per loop, nonvacuity required
GT="python3 Verify/LoopSource/loopgate.py $V $Z"
for c in Counter:0 CounterBadInit:1 CounterBadPres:1 CounterBadDecr:1 CounterBadExit:1; do IFS=: read n w <<< "$c"; expect $w "gate $n" $GT $R/inputs/$n.sol Counter.bump "$OUT/gate/$n" --assume '(>= |n@21| 3)' --assume '(>= |count@17| 5)'; done
for c in Gcd:0 GcdBadInit:1 GcdBadPres:1 GcdBadDecr:1 GcdBadExit:1 GcdVacuous:4; do IFS=: read n w <<< "$c"; expect $w "gate $n" $GT $R/inputs/$n.sol Gcd.gcd "$OUT/gate/$n" --assume '(= |a@19| 12)' --assume '(= |b@20| 18)'; done
python3 -c "import json;print(json.dumps({'fails': $fails, 'checks': $(grep -c '^PASS\|^FAIL' "$OUT/replay.log")}))" | tee "$OUT/replay.json"
[ $fails = 0 ]

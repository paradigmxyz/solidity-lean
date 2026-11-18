#!/usr/bin/env bash
# T4 box session: Counter Resources + Lifecycle, producer built from the freeze head, --fresh replay.
# Usage: box-v4.sh STEP [MODULE...]
#   STEP = 0 setup | 3d Source diagnosis (capped) | 1 producer | 2 lifecycle | 3 resources
#          | 4 fresh (MODULE...) | 5 audit | 6 ctx build | 6c composed (bound lifecycle) | 7 ctx fresh
#          | 8 ctx audit
# One box, at most 2 h, run in this order:
#   0, 3d, 1, 3, 4 Verify.LoopSource.Equiv.Counter.Resources Verify.LoopSource.Equiv.Counter.Neg,
#   6, 6c, 7, 8, 2, 4 CounterRun.Lifecycle, 5
# A step whose build dies in Contracts.VerifyCounter.Source with Lean's memory exception records
# itself OPEN (not FAIL) in steps-open.json; the steps after it that need that module are OPEN too.
# A step not started by 1h50 after step 0 began is recorded OPEN (steps-open.json) and the box is
# deleted. Each step writes /home/ubuntu/rcpt/<step>[-<n>]/ and exits nonzero on any failure; the
# operator copies /home/ubuntu/rcpt off the box (copy_files) after every step.
set -euo pipefail
SOLAR_HEAD=${SOLAR_HEAD:-92c59b665bbd7ce17b39dd2317e5e66379408528}  # freeze head (or 41f30a4a4f64d4f28849332aef30d26487144e2e)
LEAN_REV=96f869131d96c88af941a765b03b005e23424e3f                    # [secret GIT_AUTHOR_NAME]/t4-loop-equiv-v4
CTX_REV=25f481785bd349753c345f72d3db013b2d7e6220                     # [secret GIT_AUTHOR_NAME]/t4-ctx-bridge
BIND_SOLAR=ed238a92ea60b39f38cdb56d1e8762e407efdb3f                  # [secret GIT_AUTHOR_NAME]/t7-lifecycle-bind
CTX_BASE=c6295eeb                                                    # [secret GIT_AUTHOR_NAME]/lc-ctor-args (on the pin)
LEAN_PIN=334d1d924f8f6c29ac827fd81d1cc739721b479a                    # tools/certify/solidity-lean.rev at the head
EXPECT_RT=509845d3b18cf635ec7ee9b1a9d225cfeec995099a9f5e0d55f27ae6559f411d
EXPECT_STAGE0=0c544806b2b5013d2c38ce859b167d03e3c19162b53b2ab8f5319b3d55bd3003
MEM_MAX=${MEM_MAX:-48G}
W=/home/ubuntu; STEP=$1; shift
R=$W/rcpt/$STEP; n=1; while [ -e "$R" ]; do n=$((n+1)); R=$W/rcpt/$STEP-$n; done; mkdir -p "$R"
# The 1h50 budget, from step 0's start.
[ "$STEP" = 0 ] && date +%s > $W/rcpt/.t0
if [ "$STEP" != 0 ] && [ $(( $(date +%s) - $(cat $W/rcpt/.t0) )) -ge 6600 ]; then
  echo "{\"step\":\"$STEP $*\",\"status\":\"OPEN\",\"reason\":\"not started by 1h50\"}" >> $W/rcpt/steps-open.json
  echo "budget spent: step $STEP recorded OPEN"; exit 9
fi
export PATH=$HOME/.elan/bin:$HOME/.cargo/bin:$HOME/.local/bin:$PATH LEAN_NUM_THREADS=${LEAN_NUM_THREADS:-4}
exec > >(tee -a "$R/step.log") 2>&1

# Hatch variables must be unset in every step.
for v in CERTIFY_ALLOW_UNPINNED CERTIFY_REPLAY_TRUST_UPSTREAM CERTIFY_SKIP_BUILD CERTIFY_ALLOW_FOREIGN_SOLAR; do
  if [ -n "${!v+x}" ]; then echo "HATCH $v is set: refusing"; exit 3; fi
done
echo '{"hatch_unset":["CERTIFY_ALLOW_UNPINNED","CERTIFY_REPLAY_TRUST_UPSTREAM","CERTIFY_SKIP_BUILD","CERTIFY_ALLOW_FOREIGN_SOLAR"]}' > "$R/hatch.json"

# scoped TAG CMD...: run CMD in its own transient cgroup scope (MemoryMax=$MEM_MAX). Inside the
# scope, after CMD returns, read that scope's memory.max, memory.peak and memory.events and write
# TAG.json with the exit code and wall time; CMD's output goes to TAG.out.
scoped() {
  local tag=$1; shift
  set +e
  sudo systemd-run --scope --quiet -p MemoryMax=$MEM_MAX --uid="$(id -u)" --gid="$(id -g)" \
    env PATH="$PATH" HOME="$HOME" LEAN_NUM_THREADS="$LEAN_NUM_THREADS" RCPT="$R" TAG="$tag" \
    bash -c '
      t0=$(date +%s.%N); "$@" > "$RCPT/$TAG.out" 2>&1; rc=$?
      cg=/sys/fs/cgroup$(cut -d: -f3 /proc/self/cgroup)
      python3 - "$rc" "$t0" "$cg" "$TAG" > "$RCPT/$TAG.json" <<"EOF"
import sys,time,json
rc,t0,cg,tag=int(sys.argv[1]),float(sys.argv[2]),sys.argv[3],sys.argv[4]
rd=lambda f: open(cg+"/"+f).read().strip()
ev=dict(l.split() for l in rd("memory.events").splitlines())
print(json.dumps({"tag":tag,"exit":rc,"wall_s":round(time.time()-t0,1),"cgroup":cg,
  "memory.max":rd("memory.max"),"memory.peak_bytes":int(rd("memory.peak")),"memory.events":ev}))
EOF
      exit $rc' _ "$@"
  local rc=$?; set -e
  cat "$R/$tag.json"
  # MemoryMax must be in force: a scope with memory.max "max" is not a finite run.
  if python3 -c "import json,sys;sys.exit(0 if json.load(open('$R/$tag.json'))['memory.max']=='max' else 1)"; then
    echo "memory.max is 'max': MemoryMax not in force"; exit 10
  fi
  return $rc
}

# srcdied TAG: the build's log shows Contracts.VerifyCounter.Source died of Lean's memory exception.
# Exactly that signature: the only failed module (✖ lines and lake's failure list) is
# Contracts.VerifyCounter.Source, its block reports Lean's memory_exception and exit 134. Anything else is FAIL.
srcdied() {
  local f="$R/$1.out"
  [ "$(grep -c '^✖ ' "$f")" = 1 ] && grep -q '^✖ \[[0-9/]*\] Building Contracts.VerifyCounter.Source ' "$f" || return 1
  [ "$(sed -n '/^Some required targets logged failures:/,$p' "$f" | grep -c '^- ')" = 1 ] || return 1
  sed -n '/^Some required targets logged failures:/,$p' "$f" | grep -qx -- '- Contracts.VerifyCounter.Source' || return 1
  sed -n '/^✖ .*Building Contracts.VerifyCounter.Source /,/^error: Lean exited with code/p' "$f" > "$f.srcblock"
  grep -q 'lean::memory_exception' "$f.srcblock" && grep -qx 'error: Lean exited with code 134' "$f.srcblock"
}
open_step() { echo "{\"step\":\"$STEP $*\",\"status\":\"OPEN\",\"reason\":\"Contracts.VerifyCounter.Source memory_exception\"}" >> $W/rcpt/steps-open.json; }

case $STEP in
0) # setup: toolchains and both checkouts at exact commits
  sudo apt-get update -qq && sudo apt-get install -y -qq git zstd build-essential pkg-config >/dev/null
  command -v cargo >/dev/null || curl -sSf https://sh.rustup.rs | sh -s -- -y --profile minimal >/dev/null
  command -v elan >/dev/null || curl -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y --default-toolchain none >/dev/null
  command -v uv >/dev/null || curl -LsSf https://astral.sh/uv/install.sh | sh >/dev/null
  uv python install 3.14 >/dev/null
  git clone -q https://github.com/paradigmxyz/solar.git $W/solar && git -C $W/solar checkout -q $SOLAR_HEAD
  git clone -q https://github.com/paradigmxyz/solidity-lean.git $W/sl && git -C $W/sl checkout -q $LEAN_REV
  git clone -q https://github.com/paradigmxyz/solidity-lean.git $W/sl2 && git -C $W/sl2 checkout -q $CTX_REV
  git -C $W/sl2 merge-base --is-ancestor $LEAN_PIN $CTX_REV || { echo "ctx branch is not on the pin"; exit 4; }
  if git -C $W/sl2 diff --name-only $CTX_BASE $CTX_REV | grep -v '^Verify/LoopSource/'; then echo "ctx branch touches other paths"; exit 4; fi
  [ "$(git -C $W/solar show $SOLAR_HEAD:tools/certify/solidity-lean.rev)" = "$LEAN_PIN" ] || { echo "pin mismatch"; exit 4; }
  git -C $W/sl merge-base --is-ancestor $LEAN_PIN $LEAN_REV || { echo "lean branch is not on the pin"; exit 4; }
  if git -C $W/sl diff --name-only $LEAN_PIN $LEAN_REV | grep -v '^Verify/LoopSource/'; then echo "lean branch touches other paths"; exit 4; fi
  # Self-test of step 2's refusal regex on the committed kernel refusal.
  python3 - $W/sl/Verify/LoopSource/Equiv/Counter/run-v3/LifecycleBad.err <<'EOF' || { echo "refusal regex self-test failed"; exit 12; }
import re,sys
log=open(sys.argv[1]).read()
sys.exit(0 if re.search(r"\(kernel\) declaration type mismatch, '[^']*checkB_eq'", log) else 1)
EOF
  echo '{"refusal_regex_selftest":"match"}' > $R/selftest.json
  (cd $W/sl && elan toolchain install "$(cat lean-toolchain)" && lake exe cache get) > $R/cache.log 2>&1
  (cd $W/sl2 && lake exe cache get) >> $R/cache.log 2>&1
  mkdir -p $HOME/.cache/solc
  curl -sSfL -o $HOME/.cache/solc/solc-0.8.35 https://github.com/argotorg/solidity/releases/download/v0.8.35/solc-static-linux
  chmod +x $HOME/.cache/solc/solc-0.8.35
  { echo "solar $SOLAR_HEAD"; echo "lean $LEAN_REV"; echo "pin $LEAN_PIN"; sha256sum $HOME/.cache/solc/solc-0.8.35; } > $R/inputs.txt
  # Host limits that Lean's -M and interpreter checks depend on, for comparison with a passing host.
  { ulimit -a; echo "nproc $(nproc)"; grep -E 'MemTotal|MemAvailable|CommitLimit|Committed_AS' /proc/meminfo
    cat /proc/sys/vm/overcommit_memory /proc/sys/vm/max_map_count; uname -r; findmnt -no FSTYPE,OPTIONS $W
  } > $R/host-limits.txt 2>&1 ;;

1) # producer: solar built from the freeze head; its embedded commit must equal the driver commit
  cd $W/solar
  scoped build-solar cargo build --locked --release --bin solar
  B=$W/solar/target/release/solar
  # The embedded commit is solar --version's "Commit SHA:" line; at least 12 hex chars, and an exact
  # prefix of the driver commit on its own length.
  EMB=$($B --version | sed -n 's/^Commit SHA: *\([0-9a-f]*\)$/\1/p' | head -1)
  [[ "$EMB" =~ ^[0-9a-f]{12,}$ ]] || { echo "embedded commit '$EMB' is not >= 12 hex chars"; exit 5; }
  [ "${SOLAR_HEAD:0:${#EMB}}" = "$EMB" ] || { echo "embedded $EMB != driver $SOLAR_HEAD"; exit 5; }
  $B --version > $R/solar-version.txt
  cp $W/sl/Verify/LoopSource/Equiv/Counter/run-v3/Counter.sol.txt $W/Counter.sol
  cd $W && rm -rf export && $B Counter.sol -Ogas --evm-version osaka --emit=bin,bin-runtime,abi -Zemit-lean-stages=export > rt.json
  python3 - "$B" "$EMB" > $R/producer.json <<EOF
import json,hashlib,sys
B,EMB=sys.argv[1],sys.argv[2]
h=lambda b: hashlib.sha256(b).hexdigest()
j=json.load(open('$W/rt.json')); c=[v for k,v in j['contracts'].items() if k.endswith(':Counter')][0]
rt=bytes.fromhex(c['bin-runtime']); ini=bytes.fromhex(c['bin'])
s0=h(open('$W/export/Counter/Stage0.lean','rb').read())
print(json.dumps({"binary_path":B,"binary_sha256":h(open(B,'rb').read()),"embedded_commit":EMB,
 "driver_commit":"$SOLAR_HEAD","embedded_len":len(EMB),
 "embedded_eq_driver":len(EMB)>=12 and "$SOLAR_HEAD"[:len(EMB)]==EMB,
 "flags":["-Ogas","--evm-version","osaka","--emit=bin,bin-runtime,abi","-Zemit-lean-stages=export"],
 "source_sha256":h(open('$W/Counter.sol','rb').read()),"runtime_bytes":len(rt),"runtime_sha256":h(rt),
 "init_bytes":len(ini),"init_sha256":h(ini),"stage0_sha256":s0,
 "runtime_eq_committed":h(rt)=="$EXPECT_RT","stage0_eq_committed":s0=="$EXPECT_STAGE0"}))
EOF
  cat $R/producer.json
  python3 -c "import json,sys;d=json.load(open('$R/producer.json'));sys.exit(0 if d['runtime_eq_committed'] and d['stage0_eq_committed'] else 6)" \
    || { echo "STOP: the freeze-head producer emits a different runtime or Stage0; the committed Counter proofs are for other bytes"; exit 6; } ;;

2) # lifecycle: the freeze head's own generic.lifecycle_lean on this producer's init and runtime
  cd $W/sl; B=$W/solar/target/release/solar; mkdir -p Certified/CounterRun/fe
  cp $W/Counter.sol Certified/CounterRun/fe/CounterRun.sol
  { printf -- "-- Generated by solar's tools/certify/generic.py with scripts/solc_ast_to_lean_source.py; do not edit.\n\nimport SolidCore.Solidity.Checked\n\nopen SolidCore.Solidity\n\n"
    python3 scripts/solc_ast_to_lean_source.py Certified/CounterRun/fe/CounterRun.sol --contract Counter \
      --solc $HOME/.cache/solc/solc-0.8.35 --namespace Certified.CounterRun.Src --body-only; } > Certified/CounterRun/Source.lean
  # Run-local lib, as the driver's declare_lean_lib writes it. Not committed; nothing else in the pinned lakefile changes.
  printf '\nlean_lib «CounterRun» where\n  srcDir := "Certified"\n  globs := #[.submodules `CounterRun]\n  leanOptions := solarTVOptions\n' >> lakefile.lean
  git diff lakefile.lean > $R/lakefile-runlocal.diff
  sed "s#/home/hand/solar446#$W/solar#; s#/home/hand/exporter/target/debug/solar#$B#; s#/home/hand/run/Counter.sol#$W/Counter.sol#" \
    Verify/LoopSource/Equiv/Counter/run-v3/life.py.txt > $W/life.py
  uv run --python 3.14 --no-project python $W/life.py 8 '[[1,8]]' Certified/CounterRun/Lifecycle.lean Certified.CounterRun.Lifecycle > $R/life-gen.json
  uv run --python 3.14 --no-project python $W/life.py 8 '[[1,9]]' Certified/CounterRun/LifecycleBad.lean Certified.CounterRun.LifecycleBad > /dev/null
  sha256sum Certified/CounterRun/*.lean > $R/lifecycle-files.sha256
  scoped build-lifecycle lake build -KleanMemory=6000 CounterRun.Lifecycle
  if scoped build-lifecycle-bad lake build -KleanMemory=6000 CounterRun.LifecycleBad; then echo "control NOT refused"; exit 7; fi
  # A refusal counts only as the kernel's: the checkB_eq type mismatch, and no OOM in the scope.
  python3 - "$R" > $R/control.json <<'EOF' || { cat $R/control.json; echo "control failed for another reason"; exit 7; }
import json,sys,re
R=sys.argv[1]; log=open(R+"/build-lifecycle-bad.out").read(); m=json.load(open(R+"/build-lifecycle-bad.json"))
kernel=bool(re.search(r"\(kernel\) declaration type mismatch, '[^']*checkB_eq'", log))
oom=int(m["memory.events"].get("oom_kill","0")); mem_exc="memory_exception" in log or "out of memory" in log
ok=kernel and oom==0 and not mem_exc and m["exit"]!=0
print(json.dumps({"control":"wrong storage (1,9)","exit":m["exit"],"kernel_checkB_eq_mismatch":kernel,
  "oom_kill":oom,"memory_exception":mem_exc,"refused":ok}))
sys.exit(0 if ok else 1)
EOF
  cat $R/control.json ;;

3) # resources and the modules it composes (Contracts.VerifyCounter.Source builds under its lib's -M 3000, unchanged)
  cd $W/sl
  # Up to 2 extra attempts (approved), only on exit 134 with a memory_exception or "out of memory"
  # message; the lakefile is unchanged and every attempt's log and memory json are kept.
  a=1
  while :; do
    git diff --quiet lakefile.lean || { echo "lakefile changed"; exit 11; }
    set +e
    scoped "build-resources-a$a" lake build -KleanMemory=6000 Verify.LoopSource.Equiv.Counter.Resources \
      Verify.LoopSource.Equiv.Counter.Closed Verify.LoopSource.Equiv.Counter.Neg Verify.LoopSource.Equiv.Counter.Check
    rc=$?; set -e
    mem=0; grep -qE 'memory_exception|out of memory' "$R/build-resources-a$a.out" && mem=1
    # lake reports 1; the inner Lean exit is in its log ("Lean exited with code N").
    inner=$(sed -n 's/^error: Lean exited with code \([0-9]*\)$/\1/p' "$R/build-resources-a$a.out" | head -1)
    echo "{\"attempt\":$a,\"lake_exit\":$rc,\"inner_exit\":\"$inner\",\"memory_exception\":$mem}" >> $R/attempts.log
    if [ $rc -eq 0 ]; then break; fi
    if [ $a -lt 3 ] && [ "$inner" = 134 ] && [ $mem -eq 1 ]; then a=$((a+1)); continue; fi
    echo "{\"attempts\":$a,\"exit\":$rc,\"memory_exception\":$mem}" > $R/attempts.json; exit $rc
  done
  echo "{\"attempts\":$a,\"exit\":0,\"source_headroom\":\"OPEN\"}" > $R/attempts.json; cat $R/attempts.json ;;

3d) # diagnosis only (no receipt for acceptance): compile Contracts.VerifyCounter.Source exactly as lake
  # does (its lib's -M 3000, lakefile unchanged), alone, with Lean's own peak report, then with
  # LEAN_NUM_THREADS=1 and with an 8 MiB / unlimited stack, to localize the interpreter memory check.
  cd $W/sl; git diff --quiet lakefile.lean || { echo "lakefile changed"; exit 11; }
  for v in "default:" "threads1:LEAN_NUM_THREADS=1" "stack8m:ulimit -s 8192;" "stackunl:ulimit -s unlimited;"; do
    tag=${v%%:*}; pre=${v#*:}
    scoped "src-$tag" bash -c "$pre timeout 600 lake env lean -M 3000 --stats Contracts/VerifyCounter/Source.lean -o /tmp/src-$tag.olean" || true
  done ;;

4) # --fresh: replay each top module's whole imported closure from scratch
  cd $W/sl
  [ $# -gt 0 ] || { echo "step 4 needs modules"; exit 2; }
  for m in "$@"; do
    scoped "fresh-$m" lake env leanchecker --fresh $m
  done ;;

5) # transitive axiom audit, forbidden tokens, receipts digest
  cd $W/sl
  cat > Certified/CounterRun/Audit.lean <<'EOF'
import Verify.LoopSource.Equiv.Counter.Resources
import Verify.LoopSource.Equiv.Counter.Neg
import CounterRun.Lifecycle
#print axioms Verify.LoopSource.Equiv.CounterResources.counter_certified_bounded
#print axioms Verify.LoopSource.Equiv.CounterResources.counter_resources
#print axioms Verify.LoopSource.Equiv.CounterClosed.counter_equiv_closed
#print axioms Verify.LoopSource.Equiv.CounterGas.bounded_inhabited
#print axioms Certified.CounterRun.Lifecycle.statement
#print axioms Verify.LoopSource.Equiv.CounterNeg.neg_natsub_inv
EOF
  scoped audit lake env lean Certified/CounterRun/Audit.lean
  if grep -E 'sorryAx|ofReduceBool|trustCompiler' $R/audit.out; then echo "forbidden axiom"; exit 8; fi
  if grep -rnE '\bsorry\b|native_decide|ofReduceBool|@\[extern|implemented_by|^axiom ' Verify/LoopSource Certified/CounterRun > $R/forbidden.txt; then echo "forbidden token"; exit 8; fi
  (cd $W/rcpt && find . -type f ! -name receipts.sha256 | sort | xargs sha256sum > receipts.sha256) ;;
6) # ctx: build the deploy certificates (box-only) and the closed expected theorem with its closure
  cd $W/sl2
  set +e
  scoped build-ctx lake build -KleanMemory=6000 Verify.LoopSource.Equiv.CounterDeploy8 Verify.LoopSource.Equiv.CounterDeploy5 \
    Verify.LoopSource.Equiv.CounterClosedCtx
  rc=$?; set -e
  if [ $rc -ne 0 ] && srcdied build-ctx; then open_step build-ctx; echo "OPEN: Source died"; exit 0; fi
  exit $rc ;;

6c) # composed: solar at the binding head, its generic driver's lifecycle run bound to counter_expected
  # (init and runtime from this fresh run), then Certified.counter_f1c87a33.Composed in the run's clone.
  [ -e $W/sl2/.lake/build/lib/lean/Verify/LoopSource/Equiv/CounterCtx.olean ] || { echo '{"status":"FAIL","stage":"CounterCtx not built (step 6)"}' > $R/composed.json; exit 13; }
  [ -d $W/solar7 ] || { git clone -q https://github.com/paradigmxyz/solar.git $W/solar7 && git -C $W/solar7 checkout -q $BIND_SOLAR; }
  cd $W/solar7; [ "$(git rev-parse HEAD)" = "$BIND_SOLAR" ] || { echo "solar7 not at $BIND_SOLAR"; exit 5; }
  git diff --quiet HEAD || { echo "solar7 has edits"; exit 5; }
  # The driver's own build (build_solar: debug, --locked); the run then refuses any other binary.
  scoped build-solar7 cargo build --locked --bin solar
  B7=$W/solar7/target/debug/solar
  EMB7=$($B7 --version | sed -n 's/^Commit SHA: *\([0-9a-f]*\)$/\1/p' | head -1)
  [ "$EMB7" = "$BIND_SOLAR" ] || { echo "embedded '$EMB7' != $BIND_SOLAR"; exit 5; }
  $B7 --version > $R/solar7-version.txt
  python3 - "$B7" "$EMB7" > $R/producer7.json <<EOF
import json,hashlib,sys,re
B,EMB=sys.argv[1],sys.argv[2]
h=lambda f: hashlib.sha256(open(f,'rb').read()).hexdigest()
g=open('$W/solar7/tools/certify/generic.py').read()
opts=re.search(r'(?m)^OPTIONS = (\[.*\])$',g).group(1)
print(json.dumps({"binary_path":B,"binary_sha256":h(B),"embedded_commit":EMB,"driver_commit":"$BIND_SOLAR",
 "embedded_eq_driver":EMB=="$BIND_SOLAR","build":["cargo","build","--locked","--bin","solar"],
 "compile_flags":json.loads(opts),"cargo_lock_sha256":h('$W/solar7/Cargo.lock'),
 "generic_py_sha256":h('$W/solar7/tools/certify/generic.py'),
 "bind_json_sha256":h('$W/solar7/tools/certify/testdata/lifecycle_bind/counter-bind.json'),
 "source_sha256":h('$W/Counter.sol')}))
EOF
  cat $R/producer7.json
  rm -rf $W/genwork $R/gen-record
  set +e
  CERTIFY_SOLAR_SHA256=$(sha256sum $B7 | cut -d' ' -f1) scoped generic-lifecycle \
    uv run --python 3.14 --no-project python tools/certify/generic.py $W/Counter.sol none --contract Counter \
    --tier lifecycle --constructor-args 8 --lifecycle-bind tools/certify/testdata/lifecycle_bind/counter-bind.json \
    --solidity-lean $W/sl2 --base $CTX_REV --packages-from $W/sl2 --work $W/genwork --record-dir $R/gen-record
  rc=$?; set -e
  # Verdict: PASS only with CERTIFIED, the bound source, the built composed theorem and this binary.
  python3 - "$R" "$rc" "$(sha256sum $B7 | cut -d' ' -f1)" > $R/composed.json <<'EOF' || true
import json,sys,os
R,rc,bsha=sys.argv[1],int(sys.argv[2]),sys.argv[3]
p=R+"/gen-record/record.json"
r=json.load(open(p)) if os.path.exists(p) else {}
life=r.get("lifecycle") or {}; comp=life.get("composed") or {}
if r.get("name")!="counter_f1c87a33": stage="name "+str(r.get("name"))
elif (r.get("solar") or {}).get("binary_sha256")!=bsha: stage="driver binary is not the recorded build"
elif life.get("source_same") is not True: stage="SourceSame"
elif not str(life.get("statement","")).startswith("Certified.counter_f1c87a33.Lifecycle.statement"): stage="Lifecycle"
elif comp.get("built") is not True: stage="Composed"
elif r.get("status")!="CERTIFIED" or rc!=0: stage="driver status %s exit %d"%(r.get("status"),rc)
else: stage=None
print(json.dumps({"status":"PASS" if stage is None else "FAIL","stage":stage,"driver_exit":rc,
 "record_status":r.get("status"),"name":r.get("name"),"source_same":life.get("source_same"),
 "composed":comp,"initcode_sha256":life.get("initcode_sha256"),"bin_runtime_sha256":life.get("bin_runtime_sha256"),
 "runtime_sha256":life.get("runtime_sha256"),"lifecycle_lean_sha256":life.get("lean_sha256"),
 "stages":life.get("stages")}))
EOF
  cat $R/composed.json
  python3 -c "import json,sys;sys.exit(0 if json.load(open('$R/composed.json'))['status']=='PASS' else 1)" || exit 14 ;;

7) # ctx: replay the closed theorem's whole imported closure from scratch
  cd $W/sl2
  [ -e .lake/build/lib/lean/Verify/LoopSource/Equiv/CounterClosedCtx.olean ] || { open_step "not built"; exit 0; }
  for m in Verify.LoopSource.Equiv.CounterClosedCtx; do scoped "fresh-$m" lake env leanchecker --fresh $m; done
  # The composed theorem's module, in the generic run's clone (step 6c).
  G=$W/genwork/solidity-lean
  [ -e $G/.lake/build/lib/lean/counter_f1c87a33/Composed.olean ] || { echo '{"status":"FAIL","stage":"Composed not built (step 6c)"}' > $R/composed.json; exit 14; }
  cd $G; scoped fresh-composed lake env leanchecker --fresh counter_f1c87a33.Composed ;;

8) # ctx: transitive axiom audit of the exported theorem
  cd $W/sl2
  [ -e .lake/build/lib/lean/Verify/LoopSource/Equiv/CounterClosedCtx.olean ] || { open_step "not built"; exit 0; }
  printf 'import Verify.LoopSource.Equiv.CounterClosedCtx\n#print axioms Verify.LoopSource.Equiv.CounterClosedCtx.counter_expected_closed\n#print axioms Verify.LoopSource.Equiv.CounterCtx.counter_expected\n' > /tmp/AuditCtx.lean
  scoped audit-ctx lake env lean /tmp/AuditCtx.lean
  grep -q "counter_expected_closed' depends on axioms: \[propext, Classical.choice, Quot.sound\]" $R/audit-ctx.out || { echo "axioms differ"; exit 8; }
  if grep -rnE '\bsorry\b|native_decide|ofReduceBool|@\[extern|implemented_by|^axiom ' Verify/LoopSource > $R/forbidden-ctx.txt; then echo "forbidden token"; exit 8; fi
  G=$W/genwork/solidity-lean; cfail=0
  if [ -e $G/.lake/build/lib/lean/counter_f1c87a33/Composed.olean ]; then
  cd $G
  printf 'import counter_f1c87a33.Composed\n#print axioms Certified.counter_f1c87a33.Composed.composed\n' > /tmp/AuditComposed.lean
  scoped audit-composed lake env lean /tmp/AuditComposed.lean
  grep -q "Certified.counter_f1c87a33.Composed.composed' depends on axioms: \[propext, Classical.choice, Quot.sound\]" $R/audit-composed.out || { echo "axioms differ"; exit 8; }
  if grep -rnE '\bsorry\b|native_decide|ofReduceBool|@\[extern|implemented_by|^axiom ' Certified/counter_f1c87a33 > $R/forbidden-composed.txt; then echo "forbidden token"; exit 8; fi
  else echo '{"status":"FAIL","stage":"Composed not built (step 6c)"}' > $R/composed.json; cfail=14; fi
  (cd $W/rcpt && find . -type f ! -name receipts.sha256 | sort | xargs sha256sum > receipts.sha256)
  exit $cfail ;;
esac

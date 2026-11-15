#!/usr/bin/env bash
# Lane E on GENERATED end-to-end artefacts (docs/eval/e.md, "Generated VCs"): proof-DAG and kernel
# statistics of every theorem of each already-built generated module, by #e_module_stats
# (Verify/Eval/E/Stats.lean). Builds nothing: a module whose .olean is missing is reported and
# skipped. Takes one admission slot of scripts/eval/check.sh (or the lane E lock with E_NOSLOT=1).
#
#   Verify/Eval/E/generated.sh            # writes ~/evalE/genvc/{GenStats.lean,log,time,sizes}
set -euo pipefail
repo="$(cd "$(dirname "$0")/../../.." && pwd)"; cd "$repo"
[ -f "$HOME/env.sh" ] && source "$HOME/env.sh"
out="$HOME/evalE/genvc"; mkdir -p "$out" "$HOME/eval-slots"
mods=(Contracts.VerifyCounter.Inferred Contracts.VerifyCounter.Bump Contracts.VerifyCounter.BumpTotal
      Contracts.VerifyCounter.BumpWrongRank verify_counter.gen.Counter.Stage0
      verify_counter.Proofs.Stages verify_counter.Proofs.Execution verify_counter.Proofs.Assembly
      verify_counter.Proofs.Runs.Evm1 verify_counter.Proofs.Runs.Mir1 verify_counter.gen.Counter.Evm1
      W1Proofs.Segment Contracts.Counter.VC.Export Verify.VC.Obligations Verify.VC.EndToEnd)
lib=.lake/build/lib/lean
: > "$out/sizes"
src="import Verify.Eval.E.Stats"
cmds=""
for m in "${mods[@]}"; do
  f="$lib/$(echo "$m" | tr . /).olean"
  if [ -f "$f" ]; then
    echo "$m $(stat -c %s "$f")" >> "$out/sizes"
    src="$src
import $m"
    cmds="$cmds
#e_module_stats $m"
  else
    echo "$m MISSING" >> "$out/sizes"
  fi
done
printf '%s\n\nset_option maxHeartbeats 0\n%s\n' "$src" "$cmds" > "$out/GenStats.lean"
export LEAN_PATH="$HOME/evalE/olean:$(lake env printenv LEAN_PATH)"
export LEAN_NUM_THREADS=1
if [ "${E_NOSLOT:-0}" = 1 ]; then lock="$HOME/evalE/noslot.lock"; else lock="$HOME/eval-slots/1.lock"; fi
exec {fd}>"$lock"; flock "$fd"
/usr/bin/time -v -o "$out/time" lean --root="$out" -M 6000 "$out/GenStats.lean" > "$out/log" 2>&1 || true
flock -u "$fd"
cat "$out/sizes"; grep -E "e_module_stats|error" "$out/log"; grep -E "Maximum resident|Elapsed" "$out/time"

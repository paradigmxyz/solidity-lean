#!/usr/bin/env bash
# Lane A baseline on GENERATED end-to-end artefacts already in the checkout (not handwritten):
# re-elaborate each module with today's engine under scripts/eval/check.sh (one slot, the
# library's own leanOptions: maxHeartbeats 200000, backward.do.legacy false), then replay every
# theorem of the built modules in the kernel only (Verify/Eval/A/Replay.lean).
#
#   scripts/eval/fixtures/run_generated.sh
#
# Never writes .olean files of these modules (no -o): lake's build stays as it is.
# Contracts/VerifyCounter/BumpWrongRank.lean is the negative: it must FAIL (exit != 0).
set -u
repo="$(cd "$(dirname "$0")/../../.." && pwd)"
cd "$repo"
[ -f "$HOME/env.sh" ] && source "$HOME/env.sh"
opts=(-DmaxHeartbeats=200000 -Dbackward.do.legacy=false)
files="${GEN_FILES:-Contracts/VerifyCounter/Inferred.lean Contracts/VerifyCounter/Bump.lean Contracts/VerifyCounter/BumpTotal.lean Contracts/VerifyCounter/BumpWrongRank.lean}"
mods="${GEN_MODS:-Contracts.VerifyCounter.Inferred Contracts.VerifyCounter.Bump Contracts.VerifyCounter.BumpTotal verify_counter.gen.Counter.Stage0}"
for f in $files; do
  scripts/eval/check.sh A "$f" "${opts[@]}" > "$HOME/eval-logs/gen-A-$(basename "$f" .lean).out" 2>&1
  code=$?
  echo "[gen] $f: exit $code $(tail -1 "$HOME/eval-logs/gen-A-$(basename "$f" .lean).out")"
done
lake env lean --run Verify/Eval/A/Replay.lean $mods > "$HOME/eval-logs/replay-A-generated.jsonl" 2>&1
echo "[gen] replay exit $?"

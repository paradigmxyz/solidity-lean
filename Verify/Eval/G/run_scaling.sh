#!/usr/bin/env bash
# Lane G: generate the scaling family (gen_scaling.py) and check every file under
# scripts/eval/check.sh (admission slots, receipts in ~/eval-receipts.jsonl). Summary lines go to
# ~/g-gen/scaling/summary.txt. Needs Verify.Eval.G.Model and Verify.Eval.G.Kernel built.
#   [G_VARIANTS='base once fresh shared facts'] Verify/Eval/G/run_scaling.sh [N ...]
set -uo pipefail
repo="$(cd "$(dirname "$0")/../../.." && pwd)"
cd "$repo"
out="$HOME/g-gen/scaling"
ns="$*"; [ -n "$ns" ] || ns="16 32 64 128 256"
python3 Verify/Eval/G/gen_scaling.py "$out" $ns
for n in $ns; do
  for v in ${G_VARIANTS:-base once fresh shared facts}; do
    f="$out/scale_"$v"_"$n".lean"
    res=$(scripts/eval/check.sh G "$f" 2>&1)
    { echo "## $v $n"
      echo "$res" | grep -E 'g_time|kernel_recheck_all|proof_stats|depends on axioms|g_simp:|error|\[check\]' ; } >> "$out/summary.txt"
  done
done

#!/usr/bin/env bash
# fast_inner_gate.sh — FAST INNER-LOOP gate for the divergence fix agent.
#
# Motivation (measured 2026-07-22, 14-core M-series, warm .lake):
#   A plain `lake build` after an Interface.lean-touching fix rebuilds the
#   serial spine (Interface ~6min, TypeCheck+Checked ~1min) AND THEN fans out
#   over all ~87 witness modules + proof modules (~8-9min wall, with a long
#   tail: LoweringUnify/StageDCompletion/EvalOrderIntrinsic run 1.5-12min
#   EACH). The witness fan-out is >55% of every iteration's wall time, but a
#   fix iteration only needs (a) the spine to elaborate (types + proofs in
#   changed modules ARE checked — Lean cannot compile a module without
#   checking its proofs) and (b) the SPECIFIC repro to flip green.
#
# This script builds ONLY:
#   1. the semantic spine (Interpreter -> ABI -> Interface -> TypeCheck ->
#      Checked) — i.e. every module a semantics fix actually edits, WITH all
#      in-module proof obligations checked as always;
#   2. the proof modules that state cross-cutting laws (FuelMonotonicity,
#      AdoptionLaws) — cheap (~10s each) and the most likely to break on a
#      semantics change, so failing them EARLY is pure win;
#   3. any extra module targets passed as arguments (e.g. the witness for the
#      bug being fixed: SolidCore.Witness.Foo).
#
# It is NOT a substitute for the green gate. The full `lake build` (all
# witnesses) + contest sample suite still runs ONCE, at the end, before the
# fix may be reported green. Soundness is unchanged: nothing is ever merged
# that has not passed the identical full gate; this only removes ~9min of
# witness re-elaboration from every INTERMEDIATE iteration.
#
# Usage:
#   scripts/fast_inner_gate.sh                          # spine + laws only
#   scripts/fast_inner_gate.sh SolidCore.Witness.Foo    # + the repro's witness
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/.."
LAKE_BIN="${LAKE:-/Users/dan/.elan/bin/lake}"

TARGETS=(
  +SolidCore.Solidity.Interpreter
  +SolidCore.Solidity.ABI
  +SolidCore.Solidity.Interface
  +SolidCore.Solidity.TypeCheck
  +SolidCore.Solidity.Checked
  +SolidCore.Solidity.FuelMonotonicity
  +SolidCore.Solidity.AdoptionLaws
  +SolidCore.Solidity.Interaction
)
for extra in "$@"; do
  TARGETS+=("+${extra#+}")
done

echo "fast_inner_gate: ${#TARGETS[@]} module targets (spine + laws + repro)"
exec "$LAKE_BIN" build "${TARGETS[@]}"

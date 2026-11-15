#!/usr/bin/env bash
# Lane G: capture the real side conditions W1Proofs' sym_mem_disch is asked, from a certified
# contract's stage proofs, unchanged, under Capture/Hook.lean.
#
#   Verify/Eval/G/capture.sh <contract> [Runs file stem ...]
#
# Compiles Certified/<contract>/gen/* into ~/g-build (outside .lake), writes for each Runs file a
# copy that imports the hook instead of W1Proofs.Axioms (the axiom guards dropped: the copies are
# for capture only) to ~/g-gen/capture/<contract>/, runs it under scripts/eval/check.sh and appends
# the captured goals to ~/g-gen/capture/<contract>.txt. Needs W1Proofs.Tactic and
# Verify.Eval.G.Capture.Hook built (lake build Verify.Eval.G.Capture.Hook).
set -euo pipefail
c="$1"; shift
repo="$(cd "$(dirname "$0")/../../.." && pwd)"
cd "$repo"
out="$HOME/g-gen/capture/$c"; mkdir -p "$out"
mods=$(cd Certified && find "$c/gen" -name '*.lean' ! -name Manifest.lean ! -name Bytecode.lean ! -name Spec.lean | sed 's/\.lean$//; s#/#.#g')
"$HOME/g-compile-src.sh" Certified $mods > "$out/compile.log" 2>&1 || { tail "$out/compile.log"; exit 1; }
stems="$*"
[ -n "$stems" ] || stems=$(ls Certified/$c/Proofs/Runs | sed 's/\.lean$//')
for s in $stems; do
  f="$out/$s.lean"
  { echo "import Verify.Eval.G.Capture.Hook"
    grep -v '^import W1Proofs.Axioms' "Certified/$c/Proofs/Runs/$s.lean" | grep -v '^#guard_msgs' | grep -v '^#axioms_within' | grep -v '^#print axioms' | grep -v "depends on axioms"
  } > "$f"
  echo "=== $c $s" >> "$HOME/g-gen/capture/$c.txt"
  LEAN_PATH="$HOME/g-build" G_CAPTURE_OUT="$HOME/g-gen/capture/$c.txt" scripts/eval/check.sh G "$f" > "$out/$s.out" 2>&1 || true
  tail -1 "$out/$s.out"
done

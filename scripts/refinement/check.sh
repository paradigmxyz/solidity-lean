#!/usr/bin/env bash
# Check the refinement of solar's bytecode against SolidCore.
#
# Builds solar at the commit in scripts/refinement/solar-rev, regenerates the
# corpus's bytecode and source files and fails if any differs from the checked-in
# copy, then does the same for solar's analysis facts on the corpus with
# scripts/refinement/facts.sh (solar at scripts/refinement/prove-rev). Finally it
# builds SolidCore.Refinement, which checks every refinement proof, and
# SolidCore.Refinement.Facts, which checks every fact's Lean theorem.
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/../.."

scripts/refinement/gen.sh --check
scripts/refinement/facts.sh --check
lake exe cache get
lake build SolidCore.Refinement
lake build SolidCore.Refinement.Facts

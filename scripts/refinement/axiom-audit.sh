#!/usr/bin/env bash
# The axiom pass: elaborates the eight SolidCore/Refinement/Axioms files (one environment can hold
# only one of the w1, w4, c4 and mulx exports, which all declare SolarTV.Export.Main), then
# checks every #print axioms line and greps the files' import closure. Build the libraries first:
#   lake -KleanMemory=6000 build SolidCore SolidCoreSolarC4 SolidCoreSolarMulX SolidCoreSolarW4 \
#     SolidCoreSolarBankSource SolidCore.Refinement.Axioms.Audit \
#     ContractsCounter ContractsVC VerifyLoom VerifySpecTrustedBase
set -uo pipefail
cd "$(dirname "$0")/../.."
logs=() closures=()
for part in Main C4 MulX W4 CounterGeneric Contracts Token VerifyCounter; do
  log=.lake/axiom-$part.log
  lake env lean -M "${AXIOM_MEMORY:-6000}" "SolidCore/Refinement/Axioms/$part.lean" > "$log" 2>&1
  echo "$part: lean exit $?"
  logs+=("$log")
  part_lc=$(echo "$part" | tr '[:upper:]' '[:lower:]')
  closures+=(".lake/axiom-closure-$part_lc.txt")
done
python3 scripts/refinement/axiom-closure.py "${logs[@]}" -- "${closures[@]}"

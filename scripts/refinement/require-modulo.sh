#!/usr/bin/env bash
# The generic assembly theorem on a layout with a turned branch, fallthroughs and a backward
# jump: solar's UI test require_modulo_chain.sol, whose EVM IR to bytecode stage
# SolidCore/Refinement/Solar/RequireModulo/Assembly.lean proves from Assemble.stage_of_check.
#
#   scripts/refinement/require-modulo.sh
#
# 1. Puts the solar checkout that lakefile.lean requires (../ck-pipeline next to this repository,
#    fetched from SOLAR_REPO when it is not a git checkout yet) at the pinned solar commit, with
#    no uncommitted changes, as the milestone checks do.
# 2. Builds solar (cargo, CARGO_TARGET_DIR, default target in that checkout), or takes SOLAR,
#    which must report the pinned commit.
# 3. Compiles the checkout's tests/ui/codegen/lowering/evm-ir/constructs/require_modulo_chain.sol
#    with -Ogas --evm-version osaka and -Zemit-lean-stages, and checks that the last EVM IR stage
#    (Evm10.lean, after block-layout) and the bytecode (Bytecode.lean) are the committed files
#    byte for byte, and the bytecode is solar's --emit=bin-runtime output.
# 4. Builds the module with lake under a cap per Lean process (LEAN_MEMORY, MB, default 4500)
#    and prints the axioms of the stage, the check and the negative tests, failing on any axiom
#    beyond propext, Classical.choice and Quot.sound.
# 5. Negative test: Assemble.stage_of_check, applied to the bytes this script gives it with the
#    checker run by the kernel, proves the stage for solar's bytecode and fails for a one-byte
#    mutant (NOT for the ISZERO of the turned branch), where the checker evaluates to false.
set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$root"

# solar: branch ck-pipeline, the commit the milestone checks pin.
solar_rev=f19e9e46309c7cdb3a0f36668f7881d12bb8503a
test_sol=tests/ui/codegen/lowering/evm-ir/constructs/require_modulo_chain.sol
contract=RequireModuloCases
lean_dir=SolidCore/Refinement/Solar/RequireModulo
# The runtime bytecode, 103 bytes.
bytecode=34604a575f3560e01c80631ea7714403604a5760443610604a576024358015604e57600435818106604a576003820615603a5760018116604a575b9081019081106061575f5260205ff35b5f5ffd5b60125b602052634e487b715f526024601cfd5b6011605156

tv_dir="$(sed -nE 's|^require solar_tv from "[.][.]" / "([^"]+)" / "solar-tv"$|\1|p' lakefile.lean)"
[[ -n "$tv_dir" ]] || { echo "error: lakefile.lean requires solar_tv from no ../<dir>/solar-tv" >&2; exit 1; }
tv="$(cd "$root/.." && pwd)/$tv_dir"
export PATH="$HOME/.elan/bin:$PATH"
export LEAN_NUM_THREADS="${LEAN_NUM_THREADS:-2}"
memory="${LEAN_MEMORY:-4500}"
export CARGO_TARGET_DIR="${CARGO_TARGET_DIR:-$tv/target}"
work="$(mktemp -d)"
trap 'rm -rf "$work"' EXIT

step() { printf '\n== %s\n' "$*"; }
die() { echo "error: $*" >&2; exit 1; }

step "1. solar at $solar_rev"
if [[ ! -e "$tv/.git" ]]; then
  repo="${SOLAR_REPO:?set SOLAR_REPO to a solar clone, bundle or URL with commit $solar_rev}"
  mkdir -p "$tv"
  git -C "$tv" init -q
  git -C "$tv" fetch -q "$repo" '+refs/heads/*:refs/remotes/solar/*'
  git -C "$tv" checkout -q --detach "$solar_rev"
fi
git -C "$tv" diff --quiet HEAD || die "$tv has uncommitted changes"
if [[ "$(git -C "$tv" rev-parse HEAD)" != "$solar_rev" ]]; then
  git -C "$tv" checkout -q --detach "$solar_rev"
fi
echo "solar $solar_rev"

step "2. build solar"
if [[ -n "${SOLAR-}" ]]; then
  solar="$SOLAR"
else
  (cd "$tv" && cargo build -j "${CARGO_BUILD_JOBS:-2}" --bin solar 2>&1 | tail -n 1)
  solar="$CARGO_TARGET_DIR/debug/solar"
fi
"$solar" --version | grep -q "^Commit SHA: $solar_rev\$" || die "$solar is not solar $solar_rev"
"$solar" --version | head -n 1

step "3. regenerate the stages and compare them with the committed files"
(cd "$tv" && "$solar" "$test_sol" -Ogas --evm-version osaka --emit=bin-runtime \
  -Zemit-lean-stages="$work/gen" 2>/dev/null) > "$work/out.json" || die "solar failed on $test_sol"
emitted="$(python3 -c 'import json,sys; c=json.load(open(sys.argv[1]))["contracts"]; print(next(v["bin-runtime"] for k,v in c.items() if k.endswith(":" + sys.argv[2])))' "$work/out.json" "$contract")"
[[ "$emitted" == "$bytecode" ]] || die "solar's bytecode is not the pinned one: $emitted"
last="$(ls "$work/gen/$contract" | sed -nE 's/^Evm([0-9]+)[.]lean$/\1/p' | sort -n | tail -n 1)"
[[ "$last" == 10 ]] || die "the last EVM IR stage is Evm$last.lean, not Evm10.lean"
for file in Evm10.lean Bytecode.lean; do
  cmp -s "$work/gen/$contract/$file" "$lean_dir/$file" || {
    diff "$work/gen/$contract/$file" "$lean_dir/$file" | head -n 40 >&2
    die "$lean_dir/$file is not solar's output"
  }
done
grep -q "^  \"$bytecode\"\$" "$lean_dir/Bytecode.lean" || die "Bytecode.lean has other bytes"
echo "Evm10.lean and Bytecode.lean regenerate byte for byte; bytecode is solar's (103 bytes)"

step "4. build and audit the axioms"
if [[ ! -f .lake/packages/mathlib/.lake/build/lib/lean/Mathlib.olean ]]; then
  lake exe cache get > "$work/cache.log" 2>&1 || { tail -n 20 "$work/cache.log" >&2; die "lake exe cache get failed"; }
fi
if ! lake build -R -KleanMemory="$memory" SolidCore.Refinement.Solar.RequireModulo.Assembly \
    > "$work/build.log" 2>&1; then
  grep -E '^error' -A8 "$work/build.log" | head -n 40 >&2
  die "lake build failed"
fi
tail -n 1 "$work/build.log"
cat > "$work/Audit.lean" <<'LEAN'
import SolidCore.Refinement.Solar.RequireModulo.Assembly
open SolidCore.Refinement.Solar
#print axioms Assemble.stage_of_check
#print axioms RequireModulo.check_ok
#print axioms RequireModulo.stage
#print axioms RequireModulo.unturned_check
#print axioms RequireModulo.forward_check
#print axioms RequireModulo.mutated_bytes
#print axioms RequireModulo.mutantNot_check
#print axioms RequireModulo.mutantDiv_check
LEAN
report="$(lake env lean -M "$memory" "$work/Audit.lean" 2>&1)"
echo "$report"
if grep -q "error" <<<"$report"; then die "the audit file does not check"; fi
bad="$(grep "depends on axioms" <<<"$report" |
  sed -E 's/.*depends on axioms: \[(.*)\]/\1/' | tr ',' '\n' | tr -d ' ' |
  grep -v -x -E 'propext|Classical\.choice|Quot\.sound' || true)"
[[ -z "$bad" ]] || die "axioms beyond propext, Classical.choice and Quot.sound: $bad"
[[ "$(grep -c "depends on axioms" <<<"$report")" -eq 8 ]] || die "a theorem is missing from the audit"

step "5. negative: the generic assembly checker rejects a mutated bytecode"
# stage_of_check for the program and certificate on the bytes given, the check by the kernel.
generic_stage() {
  cat > "$work/$1.lean" <<LEAN
import SolidCore.Refinement.Solar.RequireModulo.Assembly
open SolidCore.Refinement.Solar
set_option maxRecDepth 100000 in
theorem generic_stage (o : SolarTV.Machine.Oracle) :
    SolarTV.Stage (SolarTV.evmirSem o) SolidCore.Refinement.ethLib
      SolarTV.Export.RequireModuloCases.evm10
      (EthLib.Execution.Evm.Logic.NatCode.ofNat 0x$2 103) RequireModulo.scope :=
  Assemble.stage_of_check
    (show Assemble.check SolarTV.Export.RequireModuloCases.evm10
      (EthLib.Execution.Evm.Logic.NatCode.ofNat 0x$2 103) RequireModulo.cert = true by
      decide +kernel) o fun _ h => h
#print axioms generic_stage
LEAN
  # The mutant's case fails by design: its error is the output to check.
  { lake env lean -M "$memory" "$work/$1.lean" 2>&1 || true; } | tr -s '[:space:]' ' '
}
control="$(generic_stage control "$bytecode")"
[[ "$control" == *"depends on axioms: [propext, Classical.choice, Quot.sound]"* && "$control" != *error* ]] ||
  die "stage_of_check does not prove the stage for solar's bytecode: $control"
echo "control: stage_of_check proves the stage for solar's bytecode (propext, Classical.choice, Quot.sound)"
[[ "${bytecode:94:2}" == "15" ]] || die "offset 47 is not ISZERO"
edited="$(generic_stage mutant "${bytecode:0:94}19${bytecode:96}")"
grep -q -E 'error: Tactic `decide` proved that the proposition Assemble\.check SolarTV\.Export\.RequireModuloCases\.evm10 .* RequireModulo\.cert = true is false' <<<"$edited" ||
  die "the mutated bytecode did not fail the generic checker: $edited"
echo "rejected by a mismatch, as expected: the kernel evaluates Assemble.check on the mutant to false"

printf '\nok: RequireModuloCases assembly checked (solar %s)\n' "$solar_rev"

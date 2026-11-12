#!/usr/bin/env bash
# The generic assembly theorem on c4, two uint8 fields packed in one slot: the EVM IR to
# bytecode stage of scripts/refinement/c4/c4.sol's Main, which
# SolidCore/Refinement/Solar/C4/Assembly.lean proves from Assemble.stage_of_check, from any
# storage on every call with no value. solar's solar-tv/milestone/c4 proves the stages before it.
#
#   scripts/refinement/c4.sh
#
# 1. Puts the solar checkout that lakefile.lean requires (the ../<dir>/solar-tv next to this repository,
#    fetched from SOLAR_REPO when it is not a git checkout yet) at the pinned solar commit, with
#    no uncommitted changes, as the milestone checks do.
# 2. Builds solar (cargo, CARGO_TARGET_DIR, default target in that checkout), or takes SOLAR,
#    which must report the pinned commit.
# 3. Compiles c4.sol with solar's default options, -Zcheck-analyses=false (as release builds
#    run) and -Zemit-lean-stages, and checks that the final EVM IR stage (Evm5.lean, after
#    cfg-simplify-early) and the bytecode (Bytecode.lean) are the committed files byte for byte,
#    and the bytecode is solar's --emit=bin-runtime output, the pinned 107 bytes.
# 4. Builds the module with lake under a cap per Lean process (LEAN_MEMORY, MB, default 4500)
#    and prints the axioms of the stage, the check and the negative tests, failing on any axiom
#    beyond propext, Classical.choice and Quot.sound.
# 5. Negative test: Assemble.stage_of_check, applied to the bytes this script gives it with the
#    checker run by the kernel, proves the stage for solar's bytecode and fails for a one-byte
#    mutant (SUB for the addition's ADD), where the checker evaluates to false.
set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$root"

# solar: branch ck-mulx, whose solar-tv has the c4 milestone.
solar_rev=37540a4715ffa6aa06e48e810e9aed57f74ef242
sol=scripts/refinement/c4/c4.sol
contract=Main
# The runtime bytecode, 107 bytes.
bytecode=346055575f3560e01c806302067e6a036055576024361060ff60043511176055576004355f5460ff8116820160ff81116059579060ff1916179081601e1a1860081b9061ff00191617805f5560ff165f5260205ff35b5f5ffd5b6011602052634e487b715f526024601cfd

tv_dir="$(sed -nE 's|^require solar_tv from "[.][.]" / "([^"]+)" / "solar-tv"$|\1|p' lakefile.lean)"
[[ -n "$tv_dir" ]] || { echo "error: lakefile.lean requires solar_tv from no ../<dir>/solar-tv" >&2; exit 1; }
tv="$(cd "$root/.." && pwd)/$tv_dir"
# The exported stages the proofs import.
lean_dir="$tv/milestone/c4/gen/Main"
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
runtime() {
  python3 -c 'import json,sys; c=json.load(sys.stdin)["contracts"]; print(next(v["bin-runtime"] for k,v in c.items() if k.endswith(":" + sys.argv[1])))' "$contract"
}
emitted="$("$solar" "$sol" --emit=bin-runtime -Zcheck-analyses=false -Zemit-lean-stages="$work/gen" \
  2>/dev/null | runtime)" || die "solar failed on $sol"
[[ "$emitted" == "$bytecode" ]] || die "solar's bytecode is not the pinned one: $emitted"
plain="$("$solar" "$sol" --emit=bin-runtime -Zcheck-analyses=false 2>/dev/null | runtime)"
[[ "$plain" == "$bytecode" ]] || die "-Zemit-lean-stages changed the bytecode: $plain"
last="$(ls "$work/gen/$contract" | sed -nE 's/^Evm([0-9]+)[.]lean$/\1/p' | sort -n | tail -n 1)"
[[ "$last" == 5 ]] || die "the last EVM IR stage is Evm$last.lean, not Evm5.lean"
for file in Evm5.lean Bytecode.lean; do
  cmp -s "$work/gen/$contract/$file" "$lean_dir/$file" || {
    diff "$work/gen/$contract/$file" "$lean_dir/$file" | head -n 40 >&2
    die "$lean_dir/$file is not solar's output"
  }
done
grep -q "^  \"$bytecode\"\$" "$lean_dir/Bytecode.lean" || die "Bytecode.lean has other bytes"
echo "Evm5.lean and Bytecode.lean regenerate byte for byte; bytecode is solar's (107 bytes)"

step "4. build and audit the axioms"
if [[ ! -f .lake/packages/mathlib/.lake/build/lib/lean/Mathlib.olean ]]; then
  lake exe cache get > "$work/cache.log" 2>&1 || { tail -n 20 "$work/cache.log" >&2; die "lake exe cache get failed"; }
fi
if ! lake build -R -KleanMemory="$memory" SolidCore.Refinement.Solar.C4.Assembly \
    > "$work/build.log" 2>&1; then
  grep -E '^error' -A8 "$work/build.log" | head -n 40 >&2
  die "lake build failed"
fi
tail -n 1 "$work/build.log"
cat > "$work/Audit.lean" <<'LEAN'
import SolidCore.Refinement.Solar.C4.Assembly
open SolidCore.Refinement.Solar
#print axioms Assemble.stage_of_check
#print axioms C4.check_ok
#print axioms C4.stage
#print axioms C4.mutated_bytes
#print axioms C4.mutantSub_check
#print axioms C4.mutantShl_check
LEAN
report="$(lake env lean -M "$memory" "$work/Audit.lean" 2>&1)"
echo "$report"
if grep -q "error" <<<"$report"; then die "the audit file does not check"; fi
bad="$(grep "depends on axioms" <<<"$report" |
  sed -E 's/.*depends on axioms: \[(.*)\]/\1/' | tr ',' '\n' | tr -d ' ' |
  grep -v -x -E 'propext|Classical\.choice|Quot\.sound' || true)"
[[ -z "$bad" ]] || die "axioms beyond propext, Classical.choice and Quot.sound: $bad"
[[ "$(grep -c "depends on axioms" <<<"$report")" -eq 6 ]] || die "a theorem is missing from the audit"

step "5. negative: the generic assembly checker rejects a mutated bytecode"
# stage_of_check for the program and certificate on the bytes given, the check by the kernel.
generic_stage() {
  cat > "$work/$1.lean" <<LEAN
import SolidCore.Refinement.Solar.C4.Assembly
open SolidCore.Refinement.Solar
set_option maxRecDepth 100000 in
theorem generic_stage (o : SolarTV.Machine.Oracle) :
    SolarTV.Stage (SolarTV.evmirSem o) SolidCore.Refinement.ethLib
      SolarTV.Export.Main.evm5
      (EthLib.Execution.Evm.Logic.NatCode.ofNat 0x$2 107) C4.scope :=
  Assemble.stage_of_check
    (show Assemble.check SolarTV.Export.Main.evm5
      (EthLib.Execution.Evm.Logic.NatCode.ofNat 0x$2 107) C4.cert = true by
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
[[ "${bytecode:86:2}" == "01" ]] || die "offset 0x2b is not ADD"
edited="$(generic_stage mutant "${bytecode:0:86}03${bytecode:88}")"
grep -q -E 'error: Tactic `decide` proved that the proposition Assemble\.check SolarTV\.Export\.Main\.evm5 .* C4\.cert = true is false' <<<"$edited" ||
  die "the mutated bytecode did not fail the generic checker: $edited"
echo "rejected by a mismatch, as expected: the kernel evaluates Assemble.check on the mutant to false"

printf '\nok: c4 assembly checked (solar %s)\n' "$solar_rev"

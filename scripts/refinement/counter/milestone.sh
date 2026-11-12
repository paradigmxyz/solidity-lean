#!/usr/bin/env bash
# The counter milestone in one command: solar's bytecode for a storage counter (inc adds its
# argument to the uint256 in slot 0 with the overflow check) meets inc's specification verified
# on SolidCore with the Loom VC generator, with every stage of solar's pipeline proved in Lean.
#
#   scripts/refinement/counter/milestone.sh
#
# 1. Puts the solar checkout that lakefile.lean requires (its solar_tv path, ../ck-pipeline
#    next to this repository; fetched from SOLAR_REPO, a clone, bundle or URL whose branches
#    hold the pinned commit, when it is not a git checkout yet, even if restored builds are
#    there) at the pinned solar commit, with no uncommitted changes, and checks
#    that its compiler sources are those of the commit the evidence's manifest names, except for
#    the stage exporter (crates/codegen/src/lean_stages.rs), which only prints the stages as Lean.
# 2. Builds solar (cargo -j2, CARGO_TARGET_DIR, default target in that checkout).
# 3. Runs solar-tv/milestone/certify.sh on counter.sol: compiles Counter with -Ogas
#    --evm-version osaka and -Zemit-lean-stages, checks the pinned bytecode and the manifest's
#    hashes, regenerates every backend stage proof, builds them one module at a time under
#    4.5 GB, audits their axioms, runs solar-tv's negative tests (a bytecode mutation of the
#    addition and edits of the stage outputs: the SSTORE's key (a wrong slot), the addition,
#    the call value check and the overflow check dropped, each rejected by a mismatch, with
#    unedited controls passing), and
#    checks that every regenerated file is the committed evidence (except the compiler's build
#    commit in the manifest). Then restores the manifest.
# 4. Binds the source: scripts/refinement/counter/counter.sol (which SolidCore parses) is
#    solar-tv/milestone/counter/counter.sol (which solar's stages come from) byte for byte,
#    solar compiles it to the pinned bytecode, the Lean literals and sha256s are solar's
#    output, and, with solc 0.8.35 (SOLC, or cached or downloaded and checked; without one the
#    check is skipped and reported unless REQUIRE_SOLC=1), SolidCore's source AST regenerates
#    to the committed Counter/Source.lean.
# 5. Negative tests: one-byte mutations of the bytecode's ADD (x + d) and SSTORE (slot 0), the
#    overflow check's PUSH1 0x41 JUMPI replaced by POP JUMPDEST JUMPDEST, and the call value
#    check's jump target (offset 2) changed from 0x34 to the Panic(0x11) block's 0x41, fail the
#    artifact check by a sha256 mismatch; in Lean, Counter.Milestone proves the assembly checker's walk
#    rejects all three, Counter.Assembly and Counter.NegativeAt that the generic checker rejects
#    all three, Counter.Lowering proves the source stage false for a lowering that subtracts
#    instead of adding, and Counter.NegativeAt proves, from any storage, the assembly stage false
#    for the third mutant and the source stage false for a lowering without the overflow check,
#    each by a mismatch of observables (the overflow revert against a success), and
#    Counter.NegativeValue proves the assembly stage on calls with value false for the fourth
#    mutant, by a mismatch of observables (the empty revert against Panic(0x11)).
# 6. Fetches Mathlib's build cache when Mathlib is not built, builds the proof chain with lake,
#    one Lean process at a time under a cap of LEAN_MEMORY MB (default 4500), and prints the
#    axioms of the final theorems (certified, from the deployed storage, and certifiedAt, from
#    any initial storage, where the overflow revert is reached; refinesSeq, every sequence of inc
#    calls with the storage carried between calls; certifiedEvery, every call of inc and get with
#    or without value, malformed call data and unknown selectors, from any storage, with
#    certifiedValue, its calls with value; certifiedSeqEvery, every sequence of those calls), each
#    stage (the assembly stages, stage and
#    stageAt, from the generic theorem for every program the checker accepts, and directly as
#    cross-checks, stage_run and stageAt_run) and the negative tests, failing on any axiom beyond
#    propext, Classical.choice and Quot.sound.
# 7. Negative test of the generic assembly theorem: Assemble.stage_of_check, applied to the
#    bytes this script gives it with the checker run by the kernel, proves the counter's
#    assembly stage for solar's bytecode (only the three axioms) and fails for all four step 5
#    mutants, where the checker evaluates to false.
set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../../.." && pwd)"
cd "$root"

# solar: branch ck-pipeline, the generator of backend stage proofs and counter's evidence.
solar_rev=f19e9e46309c7cdb3a0f36668f7881d12bb8503a
# The commit whose compiler sources built the committed evidence (its manifest's compiler).
compiler_rev=1134e61fc7faa873d870d59a651839ce4c996cf8
# The runtime bytecode, 83 bytes.
bytecode=346034575f3560e01c80636d4ce63c146038578063812600df03603457602436106034575f5460043581019081106041575f55005b5f5ffd5b5f545f5260205ff35b6011602052634e487b715f526024601cfd
bytecode_sha256=daed21b0c790bb2c08bcf999c9ebc6fea950c213ea0a799418552aa14c18f6ec
solc_version=0.8.35
solc_sha256=fa8ac9a32d301ad023a36ee5a29f8e291fe3200c60244e43c142539e82a617f4

# lakefile.lean requires solar_tv from ../<dir>/solar-tv: the solar checkout is ../<dir>.
tv_dir="$(sed -nE 's|^require solar_tv from "[.][.]" / "([^"]+)" / "solar-tv"$|\1|p' lakefile.lean)"
[[ -n "$tv_dir" ]] || { echo "error: lakefile.lean requires solar_tv from no ../<dir>/solar-tv" >&2; exit 1; }
tv="$(cd "$root/.." && pwd)/$tv_dir"
export PATH="$HOME/.elan/bin:$PATH"
export LEAN_NUM_THREADS="${LEAN_NUM_THREADS:-2}"
# The cap of each Lean process, in MB.
memory="${LEAN_MEMORY:-4500}"
export CARGO_TARGET_DIR="${CARGO_TARGET_DIR:-$tv/target}"
sol=scripts/refinement/counter/counter.sol
lean_dir=SolidCore/Refinement/Solar/Counter
size=$((${#bytecode} / 2))
logs="$(mktemp -d)"
trap 'rm -rf "$logs"' EXIT

step() { printf '\n== %s\n' "$*"; }
die() { echo "error: $*" >&2; exit 1; }
sha_hex() { python3 -c 'import hashlib,sys; print(hashlib.sha256(bytes.fromhex(sys.argv[1])).hexdigest())' "$1"; }
bin_runtime() {
  "$solar" "$1" -Ogas --evm-version osaka --emit=bin-runtime 2>/dev/null |
    python3 -c 'import json,sys; c=json.load(sys.stdin)["contracts"]; print(next(v["bin-runtime"] for k,v in c.items() if k.endswith(":Counter")))'
}
# Whether hex is the milestone's bytecode by its sha256: prints a mismatch and fails otherwise.
check_bytecode() {
  local got
  got="$(sha_hex "$1")"
  if [[ "$got" != "$bytecode_sha256" ]]; then
    echo "mismatch: sha256 $got, expected $bytecode_sha256" >&2
    return 1
  fi
}

step "1. solar at $solar_rev"
if [[ ! -e "$tv/.git" ]]; then
  # A new checkout, in a directory that may already hold restored builds (target, .lake).
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
exporter=crates/codegen/src/lean_stages.rs
git -C "$tv" diff --quiet "$compiler_rev" HEAD -- crates Cargo.toml Cargo.lock ":!$exporter" ||
  die "the compiler sources at $solar_rev differ from $compiler_rev's"
echo "solar $solar_rev; compiler sources identical to $compiler_rev except the exporter $exporter"

step "2. build solar"
(cd "$tv" && cargo build -j "${CARGO_BUILD_JOBS:-2}" --bin solar 2>&1 | tail -n 1)
solar="$CARGO_TARGET_DIR/debug/solar"
"$solar" --version | head -n 1

step "3. certify solar's backend stages and compare them with the evidence"
manifest=solar-tv/milestone/counter/gen/Counter
restore() { git -C "$tv" checkout -q -- "$manifest/Manifest.lean" "$manifest/manifest.json"; }
if ! (cd "$tv" && CERTIFY_SKIP_BUILD=1 SOLAR="$solar" LEAN_MEMORY="$memory" \
    solar-tv/milestone/certify.sh solar-tv/milestone/counter/counter.sol Counter) > "$logs/certify.log" 2>&1; then
  tail -n 30 "$logs/certify.log" >&2
  restore
  die "certify.sh failed for counter"
fi
grep -E '^(==|ok|skip|counter|every|stages|bytecode)' "$logs/certify.log"
grep "depends on axioms" "$logs/certify.log"
for case in Evm5-sstore-key Evm5-no-overflow-check Evm5-no-callvalue-check; do
  grep -q "^ok   $case: " "$logs/certify.log" || die "the negative test $case did not reject its edit"
done
restore
git -C "$tv" diff --quiet HEAD || die "certify.sh left changes in $tv"
[[ -z "$(git -C "$tv" status --porcelain -- solar-tv/milestone/counter)" ]] ||
  die "certify.sh left files the evidence does not have"

step "4. bind the source and the bytecode"
cmp -s "$sol" "$tv/solar-tv/milestone/counter/counter.sol" ||
  die "$sol and solar-tv/milestone/counter/counter.sol differ"
echo "$sol is solar-tv/milestone/counter/counter.sol byte for byte"
out="$(bin_runtime "$sol")"
[[ "$out" == "$bytecode" ]] || die "solar's bytecode is not the milestone's: $out"
check_bytecode "$out"
[[ "$(cat "$tv/solar-tv/milestone/counter/bytecode.hex")" == "$bytecode" ]] ||
  die "solar-tv's pinned bytecode.hex is not the milestone's"
manifest_sha="$(python3 -c 'import json,sys; print(json.load(open(sys.argv[1]))["bytecode_sha256"])' "$tv/$manifest/manifest.json")"
[[ "$manifest_sha" == "$bytecode_sha256" ]] || die "the manifest's sha256 is not the bytecode's"
grep -q "^def runtimeSha256 : String := \"$bytecode_sha256\"" "$lean_dir/Spec.lean" ||
  die "Spec.lean records another sha256"
grep -q "^  \"$bytecode\"\$" "$lean_dir/Spec.lean" || die "Spec.lean's runtimeHex has other bytes"
grep -q "^  0x$bytecode\$" "$lean_dir/Spec.lean" || die "Spec.lean's runtimeNat has other bytes"
grep -q "^def runtimeSize : Nat := $size\$" "$lean_dir/Spec.lean" ||
  die "Spec.lean's runtimeSize is not the bytecode's length"
echo "bytecode sha256 $bytecode_sha256 ($size bytes): solar's output, Spec.lean's literals and the manifest's"
if [[ -z "${SOLC-}" ]]; then
  cached="${XDG_CACHE_HOME:-$HOME/.cache}/solc/solc-$solc_version"
  if [[ ! -x "$cached" ]]; then
    mkdir -p "$(dirname "$cached")"
    curl -fsSL -o "$cached.tmp" \
      "https://github.com/argotorg/solidity/releases/download/v$solc_version/solc-static-linux" || true
    if [[ -s "$cached.tmp" ]] && echo "$solc_sha256  $cached.tmp" | sha256sum -c --quiet; then
      chmod +x "$cached.tmp"
      mv "$cached.tmp" "$cached"
    else
      rm -f "$cached.tmp"
    fi
  fi
  if [[ -x "$cached" ]] && echo "$solc_sha256  $cached" | sha256sum -c --quiet; then SOLC="$cached"; fi
fi
if [[ -n "${SOLC-}" ]]; then
  "$SOLC" --version | grep -q "Version: $solc_version+" || die "$SOLC is not solc $solc_version"
  {
    echo "-- Generated by scripts/refinement/counter/milestone.sh from $sol with solc $solc_version. Do not edit."
    echo
    echo "import SolidCore.Solidity.Checked"
    echo
    echo "open SolidCore.Solidity"
    echo
    python3 scripts/solc_ast_to_lean_source.py "$sol" --contract Counter --solc "$SOLC" \
      --namespace "SolidCore.Refinement.Source.Counter" --body-only |
      sed "s|^def importedSourceName : String := .*$|def importedSourceName : String := \"$sol\"|"
  } | diff -q - "$lean_dir/Source.lean" > /dev/null ||
    die "$lean_dir/Source.lean is not the source AST of $sol"
  echo "SolidCore's source AST of counter.sol regenerates to $lean_dir/Source.lean"
elif [[ -n "${REQUIRE_SOLC-}" ]]; then
  die "no solc $solc_version (set SOLC)"
else
  echo "skipped: no solc $solc_version, so the source AST check did not run"
fi

step "5. negative: mutated bytecode is rejected"
[[ "${bytecode:84:2}" == "01" ]] || die "offset 42 is not ADD"
[[ "${bytecode:100:2}" == "55" ]] || die "offset 50 is not SSTORE"
[[ "${bytecode:92:6}" == "604157" ]] || die "offsets 46 to 48 are not the overflow check's PUSH1 0x41 JUMPI"
no_check="${bytecode:0:92}505b5b${bytecode:98}"
grep -q "^  0x$no_check\$" "$lean_dir/NegativeAt.lean" || die "NegativeAt.lean's mutantNoCheckNat is not the mutant"
[[ "${bytecode:0:8}" == "34603457" ]] || die "offsets 0 to 3 are not the call value check's CALLVALUE PUSH1 0x34 JUMPI"
value="${bytecode:0:4}41${bytecode:6}"
grep -q "^  0x$value\$" "$lean_dir/NegativeValue.lean" || die "NegativeValue.lean's mutantValueNat is not the mutant"
for mutant in "${bytecode:0:84}03${bytecode:86}" "${bytecode:0:100}54${bytecode:102}" "$no_check" "$value"; do
  if check_bytecode "$mutant"; then die "a mutated bytecode passed the check"; fi
done
echo "the four mutants (ADD to SUB at 42, SSTORE to SLOAD at 50, the overflow check's PUSH1 0x41"
echo "JUMPI at 46 to POP JUMPDEST JUMPDEST, the call value check's jump target 0x34 to 0x41 at 2)"
echo "rejected by a mismatch, as expected; in Lean,"
echo "mutantAdd_no_walk, mutantStore_no_walk and mutantNoCheck_no_walk prove the assembly walk"
echo "rejects them, mutantAdd_check, mutantStore_check and mutantNoCheck_check that the generic"
echo "checker rejects them, lowering_rejects_bad proves the source stage false for a lowering with"
echo "SUB for ADD, and, from any storage, stageAt_rejects proves the assembly stage false for the"
echo "third mutant and loweringAt_rejects the source stage false for a lowering without"
echo "the overflow check, each by different observables on inc(1) from a full slot 0, and"
echo "assemblyValue_rejects the assembly stage on calls with value false for the fourth, by"
echo "different observables on get() with value 1 (the empty revert against Panic(0x11))"

step "6. build the proof chain and audit its axioms"
if [[ ! -f .lake/packages/mathlib/.lake/build/lib/lean/Mathlib.olean ]]; then
  lake exe cache get > "$logs/cache.log" 2>&1 || { tail -n 20 "$logs/cache.log" >&2; die "lake exe cache get failed"; }
  echo "Mathlib from its build cache"
fi
if ! lake build -KleanMemory="$memory" SolidCore.Refinement.Solar.Counter.Milestone \
    SolidCore.Refinement.Solar.Counter.Sequences > "$logs/build.log" 2>&1; then
  grep -E '^error' -A8 "$logs/build.log" | head -n 40 >&2
  die "lake build failed"
fi
tail -n 1 "$logs/build.log"
audit="$logs/Audit.lean"
cat > "$audit" <<'LEAN'
import SolidCore.Refinement.Solar.Counter.Sequences
import SolidCore.Refinement.Solar.Counter.Sequences
open SolidCore.Refinement.Solar.Counter
#check @certified
#check @certifiedAt
#print axioms certified
#print axioms certifiedAt
#print axioms satisfies
#print axioms satisfiesAt
#print axioms vcs
#print axioms shapeOk_eq_true
#print axioms lowering
#print axioms loweringAt
#print axioms SolarTV.Milestone.Counter.counter_mir_to_evmir
#print axioms stage
#print axioms stage_run
#print axioms stageAt
#print axioms stageAt_run
#print axioms stageAnyStorage
#print axioms check_ok
#print axioms SolidCore.Refinement.Solar.Assemble.stage_of_check
#print axioms target_run
#print axioms target_run_at
#print axioms lowering_rejects_bad
#print axioms mutantAdd_no_walk
#print axioms mutantStore_no_walk
#print axioms loweringAt_rejects
#print axioms mutantNoCheck_run_at
#print axioms stageAt_rejects
#print axioms mutantNoCheck_no_walk
#print axioms refinesSeq
#print axioms two_calls
#print axioms mutantAdd_check
#print axioms mutantStore_check
#print axioms mutantNoCheck_check
#check @certifiedEvery
#print axioms certifiedEvery
#print axioms certifiedSeqEvery
#print axioms satisfiesEvery
#print axioms source_run_every
#print axioms mir_run_every
#print axioms loweringEvery
#print axioms assemblyEvery
#print axioms certifiedValue
#print axioms target_run_value
#print axioms assemblyValue_rejects
#print axioms mutantValue_run
#print axioms mutantValue_check
#print axioms mutantValue_no_walk
#check @certifiedSeq
#check @total
#print axioms certifiedSeq
#print axioms total
LEAN
report="$(lake env lean -M "$memory" "$audit" 2>&1)"
echo "$report"
if grep -q "error" <<<"$report"; then die "the audit file does not check"; fi
bad="$(grep "depends on axioms" <<<"$report" |
  sed -E 's/.*depends on axioms: \[(.*)\]/\1/' | tr ',' '\n' | tr -d ' ' |
  grep -v -x -E 'propext|Classical\.choice|Quot\.sound' || true)"
[[ -z "$bad" ]] || die "axioms beyond propext, Classical.choice and Quot.sound: $bad"
[[ "$(grep -c "depends on axioms" <<<"$report")" -eq 45 ]] || die "a theorem is missing from the audit"

step "7. negative: the generic assembly checker rejects the mutated bytecode"
# stage_of_check for the counter's program and certificate on the bytes given, the check by the
# kernel.
generic_stage() {
  cat > "$logs/$1.lean" <<LEAN
import SolidCore.Refinement.Solar.Counter.Assembly
open SolidCore.Refinement.Solar
set_option maxRecDepth 100000 in
theorem generic_stage (o : SolarTV.Machine.Oracle) :
    SolarTV.Stage (SolarTV.evmirSem o) SolidCore.Refinement.ethLib SolarTV.Export.Counter.evm5
      (EthLib.Execution.Evm.Logic.NatCode.ofNat 0x$2 Counter.runtimeSize) Counter.scope :=
  Assemble.stage_of_check
    (show Assemble.check SolarTV.Export.Counter.evm5
      (EthLib.Execution.Evm.Logic.NatCode.ofNat 0x$2 Counter.runtimeSize) Counter.cert = true by
      decide +kernel) o fun _ h => Counter.scope_value h
#print axioms generic_stage
LEAN
  # A mutant's case fails by design: its error is the output to check.
  { lake env lean -M "$memory" "$logs/$1.lean" 2>&1 || true; } | tr -s '[:space:]' ' '
}
control="$(generic_stage control "$bytecode")"
[[ "$control" == *"depends on axioms: [propext, Classical.choice, Quot.sound]"* && "$control" != *error* ]] ||
  die "stage_of_check does not prove the stage for solar's bytecode: $control"
echo "control: stage_of_check proves the stage for solar's bytecode (propext, Classical.choice, Quot.sound)"
for case in "add ${bytecode:0:84}03${bytecode:86}" "store ${bytecode:0:100}54${bytecode:102}" \
    "no_check $no_check" "value $value"; do
  name="${case%% *}"
  edited="$(generic_stage "mutant_$name" "${case#* }")"
  grep -q -E 'error: Tactic `decide` proved that the proposition Assemble\.check SolarTV\.Export\.Counter\.evm5 .* Counter\.cert = true is false' <<<"$edited" ||
    die "the $name mutant did not fail the generic checker: $edited"
  echo "$name mutant rejected by a mismatch, as expected: the kernel evaluates Assemble.check to false"
done

printf '\nok: counter milestone checked (solar %s, bytecode sha256 %s)\n' "$solar_rev" "$bytecode_sha256"

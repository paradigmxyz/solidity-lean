#!/usr/bin/env bash
# The w5 milestone in one command: solar's bytecode for w5 meets w5's verified specification,
# with every stage of solar's pipeline proved in Lean.
#
#   scripts/refinement/w5-milestone.sh
#
# 1. Puts the solar checkout that lakefile.lean requires (its solar_tv path, ../ck-pipeline
#    next to this repository; fetched from SOLAR_REPO, a clone, bundle or URL whose branches
#    hold the pinned commit, when it is not a git checkout yet, even if restored builds are
#    there) at the pinned solar commit, and checks that its compiler sources are those of the
#    commit the evidence names, except for the stage exporter (crates/codegen/src/lean_stages.rs),
#    which only prints the stages as Lean.
# 2. Builds solar (cargo, CARGO_TARGET_DIR, default target in that checkout).
# 3. Runs solar-tv/milestone/w1/gen.sh: compiles w1.sol with -Ogas --evm-version osaka and
#    -Zemit-lean-stages, checks the bytecode and the manifest's hashes, and builds the stages.
#    Then checks that every regenerated file is the committed evidence, byte for byte except
#    for the compiler's build commit in its version, and restores the committed files.
# 4. Binds the source: w5.sol (which SolidCore parses) is w1.sol (which solar's stages come
#    from) up to comments and whitespace, solar compiles both to the same bytecode, the Lean
#    literals and sha256s are solar's output, and, with solc 0.8.35 (SOLC, checked to be that
#    version; else the cached or downloaded release, checked by its sha256), the SolidCore
#    source AST regenerates to the committed Source/W5.lean. Without network and SOLC, that
#    one check is skipped and reported, unless REQUIRE_SOLC=1.
# 5. Negative tests: a one-byte mutation of the bytecode fails the artifact check, and
#    solar-tv's negative.sh shows meaning-changing edits of the bytecode and of stage outputs
#    fail their proofs with a mismatch (the assembly walk, or sym_exec on a path whose runs end
#    differently), with unedited controls passing.
# 6. Fetches Mathlib's build cache when Mathlib is not built, builds the proof chain with lake
#    under a cap per Lean process (LEAN_MEMORY, MB, default 4500), and prints the axioms of the
#    final theorems (certified, certifiedAt from any initial storage, and certifiedValue on
#    every call with a nonzero value, which f rejects because it is not payable), each stage,
#    the generic assembly theorem and the negative tests (loweringValue_rejects: the source
#    stage on the value scope is false for a lowering without the call value check), failing
#    on any axiom beyond propext, Classical.choice and Quot.sound. One module needs more: the
#    statement lowering's mutual block (SolidCore/Solidity/Interface/Statements.lean) peaks at
#    about 5.4 GB in the kernel on one thread, so it builds first and alone, on one thread,
#    under W5_LOWERING_MEMORY (MB, default 7000).
# 7. Negative test of the generic assembly theorem: Assemble.stage_of_check, applied to the
#    bytes this script gives it with the checker run by the kernel, proves w1's assembly stage
#    for solar's bytecode (only the three axioms) and fails for the step 5 mutant, where the
#    checker evaluates to false.
#
# It needs git, cargo, python3, curl and elan (Lean 4.35.0 from lean-toolchain); a fresh
# directory works: clone this repository, set SOLAR_REPO, and run it. Each step's time is
# printed at the end.
set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$root"

# solar: branch ck-pipeline, the exporter, the backend stage proofs on Lean 4.35.0 and the
# generator of backend stage proofs (certify.sh), whose output w1's proofs are.
solar_rev=f19e9e46309c7cdb3a0f36668f7881d12bb8503a
# The commit whose compiler sources built the committed evidence (its manifest's compiler).
compiler_rev=7b1f8a1b4a98fd79903551f488da83432d919c5a
# The runtime bytecode, 68 bytes.
bytecode=34602e575f3560e01c806313d1aa2e03602e5760443610602e5760043560243581019081106032575f5260205ff35b5f5ffd5b6011602052634e487b715f526024601cfd
bytecode_sha256=24d2438e4d77b39b2530aac7af63774b10576eabc3c093d282620ab44403778b
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
work="$(mktemp -d)"
trap 'rm -rf "$work"' EXIT
start=$SECONDS
last=$SECONDS
times=()
step_name=
step() {
  if [[ -n "$step_name" ]]; then times+=("$step_name $((SECONDS - last))s"); fi
  last=$SECONDS
  step_name="${1%%.*}"
  printf '\n== %s\n' "$*"
}
die() { echo "error: $*" >&2; exit 1; }
sha_hex() { python3 -c 'import hashlib,sys; print(hashlib.sha256(bytes.fromhex(sys.argv[1])).hexdigest())' "$1"; }
bin_runtime() {
  "$solar" "$1" -Ogas --evm-version osaka --emit=bin-runtime 2>/dev/null |
    python3 -c 'import json,sys; c=json.load(sys.stdin)["contracts"]; print(next(v["bin-runtime"] for k,v in c.items() if k.endswith(":Main")))'
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

step "3. regenerate solar's stages and compare them with the evidence"
gen=solar-tv/milestone/w1/gen
restore() { git -C "$tv" checkout -q -- "$gen"; git -C "$tv" clean -qfd -- "$gen"; }
trap 'restore; rm -rf "$work"' EXIT
W1_SKIP_BUILD=1 SOLAR="$solar" "$tv/solar-tv/milestone/w1/gen.sh"
[[ -z "$(git -C "$tv" ls-files --others --exclude-standard -- "$gen")" ]] ||
  die "gen.sh wrote files the evidence does not have"
norm() { sed -E 's/commit\.[0-9a-f]{8}/commit.<build>/g'; }
for file in $(git -C "$tv" ls-files -- "$gen"); do
  if ! diff -q <(git -C "$tv" show "HEAD:$file" | norm) <(norm < "$tv/$file") > /dev/null; then
    git -C "$tv" diff -- "$file" | head -n 40 >&2
    die "regenerated $file is not the committed evidence"
  fi
done
echo "every file of $gen regenerates to the committed evidence (stages, bytecode, manifest)"
restore
trap 'rm -rf "$work"' EXIT

step "4. bind the source and the bytecode"
w1="$tv/solar-tv/milestone/w1/w1.sol"
w5=scripts/refinement/corpus/w5.sol
strip_sol() { sed -E 's|//.*$||' "$1" | tr -s '[:space:]' ' ' | sed -E 's/ ?([{}();,]) ?/\1/g; s/^ //; s/ $//'; }
[[ "$(strip_sol "$w1")" == "$(strip_sol "$w5")" ]] || die "$w5 and w1.sol are different contracts"
echo "w5.sol and w1.sol are the same source up to comments and whitespace"
out1="$(bin_runtime "$w1")"
out5="$(bin_runtime "$w5")"
[[ "$out1" == "$bytecode" && "$out5" == "$bytecode" ]] || die "solar's bytecode is not the milestone's"
check_bytecode "$out1"
manifest_sha="$(python3 -c 'import json,sys; print(json.load(open(sys.argv[1]))["bytecode_sha256"])' "$tv/$gen/Main/manifest.json")"
[[ "$manifest_sha" == "$bytecode_sha256" ]] || die "the manifest's sha256 is not the bytecode's"
grep -q "def Main.runtimeSha256 : String := \"$bytecode_sha256\"" SolidCore/Refinement/Bytecode/W5.lean ||
  die "Bytecode/W5.lean records another sha256"
grep -q "^  0x$bytecode\$" SolidCore/Refinement/Bytecode/W5.lean || die "Bytecode/W5.lean has other bytes"
scripts/refinement/check-solar-w1.sh "$solar" "$w1" | tail -n 1
echo "bytecode sha256 $bytecode_sha256 (68 bytes)"
solc_skipped=
if [[ -n "${SOLC-}" ]]; then
  "$SOLC" --version | grep -q "Version: $solc_version+" ||
    die "SOLC is $("$SOLC" --version | tail -n 1), not solc $solc_version"
else
  SOLC="${XDG_CACHE_HOME:-$HOME/.cache}/solc/solc-$solc_version"
  if [[ ! -x "$SOLC" ]]; then
    mkdir -p "$(dirname "$SOLC")"
    if curl -fsSL -o "$SOLC.tmp" \
      "https://github.com/argotorg/solidity/releases/download/v$solc_version/solc-static-linux"; then
      chmod +x "$SOLC.tmp"
      mv "$SOLC.tmp" "$SOLC"
    else
      rm -f "$SOLC.tmp"
      [[ -z "${REQUIRE_SOLC-}" ]] || die "cannot download solc $solc_version; set SOLC"
      solc_skipped=1
    fi
  fi
  if [[ -z "$solc_skipped" ]]; then
    echo "$solc_sha256  $SOLC" | sha256sum -c --quiet || die "$SOLC is not the solc $solc_version release"
  fi
fi
if [[ -n "$solc_skipped" ]]; then
  echo "SKIPPED: no solc $solc_version (set SOLC or allow the download); the source AST is not regenerated"
else
# The generator's commands for one source, as scripts/refinement/gen.sh runs them.
{
  echo "-- Generated by scripts/refinement/gen.sh from $w5 with solc $solc_version. Do not edit."
  echo
  echo "import SolidCore.Solidity.Checked"
  echo
  echo "open SolidCore.Solidity"
  echo
  python3 scripts/solc_ast_to_lean_source.py "$w5" --contract Main --solc "$SOLC" \
    --namespace "SolidCore.Refinement.Source.W5" --body-only |
    sed "s|^def importedSourceName : String := .*$|def importedSourceName : String := \"$w5\"|"
} | diff -q - SolidCore/Refinement/Source/W5.lean > /dev/null ||
  die "SolidCore/Refinement/Source/W5.lean is not the source AST of $w5"
echo "SolidCore's source AST of w5.sol regenerates to SolidCore/Refinement/Source/W5.lean"
fi

step "5. negative: a mutated bytecode is rejected"
[[ "${bytecode:66:2}" == "01" ]] || die "offset 33 is not ADD"
mutant="${bytecode:0:66}03${bytecode:68}"  # offset 33: ADD (01) to SUB (03)
if check_bytecode "$mutant"; then die "the mutated bytecode passed the check"; fi
echo "rejected by a mismatch, as expected; in Lean, mutant_not_stage proves the assembly stage"
echo "false for it, and lowering_rejects_bad the source stage false for a lowering with SUB for ADD"
(cd "$tv/solar-tv" && lake build W1Proofs > /dev/null 2>&1) || die "lake build W1Proofs failed in $tv/solar-tv"
LEAN_MEMORY="$memory" "$tv/solar-tv/milestone/w1/proofs/negative.sh"

step "6. build the proof chain and audit its axioms"
if [[ ! -f .lake/packages/mathlib/.lake/build/lib/lean/Mathlib.olean ]]; then
  lake exe cache get > "$work/cache.log" 2>&1 || { tail -n 20 "$work/cache.log" >&2; die "lake exe cache get failed"; }
  echo "Mathlib from its build cache"
fi
log="${W5_BUILD_LOG:-$work/build.log}"
# Builds with lake, appending to the log, and fails with its errors.
build() {
  if ! "$@" >> "$log" 2>&1; then
    grep -E '^error' "$log" | head -n 20 >&2
    cp "$log" "${TMPDIR:-/tmp}/w5-milestone-build.log"
    die "$* failed (${TMPDIR:-/tmp}/w5-milestone-build.log)"
  fi
}
: > "$log"
# The statement lowering alone, after its imports, so that no other Lean process runs beside it.
# Lake keeps the configuration it last elaborated, -K options included: -R makes each cap apply.
build lake build -R -KleanMemory="$memory" SolidCore.Solidity.Interface.Expressions
build env LEAN_NUM_THREADS=1 lake build -R -KleanMemory="${W5_LOWERING_MEMORY:-7000}" \
  SolidCore.Solidity.Interface.Statements
build lake build -R -KleanMemory="$memory" W1Proofs SolidCore.Refinement.Solar.Milestone \
  SolidCore.Refinement.Solar.W1Value SolidCore.Refinement.Solar.Sequences
tail -n 1 "$log"
audit="$work/audit.lean"
cat > "$audit" <<'LEAN'
import SolidCore.Refinement.Solar.Milestone
import SolidCore.Refinement.Solar.W1Value
import SolidCore.Refinement.Solar.Sequences
import W1Proofs
open SolidCore.Refinement.Solar.W1
#check @certified
#check @certifiedAt
#check @certifiedValue
#check @certifiedSeq
#print axioms certified
#print axioms certifiedAt
#print axioms certifiedSeq
#print axioms lowering
#print axioms loweringAt
#print axioms SolarTV.Milestone.W1.w1_mir_to_evmir
#print axioms stage
#print axioms stageAt
#print axioms stageAt_run
#print axioms SolidCore.Verify.W5.satisfies
#print axioms SolidCore.Verify.W5.satisfiesAt
#print axioms SolidCore.Refinement.Corpus.W5.shapeOk_eq_true
#print axioms lowering_rejects_bad
#print axioms mutant_not_stage
#print axioms mutant_no_walk
#print axioms certifiedValue
#print axioms satisfiesValue
#print axioms source_run_value
#print axioms loweringValue
#print axioms target_run_value
#print axioms assemblyValue
#print axioms loweringValue_rejects
#print axioms SolidCore.Refinement.Solar.Assemble.stage_of_check
#print axioms stage_run
#print axioms check_ok
#print axioms mutant_check
LEAN
report="$(lake env lean -M "$memory" "$audit" 2>&1)"
echo "$report"
if grep -q "error" <<<"$report"; then die "the audit file does not check"; fi
bad="$(grep "depends on axioms" <<<"$report" |
  sed -E 's/.*depends on axioms: \[(.*)\]/\1/' | tr ',' '\n' | tr -d ' ' |
  grep -v -x -E 'propext|Classical\.choice|Quot\.sound' || true)"
[[ -z "$bad" ]] || die "axioms beyond propext, Classical.choice and Quot.sound: $bad"
[[ "$(grep -c "depends on axioms" <<<"$report")" -eq 26 ]] || die "a theorem is missing from the audit"

step "7. negative: the generic assembly checker rejects the mutated bytecode"
# stage_of_check for w1's program and certificate on the bytes given, the check by the kernel.
generic_stage() {
  cat > "$work/$1.lean" <<LEAN
import SolidCore.Refinement.Solar.W1
open SolidCore.Refinement.Solar
set_option maxRecDepth 100000 in
theorem generic_stage (o : SolarTV.Machine.Oracle) :
    SolarTV.Stage (SolarTV.evmirSem o) SolidCore.Refinement.ethLib W1.program
      (EthLib.Execution.Evm.Logic.NatCode.ofNat 0x$2 W1.runtimeSize) W1.scope :=
  Assemble.stage_of_check
    (show Assemble.check W1.program (EthLib.Execution.Evm.Logic.NatCode.ofNat 0x$2 W1.runtimeSize)
      W1.cert = true by decide +kernel) o fun _ h => (W1.scope_facts h).1
#print axioms generic_stage
LEAN
  # The mutant's case fails by design: its error is the output to check.
  { lake env lean -M "$memory" "$work/$1.lean" 2>&1 || true; } | tr -s '[:space:]' ' '
}
control="$(generic_stage control "$bytecode")"
[[ "$control" == *"depends on axioms: [propext, Classical.choice, Quot.sound]"* && "$control" != *error* ]] ||
  die "stage_of_check does not prove the stage for solar's bytecode: $control"
echo "control: stage_of_check proves the stage for solar's bytecode (propext, Classical.choice, Quot.sound)"
edited="$(generic_stage mutant "$mutant")"
grep -q -E 'error: Tactic `decide` proved that the proposition Assemble\.check W1\.program .* W1\.cert = true is false' <<<"$edited" ||
  die "the mutated bytecode did not fail the generic checker: $edited"
echo "rejected by a mismatch, as expected: the kernel evaluates Assemble.check on the mutant to false"

times+=("$step_name $((SECONDS - last))s")
echo "step times (step seconds): ${times[*]}; total $((SECONDS - start))s"
skipped="${solc_skipped:+ (source AST regeneration skipped: no solc)}"
printf '\nok: w5 milestone checked (solar %s, bytecode sha256 %s)%s\n' "$solar_rev" "$bytecode_sha256" "$skipped"

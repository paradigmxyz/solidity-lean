import Lake
open Lake DSL

-- The EVM semantics the refinement theorems run solar's bytecode on.
require EthLib from git
  "https://github.com/ethereum/EthLib.git" @ "2cd5d14a6a2f6fd22ef6b68423e45cfa3a21001a"

-- evmyul and evm-interaction are vendored with the changes Lean 4.35 needs; see
-- vendor/README.md.
require evmyul from "vendor" / "evmyul"

-- The shared "language of composition": the interaction monad, Query/Answer,
-- OpenWorld, and ForwardRel, extracted verbatim from evm-compiler.
require «evm-interaction» from "vendor" / "evm-interaction"

-- Mathlib at the release EthLib builds against. Listed last, so its pins of
-- Batteries, Aesop and the rest win over older ones further up.
require "leanprover-community" / "mathlib" @ git "v4.35.0"

package «solidity-lean» where
  -- `lake build -KleanMemory=4500` caps each Lean process's memory in MB, without changing
  -- the build's traces.
  weakLeanArgs := match get_config? leanMemory with
    | some mb => #["-M", mb]
    | none => #[]
  leanOptions := #[
    ⟨`maxHeartbeats, 1000000⟩,
    -- Lean 4.35's new `do` elaborator drops the `match` hypotheses that the
    -- automatic termination proofs of the checker and interpreter rely on.
    ⟨`backward.do.legacy, true⟩
  ]

-- The default root retains every proof and witness in the full build.
@[default_target]
lean_lib SolidCore where

-- c1's hand-written refinement evaluates SolidCore with `native_decide`, which trusts Lean's
-- compiler, so it stays out of the default library: `lake build SolidCoreNative`.
lean_lib SolidCoreNative where
  roots := #[`SolidCore.Refinement.C1.Spec]

-- The giant statement-lowering mutual block takes much longer to optimize in
-- C than to execute once per prepared fixture. Keep its development build cheap;
-- opt into -O3 with `lake -KspecHuntLoweringO3=true build` for throughput profiling.
lean_lib SolidCoreStatementLowering where
  roots := #[`SolidCore.Solidity.Interface.Statements]
  moreLeancArgs := if get_config? specHuntLoweringO3 == some "true" then #[] else #["-O0"]

-- w4's stages against solar's own (solar-tv/milestone/w4), outside the default root: w4's
-- exported stages share their names (SolarTV.Export.Main) with w1's, which the root imports.
lean_lib SolidCoreSolarW4 where
  roots := #[`SolidCore.Refinement.Solar.W4.Milestone]

-- c4's source stage against solar's first lowered MIR (solar-tv/milestone/c4's export), composed
-- with solar-tv's backend stages and the assembly stage into one theorem from SolidCore to the
-- bytecode (Solar/C4/Certified.lean), outside the default root for the same reason.
lean_lib SolidCoreSolarC4 where
  roots := #[`SolidCore.Refinement.Solar.C4.Lowering, `SolidCore.Refinement.Solar.C4.LoweringGeneric,
    `SolidCore.Refinement.Solar.C4.Assembly, `SolidCore.Refinement.Solar.C4.Certified]

-- The generic source stage against solar's first lowered MIR of a narrow-mul test contract
-- (scripts/refinement/mulx/mul.sol; solar-tv/milestone/mulx, solar's export at a8179dfc),
-- composed with solar-tv's backend stages and the assembly stage into one theorem from
-- SolidCore to the bytecode (Solar/MulX/Certified.lean), outside the default root for the same
-- reason. Lowering.lean and Certified.lean need -KleanMemory=6000 (peaks of 5.4 and 4.3 GB).
lean_lib SolidCoreSolarMulX where
  roots := #[`SolidCore.Refinement.Solar.MulX.Lowering, `SolidCore.Refinement.Solar.MulX.Certified]

/-- Compile precisely the observable helper's semantic import closure. Using
individual module objects avoids building every library root in evmyul/Mathlib
(the pinned evmyul package has no Conform.lean root). -/
target specHuntNative pkg : Dynlib := do
  let some root := pkg.findModule? `SolidCore.Contest.Observable
    | error "missing SolidCore.Contest.Observable"
  let imports ← (← root.transImports.fetch).await
  let mods := imports.push root
  let objects ← mods.flatMapM fun mod =>
    (mod.nativeFacets true).mapM (·.fetch mod)
  let (_, libraries) ← mods.foldlM (init := (({} : Lean.NameSet), #[])) fun (seen, jobs) mod => do
    if seen.contains mod.pkg.keyName then return (seen, jobs)
    let libs ← mod.pkg.externLibs.mapM (·.static.fetch)
    return (seen.insert mod.pkg.keyName, jobs ++ libs)
  -- Mathlib's import closure reaches ImportGraph, which links Lake, so the
  -- plugin needs the toolchain's shared libraries at load time.
  let rpath := s!"-Wl,-rpath,{(← getLeanLibDir)}"
  buildLeanSharedLib "specHuntNative"
    (pkg.sharedLibDir / nameToSharedLib "specHuntNative")
    (objects ++ libraries) #[] #[rpath] #[] (plugin := true)

-- Only witnesses load the native semantic plugin. Proofs and the semantic
-- modules still elaborate normally; this introduces no alternative evaluator.
lean_lib SolidCoreWitness where
  roots := #[`SolidCore.Witness]
  globs := #[.submodules `SolidCore.Witness]
  dynlibs := if get_config? specHuntNative == some "false" then #[]
             else #[{ key := .packageTarget .anonymous `specHuntNative }]

/-- Byte-parity witness for the repo-owned pure Keccak vs the pinned FFI hash.
    `supportInterpreter` + the transitively-linked `libleanffi` let the native
    pinned `keccak256` be compared against the pure implementation. -/
lean_exe keccakParity where
  root := `KeccakParity
  supportInterpreter := true

/-- Byte-parity witness for the in-semantics precompile implementations
    (`Precompile.execute?` / `Shared.Crypto`): sha256 and blake2f against the
    pinned NATIVE FFI, the rest against published known-answer vectors. -/
lean_exe precompileParity where
  root := `PrecompileParity
  supportInterpreter := true

/-- Native execution of harness-generated input using the same checked semantics.
    Proof elaboration remains part of the normal library build. -/
lean_exe specHuntRunner where
  root := `SpecHuntRunner
  supportInterpreter := true

/-- Loom's monad algebras and weakest preconditions, ported to Lean 4.35 (Loom/README.md). Only
the ported modules are kept; every one builds. -/
lean_lib Loom where
  roots := #[`Loom]
  globs := #[.andSubmodules `Loom]

/-- Verification on top of SolidCore: the Loom-based VC generator and the specs it proves
(Verify/*.lean), solar-verify's spec language with ghost erasure and its trusted base
(Verify/Spec), solar-verify's VCs checked against Loom models (Verify/VC) and the composition
of a source triple with the refinement to bytecode (Verify/Final.lean). `lake build Verify`
builds the root's closure; the libraries below hold the heavier, generated-input parts. -/
lean_lib Verify where
  roots := #[`Verify]

-- bank's and events' assembly stages against solar's exports (solar-tv/milestone/bank and
-- solar-tv/milestone/events at 0a455fda): the generic assembler check with mapping hashes,
-- CALLER, LOG2 and LOG3 and internal calls through pushed return labels, under an oracle whose
-- caller and hash are EthLib's, and bank's composition from its first lowered MIR. Outside the
-- default root: the exports share solar-tv's milestone libraries. Each module fits in
-- -KleanMemory=3000 (peaks of 2.6 GB, 2.3 GB of them the imports' mapped oleans): the kernel
-- evaluates the check's one-pass form (Solar/AssembleFast.lean).
lean_lib SolidCoreSolarBank where
  roots := #[`SolidCore.Refinement.Solar.Bank.Assembly, `SolidCore.Refinement.Solar.Bank.Mutants,
    `SolidCore.Refinement.Solar.Events.Assembly]

-- The generic source stages of bank and events (SolidCore to solar's first lowered MIR) and
-- their composition with solar-tv's backend stages and the assembly stage, outside the default
-- root for the same reason. Bank/Lowering.lean needs -KleanMemory=3500 (a peak of 3.4 GB); the rest
-- fit in 3000, and Bank/Certified.lean and Events/Certified.lean bind the theorems to the exports'
-- manifests (Solar/Hex.lean decodes the manifest's hex).
lean_lib SolidCoreSolarBankSource where
  roots := #[`SolidCore.Refinement.Solar.Bank.Lowering, `SolidCore.Refinement.Solar.Events.Lowering,
    `SolidCore.Refinement.Solar.Bank.Certified, `SolidCore.Refinement.Solar.Events.Certified,
    `SolidCore.Refinement.Solar.Total]

-- SolidCore ends on bank's, events' and mulx's certified scopes (within fuel 4096), so their
-- certified stages are total refinements (Solar/Totality.lean). Outside the default root: it
-- imports the three certified theorems. Fits in -KleanMemory=3000.
lean_lib SolidCoreSolarTotality where
  roots := #[`SolidCore.Refinement.Solar.Totality]

-- The assembly checker for code with loops on reads of the block and the transaction, ADDRESS
-- and SLT: an accepted program and its kernel-checked execution theorem, and a mutant of an
-- environment read that the checker rejects by evaluation (Solar/AssembleLoopEnv.lean).
lean_lib SolidCoreSolarAssemblyEnv where
  roots := #[`SolidCore.Refinement.Solar.AssembleLoopEnv]

-- The assembly theorem in its per-run oracle form (Solar/RunOracle.lean), and what GAS,
-- RETURNDATASIZE, RETURNDATACOPY, CALLDATACOPY and STATICCALL do in SolarTV and EthLib, one
-- instruction at a time, under the oracle of a run (Solar/AssembleEffects.lean), and the
-- refinement at the gas a run has from a block simulation under the runner of messages
-- (Solar/AssembleRun.lean), met by every program the loop checker accepts
-- (Solar/AssembleRunLoop.lean), and by every program the checker with contexts accepts, which
-- types an internal function once per call site (Solar/AssembleCtx.lean).
lean_lib SolidCoreSolarRunOracle where
  roots := #[`SolidCore.Refinement.Solar.RunOracle, `SolidCore.Refinement.Solar.AssembleEffects,
    `SolidCore.Refinement.Solar.AssembleRun, `SolidCore.Refinement.Solar.AssembleRunLoop,
    `SolidCore.Refinement.Solar.RunOracleSource,
    `SolidCore.Refinement.Solar.AssembleCut, `SolidCore.Refinement.Solar.AssembleDyn,
    `SolidCore.Refinement.Solar.AssembleMem, `SolidCore.Refinement.Solar.AssembleDynCopy,
    `SolidCore.Refinement.Solar.AssembleDynExample, `SolidCore.Refinement.Solar.AssembleCall,
    `SolidCore.Refinement.Solar.AssembleCallWorld, `SolidCore.Refinement.Solar.AssembleCallCut,
    `SolidCore.Refinement.Solar.AssembleCallSeg, `SolidCore.Refinement.Solar.AssembleCallExample,
    `SolidCore.Refinement.Solar.AssembleCallPre, `SolidCore.Refinement.Solar.AssembleCallStatic,
    `SolidCore.Refinement.Solar.AssembleCallStaticRunner, `SolidCore.Refinement.Solar.AssembleCtxTrack,
    `SolidCore.Refinement.Solar.AssembleCtx, `SolidCore.Refinement.Solar.AssembleCtxExample,
    `SolidCore.Refinement.Solar.AssembleCtxCall,
    `SolidCore.Refinement.Solar.AssembleNoCall, `SolidCore.Refinement.Solar.AssembleNoCallExample,
    `SolidCore.Refinement.Solar.AssembleCtxGas, `SolidCore.Refinement.Solar.AssembleCtxGasFrom]

-- Runs that revert: no step of EthLib throws a revert and only REVERT ends a frame with it
-- (Solar/EthLibErr.lean), so a run with less gas that reverts follows the run with more
-- (Solar/EthLibErrLow.lean), and the loop checker's theorem relates revert data
-- (Solar/AssembleRevert.lean), and so does the checker with GAS and memory at any offset
-- (Solar/AssembleRevertCut.lean), each with an example and mutants (Solar/AssembleRevert*Example.lean).
lean_lib SolidCoreSolarRevert where
  roots := #[`SolidCore.Refinement.Solar.EthLibErr, `SolidCore.Refinement.Solar.EthLibErrLow,
    `SolidCore.Refinement.Solar.AssembleRevert, `SolidCore.Refinement.Solar.AssembleRevertExample,
    `SolidCore.Refinement.Solar.AssembleRevertCut, `SolidCore.Refinement.Solar.AssembleRevertCutExample,
    `SolidCore.Refinement.Solar.AssembleRevertCall]

-- CODECOPY, CALL with value and CREATE2 at the frame's own gas, from a run that succeeds, and what
-- they do in SolarTV (Solar/AssembleCodeCopy.lean, Solar/AssembleCallValue.lean,
-- Solar/AssembleCreate.lean).
lean_lib SolidCoreSolarCreate where
  roots := #[`SolidCore.Refinement.Solar.AssembleCodeCopy, `SolidCore.Refinement.Solar.AssembleCreate,
    `SolidCore.Refinement.Solar.AssembleCallValue, `SolidCore.Refinement.Solar.AssembleCreateBack,
    `SolidCore.Refinement.Solar.AssembleCallValueEffect, `SolidCore.Refinement.Solar.AssembleCallValueZero,
    `SolidCore.Refinement.Solar.AssembleCreateSeg, `SolidCore.Refinement.Solar.AssembleCallValueSeg,
    `SolidCore.Refinement.Solar.AssembleCallValueZeroSeg,
    `SolidCore.Refinement.Solar.AssembleCreateSegOracle, `SolidCore.Refinement.Solar.AssembleCreateExample,
    `SolidCore.Refinement.Solar.AssembleCreateCut,
    `SolidCore.Refinement.Solar.AssembleCreateRun, `SolidCore.Refinement.Solar.AssembleCreateCutQ,
    `SolidCore.Refinement.Solar.AssembleCreateSegF, `SolidCore.Refinement.Solar.AssembleCreateRunF]

/-! solar's translation validation (formerly solar's `solar-tv` Lean package, moved here so that
every Lean source of the certified translation lives in this repository; solar keeps only the
stage exporter and the drivers that generate Lean against a pinned commit of this repository).
These libraries keep Lean's default options (as their own package had), not the ones above. -/

/-- The option defaults of solar's former `solar_tv` package. -/
def solarTVOptions : Array LeanOption := #[
  ⟨`maxHeartbeats, (200000 : Nat)⟩,
  ⟨`backward.do.legacy, false⟩
]

/-- solar's word semantics and rewrite-rule lemmas (`EvmRules`), vendored from solar's
scripts/evm-rules/lean at the commit vendor/evm-rules/README.md names. -/
lean_lib EvmRules where
  srcDir := "vendor/evm-rules"
  globs := #[.andSubmodules `EvmRules]
  leanOptions := solarTVOptions

/-- MIR and EVM IR semantics, the stages and their refinement, assembly walk, cut points and
symbolic memory laws. -/
lean_lib SolarTV where
  srcDir := "tv"
  globs := #[.andSubmodules `SolarTV]
  leanOptions := solarTVOptions

/-- The symbolic-execution procedures and assembly items that the generated per-contract proofs
use, and w1's own stage proofs. Symbolic execution is heavy: fail on running out of memory rather
than exhaust the machine. -/
lean_lib W1Proofs where
  srcDir := "tv"
  globs := #[.andSubmodules `W1Proofs]
  leanOptions := solarTVOptions
  moreLeanArgs := #["-M", "3000"]

/-! Generated per-contract stages and proofs that the headline theorems import, as solar's
exporter and certify driver write them (Certified/<name>/gen and Certified/<name>/Proofs, module
names without a `Certified` prefix). Regenerate with solar's certify driver; see
Certified/README.md. -/

/-- w1's exported stages and their checks. -/
lean_lib W1 where
  srcDir := "Certified/w1"
  roots := #[`W1]
  globs := #[.andSubmodules `W1, .submodules `gen]
  leanOptions := solarTVOptions

lean_lib counter where
  srcDir := "Certified"
  roots := #[`counter.Proofs]
  globs := #[.submodules `counter]
  leanOptions := solarTVOptions
  moreLeanArgs := #["-M", "3000"]

lean_lib w4 where
  srcDir := "Certified"
  roots := #[`w4.Proofs]
  globs := #[.submodules `w4]
  leanOptions := solarTVOptions
  moreLeanArgs := #["-M", "3000"]

lean_lib masks where
  srcDir := "Certified"
  roots := #[`masks.Proofs]
  globs := #[.submodules `masks]
  leanOptions := solarTVOptions
  moreLeanArgs := #["-M", "3000"]

lean_lib bank where
  srcDir := "Certified"
  roots := #[`bank.Proofs]
  globs := #[.submodules `bank]
  leanOptions := solarTVOptions
  moreLeanArgs := #["-M", "3000"]

lean_lib c4 where
  srcDir := "Certified"
  roots := #[`c4.Proofs]
  globs := #[.submodules `c4]
  leanOptions := solarTVOptions
  moreLeanArgs := #["-M", "3000"]

lean_lib mulx where
  srcDir := "Certified"
  roots := #[`mulx.Proofs]
  globs := #[.submodules `mulx]
  leanOptions := solarTVOptions
  moreLeanArgs := #["-M", "3000"]

lean_lib events where
  srcDir := "Certified"
  roots := #[`events.Proofs]
  globs := #[.submodules `events]
  leanOptions := solarTVOptions
  moreLeanArgs := #["-M", "3000"]

lean_lib reader where
  srcDir := "Certified"
  roots := #[`reader.Proofs]
  globs := #[.submodules `reader]
  leanOptions := solarTVOptions
  moreLeanArgs := #["-M", "3000"]

/-- solar-verify's Token (Contracts/Token/VC's source): its exported stages and backend proofs. -/
lean_lib verify_token where
  srcDir := "Certified"
  roots := #[`verify_token.Proofs]
  globs := #[.submodules `verify_token]
  leanOptions := solarTVOptions
  -- Shape.lean peaks at 2.9 GB with LEAN_NUM_THREADS=2 (CI's setting), above a 3000 MB cap.
  moreLeanArgs := #["-M", "4500"]

-- solar-verify's spec language: its meaning over SolidCore's and EthLib's calls and observables,
-- ghost erasure, the trusted base as named hypotheses, and the specs solar-verify exports
-- (Verify/Spec, scripts/refinement/spec/check.sh).
lean_lib VerifySpec where
  roots := #[`Verify.Spec.Syntax, `Verify.Spec.Semantics, `Verify.Spec.Contract,
    `Verify.Spec.Ghost, `Verify.Spec.GhostFree, `Verify.Spec.TrustedBase,
    `Verify.Spec.TrustedBase.Hypotheses, `Verify.Spec.TrustedBase.Interface,
    `Verify.Spec.TreeMapNested]

-- The trusted base discharged for c4 and Counter on their checked-in source ASTs, and its axiom
-- audit. Separate from VerifySpec because the ASTs import the type checker.
lean_lib VerifySpecTrustedBase where
  roots := #[`Verify.Spec.TrustedBase.Instances, `Verify.Spec.TrustedBase.Axioms]

-- c4's exported spec (solar-verify --emit-lean-spec, scripts/refinement/spec/check.sh) proved of
-- SolidCore and of solar's bytecode, and the axiom audit. Needs the generated corpus
-- (scripts/refinement/gen.sh), so it is outside the default root.
lean_lib ContractsC4Spec where
  roots := #[`Contracts.C4.Spec.Export, `Contracts.C4.Spec.ExportWrong, `Contracts.C4.Spec.Bytecode,
    `Contracts.C4.Spec.Axioms]

-- solar-verify's verification conditions checked against SolidCore through the Loom generator
-- (Verify/VC.lean), the generic theorem from an erased function to its obligations
-- (Verify/VC/Obligations.lean) and its fuel uniformity (Verify/FuelStable.lean), outside the default
-- root: it builds on the generic source stage.
lean_lib VerifyVC where
  roots := #[`Verify.VC, `Verify.FuelStable, `Verify.Spec.Tree, `Verify.Spec.Hash, `Verify.Spec.TreeMap,
    `Verify.Spec.TreeIn, `Verify.Spec.TreeSplit]

-- solar-verify's transcripts of scripts/verify/{Counter,Token}.sol (scripts/verify/check.sh) bound
-- to their scripts, Token.burn and Token.transfer proved from the checked VCs, and the mutants.
lean_lib ContractsVC where
  roots := #[`Contracts.Counter.VC.Bind, `Contracts.Token.VC.Bind, `Contracts.Token.VC.Burn,
    `Contracts.Token.VC.Transfer, `Contracts.Token.VC.Mutants, `Contracts.Counter.VC.Inc, `Contracts.Counter.VC.Get,
    `Contracts.Counter.VC.Mutants, `Contracts.Counter.VC.Generic, `Contracts.Counter.VC.Discharged,
    `Contracts.Token.VC.Discharged, `Contracts.Token.VC.FromScript,
    `Contracts.Counter.VC.MilestoneDischarged, `Contracts.Counter.VC.ScriptEndToEnd]
  -- The exports, sources and mutants the roots import are under the same directories.
  globs := #[.submodules `Contracts.Counter.VC, .submodules `Contracts.Token.VC]

-- SolidCore's checked Uniswap V2 port: Contracts/UniswapV2/<contract>/{Source,Core}.lean, which
-- scripts/verify/uniswap_v2_gen.sh generates before the build (they are not committed: v2-core is
-- GPL-3.0), so run it first: scripts/verify/uniswap_v2_gen.sh && lake build ContractsUniswapV2.
-- Each Core is the kernel's type check and translation of its contract (contract_ok).
lean_lib ContractsUniswapV2 where
  roots := #[`Contracts.UniswapV2.ERC20.Core, `Contracts.UniswapV2.Factory.Core]
  -- The generated sources the roots import belong to this library too, or Lake looks for their
  -- object files elsewhere instead of building them.
  globs := #[.one `Contracts.UniswapV2.ERC20.Source, .one `Contracts.UniswapV2.ERC20.Core,
    .one `Contracts.UniswapV2.Factory.Source, .one `Contracts.UniswapV2.Factory.Core]

-- solar-verify's ERC20 specs connected to SolidCore's checked UniswapV2ERC20 (Meets: approve and
-- transfer meet their exported specs and the mutated spec is refused; SpecTree: the specs hold in
-- every world). scripts/verify/uniswap_v2_spec.sh generates Spec, SpecMut and Connect (derived from
-- the GPL-3.0 port, so not committed) after scripts/verify/uniswap_v2_gen.sh.
lean_lib ContractsUniswapV2ERC20Spec where
  roots := #[`Contracts.UniswapV2.ERC20.Meets, `Contracts.UniswapV2.ERC20.SpecTree]
  globs := #[.one `Contracts.UniswapV2.ERC20.Spec, .one `Contracts.UniswapV2.ERC20.SpecMut,
    .one `Contracts.UniswapV2.ERC20.Connect, .one `Contracts.UniswapV2.ERC20.SpecTreeKeccak,
    .one `Contracts.UniswapV2.ERC20.Meets, .one `Contracts.UniswapV2.ERC20.SpecTree]

-- UniswapV2Pair's translation is checked in stages, one module each, each within 6 GB:
-- Pair/Contract.lean composes contract_ok from Check, Ctx, Clones, one Fn module per run of
-- functions (mint and swap in three each: Fn/<fn>_pre, Fn/<fn>_lower, Fn/<fn>), Groups and Asm.
-- Not in CI yet: 22 modules, the largest (swap's lowering) at 5.98 GB under -M 6000.
lean_lib ContractsUniswapV2Pair where
  roots := #[`Contracts.UniswapV2.Pair.Contract]
  globs := #[.submodules `Contracts.UniswapV2.Pair]

-- Loom's axiom audit and the check that the certified Loom path stays off Loom's unported
-- layers (Verify/LoomAxioms.lean, Verify/LoomImports.lean).
lean_lib VerifyLoom where
  roots := #[`Verify.LoomAxioms, `Verify.LoomImports]

-- Counter end to end: its source triple carried through the refinement to solar's bytecode
-- (Verify.Final) and solar-verify's verdict as named hypotheses; the headline
-- (Contracts/Counter/Headline.lean) discharges the verdict for solar-verify's exported spec of
-- scripts/verify/CounterMilestone.sol and states it of solar's bytecode.
lean_lib ContractsCounter where
  roots := #[`Contracts.Counter.Final, `Contracts.Counter.Verdict, `Contracts.Counter.EndToEnd,
    `Contracts.Counter.Headline, `Contracts.Counter.SpecTree, `Contracts.Counter.Exports]
  -- The roots themselves (explicit globs replace the default of one glob per root), and the
  -- spec exports, deploy proof and source binding they import.
  globs := #[.one `Contracts.Counter.Final, .one `Contracts.Counter.Verdict,
    .one `Contracts.Counter.EndToEnd, .one `Contracts.Counter.Headline,
    .one `Contracts.Counter.Verify, .one `Contracts.Counter.Deploy,
    .one `Contracts.Counter.SpecTree, .one `Contracts.Counter.Exports, .one `SolidCore.Refinement.Deploy,
    .submodules `Contracts.Counter.Spec]

-- The published shape of a certificate (Verify/Shapes.lean: equivalence, termination, spec and
-- resources, apart), the forward assembly stage from a gas bound on (AssembleGas, and
-- AssembleGasLoop for code with loops) and Counter's
-- instance: its bytecode run by the checker with GAS
-- (Contracts/Counter/Execution.lean), the statement's inputs (ShapeSpec), the proof (Shape) and the
-- negative controls (ShapeNeg). Certified/counter/Final.lean, which solar's certify driver writes,
-- states the published theorem over them. Verify/ShapeCtx.lean: the same shape, without resources,
-- through the context checker (AssembleCtxCall).
lean_lib ContractsShapes where
  roots := #[`Verify.Shapes, `Verify.ShapeGeneric, `SolidCore.Refinement.Solar.AssembleGas,
    `SolidCore.Refinement.Solar.AssembleGasLoop, `Contracts.Counter.Execution, `Contracts.Counter.ShapeSpec,
    `Contracts.Counter.Shape, `Contracts.Counter.ShapeNeg, `Verify.ShapeBundle,
    `Contracts.Counter.ShapeExport, `Verify.ShapeCtx, `Verify.ShapeCtxGas]
  globs := #[.one `Verify.Shapes, .one `Verify.ShapeGeneric, .one `SolidCore.Refinement.Solar.AssembleGas,
    .one `SolidCore.Refinement.Solar.AssembleGasLoop,
    .one `Contracts.Counter.Execution, .one `Contracts.Counter.ShapeSpec,
    .one `Contracts.Counter.Shape, .one `Contracts.Counter.ShapeNeg, .one `Verify.ShapeBundle,
    .one `Contracts.Counter.ShapeExport, .one `Verify.ShapeCtx, .one `Verify.ShapeCtxGas]

-- solar-verify's Token end to end: the generic source stage from SolidCore's checked Token to
-- Certified/verify_token's stage0, the assembly stage of its evm12, and solar-verify's Token
-- triples carried to solar's bytecode.
lean_lib ContractsToken where
  roots := #[`Contracts.Token.Lowering, `Contracts.Token.Assembly, `Contracts.Token.Discharge,
    `Contracts.Token.EndToEnd, `Contracts.Token.Exports, `Contracts.Token.LoweringIn,
    `Contracts.Token.TransferMeets, `Contracts.Token.SpecTree, `Contracts.Token.WorldSpec,
    `Contracts.Token.HashScope]
  globs := #[.one `Contracts.Token.Lowering, .one `Contracts.Token.LoweringIn, .one `Contracts.Token.WorldSpec, .one `Contracts.Token.Assembly,
    .one `Contracts.Token.Discharge, .one `Contracts.Token.EndToEnd,
    .one `Contracts.Token.Exports, .one `Contracts.Token.TransferMeets, .one `Contracts.Token.SpecTree,
    .one `Contracts.Token.HashScope,
    .submodules `Contracts.Token.Spec]

/-! solar-verify's verification conditions and their kernel-checked discharge (formerly solar's
crates/verify/lean). An exported VC module imports `Verify.Obligation`; `Verify.Discharge` holds the
certificate checkers a VC is accepted by (Verify/Discharge/README.md). Lean's default options, as
solar's `solar_verify` package had. -/
lean_lib VerifyDischarge where
  roots := #[`Verify.Obligation, `Verify.Discharge]
  leanOptions := #[⟨`maxHeartbeats, (200000 : Nat)⟩, ⟨`backward.do.legacy, false⟩]

-- ArrayMax and Vault: solar-verify's exported VCs of their specs (Contracts/{ArrayMax,Vault}/Vc),
-- every required obligation proved in the kernel (Proofs/), Vault's vacuous obligations shown
-- vacuous (Contracts/Vault/Proofs/Vacuous.lean), and the axiom audits.
lean_lib ContractsArrayMaxVault where
  roots := #[`Contracts.ArrayMax.Audit, `Contracts.Vault.Audit]
  globs := #[.submodules `Contracts.ArrayMax, .submodules `Contracts.Vault]
  leanOptions := #[⟨`maxHeartbeats, (200000 : Nat)⟩, ⟨`backward.do.legacy, false⟩]

-- verify_counter: the stages of solar's crates/verify/examples/Counter.sol (the counter with
-- bump's loop) that solar-tv/milestone/verify_counter exports; for now its first lowered MIR.
lean_lib verify_counter where
  srcDir := "Certified"
  roots := #[`verify_counter.Proofs]
  globs := #[.submodules `verify_counter]
  leanOptions := solarTVOptions
  moreLeanArgs := #["-M", "3000"]

-- solar-verify's spec of that Counter (Contracts/Counter/Verify.lean) on solar's first lowered
-- MIR, every function and every call, bump's loop through cut points (Bump.lean), and carried
-- along any backend proved back to it (Holds.lean).
lean_lib ContractsVerifyCounter where
  roots := #[`Contracts.VerifyCounter.Holds]
  globs := #[.submodules `Contracts.VerifyCounter]
  leanOptions := solarTVOptions
  moreLeanArgs := #["-M", "3000"]

-- Math.sqrt's Newton loop inside CallSqrt's internal call: its generated ranking certificate
-- (Contracts/CallSqrt/Inferred.lean), sqrt's total contract under any caller, every call ending on
-- the first lowered MIR and the final EVM IR, and the exact bytecode (Final.lean).
lean_lib ContractsCallSqrt where
  roots := #[`Contracts.CallSqrt.Final]
  globs := #[.submodules `Contracts.CallSqrt]
  leanOptions := solarTVOptions
  moreLeanArgs := #["-M", "3000"]

-- callsqrt: the stages of Certified/callsqrt/callsqrt.sol's CallSqrt and their kernel proofs, which
-- solar's scripts/certify writes.
lean_lib «callsqrt» where
  srcDir := "Certified"
  roots := #[`callsqrt.Proofs]
  globs := #[.submodules `callsqrt]

-- Non-vacuity of the source semantics under a call oracle (SolidCore/Refinement/SourceOracle.lean):
-- one contract per external-call family of a constant-product pair (Contracts/CallFamilies/Calls.sol),
-- each function kernel-evaluated to a normal return in an open world and to no normal return in the
-- closed world of Source.run. The kernel_rfl selector table needs more than 3000 MB.
lean_lib ContractsCallFamilies where
  roots := #[`Contracts.CallFamilies.NonVacuity]
  globs := #[.submodules `Contracts.CallFamilies]
  moreLeanArgs := #["-M", "6000"]

-- arraymax: the stages of Certified/arraymax/arraymax.sol's ArrayMaxEntry, which solar's
-- scripts/certify writes, and the kernel proofs of its EVM IR stages (evm1 to evm15). The MIR stages
-- (Runs.Mir1-3, Runs.Sched) and the composition (Proofs.Stages) do not check yet: the first fails
-- sym_seg on the ABI decoder's checks; they are left out of the library until they do.
lean_lib «arraymax» where
  srcDir := "Certified"
  roots := #[`arraymax.Proofs.Runs.Evm1, `arraymax.Proofs.Runs.Evm2, `arraymax.Proofs.Runs.Evm3, `arraymax.Proofs.Runs.Evm4, `arraymax.Proofs.Runs.Evm5, `arraymax.Proofs.Runs.Evm6, `arraymax.Proofs.Runs.Evm7, `arraymax.Proofs.Runs.Evm8, `arraymax.Proofs.Runs.Evm9, `arraymax.Proofs.Runs.Evm10, `arraymax.Proofs.Runs.Evm11, `arraymax.Proofs.Runs.Evm12, `arraymax.Proofs.Runs.Evm13, `arraymax.Proofs.Runs.Evm14, `arraymax.Proofs.Runs.Evm15]
  globs := #[.submodules `arraymax.gen]

-- UniswapV2Pair's published statement of swap, skim and sync (Contracts/UniswapV2/PairSpec): the
-- statement over an open world (Verify/ShapeOpen.lean), the stage theorems it composes as named
-- Props, the composition wrapper and the negative controls. scripts/verify/uniswap_v2_pair_spec.sh
-- generates its inputs (Spec, SpecWrongK, Bytecode, Runtime; derived from the GPL-3.0 port, so not
-- committed) after scripts/verify/uniswap_v2_gen.sh.
lean_lib ContractsUniswapV2PairSpec where
  roots := #[`Contracts.UniswapV2.PairSpec.Published, `Contracts.UniswapV2.PairSpec.Negative, `Contracts.UniswapV2.PairSpec.Axioms]
  globs := #[.submodules `Contracts.UniswapV2.PairSpec]

-- uv2_erc20: UniswapV2ERC20's exported stages (Certified/uv2_erc20/gen, written by solar's
-- -Zemit-lean-stages from the GPL-3.0 v2-core port before the build, so not committed), the
-- certificate of the checker with contexts and gas (CtxGas.lean, solar's tools/certify/gen_ctxgas.py,
-- also generated) and the transfer slice's gas bound (Gas.lean, GasGuard.lean).
lean_lib «uv2_erc20» where
  srcDir := "Certified"
  roots := #[`uv2_erc20.Gas]
  globs := #[.submodules `uv2_erc20]

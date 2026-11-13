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

-- solar's translation validation library: its contract semantics interface (SolarTV.Sem:
-- Call, Observable, Sem, Stage) is this library's, its lowered MIR and EVM IR semantics are
-- the languages of the w5 milestone's stages, and its W1Proofs library proves the backend
-- stages. A git dependency on solar at 2144dccb, whose solar-tv has the w1, w4,
-- counter, c4, mulx, bank and events milestones and the semantics of internal calls, casts and
-- selects.
require solar_tv from git
  "https://github.com/paradigmxyz/solar.git" @ "2144dccb0984e6df238cc2e5e9d741e2e52e722d" / "solar-tv"

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
-- reason. Lowering.lean and Certified.lean need -KleanMemory=7000 (peaks of 5.4 and 4.3 GB).
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

/-- Loom's monad algebras and weakest preconditions, vendored with the changes Lean
4.35 needs; see vendor/loom/README.md. -/
lean_lib Loom where
  srcDir := "vendor/loom"
  -- The port is in progress: the modules below build on Lean 4.35; the rest of
  -- vendor/loom/Loom is being ported and joins this list as it builds.
  roots := #[`Loom.MonadUtil, `Loom.SpecMonad, `Loom.MonadAlgebras.Defs,
    `Loom.MonadAlgebras.Instances.Basic, `Loom.MonadAlgebras.Instances.StateT,
    `Loom.MonadAlgebras.Instances.ExceptT, `Loom.MonadAlgebras.Instances.ReaderT,
    `Loom.MonadAlgebras.Instances.Gen, `Loom.MonadAlgebras.WP.Basic,
    `Loom.MonadAlgebras.WP.Liberal, `Loom.MonadAlgebras.Instances.ExceptTErr,
    `Loom.MonadAlgebras.WP.Variant]

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
    `SolidCore.Refinement.Solar.Bank.Certified, `SolidCore.Refinement.Solar.Events.Certified]

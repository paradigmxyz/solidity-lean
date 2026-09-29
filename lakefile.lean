import Lake
open Lake DSL

require evmyul from git
  "https://github.com/danrobinson/EVMYulLean.git" @ "b08573c65e33feb5331abe2b7c1d76be89bb8eff"

-- The shared "language of composition": the interaction monad, Query/Answer,
-- OpenWorld, and ForwardRel, extracted verbatim from evm-compiler. Consumed as a
-- Lake path dependency (a sibling git repo); promote to a git URL later. A
-- hash-check (scripts/check_shared_interaction_hashes.py) guarantees its
-- Simulation sources stay byte-identical to evm-compiler's.
require «evm-interaction» from git
  "https://github.com/danrobinson/evm-interaction.git" @ "c939817c55f966dab97e1ba8df05ceca1fdfbdb2"

package «solidity-lean» where
  leanOptions := #[
    ⟨`maxHeartbeats, 1000000⟩
  ]

-- The default root retains every proof and witness in the full build.
@[default_target]
lean_lib SolidCore where

-- The giant statement-lowering mutual block takes much longer to optimize in
-- C than to execute once per prepared fixture. Keep its development build cheap;
-- opt into -O3 with `lake -KspecHuntLoweringO3=true build` for throughput profiling.
lean_lib SolidCoreStatementLowering where
  roots := #[`SolidCore.Solidity.Interface.Statements]
  moreLeancArgs := if get_config? specHuntLoweringO3 == some "true" then #[] else #["-O0"]

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
  buildLeanSharedLib "specHuntNative"
    (pkg.sharedLibDir / nameToSharedLib "specHuntNative")
    (objects ++ libraries) #[] #[] #[] (plugin := true)

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

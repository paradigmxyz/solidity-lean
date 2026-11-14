import Lake
open Lake DSL

require evmyul from ".." / "evmyul"

package «evm-interaction» {
  moreLeanArgs := #[
    "-DautoImplicit=false",
    "-Dlinter.all=false",
    "-Dlinter.constructorNameAsVariable=false",
    "-Dlinter.deprecated=false",
    "-Dlinter.unnecessarySeqFocus=false",
    "-Dlinter.unnecessarySimpa=false",
    "-Dlinter.unreachableTactic=false",
    "-Dlinter.unusedSimpArgs=false",
    "-Dlinter.unusedTactic=false",
    "-Dlinter.unusedVariables=false"
  ]
  moreServerOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`linter.all, false⟩,
    ⟨`linter.constructorNameAsVariable, false⟩,
    ⟨`linter.deprecated, false⟩,
    ⟨`linter.unnecessarySeqFocus, false⟩,
    ⟨`linter.unnecessarySimpa, false⟩,
    ⟨`linter.unreachableTactic, false⟩,
    ⟨`linter.unusedSimpArgs, false⟩,
    ⟨`linter.unusedTactic, false⟩,
    ⟨`linter.unusedVariables, false⟩
  ]
}

@[default_target]
lean_lib «EvmInteraction» where
  roots := #[`EvmInteraction]
  globs := #[`EvmInteraction, `EvmInteraction.Simulation.Interaction,
             `EvmInteraction.Simulation.OpenWorld, `EvmInteraction.Simulation.Outcome].map Lake.Glob.one

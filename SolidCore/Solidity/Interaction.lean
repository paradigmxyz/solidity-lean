/-
Bridge to the shared interaction package (`evm-interaction`).

Phase 2 establishes the dependency and pins the alphabet this repo will program
against. Phase 5 threads these types through the interpreter's external
boundary. The names below are the exact `EvmCompiler.Simulation.*` declarations
extracted verbatim from evm-compiler — identical types, so any future cross-repo
statement is definitionally well-formed.
-/
import EvmCompiler.Simulation.Interaction
import EvmCompiler.Simulation.OpenWorld
import EvmCompiler.Simulation.Outcome

namespace SolidCore
namespace Solidity
namespace Shared

/-- The free interaction monad this repo's semantics will emit into. -/
abbrev Interaction := EvmCompiler.Simulation.Interaction

/-- The external query alphabet (resource + external requests). -/
abbrev Query := EvmCompiler.Simulation.Query

/-- The answer type indexed by a query. -/
abbrev Answer := EvmCompiler.Simulation.Answer

/-- The world snapshot carried by an external query. -/
abbrev OpenWorld := EvmCompiler.Simulation.OpenWorld

/-- The composition relation all of solidity-lean's theorems are stated in. -/
abbrev ForwardRel := @EvmCompiler.Simulation.Interaction.ForwardRel

end Shared
end Solidity
end SolidCore

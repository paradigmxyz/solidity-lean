/-
`evm-interaction`: the standalone language-of-composition package.

Verbatim extraction of evm-compiler's `EvmCompiler.Simulation.*` framework
(the free interaction monad, `Query`/`Answer`, `OpenWorld`, `ForwardRel` and its
composition lemmas). The `EvmCompiler.Simulation.*` namespaces and declaration
names are preserved so evm-compiler's frozen theorem statements stay textually
unchanged; since 2026-07-09 evm-compiler consumes this package directly (its
local copies are deleted), so this IS the single source. Module paths live
under `EvmInteraction.*` (namespaces unchanged) so the root `EvmCompiler` lib
prefix of evm-compiler does not claim them. Depends only on the pinned EVMYulLean + Mathlib.
-/
import EvmInteraction.Simulation.Interaction
import EvmInteraction.Simulation.OpenWorld
import EvmInteraction.Simulation.Outcome

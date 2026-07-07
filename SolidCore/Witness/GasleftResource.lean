/-
A3 — `gasleft` as `Query.resource .gas`.

`EnvWord.gasleft` no longer reads the ambient constant directly; it emits a
`Query.resource .gas` observation on the shared alphabet's reserved resource arm
(`EvmCompiler.Simulation.ResourceQuery.gas`) and resumes on the answered word.
Every answerer supplies the ambient `context.gasleft`, so the returned value is
unchanged — the query simply now appears in the transcript.

This witness drives a real `gasleft`-reading expression through the evaluator and
machine-checks (at `lake build SolidCore` time) that:
  * the ordered query transcript contains exactly the `resource .gas` query, and
  * folding the tree under the context answerer returns the ambient
    `context.gasleft` word (behaviour-preserving by construction).
-/
import SolidCore.Witness.Interface

namespace SolidCore
namespace Solidity
namespace Executable
namespace Examples

open SolidCore.Solidity.Source

/-- A context whose ambient gas is a distinctive sentinel word. -/
def gasleftResourceContext : SolidCore.Solidity.Source.Context :=
  { SolidCore.Solidity.Source.Context.empty with gasleft := 0x9999 }

/-- The interaction tree of evaluating the `gasleft()` expression through the
    real expression evaluator (un-folded). -/
def gasleftResourceTree :
    SolI (SolidCore.Solidity.Source.Value ×
      SolidCore.Solidity.Source.Runtime) :=
  SolidCore.Solidity.Source.Expr.evalWithRuntimeOrderFuel 4
    SolidCore.Solidity.Source.ChildEvalOrder.leftToRight
    gasleftResourceContext
    (SolidCore.Solidity.Source.Runtime.ofState
      SolidCore.Solidity.Source.State.empty)
    (SolidCore.Solidity.Source.Expr.env
      SolidCore.Solidity.Source.EnvWord.gasleft)

/-- The ordered query transcript of the `gasleft()` execution, answered by the
    context answerer. Expected: exactly one `resource .gas` query. -/
def gasleftResourceTranscript : List EvmCompiler.Simulation.Query :=
  SolidCore.Solidity.Source.SolI.queryTranscript 4
    (SolidCore.Solidity.Source.contextAnswer gasleftResourceContext)
    gasleftResourceTree

/-- Acceptance predicate: the transcript is exactly the reserved `resource .gas`
    query, and folding the tree under the context answerer yields the ambient
    `context.gasleft` word (`0x9999`) — the value the ambient constant would have
    produced before the query existed. -/
def gasleftResourceMatches : Bool :=
  let transcriptOk :=
    match gasleftResourceTranscript with
    | [ EvmCompiler.Simulation.Query.resource
          EvmCompiler.Simulation.ResourceQuery.gas ] => true
    | _ => false
  let valueOk :=
    match SolidCore.Solidity.Source.SolI.run gasleftResourceContext
        gasleftResourceTree with
    | Except.ok (SolidCore.Solidity.Source.Value.word gas, _) =>
        SolidCore.Solidity.Source.wordEq gas gasleftResourceContext.gasleft
    | _ => false
  transcriptOk && valueOk

end Examples
end Executable
end Solidity
end SolidCore

/- Build-time machine-check: `lake build SolidCore` fails (this `#eval` throws)
    if the `gasleft`-as-resource-query wiring regresses (missing query in the
    transcript, or a folded value that no longer equals the ambient gas word). -/
#eval
  if SolidCore.Solidity.Executable.Examples.gasleftResourceMatches then
    (pure () : IO Unit)
  else
    throw (IO.userError
      "gasleftResourceMatches failed: gasleft resource-query witness regressed")

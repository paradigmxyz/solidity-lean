/-
Phase 5 acceptance hardening (Phase 6, punch-list item 6).

A **real** two-external-call contract execution as an explicit interaction tree,
with its query transcript machine-checked at library-build time. Unlike the
synthetic `phase5DemoTree` (which just calls `emitLowLevelCall` twice with
hardcoded addresses), this drives the hand-built `probeBoth` function (a
`staticcall` followed by a `delegatecall`) through the real evaluator
(`FunctionDef.call`), so the two external-call queries come from actual Solidity
execution. `SolI.queryTranscript` exposes the raw ordered `Query` transcript over
the shared alphabet; folding the same tree under the scripted responder yields
the results.

Built-but-not-manifest: this is compiled by `lake build SolidCore` (the frozen
conformance manifest is untouched — item 6 asserts existing Phase 5 behavior, not
new coverage). The transcript shape and results are pinned by
`phase5RealDemoTranscriptMatches`.
-/
import SolidCore.Witness.Interface

namespace SolidCore
namespace Solidity
namespace Executable
namespace Examples

open SolidCore.Solidity.Source

/-- The elaborated core `FunctionDef` for the hand-built two-external-call
    `probeBoth` (a `staticcall` then a `delegatecall`). -/
def phase5RealDemoFunction? : Option SolidCore.Solidity.Source.FunctionDef :=
  FunctionDecl.toCore?
    (storageNames := []) (constants := []) (extraEnv := [])
    (contracts := []) (usingDecls := []) (modifiers := [])
    (functions := [lowLevelStaticDelegateFunction]) (freeFunctions := [])
    (decl := lowLevelStaticDelegateFunction)

/-- The raw interaction tree of the real two-call execution (un-folded). -/
def phase5RealDemoTree? :
    Option (SolI SolidCore.Solidity.Source.CallResult) :=
  phase5RealDemoFunction?.bind (fun function =>
    SolidCore.Solidity.Source.FunctionDef.call 8
      [function.toInternal]
      SolidCore.Solidity.Source.Context.empty function
      SolidCore.Solidity.Source.State.empty
      [ SolidCore.Solidity.Source.Value.word 0xcafe
      , SolidCore.Solidity.Source.Value.bytes [7, 7] ])

/-- The ordered query transcript emitted by the real execution, answered by the
    scripted responder. Expected: exactly two external-call queries. -/
def phase5RealDemoTranscript : List EvmCompiler.Simulation.Query :=
  match phase5RealDemoTree? with
  | some tree =>
      SolidCore.Solidity.Source.SolI.queryTranscript 8
        (SolidCore.Solidity.Source.ScriptedResponder.answer
          lowLevelStaticDelegateResponder)
        tree
  | none => []

/-- Acceptance predicate: the transcript is exactly two external-call queries to
    `0xcafe`, emitted in the construct-intrinsic child-evaluation order — tuple
    components evaluate LEFT to RIGHT (solc ExpressionCompiler.cpp:400), so the
    `staticcall` first, then the `delegatecall`, matching the source tuple
    `(staticcall(...), delegatecall(...))` (the responder keys on
    kind/target/calldata, not order, so results are unaffected). Folding the
    same tree under the responder returns the
    two expected results (`staticcall` success with output `[1]`, `delegatecall`
    failure with output `[2,3]`), checked by `lowLevelStaticDelegateMatches`. -/
def phase5RealDemoTranscriptMatches : Bool :=
  let shapeOk :=
    match phase5RealDemoTranscript with
    | [ EvmCompiler.Simulation.Query.external _
          (EvmCompiler.Simulation.ExternalRequest.call first)
      , EvmCompiler.Simulation.Query.external _
          (EvmCompiler.Simulation.ExternalRequest.call second) ] =>
        (match first.kind with
         | EvmCompiler.Simulation.CallKind.staticcall => true
         | _ => false) &&
        (match second.kind with
         | EvmCompiler.Simulation.CallKind.delegatecall => true
         | _ => false) &&
        SolidCore.Solidity.Source.addressToWord first.codeAddress == 0xcafe &&
        SolidCore.Solidity.Source.addressToWord second.codeAddress == 0xcafe
    | _ => false
  shapeOk && (lowLevelStaticDelegateMatches == some true)

end Examples
end Executable
end Solidity
end SolidCore

/- Build-time machine-check: `lake build SolidCore` fails (this `#eval` throws)
    if the real two-external-call interaction-tree demo regresses. Enforced by
    the compiled evaluator — like a harness `#eval` — so no proof axioms are
    introduced (in-kernel `decide` cannot reduce the interpreter, and
    `native_decide` is avoided to keep the axiom set empty). -/
#eval
  if SolidCore.Solidity.Executable.Examples.phase5RealDemoTranscriptMatches then
    (pure () : IO Unit)
  else
    throw (IO.userError
      "phase5RealDemoTranscriptMatches failed: interaction-tree demo regressed")

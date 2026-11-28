import Verify.LoopSource.Equiv.Stage
import Verify.LoopSource.Proof.EraseLoop

/-!
# The loop's source edge from the erasure

`loop_stage` and `loop_equiv` (`Stage.lean`) take `BodyRuns` of the function's body as the premise
`hb`. `bodyRuns_of_eraseLoop` gives it from `eraseLoopStmt`, so a function whose body
`eraseLoopStmt` erases (a counted loop, `EraseLoop.lean`) needs no hand-written body summary:

* `loop_stage_of_eraseLoop`: the source-to-MIR stage.
* `source_edge_of_eraseLoop`: it composed (`Stage.trans`) with the backend's MIR-to-EVM-IR stage:
  SolidCore's runtime to EVM IR on every valid call of the function.
* `loop_equiv_of_eraseLoop`: the driver's `Shapes.Equiv`, with the assembler's loop checker.

Every other premise is `loop_stage`'s, unchanged.
-/

namespace Verify.LoopSource.Equiv
open SolarTV SolarTV.Machine SolarTV.MIR.Lowered SolidCore.Refinement SolidCore.Refinement.Generic
open SolidCore.Solidity.Source Verify.LoopSource.Interface Verify.LoopSource.Generic
open SolidCore.Refinement.Generic.Loop SolidCore.Refinement.Solar

variable {fuel : Nat} {c : SolidCore.Solidity.TypeCheck.CheckedContract}
    {sel : Nat} {fn : FunctionDef} {ws : List Nat} {b : Br} {T : Tree} (hsel : sel < 2 ^ 32)
    (hfind : c.core.findFunctionBySelector? sel = some fn)
    (hw : widthsOf fn.params fn.paramAbiCleanups = some ws) (hret : fn.returns.all wordBinding = true)
    (h : eraseLoopStmt { envOf c.core with facts := argFacts ws 0 } fuel fn.body (initState fn) = some b)
    (hT : brTree fn (argFacts ws 0) b = some T)
    {C : Cut} {ev : EnvFlags} {m : Module} {le li : List (Facts × Out)}
    (hchk : C.check ev m sel fn.params.length = some (le, li))
    {L : Val → LoopRecord} {toSrc : Val → Val} {X A : Val → Prop}
    (hobl : Obl L toSrc X A fn.params.length C.cases T le li)
    (hA : ∀ σ args, ArgsOk fn ws args → A ⟨args, slotValue σ, solHash, callerWord⟩)
include hsel hfind hw hret h hT hchk hobl hA

/-- **The loop's source-to-MIR stage, from the erasure.** -/
theorem loop_stage_of_eraseLoop (o : Oracle) (ho : SourceAsk ev o) :
    Stage (solidCoreRuntime fuel) (mirSem o) c m (SelCall sel fn ws) :=
  loop_stage hsel hfind hw hret (bodyRuns_of_eraseLoop h) hT hchk hobl hA o ho

/-- **The source edge, from the erasure**: the loop's source-to-MIR stage composed with the
backend's MIR-to-EVM-IR stage. -/
theorem source_edge_of_eraseLoop (o : Oracle) (ho : SourceAsk ev o)
    {q : Assemble.Program} {scope : Call → Prop}
    (backend : Stage (mirSem o) (evmirSem o) m q scope)
    (hscope : ∀ call, SelCall sel fn ws call → scope call) :
    Stage (solidCoreRuntime fuel) (evmirSem o) c q (SelCall sel fn ws) :=
  (loop_stage_of_eraseLoop hsel hfind hw hret h hT hchk hobl hA o ho).trans (backend.mono hscope)

/-- **`Shapes.Equiv` for a function with a counted loop, from the erasure.** -/
theorem loop_equiv_of_eraseLoop
    {q : Assemble.Program} {code : ByteArray} {scope : Call → Prop} {cert : Assemble.Cert} {mx : List Nat}
    (backend : Stage (mirSem Shapes.oracle) (evmirSem Shapes.oracle) m q scope)
    (hscope : ∀ call, SelCall sel fn ws call → scope call)
    (asm : AssembleLoop.checkL q code cert mx = true) :
    Shapes.Equiv (solidCoreRuntime fuel) c code (SelCall sel fn ws) :=
  loop_equiv hsel hfind hw hret (bodyRuns_of_eraseLoop h) hT hchk hobl hA backend hscope asm

end Verify.LoopSource.Equiv

/-- info: 'Verify.LoopSource.Equiv.loop_stage_of_eraseLoop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Verify.LoopSource.Equiv.loop_stage_of_eraseLoop

/-- info: 'Verify.LoopSource.Equiv.source_edge_of_eraseLoop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Verify.LoopSource.Equiv.source_edge_of_eraseLoop

/-- info: 'Verify.LoopSource.Equiv.loop_equiv_of_eraseLoop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Verify.LoopSource.Equiv.loop_equiv_of_eraseLoop

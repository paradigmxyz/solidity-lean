import Verify.LoopSource.Equiv.Stage
import Verify.LoopSource.Equiv.Obl

/-!
# The loop's stage and `Shapes.Equiv` from the checks alone

`loop_stage_checked` and `loop_equiv_checked` are `loop_stage` and `loop_equiv` with the leaves'
obligations `Obl` replaced by the decided check `Inv.checkWith` of an invariant `I` and a measure
`μ` (`obl_of_checkWith`). Their premises are the source loop's `BodyRuns`, two kernel-checked
functions of the compiler's output (`Cut.check`, `Inv.checkWith`), and, for `Equiv`, the backend's
stage and the assembler's loop checker, which the driver proves for every program.
-/

namespace Verify.LoopSource.Equiv
open SolarTV SolarTV.Machine SolarTV.MIR.Lowered SolidCore.Refinement SolidCore.Refinement.Generic
open SolidCore.Solidity.Source Verify.LoopSource.Interface Verify.LoopSource.Generic
open SolidCore.Refinement.Generic.Loop SolidCore.Refinement.Solar

/-- **The loop's source-to-MIR stage from the checks.** -/
theorem loop_stage_checked {fuel : Nat} {c : SolidCore.Solidity.TypeCheck.CheckedContract} {sel : Nat}
    {fn : FunctionDef} {ws : List Nat} {b : Br} {T : Tree} (hsel : sel < 2 ^ 32)
    (hfind : c.core.findFunctionBySelector? sel = some fn)
    (hw : widthsOf fn.params fn.paramAbiCleanups = some ws) (hret : fn.returns.all wordBinding = true)
    (hb : BodyRuns { envOf c.core with facts := argFacts ws 0 } fuel fn b)
    (hT : brTree fn (argFacts ws 0) b = some T)
    {C : Cut} {ev : EnvFlags} {m : Module} {le li : List (Facts × Out)}
    (hchk : C.check ev m sel fn.params.length = some (le, li))
    {I : List Inv.F} {μ : WExpr} (hinv : Inv.checkWith fn.params.length C.cases T le li I μ = true)
    (o : Oracle) (ho : SourceAsk ev o) :
    Stage (solidCoreRuntime fuel) (mirSem o) c m (SelCall sel fn ws) :=
  loop_stage hsel hfind hw hret hb hT hchk (Inv.obl_of_checkWith hinv) (fun _ _ _ => trivial) o ho

/-- **`Shapes.Equiv` for a loop-carrying function from the checks.** -/
theorem loop_equiv_checked {fuel : Nat} {c : SolidCore.Solidity.TypeCheck.CheckedContract} {sel : Nat}
    {fn : FunctionDef} {ws : List Nat} {b : Br} {T : Tree} (hsel : sel < 2 ^ 32)
    (hfind : c.core.findFunctionBySelector? sel = some fn)
    (hw : widthsOf fn.params fn.paramAbiCleanups = some ws) (hret : fn.returns.all wordBinding = true)
    (hb : BodyRuns { envOf c.core with facts := argFacts ws 0 } fuel fn b)
    (hT : brTree fn (argFacts ws 0) b = some T)
    {C : Cut} {ev : EnvFlags} {m : Module} {le li : List (Facts × Out)}
    (hchk : C.check ev m sel fn.params.length = some (le, li))
    {I : List Inv.F} {μ : WExpr} (hinv : Inv.checkWith fn.params.length C.cases T le li I μ = true)
    {q : Assemble.Program} {code : ByteArray} {scope : Call → Prop} {cert : Assemble.Cert} {mx : List Nat}
    (backend : Stage (mirSem Shapes.oracle) (evmirSem Shapes.oracle) m q scope)
    (hscope : ∀ call, SelCall sel fn ws call → scope call)
    (asm : AssembleLoop.checkL q code cert mx = true) :
    Shapes.Equiv (solidCoreRuntime fuel) c code (SelCall sel fn ws) :=
  loop_equiv hsel hfind hw hret hb hT hchk (Inv.obl_of_checkWith hinv) (fun _ _ _ => trivial) backend
    hscope asm

end Verify.LoopSource.Equiv

/-- info: 'Verify.LoopSource.Equiv.Inv.obl_of_checkWith' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Verify.LoopSource.Equiv.Inv.obl_of_checkWith

/-- info: 'Verify.LoopSource.Equiv.loop_stage_checked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Verify.LoopSource.Equiv.loop_stage_checked

/-- info: 'Verify.LoopSource.Equiv.loop_equiv_checked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Verify.LoopSource.Equiv.loop_equiv_checked

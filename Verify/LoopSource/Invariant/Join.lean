import Verify.LoopSource.Equiv.EraseLoopCounterJoin
import Verify.LoopSource.Invariant.While

/-!
# The loop join for an invariant-carrying `while` loop

`EraseLoopJoin.GeneratedTarget` (`Equiv/EraseLoopCounterJoin.lean`) gives the driver's
`Shapes.Certified` for a function whose loop `eraseLoopStmt` erases to its closed form. This module
states and proves the same conclusion when the source loop is a `while` loop erased through an
invariant (`Invariant/While.lean`): the source premise `eraseLoopStmt … = some b` becomes
`eraseWhile … wd … = some b` with the loop's obligations `Invariant.Obl … wd I μ` (initiation,
preservation, exit, no overflow and a falling measure, about words). Everything else is unchanged:

* the MIR side keeps the cut-point certificate: `Cut.check` and its leaves' obligations
  `Equiv.Obl` against a tree `T0` whose observables are the erased tree's on every clean
  valuation (`WhileTarget` takes any proof of them; `WhileGeneratedTarget` takes them as the
  generator emits them, valid sequents `allSeqs` of an invariant and a measure, exactly as
  `GeneratedTarget` does);
* the backend's MIR-to-EVM-IR stage, the assembler's loop checker and a measure bridge of the
  final EVM IR give the constant gas bound, as in `GeneratedTarget`;
* `Allowed` and `Post` are checked on `T0` (`OnTree`).

The two invariants are separate: the source one (`I`, `μ`, over the source header's words) proves the
source loop ends in its `exit` words; the MIR one (in `Equiv.Obl`, over the MIR header's words)
proves the MIR loop runs to `T0`'s observable. A solver may propose both; the kernel checks both.
-/

namespace Verify.LoopSource.Invariant.Join
open SolarTV SolarTV.Machine SolarTV.MIR.Lowered SolidCore.Refinement SolidCore.Refinement.Generic
open SolidCore.Solidity.Source Verify.LoopSource.Interface Verify.LoopSource.Generic
open SolidCore.Refinement.Generic.Loop SolidCore.Refinement.Solar Verify.LoopSource.Equiv
open Verify.LoopSource.Invariant

/-- **The constant-gas join for a `while` loop through its invariant**, with the MIR side's
obligations given by any proof. -/
def WhileTarget : Prop :=
  ∀ (fuel : Nat) (c : SolidCore.Solidity.TypeCheck.CheckedContract) (sel : Nat) (fn : FunctionDef)
    (ws : List Nat) (b : Br) (T : Tree),
    sel < 2 ^ 32 → c.core.findFunctionBySelector? sel = some fn →
    widthsOf fn.params fn.paramAbiCleanups = some ws → fn.returns.all wordBinding = true →
    ∀ (wd : WhileData) (Is : Val → Val → Prop) (μs : Val → Val → Nat),
    Invariant.Obl { envOf c.core with facts := argFacts ws 0 } wd Is μs →
    eraseWhile { envOf c.core with facts := argFacts ws 0 } wd fuel fn.body (initState fn) = some b →
    brTree fn (argFacts ws 0) b = some T →
    ∀ (C : Cut) (ev : EnvFlags) (m : Module) (le li : List (Facts × Out)),
    C.check ev m sel fn.params.length = some (le, li) →
    ∀ (T0 : Tree) (L : Val → LoopRecord) (toSrc : Val → Val) (X A : Val → Prop),
    Equiv.Obl L toSrc X A fn.params.length C.cases T0 le li →
    (∀ σ args, ArgsOk fn ws args → A ⟨args, slotValue σ, solHash, callerWord⟩) →
    (∀ ρ : Val, ρ.Ok → (T.eval ρ).obs = (T0.eval ρ).obs) →
    ∀ (q : Assemble.Program) (code : ByteArray) (scope : Call → Prop) (cert : Assemble.Cert)
      (mx : List Nat),
    Stage (mirSem Shapes.oracle) (evmirSem Shapes.oracle) m q scope →
    (∀ call, SelCall sel fn ws call → scope call) →
    AssembleLoop.checkL q code cert mx = true →
    ∀ (Valid : Call → Prop) (Allowed Post : Call → Observable → Prop),
    (∀ call, Valid call → SelCall sel fn ws call) → (∃ call, Valid call) →
    OnTree sel fn ws T0 Allowed → OnTree sel fn ws T0 Post →
    ∀ (R : LoopRecord) (E B Xs M : Nat),
    (∀ call, Valid call → Verify.Gas.FixedFuel.Loops (EVM.Program.block Shapes.oracle call q)
      (0, [], SolarTV.Machine.State.initial call) R E B Xs M) →
    AssembleLoop.gasBoundL cert (Verify.Gas.FixedFuel.fixedFuel E B Xs M) < 2 ^ 64 →
    Shapes.Certified (solidCoreRuntime fuel) c code Valid Allowed Post
      (fun _ => AssembleLoop.gasBoundL cert (Verify.Gas.FixedFuel.fixedFuel E B Xs M))

/-- **The `while` join**, by `LeastFuel.certified_of_bodyRuns_loops` with the source's `BodyRuns` from
`bodyRuns_of_eraseWhile`. -/
theorem while_certified : WhileTarget := by
  intro fuel c sel fn ws b T hsel hfind hw hret wd Is μs ho h hT C ev m le li hchk T0 L toSrc X A hobl
    hA hsame q code scope cert mx backend hscope asm Valid Allowed Post hsub hinh hAl hP R E B Xs M
    loops hfit
  exact LeastFuel.certified_of_bodyRuns_loops hsel hfind hw hret (bodyRuns_of_eraseWhile ho h) hT hchk
    (EraseLoopJoin.obl_of_eval hsame hobl) hA backend hscope asm hsub hinh
    (EraseLoopJoin.onTree_of_eval hsame hAl) (EraseLoopJoin.onTree_of_eval hsame hP) loops hfit

/-- **`GeneratedTarget` for a `while` loop through its invariant**: `GeneratedTarget`'s premises
word for word, with `eraseLoopStmt` replaced by `eraseWhile` and the source loop's obligations. -/
def WhileGeneratedTarget : Prop :=
  ∀ (fuel : Nat) (c : SolidCore.Solidity.TypeCheck.CheckedContract) (sel : Nat) (fn : FunctionDef)
    (ws : List Nat) (b : Br) (T : Tree),
    sel < 2 ^ 32 → c.core.findFunctionBySelector? sel = some fn →
    widthsOf fn.params fn.paramAbiCleanups = some ws → fn.returns.all wordBinding = true →
    ∀ (wd : WhileData) (Is : Val → Val → Prop) (μs : Val → Val → Nat),
    Invariant.Obl { envOf c.core with facts := argFacts ws 0 } wd Is μs →
    eraseWhile { envOf c.core with facts := argFacts ws 0 } wd fuel fn.body (initState fn) = some b →
    brTree fn (argFacts ws 0) b = some T →
    ∀ (C : Cut) (ev : EnvFlags) (m : Module) (le li : List (Facts × Out)),
    C.check ev m sel fn.params.length = some (le, li) →
    ∀ (T0 : Tree) (I : List Inv.F) (μ : WExpr) (ss : List Inv.Seq),
    Inv.allSeqs fn.params.length C.cases T0 le li I μ = some ss → (∀ s ∈ ss, s.Valid) →
    (∀ ρ : Val, ρ.Ok → (T.eval ρ).obs = (T0.eval ρ).obs) →
    ∀ (q : Assemble.Program) (code : ByteArray) (scope : Call → Prop) (cert : Assemble.Cert)
      (mx : List Nat),
    Stage (mirSem Shapes.oracle) (evmirSem Shapes.oracle) m q scope →
    (∀ call, SelCall sel fn ws call → scope call) →
    AssembleLoop.checkL q code cert mx = true →
    ∀ (Valid : Call → Prop) (Allowed Post : Call → Observable → Prop),
    (∀ call, Valid call → SelCall sel fn ws call) → (∃ call, Valid call) →
    OnTree sel fn ws T0 Allowed → OnTree sel fn ws T0 Post →
    ∀ (R : LoopRecord) (E B Xs M : Nat),
    (∀ call, Valid call → Verify.Gas.FixedFuel.Loops (EVM.Program.block Shapes.oracle call q)
      (0, [], SolarTV.Machine.State.initial call) R E B Xs M) →
    AssembleLoop.gasBoundL cert (Verify.Gas.FixedFuel.fixedFuel E B Xs M) < 2 ^ 64 →
    Shapes.Certified (solidCoreRuntime fuel) c code Valid Allowed Post
      (fun _ => AssembleLoop.gasBoundL cert (Verify.Gas.FixedFuel.fixedFuel E B Xs M))

/-- **The `while` join for generated obligations**, by `while_certified` and `Inv.obl_of_seqs`. -/
theorem while_certified_generated : WhileGeneratedTarget := by
  intro fuel c sel fn ws b T hsel hfind hw hret wd Is μs ho h hT C ev m le li hchk T0 I μ ss hss hv
    hsame q code scope cert mx backend hscope asm Valid Allowed Post hsub hinh hAl hP R E B Xs M loops
    hfit
  exact while_certified fuel c sel fn ws b T hsel hfind hw hret wd Is μs ho h hT C ev m le li hchk T0
    (fun _ => Inv.recOf I μ) id (fun _ => True) (fun _ => True) (Inv.obl_of_seqs hss hv)
    (fun _ _ _ => trivial) hsame q code scope cert mx backend hscope asm Valid Allowed Post hsub hinh
    hAl hP R E B Xs M loops hfit

/-- **The source-to-MIR stage of a `while` loop through its invariant**: `loop_stage` with the
source's `BodyRuns` from `eraseWhile`, under every oracle the flags allow. -/
theorem while_stage {fuel : Nat} {c : SolidCore.Solidity.TypeCheck.CheckedContract} {sel : Nat}
    {fn : FunctionDef} {ws : List Nat} {b : Br} {T : Tree} (hsel : sel < 2 ^ 32)
    (hfind : c.core.findFunctionBySelector? sel = some fn)
    (hw : widthsOf fn.params fn.paramAbiCleanups = some ws) (hret : fn.returns.all wordBinding = true)
    {wd : WhileData} {Is : Val → Val → Prop} {μs : Val → Val → Nat}
    (ho : Invariant.Obl { envOf c.core with facts := argFacts ws 0 } wd Is μs)
    (h : eraseWhile { envOf c.core with facts := argFacts ws 0 } wd fuel fn.body (initState fn) = some b)
    (hT : brTree fn (argFacts ws 0) b = some T)
    {C : Cut} {ev : EnvFlags} {m : Module} {le li : List (Facts × Out)}
    (hchk : C.check ev m sel fn.params.length = some (le, li))
    {T0 : Tree} {L : Val → LoopRecord} {toSrc : Val → Val} {X A : Val → Prop}
    (hobl : Equiv.Obl L toSrc X A fn.params.length C.cases T0 le li)
    (hA : ∀ σ args, ArgsOk fn ws args → A ⟨args, slotValue σ, solHash, callerWord⟩)
    (hsame : ∀ ρ : Val, ρ.Ok → (T.eval ρ).obs = (T0.eval ρ).obs)
    (o : Oracle) (hoa : SourceAsk ev o) :
    Stage (solidCoreRuntime fuel) (mirSem o) c m (SelCall sel fn ws) :=
  loop_stage hsel hfind hw hret (bodyRuns_of_eraseWhile ho h) hT hchk
    (EraseLoopJoin.obl_of_eval hsame hobl) hA o hoa

end Verify.LoopSource.Invariant.Join

/-- info: 'Verify.LoopSource.Invariant.Join.while_certified' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Verify.LoopSource.Invariant.Join.while_certified

/-- info: 'Verify.LoopSource.Invariant.Join.while_certified_generated' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Verify.LoopSource.Invariant.Join.while_certified_generated

/-- info: 'Verify.LoopSource.Invariant.Join.while_stage' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Verify.LoopSource.Invariant.Join.while_stage

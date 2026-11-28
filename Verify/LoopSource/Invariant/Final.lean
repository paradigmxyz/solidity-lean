import Verify.LoopSource.Invariant.Seqs
import Verify.LoopSource.Equiv.EraseLoopFinal
import Verify.Phase3.Infer.SeqW
import Verify.Spec.TreeLoopCheck

/-!
# The published theorem of a `while` loop through its invariant

`Route.final_of_generatedW_spec` (`Verify/Phase3/Route/FinalW.lean`) publishes the driver's
`Shapes.Certified` for a one-loop function whose body `eraseLoopStmt` erases. This module states
the same conclusion for a body whose loop is a `while` loop erased through an invariant
(`Invariant/While.lean`), in terms of values the driver computes and the kernel decides:

* `whileOf c? sel fuel wd = some (n, b, Te)`: the checked contract's function at `sel` has arity
  `n`, its body erases by `eraseWhile` with the loop's data `wd` (which `check` recomputes inside
  the erasure: the condition, the body's guards and end at the header proposed by `wd`) to `b`,
  whose tree is `Te`;
* `srcSeqsOf c? sel wd Is μs = some ss0` with every sequent valid: the source loop's obligations
  (`Invariant.Obl`) for the invariant `Is` and measure `μs` over the source header's words, by
  `obl_of_whileSeqs`;
* the MIR side as `final_of_generatedW` takes it: the cut check, the sequents `allSeqsW` of the
  MIR invariant `I` and measure `μ` over a tree `T` observably equal to `Te`, the backend stage,
  the loop checker and the fixed-fuel premises.

The two invariants are separate and both untrusted until the kernel checks their sequents.

**The spec** (`final_of_whileW_spec`): `TreeLoop.LoopSpec` names `eraseLoopStmt`, so this route
takes `WhileSpec` instead: the bundle is the contract's export (`ExportedFor`) and its allowed
statuses and postcondition hold on the erased tree `Te` for the function, whichever it is of arity
`n`. `whileSpec_of_check` gives it from the kernel's `whileSpecCheck` (the export's names and its
only spec of `sel`, as `exportedCheck`) and `TreeMeets` of every function spec of the selector at
`TreeLoop.ctx0` on `Te`; a bundle with no spec of the selector gives none (`not_whileSpec_of_none`).

Nothing here names a contract, a selector or a file. Every theorem is proved; no axiom is added.
-/

namespace Verify.LoopSource.Invariant.Final
open SolarTV SolarTV.Machine SolarTV.MIR.Lowered SolidCore.Refinement SolidCore.Refinement.Generic
open SolidCore.Solidity.Source Verify.LoopSource.Interface Verify.LoopSource.Generic
open SolidCore.Refinement.Generic.Loop SolidCore.Refinement.Solar
open Verify.LoopSource.Equiv Verify.LoopSource.Invariant
open Verify.LoopSource.Equiv.GenObl (Checked)
open Verify.LoopSource.Equiv.EraseLoopFinal (sigOf obl_of_eval onTree_of_eval)
open SolidCore.Refinement.Shapes (bundlePost bundleAllowed ctxOfCall idStep)
open SolidCore.Spec.TreeLoop (ExportedFor exportedCheck exportedFor_of_check onTree_ctxOfCall
  onTree_ctxOfCall_fixed)

/-! ## What the driver computes -/

/-- The arity, the `eraseWhile` erasure and its tree of the function at `sel`, with the loop data
`wd`, at fuel `fuel`. -/
def whileOf (c? : Checked) (sel fuel : Nat) (wd : WhileData) : Option (Nat × Br × Tree) := do
  let c ← c?.toOption
  let fn ← c.core.findFunctionBySelector? sel
  let ws ← widthsOf fn.params fn.paramAbiCleanups
  let b ← eraseWhile { envOf c.core with facts := argFacts ws 0 } wd fuel fn.body (initState fn)
  let T ← brTree fn (argFacts ws 0) b
  pure (fn.params.length, b, T)

/-- The source loop's sequents for the invariant `I` and the measure `μ`, in the function's
erasure environment. -/
def srcSeqsOf (c? : Checked) (sel : Nat) (wd : WhileData) (I : List Inv.F) (μ : WExpr) :
    Option (List Inv.Seq) := do
  let c ← c?.toOption
  let fn ← c.core.findFunctionBySelector? sel
  let ws ← widthsOf fn.params fn.paramAbiCleanups
  whileSeqs { envOf c.core with facts := argFacts ws 0 } wd I μ

/-- **The function the computed facts speak of.** -/
theorem facts_of {c? : Checked} {sel fuel n : Nat} {wd : WhileData} {b : Br} {Te : Tree}
    {ws : List Nat} {I : List Inv.F} {μ : WExpr} {ss : List Inv.Seq}
    (hE : whileOf c? sel fuel wd = some (n, b, Te)) (hS : sigOf c? sel = some (ws, true))
    (hs : srcSeqsOf c? sel wd I μ = some ss) :
    ∃ c fn, c? = .ok c ∧ c.core.findFunctionBySelector? sel = some fn ∧
      widthsOf fn.params fn.paramAbiCleanups = some ws ∧ fn.returns.all wordBinding = true ∧
      fn.params.length = n ∧
      eraseWhile { envOf c.core with facts := argFacts ws 0 } wd fuel fn.body (initState fn) = some b ∧
      brTree fn (argFacts ws 0) b = some Te ∧
      whileSeqs { envOf c.core with facts := argFacts ws 0 } wd I μ = some ss := by
  cases hc : c? with
  | error e => simp [sigOf, hc, Except.toOption] at hS
  | ok c =>
    cases hf : c.core.findFunctionBySelector? sel with
    | none => simp [sigOf, hc, hf, Except.toOption] at hS
    | some fn =>
      cases hw : widthsOf fn.params fn.paramAbiCleanups with
      | none => simp [sigOf, hc, hf, hw, Except.toOption] at hS
      | some ws' =>
        simp only [sigOf, hc, hf, hw, Except.toOption, Option.bind_eq_bind, Option.bind_some,
          Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hS
        obtain ⟨rfl, hr⟩ := hS
        simp only [srcSeqsOf, hc, hf, hw, Except.toOption, Option.bind_eq_bind,
          Option.bind_some] at hs
        cases he : eraseWhile { envOf c.core with facts := argFacts ws' 0 } wd fuel fn.body
            (initState fn) with
        | none => simp [whileOf, hc, hf, hw, he, Except.toOption] at hE
        | some b' =>
          cases ht : brTree fn (argFacts ws' 0) b' with
          | none => simp [whileOf, hc, hf, hw, he, ht, Except.toOption] at hE
          | some T' =>
            simp only [whileOf, hc, hf, hw, he, ht, Except.toOption, Option.bind_eq_bind,
              Option.bind_some, Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hE
            obtain ⟨rfl, rfl, rfl⟩ := hE
            exact ⟨c, fn, rfl, hf, hw, hr, rfl, he, ht, hs⟩

/-! ## The published theorem -/

/-- **The published `while` loop theorem from the MIR side's obligations**: any proof of `Obl`
for the record `recOf I μ` over the sequents' tree `T`. -/
theorem final_of_while_obl {fuel sel n E B X M pi ex : Nat} {c? : Checked} {wd : WhileData}
    {Is : List Inv.F} {μs : WExpr} {ss0 : List Inv.Seq} {b : Br} {Te T : Tree}
    {ws : List Nat} {C : Cut} {ev : EnvFlags} {m : Module} {le li : List (Facts × Out)}
    {I : List Inv.F} {μ : WExpr} {q : Assemble.Program} {code : ByteArray}
    {scope : Call → Prop} {cert : Assemble.Cert} {mx : List Nat} {Valid : Call → Prop}
    {Allowed Post : Call → Observable → Prop} {R : LoopRecord}
    (hsel : sel < 2 ^ 32)
    (hE : whileOf c? sel fuel wd = some (n, b, Te)) (hS : sigOf c? sel = some (ws, true))
    (hsrc : srcSeqsOf c? sel wd Is μs = some ss0) (hv0 : ∀ s ∈ ss0, s.Valid)
    (hchk : C.check ev m sel n = some (le, li))
    (ho : Verify.LoopSource.Equiv.Obl (fun _ => Inv.recOf I μ) id (fun _ => True) (fun _ => True) n C.cases T le li)
    (hsame : ∀ ρ : Val, ρ.Ok → (Te.eval ρ).obs = (T.eval ρ).obs)
    (backend : Stage (mirSem Shapes.oracle) (evmirSem Shapes.oracle) m q scope)
    (hscope : ∀ call, scope call)
    (asm : AssembleLoop.checkL q code cert mx = true)
    (hsub : ∀ call, Valid call → ∃ σ args, args.length = n ∧ (∀ a ∈ args, a < 2 ^ 256) ∧
      argsClean ws args = true ∧ call = selCall sel σ args)
    (hinh : ∃ call, Valid call)
    (hAl : ∀ fn : FunctionDef, fn.params.length = n → OnTree sel fn ws T Allowed)
    (hP : ∀ fn : FunctionDef, fn.params.length = n → OnTree sel fn ws T Post)
    (loops : ∀ call, Valid call → Verify.Gas.FixedFuel.Loops (EVM.Program.block Shapes.oracle call q)
      (0, [], SolarTV.Machine.State.initial call) R E B X M)
    (hpi : Verify.Gas.FixedFuel.perIterGas cert B = pi)
    (hex : Verify.Gas.FixedFuel.exitGas cert E X = ex) (hfit : M * pi + ex < 2 ^ 64) :
    ∃ c, c? = .ok c ∧
      Shapes.Certified (solidCoreRuntime fuel) c code Valid Allowed Post (fun _ => M * pi + ex) := by
  obtain ⟨c, fn, hc, hf, hw, hr, hn, he, ht, hs0⟩ := facts_of hE hS hsrc
  have hsrcObl := obl_of_whileSeqs hs0 hv0
  have hgas : AssembleLoop.gasBoundL cert (Verify.Gas.FixedFuel.fixedFuel E B X M) = M * pi + ex := by
    rw [Verify.Gas.FixedFuel.gasBoundL_fixed, Verify.Gas.FixedFuel.fixedGas, hpi, hex]
  have h := LeastFuel.certified_of_bodyRuns_loops hsel hf hw hr (bodyRuns_of_eraseWhile hsrcObl he)
    ht (hn ▸ hchk) (L := fun _ => Inv.recOf I μ) (toSrc := id) (X := fun _ => True)
    (A := fun _ => True) (obl_of_eval hsame (hn ▸ ho)) (fun _ _ _ => trivial)
    backend (fun call _ => hscope call) asm
    (fun call hc => by
      obtain ⟨σ, args, hl, ha, hcl, rfl⟩ := hsub call hc
      exact ⟨σ, args, ⟨hl.trans hn.symm, ha, hcl⟩, rfl⟩)
    hinh (onTree_of_eval hsame (hAl fn hn)) (onTree_of_eval hsame (hP fn hn)) loops
    (hgas ▸ hfit)
  rw [hgas] at h
  exact ⟨c, hc, h⟩

/-- **The published `while` loop theorem from `allSeqsW`**: the MIR invariant and measure
`loop_infer.py` proposes, over the tree of the source's own `eraseWhile` erasure. -/
theorem final_of_whileW {fuel sel n E B X M pi ex : Nat} {c? : Checked} {wd : WhileData}
    {Is : List Inv.F} {μs : WExpr} {ss0 : List Inv.Seq} {b : Br} {Te T : Tree}
    {ws : List Nat} {C : Cut} {ev : EnvFlags} {m : Module} {le li : List (Facts × Out)}
    {I : List Inv.F} {μ : WExpr} {ss : List Inv.Seq} {q : Assemble.Program} {code : ByteArray}
    {scope : Call → Prop} {cert : Assemble.Cert} {mx : List Nat} {Valid : Call → Prop}
    {Allowed Post : Call → Observable → Prop} {R : LoopRecord}
    (hsel : sel < 2 ^ 32)
    (hE : whileOf c? sel fuel wd = some (n, b, Te)) (hS : sigOf c? sel = some (ws, true))
    (hsrc : srcSeqsOf c? sel wd Is μs = some ss0) (hv0 : ∀ s ∈ ss0, s.Valid)
    (hchk : C.check ev m sel n = some (le, li))
    (hss : Verify.Phase3.Infer.allSeqsW n C.cases T le li I μ = some ss) (hv : ∀ s ∈ ss, s.Valid)
    (hsame : ∀ ρ : Val, ρ.Ok → (Te.eval ρ).obs = (T.eval ρ).obs)
    (backend : Stage (mirSem Shapes.oracle) (evmirSem Shapes.oracle) m q scope)
    (hscope : ∀ call, scope call)
    (asm : AssembleLoop.checkL q code cert mx = true)
    (hsub : ∀ call, Valid call → ∃ σ args, args.length = n ∧ (∀ a ∈ args, a < 2 ^ 256) ∧
      argsClean ws args = true ∧ call = selCall sel σ args)
    (hinh : ∃ call, Valid call)
    (hAl : ∀ fn : FunctionDef, fn.params.length = n → OnTree sel fn ws T Allowed)
    (hP : ∀ fn : FunctionDef, fn.params.length = n → OnTree sel fn ws T Post)
    (loops : ∀ call, Valid call → Verify.Gas.FixedFuel.Loops (EVM.Program.block Shapes.oracle call q)
      (0, [], SolarTV.Machine.State.initial call) R E B X M)
    (hpi : Verify.Gas.FixedFuel.perIterGas cert B = pi)
    (hex : Verify.Gas.FixedFuel.exitGas cert E X = ex) (hfit : M * pi + ex < 2 ^ 64) :
    ∃ c, c? = .ok c ∧
      Shapes.Certified (solidCoreRuntime fuel) c code Valid Allowed Post (fun _ => M * pi + ex) :=
  final_of_while_obl hsel hE hS hsrc hv0 hchk (Verify.Phase3.Infer.obl_of_seqsW hss hv) hsame
    backend hscope asm hsub hinh hAl hP loops hpi hex hfit

/-! ## The exported spec on the erased tree -/

/-- **The `while` route's spec premises**: `b` is the contract's export with a spec of `sel`, and
its allowed statuses and postcondition hold on the erased tree `T` for the function of arity `n`. -/
structure WhileSpec (c? : Checked) (sel n : Nat) (ws : List Nat) (T : Tree)
    (b : SolidCore.Spec.Bundle) : Prop where
  exported : ∀ c, c? = .ok c → ExportedFor c b sel
  allowed : ∀ fn : FunctionDef, fn.params.length = n → OnTree sel fn ws T (bundleAllowed b ctxOfCall)
  post : ∀ fn : FunctionDef, fn.params.length = n → OnTree sel fn ws T (bundlePost b ctxOfCall idStep)

/-- The kernel's check of the bundle's names: the contract type checks, and `b` is its export
with its function of `sel`'s spec, the only one of `sel`, at index `i` (`exportedCheck`). -/
def whileSpecCheck (c? : Checked) (sel : Nat) (b : SolidCore.Spec.Bundle) (i : Nat) : Bool :=
  match c? with
  | .ok c =>
    match c.core.findFunctionBySelector? sel with
    | some f => exportedCheck c.decl.name f b sel i
    | none => false
  | .error _ => false

theorem exported_of_check {c? : Checked} {sel : Nat} {b : SolidCore.Spec.Bundle} {i : Nat}
    (h : whileSpecCheck c? sel b i = true) : ∀ c, c? = .ok c → ExportedFor c b sel := by
  rintro c rfl
  simp only [whileSpecCheck] at h
  split at h
  · rename_i f hf
    exact exportedFor_of_check hf h
  · cases h

/-- **The spec premises from the kernel's check and `TreeMeets` on the erased tree.** -/
theorem whileSpec_of_check {c? : Checked} {sel n : Nat} {ws : List Nat} {T : Tree}
    {b : SolidCore.Spec.Bundle} {i : Nat} (hsel : sel < 2 ^ 32) (hchk : whileSpecCheck c? sel b i = true)
    (hm : ∀ fs ∈ b.spec.specs, fs.selector = sel →
      SolidCore.Spec.TreeMeets b fs SolidCore.Spec.TreeLoop.ctx0 n T) :
    WhileSpec c? sel n ws T b where
  exported := exported_of_check hchk
  allowed fn hl := (onTree_ctxOfCall (fn := fn) (ws := ws) hsel (hl ▸ hm)).1
  post fn hl := (onTree_ctxOfCall (fn := fn) (ws := ws) hsel (hl ▸ hm)).2

/-- The same from `TreeMeetsFixed`. -/
theorem whileSpec_of_check_fixed {c? : Checked} {sel n : Nat} {ws : List Nat} {T : Tree}
    {b : SolidCore.Spec.Bundle} {i : Nat} (hsel : sel < 2 ^ 32) (hchk : whileSpecCheck c? sel b i = true)
    (hm : ∀ fs ∈ b.spec.specs, fs.selector = sel →
      SolidCore.Spec.TreeMeetsFixed b fs SolidCore.Spec.TreeLoop.ctx0 n T) :
    WhileSpec c? sel n ws T b where
  exported := exported_of_check hchk
  allowed fn hl := (onTree_ctxOfCall_fixed (fn := fn) (ws := ws) hsel (hl ▸ hm)).1
  post fn hl := (onTree_ctxOfCall_fixed (fn := fn) (ws := ws) hsel (hl ▸ hm)).2

/-- **A bundle with no spec of the selector gives no `WhileSpec`** for a contract that type
checks: the spec is never the vacuous `OnTree` of a bundle that says nothing of the function. -/
theorem not_whileSpec_of_none {c? : Checked} {c : SolidCore.Solidity.TypeCheck.CheckedContract}
    (hc : c? = .ok c) {sel n : Nat} {ws : List Nat} {T : Tree} {b : SolidCore.Spec.Bundle}
    (h : ∀ fs ∈ b.spec.specs, fs.selector ≠ sel) : ¬ WhileSpec c? sel n ws T b := by
  intro hw
  obtain ⟨-, -, -, fs, hfs, hs, -⟩ := hw.exported c hc
  exact h fs hfs hs

/-- **With the exported spec**: the allowed statuses and postcondition are solar-verify's export
`bd` (`bundleAllowed bd ctxOfCall`, `bundlePost bd ctxOfCall idStep`) on the erased tree `Te`, and
`bd` is the contract's export (`ExportedFor`). -/
theorem final_of_whileW_spec {fuel sel n E B X M pi ex : Nat} {c? : Checked} {wd : WhileData}
    {Is : List Inv.F} {μs : WExpr} {ss0 : List Inv.Seq} {b : Br} {Te T : Tree}
    {ws : List Nat} {C : Cut} {ev : EnvFlags} {m : Module} {le li : List (Facts × Out)}
    {I : List Inv.F} {μ : WExpr} {ss : List Inv.Seq} {q : Assemble.Program} {code : ByteArray}
    {scope : Call → Prop} {cert : Assemble.Cert} {mx : List Nat} {Valid : Call → Prop}
    {R : LoopRecord} {bd : SolidCore.Spec.Bundle}
    (hsel : sel < 2 ^ 32)
    (hE : whileOf c? sel fuel wd = some (n, b, Te)) (hS : sigOf c? sel = some (ws, true))
    (hsrc : srcSeqsOf c? sel wd Is μs = some ss0) (hv0 : ∀ s ∈ ss0, s.Valid)
    (hchk : C.check ev m sel n = some (le, li))
    (hss : Verify.Phase3.Infer.allSeqsW n C.cases T le li I μ = some ss) (hv : ∀ s ∈ ss, s.Valid)
    (hsame : ∀ ρ : Val, ρ.Ok → (Te.eval ρ).obs = (T.eval ρ).obs)
    (hspec : WhileSpec c? sel n ws Te bd)
    (backend : Stage (mirSem Shapes.oracle) (evmirSem Shapes.oracle) m q scope)
    (hscope : ∀ call, scope call)
    (asm : AssembleLoop.checkL q code cert mx = true)
    (hsub : ∀ call, Valid call → ∃ σ args, args.length = n ∧ (∀ a ∈ args, a < 2 ^ 256) ∧
      argsClean ws args = true ∧ call = selCall sel σ args)
    (hinh : ∃ call, Valid call)
    (loops : ∀ call, Valid call → Verify.Gas.FixedFuel.Loops (EVM.Program.block Shapes.oracle call q)
      (0, [], SolarTV.Machine.State.initial call) R E B X M)
    (hpi : Verify.Gas.FixedFuel.perIterGas cert B = pi)
    (hex : Verify.Gas.FixedFuel.exitGas cert E X = ex) (hfit : M * pi + ex < 2 ^ 64) :
    ∃ c, c? = .ok c ∧
      Shapes.Certified (solidCoreRuntime fuel) c code Valid (bundleAllowed bd ctxOfCall)
        (bundlePost bd ctxOfCall idStep) (fun _ => M * pi + ex) ∧
      ExportedFor c bd sel := by
  have hback : ∀ ρ : Val, ρ.Ok → (T.eval ρ).obs = (Te.eval ρ).obs := fun ρ h => (hsame ρ h).symm
  obtain ⟨c, hc, hcert⟩ := final_of_whileW hsel hE hS hsrc hv0 hchk hss hv hsame backend hscope asm
    hsub hinh (fun fn hl => onTree_of_eval hback (hspec.allowed fn hl))
    (fun fn hl => onTree_of_eval hback (hspec.post fn hl)) loops hpi hex hfit
  exact ⟨c, hc, hcert, hspec.exported c hc⟩

end Verify.LoopSource.Invariant.Final

/-- info: 'Verify.LoopSource.Invariant.Final.final_of_while_obl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Verify.LoopSource.Invariant.Final.final_of_while_obl

/-- info: 'Verify.LoopSource.Invariant.Final.final_of_whileW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Verify.LoopSource.Invariant.Final.final_of_whileW

/-- info: 'Verify.LoopSource.Invariant.Final.whileSpec_of_check' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Verify.LoopSource.Invariant.Final.whileSpec_of_check

/-- info: 'Verify.LoopSource.Invariant.Final.final_of_whileW_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Verify.LoopSource.Invariant.Final.final_of_whileW_spec

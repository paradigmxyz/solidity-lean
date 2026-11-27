import Verify.Phase3.Infer.SeqW
import Verify.LoopSource.Equiv.EraseLoopFinal
import Verify.Spec.TreeLoopCheck

/-!
# The published loop theorem for discovered invariants, with the exported spec

`EraseLoopFinal.final_of_generated` publishes the driver's `Shapes.Certified` for a one-loop function
from the generator's modules, with the sequents `Inv.allSeqs` of an invariant and a measure. Two
things keep it from serving a loop whose result is a loop word, or from carrying the contract's
NatSpec:

* `allSeqs` compares two ends only through `haltGoals`, which has no goal for a computed output
  word: a function that returns a loop word has no sequents. `Verify.Phase3.Infer.allSeqsW` adds
  those goals and `obl_of_seqsW` proves the same `Obl`.
* its allowed statuses and postcondition are premises; the generated loop final declares them `True`.

This module states the theorem once from `Obl` itself (`final_of_obl`), so any route that proves the
obligations of the erased loop's leaves (the built-in sequents, `allSeqsW`, or a later checker) gives
the published statement, and then:

* `final_of_generatedW`: the same from `allSeqsW`, the sequents `loop_infer.py`'s candidates are
  checked against (the invariant and measure are untrusted until `valid`);
* `final_of_obl_spec`, `final_of_generatedW_spec`: the specification is solar-verify's export `bd`
  (`Shapes.bundleAllowed bd ctxOfCall`, `Shapes.bundlePost bd ctxOfCall idStep`), from the O6 spec
  bridge's `TreeLoop.LoopSpec` on the **erased tree** `Te`, the tree the obligations' tree `T`
  observes alike (`hsame`). The property therefore comes from the spec bundle the source exports
  (spec_connect.py binds that bundle to the run's fresh export: `spec_is_fresh`), never from a
  target the inference tool was handed, and the tree the invariant is checked against is the
  source's own erasure (`erasedOf_eq`), never one the tool chose. The conclusion keeps
  `ExportedFor c bd sel`.

Nothing here names a contract, a selector or a file. Every theorem is proved; no axiom is added.
-/

namespace Verify.Phase3.Route
open SolarTV SolarTV.Machine SolarTV.MIR.Lowered SolidCore.Refinement SolidCore.Refinement.Generic
open SolidCore.Solidity.Source Verify.LoopSource.Interface Verify.LoopSource.Generic
open SolidCore.Refinement.Generic.Loop SolidCore.Refinement.Solar
open Verify.LoopSource.Equiv
open Verify.LoopSource.Equiv.GenObl (Checked erasedOf)
open Verify.LoopSource.Equiv.EraseLoopFinal (sigOf facts_of obl_of_eval onTree_of_eval)
open SolidCore.Refinement.Shapes (bundlePost bundleAllowed ctxOfCall idStep)

/-- `OnTree` speaks of a function only through its arity. -/
theorem onTree_of_length {sel : Nat} {fn fn' : FunctionDef} {ws : List Nat} {T : Tree}
    {Q : Call → Observable → Prop} (h : OnTree sel fn ws T Q)
    (hl : fn.params.length = fn'.params.length) : OnTree sel fn' ws T Q :=
  fun σ args ⟨ha, hb, hc⟩ => h σ args ⟨ha.trans hl.symm, hb, hc⟩

/-- **The published loop theorem from the obligations themselves**: `final_of_generated` with the
sequents replaced by any proof of `Obl` for the record `recOf I μ` over the sequents' tree `T`. -/
theorem final_of_obl {fuel sel n E B X M pi ex : Nat} {c? : Checked} {b : Br} {Te T : Tree}
    {ws : List Nat} {C : Cut} {ev : EnvFlags} {m : Module} {le li : List (Facts × Out)}
    {I : List Inv.F} {μ : WExpr} {q : Assemble.Program} {code : ByteArray}
    {scope : Call → Prop} {cert : Assemble.Cert} {mx : List Nat} {Valid : Call → Prop}
    {Allowed Post : Call → Observable → Prop} {R : LoopRecord}
    (hsel : sel < 2 ^ 32)
    (hE : erasedOf c? sel fuel = some (n, b, Te)) (hS : sigOf c? sel = some (ws, true))
    (hchk : C.check ev m sel n = some (le, li))
    (ho : Obl (fun _ => Inv.recOf I μ) id (fun _ => True) (fun _ => True) n C.cases T le li)
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
  obtain ⟨c, fn, hc, hf, hw, hr, hn, he, ht⟩ := facts_of hE hS
  have hgas : AssembleLoop.gasBoundL cert (Verify.Gas.FixedFuel.fixedFuel E B X M) = M * pi + ex := by
    rw [Verify.Gas.FixedFuel.gasBoundL_fixed, Verify.Gas.FixedFuel.fixedGas, hpi, hex]
  have h := LeastFuel.eraseLoop_certified_loops fuel c sel fn ws b Te hsel hf hw hr he ht C ev m le li
    (hn ▸ hchk) (fun _ => Inv.recOf I μ) id (fun _ => True) (fun _ => True)
    (obl_of_eval hsame (hn ▸ ho)) (fun _ _ _ => trivial) q code scope cert mx
    backend (fun call _ => hscope call) asm Valid Allowed Post
    (fun call hc => by
      obtain ⟨σ, args, hl, ha, hcl, rfl⟩ := hsub call hc
      exact ⟨σ, args, ⟨hl.trans hn.symm, ha, hcl⟩, rfl⟩)
    hinh (onTree_of_eval hsame (hAl fn hn)) (onTree_of_eval hsame (hP fn hn)) R E B X M loops
    (hgas ▸ hfit)
  rw [hgas] at h
  exact ⟨c, hc, h⟩

/-- **The published loop theorem from `allSeqsW`**: the sequents of the invariant and measure
`loop_infer.py` proposes, over the tree of the source's own erasure. -/
theorem final_of_generatedW {fuel sel n E B X M pi ex : Nat} {c? : Checked} {b : Br} {Te T : Tree}
    {ws : List Nat} {C : Cut} {ev : EnvFlags} {m : Module} {le li : List (Facts × Out)}
    {I : List Inv.F} {μ : WExpr} {ss : List Inv.Seq} {q : Assemble.Program} {code : ByteArray}
    {scope : Call → Prop} {cert : Assemble.Cert} {mx : List Nat} {Valid : Call → Prop}
    {Allowed Post : Call → Observable → Prop} {R : LoopRecord}
    (hsel : sel < 2 ^ 32)
    (hE : erasedOf c? sel fuel = some (n, b, Te)) (hS : sigOf c? sel = some (ws, true))
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
  final_of_obl hsel hE hS hchk (Verify.Phase3.Infer.obl_of_seqsW hss hv) hsame backend hscope asm
    hsub hinh hAl hP loops hpi hex hfit

/-- **With the exported spec**: the allowed statuses and postcondition are solar-verify's export
`bd` (`bundleAllowed bd ctxOfCall`, `bundlePost bd ctxOfCall idStep`), from the spec bridge's
`LoopSpec` on the erased tree `Te`; `bd` is the contract's export (`ExportedFor`). -/
theorem final_of_obl_spec {fuel sel n E B X M pi ex : Nat} {c? : Checked} {b : Br} {Te T : Tree}
    {ws : List Nat} {C : Cut} {ev : EnvFlags} {m : Module} {le li : List (Facts × Out)}
    {I : List Inv.F} {μ : WExpr} {q : Assemble.Program} {code : ByteArray}
    {scope : Call → Prop} {cert : Assemble.Cert} {mx : List Nat} {Valid : Call → Prop}
    {R : LoopRecord} {bd : SolidCore.Spec.Bundle}
    (hsel : sel < 2 ^ 32)
    (hE : erasedOf c? sel fuel = some (n, b, Te)) (hS : sigOf c? sel = some (ws, true))
    (hchk : C.check ev m sel n = some (le, li))
    (ho : Obl (fun _ => Inv.recOf I μ) id (fun _ => True) (fun _ => True) n C.cases T le li)
    (hsame : ∀ ρ : Val, ρ.Ok → (Te.eval ρ).obs = (T.eval ρ).obs)
    (hspec : ∀ c, c? = .ok c → SolidCore.Spec.TreeLoop.LoopSpec c fuel sel ws Te bd)
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
      SolidCore.Spec.TreeLoop.ExportedFor c bd sel := by
  obtain ⟨c, fn, hc, hf, -, -, hn, -, -⟩ := facts_of hE hS
  obtain ⟨f, -, hf', -, -, -, -, -, hA, hP, hx⟩ := hspec c hc
  obtain rfl : f = fn := Option.some.inj (hf'.symm.trans hf)
  have hback : ∀ ρ : Val, ρ.Ok → (T.eval ρ).obs = (Te.eval ρ).obs := fun ρ h => (hsame ρ h).symm
  have hAl : ∀ fn' : FunctionDef, fn'.params.length = n →
      OnTree sel fn' ws T (bundleAllowed bd ctxOfCall) :=
    fun fn' hl => onTree_of_length (onTree_of_eval hback hA) (hn.trans hl.symm)
  have hPo : ∀ fn' : FunctionDef, fn'.params.length = n →
      OnTree sel fn' ws T (bundlePost bd ctxOfCall idStep) :=
    fun fn' hl => onTree_of_length (onTree_of_eval hback hP) (hn.trans hl.symm)
  obtain ⟨c', hc', hcert⟩ := final_of_obl hsel hE hS hchk ho hsame backend hscope asm hsub hinh hAl
    hPo loops hpi hex hfit
  obtain rfl : c' = c := by
    have := hc'.symm.trans hc
    simpa using this
  exact ⟨c', hc', hcert, hx⟩

/-- **`allSeqsW` with the exported spec**: the route a loop with no hand-written invariant takes. -/
theorem final_of_generatedW_spec {fuel sel n E B X M pi ex : Nat} {c? : Checked} {b : Br}
    {Te T : Tree} {ws : List Nat} {C : Cut} {ev : EnvFlags} {m : Module} {le li : List (Facts × Out)}
    {I : List Inv.F} {μ : WExpr} {ss : List Inv.Seq} {q : Assemble.Program} {code : ByteArray}
    {scope : Call → Prop} {cert : Assemble.Cert} {mx : List Nat} {Valid : Call → Prop}
    {R : LoopRecord} {bd : SolidCore.Spec.Bundle}
    (hsel : sel < 2 ^ 32)
    (hE : erasedOf c? sel fuel = some (n, b, Te)) (hS : sigOf c? sel = some (ws, true))
    (hchk : C.check ev m sel n = some (le, li))
    (hss : Verify.Phase3.Infer.allSeqsW n C.cases T le li I μ = some ss) (hv : ∀ s ∈ ss, s.Valid)
    (hsame : ∀ ρ : Val, ρ.Ok → (Te.eval ρ).obs = (T.eval ρ).obs)
    (hspec : ∀ c, c? = .ok c → SolidCore.Spec.TreeLoop.LoopSpec c fuel sel ws Te bd)
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
      SolidCore.Spec.TreeLoop.ExportedFor c bd sel :=
  final_of_obl_spec hsel hE hS hchk (Verify.Phase3.Infer.obl_of_seqsW hss hv) hsame hspec backend
    hscope asm hsub hinh loops hpi hex hfit

end Verify.Phase3.Route

/-- info: 'Verify.Phase3.Route.final_of_obl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Verify.Phase3.Route.final_of_obl

/-- info: 'Verify.Phase3.Route.final_of_generatedW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Verify.Phase3.Route.final_of_generatedW

/-- info: 'Verify.Phase3.Route.final_of_obl_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Verify.Phase3.Route.final_of_obl_spec

/-- info: 'Verify.Phase3.Route.final_of_generatedW_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Verify.Phase3.Route.final_of_generatedW_spec

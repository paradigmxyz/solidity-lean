import Verify.LoopSource.Equiv.EraseLoopLeastFuel
import Verify.LoopSource.Equiv.GenObl
import Verify.Gas.FixedFuel.Gas

/-!
# The published loop theorem from the driver's generated modules

`EraseLoopJoin.eraseLoop_certified_generated` (`GeneratedTarget`, in EraseLoopCounterJoin.lean) takes, for one function of a
checked contract, facts about that function (its selector, ABI widths, word returns, erasure and
tree) that the driver cannot name before the contract is checked: `c`, `fn` and `ws` are bound by
the contract. `final_of_generated` restates it in terms of values the driver computes and the
kernel decides:

* `GenObl.erasedOf c? sel fuel = some (n, b, Te)`, the generator's `erasedOf_eq` (by `kernel_rfl`);
* `sigOf c? sel = some (ws, true)`: the function's ABI widths and that its returns are words;
* the generator's `leaves`, `seqs`, `valid` and `same` (the cut check, the sequents and their
  validity over the sequents' tree `T`, and `T` observably equal to the erased tree `Te`);
* a backend stage from the cut's first lowered MIR to the final EVM IR `q`, on every call of a
  scope covering every call;
* the loop checker on the bytes, and the fixed-fuel premises (`Loops`, the fit) with the gas
  bound split as `M * pi + ex` (`perIterGas`, `exitGas` by `decide`);
* valid calls that are calls of `sel` with `n` clean argument words (`hsub`), an inhabited `Valid`,
  and the allowed statuses and postcondition on `T` for the function, whichever it is.

The proof is `GeneratedTarget`'s, through `LeastFuel.eraseLoop_certified_loops` (`BridgeTarget`); it
is restated here, with the two tree-transport lemmas, so that this module imports no contract:
EraseLoopCounterJoin.lean imports Counter's export, whose `SolarTV.Export.Counter` names would clash
with a run's own export of a contract named Counter.

It concludes the driver's statement shape `∃ c, c? = .ok c ∧ Shapes.Certified (solidCoreRuntime
fuel) c code Valid Allowed Post (fun _ => M * pi + ex)`. Nothing here names a contract, a selector
or a file.
-/

namespace Verify.LoopSource.Equiv.EraseLoopFinal
open SolarTV SolarTV.Machine SolarTV.MIR.Lowered SolidCore.Refinement SolidCore.Refinement.Generic
open SolidCore.Solidity.Source Verify.LoopSource.Interface Verify.LoopSource.Generic
open SolidCore.Refinement.Generic.Loop SolidCore.Refinement.Solar
open Verify.LoopSource.Equiv.GenObl (Checked erasedOf)

/-- **Obligations depend on the tree only through its observables** (as
`EraseLoopJoin.obl_of_eval`). -/
theorem obl_of_eval {L : Val → LoopRecord} {toSrc : Val → Val} {X A : Val → Prop} {n : Nat}
    {cases : List Facts} {T T0 : Tree} {le li : List (Facts × Out)}
    (h : ∀ ρ : Val, ρ.Ok → (T.eval ρ).obs = (T0.eval ρ).obs)
    (o : Obl L toSrc X A n cases T0 le li) : Obl L toSrc X A n cases T le li where
  entry ρ hl hok hA p hp hh := by
    have hx := o.entry ρ hl hok hA p hp hh
    obtain ⟨F, out⟩ := p
    cases out with
    | exit U =>
      dsimp only at hx ⊢
      rw [h ρ hok]
      exact hx
    | back hs => exact hx
  iter σ hl hok hA hP hX p hp hh := by
    have hx := o.iter σ hl hok hA hP hX p hp hh
    obtain ⟨F, out⟩ := p
    cases out with
    | exit U =>
      dsimp only at hx ⊢
      rw [h (trunc n σ) hok]
      exact hx
    | back hs => exact hx
  facts := o.facts

/-- **Tree properties move the same way** (as `EraseLoopJoin.onTree_of_eval`). -/
theorem onTree_of_eval {sel : Nat} {fn : FunctionDef} {ws : List Nat} {T T0 : Tree}
    {Q : Call → Observable → Prop} (h : ∀ ρ : Val, ρ.Ok → (T.eval ρ).obs = (T0.eval ρ).obs)
    (hQ : OnTree sel fn ws T0 Q) : OnTree sel fn ws T Q := by
  intro σ args ha
  rw [h ⟨args, slotValue σ, solHash, callerWord⟩ (slotValue_store σ)]
  exact hQ σ args ha

/-- The ABI widths of the function at `sel` of a checked contract, and whether its returns are
words: `none` when there is no such function or its arguments have no word widths. -/
def sigOf (c? : Checked) (sel : Nat) : Option (List Nat × Bool) := do
  let c ← c?.toOption
  let fn ← c.core.findFunctionBySelector? sel
  let ws ← widthsOf fn.params fn.paramAbiCleanups
  pure (ws, fn.returns.all wordBinding)

/-- **The function the computed facts speak of**: a checked contract, its function at `sel` with
widths `ws` and word returns, of arity `n`, whose body erases to `b` with tree `Te`. -/
theorem facts_of {c? : Checked} {sel fuel n : Nat} {b : Br} {Te : Tree} {ws : List Nat}
    (hE : erasedOf c? sel fuel = some (n, b, Te)) (hS : sigOf c? sel = some (ws, true)) :
    ∃ c fn, c? = .ok c ∧ c.core.findFunctionBySelector? sel = some fn ∧
      widthsOf fn.params fn.paramAbiCleanups = some ws ∧ fn.returns.all wordBinding = true ∧
      fn.params.length = n ∧
      eraseLoopStmt { envOf c.core with facts := argFacts ws 0 } fuel fn.body (initState fn) = some b ∧
      brTree fn (argFacts ws 0) b = some Te := by
  have hErased := GenObl.erased_of hE
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
        obtain ⟨hn, he, ht⟩ := hErased c hc fn ws' hf hw
        exact ⟨c, fn, rfl, hf, hw, hr, hn, he, ht⟩

/-- **The published loop theorem** from the generated modules: `GeneratedTarget` at the
contract's own function, with `T0` the sequents' tree, the record `recOf I μ` and the gas bound
`M * pi + ex`. -/
theorem final_of_generated {fuel sel n E B X M pi ex : Nat} {c? : Checked} {b : Br} {Te T : Tree}
    {ws : List Nat} {C : Cut} {ev : EnvFlags} {m : Module} {le li : List (Facts × Out)}
    {I : List Inv.F} {μ : WExpr} {ss : List Inv.Seq} {q : Assemble.Program} {code : ByteArray}
    {scope : Call → Prop} {cert : Assemble.Cert} {mx : List Nat} {Valid : Call → Prop}
    {Allowed Post : Call → Observable → Prop} {R : LoopRecord}
    (hsel : sel < 2 ^ 32)
    (hE : erasedOf c? sel fuel = some (n, b, Te)) (hS : sigOf c? sel = some (ws, true))
    (hchk : C.check ev m sel n = some (le, li))
    (hss : Inv.allSeqs n C.cases T le li I μ = some ss) (hv : ∀ s ∈ ss, s.Valid)
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
    (obl_of_eval hsame (Inv.obl_of_seqs (hn ▸ hss) hv)) (fun _ _ _ => trivial) q code scope cert mx
    backend (fun call _ => hscope call) asm Valid Allowed Post
    (fun call hc => by
      obtain ⟨σ, args, hl, ha, hcl, rfl⟩ := hsub call hc
      exact ⟨σ, args, ⟨hl.trans hn.symm, ha, hcl⟩, rfl⟩)
    hinh (onTree_of_eval hsame (hAl fn hn)) (onTree_of_eval hsame (hP fn hn)) R E B X M loops
    (hgas ▸ hfit)
  rw [hgas] at h
  exact ⟨c, hc, h⟩

/-- info: 'Verify.LoopSource.Equiv.EraseLoopFinal.final_of_generated' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms final_of_generated

end Verify.LoopSource.Equiv.EraseLoopFinal

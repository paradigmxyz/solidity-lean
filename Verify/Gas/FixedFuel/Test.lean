import Verify.Gas.FixedFuel.Gas

/-!
# Tests of the fixed-fuel gas stage

* **A bounded loop.** `for (i = 0; i < 10; i++)` as a machine on its counter (`countStep`),
  with its record and bridge. The run ends within `fixedFuel 0 1 1 10 = 11` steps
  (`count_ends`), and that fuel is tight: at 10 steps it has not ended (`count_tight`).
  Its verdict, at the per-iteration and exit gas the driver reports for the bounded test
  contract, is `bounded`.
* **A loop that must be REJECTED for resources.** A loop to an argument word: the measure bound
  over all calls is `2 ^ 256 - 1`, so the fixed bound is past `2 ^ 64` and the verdict is
  `outOfGas`, which refutes `Resources` at it (`arg_not_resources`).
-/

namespace Verify.Gas.FixedFuel.Test

open Verify.Gas.FixedFuel Verify.LoopSource.Interface
open SolidCore.Refinement.Generic (Val WExpr BinOp SymState Br wordSize)

/-- `for (i = 0; i < 10; i++)` on its counter: the header is the counter's value. -/
def countStep (s : SolarTV.Machine.State) : Nat → Option (Res ⊕ Nat) := fun i =>
  if i < 10 then some (.inr (i + 1)) else some (.inl (.stop, s))

/-- Its record: the counter is argument word 0 of the header valuation. -/
def countRecord (H : SymState) (bb : Br) : LoopRecord where
  H := H
  P σ := σ.args.getD 0 0 ≤ 10
  m σ := 10 - σ.args.getD 0 0
  c := .bin .lt (.arg 0) (.lit 10)
  bb := bb

theorem count_cond {H : SymState} {bb : Br} (σ : Val) (h : σ.args.getD 0 0 ≤ 10) :
    (countRecord H bb).c.eval σ = 0 ↔ 10 ≤ σ.args.getD 0 0 := by
  have h1 : σ.args.getD 0 0 % wordSize = σ.args.getD 0 0 :=
    Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt h (by decide))
  have h2 : (10 : Nat) % wordSize = 10 := by decide
  have h3 : (1 : Nat) % wordSize = 1 := by decide
  have h4 : (0 : Nat) % wordSize = 0 := by decide
  simp only [countRecord, WExpr.eval, BinOp.eval, h1, h2]
  by_cases hl : σ.args.getD 0 0 < 10
  · simp only [hl, ite_true, h3]
    omega
  · simp only [hl, ite_false, h4]
    exact ⟨fun _ => Nat.le_of_not_lt hl, fun _ => trivial⟩

/-- Its bridge: one step per iteration, one step to stop. -/
def countBridge (s : SolarTV.Machine.State) (H : SymState) (bb : Br) :
    Bridge (countRecord H bb) (countStep s) 1 1 where
  At σ i := i = σ.args.getD 0 0
  iter := by
    intro σ i hx hp hc
    have hp' : σ.args.getD 0 0 ≤ 10 := hp
    have hlt : σ.args.getD 0 0 < 10 := by
      refine Nat.lt_of_not_le fun hn => hc ?_
      exact (count_cond σ hp').mpr hn
    let σ' : Val := { σ with args := [σ.args.getD 0 0 + 1] }
    have hstep : (countRecord H bb).Step σ σ' := by
      refine ⟨hp, hc, ?_, ?_⟩
      · show [σ.args.getD 0 0 + 1].getD 0 0 ≤ 10
        simp only [List.getD_cons_zero]
        omega
      · show 10 - [σ.args.getD 0 0 + 1].getD 0 0 < 10 - σ.args.getD 0 0
        simp only [List.getD_cons_zero]
        omega
    refine ⟨σ', i + 1, hstep, ?_, 1, Nat.le_refl 1, .cont ?_ (.refl _)⟩
    · show i + 1 = [σ.args.getD 0 0 + 1].getD 0 0
      simp only [List.getD_cons_zero, hx]
    · subst hx
      simp only [countStep, hlt, ite_true]
  done := by
    intro σ i hx hp hc
    have hge : 10 ≤ σ.args.getD 0 0 := (count_cond σ hp).mp hc
    have hn : ¬ i < 10 := by omega
    exact ⟨(.stop, s), by simp only [SolarTV.Machine.iterate, countStep, hn, ite_false]⟩

/-- The loop from counter 0: the header at once, measure 10. -/
theorem count_loops (s : SolarTV.Machine.State) (H : SymState) (bb : Br) :
    Loops (countStep s) 0 (countRecord H bb) 0 1 1 10 :=
  ⟨countBridge s H bb, ⟨[0], fun _ => 0, fun _ _ => 0, 0⟩, 0, ⟨0, Nat.le_refl 0, .refl _⟩,
    rfl, by simp [countRecord], by simp [countRecord]⟩

/-- **The bounded loop ends within its fixed fuel.** -/
theorem count_ends (s : SolarTV.Machine.State) (H : SymState) (bb : Br) :
    ∃ r, SolarTV.Machine.iterate (countStep s) (fixedFuel 0 1 1 10) 0 = some r :=
  ends_of_loops (count_loops s H bb)

/-- The fixed fuel is 11 and the run needs all of it. -/
theorem count_tight (s : SolarTV.Machine.State) :
    fixedFuel 0 1 1 10 = 11 ∧ SolarTV.Machine.iterate (countStep s) 10 0 = none ∧
      SolarTV.Machine.iterate (countStep s) 11 0 = some (.stop, s) := by
  refine ⟨rfl, ?_, ?_⟩ <;> simp [SolarTV.Machine.iterate, countStep]

/-! The verdicts at the numbers the driver reports for its two test contracts
(tools/certify/examples/fixed_fuel: `bounded.sol` and `word_limit.sol`). -/

/-- Per-iteration and exit gas of the bounded contract's loop. -/
def boundedPerIter : Nat := 22100 * (2 * 22)
def boundedExit : Nat := 22100 * ((1 + 3) * 22) + 12

theorem bounded_verdict :
    verdictOf (some 10) boundedPerIter boundedExit = .bounded 11668812 := by decide

/-- Per-iteration and exit gas of the argument-bounded contract's loop. -/
def argPerIter : Nat := 22100 * (2 * 29)
def argExit : Nat := 22100 * ((1 + 3) * 29) + 12

theorem arg_verdict :
    verdictOf (some (2 ^ 256 - 1)) argPerIter argExit =
      .outOfGas ((2 ^ 256 - 1) * argPerIter + argExit) := by decide

/-- **REJECTED for resources**: no `Resources` at the argument-bounded loop's fixed bound. -/
theorem arg_not_resources {S : SolarTV.Sem} {p : S.Prog} {code : ByteArray}
    {Valid : SolarTV.Call → Prop} {call : SolarTV.Call} (hc : Valid call) :
    ¬SolidCore.Refinement.Shapes.Resources S p code Valid
      (fun _ => (2 ^ 256 - 1) * argPerIter + argExit) :=
  not_resources_of_outOfGas arg_verdict hc

/-- The three verdicts are distinct. -/
example (G G' : Nat) : Verdict.bounded G ≠ .outOfGas G' ∧ Verdict.bounded G ≠ .unsupported ∧
    Verdict.outOfGas G ≠ .unsupported := by
  refine ⟨?_, ?_, ?_⟩ <;> intro h <;> cases h

end Verify.Gas.FixedFuel.Test

/-- info: 'Verify.Gas.FixedFuel.Test.count_ends' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Verify.Gas.FixedFuel.Test.count_ends

/-- info: 'Verify.Gas.FixedFuel.resources_of_verdict' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Verify.Gas.FixedFuel.resources_of_verdict

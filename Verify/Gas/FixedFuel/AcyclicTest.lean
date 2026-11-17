import Verify.Gas.FixedFuel.Acyclic

/-!
# Tests of the fixed fuel of a loop-free program

A ranked program ends within its rank's fuel under every oracle (`ends_three`); the rank check
refuses a wrong rank, a loop and a dynamic jump, so a program outside the loop-free fragment never
gets a fuel from here.
-/

namespace Verify.Gas.FixedFuel.AcyclicTest

open SolarTV SolarTV.Machine SolarTV.EVM.Program Verify.Gas.FixedFuel.Acyclic

/-- A dispatcher's shape: block 0 branches to 2 or falls through to 1, which jumps to 2. -/
def diamond : Program :=
  { blocks := [[.effect .callvalue 0, .jumpi 2], [.op (.stack (.push 0)), .jump 2],
    [.op (.stack (.push 0)), .op (.stack (.push 0)), .ret]] }

theorem diamond_ok : rankOk diamond [2, 1, 0] = true := by decide +kernel

theorem ends_three (o : Oracle) (call : Call) : (run o diamond call 3).isSome = true :=
  ends_of_rank diamond_ok (by decide +kernel) o call

/-- Every fuel from the rank's on. -/
theorem ends_six (o : Oracle) (call : Call) : (run o diamond call 6).isSome = true :=
  ends_of_rank diamond_ok (by decide +kernel) o call

/-- A rank that does not decrease along a jump. -/
theorem diamond_wrong : rankOk diamond [2, 0, 0] = false := by decide +kernel

/-- A rank of the wrong length. -/
theorem diamond_short : rankOk diamond [2, 1] = false := by decide +kernel

/-- A loop has no rank. -/
def spin : Program := { blocks := [[.jumpi 1, .jump 0], [.stop]] }

theorem spin_none (rk : List Nat) : rankOk spin rk = false := by
  cases h : rankOk spin rk
  · rfl
  · simp only [rankOk, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at h
    have h0 := h.2 0 (by decide)
    simp only [spin, targets, List.getD, List.getElem?_cons_zero, Option.getD_some, Option.map_some,
      List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true, rankOf] at h0
    simp at h0

/-- A dynamic jump has no rank. -/
def dyn : Program := { blocks := [[.jumpDyn]] }

theorem dyn_none (rk : List Nat) : rankOk dyn rk = false := by
  simp [rankOk, dyn, targets, List.getD]

/-- info: 'Verify.Gas.FixedFuel.Acyclic.ends_of_rank' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ends_of_rank

/-- info: 'Verify.Gas.FixedFuel.AcyclicTest.ends_three' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ends_three

end Verify.Gas.FixedFuel.AcyclicTest

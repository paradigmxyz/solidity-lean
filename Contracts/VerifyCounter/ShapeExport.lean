import Contracts.VerifyCounter.ShapeSource
import Verify.ShapeSpecExport
import verify_counter.gen.Counter.Spec

/-!
# VerifyCounter's bump against solar-verify's own export of its spec

`ShapeSource.published` states the four obligations of the exact bytecode against SolidCore's
checked `Counter` with `Shapes.specPost VerifyCounter.spec`, a Lean restatement of the NatSpec.
This file states the same with the postcondition read off solar-verify's export of
Certified/verify_counter/verify_counter.sol, written fresh by the certify driver
(`Certified.verify_counter.gen.Counter.Spec.Counter`, `Shapes.bundlePost`), so that the
specification of the statement is the tool's output, not a copy of it:

* `meets`: every SolidCore result of a valid call (`bump(n)`, `n < 2 ^ 32`, no value, any
  storage) meets the exported spec of every function: `increment` and `max` do not apply (their
  selectors differ), and `bump`'s `count == old(count) + n` and the invariant `count <= limit`
  hold of every success, from `Source.success_spec` (slot 0 is the old count plus `n`, at most
  the limit in slot 1, which the call leaves as it was);
* `published`: `Shapes.Certified` with that postcondition, equivalence, termination and resources
  from `ShapeSource.published`;
* `nonvacuous`: the exported spec rejects a success of `bump(1)` that leaves `count` at 0, and
  the allowed statuses reject a revert with empty data.
-/

namespace Contracts.VerifyCounter.ShapeExport

open SolidCore.Refinement SolarTV Contracts.VerifyCounter.Source Contracts.VerifyCounter.ShapeSource
open SolidCore.Refinement.Shapes SolidCore.Spec SolidCore.Refinement.Generic.Loop

/-- The exported spec bundle. -/
abbrev B : Bundle := Certified.verify_counter.gen.Counter.Spec.Counter

/-- The postcondition of the statement: solar-verify's export of the source. -/
def post : Call → Observable → Prop := bundlePost B ctxOfCall idStep

theorem bumpSel_lt : bumpSel < 2 ^ 32 := by decide

theorem slotValue_lt (σ : List (Nat × Nat)) (k : Nat) : slotValue σ k < 2 ^ 256 := by
  unfold slotValue
  suffices ∀ (l : List (Nat × Nat)) (a : Nat), a < 2 ^ 256 →
      l.foldl (fun acc kv => if kv.1 % 2^256 = k % 2^256 then kv.2 % 2^256 else acc) a < 2 ^ 256 from
    this σ 0 (by decide)
  intro l
  induction l with
  | nil => intro a h; exact h
  | cons kv l ih =>
    intro a h
    simp only [List.foldl_cons]
    apply ih
    split
    · exact Nat.mod_lt _ (by decide)
    · exact h

theorem decodes_bump {a : Nat} (ha : a < 2 ^ 256) {args : List Int}
    (h : decodeWords [.uint 256] (words (((Abi.calldata bumpSel [a]).data.toList.map (·.toNat)).drop 4)) = some args) :
    args = [(a : Int)] := by
  rw [SolidCore.Spec.words_calldata bumpSel (by simpa using ha)] at h
  simp only [Nat.reducePow] at ha
  simpa [decodeWords, Ty.ofWord, ha, eq_comm] using h

/-- **The exported spec of every SolidCore result of a valid call.** -/
theorem meets {c : SolidCore.Solidity.TypeCheck.CheckedContract} (hc : contract? = .ok c) :
    Shapes.Meets (solidCoreRuntime fuel) c ValidS post := by
  obtain ⟨T, hT⟩ := tree_ok
  rintro _ ⟨σ, a, ha, rfl⟩ obs hrun fs hfs args pre hpre
  change runtimeRun fuel c (bumpCall σ a) = some obs at hrun
  have haw : a < 2 ^ 256 := by omega
  simp only [B, Certified.verify_counter.gen.Counter.Spec.Counter, List.mem_cons, List.not_mem_nil,
    or_false] at hfs
  rcases hfs with rfl | rfl | rfl
  · exact absurd hpre (not_pre_of_sel bumpSel_lt (by decide) [a] 0 σ)
  · obtain ⟨⟨-, -, hd⟩, hst, -, -, hinv⟩ := hpre
    have hargs := decodes_bump haw hd
    subst hargs
    refine ⟨fun hs => ?_, fun h => absurd rfl h⟩
    obtain ⟨h0, hle, hframe⟩ := success_spec hc hT σ a haw hrun hs
    have h1 := hframe 1 (by decide)
    have l0 := slotValue_lt σ 0
    have l1 := slotValue_lt σ 1
    simp only [Nat.reducePow] at l0 l1
    refine ⟨[], rfl, ?_, ?_⟩ <;>
      simp only [Bundle.satAll, Bundle.sat, List.mem_cons, List.not_mem_nil, or_false, forall_eq,
        eval, slotOf, mkEnv, Env.cur, BinOp.apply, Ty.ofBits, ofProp_ne_zero, hst, h0, h1,
        ite_true, ite_false, Bool.false_eq_true, wordMod, toWord, List.getD_cons_zero, bumpCall, B,
        Certified.verify_counter.gen.Counter.Spec.Counter, h1] <;>
      (try simp only [Nat.mul_zero, pow_zero, Nat.div_one, Nat.reducePow, Nat.reduceMul, Nat.reduceMod,
        Int.reduceMod, Int.zero_emod, Int.toNat_zero, Int.reduceToNat]) <;>
      (try simp only [h1]) <;>
      (try simp only [Nat.mod_eq_of_lt l0, Nat.mod_eq_of_lt l1]) <;> push_cast <;> omega
  · exact absurd hpre (not_pre_of_sel bumpSel_lt (by decide) [a] 0 σ)

/-- **The published statement, with solar-verify's export as its specification.** -/
theorem published : ∃ c, contract? = .ok c ∧
    Shapes.Certified (solidCoreRuntime fuel) c SolarTV.Milestone.VerifyCounter.code ValidS Allowed post
      SolarTV.Milestone.VerifyCounter.Bump.gasBound := by
  obtain ⟨c, hc, h⟩ := ShapeSource.published
  exact ⟨c, hc, ⟨h.inhabited, h.equiv, h.terminates, meets hc, h.resources⟩⟩

/-- The exported spec and the allowed statuses each reject a result of a valid call. -/
theorem nonvacuous :
    (∃ (call : Call) (obs : Observable), ValidS call ∧ ¬ post call obs) ∧
      (∃ (call : Call) (obs : Observable), ValidS call ∧ obs.success = false ∧ ¬ Allowed call obs) := by
  refine ⟨⟨bumpCall [] 1, ⟨true, [], [], fun _ => 0⟩, ⟨[], 1, by decide, rfl⟩, fun h => ?_⟩,
    ⟨bumpCall [] 0, ⟨false, [], [], fun _ => 0⟩, ⟨[], 0, by decide, rfl⟩, rfl, ?_⟩⟩
  · have hpre : Pre B (B.spec.specs[1]'(by decide)) (ctxOfCall (bumpCall [] 1))
        ⟨slotValue [], Ghost.zero, 1⟩ (bumpCall [] 1) [1] := by
      refine ⟨⟨?_, ?_, ?_⟩, rfl, ?_, ?_, ?_⟩
      · decide
      · exact selectorOf_calldata bumpSel_lt [1] 0 []
      · have := SolidCore.Spec.words_calldata bumpSel (args := [1]) (by simp)
        simp only [bumpCall] at this ⊢
        rw [this]; decide
      · simp [ctxOfCall]
      · simp [Bundle.satAll, B, Certified.verify_counter.gen.Counter.Spec.Counter]
      · simp [Bundle.satAll, Bundle.sat, B, Certified.verify_counter.gen.Counter.Spec.Counter, Holds', eval,
          slotOf, mkEnv, Env.cur, BinOp.apply, Ty.ofBits, slotValue]
    have := (h _ (List.getElem_mem _) _ _ hpre).1 rfl
    obtain ⟨rets, -, hens, -⟩ := this
    simp [Bundle.satAll, Bundle.sat, B, Certified.verify_counter.gen.Counter.Spec.Counter, Holds', eval,
      slotOf, mkEnv, Env.cur, BinOp.apply, Ty.ofBits, slotValue] at hens
  · simp only [Allowed, Bool.false_eq_true, false_or]
    rintro (h | h) <;> simp at h <;> exact absurd h (by decide)

/-- info: 'Contracts.VerifyCounter.ShapeExport.published' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms published

/-- info: 'Contracts.VerifyCounter.ShapeExport.nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms nonvacuous

end Contracts.VerifyCounter.ShapeExport

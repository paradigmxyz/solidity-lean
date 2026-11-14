import SolidCore.Refinement.Solar.Counter.AssemblyAt
import SolidCore.Refinement.Sequence

/-!
# counter: every sequence of inc calls, storage carried between calls

A deployed Counter sees a sequence of calls, each from the storage the previous one left.
refinesSeq states that SolidCore's checked Counter and solar's bytecode show the same
observables on every finite sequence of inc calls (any argument words, no value) from the
deployed storage, each call starting from the previous call's final storage exactly: the
lifting theorem of SolidCore/Refinement/Sequence.lean (refinesSeq_of_closed) applied to the
source and assembly runs from any storage (source_run_at, target_run_at), which both give
expectedAt σ d.

* next obs, the storage list the next call starts from, is slot 0's word: [(0, obs.storage 0)].
* onlySlot0 σ: σ holds nothing outside slot 0. The deployed storage [] does, and inc keeps it
  (it writes only slot 0, or reverts and keeps σ), and on it next is exact: it reads back as the
  whole final storage (exact_next).
* two_calls: the case of two calls spelled out, inc(d1) then inc(d2) from the deployed storage:
  both sides show expectedAt [] d1, then expectedAt [(0, d1)] d2, the second call seeing slot 0
  holding d1.
-/

namespace SolidCore.Refinement.Solar.Counter

open EthLib.Base SolidCore.Refinement SolidCore.Refinement.Abi SolidCore.Refinement.Evm.Wide

/-- The storage list the next call starts from: slot 0's word. -/
def next (obs : Observable) : List (Nat × Nat) := [(0, obs.storage 0)]

/-- The messages of the sequences: inc on any argument word, with no value. -/
def incMsg : Msg → Prop := fun m => ∃ d : U256, m = ⟨(callOf incSelector [d]).calldata, 0⟩

/-- Storage that holds nothing outside slot 0. -/
def onlySlot0 (σ : List (Nat × Nat)) : Prop := ∀ slot, slot % 2 ^ 256 ≠ 0 → slotValue σ slot = 0

theorem slotValue_next (w slot : Nat) :
    slotValue [(0, w)] slot = if slot % 2 ^ 256 = 0 then w % 2 ^ 256 else 0 := by
  show (if 0 % 2 ^ 256 = slot % 2 ^ 256 then w % 2 ^ 256 else 0) = _
  by_cases h : slot % 2 ^ 256 = 0
  · rw [ite_eq_left (by rw [h, Nat.zero_mod]), ite_eq_left h]
  · rw [ite_eq_right (by rw [Nat.zero_mod]; exact Ne.symm h), ite_eq_right h]

theorem onlySlot0_next (obs : Observable) : onlySlot0 (next obs) := by
  intro slot h
  rw [next, slotValue_next, ite_eq_right h]

/-- From storage with nothing outside slot 0, the storage list next gives after inc reads back
as exactly the final storage. -/
theorem exact_next {σ : List (Nat × Nat)} (hσ : onlySlot0 σ) (d : U256) :
    Exact next (expectedAt σ d) := by
  funext slot
  rw [next, slotValue_next]
  have hlt := slotValue_lt σ 0
  have hmod := SolidCore.Refinement.Evm.Wide.slotValue_mod σ slot
  have hz := hσ slot
  unfold expectedAt
  by_cases hof : slotValue σ 0 + d.toNat < 2 ^ 256 <;>
    by_cases h : slot % 2 ^ 256 = 0 <;>
    simp only [Nat.reducePow] at hof h hlt hmod hz ⊢
  · simp only [hof, h, ↓reduceIte, Nat.zero_mod]
    exact Nat.mod_eq_of_lt hof
  · simp only [hof, h, ↓reduceIte]
    exact (hz h).symm
  · simp only [hof, h, ↓reduceIte]
    rw [Nat.mod_eq_of_lt hlt, ← hmod, h]
  · simp only [hof, h, ↓reduceIte]
    exact (hz h).symm

theorem onlySlot0_nil : onlySlot0 [] := fun _ _ => rfl

/-- **The counter on every sequence of inc calls**: from the deployed storage, SolidCore's
checked Counter and solar's bytecode on EthLib finish every finite sequence of inc calls with
the same observables, each call starting from exactly the storage the previous one left. -/
theorem refinesSeq : ∃ c, contract? = .ok c ∧ RefinesSeq fuel c code next [] incMsg := by
  obtain ⟨c, hc, -⟩ := satisfiesAt
  refine ⟨c, hc, refinesSeq_of_closed onlySlot0 onlySlot0_nil ?_ ?_⟩
  · rintro σ - call ⟨m, ⟨d, rfl⟩, rfl⟩
    exact ⟨expectedAt σ d, source_run_at hc d σ, target_run_at d σ⟩
  · rintro σ hσ m ⟨d, rfl⟩ obs hrun
    have h := target_run_at d σ
    change Target.run code { callOf incSelector [d] with storage := σ } = some obs at hrun
    rw [h] at hrun
    cases hrun
    exact ⟨exact_next hσ d, onlySlot0_next _⟩

/-- **Two calls**, spelled out: inc(d1) then inc(d2) from the deployed storage, on SolidCore and
on solar's bytecode, the second call starting from slot 0 holding d1. -/
theorem two_calls {c : SolidCore.Solidity.TypeCheck.CheckedContract} (hc : contract? = .ok c)
    (d1 d2 : U256) :
    let ms : List Msg := [⟨(callOf incSelector [d1]).calldata, 0⟩, ⟨(callOf incSelector [d2]).calldata, 0⟩]
    let obss := [expected d1, expectedAt [(0, d1.toNat)] d2]
    runSeq (Source.run fuel c) next [] ms = some obss ∧
      runSeq (Target.run code) next [] ms = some obss := by
  have hn : next (expected d1) = [(0, d1.toNat)] := by
    simp [next, expected]
  have hs1 : Source.run fuel c ⟨(callOf incSelector [d1]).calldata, 0, []⟩ = some (expected d1) := by
    have h := source_run_at hc d1 []
    rwa [expectedAt_nil] at h
  have ht1 : Target.run code ⟨(callOf incSelector [d1]).calldata, 0, []⟩ = some (expected d1) := by
    have h := target_run_at d1 []
    rwa [expectedAt_nil] at h
  have hs2 : Source.run fuel c ⟨(callOf incSelector [d2]).calldata, 0, next (expected d1)⟩ =
      some (expectedAt [(0, d1.toNat)] d2) := by
    rw [hn]
    exact source_run_at hc d2 _
  have ht2 : Target.run code ⟨(callOf incSelector [d2]).calldata, 0, next (expected d1)⟩ =
      some (expectedAt [(0, d1.toNat)] d2) := by
    rw [hn]
    exact target_run_at d2 _
  simp only [runSeq, Msg.call, hs1, hs2, ht1, ht2, Option.map_some, and_self]

/-- info: 'SolidCore.Refinement.Solar.Counter.refinesSeq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms refinesSeq

/-- info: 'SolidCore.Refinement.Solar.Counter.two_calls' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms two_calls

end SolidCore.Refinement.Solar.Counter

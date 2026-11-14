import SolidCore.Refinement.Solar.Counter.Spec

/-!
# counter: the specification of `inc` from any storage

Spec.lean states `post` for any storage but proves it, and SolidCore's run, from the deployed
(empty) storage, where slot 0 holds 0 and the overflow branch is never reached. This file proves
both on `scopeAt`, every call of `inc(d)` with no value from any storage `σ`, which the call
writes over the deployed storage (`run_eq_at`).

* `expectedAt σ d`: success with slot 0 holding `x + d` (`x` the word in slot 0 of `σ`) and every
  other slot of `σ` kept when `x + d` fits; otherwise a revert with Panic(0x11) keeping `σ`.
* `run_inc_at`: SolidCore runs `inc` from `σ` to `expectedAt σ d`, by symbolic evaluation of the
  interpreter (`wide_symex`), both branches of the overflow check included.
* `vcsAt`, `implementsAt`, `specAt`, `satisfiesAt`: Loom's verification conditions of `model`
  on `scopeAt`, and the specification as a triple and as `Satisfies` on SolidCore.
* `source_run_at`: `run_inc_at` from the checked contract, for the source stage.
-/

namespace SolidCore.Refinement.Solar.Counter

open EthLib.Base SolidCore.Refinement SolidCore.Refinement.Abi SolidCore.Refinement.Wide
open SolidCore.Refinement.Evm.Wide SolidCore.Solidity SolidCore.Solidity.Source SolidCore.Verify

/-- What a call of `inc(d)` from the storage `σ` shows, with `x` the word in slot 0: when
`x + d` fits, success with no output and slot 0 holding `x + d`; otherwise a revert with
`Panic(0x11)` that keeps `σ`. -/
def expectedAt (σ : List (Nat × Nat)) (d : U256) : Observable :=
  if slotValue σ 0 + d.toNat < 2 ^ 256 then
    { success := true, output := [], logs := [],
      storage := fun slot => if slot % 2 ^ 256 = 0 then slotValue σ 0 + d.toNat else slotValue σ slot }
  else { success := false, output := panic 0x11, logs := [], storage := slotValue σ }

theorem observe_model_at (σ : List (Nat × Nat)) (d : U256) :
    observe (slotValue σ) (model [d.toNat] (slotValue σ)) = expectedAt σ d := by
  unfold expectedAt
  by_cases h : slotValue σ 0 + d.toNat < 2 ^ 256
  · simp only [model, sload, sstore, bind, StateT.bind, pure, StateT.pure, Except.bind,
      Except.pure, List.getD_cons_zero, h, ↓reduceIte, observe, Nat.zero_mod, Nat.mod_eq_of_lt h]
  · simp only [model, sload, bind, StateT.bind, Except.bind, revert, List.getD_cons_zero, h,
      ↓reduceIte, observe]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem run_inc_at {c : TypeCheck.CheckedContract} (hcore : c.core = coreLit) {d : Source.State}
    (hd : DeployedAt fuel c d []) (w : U256) (σ : List (Nat × Nat)) :
    Source.run fuel c (callAt incSelector [w] σ) = some (expectedAt σ w) := by
  rw [run_eq_at hd]
  have hev := hd.events
  have h0 : ∀ q : Nat, d.storage[q]? = none := fun q => hd.getElem?_eq_none (by simp)
  have hget := getD_storage h0 σ
  generalize σ.foldl (fun acc kv => StorageMap.insertLoop acc kv.1 kv.2) d.storage = m at hget
  simp only [hcore, List.map_cons, List.map_nil]
  wide_symex [coreLit, fuel, ctxOf, hcore, incSelector, get?_insert]
  all_goals
    have hx0 := hget 0
    have hlt := slotValue_lt σ 0
    have hw := w.isLt
    simp only [Nat.zero_mod] at hx0
  case pos =>
    rename_i hp
    have hno : ¬ slotValue σ 0 + w.toNat < 2 ^ 256 := by
      revert hp
      cases hm : m[0]? with
      | none =>
        simp only [hm, Option.getD_none] at hx0
        rw [← hx0]
        simp only [Nat.reducePow] at hw ⊢
        omega
      | some v =>
        simp only [hm, Option.getD_some] at hx0
        rw [← hx0]
        rw [← hx0] at hlt
        simp only [Nat.reducePow] at hw hlt ⊢
        omega
    simp only [expectedAt, hno, ↓reduceIte, Source.observe, callAt]
    rfl
  case h_1 =>
    rename_i hp _ v heq
    rw [heq] at hx0 hp
    simp only [Option.getD_some] at hx0
    subst hx0
    have hyes : slotValue σ 0 + w.toNat < 2 ^ 256 := by
      simp only [Nat.reducePow] at hw hlt hp ⊢
      omega
    have hm : slotValue σ 0 % 2 ^ 256 = slotValue σ 0 := Nat.mod_eq_of_lt hlt
    simp only [Nat.reducePow] at hm
    try simp only [hm, Nat.mod_eq_of_lt hlt]
    simp only [expectedAt, hyes, ↓reduceIte]
    simp [Source.observe, State.logEntries, State.loadSlot, StorageMap.lookup?]
    funext slot
    have hs := hget slot
    simp only [Nat.reducePow] at hs
    simp only [Std.HashMap.getElem?_insert, Shared.norm, Shared.wordModulus, EvmYul.UInt256.size, beq_iff_eq]
    rw [← hs]
    have hyes' : slotValue σ 0 + w.toNat < 115792089237316195423570985008687907853269984665640564039457584007913129639936 := hyes
    by_cases hz : slot % 115792089237316195423570985008687907853269984665640564039457584007913129639936 = 0
    · simp only [hz, ↓reduceIte, Nat.mod_eq_of_lt hyes']
    · have hz' : ¬ 0 = slot % 115792089237316195423570985008687907853269984665640564039457584007913129639936 := fun e => hz e.symm
      simp only [hz, hz', ↓reduceIte]
      cases m[slot % 115792089237316195423570985008687907853269984665640564039457584007913129639936]? <;> rfl
  case h_2 =>
    rename_i hp _ heq
    rw [heq] at hx0 hp
    simp only [Option.getD_none] at hx0
    have hyes : slotValue σ 0 + w.toNat < 2 ^ 256 := by rw [← hx0]; simpa using hw
    unfold expectedAt
    rw [← hx0, Nat.zero_add]
    simp only [w.isLt, ↓reduceIte]
    simp [Source.observe, State.logEntries, State.loadSlot, StorageMap.lookup?]
    funext slot
    have hs := hget slot
    simp only [Nat.reducePow] at hs
    simp only [Std.HashMap.getElem?_insert, Shared.norm, Shared.wordModulus, EvmYul.UInt256.size, beq_iff_eq]
    rw [← hs]
    have hyes' : slotValue σ 0 + w.toNat < 115792089237316195423570985008687907853269984665640564039457584007913129639936 := hyes
    by_cases hz : slot % 115792089237316195423570985008687907853269984665640564039457584007913129639936 = 0
    · simp only [hz, ↓reduceIte, Nat.mod_eq_of_lt hyes']
    · have hz' : ¬ 0 = slot % 115792089237316195423570985008687907853269984665640564039457584007913129639936 := fun e => hz e.symm
      simp only [hz, hz', ↓reduceIte]
      cases m[slot % 115792089237316195423570985008687907853269984665640564039457584007913129639936]? <;> rfl


/-- Every call of `inc` on any argument word, with no value, from any storage. -/
def scopeAt : Call → Prop := fun call => ∃ σ, fullScope fns σ call

theorem scopeAt_callOf {call : Call} (h : scopeAt call) :
    ∃ d : U256, ∃ σ, call = { callOf incSelector [d] with storage := σ } := by
  obtain ⟨σ, fn, hfn, args, hlen, hlt, rfl⟩ := h
  simp only [fns, List.mem_singleton] at hfn
  subst hfn
  match args, hlen with
  | [a], _ =>
    refine ⟨BitVec.ofNat 256 a, σ, ?_⟩
    have ha' : a % 2 ^ 256 = a := Nat.mod_eq_of_lt (hlt a (by simp))
    simp only [callOf, List.map_cons, List.map_nil, BitVec.toNat_ofNat, ha']

theorem expectedAt_nil (d : U256) : expectedAt [] d = expected d := by
  have hd := d.isLt
  simp only [expectedAt, slotValue_nil, Nat.zero_add, hd, ↓reduceIte, expected]

/-- `model` implements SolidCore's `Counter` on every call of `scopeAt`. -/
theorem implementsAt {c : TypeCheck.CheckedContract} (hcore : c.core = coreLit) {d : Source.State}
    (hd : DeployedAt fuel c d []) : Implements fuel c scopeAt (argWords 1) model := by
  rintro call ⟨σ, hs⟩
  refine implements_of_run' (s := σ) (by simp [fns]) (fun fn hfn ws hl => ?_) call hs
  simp only [fns, List.mem_cons, List.not_mem_nil, or_false] at hfn
  subst hfn
  rcases ws with _ | ⟨w, _ | _⟩ <;> simp at hl
  rw [List.map_singleton, observe_model_at]
  exact run_inc_at hcore hd w σ

/-- The verification conditions of `inc` from any storage, by Loom's weakest preconditions. -/
theorem vcsAt : ∀ call, scopeAt call → pre call → vc model (argWords 1) post call := by
  rintro call ⟨σ, hs⟩ hp
  refine vcs_of_fullScope (s := σ) (by simp [fns]) ?_ call hs hp
  intro fn hfn call args hcall hw hlen hargs hinit hpre
  simp only [fns, List.mem_cons, List.not_mem_nil, or_false] at hfn
  subst fn hcall
  rcases args with _ | ⟨a, _ | _⟩ <;> simp at hlen
  have ha : a < 2 ^ 256 := hargs a (by simp)
  simp only [model, post, hw, wp_bind, wp_pure, wp_sload, wp_sstore, wp_revert, wp_ite,
    List.getD_cons_zero]
  split
  · rename_i h
    have h' : slotValue σ 0 + a < 115792089237316195423570985008687907853269984665640564039457584007913129639936 := h
    simp
    intro slot
    rw [Nat.mod_eq_of_lt h']
  · rename_i h
    simp

/-- **The specification of Counter's `inc` from any storage**, as a triple against SolidCore. -/
theorem specAt : ∃ c, contract? = .ok c ∧ Triple fuel c scopeAt pre post := by
  obtain ⟨c, hc⟩ := contract_ok
  obtain ⟨hk, _, hemp⟩ := shape_of hc
  obtain ⟨d, hd⟩ := deployed_of hemp
  exact ⟨c, hc, triple_of_wp (implementsAt hk (deployedAt_of_deployed hd)) vcsAt⟩

/-- The specification from any storage as `Satisfies` on SolidCore. -/
theorem satisfiesAt : ∃ c, contract? = .ok c ∧ Satisfies (solidCore fuel) c scopeAt pre post := by
  obtain ⟨c, hc, h⟩ := specAt
  exact ⟨c, hc, satisfies_of_triple h⟩

/-- SolidCore runs `inc` on any argument word from any storage `σ` to `expectedAt σ d`. -/
theorem source_run_at {c : TypeCheck.CheckedContract} (hc : contract? = .ok c) (w : U256)
    (σ : List (Nat × Nat)) :
    Source.run fuel c { callOf incSelector [w] with storage := σ } = some (expectedAt σ w) := by
  obtain ⟨hk, _, hemp⟩ := shape_of hc
  obtain ⟨d, hd⟩ := deployed_of hemp
  exact run_inc_at hk (deployedAt_of_deployed hd) w σ

/-- info: 'SolidCore.Refinement.Solar.Counter.satisfiesAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms satisfiesAt

/-- info: 'SolidCore.Refinement.Solar.Counter.source_run_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms source_run_at

end SolidCore.Refinement.Solar.Counter

import Contracts.UniswapV2.ERC20.Nested.TransferFromSpec

namespace SolidCore.Spec.UniswapV2.ERC20.Nested

open SolarTV SolidCore.Refinement SolidCore.Refinement.Generic SolidCore.Refinement.Shapes

/-- The postcondition of every source result on a valid call of transferFrom: exactly
`transferFromResult` of the call's storage and argument words. -/
def TransferFromPost (call : Call) (obs : Observable) : Prop :=
  obs = transferFromResult (slotValue call.storage) ((callArgs call).getD 0 0) ((callArgs call).getD 1 0)
    ((callArgs call).getD 2 0)

/-- The valid calls of transferFrom: the generic stage's. -/
abbrev TransferFromValid (call : Call) : Prop :=
  ∃ σ, Covers deployed σ ∧ SolidCore.Refinement.Abi.fullScope [fn_transferFrom] σ call

/-- **transferFrom's exact sequential result holds of every SolidCore run of the checked
UniswapV2ERC20** on its valid calls. No hash premise. -/
theorem transferFrom_meets {c : SolidCore.Solidity.TypeCheck.CheckedContract}
    (hc : SolidCore.Verify.VC.UniswapV2ERC20.contract? = .ok c) :
    Meets (solidCore SolidCore.Verify.VC.UniswapV2ERC20.fuel) c TransferFromValid TransferFromPost := by
  have hdep := deploy_eq
  simp only [deploy?, hc] at hdep
  obtain ⟨dd, hdd⟩ := Wide.deployedAt_of hdep
  have hmap := transferFrom_erase_eq
  simp only [transferFrom_erase?, hc, Option.map_eq_some_iff, Prod.mk.injEq] at hmap
  obtain ⟨f, hf, hlen, hT⟩ := hmap
  rintro _ ⟨σ, hcov, fn, hfn, args, hl, hargs, rfl⟩ obs hrun
  simp only [List.mem_singleton] at hfn
  subst hfn
  change Source.run SolidCore.Verify.VC.UniswapV2ERC20.fuel c
    { calldata := SolidCore.Refinement.Abi.calldata 599290589 args, callvalue := 0, storage := σ } = some obs at hrun
  have hrun' := source_run hdd hcov (by decide) hf hT args
    (by simpa [fn_transferFrom] using hl.trans hlen.symm) hargs
  rw [hrun'] at hrun
  cases hrun
  match args, hl, hargs with
  | [frm, dst, value], _, hargs =>
    unfold TransferFromPost callArgs
    rw [words_calldata _ hargs]
    exact transferFrom_tree_eval frm dst value _ (hargs frm (by simp)) (hargs dst (by simp))
      (hargs value (by simp)) (fun k => Generic.slotValue_lt σ k)

theorem upd_eq (st : Nat → Nat) {k : Nat} (v : Nat) (hk : k < 2 ^ 256) : upd st k v k = v := by
  unfold upd; rw [Nat.mod_eq_of_lt hk]; simp

theorem upd_ne (st : Nat → Nat) {k n : Nat} (v : Nat) (hn : n < 2 ^ 256) (h : k ≠ n) :
    upd st k v n = st n := by
  unfold upd; rw [Nat.mod_eq_of_lt hn]; simp [h]

/-- **transferFrom between two parties, key by key, on its footprint**: under keccak256's separation
on the four preimages the call hashes, a clean call succeeds exactly when the allowance is infinite or
covers `value`, the balance covers it and the recipient's balance does not overflow (all on the
storage before the call), and then the allowance is spent (or stays infinite), the balance debited
and the recipient's credited. -/
theorem transferFrom_keys (st : Nat → Nat) (hst : ∀ k, st k < 2 ^ 256) (frm dst value : Nat)
    (hfa : frm < 2 ^ 160) (hda : dst < 2 ^ 160) (hne : frm ≠ dst)
    (h : HashScopeNested.Scoped (HashScopeNested.transferFromFootprint caller frm dst)) :
    ((transferFromResult st frm dst value).success = true ↔
      (st (allowanceSlot frm caller) = umax ∨ value ≤ st (allowanceSlot frm caller)) ∧
        value ≤ st (balanceSlot frm) ∧ st (balanceSlot dst) + value < 2 ^ 256) ∧
    ((transferFromResult st frm dst value).success = true →
      (transferFromResult st frm dst value).storage (allowanceSlot frm caller) =
          (if st (allowanceSlot frm caller) = umax then umax else st (allowanceSlot frm caller) - value) ∧
        (transferFromResult st frm dst value).storage (balanceSlot frm) = st (balanceSlot frm) - value ∧
        (transferFromResult st frm dst value).storage (balanceSlot dst) = st (balanceSlot dst) + value) := by
  obtain ⟨hAF, hAT, hFT, -, -, -⟩ := HashScopeNested.transferFrom_slots h (by decide) (by omega) (by omega)
  have hFT := hFT hne
  have hl := solHash_lt
  simp only [Generic.wordSize] at hl
  have hA := hl caller (solHash frm 2)
  have hF := hl frm 1
  have hT := hl dst 1
  have hsA := hst (allowanceSlot frm caller)
  have hsF := hst (balanceSlot frm)
  have hsT := hst (balanceSlot dst)
  unfold transferFromResult transferSteps revertWith
  simp only [allowanceSlot, balanceSlot, umax] at *
  generalize solHash caller (solHash frm 2) = A at *
  generalize solHash frm 1 = F at *
  generalize solHash dst 1 = T at *
  clear hl hst
  simp only [hfa, hda, and_self, ite_true]
  have r1 := upd_eq st (k := A); have r2 := upd_eq st (k := F); have r3 := upd_eq st (k := T)
  have r1' := fun (s : Nat → Nat) v => upd_eq s (k := A) v hA
  have r2' := fun (s : Nat → Nat) v => upd_eq s (k := F) v hF
  have r3' := fun (s : Nat → Nat) v => upd_eq s (k := T) v hT
  have q1 := fun (s : Nat → Nat) v => upd_ne s v hF hAF
  have q2 := fun (s : Nat → Nat) v => upd_ne s v hT hAT
  have q3 := fun (s : Nat → Nat) v => upd_ne s v hT hFT
  have q4 := fun (s : Nat → Nat) v => upd_ne s v hA (Ne.symm hAT)
  have q5 := fun (s : Nat → Nat) v => upd_ne s v hA (Ne.symm hAF)
  have q6 := fun (s : Nat → Nat) v => upd_ne s v hF (Ne.symm hFT)
  clear r1 r2 r3
  simp only [r1', r2', r3', q1, q2, q3, q4, q5, q6]
  split_ifs <;> simp only [r1', r2', r3', q1, q2, q3, q4, q5, q6, Bool.true_eq_false, Bool.false_eq_true,
    iff_true, iff_false, true_iff, false_iff, true_implies, false_implies, and_true, true_and, not_true_eq_false,
    not_false_eq_true, IsEmpty.forall_iff, if_true, if_false, ite_true, ite_false] <;> omega

/-- **transferFrom to oneself, on its footprint**: success exactly when the allowance is infinite or
covers `value` and the balance covers it, with no overflow condition (the credit reads the debited
slot); the balance is unchanged. -/
theorem transferFrom_self (st : Nat → Nat) (hst : ∀ k, st k < 2 ^ 256) (frm value : Nat)
    (hfa : frm < 2 ^ 160)
    (h : HashScopeNested.Scoped (HashScopeNested.transferFromFootprint caller frm frm)) :
    ((transferFromResult st frm frm value).success = true ↔
      (st (allowanceSlot frm caller) = umax ∨ value ≤ st (allowanceSlot frm caller)) ∧
        value ≤ st (balanceSlot frm)) ∧
    ((transferFromResult st frm frm value).success = true →
      (transferFromResult st frm frm value).storage (balanceSlot frm) = st (balanceSlot frm)) := by
  obtain ⟨hAF, -, -, -, -, -⟩ := HashScopeNested.transferFrom_slots h (by decide) (by omega) (by omega)
  have hl := solHash_lt
  simp only [Generic.wordSize] at hl
  have hA := hl caller (solHash frm 2)
  have hF := hl frm 1
  have hsA := hst (allowanceSlot frm caller)
  have hsF := hst (balanceSlot frm)
  unfold transferFromResult transferSteps revertWith
  simp only [allowanceSlot, balanceSlot, umax] at *
  generalize solHash caller (solHash frm 2) = A at *
  generalize solHash frm 1 = F at *
  clear hl hst
  simp only [hfa, and_self, ite_true]
  have r1' := fun (s : Nat → Nat) v => upd_eq s (k := A) v hA
  have r2' := fun (s : Nat → Nat) v => upd_eq s (k := F) v hF
  have q1 := fun (s : Nat → Nat) v => upd_ne s v hF hAF
  have q5 := fun (s : Nat → Nat) v => upd_ne s v hA (Ne.symm hAF)
  simp only [r1', r2', q1, q5]
  split_ifs <;> simp only [r1', r2', q1, q5, Bool.true_eq_false, Bool.false_eq_true,
    iff_true, iff_false, true_iff, false_iff, true_implies, false_implies, and_true, true_and, not_true_eq_false,
    not_false_eq_true, IsEmpty.forall_iff, if_true, if_false, ite_true, ite_false] <;> omega

/-- The target's concrete case, for transferFrom: a self-transfer of 1 at the maximal balance with an
infinite allowance succeeds and leaves the balance at `2 ^ 256 - 1`. -/
theorem transferFrom_self_max (st : Nat → Nat) (hst : ∀ k, st k < 2 ^ 256) (frm : Nat)
    (hfa : frm < 2 ^ 160)
    (h : HashScopeNested.Scoped (HashScopeNested.transferFromFootprint caller frm frm))
    (hb : st (balanceSlot frm) = 2 ^ 256 - 1) (ha : st (allowanceSlot frm caller) = umax) :
    (transferFromResult st frm frm 1).success = true ∧
      (transferFromResult st frm frm 1).storage (balanceSlot frm) = 2 ^ 256 - 1 := by
  have := transferFrom_self st hst frm 1 hfa h
  have hs : (transferFromResult st frm frm 1).success = true := this.1.2 ⟨.inl ha, by omega⟩
  exact ⟨hs, (this.2 hs).trans hb⟩

/-- The target's other concrete case: a self-transfer above the balance reverts. -/
theorem transferFrom_self_short (st : Nat → Nat) (hst : ∀ k, st k < 2 ^ 256) (frm value : Nat)
    (hfa : frm < 2 ^ 160)
    (h : HashScopeNested.Scoped (HashScopeNested.transferFromFootprint caller frm frm))
    (hlt : st (balanceSlot frm) < value) :
    (transferFromResult st frm frm value).success = false := by
  have := (transferFrom_self st hst frm value hfa h).1
  cases hr : (transferFromResult st frm frm value).success
  · rfl
  · exact absurd (this.1 hr).2 (by omega)

/-- info: 'SolidCore.Spec.UniswapV2.ERC20.Nested.transferFrom_meets' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms transferFrom_meets

end SolidCore.Spec.UniswapV2.ERC20.Nested


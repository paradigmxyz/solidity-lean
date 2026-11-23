import Contracts.UniswapV2.ERC20.Slice.Post
import Verify.Spec.HashScopeFrame

/-!
# transfer's target postcondition frames storage by address

\`TargetPost\` (Post.lean) frames the storage of a successful \`transfer(to, v)\` by slot: every slot
other than \`balKey caller\` and \`balKey to\` keeps its value. \`targetPost_frame\` turns that into the
frame by address, from the finite premise \`KeccakSep (erc20Preimages 1 2 A)\` of
Verify/Spec/HashScopeFinite.lean (UniswapV2ERC20's layout: \`balanceOf\` at slot 1, \`allowance\` at
slot 2) for a finite set \`A\` of addresses holding the caller and the recipient: \`balanceOf[k]\` is
unchanged for every \`k ∈ A\` other than the caller and the recipient, and \`allowance[o][p]\` for every
\`o, p ∈ A\` (\`transfer_frame\`, Verify/Spec/HashScopeFrame.lean).

\`real_erc20_caller_AB\` discharges the premise at the real keccak256 for \`A = {caller, addrA, addrB}\`
by one kernel evaluation, so \`targetPost_frame_real\` holds with no hash premise for a transfer to
any of the three.
-/

namespace SolidCore.Spec.UniswapV2.ERC20.Slice

open SolarTV SolidCore.Refinement SolidCore.Refinement.Generic SolidCore.Spec TrustedBase

/-- **TargetPost's slot frame is an address-level frame on \`A\`**: on a successful
\`transfer(dst, v)\` with the caller and \`dst\` in \`A\`, every other balance of \`A\` and every allowance
of \`A\` is unchanged. -/
theorem targetPost_frame {call : Call} {obs : Observable} (hp : TargetPost call obs)
    {σ : List (Nat × Nat)} {dst v : Nat} (hc : call = transferCall σ dst v) (hdst : dst < 2 ^ 160)
    (hv : v < 2 ^ 256) (hok : obs.success = true) {A : Finset Nat}
    (h : KeccakSep (erc20Preimages balanceSlot 2 A)) (hA : ∀ x ∈ A, x < 2 ^ 160)
    (hcA : caller ∈ A) (hdA : dst ∈ A) :
    (∀ k ∈ A, k ≠ caller → k ≠ dst → obs.storage (balKey k) = slotValue σ (balKey k)) ∧
      ∀ o ∈ A, ∀ p ∈ A,
        obs.storage (solHash p (solHash o 2)) = slotValue σ (solHash p (solHash o 2)) :=
  transfer_frame h hA (by decide) hcA hdA ((hp σ dst v hc hdst hv).2.2.1 hok).2.2

/-! ## The premise at the real keccak256 for the caller and two addresses -/

/-- The preimages of \`erc20Preimages b a\` of a list's addresses, as a list. -/
def erc20List (b a : Nat) (L : List Nat) : List (List Nat) :=
  L.map (fun k => mappingPreimage k b) ++ L.map (fun o => mappingPreimage o a) ++
    L.flatMap fun o => L.map fun p => mappingPreimage p (keccakWord (mappingPreimage o a))

theorem erc20Preimages_sub_list (b a : Nat) (L : List Nat) :
    erc20Preimages b a L.toFinset ⊆ (erc20List b a L).toFinset := by
  intro x hx
  simp only [erc20Preimages, balancePreimages, allowancePreimages, Finset.mem_union,
    Finset.mem_image, Finset.mem_product, List.mem_toFinset] at hx
  rw [List.mem_toFinset]
  simp only [erc20List, List.mem_append, List.mem_map, List.mem_flatMap]
  rcases hx with (⟨k, hk, rfl⟩ | ⟨o, ho, rfl⟩ | ⟨⟨o, p⟩, ⟨ho, hp⟩, rfl⟩)
  · exact .inl (.inl ⟨k, hk, rfl⟩)
  · exact .inl (.inr ⟨o, ho, rfl⟩)
  · exact .inr ⟨o, ho, p, hp, rfl⟩

/-- The interface's caller and the two addresses \`addrA\`, \`addrB\` of HashScopeCheck.lean. -/
def addrsCallerAB : List Nat := [caller, addrA, addrB]

set_option maxRecDepth 100000 in
/-- The check at the real keccak256 on the 15 preimages: one kernel evaluation. -/
theorem real_erc20List_callerAB : ScopedSep (erc20List 1 2 addrsCallerAB) :=
  scopedSep_of_check (by decide +kernel)

/-- **The premise holds at the real keccak256 for the caller, \`addrA\` and \`addrB\`.** -/
theorem real_erc20_callerAB : KeccakSep (erc20Preimages 1 2 addrsCallerAB.toFinset) :=
  ((keccakSep_toFinset_iff _).2 real_erc20List_callerAB).mono (erc20Preimages_sub_list _ _ _)

/-- **With no hash premise**: a successful \`transfer(dst, v)\` to the caller, \`addrA\` or \`addrB\` leaves
the balance of each of the three other than the caller and \`dst\`, and every allowance among them. -/
theorem targetPost_frame_real {call : Call} {obs : Observable} (hp : TargetPost call obs)
    {σ : List (Nat × Nat)} {dst v : Nat} (hc : call = transferCall σ dst v)
    (hv : v < 2 ^ 256) (hok : obs.success = true) (hdA : dst ∈ addrsCallerAB.toFinset) :
    (∀ k ∈ addrsCallerAB.toFinset, k ≠ caller → k ≠ dst →
        obs.storage (balKey k) = slotValue σ (balKey k)) ∧
      ∀ o ∈ addrsCallerAB.toFinset, ∀ p ∈ addrsCallerAB.toFinset,
        obs.storage (solHash p (solHash o 2)) = slotValue σ (solHash p (solHash o 2)) := by
  have hA : ∀ x ∈ addrsCallerAB.toFinset, x < 2 ^ 160 := by decide
  exact targetPost_frame hp hc (hA dst hdA) hv hok real_erc20_callerAB hA (by decide) hdA

/-- Negative control: \`targetPost_frame_real\` does not frame the caller's own balance, nor a key
outside the three (\`addrC\`): both applications fail to elaborate. -/
theorem targetPost_frame_rejects {call : Call} {obs : Observable} (hp : TargetPost call obs)
    {σ : List (Nat × Nat)} {v : Nat} (hc : call = transferCall σ addrA v) (hv : v < 2 ^ 256)
    (hok : obs.success = true) : True := by
  have hf := targetPost_frame_real hp hc hv hok (by decide)
  have _hB : obs.storage (balKey addrB) = slotValue σ (balKey addrB) :=
    hf.1 addrB (by decide) (by decide) (by decide)
  fail_if_success
    have _hcaller : obs.storage (balKey caller) = slotValue σ (balKey caller) :=
      hf.1 caller (by decide) (by decide) (by decide)
  fail_if_success
    have _hC : obs.storage (balKey addrC) = slotValue σ (balKey addrC) :=
      hf.1 addrC (by decide) (by decide) (by decide)
  trivial

/-! ## Axiom checks -/

/-- info: 'SolidCore.Spec.UniswapV2.ERC20.Slice.targetPost_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms targetPost_frame

/-- info: 'SolidCore.Spec.UniswapV2.ERC20.Slice.real_erc20List_callerAB' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms real_erc20List_callerAB

/-- info: 'SolidCore.Spec.UniswapV2.ERC20.Slice.real_erc20_callerAB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms real_erc20_callerAB

/-- info: 'SolidCore.Spec.UniswapV2.ERC20.Slice.targetPost_frame_real' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms targetPost_frame_real

/-- info: 'SolidCore.Spec.UniswapV2.ERC20.Slice.targetPost_frame_rejects' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms targetPost_frame_rejects

end SolidCore.Spec.UniswapV2.ERC20.Slice

import Contracts.UniswapV2.ERC20.Slice.Post
import Verify.Spec.HashScopeFrame

/-!
# transfer's target postcondition frames storage by address

`TargetPost` (Post.lean) frames the storage of a successful `transfer(to, v)` by slot: every slot
other than `balKey caller` and `balKey to` keeps its value. `targetPost_frame` turns that into the
frame by address, from the finite premise `KeccakSep (erc20Preimages 1 2 A)` of
Verify/Spec/HashScopeFinite.lean (UniswapV2ERC20's layout: `balanceOf` at slot 1, `allowance` at
slot 2) for a finite set `A` of addresses holding the caller and the recipient: `balanceOf[k]` is
unchanged for every `k ∈ A` other than the caller and the recipient, and `allowance[o][p]` for every
`o, p ∈ A` (`transfer_frame`, Verify/Spec/HashScopeFrame.lean).

`real_erc20_caller_AB` discharges the premise at the real keccak256 for `A = {caller, addrA, addrB}`
by one kernel evaluation per image, so `targetPost_frame_real` holds with no hash premise for a transfer to
any of the three.
-/

namespace SolidCore.Spec.UniswapV2.ERC20.Slice

open SolarTV SolidCore.Refinement SolidCore.Refinement.Generic SolidCore.Spec TrustedBase

/-- **TargetPost's slot frame is an address-level frame on `A`**: on a successful
`transfer(dst, v)` with the caller and `dst` in `A`, every other balance of `A` and every allowance
of `A` is unchanged. -/
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

/-- The preimages of `erc20Preimages b a` of a list's addresses, as a list. -/
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

/-- The interface's caller and the two addresses `addrA`, `addrB` of HashScopeCheck.lean. -/
def addrsCallerAB : List Nat := [caller, addrA, addrB]

set_option maxRecDepth 100000 in
theorem callerAB_img0 : keccakWord (mappingPreimage caller 1) = 0x38da9dc9759c46bd12ce677a753bb966a85f8995667f5aade8c3f5d0f1de587a := by decide +kernel

set_option maxRecDepth 100000 in
theorem callerAB_img1 : keccakWord (mappingPreimage addrA 1) = 0x36306db541fd1551fd93a60031e8a8c89d69ddef41d6249f5fdc265dbc8fffa2 := by decide +kernel

set_option maxRecDepth 100000 in
theorem callerAB_img2 : keccakWord (mappingPreimage addrB 1) = 0x9d4d959825f0680278e64197773b2a50cd78b2b2cb00711ddbeebf0bf93cd8a4 := by decide +kernel

set_option maxRecDepth 100000 in
theorem callerAB_img3 : keccakWord (mappingPreimage caller 2) = 0xc6743832a665c7cded03ad0214a691a21f9dd133a4844aff4db630c4c0e76d8f := by decide +kernel

set_option maxRecDepth 100000 in
theorem callerAB_img4 : keccakWord (mappingPreimage addrA 2) = 0xb314f101a00aa0d8cc6704cc6dd1e9dd7551ec98c9df52079c192c560ba66c4a := by decide +kernel

set_option maxRecDepth 100000 in
theorem callerAB_img5 : keccakWord (mappingPreimage addrB 2) = 0xf4c32baaad9a468f8a07690e6d59a45329a58ffaa2080ee4ccc1c4e2d7249e78 := by decide +kernel

set_option maxRecDepth 100000 in
theorem callerAB_img6 : keccakWord (mappingPreimage caller 0xc6743832a665c7cded03ad0214a691a21f9dd133a4844aff4db630c4c0e76d8f) = 0x72e47a8afa9b32ddec6112c2723ca59e7bf0ae176b0c691271e152d70cf5e6cd := by decide +kernel

set_option maxRecDepth 100000 in
theorem callerAB_img7 : keccakWord (mappingPreimage addrA 0xc6743832a665c7cded03ad0214a691a21f9dd133a4844aff4db630c4c0e76d8f) = 0x7d3a74a3fc0a611fd71e4dc6df7b56f55212b1f2ce16c1bd4ef2271f8a0aff0c := by decide +kernel

set_option maxRecDepth 100000 in
theorem callerAB_img8 : keccakWord (mappingPreimage addrB 0xc6743832a665c7cded03ad0214a691a21f9dd133a4844aff4db630c4c0e76d8f) = 0xcafa5432185c93d05594605b9be2d65d1ba5e47b37d566e4f31ee909a259f7e7 := by decide +kernel

set_option maxRecDepth 100000 in
theorem callerAB_img9 : keccakWord (mappingPreimage caller 0xb314f101a00aa0d8cc6704cc6dd1e9dd7551ec98c9df52079c192c560ba66c4a) = 0x9bdc4e64e6f0f064558ced04f6cf7b7f28902092b08a5e0f4fef83533c62ba01 := by decide +kernel

set_option maxRecDepth 100000 in
theorem callerAB_img10 : keccakWord (mappingPreimage addrA 0xb314f101a00aa0d8cc6704cc6dd1e9dd7551ec98c9df52079c192c560ba66c4a) = 0x4d80218e38ec5632663a8b57acdbbb6111d57e5231395495d10e4c9e7e529334 := by decide +kernel

set_option maxRecDepth 100000 in
theorem callerAB_img11 : keccakWord (mappingPreimage addrB 0xb314f101a00aa0d8cc6704cc6dd1e9dd7551ec98c9df52079c192c560ba66c4a) = 0x02d293aa0902765963fe96dce827cc61b41302193196975dfc5b7d8991325423 := by decide +kernel

set_option maxRecDepth 100000 in
theorem callerAB_img12 : keccakWord (mappingPreimage caller 0xf4c32baaad9a468f8a07690e6d59a45329a58ffaa2080ee4ccc1c4e2d7249e78) = 0x0dc98a0f0bfb252b87b2ae500df3f27e0075094bf8ce28514b1491c9a36cfb38 := by decide +kernel

set_option maxRecDepth 100000 in
theorem callerAB_img13 : keccakWord (mappingPreimage addrA 0xf4c32baaad9a468f8a07690e6d59a45329a58ffaa2080ee4ccc1c4e2d7249e78) = 0xbdf360ab9ff96112ffaa40da9615e11321c938316664145a7d0c3a3b8a374a06 := by decide +kernel

set_option maxRecDepth 100000 in
theorem callerAB_img14 : keccakWord (mappingPreimage addrB 0xf4c32baaad9a468f8a07690e6d59a45329a58ffaa2080ee4ccc1c4e2d7249e78) = 0xc2a81cd7ce1c533337814ea18730f6fabf93e8a00760325295ca851fd6fec141 := by decide +kernel

/-- The 15 preimages separated at the real keccak256, from one kernel evaluation per image. -/
theorem real_erc20List_callerAB : ScopedSep (erc20List 1 2 addrsCallerAB) :=
  keccakSeparated_of_images (H := [0x38da9dc9759c46bd12ce677a753bb966a85f8995667f5aade8c3f5d0f1de587a, 0x36306db541fd1551fd93a60031e8a8c89d69ddef41d6249f5fdc265dbc8fffa2, 0x9d4d959825f0680278e64197773b2a50cd78b2b2cb00711ddbeebf0bf93cd8a4, 0xc6743832a665c7cded03ad0214a691a21f9dd133a4844aff4db630c4c0e76d8f, 0xb314f101a00aa0d8cc6704cc6dd1e9dd7551ec98c9df52079c192c560ba66c4a, 0xf4c32baaad9a468f8a07690e6d59a45329a58ffaa2080ee4ccc1c4e2d7249e78, 0x72e47a8afa9b32ddec6112c2723ca59e7bf0ae176b0c691271e152d70cf5e6cd, 0x7d3a74a3fc0a611fd71e4dc6df7b56f55212b1f2ce16c1bd4ef2271f8a0aff0c, 0xcafa5432185c93d05594605b9be2d65d1ba5e47b37d566e4f31ee909a259f7e7, 0x9bdc4e64e6f0f064558ced04f6cf7b7f28902092b08a5e0f4fef83533c62ba01, 0x4d80218e38ec5632663a8b57acdbbb6111d57e5231395495d10e4c9e7e529334, 0x02d293aa0902765963fe96dce827cc61b41302193196975dfc5b7d8991325423, 0x0dc98a0f0bfb252b87b2ae500df3f27e0075094bf8ce28514b1491c9a36cfb38, 0xbdf360ab9ff96112ffaa40da9615e11321c938316664145a7d0c3a3b8a374a06, 0xc2a81cd7ce1c533337814ea18730f6fabf93e8a00760325295ca851fd6fec141])
    (by simp only [erc20List, addrsCallerAB, List.map_cons, List.map_nil, List.flatMap_cons,
      List.flatMap_nil, List.cons_append, List.nil_append, List.append_nil, callerAB_img0, callerAB_img1, callerAB_img2, callerAB_img3, callerAB_img4, callerAB_img5, callerAB_img6, callerAB_img7, callerAB_img8, callerAB_img9, callerAB_img10, callerAB_img11, callerAB_img12, callerAB_img13, callerAB_img14])
    (by decide) (by decide)

/-- **The premise holds at the real keccak256 for the caller, `addrA` and `addrB`.** -/
theorem real_erc20_callerAB : KeccakSep (erc20Preimages 1 2 addrsCallerAB.toFinset) :=
  ((keccakSep_toFinset_iff _).2 real_erc20List_callerAB).mono (erc20Preimages_sub_list _ _ _)

/-- **With no hash premise**: a successful `transfer(dst, v)` to the caller, `addrA` or `addrB` leaves
the balance of each of the three other than the caller and `dst`, and every allowance among them. -/
theorem targetPost_frame_real {call : Call} {obs : Observable} (hp : TargetPost call obs)
    {σ : List (Nat × Nat)} {dst v : Nat} (hc : call = transferCall σ dst v)
    (hv : v < 2 ^ 256) (hok : obs.success = true) (hdA : dst ∈ addrsCallerAB.toFinset) :
    (∀ k ∈ addrsCallerAB.toFinset, k ≠ caller → k ≠ dst →
        obs.storage (balKey k) = slotValue σ (balKey k)) ∧
      ∀ o ∈ addrsCallerAB.toFinset, ∀ p ∈ addrsCallerAB.toFinset,
        obs.storage (solHash p (solHash o 2)) = slotValue σ (solHash p (solHash o 2)) := by
  have hA : ∀ x ∈ addrsCallerAB.toFinset, x < 2 ^ 160 := by decide
  exact targetPost_frame hp hc (hA dst hdA) hv hok real_erc20_callerAB hA (by decide) hdA

/-- Negative control: `targetPost_frame_real` does not frame the caller's own balance, nor a key
outside the three (`addrC`): both applications fail to elaborate. -/
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

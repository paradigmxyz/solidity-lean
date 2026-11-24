import Verify.Spec.HashScopeCheck

/-!
# The footprint premise over a finite set of accounts

Verify/Spec/HashScopeCheck.lean keeps two forms of the keccak256 premise of an ERC20: the per-call
`ScopedSep` of the preimages one call hashes, and the universal `UniversalTransferSep`, which
`universalTransferSep_iff` shows is keccak256 separation on all `2 ^ 160` balance preimages. The
universal form is not assumed anywhere: it is a claim about `2 ^ 160` hashes into `2 ^ 256` words, and
over allowances (`2 ^ 320` nested preimages) pigeonhole refutes it (`not_nestedSlotsSeparated`).

This file states the premise in between: **`KeccakSep S`**, keccak256 injective with images at least
`2 ^ 128` on a finite set `S` of preimages, and takes for `S` the preimages an ERC20 hashes for a
finite set `A` of addresses (`erc20Preimages b a A`, with balances at slot `b` and allowances at
slot `a`):

* `balanceOf[k]` for `k ∈ A`: the preimage `k . b`;
* `allowance[o][s]` for `o, s ∈ A`: the outer preimage `o . a` and the inner one
  `s . keccak256(o . a)`, the inner key computed by keccak256 itself.

From the one hypothesis `KeccakSep (erc20Preimages b a A)`:

* `transfer_sep`, `transferFrom_sep`, `approve_sep`: the per-call premise of every `transfer`,
  `transferFrom` and `approve` among addresses of `A`, equal addresses included (`c = t`: the
  self-transfer, whose footprint names one preimage twice);
* `transfer_slots_of_keccakSep`, `transferFrom_slots_of_keccakSep`: the slot facts the ERC20 proofs
  consume (`transfer_slots`, `transferFrom_slots`) for every such pair;
* `scopedSep_transfer_iff_pair`: the existing two-preimage premise
  `ScopedSep (transferFootprint b c t)` is exactly `KeccakSep` of the balance preimages of
  `A = {c, t}`, so nothing about the old premise is weakened or replaced;
* `keccakSep_balance_of_universal`: the universal form implies the finite one for every `A`, by
  `universalTransferSep_iff`; the converse is not claimed.

**The bound.** `KeccakSep (erc20Preimages b a A)` is a premise about small sets of accounts only: it is
false once `A` has more than `2 ^ 128` addresses (`not_keccakSep_large`), since the `A.card ^ 2` inner
allowance preimages would need pairwise distinct images below `2 ^ 256`. Like `ScopedSep` it has no
`apart` clause, so it says nothing about addresses outside `A`.

`real_erc20_ABC` is the hypothesis for three addresses at the real keccak256, by one kernel
evaluation of the check. `missing_preimage_not_sep`, `missing_preimage_no_lift` and
`missing_preimage_rejected` are the negative controls: a set missing a footprint preimage does not
give that footprint's premise.
-/

namespace SolidCore.Spec

open SolidCore.Refinement SolidCore.Refinement.Generic TrustedBase

/-! ## The premise on a finite set -/

/-- **keccak256 separated on the finite set `S` of preimages**: injective on `S`, and every image of
`S` at least `2 ^ 128`. -/
def KeccakSep (S : Finset (List Nat)) : Prop := KeccakSeparated (· ∈ S)

theorem KeccakSep.mono {S T : Finset (List Nat)} (h : KeccakSep T) (hST : S ⊆ T) : KeccakSep S :=
  KeccakSeparated.mono h fun _ hx => hST hx

/-- On a list's elements it is the per-call premise. -/
theorem keccakSep_toFinset_iff (L : List (List Nat)) : KeccakSep L.toFinset ↔ ScopedSep L := by
  simp only [KeccakSep, ScopedSep, List.mem_toFinset]

/-- `KeccakSep S` is the per-call premise of the list of `S`'s elements. -/
theorem keccakSep_iff_toList (S : Finset (List Nat)) : KeccakSep S ↔ ScopedSep S.toList := by
  simp only [KeccakSep, ScopedSep, Finset.mem_toList]

/-- **A footprint inside `S` is separated when `S` is** (`SeparatedBy.mono` at keccak256). -/
theorem scopedSep_of_keccakSep {S : Finset (List Nat)} {L : List (List Nat)} (h : KeccakSep S)
    (hL : ∀ x ∈ L, x ∈ S) : ScopedSep L :=
  (scopedSep_iff L).2 <| ((scopedSep_iff _).1 ((keccakSep_iff_toList S).1 h)).mono
    fun x hx => Finset.mem_toList.2 (hL x hx)

/-! ## The preimages an ERC20 hashes for the addresses `A` -/

/-- `balanceOf[k]` for `k ∈ A`, the mapping at slot `b`. -/
def balancePreimages (b : Nat) (A : Finset Nat) : Finset (List Nat) :=
  A.image fun k => mappingPreimage k b

/-- `allowance[o][s]` for `o, s ∈ A`, the mapping at slot `a`: the outer preimages `o . a` and the
inner preimages `s . keccak256(o . a)`. -/
def allowancePreimages (a : Nat) (A : Finset Nat) : Finset (List Nat) :=
  A.image (fun o => mappingPreimage o a) ∪
    (A ×ˢ A).image fun p => mappingPreimage p.2 (keccakWord (mappingPreimage p.1 a))

/-- **Every preimage an ERC20 with balances at slot `b` and allowances at slot `a` hashes for the
addresses `A`.** -/
def erc20Preimages (b a : Nat) (A : Finset Nat) : Finset (List Nat) :=
  balancePreimages b A ∪ allowancePreimages a A

theorem balance_mem {b a : Nat} {A : Finset Nat} {k : Nat} (hk : k ∈ A) :
    mappingPreimage k b ∈ erc20Preimages b a A :=
  Finset.mem_union_left _ (Finset.mem_image_of_mem (fun k => mappingPreimage k b) hk)

theorem outer_mem {b a : Nat} {A : Finset Nat} {o : Nat} (ho : o ∈ A) :
    mappingPreimage o a ∈ erc20Preimages b a A :=
  Finset.mem_union_right _ (Finset.mem_union_left _
    (Finset.mem_image_of_mem (fun o => mappingPreimage o a) ho))

theorem inner_mem {b a : Nat} {A : Finset Nat} {o s : Nat} (ho : o ∈ A) (hs : s ∈ A) :
    mappingPreimage s (keccakWord (mappingPreimage o a)) ∈ erc20Preimages b a A :=
  Finset.mem_union_right _ (Finset.mem_union_right _
    (Finset.mem_image_of_mem
      (fun p : Nat × Nat => mappingPreimage p.2 (keccakWord (mappingPreimage p.1 a)))
      (show (o, s) ∈ A ×ˢ A from Finset.mem_product.2 ⟨ho, hs⟩)))

/-! ## Every call among the addresses of `A` -/

/-- **`transfer` from `c` to `t`**, for every `c, t ∈ A`, `c = t` included. -/
theorem transfer_sep {b a : Nat} {A : Finset Nat} (h : KeccakSep (erc20Preimages b a A)) {c t : Nat}
    (hc : c ∈ A) (ht : t ∈ A) : ScopedSep (transferFootprint b c t) :=
  scopedSep_of_keccakSep h fun x hx => by
    simp only [transferFootprint, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact balance_mem hc
    · exact balance_mem ht

/-- `transfer` from the balance preimages alone, for a token with no allowance mapping. -/
theorem transfer_sep_balance {b : Nat} {A : Finset Nat} (h : KeccakSep (balancePreimages b A))
    {c t : Nat} (hc : c ∈ A) (ht : t ∈ A) : ScopedSep (transferFootprint b c t) :=
  scopedSep_of_keccakSep h fun x hx => by
    simp only [transferFootprint, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact Finset.mem_image_of_mem (fun k => mappingPreimage k b) hc
    · exact Finset.mem_image_of_mem (fun k => mappingPreimage k b) ht

/-- The self-transfer: `transfer` from `c` to `c`. -/
theorem self_transfer_sep {b a : Nat} {A : Finset Nat} (h : KeccakSep (erc20Preimages b a A))
    {c : Nat} (hc : c ∈ A) : ScopedSep (transferFootprint b c c) :=
  transfer_sep h hc hc

/-- **`approve(s, v)` sent by `c`**, for every `c, s ∈ A`. -/
theorem approve_sep {b a : Nat} {A : Finset Nat} (h : KeccakSep (erc20Preimages b a A)) {c s : Nat}
    (hc : c ∈ A) (hs : s ∈ A) : ScopedSep (approveFootprint a c s) :=
  scopedSep_of_keccakSep h fun x hx => by
    simp only [approveFootprintBy, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact outer_mem hc
    · exact inner_mem hc hs

/-- **`transferFrom(f, t, v)` sent by `c`**, for every `f, t, c ∈ A`, equal addresses included. -/
theorem transferFrom_sep {b a : Nat} {A : Finset Nat} (h : KeccakSep (erc20Preimages b a A))
    {f t c : Nat} (hf : f ∈ A) (ht : t ∈ A) (hc : c ∈ A) :
    ScopedSep (transferFromFootprint b a f t c) :=
  scopedSep_of_keccakSep h fun x hx => by
    simp only [transferFromFootprintBy, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact balance_mem hf
    · exact balance_mem ht
    · exact outer_mem hf
    · exact inner_mem hf hc

/-- **All of `A`'s calls at once**: every `transfer`, `approve` and `transferFrom` among `A`. -/
theorem erc20_sep {b a : Nat} {A : Finset Nat} (h : KeccakSep (erc20Preimages b a A)) :
    ∀ c ∈ A, ∀ t ∈ A, ScopedSep (transferFootprint b c t) ∧ ScopedSep (approveFootprint a c t) ∧
      ∀ s ∈ A, ScopedSep (transferFromFootprint b a c t s) :=
  fun _ hc _ ht => ⟨transfer_sep h hc ht, approve_sep h hc ht, fun _ hs => transferFrom_sep h hc ht hs⟩

/-! ## The slot facts the ERC20 proofs consume -/

/-- **transfer's slots for every pair of `A`**: distinct for distinct addresses, both at least
`2 ^ 128`. For `c = t` the first conjunct is vacuous and the two slots are one slot. -/
theorem transfer_slots_of_keccakSep {b a : Nat} {A : Finset Nat}
    (h : KeccakSep (erc20Preimages b a A)) (hA : ∀ x ∈ A, x < 2 ^ 160) (hb : b < 2 ^ 256)
    {c t : Nat} (hc : c ∈ A) (ht : t ∈ A) :
    (c ≠ t → solHash c b ≠ solHash t b) ∧ 2 ^ 128 ≤ solHash c b ∧ 2 ^ 128 ≤ solHash t b :=
  transfer_slots (transfer_sep h hc ht) hb (lt_trans (hA c hc) (by decide))
    (lt_trans (hA t ht) (by decide))

/-- **transferFrom's slots for every triple of `A`** (`transferFrom_slots`): the balance slots
distinct for `f ≠ t`, the allowance slot apart from both, all at least `2 ^ 128`. -/
theorem transferFrom_slots_of_keccakSep {b a : Nat} {A : Finset Nat}
    (h : KeccakSep (erc20Preimages b a A)) (hA : ∀ x ∈ A, x < 2 ^ 160) (hb : b < 2 ^ 128)
    (ha : a < 2 ^ 256) {f t c : Nat} (hf : f ∈ A) (ht : t ∈ A) (hc : c ∈ A) :
    (f ≠ t → solHash f b ≠ solHash t b) ∧ solHash c (solHash f a) ≠ solHash f b ∧
      solHash c (solHash f a) ≠ solHash t b ∧ 2 ^ 128 ≤ solHash f b ∧ 2 ^ 128 ≤ solHash t b ∧
      2 ^ 128 ≤ solHash c (solHash f a) :=
  transferFrom_slots (transferFrom_sep h hf ht hc) hb ha (lt_trans (hA f hf) (by decide))
    (lt_trans (hA t ht) (by decide)) (lt_trans (hA c hc) (by decide))

/-! ## The existing premises as instances -/

theorem balancePreimages_pair (b c t : Nat) :
    balancePreimages b {c, t} = (transferFootprint b c t).toFinset := by
  ext x
  simp only [balancePreimages, transferFootprint, Finset.mem_image, Finset.mem_insert,
    Finset.mem_singleton, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false]
  constructor
  · rintro ⟨k, rfl | rfl, rfl⟩
    · exact .inl rfl
    · exact .inr rfl
  · rintro (rfl | rfl)
    · exact ⟨c, .inl rfl, rfl⟩
    · exact ⟨t, .inr rfl, rfl⟩

/-- **The two-preimage premise is the instance `A = {c, t}`**: `ScopedSep (transferFootprint b c t)`
is `KeccakSep` of the balance preimages of `{c, t}`, exactly. -/
theorem scopedSep_transfer_iff_pair (b c t : Nat) :
    ScopedSep (transferFootprint b c t) ↔ KeccakSep (balancePreimages b {c, t}) := by
  rw [balancePreimages_pair, keccakSep_toFinset_iff]

/-- The full ERC20 set of `{c, t}` gives it too. -/
theorem scopedSep_transfer_of_pair {b a c t : Nat} (h : KeccakSep (erc20Preimages b a {c, t})) :
    ScopedSep (transferFootprint b c t) :=
  transfer_sep h (Finset.mem_insert_self _ _) (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))

/-- **The universal balance premise gives the finite one for every set of real addresses**
(`universalTransferSep_iff`). Only this direction: the finite premise is the weaker one. -/
theorem keccakSep_balance_of_universal {m : Nat} (hu : UniversalTransferSep m) {A : Finset Nat}
    (hA : ∀ x ∈ A, x < 2 ^ 160) : KeccakSep (balancePreimages m A) :=
  ((universalTransferSep_iff m).1 hu).mono fun x hx => by
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hx
    exact ⟨k, hA k hk, rfl⟩

/-! ## A real witness: three addresses at keccak256

UniswapV2ERC20's layout: `balanceOf` at slot 1, `allowance` at slot 2. -/

/-- The three addresses of HashScopeCheck.lean. -/
def addrsABC : Finset Nat := {addrA, addrB, addrC}

/-- The 15 preimages of `erc20Preimages 1 2 addrsABC` as a list: 3 balances, 3 outer and 9 inner
allowance preimages. -/
def erc20ListABC : List (List Nat) :=
  [addrA, addrB, addrC].map (fun k => mappingPreimage k 1) ++
    [addrA, addrB, addrC].map (fun o => mappingPreimage o 2) ++
    [addrA, addrB, addrC].flatMap fun o =>
      [addrA, addrB, addrC].map fun s => mappingPreimage s (keccakWord (mappingPreimage o 2))

theorem erc20Preimages_ABC_sub : erc20Preimages 1 2 addrsABC ⊆ erc20ListABC.toFinset := by
  intro x hx
  simp only [erc20Preimages, balancePreimages, allowancePreimages, Finset.mem_union,
    Finset.mem_image, Finset.mem_product] at hx
  rw [List.mem_toFinset]
  simp only [erc20ListABC, List.mem_append, List.mem_map, List.mem_flatMap]
  have hl : ∀ {k}, k ∈ addrsABC → k ∈ [addrA, addrB, addrC] := fun hk => by
    simp only [addrsABC, Finset.mem_insert, Finset.mem_singleton] at hk
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    exact hk
  rcases hx with (⟨k, hk, rfl⟩ | ⟨o, ho, rfl⟩ | ⟨⟨o, s⟩, ⟨ho, hs⟩, rfl⟩)
  · exact .inl (.inl ⟨k, hl hk, rfl⟩)
  · exact .inl (.inr ⟨o, hl ho, rfl⟩)
  · exact .inr ⟨o, hl ho, s, hl hs, rfl⟩

/-! The 15 images at the real keccak256, one kernel evaluation each (the inner preimages over the
literal outer images), so that no single evaluation holds every sponge at once. -/

set_option maxRecDepth 100000 in
theorem erc20ABC_img0 : keccakWord (mappingPreimage addrA 1) = 0x36306db541fd1551fd93a60031e8a8c89d69ddef41d6249f5fdc265dbc8fffa2 := by decide +kernel

set_option maxRecDepth 100000 in
theorem erc20ABC_img1 : keccakWord (mappingPreimage addrB 1) = 0x9d4d959825f0680278e64197773b2a50cd78b2b2cb00711ddbeebf0bf93cd8a4 := by decide +kernel

set_option maxRecDepth 100000 in
theorem erc20ABC_img2 : keccakWord (mappingPreimage addrC 1) = 0xe20f19dc6931eb9e42fe3f21abe1a9ef59942d8e586871d88564d0d0b63a5e5c := by decide +kernel

set_option maxRecDepth 100000 in
theorem erc20ABC_img3 : keccakWord (mappingPreimage addrA 2) = 0xb314f101a00aa0d8cc6704cc6dd1e9dd7551ec98c9df52079c192c560ba66c4a := by decide +kernel

set_option maxRecDepth 100000 in
theorem erc20ABC_img4 : keccakWord (mappingPreimage addrB 2) = 0xf4c32baaad9a468f8a07690e6d59a45329a58ffaa2080ee4ccc1c4e2d7249e78 := by decide +kernel

set_option maxRecDepth 100000 in
theorem erc20ABC_img5 : keccakWord (mappingPreimage addrC 2) = 0x6e3256c0d903d06dbf1594b7c30afa1a58a0e687f0a0df1b6b6358c60bd3e992 := by decide +kernel

set_option maxRecDepth 100000 in
theorem erc20ABC_img6 : keccakWord (mappingPreimage addrA 0xb314f101a00aa0d8cc6704cc6dd1e9dd7551ec98c9df52079c192c560ba66c4a) = 0x4d80218e38ec5632663a8b57acdbbb6111d57e5231395495d10e4c9e7e529334 := by decide +kernel

set_option maxRecDepth 100000 in
theorem erc20ABC_img7 : keccakWord (mappingPreimage addrB 0xb314f101a00aa0d8cc6704cc6dd1e9dd7551ec98c9df52079c192c560ba66c4a) = 0x2d293aa0902765963fe96dce827cc61b41302193196975dfc5b7d8991325423 := by decide +kernel

set_option maxRecDepth 100000 in
theorem erc20ABC_img8 : keccakWord (mappingPreimage addrC 0xb314f101a00aa0d8cc6704cc6dd1e9dd7551ec98c9df52079c192c560ba66c4a) = 0xccaeb10c53a10a2a5ba805c46b8e54cbc5a26b1c9268c2acc63e6f5ef9e92c97 := by decide +kernel

set_option maxRecDepth 100000 in
theorem erc20ABC_img9 : keccakWord (mappingPreimage addrA 0xf4c32baaad9a468f8a07690e6d59a45329a58ffaa2080ee4ccc1c4e2d7249e78) = 0xbdf360ab9ff96112ffaa40da9615e11321c938316664145a7d0c3a3b8a374a06 := by decide +kernel

set_option maxRecDepth 100000 in
theorem erc20ABC_img10 : keccakWord (mappingPreimage addrB 0xf4c32baaad9a468f8a07690e6d59a45329a58ffaa2080ee4ccc1c4e2d7249e78) = 0xc2a81cd7ce1c533337814ea18730f6fabf93e8a00760325295ca851fd6fec141 := by decide +kernel

set_option maxRecDepth 100000 in
theorem erc20ABC_img11 : keccakWord (mappingPreimage addrC 0xf4c32baaad9a468f8a07690e6d59a45329a58ffaa2080ee4ccc1c4e2d7249e78) = 0xc8f1f724c956a81e9f6b3de8de9b9bede7fd2d227ba0376ad8aa72f8dec362a3 := by decide +kernel

set_option maxRecDepth 100000 in
theorem erc20ABC_img12 : keccakWord (mappingPreimage addrA 0x6e3256c0d903d06dbf1594b7c30afa1a58a0e687f0a0df1b6b6358c60bd3e992) = 0xa538513e84b1a01d079d4ef4feb8b48c513493ed754b2612d837fd053f7b5762 := by decide +kernel

set_option maxRecDepth 100000 in
theorem erc20ABC_img13 : keccakWord (mappingPreimage addrB 0x6e3256c0d903d06dbf1594b7c30afa1a58a0e687f0a0df1b6b6358c60bd3e992) = 0x5dfa9b312d76cce84d7ae186686faf1bbbc80b4e3b79bbccf3e7150a5d7f164a := by decide +kernel

set_option maxRecDepth 100000 in
theorem erc20ABC_img14 : keccakWord (mappingPreimage addrC 0x6e3256c0d903d06dbf1594b7c30afa1a58a0e687f0a0df1b6b6358c60bd3e992) = 0x98d84cb62c65db7457149706fe353d14a5bd1158d5c81c0def593868cd6b3671 := by decide +kernel

/-- The 15 preimages separated at the real keccak256, from their images. -/
theorem real_erc20ListABC : ScopedSep erc20ListABC :=
  keccakSeparated_of_images (H := [0x36306db541fd1551fd93a60031e8a8c89d69ddef41d6249f5fdc265dbc8fffa2, 0x9d4d959825f0680278e64197773b2a50cd78b2b2cb00711ddbeebf0bf93cd8a4, 0xe20f19dc6931eb9e42fe3f21abe1a9ef59942d8e586871d88564d0d0b63a5e5c, 0xb314f101a00aa0d8cc6704cc6dd1e9dd7551ec98c9df52079c192c560ba66c4a, 0xf4c32baaad9a468f8a07690e6d59a45329a58ffaa2080ee4ccc1c4e2d7249e78, 0x6e3256c0d903d06dbf1594b7c30afa1a58a0e687f0a0df1b6b6358c60bd3e992, 0x4d80218e38ec5632663a8b57acdbbb6111d57e5231395495d10e4c9e7e529334, 0x2d293aa0902765963fe96dce827cc61b41302193196975dfc5b7d8991325423, 0xccaeb10c53a10a2a5ba805c46b8e54cbc5a26b1c9268c2acc63e6f5ef9e92c97, 0xbdf360ab9ff96112ffaa40da9615e11321c938316664145a7d0c3a3b8a374a06, 0xc2a81cd7ce1c533337814ea18730f6fabf93e8a00760325295ca851fd6fec141, 0xc8f1f724c956a81e9f6b3de8de9b9bede7fd2d227ba0376ad8aa72f8dec362a3, 0xa538513e84b1a01d079d4ef4feb8b48c513493ed754b2612d837fd053f7b5762, 0x5dfa9b312d76cce84d7ae186686faf1bbbc80b4e3b79bbccf3e7150a5d7f164a, 0x98d84cb62c65db7457149706fe353d14a5bd1158d5c81c0def593868cd6b3671])
    (by simp only [erc20ListABC, List.map_cons, List.map_nil, List.flatMap_cons,
      List.flatMap_nil, List.cons_append, List.nil_append, List.append_nil, erc20ABC_img0, erc20ABC_img1, erc20ABC_img2, erc20ABC_img3, erc20ABC_img4, erc20ABC_img5, erc20ABC_img6, erc20ABC_img7, erc20ABC_img8, erc20ABC_img9, erc20ABC_img10, erc20ABC_img11, erc20ABC_img12, erc20ABC_img13, erc20ABC_img14])
    (by decide) (by decide)

/-- **The hypothesis holds for the three addresses at the real keccak256.** -/
theorem real_erc20_ABC : KeccakSep (erc20Preimages 1 2 addrsABC) :=
  ((keccakSep_toFinset_iff _).2 real_erc20ListABC).mono erc20Preimages_ABC_sub

/-- Every `transfer`, `approve` and `transferFrom` among the three addresses, from the witness. -/
theorem real_erc20_ABC_calls :
    ∀ c ∈ addrsABC, ∀ t ∈ addrsABC, ScopedSep (transferFootprint 1 c t) ∧
      ScopedSep (approveFootprint 2 c t) ∧
      ∀ s ∈ addrsABC, ScopedSep (transferFromFootprint 1 2 c t s) :=
  erc20_sep real_erc20_ABC

/-! ## The bound: no separation for more than `2 ^ 128` accounts -/

/-- keccak256 of a mapping preimage is a word. -/
theorem keccakWord_mappingPreimage_lt (k s : Nat) : keccakWord (mappingPreimage k s) < 2 ^ 256 := by
  have e : solHash k s = keccakWord (mappingPreimage k s) := solHash_eq k s
  have := solHash_lt k s
  unfold Generic.wordSize at this
  omega

/-- **The finite premise is false for every set of more than `2 ^ 128` word-sized addresses**: under it
the inner allowance preimages of `A ×ˢ A` have pairwise distinct images, `A.card ^ 2 > 2 ^ 256` of
them, all below `2 ^ 256`. -/
theorem not_keccakSep_large {b a : Nat} {A : Finset Nat} (ha : a < 2 ^ 256)
    (hA : ∀ x ∈ A, x < 2 ^ 256) (hcard : 2 ^ 128 < A.card) : ¬ KeccakSep (erc20Preimages b a A) := by
  intro h
  let f : Nat × Nat → Nat :=
    fun p => keccakWord (mappingPreimage p.2 (keccakWord (mappingPreimage p.1 a)))
  have hinj : Set.InjOn f ↑(A ×ˢ A) := by
    rintro ⟨o, s⟩ hp ⟨o', s'⟩ hp' he
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe] at hp hp'
    have e1 := h.1 _ _ (inner_mem hp.1 hp.2) (inner_mem hp'.1 hp'.2) he
    obtain ⟨hs, hk⟩ := mappingPreimage_inj (hA s hp.2) (hA s' hp'.2)
      (keccakWord_mappingPreimage_lt o a) (keccakWord_mappingPreimage_lt o' a) e1
    have e2 := h.1 _ _ (outer_mem hp.1) (outer_mem hp'.1) hk
    obtain ⟨ho, -⟩ := mappingPreimage_inj (hA o hp.1) (hA o' hp'.1) ha ha e2
    simp [ho, hs]
  have hmaps : Set.MapsTo f ↑(A ×ˢ A) ↑(Finset.range (2 ^ 256)) := by
    intro p _
    simp only [Finset.coe_range, Set.mem_Iio]
    exact keccakWord_mappingPreimage_lt _ _
  have hle := Finset.card_le_card_of_injOn f hmaps hinj
  rw [Finset.card_product, Finset.card_range] at hle
  have h2 : 2 ^ 128 * 2 ^ 128 < A.card * A.card := Nat.mul_lt_mul'' hcard hcard
  have h3 : (2 : Nat) ^ 128 * 2 ^ 128 = 2 ^ 256 := by norm_num
  omega

/-- So some finite set of real addresses refutes it: the first `2 ^ 128 + 1`. -/
theorem not_keccakSep_range {b a : Nat} (ha : a < 2 ^ 256) :
    ¬ KeccakSep (erc20Preimages b a (Finset.range (2 ^ 128 + 1))) :=
  not_keccakSep_large ha (fun x hx => by simp at hx; omega) (by simp)

/-! ## Negative controls: a set missing a preimage -/

/-- **A set missing a footprint preimage does not give that footprint's premise**: the hash that
sends everything to `2 ^ 128` separates the balance preimage of `addrA` alone, and not the footprint
of `transfer` from `addrA` to `addrB`, which also names `addrB`'s. -/
theorem missing_preimage_not_sep :
    SeparatedBy (fun _ => 2 ^ 128) [mappingPreimage addrA 1] ∧
      ¬ SeparatedBy (fun _ => 2 ^ 128) (transferFootprint 1 addrA addrB) := by
  refine ⟨(separatedBy_iff_check _ _).2 (by decide +kernel), fun h => ?_⟩
  have h' := (separatedBy_iff_check _ _).1 h
  revert h'
  decide +kernel

/-- So no argument from the separation of a set to a footprint can skip the membership of each of
the footprint's preimages. -/
theorem missing_preimage_no_lift :
    ¬ ∀ h : List Nat → Nat, SeparatedBy h [mappingPreimage addrA 1] →
      SeparatedBy h (transferFootprint 1 addrA addrB) :=
  fun hl => missing_preimage_not_sep.2 (hl _ missing_preimage_not_sep.1)

/-- `transfer_sep` refuses a recipient outside `A`: from the premise of `A = {addrA}`, the
self-transfer of `addrA` elaborates and the transfer from `addrA` to `addrB` does not (its side
condition `addrB ∈ {addrA}` is false); `fail_if_success` makes this file build only while it is
refused. -/
theorem missing_preimage_rejected (h : KeccakSep (erc20Preimages 1 2 {addrA})) : True := by
  have _hself : ScopedSep (transferFootprint 1 addrA addrA) :=
    transfer_sep h (by decide) (by decide)
  fail_if_success
    have _hAB : ScopedSep (transferFootprint 1 addrA addrB) :=
      transfer_sep h (by decide) (by decide)
  trivial

/-! ## Axiom checks -/

/-- info: 'SolidCore.Spec.scopedSep_of_keccakSep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms scopedSep_of_keccakSep

/-- info: 'SolidCore.Spec.transfer_sep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms transfer_sep

/-- info: 'SolidCore.Spec.self_transfer_sep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms self_transfer_sep

/-- info: 'SolidCore.Spec.approve_sep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms approve_sep

/-- info: 'SolidCore.Spec.transferFrom_sep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms transferFrom_sep

/-- info: 'SolidCore.Spec.erc20_sep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms erc20_sep

/-- info: 'SolidCore.Spec.transfer_slots_of_keccakSep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms transfer_slots_of_keccakSep

/-- info: 'SolidCore.Spec.transferFrom_slots_of_keccakSep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms transferFrom_slots_of_keccakSep

/-- info: 'SolidCore.Spec.scopedSep_transfer_iff_pair' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms scopedSep_transfer_iff_pair

/-- info: 'SolidCore.Spec.scopedSep_transfer_of_pair' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms scopedSep_transfer_of_pair

/-- info: 'SolidCore.Spec.keccakSep_balance_of_universal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms keccakSep_balance_of_universal

/-- info: 'SolidCore.Spec.real_erc20ListABC' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms real_erc20ListABC

/-- info: 'SolidCore.Spec.real_erc20_ABC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms real_erc20_ABC

/-- info: 'SolidCore.Spec.real_erc20_ABC_calls' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms real_erc20_ABC_calls

/-- info: 'SolidCore.Spec.missing_preimage_not_sep' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms missing_preimage_not_sep

/-- info: 'SolidCore.Spec.missing_preimage_no_lift' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms missing_preimage_no_lift

/-- info: 'SolidCore.Spec.missing_preimage_rejected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms missing_preimage_rejected

/-- info: 'SolidCore.Spec.KeccakSep.mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms KeccakSep.mono

/-- info: 'SolidCore.Spec.keccakSep_toFinset_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms keccakSep_toFinset_iff

/-- info: 'SolidCore.Spec.keccakSep_iff_toList' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms keccakSep_iff_toList

/-- info: 'SolidCore.Spec.balance_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms balance_mem

/-- info: 'SolidCore.Spec.outer_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms outer_mem

/-- info: 'SolidCore.Spec.inner_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms inner_mem

/-- info: 'SolidCore.Spec.transfer_sep_balance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms transfer_sep_balance

/-- info: 'SolidCore.Spec.balancePreimages_pair' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms balancePreimages_pair

/-- info: 'SolidCore.Spec.erc20Preimages_ABC_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms erc20Preimages_ABC_sub

/-- info: 'SolidCore.Spec.not_keccakSep_large' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms not_keccakSep_large

/-- info: 'SolidCore.Spec.not_keccakSep_range' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms not_keccakSep_range

end SolidCore.Spec

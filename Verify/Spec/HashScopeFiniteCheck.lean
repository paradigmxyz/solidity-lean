import Verify.Spec.HashScopeFinite

/-!
# The finite ERC20 premise: a kernel checker, and a model for every finite set

Verify/Spec/HashScopeFinite.lean states the premise `KeccakSep (erc20Preimages b a A)` of an ERC20
(balances at slot `b`, allowances at slot `a`) over a finite set `A` of addresses. This file adds:

1. **A checker** (`erc20SepCheck b a As`): it lists the `n + n + n ^ 2` preimages of
   `erc20Preimages b a As.toFinset` (`erc20ListBy`) and decides separation on them (`sepCheckBy`,
   Verify/Spec/HashScopeCheck.lean). `erc20SepCheck_iff` shows it is exactly the premise, so for any
   concrete address list the premise is one kernel evaluation:
   `erc20SepCheck_sound (by decide +kernel)` (`real_erc20_A_check`). The kernel keeps about 0.4 GB
   per sponge within a declaration, so past a few sponges each image is its own declaration and
   `erc20Sep_of_images` checks the numbers (`imagesCheck`): `Witness5.premise` is the premise for
   five addresses at the real keccak256, 35 sponges.
2. **A model for every finite set** (`erc20_model`): for every finite `A` with fewer than `2 ^ 64`
   addresses some word-valued hash `h` separates `erc20PreimagesBy h b a A`, the preimages with the
   inner allowance keys computed by `h` itself. So no argument about an abstract hash refutes the
   premise for any such `A`. This is a statement about a model hash, not about keccak256. Some
   bound on `A` is needed: past `2 ^ 128` addresses the inner preimages alone outnumber the
   `2 ^ 256` words (`not_keccakSep_large`). Between `2 ^ 64` and `2 ^ 128` neither result applies.
3. **Negative controls**: the checker refuses a constant hash and a truncated one; a hash that
   passes the checker for `[addrA]` need not separate the transfer from `addrA` to `addrB`; and
   `erc20SepCheck_sound` on a list without `addrB` does not give a transfer to `addrB`.
-/

namespace SolidCore.Spec

open SolidCore.Refinement SolidCore.Refinement.Generic TrustedBase

/-! ## The preimages for any hash -/

/-- `allowance[o][s]` for `o, s ∈ A` at slot `a`, the inner key computed by the hash `h`. -/
def allowancePreimagesBy (h : List Nat → Nat) (a : Nat) (A : Finset Nat) : Finset (List Nat) :=
  A.image (fun o => mappingPreimage o a) ∪
    (A ×ˢ A).image fun p => mappingPreimage p.2 (h (mappingPreimage p.1 a))

/-- **The preimages an ERC20 hashes for `A`, the inner allowance keys computed by `h`.** -/
def erc20PreimagesBy (h : List Nat → Nat) (b a : Nat) (A : Finset Nat) : Finset (List Nat) :=
  balancePreimages b A ∪ allowancePreimagesBy h a A

/-- At keccak256 they are `erc20Preimages`. -/
theorem erc20Preimages_eq_by (b a : Nat) (A : Finset Nat) :
    erc20Preimages b a A = erc20PreimagesBy keccakWord b a A := rfl

/-- The preimages depend on `h` only through its values on the outer preimages `o . a`, `o ∈ A`. -/
theorem erc20PreimagesBy_congr {h h' : List Nat → Nat} {b a : Nat} {A : Finset Nat}
    (he : ∀ o ∈ A, h (mappingPreimage o a) = h' (mappingPreimage o a)) :
    erc20PreimagesBy h b a A = erc20PreimagesBy h' b a A := by
  unfold erc20PreimagesBy allowancePreimagesBy
  congr 2
  apply Finset.image_congr
  rintro ⟨o, s⟩ hp
  simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe] at hp
  simp only [he o hp.1]

/-- The same preimages as a list, for the address list `As`: `n` balances, `n` outer and `n ^ 2`
inner allowance preimages. -/
def erc20ListBy (h : List Nat → Nat) (b a : Nat) (As : List Nat) : List (List Nat) :=
  As.map (fun k => mappingPreimage k b) ++ As.map (fun o => mappingPreimage o a) ++
    As.flatMap fun o => As.map fun s => mappingPreimage s (h (mappingPreimage o a))

theorem erc20ListBy_toFinset (h : List Nat → Nat) (b a : Nat) (As : List Nat) :
    (erc20ListBy h b a As).toFinset = erc20PreimagesBy h b a As.toFinset := by
  ext x
  simp only [erc20ListBy, erc20PreimagesBy, balancePreimages, allowancePreimagesBy,
    List.mem_toFinset, List.mem_append, List.mem_map, List.mem_flatMap, Finset.mem_union,
    Finset.mem_image, Finset.mem_product, Prod.exists]
  constructor
  · rintro ((⟨k, hk, rfl⟩ | ⟨o, ho, rfl⟩) | ⟨o, ho, s, hs, rfl⟩)
    · exact .inl ⟨k, hk, rfl⟩
    · exact .inr (.inl ⟨o, ho, rfl⟩)
    · exact .inr (.inr ⟨o, s, ⟨ho, hs⟩, rfl⟩)
  · rintro (⟨k, hk, rfl⟩ | ⟨o, ho, rfl⟩ | ⟨o, s, ⟨ho, hs⟩, rfl⟩)
    · exact .inl (.inl ⟨k, hk, rfl⟩)
    · exact .inl (.inr ⟨o, ho, rfl⟩)
    · exact .inr ⟨o, ho, s, hs, rfl⟩

/-! ## The checker -/

/-- The check at the hash `h`: separation of the `n + n + n ^ 2` preimages of `erc20ListBy h`. -/
def erc20SepCheckBy (h : List Nat → Nat) (b a : Nat) (As : List Nat) : Bool :=
  sepCheckBy h (erc20ListBy h b a As)

/-- **The checker at keccak256**, for the address list `As`. -/
def erc20SepCheck (b a : Nat) (As : List Nat) : Bool := erc20SepCheckBy keccakWord b a As

/-- At any hash the check is separation of its preimages, the inner keys computed by that hash. -/
theorem erc20SepCheckBy_iff (h : List Nat → Nat) (b a : Nat) (As : List Nat) :
    erc20SepCheckBy h b a As = true ↔
      SeparatedBy h (erc20PreimagesBy h b a As.toFinset).toList := by
  rw [erc20SepCheckBy, ← separatedBy_iff_check, ← erc20ListBy_toFinset]
  simp only [SeparatedBy, Finset.mem_toList, List.mem_toFinset]

/-- **The checker decides the premise**: `erc20SepCheck b a As = true` is exactly
`KeccakSep (erc20Preimages b a As.toFinset)`. -/
theorem erc20SepCheck_iff (b a : Nat) (As : List Nat) :
    erc20SepCheck b a As = true ↔ KeccakSep (erc20Preimages b a As.toFinset) := by
  rw [erc20SepCheck, erc20SepCheckBy, ← scopedSep_iff_check, ← keccakSep_toFinset_iff,
    erc20ListBy_toFinset, erc20Preimages_eq_by]

/-- **Soundness**: one evaluation of the checker is the premise for the addresses of `As`. -/
theorem erc20SepCheck_sound {b a : Nat} {As : List Nat} (h : erc20SepCheck b a As = true) :
    KeccakSep (erc20Preimages b a As.toFinset) :=
  (erc20SepCheck_iff b a As).1 h

/-- Completeness: the premise makes the checker evaluate to `true`. -/
theorem erc20SepCheck_complete {b a : Nat} {As : List Nat}
    (h : KeccakSep (erc20Preimages b a As.toFinset)) : erc20SepCheck b a As = true :=
  (erc20SepCheck_iff b a As).2 h

/-! ## A model for every finite set of addresses -/

/-- **Every finite set of fewer than `2 ^ 64` addresses has a word-valued model**: some `h` below
`2 ^ 256` separates the ERC20 preimages of `A`, the inner allowance keys computed by `h` itself.

`h` is chosen in two steps. First `h₀` numbers the outer preimages `o . a`, which fixes the inner
preimages `s . h₀(o . a)` and so the whole set `S = erc20PreimagesBy h₀ b a A`. Then `h` numbers
the list of the outer preimages followed by `S`'s elements: it agrees with `h₀` on the outer
preimages (`List.idxOf_append_of_mem`), so `erc20PreimagesBy h b a A = S`
(`erc20PreimagesBy_congr`), and it is injective on `S` with images from `2 ^ 128`. A model hash,
not keccak256. -/
theorem erc20_model (b a : Nat) (A : Finset Nat) (hA : A.card < 2 ^ 64) :
    ∃ h : List Nat → Nat, (∀ x, h x < 2 ^ 256) ∧
      SeparatedBy h (erc20PreimagesBy h b a A).toList := by
  let Lo := A.toList.map fun o => mappingPreimage o a
  let h₀ : List Nat → Nat := fun x => 2 ^ 128 + Lo.idxOf x
  let S := erc20PreimagesBy h₀ b a A
  let L := Lo ++ S.toList
  let h : List Nat → Nat := fun x => 2 ^ 128 + L.idxOf x
  have hagree : ∀ o ∈ A, h (mappingPreimage o a) = h₀ (mappingPreimage o a) := fun o ho => by
    have hm : mappingPreimage o a ∈ Lo :=
      List.mem_map_of_mem (f := fun o => mappingPreimage o a) (Finset.mem_toList.2 ho)
    show 2 ^ 128 + (Lo ++ S.toList).idxOf _ = 2 ^ 128 + Lo.idxOf _
    rw [List.idxOf_append_of_mem hm]
  have hS : erc20PreimagesBy h b a A = S := erc20PreimagesBy_congr hagree
  refine ⟨h, fun x => ?_, ?_⟩
  · have hS1 : S.card ≤ A.card + (A.card + A.card * A.card) := by
      refine (Finset.card_union_le _ _).trans (Nat.add_le_add Finset.card_image_le ?_)
      refine (Finset.card_union_le _ _).trans (Nat.add_le_add Finset.card_image_le ?_)
      exact Finset.card_image_le.trans (Finset.card_product A A).le
    have hlen : L.length = A.card + S.card := by
      simp only [L, Lo, List.length_append, List.length_map, Finset.length_toList]
    have hsq : A.card * A.card < 2 ^ 64 * 2 ^ 64 := Nat.mul_lt_mul'' hA hA
    have hidx : L.idxOf x ≤ L.length := List.idxOf_le_length
    show 2 ^ 128 + L.idxOf x < 2 ^ 256
    generalize A.card * A.card = m at hS1 hsq
    omega
  · rw [hS]
    exact (separatedBy_idxOf L).mono fun x hx => List.mem_append_right _ hx

/-! ## A check on the images, for witnesses split into declarations

The kernel keeps every intermediate value of a declaration's evaluation, about 0.4 GB per sponge,
so one evaluation of `erc20SepCheck` is practical for a few sponges only. For more addresses each
image is its own declaration (`keccakWord p = v` by `decide +kernel`), and the check runs on the
numbers: `imagesCheck`, distinct and at least `2 ^ 128`. -/

/-- The images are pairwise distinct and each at least `2 ^ 128`. -/
def imagesCheck : List Nat → Bool
  | [] => true
  | v :: vs => decide (2 ^ 128 ≤ v) && !(vs.contains v) && imagesCheck vs

theorem imagesCheck_spec : ∀ {H : List Nat}, imagesCheck H = true → H.Nodup ∧ ∀ v ∈ H, 2 ^ 128 ≤ v
  | [], _ => ⟨List.nodup_nil, fun _ hv => absurd hv List.not_mem_nil⟩
  | v :: vs, h => by
    simp only [imagesCheck, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at h
    obtain ⟨⟨hv, hn⟩, hr⟩ := h
    have hn : v ∉ vs := by simpa using hn
    have ih := imagesCheck_spec hr
    refine ⟨List.nodup_cons.2 ⟨hn, ih.1⟩, fun w hw => ?_⟩
    rcases List.mem_cons.1 hw with rfl | hw
    · exact hv
    · exact ih.2 w hw

/-- **Separation from the images**: if the images of `L` are the list `H` and `H` passes
`imagesCheck`, keccak256 is separated on `L`. -/
theorem scopedSep_of_images {L : List (List Nat)} {H : List Nat} (hH : L.map keccakWord = H)
    (hc : imagesCheck H = true) : ScopedSep L :=
  keccakSeparated_of_images hH (imagesCheck_spec hc).1 (imagesCheck_spec hc).2

/-- **The ERC20 premise from the images** of `erc20ListBy keccakWord b a As`. -/
theorem erc20Sep_of_images {b a : Nat} {As : List Nat} {H : List Nat}
    (hH : (erc20ListBy keccakWord b a As).map keccakWord = H) (hc : imagesCheck H = true) :
    KeccakSep (erc20Preimages b a As.toFinset) := by
  rw [erc20Preimages_eq_by, ← erc20ListBy_toFinset, keccakSep_toFinset_iff]
  exact scopedSep_of_images hH hc

/-- `imagesCheck` refuses a repeated image. -/
theorem imagesCheck_refuses_repeat : imagesCheck [2 ^ 128, 2 ^ 128 + 1, 2 ^ 128] = false := by
  decide +kernel

/-- `imagesCheck` refuses a small image. -/
theorem imagesCheck_refuses_small : imagesCheck [2 ^ 128, 7] = false := by decide +kernel

/-! ## A real witness at keccak256: one evaluation of the checker

UniswapV2ERC20's layout: `balanceOf` at slot 1, `allowance` at slot 2. One address: its balance,
outer and inner allowance preimages, four sponges in one evaluation. -/

set_option maxRecDepth 100000 in
/-- The premise for `[addrA]` at the real keccak256, by one kernel evaluation of the checker. -/
theorem real_erc20_A_check : KeccakSep (erc20Preimages 1 2 [addrA].toFinset) :=
  erc20SepCheck_sound (by decide +kernel)

/-! ## A real witness for five addresses, one sponge per declaration

Five 160-bit addresses, `balanceOf` at slot 1 and `allowance` at slot 2: 35 preimages, 35 sponges,
each image its own `decide +kernel`, then one `imagesCheck` evaluation (`erc20Sep_of_images`).
scripts/verify/keccak/finite_check.sh writes the same declarations for any address list. -/

namespace Witness5

/-- The 5 addresses. -/
def addrs5 : List Nat :=
  [0xde4bf8ed54bbd167495522b71b48a7e37b0d933, 0xae2f402b5bb9a32b5306f9ceb578f30e46ad5719,
   0xc0152f12bc5c339eaf36577e92516be86f21ada6, 0x89eab022759da6e2b6de1ae9ca74cda234270e18,
   0x526912b8747089b4a642280e3d90d36464ee5f2]

set_option maxRecDepth 100000 in
theorem bal0 :
    keccakWord (mappingPreimage 0xde4bf8ed54bbd167495522b71b48a7e37b0d933
      0x1) =
    0x8eac5b2cb809e708ff8eaa5b24fe9c9d9b263380c66448d3b8aae7b40a932ee7 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem bal1 :
    keccakWord (mappingPreimage 0xae2f402b5bb9a32b5306f9ceb578f30e46ad5719
      0x1) =
    0x3f7112a71c026575e6f3196a6f57dfc4a134d44bd92937dd3dee16c7c5b4651 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem bal2 :
    keccakWord (mappingPreimage 0xc0152f12bc5c339eaf36577e92516be86f21ada6
      0x1) =
    0x5b312a24984f14c623157a301064f1a90b830fd9fdd83bac2cd67cb229ad8b28 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem bal3 :
    keccakWord (mappingPreimage 0x89eab022759da6e2b6de1ae9ca74cda234270e18
      0x1) =
    0xbf3c83bff723392d0c741afe42c061fadd024b5ece95ac41b89c95ed0870a179 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem bal4 :
    keccakWord (mappingPreimage 0x526912b8747089b4a642280e3d90d36464ee5f2
      0x1) =
    0xc6e1a03a375de08aa6de0db6d144958a2a17fe3d8cd4b0677d4b9ce26dde3adc := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem out0 :
    keccakWord (mappingPreimage 0xde4bf8ed54bbd167495522b71b48a7e37b0d933
      0x2) =
    0x48aa258cec0c4ca9504806ac87125f58ecc80823369eac945aca7631a87ccf3e := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem out1 :
    keccakWord (mappingPreimage 0xae2f402b5bb9a32b5306f9ceb578f30e46ad5719
      0x2) =
    0x86a72f3391688af10d5a18f018c9215c05a1eb387298074f16bd7bf82c45ae26 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem out2 :
    keccakWord (mappingPreimage 0xc0152f12bc5c339eaf36577e92516be86f21ada6
      0x2) =
    0x7c20708a2e756d2455891da29b8223bdb27a320c6253f1af3c47b844d2d968fd := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem out3 :
    keccakWord (mappingPreimage 0x89eab022759da6e2b6de1ae9ca74cda234270e18
      0x2) =
    0x2ea2f99cace6f1aeac4b0321606eb2df0181e121619136ed3c2021882d801ac := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem out4 :
    keccakWord (mappingPreimage 0x526912b8747089b4a642280e3d90d36464ee5f2
      0x2) =
    0x605b7cf7ba8d286703f4682ae2493d6efb9b9fd54acd83a1a9e186bde8520b77 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem inn0_0 :
    keccakWord (mappingPreimage 0xde4bf8ed54bbd167495522b71b48a7e37b0d933
      0x48aa258cec0c4ca9504806ac87125f58ecc80823369eac945aca7631a87ccf3e) =
    0x508e477c3fcfbb01422d53ad19c2f7f1ad4c1865f4aaec8a20f04351fa2eec02 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem inn0_1 :
    keccakWord (mappingPreimage 0xae2f402b5bb9a32b5306f9ceb578f30e46ad5719
      0x48aa258cec0c4ca9504806ac87125f58ecc80823369eac945aca7631a87ccf3e) =
    0xbc9e9575d6f0a3ed6ae34728810d481c2267237de74e85848ad3fb868b5100bc := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem inn0_2 :
    keccakWord (mappingPreimage 0xc0152f12bc5c339eaf36577e92516be86f21ada6
      0x48aa258cec0c4ca9504806ac87125f58ecc80823369eac945aca7631a87ccf3e) =
    0x271c01af55b55bc01a09d4afb520ce2a2f7a805c24abd7d75b74873d0de2dd41 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem inn0_3 :
    keccakWord (mappingPreimage 0x89eab022759da6e2b6de1ae9ca74cda234270e18
      0x48aa258cec0c4ca9504806ac87125f58ecc80823369eac945aca7631a87ccf3e) =
    0x9e30e821f665e3d933dee87b5de2c4a10dbc157275181a0ce0f42d75df8243a3 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem inn0_4 :
    keccakWord (mappingPreimage 0x526912b8747089b4a642280e3d90d36464ee5f2
      0x48aa258cec0c4ca9504806ac87125f58ecc80823369eac945aca7631a87ccf3e) =
    0xd9569541cbe9fca35c6c2347fd3c00a0afbc5ac8db537d0525e4056140e6339e := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem inn1_0 :
    keccakWord (mappingPreimage 0xde4bf8ed54bbd167495522b71b48a7e37b0d933
      0x86a72f3391688af10d5a18f018c9215c05a1eb387298074f16bd7bf82c45ae26) =
    0xd3bc88915822d174d08374872da9d87334fe64c2657027c9211c221d48260ddc := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem inn1_1 :
    keccakWord (mappingPreimage 0xae2f402b5bb9a32b5306f9ceb578f30e46ad5719
      0x86a72f3391688af10d5a18f018c9215c05a1eb387298074f16bd7bf82c45ae26) =
    0xc0094e3ad52edddc9edacf3c9e26042bc7589ca5ddafc7cc9d1c75f64405d3bc := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem inn1_2 :
    keccakWord (mappingPreimage 0xc0152f12bc5c339eaf36577e92516be86f21ada6
      0x86a72f3391688af10d5a18f018c9215c05a1eb387298074f16bd7bf82c45ae26) =
    0xa45ffb8f38e23c4932c656d1eef0e861c07c06f50e1d884085e5331026379f59 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem inn1_3 :
    keccakWord (mappingPreimage 0x89eab022759da6e2b6de1ae9ca74cda234270e18
      0x86a72f3391688af10d5a18f018c9215c05a1eb387298074f16bd7bf82c45ae26) =
    0x2a1e3a5c7309574f8e2d9c178693b5bd1ae72d5990b124916d52522202f92815 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem inn1_4 :
    keccakWord (mappingPreimage 0x526912b8747089b4a642280e3d90d36464ee5f2
      0x86a72f3391688af10d5a18f018c9215c05a1eb387298074f16bd7bf82c45ae26) =
    0xb827c57db5e99da27a92f874990144e239e24ac82a2df965fdcf0ffa8be48c21 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem inn2_0 :
    keccakWord (mappingPreimage 0xde4bf8ed54bbd167495522b71b48a7e37b0d933
      0x7c20708a2e756d2455891da29b8223bdb27a320c6253f1af3c47b844d2d968fd) =
    0xb624c9e07f474ce5c153a60fc3e49c6eeebf03cadd06d045143c810165fd601d := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem inn2_1 :
    keccakWord (mappingPreimage 0xae2f402b5bb9a32b5306f9ceb578f30e46ad5719
      0x7c20708a2e756d2455891da29b8223bdb27a320c6253f1af3c47b844d2d968fd) =
    0xfef42e68435f4c9182255e8283bf09df712a5a005fd922c26ebbccd30d04d4bf := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem inn2_2 :
    keccakWord (mappingPreimage 0xc0152f12bc5c339eaf36577e92516be86f21ada6
      0x7c20708a2e756d2455891da29b8223bdb27a320c6253f1af3c47b844d2d968fd) =
    0x73d1802c7cc43add64b0cac3accf82b19b7e2f187ab2db72f6ca168ddb2128f7 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem inn2_3 :
    keccakWord (mappingPreimage 0x89eab022759da6e2b6de1ae9ca74cda234270e18
      0x7c20708a2e756d2455891da29b8223bdb27a320c6253f1af3c47b844d2d968fd) =
    0x7ff506ffe17cc6646bd2630dc10bb5c70b469572c438f9600060dde4a4ead2 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem inn2_4 :
    keccakWord (mappingPreimage 0x526912b8747089b4a642280e3d90d36464ee5f2
      0x7c20708a2e756d2455891da29b8223bdb27a320c6253f1af3c47b844d2d968fd) =
    0x73fa6172ee1daf921ea2a7eaf4413e5f31b8691b66c18264a99527852a08ce0f := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem inn3_0 :
    keccakWord (mappingPreimage 0xde4bf8ed54bbd167495522b71b48a7e37b0d933
      0x2ea2f99cace6f1aeac4b0321606eb2df0181e121619136ed3c2021882d801ac) =
    0x798f7e2a0c4ac5fdc354d5a681b7692ec7be5b7902322d361cd0ccd30771bc2f := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem inn3_1 :
    keccakWord (mappingPreimage 0xae2f402b5bb9a32b5306f9ceb578f30e46ad5719
      0x2ea2f99cace6f1aeac4b0321606eb2df0181e121619136ed3c2021882d801ac) =
    0x53241619e20bec1331f6cb8147b80991b4f7880ec6c156913aa17a9c7edeefd9 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem inn3_2 :
    keccakWord (mappingPreimage 0xc0152f12bc5c339eaf36577e92516be86f21ada6
      0x2ea2f99cace6f1aeac4b0321606eb2df0181e121619136ed3c2021882d801ac) =
    0x225522e52fa89b057ea72a010e5c1f374905c3fa60923f70b4169b05bb2eb74e := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem inn3_3 :
    keccakWord (mappingPreimage 0x89eab022759da6e2b6de1ae9ca74cda234270e18
      0x2ea2f99cace6f1aeac4b0321606eb2df0181e121619136ed3c2021882d801ac) =
    0x9b7d3629b7fa025f55b625ad7a4e5c0761692ce935dc2dda8a98f34e9971cd1a := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem inn3_4 :
    keccakWord (mappingPreimage 0x526912b8747089b4a642280e3d90d36464ee5f2
      0x2ea2f99cace6f1aeac4b0321606eb2df0181e121619136ed3c2021882d801ac) =
    0xc54abd044bde64a66e4ef13fa4b93a8db71a72534d68596a7b0f6c6b048f2709 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem inn4_0 :
    keccakWord (mappingPreimage 0xde4bf8ed54bbd167495522b71b48a7e37b0d933
      0x605b7cf7ba8d286703f4682ae2493d6efb9b9fd54acd83a1a9e186bde8520b77) =
    0xf18383de65be3fed1b58955cd1d3b369ce965bc32275473bb03db8064c2402e2 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem inn4_1 :
    keccakWord (mappingPreimage 0xae2f402b5bb9a32b5306f9ceb578f30e46ad5719
      0x605b7cf7ba8d286703f4682ae2493d6efb9b9fd54acd83a1a9e186bde8520b77) =
    0xcee4650984dec60ed8ba7ce668960cc94963f25a60a7130c7d37cafbc65c4afe := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem inn4_2 :
    keccakWord (mappingPreimage 0xc0152f12bc5c339eaf36577e92516be86f21ada6
      0x605b7cf7ba8d286703f4682ae2493d6efb9b9fd54acd83a1a9e186bde8520b77) =
    0x4d5790b32375cd9882c2d9bd0d5e38287af28b1e18de9d398d40a2525e39e18f := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem inn4_3 :
    keccakWord (mappingPreimage 0x89eab022759da6e2b6de1ae9ca74cda234270e18
      0x605b7cf7ba8d286703f4682ae2493d6efb9b9fd54acd83a1a9e186bde8520b77) =
    0x8dba70ff02be3856a8c2f1b29cec193780104f593be69b0a688e21cdb04f3b66 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem inn4_4 :
    keccakWord (mappingPreimage 0x526912b8747089b4a642280e3d90d36464ee5f2
      0x605b7cf7ba8d286703f4682ae2493d6efb9b9fd54acd83a1a9e186bde8520b77) =
    0x9ede00946fa4e8a63429e094a02ff6c12cba813e960394bbe148e6a956b580fe := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The images of the 35 preimages, from the declarations above. -/
theorem images : (erc20ListBy keccakWord 1 2 addrs5).map keccakWord =
    [0x8eac5b2cb809e708ff8eaa5b24fe9c9d9b263380c66448d3b8aae7b40a932ee7,
     0x3f7112a71c026575e6f3196a6f57dfc4a134d44bd92937dd3dee16c7c5b4651,
     0x5b312a24984f14c623157a301064f1a90b830fd9fdd83bac2cd67cb229ad8b28,
     0xbf3c83bff723392d0c741afe42c061fadd024b5ece95ac41b89c95ed0870a179,
     0xc6e1a03a375de08aa6de0db6d144958a2a17fe3d8cd4b0677d4b9ce26dde3adc,
     0x48aa258cec0c4ca9504806ac87125f58ecc80823369eac945aca7631a87ccf3e,
     0x86a72f3391688af10d5a18f018c9215c05a1eb387298074f16bd7bf82c45ae26,
     0x7c20708a2e756d2455891da29b8223bdb27a320c6253f1af3c47b844d2d968fd,
     0x2ea2f99cace6f1aeac4b0321606eb2df0181e121619136ed3c2021882d801ac,
     0x605b7cf7ba8d286703f4682ae2493d6efb9b9fd54acd83a1a9e186bde8520b77,
     0x508e477c3fcfbb01422d53ad19c2f7f1ad4c1865f4aaec8a20f04351fa2eec02,
     0xbc9e9575d6f0a3ed6ae34728810d481c2267237de74e85848ad3fb868b5100bc,
     0x271c01af55b55bc01a09d4afb520ce2a2f7a805c24abd7d75b74873d0de2dd41,
     0x9e30e821f665e3d933dee87b5de2c4a10dbc157275181a0ce0f42d75df8243a3,
     0xd9569541cbe9fca35c6c2347fd3c00a0afbc5ac8db537d0525e4056140e6339e,
     0xd3bc88915822d174d08374872da9d87334fe64c2657027c9211c221d48260ddc,
     0xc0094e3ad52edddc9edacf3c9e26042bc7589ca5ddafc7cc9d1c75f64405d3bc,
     0xa45ffb8f38e23c4932c656d1eef0e861c07c06f50e1d884085e5331026379f59,
     0x2a1e3a5c7309574f8e2d9c178693b5bd1ae72d5990b124916d52522202f92815,
     0xb827c57db5e99da27a92f874990144e239e24ac82a2df965fdcf0ffa8be48c21,
     0xb624c9e07f474ce5c153a60fc3e49c6eeebf03cadd06d045143c810165fd601d,
     0xfef42e68435f4c9182255e8283bf09df712a5a005fd922c26ebbccd30d04d4bf,
     0x73d1802c7cc43add64b0cac3accf82b19b7e2f187ab2db72f6ca168ddb2128f7,
     0x7ff506ffe17cc6646bd2630dc10bb5c70b469572c438f9600060dde4a4ead2,
     0x73fa6172ee1daf921ea2a7eaf4413e5f31b8691b66c18264a99527852a08ce0f,
     0x798f7e2a0c4ac5fdc354d5a681b7692ec7be5b7902322d361cd0ccd30771bc2f,
     0x53241619e20bec1331f6cb8147b80991b4f7880ec6c156913aa17a9c7edeefd9,
     0x225522e52fa89b057ea72a010e5c1f374905c3fa60923f70b4169b05bb2eb74e,
     0x9b7d3629b7fa025f55b625ad7a4e5c0761692ce935dc2dda8a98f34e9971cd1a,
     0xc54abd044bde64a66e4ef13fa4b93a8db71a72534d68596a7b0f6c6b048f2709,
     0xf18383de65be3fed1b58955cd1d3b369ce965bc32275473bb03db8064c2402e2,
     0xcee4650984dec60ed8ba7ce668960cc94963f25a60a7130c7d37cafbc65c4afe,
     0x4d5790b32375cd9882c2d9bd0d5e38287af28b1e18de9d398d40a2525e39e18f,
     0x8dba70ff02be3856a8c2f1b29cec193780104f593be69b0a688e21cdb04f3b66,
     0x9ede00946fa4e8a63429e094a02ff6c12cba813e960394bbe148e6a956b580fe] := by
  simp only [erc20ListBy, addrs5, List.map_cons, List.map_nil, List.flatMap_cons, List.flatMap_nil,
    List.cons_append, List.nil_append, List.append_nil, bal0, bal1, bal2, bal3, bal4, out0, out1,
    out2, out3, out4, inn0_0, inn0_1, inn0_2, inn0_3, inn0_4, inn1_0, inn1_1, inn1_2, inn1_3,
    inn1_4, inn2_0, inn2_1, inn2_2, inn2_3, inn2_4, inn3_0, inn3_1, inn3_2, inn3_3, inn3_4, inn4_0,
    inn4_1, inn4_2, inn4_3, inn4_4]

set_option maxRecDepth 100000 in
/-- **The premise for the 5 addresses at the real keccak256.** -/
theorem premise : KeccakSep (erc20Preimages 1 2 addrs5.toFinset) :=
  erc20Sep_of_images images (by decide +kernel)

end Witness5

/-! ## Negative controls -/

/-- The checker refuses a constant hash on one address's three preimages. -/
theorem erc20Check_refuses_constant : erc20SepCheckBy (fun _ => 2 ^ 128) 1 2 [addrA] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The checker refuses keccak256 truncated to one bit (above `2 ^ 128`): one address has three
distinct preimages, and a one-bit hash collides on two of them. -/
theorem erc20Check_refuses_truncated :
    erc20SepCheckBy (fun x => 2 ^ 128 + keccakWord x % 2) 1 2 [addrA] = false := by
  decide +kernel

/-- A hash that sends `addrB`'s balance preimage onto `addrA`'s. -/
def collideB (x : List Nat) : Nat :=
  if x = mappingPreimage addrB 1 then 2 ^ 128 else
    2 ^ 128 + [mappingPreimage addrA 1, mappingPreimage addrA 2].idxOf x

/-- **The check for `[addrA]` says nothing of `addrB`**: `collideB` passes the checker for the
list `[addrA]` and does not separate the footprint of the transfer from `addrA` to `addrB`. -/
theorem erc20Check_missing_address :
    erc20SepCheckBy collideB 1 2 [addrA] = true ∧
      sepCheckBy collideB (transferFootprint 1 addrA addrB) = false := by
  decide +kernel

/-- So no argument from the check of a list reaches an address outside it. -/
theorem erc20Check_missing_no_lift :
    ¬ ∀ h : List Nat → Nat, erc20SepCheckBy h 1 2 [addrA] = true →
      SeparatedBy h (transferFootprint 1 addrA addrB) := fun hl => by
  have := (separatedBy_iff_check _ _).1 (hl collideB erc20Check_missing_address.1)
  rw [erc20Check_missing_address.2] at this
  exact Bool.false_ne_true this

/-- `erc20SepCheck_sound` on `[addrA]` gives the self-transfer of `addrA` and not the transfer to
`addrB` (its side condition `addrB ∈ [addrA].toFinset` is false): `fail_if_success` makes this file
build only while it is refused. -/
theorem erc20Check_missing_rejected (h : erc20SepCheck 1 2 [addrA] = true) : True := by
  have _hself : ScopedSep (transferFootprint 1 addrA addrA) :=
    transfer_sep (erc20SepCheck_sound h) (by decide) (by decide)
  fail_if_success
    have _hAB : ScopedSep (transferFootprint 1 addrA addrB) :=
      transfer_sep (erc20SepCheck_sound h) (by decide) (by decide)
  trivial

/-! ## Axiom checks -/

/-- info: 'SolidCore.Spec.erc20Preimages_eq_by' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms erc20Preimages_eq_by

/-- info: 'SolidCore.Spec.erc20PreimagesBy_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms erc20PreimagesBy_congr

/-- info: 'SolidCore.Spec.erc20ListBy_toFinset' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms erc20ListBy_toFinset

/-- info: 'SolidCore.Spec.erc20SepCheckBy_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms erc20SepCheckBy_iff

/-- info: 'SolidCore.Spec.erc20SepCheck_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms erc20SepCheck_iff

/-- info: 'SolidCore.Spec.erc20SepCheck_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms erc20SepCheck_sound

/-- info: 'SolidCore.Spec.erc20SepCheck_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms erc20SepCheck_complete

/-- info: 'SolidCore.Spec.erc20_model' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms erc20_model

/-- info: 'SolidCore.Spec.imagesCheck_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms imagesCheck_spec

/-- info: 'SolidCore.Spec.scopedSep_of_images' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms scopedSep_of_images

/-- info: 'SolidCore.Spec.erc20Sep_of_images' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms erc20Sep_of_images

/-- info: 'SolidCore.Spec.imagesCheck_refuses_repeat' depends on axioms: [propext] -/
#guard_msgs in
#print axioms imagesCheck_refuses_repeat

/-- info: 'SolidCore.Spec.imagesCheck_refuses_small' depends on axioms: [propext] -/
#guard_msgs in
#print axioms imagesCheck_refuses_small

/-- info: 'SolidCore.Spec.real_erc20_A_check' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms real_erc20_A_check

/-- info: 'SolidCore.Spec.Witness5.images' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Witness5.images

/-- info: 'SolidCore.Spec.Witness5.premise' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Witness5.premise

/-- info: 'SolidCore.Spec.erc20Check_refuses_constant' depends on axioms: [propext] -/
#guard_msgs in
#print axioms erc20Check_refuses_constant

/-- info: 'SolidCore.Spec.erc20Check_refuses_truncated' depends on axioms: [propext] -/
#guard_msgs in
#print axioms erc20Check_refuses_truncated

/-- info: 'SolidCore.Spec.erc20Check_missing_address' depends on axioms: [propext] -/
#guard_msgs in
#print axioms erc20Check_missing_address

/-- info: 'SolidCore.Spec.erc20Check_missing_no_lift' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms erc20Check_missing_no_lift

/-- info: 'SolidCore.Spec.erc20Check_missing_rejected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms erc20Check_missing_rejected

end SolidCore.Spec

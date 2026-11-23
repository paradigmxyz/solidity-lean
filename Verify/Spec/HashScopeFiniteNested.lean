import Verify.Spec.HashScopeFinite
import Verify.Spec.HashScopeNested

/-!
# The finite premise for nested mappings

Verify/Spec/HashScopeNested.lean states the footprint premise of a call on a nested mapping
`n[o][s]` (`HashScopeNested.Scoped`, keccak256 separated on the list `nestedFootprint n o s` of its
two preimages) and the slot facts a spec consumes from it (`slot_ne`, `nested_ne_flat`, `slot_ge`).
The universal form over all addresses is refuted by pigeonhole (`not_nestedSlotsSeparated`), so it
is never assumed. This file takes the finite premise of Verify/Spec/HashScopeFinite.lean,
`KeccakSep S` (keccak256 injective with images at least `2 ^ 128` on a finite set `S` of
preimages), for the preimages of `n[o][s]` over a finite set `A` of keys:

* `nestedPreimages n A`: the outer preimages `o . n` and the inner preimages
  `s . keccak256(o . n)` for `o, s ∈ A`. It is HashScopeFinite's `allowancePreimages n A`
  (`nestedPreimages_eq_allowancePreimages`) and the union of the footprints `nestedFootprint n o s`
  over `A × A` (`nestedPreimages_eq_footprints`).
* From `KeccakSep (nestedPreimages n A)`: `Scoped (nestedFootprint n o s)` for every `o, s ∈ A`
  (`nested_scoped`), so HashScopeNested's `approveFootprint` for every pair (`nested_approve_scoped`);
  from `KeccakSep (erc20Preimages 1 2 A)` (balances at slot 1, allowances at slot 2, as
  UniswapV2ERC20) its `transferFromFootprint` for every triple (`nested_transferFrom_scoped`).
* The slot facts for every pair of `A`: outer slots apart for distinct keys (`nested_outer_ne`),
  nested slots apart for distinct pairs (`nested_slot_ne`), a nested slot neither an outer slot
  (`nested_ne_outer`) nor a balance slot (`nested_ne_balance`), and every slot at least `2 ^ 128`
  (`nested_slot_ge`, `balance_slot_ge`), each with its bounds as premises.
* `real_nested_tokens`: the premise at the real keccak256 for three token addresses at slot 2, by
  one kernel evaluation of the check on the 12 preimages; `real_nested_ABC`: the same for
  HashScopeFinite's three addresses, from `real_erc20_ABC`.

The negative control `nested_rejected` checks that a key outside `A` is refused.
-/

namespace SolidCore.Spec

open SolidCore.Refinement SolidCore.Refinement.Generic TrustedBase

/-- SolidCore's mapping slot is keccak256 of the preimage. -/
theorem solHash_pre (k m : Nat) : solHash k m = keccakWord (mappingPreimage k m) := solHash_eq k m

/-- A mapping slot is a word. -/
theorem solHash_lt_word (k m : Nat) : solHash k m < 2 ^ 256 := by
  have h := solHash_lt k m
  unfold Generic.wordSize at h
  exact h

/-! ## The preimages of a nested mapping over `A` -/

/-- **The preimages of `n[o][s]` for `o, s ∈ A`**: the outer `o . n` and the inner
`s . keccak256(o . n)`. -/
def nestedPreimages (n : Nat) (A : Finset Nat) : Finset (List Nat) :=
  A.image (fun o => HashScopeNested.pre o n) ∪
    (A ×ˢ A).image fun p => HashScopeNested.pre p.2 (solHash p.1 n)

/-- **They are HashScopeFinite's allowance preimages.** -/
theorem nestedPreimages_eq_allowancePreimages (n : Nat) (A : Finset Nat) :
    nestedPreimages n A = allowancePreimages n A := by
  unfold nestedPreimages allowancePreimages
  simp only [solHash_pre]

theorem nested_outer_mem {n : Nat} {A : Finset Nat} {o : Nat} (ho : o ∈ A) :
    HashScopeNested.pre o n ∈ nestedPreimages n A :=
  Finset.mem_union_left _ (Finset.mem_image_of_mem (fun o => HashScopeNested.pre o n) ho)

theorem nested_inner_mem {n : Nat} {A : Finset Nat} {o s : Nat} (ho : o ∈ A) (hs : s ∈ A) :
    HashScopeNested.pre s (solHash o n) ∈ nestedPreimages n A :=
  Finset.mem_union_right _
    (Finset.mem_image_of_mem (fun p : Nat × Nat => HashScopeNested.pre p.2 (solHash p.1 n))
      (show (o, s) ∈ A ×ˢ A from Finset.mem_product.2 ⟨ho, hs⟩))

/-- **They are the union of the footprints `nestedFootprint n o s` over `A × A`.** -/
theorem nestedPreimages_eq_footprints (n : Nat) (A : Finset Nat) :
    nestedPreimages n A =
      (A ×ˢ A).biUnion fun p => (HashScopeNested.nestedFootprint n p.1 p.2).toFinset := by
  ext x
  simp only [Finset.mem_biUnion, Finset.mem_product, List.mem_toFinset,
    HashScopeNested.nestedFootprint, List.mem_cons, List.not_mem_nil, or_false]
  constructor
  · intro hx
    rcases Finset.mem_union.1 hx with hx | hx
    · obtain ⟨o, ho, rfl⟩ := Finset.mem_image.1 hx
      exact ⟨(o, o), ⟨ho, ho⟩, .inl rfl⟩
    · obtain ⟨⟨o, s⟩, hp, rfl⟩ := Finset.mem_image.1 hx
      exact ⟨(o, s), Finset.mem_product.1 hp, .inr rfl⟩
  · rintro ⟨⟨o, s⟩, ⟨ho, hs⟩, rfl | rfl⟩
    · exact nested_outer_mem ho
    · exact nested_inner_mem ho hs

/-- The nested preimages at slot `a` are among the ERC20 preimages with allowances at `a`. -/
theorem nestedPreimages_sub_erc20 (b a : Nat) (A : Finset Nat) :
    nestedPreimages a A ⊆ erc20Preimages b a A := by
  rw [nestedPreimages_eq_allowancePreimages]
  exact fun _ hx => Finset.mem_union_right _ hx

theorem keccakSep_nested_of_erc20 {b a : Nat} {A : Finset Nat}
    (h : KeccakSep (erc20Preimages b a A)) : KeccakSep (nestedPreimages a A) :=
  h.mono (nestedPreimages_sub_erc20 b a A)

/-- `KeccakSep S` is HashScopeNested's premise on the list of `S`'s elements. -/
theorem scoped_toList {S : Finset (List Nat)} (h : KeccakSep S) : HashScopeNested.Scoped S.toList :=
  (keccakSep_iff_toList S).1 h

/-! ## Every footprint among the keys of `A` -/

/-- **`n[o][s]`'s footprint for every `o, s ∈ A`**, `o = s` included. -/
theorem nested_scoped {n : Nat} {A : Finset Nat} (h : KeccakSep (nestedPreimages n A)) {o s : Nat}
    (ho : o ∈ A) (hs : s ∈ A) : HashScopeNested.Scoped (HashScopeNested.nestedFootprint n o s) :=
  scopedSep_of_keccakSep h fun x hx => by
    simp only [HashScopeNested.nestedFootprint, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact nested_outer_mem ho
    · exact nested_inner_mem ho hs

/-- **UniswapV2ERC20's `approve(spender, v)` from `caller`** (allowance at slot 2), for every
`caller, spender ∈ A`. -/
theorem nested_approve_scoped {A : Finset Nat} (h : KeccakSep (nestedPreimages 2 A))
    {caller spender : Nat} (hc : caller ∈ A) (hs : spender ∈ A) :
    HashScopeNested.Scoped (HashScopeNested.approveFootprint caller spender) :=
  nested_scoped h hc hs

/-- **UniswapV2ERC20's `transferFrom(frm, dst, v)` from `caller`** (balanceOf at slot 1, allowance
at slot 2), for every `caller, frm, dst ∈ A`, equal addresses included. -/
theorem nested_transferFrom_scoped {A : Finset Nat} (h : KeccakSep (erc20Preimages 1 2 A))
    {caller frm dst : Nat} (hc : caller ∈ A) (hf : frm ∈ A) (ht : dst ∈ A) :
    HashScopeNested.Scoped (HashScopeNested.transferFromFootprint caller frm dst) :=
  scopedSep_of_keccakSep h fun x hx => by
    simp only [HashScopeNested.transferFromFootprint, HashScopeNested.nestedFootprint,
      List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact nestedPreimages_sub_erc20 1 2 A (nested_outer_mem hf)
    · exact nestedPreimages_sub_erc20 1 2 A (nested_inner_mem hf hc)
    · exact balance_mem hf
    · exact balance_mem ht

/-- Every `approve` and `transferFrom` among `A` at once. -/
theorem nested_sep {A : Finset Nat} (h : KeccakSep (erc20Preimages 1 2 A)) :
    ∀ c ∈ A, ∀ s ∈ A, HashScopeNested.Scoped (HashScopeNested.approveFootprint c s) ∧
      ∀ t ∈ A, HashScopeNested.Scoped (HashScopeNested.transferFromFootprint c s t) :=
  fun _ hc _ hs => ⟨nested_approve_scoped (keccakSep_nested_of_erc20 h) hc hs,
    fun _ ht => nested_transferFrom_scoped h hc hs ht⟩

/-- HashScopeNested's `approveFootprint` is HashScopeCheck's at slot 2. -/
theorem nested_approveFootprint_eq (c s : Nat) :
    HashScopeNested.approveFootprint c s = approveFootprint 2 c s := by
  simp only [HashScopeNested.approveFootprint, HashScopeNested.nestedFootprint, approveFootprint,
    approveFootprintBy, solHash_pre]

/-- HashScopeNested's `transferFromFootprint` and HashScopeCheck's at slots 1 and 2 name the same
preimages, so their premises are one. -/
theorem nested_transferFrom_scoped_iff (c f t : Nat) :
    HashScopeNested.Scoped (HashScopeNested.transferFromFootprint c f t) ↔
      ScopedSep (transferFromFootprint 1 2 f t c) := by
  have e : solHash f 2 = keccakWord (mappingPreimage f 2) := solHash_pre f 2
  constructor <;> intro h <;> refine HashScopeNested.Scoped.mono h fun x hx => ?_ <;>
    simp only [HashScopeNested.transferFromFootprint, HashScopeNested.nestedFootprint,
      transferFromFootprint, transferFromFootprintBy, HashScopeNested.pre, e, List.cons_append,
      List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hx ⊢ <;> tauto

/-! ## The slot facts for every pair of `A` -/

/-- **Outer slots of distinct keys of `A` are apart** (`slot_ne`). -/
theorem nested_outer_ne {n : Nat} {A : Finset Nat} (h : KeccakSep (nestedPreimages n A))
    (hA : ∀ x ∈ A, x < 2 ^ 256) (hn : n < 2 ^ 256) {o o' : Nat} (ho : o ∈ A) (ho' : o' ∈ A)
    (hne : o ≠ o') : solHash o n ≠ solHash o' n :=
  HashScopeNested.slot_ne (scoped_toList h) (Finset.mem_toList.2 (nested_outer_mem ho))
    (Finset.mem_toList.2 (nested_outer_mem ho')) (hA o ho) (hA o' ho') hn hn fun ⟨e, _⟩ => hne e

/-- **Nested slots of distinct pairs of `A` are apart** (`slot_ne` twice): `n[o][s] = n[o'][s']`
only for `o = o'` and `s = s'`. -/
theorem nested_slot_ne {n : Nat} {A : Finset Nat} (h : KeccakSep (nestedPreimages n A))
    (hA : ∀ x ∈ A, x < 2 ^ 256) (hn : n < 2 ^ 256) {o s o' s' : Nat} (ho : o ∈ A) (hs : s ∈ A)
    (ho' : o' ∈ A) (hs' : s' ∈ A) (hne : ¬(o = o' ∧ s = s')) :
    solHash s (solHash o n) ≠ solHash s' (solHash o' n) := by
  refine HashScopeNested.slot_ne (scoped_toList h) (Finset.mem_toList.2 (nested_inner_mem ho hs))
    (Finset.mem_toList.2 (nested_inner_mem ho' hs')) (hA s hs) (hA s' hs') (solHash_lt_word _ _)
    (solHash_lt_word _ _) ?_
  rintro ⟨rfl, he⟩
  by_cases hoo : o = o'
  · exact hne ⟨hoo, rfl⟩
  · exact nested_outer_ne h hA hn ho ho' hoo he

/-- **A nested slot of `A` is no outer slot of `A`** (`nested_ne_flat`), for a small mapping slot. -/
theorem nested_ne_outer {n : Nat} {A : Finset Nat} (h : KeccakSep (nestedPreimages n A))
    (hA : ∀ x ∈ A, x < 2 ^ 256) (hn : n < 2 ^ 128) {o s o' : Nat} (ho : o ∈ A) (hs : s ∈ A)
    (ho' : o' ∈ A) : solHash s (solHash o n) ≠ solHash o' n :=
  HashScopeNested.nested_ne_flat (scoped_toList h) (Finset.mem_toList.2 (nested_outer_mem ho))
    (Finset.mem_toList.2 (nested_inner_mem ho hs)) (Finset.mem_toList.2 (nested_outer_mem ho'))
    (hA s hs) (hA o' ho') hn

/-- **A nested slot of `A` is no balance slot of `A`** (`nested_ne_flat`): allowances at slot `a`,
balances at the small slot `b`. -/
theorem nested_ne_balance {b a : Nat} {A : Finset Nat} (h : KeccakSep (erc20Preimages b a A))
    (hA : ∀ x ∈ A, x < 2 ^ 256) (hb : b < 2 ^ 128) {o s k : Nat} (ho : o ∈ A) (hs : s ∈ A)
    (hk : k ∈ A) : solHash s (solHash o a) ≠ solHash k b :=
  HashScopeNested.nested_ne_flat (scoped_toList h)
    (Finset.mem_toList.2 (nestedPreimages_sub_erc20 b a A (nested_outer_mem ho)))
    (Finset.mem_toList.2 (nestedPreimages_sub_erc20 b a A (nested_inner_mem ho hs)))
    (Finset.mem_toList.2 (balance_mem hk)) (hA s hs) (hA k hk) hb

/-- **Every outer and nested slot of `A` is at least `2 ^ 128`** (`slot_ge`). -/
theorem nested_slot_ge {n : Nat} {A : Finset Nat} (h : KeccakSep (nestedPreimages n A)) {o s : Nat}
    (ho : o ∈ A) (hs : s ∈ A) : 2 ^ 128 ≤ solHash o n ∧ 2 ^ 128 ≤ solHash s (solHash o n) :=
  ⟨HashScopeNested.slot_ge (scoped_toList h) (Finset.mem_toList.2 (nested_outer_mem ho)),
    HashScopeNested.slot_ge (scoped_toList h) (Finset.mem_toList.2 (nested_inner_mem ho hs))⟩

/-- Every balance slot of `A` is at least `2 ^ 128`. -/
theorem balance_slot_ge {b a : Nat} {A : Finset Nat} (h : KeccakSep (erc20Preimages b a A)) {k : Nat}
    (hk : k ∈ A) : 2 ^ 128 ≤ solHash k b :=
  HashScopeNested.slot_ge (scoped_toList h) (Finset.mem_toList.2 (balance_mem hk))

/-- **HashScopeNested's `transferFrom_slots` for every triple of `A`.** -/
theorem nested_transferFrom_slots {A : Finset Nat} (h : KeccakSep (erc20Preimages 1 2 A))
    (hA : ∀ x ∈ A, x < 2 ^ 256) {caller frm dst : Nat} (hc : caller ∈ A) (hf : frm ∈ A)
    (ht : dst ∈ A) :
    solHash caller (solHash frm 2) ≠ solHash frm 1 ∧ solHash caller (solHash frm 2) ≠ solHash dst 1 ∧
      (frm ≠ dst → solHash frm 1 ≠ solHash dst 1) ∧ 2 ^ 128 ≤ solHash caller (solHash frm 2) ∧
      2 ^ 128 ≤ solHash frm 1 ∧ 2 ^ 128 ≤ solHash dst 1 :=
  HashScopeNested.transferFrom_slots (nested_transferFrom_scoped h hc hf ht) (hA caller hc)
    (hA frm hf) (hA dst ht)

/-- **HashScopeNested's `approve_slot` for every pair of `A`.** -/
theorem nested_approve_slot {A : Finset Nat} (h : KeccakSep (nestedPreimages 2 A))
    {caller spender : Nat} (hc : caller ∈ A) (hs : spender ∈ A) :
    2 ^ 128 ≤ solHash spender (solHash caller 2) :=
  HashScopeNested.approve_slot (nested_approve_scoped h hc hs)

/-! ## Real witnesses at keccak256 -/

/-- HashScopeFinite's three addresses: from `real_erc20_ABC`. -/
theorem real_nested_ABC : KeccakSep (nestedPreimages 2 addrsABC) :=
  keccakSep_nested_of_erc20 real_erc20_ABC

/-- WETH on Ethereum mainnet. -/
abbrev tokWETH : Nat := 0xC02aaA39b223FE8D0A0e5C4F27eAD9083C756Cc2
/-- USDC on Ethereum mainnet. -/
abbrev tokUSDC : Nat := 0xA0b86991c6218b36c1d19D4a2e9Eb0cE3606eB48
/-- DAI on Ethereum mainnet. -/
abbrev tokDAI : Nat := 0x6B175474E89094C44Da98b954EedeAC495271d0F

/-- Three token addresses. -/
def tokens3 : Finset Nat := {tokWETH, tokUSDC, tokDAI}

/-- The 12 preimages of `nestedPreimages 2 tokens3` as a list: 3 outer and 9 inner. -/
def nestedList3 : List (List Nat) :=
  [tokWETH, tokUSDC, tokDAI].map (fun o => mappingPreimage o 2) ++
    [tokWETH, tokUSDC, tokDAI].flatMap fun o =>
      [tokWETH, tokUSDC, tokDAI].map fun s => mappingPreimage s (keccakWord (mappingPreimage o 2))

theorem nestedPreimages_3_sub : nestedPreimages 2 tokens3 ⊆ nestedList3.toFinset := by
  rw [nestedPreimages_eq_allowancePreimages]
  intro x hx
  simp only [allowancePreimages, Finset.mem_union, Finset.mem_image, Finset.mem_product] at hx
  rw [List.mem_toFinset]
  simp only [nestedList3, List.mem_append, List.mem_map, List.mem_flatMap]
  have hl : ∀ {k}, k ∈ tokens3 → k ∈ [tokWETH, tokUSDC, tokDAI] := fun hk => by
    simp only [tokens3, Finset.mem_insert, Finset.mem_singleton] at hk
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    exact hk
  rcases hx with (⟨o, ho, rfl⟩ | ⟨⟨o, s⟩, ⟨ho, hs⟩, rfl⟩)
  · exact .inl ⟨o, hl ho, rfl⟩
  · exact .inr ⟨o, hl ho, s, hl hs, rfl⟩

set_option maxRecDepth 100000 in
/-- The check at the real keccak256 on the 12 preimages: one kernel evaluation. -/
theorem real_nestedList3 : ScopedSep nestedList3 :=
  scopedSep_of_check (by decide +kernel)

/-- **The nested premise holds for the three tokens at slot 2 at the real keccak256.** -/
theorem real_nested_tokens : KeccakSep (nestedPreimages 2 tokens3) :=
  ((keccakSep_toFinset_iff _).2 real_nestedList3).mono nestedPreimages_3_sub

/-! ## Negative control: a key outside `A` -/

/-- `nested_approve_scoped` refuses a spender outside `A`: from the premise of `A = {addrA}`,
`approve(addrA)` from `addrA` elaborates and `approve(addrB)` from `addrA` does not (its side
condition `addrB ∈ {addrA}` is false); `fail_if_success` makes this file build only while it is
refused. -/
theorem nested_rejected (h : KeccakSep (nestedPreimages 2 {addrA})) : True := by
  have _hself : HashScopeNested.Scoped (HashScopeNested.approveFootprint addrA addrA) :=
    nested_approve_scoped h (by decide) (by decide)
  fail_if_success
    have _hAB : HashScopeNested.Scoped (HashScopeNested.approveFootprint addrA addrB) :=
      nested_approve_scoped h (by decide) (by decide)
  trivial

/-! ## Axiom checks -/

/-- info: 'SolidCore.Spec.nestedPreimages_eq_allowancePreimages' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms nestedPreimages_eq_allowancePreimages

/-- info: 'SolidCore.Spec.nestedPreimages_eq_footprints' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms nestedPreimages_eq_footprints

/-- info: 'SolidCore.Spec.keccakSep_nested_of_erc20' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms keccakSep_nested_of_erc20

/-- info: 'SolidCore.Spec.nested_scoped' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms nested_scoped

/-- info: 'SolidCore.Spec.nested_approve_scoped' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms nested_approve_scoped

/-- info: 'SolidCore.Spec.nested_transferFrom_scoped' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms nested_transferFrom_scoped

/-- info: 'SolidCore.Spec.nested_sep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms nested_sep

/-- info: 'SolidCore.Spec.nested_approveFootprint_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms nested_approveFootprint_eq

/-- info: 'SolidCore.Spec.nested_transferFrom_scoped_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms nested_transferFrom_scoped_iff

/-- info: 'SolidCore.Spec.nested_outer_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms nested_outer_ne

/-- info: 'SolidCore.Spec.nested_slot_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms nested_slot_ne

/-- info: 'SolidCore.Spec.nested_ne_outer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms nested_ne_outer

/-- info: 'SolidCore.Spec.nested_ne_balance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms nested_ne_balance

/-- info: 'SolidCore.Spec.nested_slot_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms nested_slot_ge

/-- info: 'SolidCore.Spec.balance_slot_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms balance_slot_ge

/-- info: 'SolidCore.Spec.nested_transferFrom_slots' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms nested_transferFrom_slots

/-- info: 'SolidCore.Spec.nested_approve_slot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms nested_approve_slot

/-- info: 'SolidCore.Spec.real_nested_ABC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms real_nested_ABC

/-- info: 'SolidCore.Spec.real_nestedList3' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms real_nestedList3

/-- info: 'SolidCore.Spec.real_nested_tokens' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms real_nested_tokens

/-- info: 'SolidCore.Spec.nested_rejected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms nested_rejected

end SolidCore.Spec

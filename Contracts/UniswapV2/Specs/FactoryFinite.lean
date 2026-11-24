import Contracts.UniswapV2.Specs.Factory
import Verify.Spec.HashScopeFiniteNested

/-!
# createPair's hash premise over a finite set of tokens

`CreatePairSpec` (Factory.lean) takes `ScopedSep (createPairFootprint t0 t1)` for its call: keccak256
separated on the four preimages of `getPair[t0][t1]` and `getPair[t1][t0]` (`getPair` at slot 2, a
nested mapping). This module discharges that premise for every pair of a finite token set `A` from
the one hypothesis `KeccakSep (nestedPreimages getPairSlot A)` (Verify/Spec/HashScopeFiniteNested.lean),
in both orders and for equal tokens. It is about the footprint only: `CreatePairSpec` stays a
statement, and `createPairSpec_of_keccakSep` assumes it.

* `createPair_sep`: `ScopedSep (createPairFootprint t0 t1)` for every `t0, t1 ∈ A`;
* `createPair_call_sep`: the premise `CreatePairSpec` names, at `sortTokens a b`, for every
  `a, b ∈ A`;
* `createPairSpec_of_keccakSep`: `CreatePairSpec` with the hash premise replaced by `a, b ∈ A`;
* `pairKey_ne`: the `getPair` slots of distinct ordered pairs of `A` are apart;
* `real_createPair_tokens`: the premise for every pair of three token addresses at the real
  keccak256 (`real_nested_tokens`, one kernel evaluation per image);
* negatives: `createPair_rejected` (a token outside `A` does not elaborate) and
  `outside_token_no_lift` (no hash argument lifts the separation of `A = {addrA}`'s preimages to
  the pair `(addrA, addrB)`).
-/

namespace SolidCore.Spec.UniswapV2.Specs.Factory

open SolidCore.Spec SolidCore.Refinement SolidCore.Refinement.Generic TrustedBase

/-- **createPair's footprint for every `t0, t1 ∈ A`**, both orders and `t0 = t1` included. -/
theorem createPair_sep {A : Finset Nat} (h : KeccakSep (nestedPreimages getPairSlot A)) {t0 t1 : Nat}
    (h0 : t0 ∈ A) (h1 : t1 ∈ A) : ScopedSep (createPairFootprint t0 t1) :=
  scopedSep_of_keccakSep h fun x hx => by
    simp only [createPairFootprint, HashScopeNested.nestedFootprint, List.cons_append,
      List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact nested_outer_mem h0
    · exact nested_inner_mem h0 h1
    · exact nested_outer_mem h1
    · exact nested_inner_mem h1 h0

theorem sortTokens_mem {A : Finset Nat} {a b : Nat} (ha : a ∈ A) (hb : b ∈ A) :
    (sortTokens a b).1 ∈ A ∧ (sortTokens a b).2 ∈ A := by
  unfold sortTokens
  split_ifs
  · exact ⟨ha, hb⟩
  · exact ⟨hb, ha⟩

/-- **The hash premise of `CreatePairSpec` for every call with `a, b ∈ A`.** -/
theorem createPair_call_sep {A : Finset Nat} (h : KeccakSep (nestedPreimages getPairSlot A)) :
    ∀ a ∈ A, ∀ b ∈ A, ScopedSep (createPairFootprint (sortTokens a b).1 (sortTokens a b).2) :=
  fun _ ha _ hb => createPair_sep h (sortTokens_mem ha hb).1 (sortTokens_mem ha hb).2

/-- **`CreatePairSpec` on the tokens of `A` without its per-call hash premise**: from the statement
(assumed, not proved here) and `KeccakSep (nestedPreimages getPairSlot A)`, the target holds of every
call with `a, b ∈ A` under the statement's other premises. -/
theorem createPairSpec_of_keccakSep (hspec : CreatePairSpec) {A : Finset Nat}
    (h : KeccakSep (nestedPreimages getPairSlot A)) :
    ∀ env W initHash st a b, a ∈ A → b ∈ A → env.WF → env.callvalue = 0 → Words st → a < U160 →
      b < U160 → W.hasCode 0 = false →
      ArrayApart (sortTokens a b).1 (sortTokens a b).2 (st allPairsSlot) →
      CreatePairTarget env W initHash st a b (createPairResult env W initHash st a b) :=
  fun env W initHash st a b ha hb hwf hv hst ha' hb' hc harr =>
    hspec env W initHash st a b hwf hv hst ha' hb' hc (createPair_call_sep h a ha b hb) harr

/-- **The `getPair` slots of distinct ordered pairs of `A` are apart** (`nested_slot_ne`); in
particular `getPair[t0][t1] ≠ getPair[t1][t0]` for `t0 ≠ t1`. -/
theorem pairKey_ne {A : Finset Nat} (h : KeccakSep (nestedPreimages getPairSlot A))
    (hA : ∀ x ∈ A, x < 2 ^ 256) {a b a' b' : Nat} (ha : a ∈ A) (hb : b ∈ A) (ha' : a' ∈ A)
    (hb' : b' ∈ A) (hne : ¬(a = a' ∧ b = b')) : pairKey a b ≠ pairKey a' b' :=
  nested_slot_ne h hA (by decide) ha hb ha' hb' hne

/-- **The premise for every pair of the three tokens at the real keccak256.** -/
theorem real_createPair_tokens :
    ∀ a ∈ tokens3, ∀ b ∈ tokens3,
      ScopedSep (createPairFootprint (sortTokens a b).1 (sortTokens a b).2) :=
  createPair_call_sep real_nested_tokens

/-! ## Negative controls: a token outside `A` -/

/-- `createPair_sep` refuses a token outside `A`: from the premise of `A = {tokWETH}` the pair
`(tokWETH, tokWETH)` elaborates and `(tokWETH, tokUSDC)` does not (its side condition
`tokUSDC ∈ {tokWETH}` is false); `fail_if_success` makes this file build only while it is refused. -/
theorem createPair_rejected (h : KeccakSep (nestedPreimages getPairSlot {tokWETH})) : True := by
  have _hself : ScopedSep (createPairFootprint tokWETH tokWETH) := createPair_sep h (by decide) (by decide)
  fail_if_success
    have _hWU : ScopedSep (createPairFootprint tokWETH tokUSDC) :=
      createPair_sep h (by decide) (by decide)
  trivial

/-- `A = {addrA}`'s preimages are the footprint of `getPair[addrA][addrA]`. -/
theorem nestedPreimages_addrA :
    nestedPreimages getPairSlot {addrA} =
      (HashScopeNested.nestedFootprint getPairSlot addrA addrA).toFinset := by
  rw [nestedPreimages_eq_footprints, Finset.singleton_product_singleton, Finset.singleton_biUnion]

/-- **No argument from the separation of `A`'s preimages reaches a token outside `A`**: the hash
numbering the preimages of `A = {addrA}` (`separatedBy_idxOf`) separates them and not the footprint of
createPair on `(addrA, addrB)`, whose `addrB . 2` and `addrB . keccak256(addrA . 2)` lie outside it and
get one image. -/
theorem outside_token_no_lift :
    ¬ ∀ hash : List Nat → Nat,
      SeparatedBy hash (HashScopeNested.nestedFootprint getPairSlot addrA addrA) →
        SeparatedBy hash (createPairFootprint addrA addrB) := by
  intro hl
  have hs := hl _ (separatedBy_idxOf (HashScopeNested.nestedFootprint getPairSlot addrA addrA))
  have hge : 2 ^ 128 ≤ solHash addrA 2 :=
    (nested_slot_ge real_nested_ABC (o := addrA) (s := addrA) (by simp [addrsABC])
      (by simp [addrsABC])).1
  have hlt : solHash addrA 2 < 2 ^ 256 := solHash_lt_word _ _
  have hBA : addrB ≠ addrA := by decide
  have out : ∀ k, k < 2 ^ 256 →
      HashScopeNested.pre addrB k ∉ HashScopeNested.nestedFootprint getPairSlot addrA addrA := by
    intro k hk
    simp only [HashScopeNested.nestedFootprint, List.mem_cons, List.not_mem_nil, or_false, not_or]
    exact ⟨fun e => hBA (mappingPreimage_inj (by decide) (by decide) hk (by decide) e).1,
      fun e => hBA (mappingPreimage_inj (by decide) (by decide) hk hlt e).1⟩
  have mu : HashScopeNested.pre addrB 2 ∈ createPairFootprint addrA addrB := by
    simp only [createPairFootprint, HashScopeNested.nestedFootprint, List.cons_append,
      List.nil_append, List.mem_cons, true_or, or_true]
  have mv : HashScopeNested.pre addrB (solHash addrA 2) ∈ createPairFootprint addrA addrB := by
    simp only [createPairFootprint, HashScopeNested.nestedFootprint, List.cons_append,
      List.nil_append, List.mem_cons, true_or, or_true]
  have e := hs.1 _ mu _ mv (by
    simp only [List.idxOf_eq_length (out 2 (by decide)), List.idxOf_eq_length (out _ hlt)])
  have := (mappingPreimage_inj (by decide) (by decide) (by decide) hlt e).2
  omega

/-! ## Axiom checks -/

/-- info: 'SolidCore.Spec.UniswapV2.Specs.Factory.createPair_sep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms createPair_sep

/-- info: 'SolidCore.Spec.UniswapV2.Specs.Factory.sortTokens_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sortTokens_mem

/-- info: 'SolidCore.Spec.UniswapV2.Specs.Factory.createPair_call_sep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms createPair_call_sep

/--
info: 'SolidCore.Spec.UniswapV2.Specs.Factory.createPairSpec_of_keccakSep' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms createPairSpec_of_keccakSep

/-- info: 'SolidCore.Spec.UniswapV2.Specs.Factory.pairKey_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms pairKey_ne

/--
info: 'SolidCore.Spec.UniswapV2.Specs.Factory.real_createPair_tokens' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms real_createPair_tokens

/-- info: 'SolidCore.Spec.UniswapV2.Specs.Factory.createPair_rejected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms createPair_rejected

/--
info: 'SolidCore.Spec.UniswapV2.Specs.Factory.nestedPreimages_addrA' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms nestedPreimages_addrA

/--
info: 'SolidCore.Spec.UniswapV2.Specs.Factory.outside_token_no_lift' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms outside_token_no_lift

end SolidCore.Spec.UniswapV2.Specs.Factory

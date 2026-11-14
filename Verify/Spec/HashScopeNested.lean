import Verify.Spec.HashScope
import Verify.Spec.TrustedBase.Hypotheses

/-!
# keccak256 separation scoped to a call's footprint, for mappings of mappings

`NestedSlotsSeparated ms ns` (TreeMapNested.lean) asks keccak256 to be injective on the slots
`n[b][a]` for **all** addresses `a`, `b`: `2 ^ 320` preimages into `2 ^ 256` words, so it is false of
keccak256 and every theorem assuming it is vacuous for the real EVM. This module states the
separation a call needs instead: keccak256 separated (`TrustedBase.KeccakSeparated`: injective,
every image at least `2 ^ 128`) on the **finite list** of preimages the call hashes, its
footprint, as hevm does (pairwise injectivity over the hash applications that occur).

* `Scoped L`: the premise, for a footprint `L` (a list, so finite by construction).
* `nestedFootprint n o s`: the two preimages of `n[o][s]`'s slot, the inner `o . n` and the outer
  `s . keccak(o . n)`; `approveFootprint` and `transferFromFootprint` are UniswapV2ERC20's (allowance
  at slot 2, balanceOf at slot 1).
* The slot facts a spec needs, each from `Scoped L` and membership in `L` only: two slots of
  the footprint are equal only for equal keys and mapping slots (`slot_ne`), a nested slot is no
  first-level slot of a small mapping slot (`nested_ne_flat`) and no small constant slot (`slot_ge`).
* `transferFrom_scoped_witness`: the premise holds of a concrete nontrivial footprint (three
  distinct keys, four preimages), by the kernel's evaluation of keccak256 on each, so it is
  satisfiable, unlike `NestedSlotsSeparated`.

`Scoped` is hash-scope's `ScopedSep` (Verify/Spec/HashScope.lean), the one footprint premise for
single-level and nested mappings alike: this module adds only the nested footprints and their slot
facts.
-/

namespace SolidCore.Spec.HashScopeNested

open SolidCore.Refinement SolidCore.Refinement.Generic

/-- **keccak256 separated on a call's footprint** `L`: injective on the finitely many preimages in
`L`, and every image at least `2 ^ 128` (so no small constant slot). -/
abbrev Scoped (L : List (List Nat)) : Prop := ScopedSep L

/-- The preimage of the slot of `m[a]` for a mapping at slot `m`. -/
abbrev pre (a m : Nat) : List Nat := TrustedBase.mappingPreimage a m

/-- The footprint of `n[o][s]`: the inner preimage `o . n` and the outer `s . keccak(o . n)`. -/
def nestedFootprint (n o s : Nat) : List (List Nat) := [pre o n, pre s (solHash o n)]

/-- `approve(spender, value)` from `caller` writes `allowance[caller][spender]` (allowance at slot 2). -/
def approveFootprint (caller spender : Nat) : List (List Nat) := nestedFootprint 2 caller spender

/-- `transferFrom(frm, to, value)` from `caller` reads and writes `allowance[frm][caller]`,
`balanceOf[frm]` and `balanceOf[to]` (balanceOf at slot 1). -/
def transferFromFootprint (caller frm dst : Nat) : List (List Nat) :=
  nestedFootprint 2 frm caller ++ [pre frm 1, pre dst 1]

theorem Scoped.mono {L L' : List (List Nat)} (h : Scoped L') (hs : ∀ x ∈ L, x ∈ L') : Scoped L :=
  TrustedBase.KeccakSeparated.mono h hs

/-- A footprint slot is no small constant slot. -/
theorem slot_ge {L : List (List Nat)} (h : Scoped L) {a m : Nat} (hx : pre a m ∈ L) :
    2 ^ 128 ≤ solHash a m := by
  rw [solHash_eq]
  exact h.2 _ hx

/-- Two footprint slots are equal only for equal keys and mapping slots. -/
theorem slot_ne {L : List (List Nat)} (h : Scoped L) {a b m n : Nat} (h1 : pre a m ∈ L)
    (h2 : pre b n ∈ L) (ha : a < 2 ^ 256) (hb : b < 2 ^ 256) (hm : m < 2 ^ 256) (hn : n < 2 ^ 256)
    (hne : ¬(a = b ∧ m = n)) : solHash a m ≠ solHash b n := by
  intro he
  rw [solHash_eq, solHash_eq] at he
  exact hne (mappingPreimage_inj ha hb hm hn (h.1 _ _ h1 h2 he))

/-- A nested footprint slot `n[o][s]` is no first-level slot `m[b]` of a small mapping slot. -/
theorem nested_ne_flat {L : List (List Nat)} (h : Scoped L) {o s n b m : Nat}
    (hi : pre o n ∈ L) (ho : pre s (solHash o n) ∈ L) (hf : pre b m ∈ L)
    (hs : s < 2 ^ 256) (hb : b < 2 ^ 256) (hm : m < 2 ^ 128) :
    solHash s (solHash o n) ≠ solHash b m := by
  have hge := slot_ge h hi
  have hlt := solHash_lt o n
  unfold Generic.wordSize at hlt
  exact slot_ne h ho hf hs hb hlt (by omega) (fun ⟨_, e⟩ => by omega)

/-- **transferFrom's slots are apart on its footprint**: `allowance[frm][caller]` is neither balance
slot, the two balance slots differ for different keys, and none is a small constant slot. -/
theorem transferFrom_slots {caller frm dst : Nat} (h : Scoped (transferFromFootprint caller frm dst))
    (hc : caller < 2 ^ 256) (hf : frm < 2 ^ 256) (ht : dst < 2 ^ 256) :
    solHash caller (solHash frm 2) ≠ solHash frm 1 ∧ solHash caller (solHash frm 2) ≠ solHash dst 1 ∧
      (frm ≠ dst → solHash frm 1 ≠ solHash dst 1) ∧ 2 ^ 128 ≤ solHash caller (solHash frm 2) ∧
      2 ^ 128 ≤ solHash frm 1 ∧ 2 ^ 128 ≤ solHash dst 1 := by
  simp only [transferFromFootprint, nestedFootprint] at h
  have m0 : pre frm 2 ∈ [pre frm 2, pre caller (solHash frm 2)] ++ [pre frm 1, pre dst 1] := by simp
  have m1 : pre caller (solHash frm 2) ∈ [pre frm 2, pre caller (solHash frm 2)] ++ [pre frm 1, pre dst 1] := by simp
  have m2 : pre frm 1 ∈ [pre frm 2, pre caller (solHash frm 2)] ++ [pre frm 1, pre dst 1] := by simp
  have m3 : pre dst 1 ∈ [pre frm 2, pre caller (solHash frm 2)] ++ [pre frm 1, pre dst 1] := by simp
  exact ⟨nested_ne_flat h m0 m1 m2 hc hf (by norm_num), nested_ne_flat h m0 m1 m3 hc ht (by norm_num),
    fun hne => slot_ne h m2 m3 hf ht (by norm_num) (by norm_num) (fun ⟨e, _⟩ => hne e),
    slot_ge h m1, slot_ge h m2, slot_ge h m3⟩

/-- **approve's slot is no small constant slot** on its footprint. -/
theorem approve_slot {caller spender : Nat} (h : Scoped (approveFootprint caller spender)) :
    2 ^ 128 ≤ solHash spender (solHash caller 2) :=
  slot_ge h (by simp [approveFootprint, nestedFootprint])

end SolidCore.Spec.HashScopeNested

namespace SolidCore.Spec.HashScopeNested

open SolidCore.Refinement SolidCore.Refinement.Generic

/-! ## The premise is satisfiable and not trivial

`transferFrom_scoped_witness`: on the footprint of `transferFrom(1, 2, _)` from `0x2000` (the stage's
caller) the premise holds, from the four images by the kernel's evaluation of keccak256 (one per
declaration). `not_scoped_collision`: it is not `True` either, since a footprint with two byte lists
of one image (`[0]` and `[256]`, the same bytes) refutes it. -/

/-- keccak256 of `1 . 2` (the slot of `allowance[1]`'s inner mapping). -/
abbrev kInner : Nat := 0xe90b7bceb6e7df5418fb78d8ee546e97c83a08bbccc01a0644d599ccd2a7c2e0

set_option maxRecDepth 100000 in
theorem image_inner : keccakWord (TrustedBase.mappingPreimage 1 2) = kInner := by decide +kernel

set_option maxRecDepth 100000 in
theorem image_outer : keccakWord (TrustedBase.mappingPreimage 0x2000 kInner) =
    0x2e4aafeb9f8b1b374b0f80165f823ef45fa5ed8d99f592ae99f791121a39e502 := by decide +kernel

set_option maxRecDepth 100000 in
theorem image_from : keccakWord (TrustedBase.mappingPreimage 1 1) =
    0xcc69885fda6bcc1a4ace058b4a62bf5e179ea78fd58a1ccd71c22cc9b688792f := by decide +kernel

set_option maxRecDepth 100000 in
theorem image_to : keccakWord (TrustedBase.mappingPreimage 2 1) =
    0xd9d16d34ffb15ba3a3d852f0d403e2ce1d691fb54de27ac87cd2f993f3ec330f := by decide +kernel

/-- **The scoped premise holds of a concrete nontrivial footprint**: `transferFrom(1, 2, _)` from
`0x2000`, four preimages over three distinct keys and both mapping levels. -/
theorem transferFrom_scoped_witness : Scoped (transferFromFootprint 0x2000 1 2) := by
  have hi : solHash 1 2 = kInner := by rw [solHash_eq]; exact image_inner
  unfold Scoped transferFromFootprint nestedFootprint pre
  rw [hi]
  exact TrustedBase.keccakSeparated_of_images (H := [kInner,
      0x2e4aafeb9f8b1b374b0f80165f823ef45fa5ed8d99f592ae99f791121a39e502,
      0xcc69885fda6bcc1a4ace058b4a62bf5e179ea78fd58a1ccd71c22cc9b688792f,
      0xd9d16d34ffb15ba3a3d852f0d403e2ce1d691fb54de27ac87cd2f993f3ec330f])
    (by simp only [List.cons_append, List.nil_append, List.map_cons, List.map_nil, image_inner,
      image_outer, image_from, image_to]) (by decide) (by decide)

set_option maxRecDepth 100000 in
/-- **The scoped premise is not trivial**: it fails on a footprint with a collision. -/
theorem not_scoped_collision : ¬ Scoped [[0], [256]] := by
  intro h
  have := h.1 [0] [256] (by simp) (by simp) (by decide +kernel)
  simp at this

/-- info: 'SolidCore.Spec.HashScopeNested.transferFrom_scoped_witness' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms transferFrom_scoped_witness

/-- info: 'SolidCore.Spec.HashScopeNested.transferFrom_slots' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms transferFrom_slots

end SolidCore.Spec.HashScopeNested

/-
openworld/postworld Stage 2 — the adoption round-trip laws.

Mirror of the Yul side's `ofYulShared_installYulShared`
(`evm-interaction EvmCompiler/Simulation/OpenWorld.lean`): adoption of an
answered `postWorld` is faithful, and the echo answer (`postWorld := sent
world`, `Query.defaultAnswer`'s convention) is a no-op on every carried field.

The exactness of the main law comes from the same design choice the Yul side
made: the adopted world is retained VERBATIM (`State.envWorld?`) and the next
snapshot returns it verbatim when nothing mutated — no map surgery, so the law
is `=`, not merely extensional.
-/
import SolidCore.Solidity.Interpreter

namespace SolidCore
namespace Solidity
namespace Source

/-! ### Ord bridge instances for the shared `UInt256`

`EvmYul.UInt256` derives `Ord` structurally (compare on the wrapped `Fin`,
then `.then .eq`); the Batteries RBMap lemmas are gated on `Std.TransCmp` /
`Std.LawfulEqCmp`, which `Fin`'s compare has and the derived structure compare
inherits through the bridge below. -/

theorem UInt256.compare_def (a b : EvmYul.UInt256) :
    compare a b = compare a.val b.val := by
  cases a; cases b
  simp [compare, EvmYul.instOrdUInt256.ord]

instance : Std.OrientedCmp
    (compare : EvmYul.UInt256 → EvmYul.UInt256 → Ordering) where
  eq_swap {a b} := by
    rw [UInt256.compare_def, UInt256.compare_def]
    exact Std.OrientedCmp.eq_swap

instance : Std.TransCmp
    (compare : EvmYul.UInt256 → EvmYul.UInt256 → Ordering) where
  isLE_trans {a b c} h₁ h₂ := by
    rw [UInt256.compare_def] at h₁ h₂ ⊢
    exact Std.TransCmp.isLE_trans h₁ h₂

instance : Std.LawfulEqCmp
    (compare : EvmYul.UInt256 → EvmYul.UInt256 → Ordering) where
  eq_of_compare {a b} h := by
    rw [UInt256.compare_def] at h
    cases a; cases b
    exact congrArg EvmYul.UInt256.mk (Std.LawfulEqCmp.eq_of_compare h)

/-! ### The round-trip law (mirror of `ofYulShared_installYulShared`) -/

/-- Adopting an arbitrary answered world and snapshotting immediately gives
    back exactly that world — for EVERY `w`, with `=`. This is the algebraic
    heart of the arbitrary-changes model: adoption loses nothing the
    environment said. -/
@[simp] theorem snapshotWorld_adoptWorld
    (w : SolidCore.Solidity.Shared.OpenWorld)
    (context : Context) (s : State) :
    snapshotWorld context (adoptWorld w context s) = w := by
  simp [adoptWorld, snapshotWorld]

/-- Adoption is idempotent: adopting the same answer twice is the same state
    as adopting it once (all adopted fields are functions of `w` and of
    state components adoption does not change). -/
theorem adoptWorld_idempotent
    (w : SolidCore.Solidity.Shared.OpenWorld)
    (context : Context) (s : State) :
    adoptWorld w context (adoptWorld w context s) = adoptWorld w context s := by
  simp [adoptWorld]

/-! ### Word/UInt256 conversion round-trips -/

theorem u256ToWord_wordToU256 (x : Word) :
    u256ToWord (wordToU256 x) = SolidCore.Solidity.Shared.norm x := rfl

theorem norm_u256ToWord (u : EvmYul.UInt256) :
    SolidCore.Solidity.Shared.norm (u256ToWord u) = u256ToWord u :=
  Nat.mod_eq_of_lt u.val.isLt

theorem wordToU256_norm (x : Word) :
    wordToU256 (SolidCore.Solidity.Shared.norm x) = wordToU256 x := by
  apply congrArg EvmYul.UInt256.mk
  apply Fin.ext
  show SolidCore.Solidity.Shared.norm x % _ = x % _
  simp only [SolidCore.Solidity.Shared.norm,
    SolidCore.Solidity.Shared.wordModulus]
  exact Nat.mod_mod_of_dvd x dvd_rfl

theorem wordToU256_u256ToWord (u : EvmYul.UInt256) :
    wordToU256 (u256ToWord u) = u := by
  cases u with
  | mk v =>
      apply congrArg EvmYul.UInt256.mk
      apply Fin.ext
      show v.val % _ = v.val
      exact Nat.mod_eq_of_lt v.isLt

theorem wordEq_iff_norm (a b : Word) :
    wordEq a b = true ↔
      SolidCore.Solidity.Shared.norm a = SolidCore.Solidity.Shared.norm b := by
  simp [wordEq]

theorem wordToU256_eq_iff (a b : Word) :
    wordToU256 a = wordToU256 b ↔ wordEq a b = true := by
  rw [wordEq_iff_norm]
  constructor
  · intro h
    exact congrArg u256ToWord h
  · intro h
    rw [← wordToU256_norm a, ← wordToU256_norm b, h]

theorem u256_eq_wordToU256_iff (u : EvmYul.UInt256) (k : Word) :
    u = wordToU256 k ↔ wordEq (u256ToWord u) k = true := by
  constructor
  · intro h
    rw [h]
    rw [wordEq_iff_norm, u256ToWord_wordToU256]
    simp [SolidCore.Solidity.Shared.norm, SolidCore.Solidity.Shared.wordModulus]
  · intro h
    have hn : SolidCore.Solidity.Shared.norm (u256ToWord u) =
        SolidCore.Solidity.Shared.norm k := (wordEq_iff_norm _ _).1 h
    rw [norm_u256ToWord] at hn
    calc u = wordToU256 (u256ToWord u) := (wordToU256_u256ToWord u).symm
      _ = wordToU256 (SolidCore.Solidity.Shared.norm k) := by rw [hn]
      _ = wordToU256 k := wordToU256_norm k

theorem compare_wordToU256_eq_iff (a b : Word) :
    (compare (wordToU256 a) (wordToU256 b) = .eq) ↔ wordEq a b = true := by
  rw [← wordToU256_eq_iff]
  exact Std.LawfulEqCmp.compare_eq_iff_eq

/-! ### Storage conversion round-trip (lookup-extensional) -/

/-- Well-formedness for a `StorageMap`: every physically stored key and value is
    already `norm`-canonical. Every `StorageMap` the interpreter builds is WF —
    `{}` is trivially WF, and `StorageMap.insertLoop`/`State.storeSlot` `norm`
    both key and value at every write — so this hypothesis is always available at
    the interpreter's call sites. It is genuinely required: `StorageMap.lookup?`
    matches keys by exact `norm`-query equality, whereas the round-trip through
    `EvmYul.Storage` canonicalizes keys, so a non-canonical physical key would
    break the round-trip law. -/
def StorageMap.WF (m : StorageMap) : Prop :=
  ∀ p ∈ Std.HashMap.toList m,
    SolidCore.Solidity.Shared.norm p.1 = p.1 ∧ SolidCore.Solidity.Shared.norm p.2 = p.2

/-- A `UInt256` key equals a `norm`-query exactly when its `wordToU256` preimage
    compares equal — the bridge between HashMap `==`-matching and RBMap
    `compare`-matching. -/
theorem u256ToWord_beq_norm_eq (u : EvmYul.UInt256) (k : Word) :
    (u256ToWord u == SolidCore.Solidity.Shared.norm k) =
      (compare (wordToU256 k) u == Ordering.eq) := by
  have hiff : u256ToWord u = SolidCore.Solidity.Shared.norm k ↔ u = wordToU256 k := by
    constructor
    · intro h
      calc u = wordToU256 (u256ToWord u) := (wordToU256_u256ToWord u).symm
        _ = wordToU256 (SolidCore.Solidity.Shared.norm k) := by rw [h]
        _ = wordToU256 k := wordToU256_norm k
    · intro h; rw [h, u256ToWord_wordToU256]
  have hcmp : (compare (wordToU256 k) u = Ordering.eq) ↔ u = wordToU256 k := by
    rw [Std.LawfulEqCmp.compare_eq_iff_eq]
    exact eq_comm
  by_cases h : u = wordToU256 k
  · simp only [(hiff.2 h : u256ToWord u = _), beq_self_eq_true]
    have : compare (wordToU256 k) u = Ordering.eq := hcmp.2 h
    simp [this]
  · have h1 : ¬ (u256ToWord u = SolidCore.Solidity.Shared.norm k) := fun hc => h (hiff.1 hc)
    have h2 : ¬ (compare (wordToU256 k) u = Ordering.eq) := fun hc => h (hcmp.1 hc)
    have e1 : (u256ToWord u == SolidCore.Solidity.Shared.norm k) = false := by simp [h1]
    have e2 : (compare (wordToU256 k) u == Ordering.eq) = false := by simp [h2]
    rw [e1, e2]

/-- Folding a list of word pairs into an `EvmYul.Storage` (each key/value sent
    through `wordToU256`) is a last-write-wins insert: the resulting `find?` is
    the *reverse* first match on the source list, falling back to `init`. Keys
    are unique in the sources we use, so reverse/forward first match coincide. -/
theorem find?_storage_foldl (L : List (Word × Word)) (init : EvmYul.Storage)
    (k : Word) :
    (L.foldl (fun acc kv => acc.insert (wordToU256 kv.1) (wordToU256 kv.2)) init).find?
        (wordToU256 k)
      = (L.reverse.find? (fun kv => wordEq kv.1 k)).elim
          (init.find? (wordToU256 k)) (fun kv => some (wordToU256 kv.2)) := by
  induction L generalizing init with
  | nil => simp
  | cons kv t ih =>
      simp only [List.foldl_cons, List.reverse_cons]
      rw [ih (init.insert (wordToU256 kv.1) (wordToU256 kv.2)), List.find?_append]
      cases hrt : t.reverse.find? (fun kv => wordEq kv.1 k) with
      | some w => simp
      | none =>
          simp only [Option.none_or, List.find?_cons, List.find?_nil]
          by_cases hb : wordEq kv.1 k = true
          · have hc : compare (wordToU256 k) (wordToU256 kv.1) = Ordering.eq := by
              rw [compare_wordToU256_eq_iff, wordEq_iff_norm]
              exact ((wordEq_iff_norm _ _).1 hb).symm
            simp only [hb, Option.elim]
            rw [Batteries.RBMap.find?_insert_of_eq _ hc]
          · have hbf : wordEq kv.1 k = false := by
              cases hh : wordEq kv.1 k
              · rfl
              · exact absurd hh hb
            have hc : compare (wordToU256 k) (wordToU256 kv.1) ≠ Ordering.eq := by
              intro hcontra
              have hkk : wordEq k kv.1 = true := (compare_wordToU256_eq_iff k kv.1).1 hcontra
              have hsym : wordEq kv.1 k = true := by
                rw [wordEq_iff_norm] at hkk ⊢; exact hkk.symm
              exact hb hsym
            simp only [hbf, Option.elim]
            rw [Batteries.RBMap.find?_insert_of_ne _ hc]

/-- First-match `find?` is determined by membership + uniqueness. -/
theorem list_find?_eq_some_of_unique {α : Type} {l : List α} {p : α → Bool}
    {y : α} (hy : y ∈ l) (hp : p y = true)
    (huniq : ∀ z ∈ l, p z = true → z = y) :
    l.find? p = some y := by
  induction l with
  | nil => cases hy
  | cons a t ih =>
      by_cases ha : p a = true
      · have haY : a = y := huniq a (List.mem_cons_self) ha
        subst haY
        simp [List.find?, ha]
      · have hy' : y ∈ t := by
          cases hy with
          | head => exact absurd hp ha
          | tail _ h => exact h
        have ha' : p a = false := by
          cases hpa : p a
          · rfl
          · exact absurd hpa ha
        simp only [List.find?, ha']
        exact ih hy' (fun z hz hpz => huniq z (List.mem_cons_of_mem _ hz) hpz)

/-- Bridge: `RBMap.findEntry?` is exactly the first `toList` entry whose key
    compares equal (sortedness makes it unique). -/
theorem toList_find?_eq_findEntry? (T : EvmYul.Storage) (u : EvmYul.UInt256) :
    T.toList.find? (fun kv => compare u kv.1 == Ordering.eq) =
      T.findEntry? u := by
  cases hFind : T.findEntry? u with
  | some y =>
      have hMem := (Batteries.RBMap.findEntry?_some.1 hFind)
      apply list_find?_eq_some_of_unique hMem.1
      · simp [hMem.2]
      · intro z hz hpz
        have hzEq : compare u z.1 = Ordering.eq := by
          cases hc : compare u z.1 <;> simp_all
        -- two toList entries whose keys both compare .eq to u are the same
        -- entry, by sortedness (mem_toList_unique on the pair order).
        have hyz : Ordering.byKey Prod.fst compare z y = Ordering.eq := by
          show compare z.1 y.1 = Ordering.eq
          have h₁ : compare z.1 u = Ordering.eq := by
            have hs := Std.OrientedCmp.eq_swap
              (cmp := compare) (a := z.1) (b := u)
            rw [hs, hzEq]
            rfl
          have h₂ := Std.TransCmp.congr_left (cmp := compare) h₁ (c := y.1)
          rw [h₂]
          exact hMem.2
        exact Batteries.RBSet.mem_toList_unique hz hMem.1 hyz
  | none =>
      apply List.find?_eq_none.2
      intro z hz
      by_contra hpz
      have hzEq : compare u z.1 = Ordering.eq := by
        cases hc : compare u z.1 <;> simp_all
      have hMemP : Batteries.RBSet.MemP (fun kv => compare u kv.1) T := by
        exact Batteries.RBNode.memP_def.2
          ⟨z, Batteries.RBSet.mem_toList.1 hz, hzEq⟩
      have := (Batteries.RBSet.memP_iff_findP?.1 hMemP)
      rcases this with ⟨y, hy⟩
      rw [show T.findEntry? u = T.findP? (fun kv => compare u kv.1) from rfl]
        at hFind
      rw [hFind] at hy
      cases hy

/-- On a list with at most one match for `p`, reversing before `find?` gives the
    same result: the unique match is found regardless of direction. -/
theorem find?_reverse_eq_of_unique {α : Type} {l : List α} {p : α → Bool}
    (huniq : ∀ x ∈ l, ∀ y ∈ l, p x = true → p y = true → x = y) :
    l.reverse.find? p = l.find? p := by
  cases hf : l.find? p with
  | some y =>
      have hy : y ∈ l := List.mem_of_find?_eq_some hf
      have hpy : p y = true := List.find?_some hf
      apply list_find?_eq_some_of_unique (List.mem_reverse.2 hy) hpy
      intro z hz hpz
      exact huniq z (List.mem_reverse.1 hz) y hy hpz hpy
  | none =>
      rw [List.find?_eq_none] at hf ⊢
      intro x hx
      exact hf x (List.mem_reverse.1 hx)

/-- Folding a `UInt256` store's entries back into a `StorageMap` (each key/value
    sent through `u256ToWord`) is a last-write-wins insert: the `norm k` lookup
    is the *reverse* first match on the source list, falling back to `init`. -/
theorem getElem?_storage_foldl (L : List (EvmYul.UInt256 × EvmYul.UInt256))
    (init : StorageMap) (k : Word) :
    (L.foldl (fun acc kv => Std.HashMap.insert acc (u256ToWord kv.1) (u256ToWord kv.2))
        init)[SolidCore.Solidity.Shared.norm k]?
      = (L.reverse.find? (fun kv => compare (wordToU256 k) kv.1 == Ordering.eq)).elim
          (init[SolidCore.Solidity.Shared.norm k]?) (fun kv => some (u256ToWord kv.2)) := by
  induction L generalizing init with
  | nil => simp
  | cons kv t ih =>
      simp only [List.foldl_cons, List.reverse_cons]
      rw [ih (Std.HashMap.insert init (u256ToWord kv.1) (u256ToWord kv.2)),
        List.find?_append]
      cases hrt : t.reverse.find?
          (fun kv => compare (wordToU256 k) kv.1 == Ordering.eq) with
      | some w => simp
      | none =>
          rw [Std.HashMap.getElem?_insert, u256ToWord_beq_norm_eq]
          cases hb : (compare (wordToU256 k) kv.1 == Ordering.eq) <;>
            simp [hb]

/-- Looking up the round-tripped `EvmYul.Storage` in the rebuilt `StorageMap` is
    exactly the RBMap lookup. -/
theorem lookup?_storageToWordMap (T : EvmYul.Storage) (k : Word) :
    StorageMap.lookup? (storageToWordMap T) k =
      (T.find? (wordToU256 k)).map u256ToWord := by
  have hfun : (fun (acc : StorageMap) (kv : EvmYul.UInt256 × EvmYul.UInt256) =>
      StorageMap.insertLoop acc (u256ToWord kv.1) (u256ToWord kv.2)) =
      (fun acc kv => Std.HashMap.insert acc (u256ToWord kv.1) (u256ToWord kv.2)) := by
    funext acc kv
    simp only [StorageMap.insertLoop, norm_u256ToWord]
  unfold StorageMap.lookup? storageToWordMap
  rw [Std.HashMap.get?_eq_getElem?, hfun, getElem?_storage_foldl,
    Std.HashMap.getElem?_empty]
  rw [find?_reverse_eq_of_unique (l := T.toList) (by
    intro x hx y hy hpx hpy
    have hxe : compare (wordToU256 k) x.1 = Ordering.eq := by
      simpa using hpx
    have hye : compare (wordToU256 k) y.1 = Ordering.eq := by
      simpa using hpy
    have hxy : Ordering.byKey Prod.fst compare x y = Ordering.eq := by
      show compare x.1 y.1 = Ordering.eq
      have h₁ : compare x.1 (wordToU256 k) = Ordering.eq := by
        have hs := Std.OrientedCmp.eq_swap
          (cmp := compare) (a := x.1) (b := wordToU256 k)
        rw [hs, hxe]; rfl
      have h₂ := Std.TransCmp.congr_left (cmp := compare) h₁ (c := y.1)
      rw [h₂]; exact hye
    exact Batteries.RBSet.mem_toList_unique hx hy hxy)]
  rw [toList_find?_eq_findEntry?]
  show (T.findEntry? (wordToU256 k)).elim none (fun kv => some (u256ToWord kv.2)) =
    ((T.findEntry? (wordToU256 k)).map (·.2)).map u256ToWord
  cases T.findEntry? (wordToU256 k) <;> rfl

/-- Rebuilding an `EvmYul.Storage` from a well-formed `StorageMap` and reading
    it back yields the original HashMap lookup (through `wordToU256`). -/
theorem find?_wordMapToStorage (m : StorageMap) (hm : StorageMap.WF m) (k : Word) :
    (wordMapToStorage m).find? (wordToU256 k) =
      (StorageMap.lookup? m k).map wordToU256 := by
  have hz_props : ∀ z ∈ Std.HashMap.toList m, wordEq z.1 k = true →
      z.1 = SolidCore.Solidity.Shared.norm k ∧
        m[SolidCore.Solidity.Shared.norm k]? = some z.2 := by
    intro z hzmem hpz
    have hwf := (hm z hzmem).1
    have hnn : SolidCore.Solidity.Shared.norm z.1 = SolidCore.Solidity.Shared.norm k :=
      (wordEq_iff_norm _ _).1 hpz
    have hz1 : z.1 = SolidCore.Solidity.Shared.norm k := by rw [← hwf]; exact hnn
    refine ⟨hz1, ?_⟩
    have hz2 : m[z.1]? = some z.2 := by
      rw [Std.HashMap.getElem?_eq_some_iff_exists_beq_and_mem_toList]
      exact ⟨z.1, by simp, by rw [Prod.mk.eta]; exact hzmem⟩
    rw [hz1] at hz2; exact hz2
  have hlk : StorageMap.lookup? m k = m[SolidCore.Solidity.Shared.norm k]? := by
    unfold StorageMap.lookup?; rw [Std.HashMap.get?_eq_getElem?]
  have hfold : (wordMapToStorage m).find? (wordToU256 k) =
      (m.toList.foldl (fun (acc : EvmYul.Storage) kv =>
        acc.insert (wordToU256 kv.1) (wordToU256 kv.2))
        default).find? (wordToU256 k) := by
    unfold wordMapToStorage
    rw [Std.HashMap.fold_eq_foldl_toList]
  rw [hfold, find?_storage_foldl]
  have hdef : (default : EvmYul.Storage).find? (wordToU256 k) = none := rfl
  rw [hdef, hlk]
  cases hg : m[SolidCore.Solidity.Shared.norm k]? with
  | some v =>
      have hmem : (SolidCore.Solidity.Shared.norm k, v) ∈ Std.HashMap.toList m := by
        rcases (Std.HashMap.getElem?_eq_some_iff_exists_beq_and_mem_toList).1 hg
          with ⟨k', hbeq, hmem'⟩
        have hkk : SolidCore.Solidity.Shared.norm k = k' := by simpa using hbeq
        rw [hkk]; exact hmem'
      have hfr : (Std.HashMap.toList m).reverse.find? (fun kv => wordEq kv.1 k) =
          some (SolidCore.Solidity.Shared.norm k, v) := by
        apply list_find?_eq_some_of_unique (List.mem_reverse.2 hmem)
        · show wordEq (SolidCore.Solidity.Shared.norm k) k = true
          rw [wordEq_iff_norm]
          simp only [SolidCore.Solidity.Shared.norm]
          exact Nat.mod_mod_of_dvd k dvd_rfl
        · intro z hz hpz
          obtain ⟨hz1, hz2⟩ := hz_props z (List.mem_reverse.1 hz) hpz
          rw [hg] at hz2
          have hz2v : z.2 = v := (Option.some.inj hz2).symm
          calc z = (z.1, z.2) := (Prod.mk.eta).symm
            _ = (SolidCore.Solidity.Shared.norm k, v) := by rw [hz1, hz2v]
      rw [hfr]; rfl
  | none =>
      have hnone : (Std.HashMap.toList m).reverse.find? (fun kv => wordEq kv.1 k) = none := by
        rw [List.find?_eq_none]
        intro z hz hpz
        obtain ⟨_, hz2⟩ := hz_props z (List.mem_reverse.1 hz) hpz
        rw [hg] at hz2
        cases hz2
      rw [hnone]; rfl

/-- The storage conversion round-trip is lookup-extensional (up to `norm`, which
    every interpreter read applies anyway; canonical stores are already
    normalized). Requires `StorageMap.WF m` — the round-trip canonicalizes keys,
    so a non-canonical physical key would break the law — which holds of every
    `StorageMap` the interpreter builds. -/
theorem lookup?_roundtrip (m : StorageMap) (hm : StorageMap.WF m) (k : Word) :
    StorageMap.lookup? (storageToWordMap (wordMapToStorage m)) k =
      (StorageMap.lookup? m k).map SolidCore.Solidity.Shared.norm := by
  rw [lookup?_storageToWordMap, find?_wordMapToStorage m hm]
  cases StorageMap.lookup? m k <;>
    simp [u256ToWord_wordToU256]

/-! ### The echo no-op (Stage 2 behavior preservation)

`Query.defaultAnswer` and every delta-less responder row answer
`postWorld := sent world`. Adopting that echo answer changes nothing the
interpreter can observe: storage/transient reads are unchanged (up to `norm`,
which every read applies; canonical stores are already normalized), balance and
nonce are unchanged (up to `norm`), and the event/interaction records are
untouched. Together with `snapshotWorld_adoptWorld` (adopted-clean states
return the adopted world verbatim, so for them the echo re-adoption is
`adoptWorld_idempotent`) this covers every reachable state. -/

theorem snapshotWorld_find_self (context : Context) (s : State)
    (h : s.envWorld? = none ∨ s.worldMutatedSinceAdoption = true) :
    (snapshotWorld context s).accounts.find? (wordToAddress context.self) =
      some (snapshotSelfAccount context s) := by
  have hEq : compare (wordToAddress context.self)
      (wordToAddress context.self) = Ordering.eq :=
    Std.LawfulEqCmp.compare_eq_iff_eq.2 rfl
  cases hw : s.envWorld? with
  | none =>
      simp [snapshotWorld, hw, snapshotWorldSeed,
        Batteries.RBMap.find?_insert_of_eq _ hEq]
  | some w =>
      have hm : s.worldMutatedSinceAdoption = true := by
        rcases h with h | h
        · rw [hw] at h; cases h
        · exact h
      simp [snapshotWorld, hw, hm,
        Batteries.RBMap.find?_insert_of_eq _ hEq]

/-- Echo adoption is a no-op on every interpreter-observable state component
    (the rebuild branches; adopted-clean states are covered exactly by
    `snapshotWorld_adoptWorld` + `adoptWorld_idempotent`). -/
theorem adoptWorld_echo_noop (context : Context) (s : State)
    (h : s.envWorld? = none ∨ s.worldMutatedSinceAdoption = true)
    (hStorageWF : StorageMap.WF s.storage) (hTransientWF : StorageMap.WF s.transient) :
    (∀ k, (adoptWorld (snapshotWorld context s) context s).loadSlot k =
      SolidCore.Solidity.Shared.norm (s.loadSlot k)) ∧
    (∀ k, (adoptWorld (snapshotWorld context s) context s).loadTransientSlot
        k = SolidCore.Solidity.Shared.norm (s.loadTransientSlot k)) ∧
    (adoptWorld (snapshotWorld context s) context s).selfBalance =
      SolidCore.Solidity.Shared.norm s.selfBalance ∧
    (adoptWorld (snapshotWorld context s) context s).selfNonce =
      SolidCore.Solidity.Shared.norm s.selfNonce ∧
    (adoptWorld (snapshotWorld context s) context s).events = s.events ∧
    (adoptWorld (snapshotWorld context s) context s).externalInteractions =
      s.externalInteractions ∧
    (adoptWorld (snapshotWorld context s) context s).immutables =
      s.immutables ∧
    (adoptWorld (snapshotWorld context s) context s).selfdestructs =
      s.selfdestructs := by
  have hSelf := snapshotWorld_find_self context s h
  have hAcct :
      ((snapshotWorld context s).accounts.find?
        (wordToAddress context.self)).getD default =
        snapshotSelfAccount context s := by
    rw [hSelf]; rfl
  have hStorage : (adoptWorld (snapshotWorld context s) context s).storage =
      storageToWordMap (wordMapToStorage s.storage) := by
    simp [adoptWorld, hAcct, snapshotSelfAccount]
  have hTransient :
      (adoptWorld (snapshotWorld context s) context s).transient =
        storageToWordMap (wordMapToStorage s.transient) := by
    simp [adoptWorld, hAcct, snapshotSelfAccount]
  refine ⟨?_, ?_, ?_, ?_, rfl, rfl, rfl, rfl⟩
  · intro k
    unfold State.loadSlot
    rw [hStorage, lookup?_roundtrip s.storage hStorageWF]
    cases StorageMap.lookup? s.storage k <;> rfl
  · intro k
    unfold State.loadTransientSlot
    rw [hTransient, lookup?_roundtrip s.transient hTransientWF]
    cases StorageMap.lookup? s.transient k <;> rfl
  · show u256ToWord ((((snapshotWorld context s)).accounts.find?
        (wordToAddress context.self)).getD default).balance = _
    rw [hAcct]
    rfl
  · show u256ToWord ((((snapshotWorld context s)).accounts.find?
        (wordToAddress context.self)).getD default).nonce = _
    rw [hAcct]
    rfl

end Source
end Solidity
end SolidCore

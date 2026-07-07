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

theorem wordMapToStorage_cons (kv : Word × Word) (t : WordMap) :
    wordMapToStorage (kv :: t) =
      (wordMapToStorage t).insert (wordToU256 kv.1) (wordToU256 kv.2) := by
  simp only [wordMapToStorage, List.foldr_cons]

theorem find?_wordMapToStorage (m : WordMap) (k : Word) :
    (wordMapToStorage m).find? (wordToU256 k) =
      (WordMap.lookup? m k).map wordToU256 := by
  induction m with
  | nil => rfl
  | cons kv t ih =>
      rw [wordMapToStorage_cons, Batteries.RBMap.find?_insert]
      by_cases h : wordEq kv.1 k = true
      · have hc : compare (wordToU256 k) (wordToU256 kv.1) = .eq := by
          rw [compare_wordToU256_eq_iff, wordEq_iff_norm]
          exact ((wordEq_iff_norm _ _).1 h).symm
        simp [hc, WordMap.lookup?, h, wordToU256_norm]
      · have hc : ¬(compare (wordToU256 k) (wordToU256 kv.1) = .eq) := by
          rw [compare_wordToU256_eq_iff, wordEq_iff_norm]
          intro hcontra
          exact h ((wordEq_iff_norm _ _).2 hcontra.symm)
        simp [hc, WordMap.lookup?, h, ih]

/-- List-side characterization: looking a `Word` key up in the converted
    assoc list is the first entry whose exact `UInt256` key is
    `wordToU256 k`. -/
theorem lookup?_map_conv (l : List (EvmYul.UInt256 × EvmYul.UInt256))
    (k : Word) :
    WordMap.lookup?
        (l.map (fun kv => (u256ToWord kv.1, u256ToWord kv.2))) k =
      (l.find? (fun kv =>
        compare (wordToU256 k) kv.1 == Ordering.eq)).map
        (fun kv => u256ToWord kv.2) := by
  induction l with
  | nil => rfl
  | cons kv t ih =>
      by_cases h : kv.1 = wordToU256 k
      · have hEq : wordEq (u256ToWord kv.1) k = true :=
          (u256_eq_wordToU256_iff kv.1 k).1 h
        have hCmp : compare (wordToU256 k) kv.1 = Ordering.eq := by
          rw [h]
          exact Std.LawfulEqCmp.compare_eq_iff_eq.2 rfl
        simp [WordMap.lookup?, List.find?, hEq, hCmp, norm_u256ToWord]
      · have hNe : ¬(wordEq (u256ToWord kv.1) k = true) := fun hAbs =>
          h ((u256_eq_wordToU256_iff kv.1 k).2 hAbs)
        have hCmp : ¬(compare (wordToU256 k) kv.1 = Ordering.eq) := by
          intro hc
          exact h (Std.LawfulEqCmp.eq_of_compare hc).symm
        have hBeq : (compare (wordToU256 k) kv.1 == Ordering.eq) = false := by
          cases hc : compare (wordToU256 k) kv.1 <;> simp_all
        simp [WordMap.lookup?, List.find?, hNe, hBeq, ih]

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

/-- Looking up the converted assoc list is exactly the RBMap lookup. -/
theorem lookup?_storageToWordMap (T : EvmYul.Storage) (k : Word) :
    WordMap.lookup? (storageToWordMap T) k =
      (T.find? (wordToU256 k)).map u256ToWord := by
  show WordMap.lookup?
      (T.toList.map (fun kv => (u256ToWord kv.1, u256ToWord kv.2))) k = _
  rw [lookup?_map_conv, toList_find?_eq_findEntry?]
  show _ = ((T.findEntry? (wordToU256 k)).map (·.2)).map u256ToWord
  cases T.findEntry? (wordToU256 k) <;> rfl

/-- The storage conversion round-trip is lookup-extensional (up to `norm`,
    which every interpreter read applies anyway; canonical stores are
    already normalized). -/
theorem lookup?_roundtrip (m : WordMap) (k : Word) :
    WordMap.lookup? (storageToWordMap (wordMapToStorage m)) k =
      (WordMap.lookup? m k).map SolidCore.Solidity.Shared.norm := by
  rw [lookup?_storageToWordMap, find?_wordMapToStorage]
  cases WordMap.lookup? m k <;> rfl

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
    (h : s.envWorld? = none ∨ s.worldMutatedSinceAdoption = true) :
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
    rw [hStorage, lookup?_roundtrip]
    cases WordMap.lookup? s.storage k <;> rfl
  · intro k
    unfold State.loadTransientSlot
    rw [hTransient, lookup?_roundtrip]
    cases WordMap.lookup? s.transient k <;> rfl
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

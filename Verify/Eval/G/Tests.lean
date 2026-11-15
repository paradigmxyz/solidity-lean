import Verify.Eval.G.Model

/-!
# Lane G: tests of the shared discharger

1. g_simp proves a rewrite chain's side conditions from one internalized context, with the
   standard axioms only.
2. Sibling isolation (must FAIL if any fact leaks): a split on x = 0 where each child has a side
   condition only its own hypothesis proves. In the positive child (h : x = 0) the read through
   the store at x moves (a = 64 is past x's 32 bytes) and the read through the store at y must
   NOT move (y > a holds only when x ≠ 0). In the negative child (h : ¬x = 0) it is the other way
   round. Each child is closed by exact with a hypothesis stating exactly the form it must have,
   so a fact or a cached discharge that crossed from one sibling to the other changes that
   form and the exact fails. The contradictory pair x = 0 / ¬x = 0 also means a leaked E-graph
   would be inconsistent and discharge everything. g_split_simp_shared runs the same with ONE
   Sym.simp cache across both children (positive first).
3. The wrong control g_split_simp_leaky (negative child discharged from the positive child's
   goal) must be rejected by the same test: fail_if_success shows it is.
-/

open Verify.Eval.G.Model

set_option g_simp.trace true

theorem shared_chain (m : Mem) (p q v : Word) (hp : p < 18446744073709551616)
    (hq : Evm.add p 96 ≤ q) (_hq2 : q < 18446744073709551616) :
    (((m.store (Evm.add p 0).toNat v).store (Evm.add p 32).toNat v).store
      (Evm.add p 64).toNat v).read q.toNat 32 = m.read q.toNat 32 := by
  g_simp [Mem.read_store_disjoint] using [toNat_evm_add]
  all_goals rfl

/-- info: 'shared_chain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms shared_chain

section isolation

variable (m : Mem) (x y a : Nat) (v w : Word) (ha : a = 64) (hy : ¬x = 0 → a + 32 ≤ y)
  (P : List Nat → List Nat → Prop)
  (hpos : x = 0 → P (m.read a 32) ((m.store y w).read a 32))
  (hneg : ¬x = 0 → P ((m.store x v).read a 32) (m.read a 32))
include ha hy hpos hneg

theorem sibling_isolation : P ((m.store x v).read a 32) ((m.store y w).read a 32) := by
  g_split_simp (x = 0) [Mem.read_store_disjoint]
  · exact hpos h
  · exact hneg h

theorem sibling_isolation_shared_cache :
    P ((m.store x v).read a 32) ((m.store y w).read a 32) := by
  g_split_simp_shared (x = 0) [Mem.read_store_disjoint]
  · exact hpos h
  · exact hneg h

/-- The leaky control does not get through the same test. -/
theorem sibling_isolation_rejects_leak :
    P ((m.store x v).read a 32) ((m.store y w).read a 32) := by
  fail_if_success
    g_split_simp_leaky (x = 0) [Mem.read_store_disjoint]
    · exact hpos h
    · exact hneg h
  by_cases h : x = 0
  · rw [Mem.read_store_disjoint m x v a 32 (by omega)]; exact hpos h
  · rw [Mem.read_store_disjoint m y w a 32 (by have := hy h; omega)]; exact hneg h

end isolation

/-- info: 'sibling_isolation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sibling_isolation

/-- info: 'sibling_isolation_shared_cache' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sibling_isolation_shared_cache

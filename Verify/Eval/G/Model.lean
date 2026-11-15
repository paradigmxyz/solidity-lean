import Verify.Eval.G.Shared

/-!
# Lane G: a pure-Lean copy of the memory side conditions of W1Proofs' sym_mem

The words, the one word operation and the memory model the side conditions mention, as small
definitions (W1Proofs.Tactic is not built here): Word is BitVec 256, Evm.add is addition, a
memory maps byte addresses to bytes, and Mem.read_store_disjoint has the side condition of
SolarTV.MemorySymbolic's lemma of that name, word for word:
address + count <= offset \/ offset + 32 <= address.

base_mem_disch copies tv/W1Proofs/Tactic.lean's sym_mem_disch_core (lines 1064-1075): per side
condition, unfold the word operations everywhere, rewrite words to their toNat (the bitvec_to_nat simp set, which core
Lean registers and Mathlib extends; here only core's lemmas), fold literals, omega;
without error recovery.
-/

namespace Verify.Eval.G.Model

abbrev Word := BitVec 256

/-- The word addition W1Proofs' Evm.add is. -/
def Evm.add (a b : Word) : Word := a + b

/-- Byte-addressed memory. -/
structure Mem where
  bytes : Nat → Nat

def Mem.store (m : Mem) (o : Nat) (v : Word) : Mem :=
  ⟨fun i => if o ≤ i ∧ i < o + 32 then v.toNat else m.bytes i⟩

def Mem.read (m : Mem) (a n : Nat) : List Nat := (List.range n).map fun i => m.bytes (a + i)

/-- SolarTV.MemorySymbolic.Mem.read_store_disjoint's statement on this model. -/
theorem Mem.read_store_disjoint (m : Mem) (offset : Nat) (value : Word) (address count : Nat)
    (h : address + count ≤ offset ∨ offset + 32 ≤ address) :
    (m.store offset value).read address count = m.read address count := by
  unfold read store
  apply List.map_congr_left
  intro i hi
  simp only [List.mem_range] at hi
  have : ¬(offset ≤ address + i ∧ address + i < offset + 32) := by omega
  simp [this]

/-- A read at the offset a store wrote: SolarTV's Mem.read_store_at shape. -/
theorem Mem.read_store_at (m : Mem) (offset : Nat) (value : Word) (address : Nat)
    (h : address = offset) :
    (m.store offset value).read address 32 = (List.range 32).map fun _ => value.toNat := by
  subst h
  unfold read store
  apply List.map_congr_left
  intro i hi
  simp only [List.mem_range] at hi
  simp [hi]

/-- The only trigger the side conditions need: a sum of words as numbers. -/
theorem toNat_evm_add (a b : Word) : (Evm.add a b).toNat = (a.toNat + b.toNat) % 2 ^ 256 :=
  BitVec.toNat_add a b

/-- The fact g_facts collects instead: a word sum as the bit-vector sum grind reads natively. -/
theorem evm_add_eq (a b : Word) : Evm.add a b = a + b := rfl

end Verify.Eval.G.Model

open Verify.Eval.G.Model in
/-- tv/W1Proofs/Tactic.lean's sym_mem_disch_core on this model (see the module docs). -/
macro "base_mem_disch_core" : tactic => `(tactic|
  ((try simp only [Verify.Eval.G.Model.Evm.add] at *)
   <;> (try simp -implicitDefEqProofs only [bitvec_to_nat] at *)
   <;> (try simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] at *)
   <;> omega))

open Lean Elab Tactic in
/-- base_mem_disch_core without error recovery, as sym_mem_disch. -/
elab "base_mem_disch" : tactic => do
  withoutRecover (evalTactic (← `(tactic| base_mem_disch_core)))

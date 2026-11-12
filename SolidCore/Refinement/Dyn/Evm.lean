import SolidCore.Refinement.Evm.Symex
import SolidCore.Refinement.Dyn.Abi

/-!
# Symbolic execution of a dispatcher on malformed call data

A per-contract theorem that solar's bytecode rejects malformed call data
(`Dyn.Malformed`) is one call of the tactic `dyn_symex` under the generic lemma
`malformed_of_frame`, which reduces `Target.run` to a frame specification: from
pc 0 with no value, 10M gas and call data `selectorOf s ++ data`, where `data` is
any malformed byte string shorter than `2 ^ 32`, the frame halts with `Reverted`.

Unlike `dirty_symex`, the call data is not a list of words: its size and its
bytes are free. The run keeps CALLDATASIZE as `BitVec.ofNat 256 (4 + data.size)`
and every CALLDATALOAD as the word `loadWord msg.data x.toNat 32` at its offset `x`,
which EthLib reads as 32 bytes zero-padded past the end. Only the selector is
evaluated (`shr_selectorOf_append`). `tailPastEnd_iff` restates the malformed
hypothesis on those words: an offset word `o` at byte `4 + pos` of the call data,
and the length word at `o + 4`, the offset of the tail in the call data.

At each JUMPI the tactic turns the condition, an OR of comparisons, into one
proposition (`ite_or_ite`, `ite_eq_zero`) and decides the branch, or refutes it,
with `bv_omega` from the size bound and the malformed hypothesis, or with
`bv_decide` where `bv_omega` fails. A path that reaches RETURN or STOP, or an
opcode no rule covers, is left as an unsolved goal. MSTORE at a known offset grows the
memory as in `dirty_symex`.
-/

open EthLib.Base EthLib.Execution EthLib.Execution.Evm EthLib.Execution.Evm.Logic GasCosts
open SolidCore.Refinement.Evm.Logic SolidCore.Refinement.Evm.Symex

namespace SolidCore.Refinement.Dyn

/-! ## The call data -/

/-- `SHR 224` of the first word of the call data is its selector, whatever follows it. -/
theorem shr_selectorOf_append (s : Nat) (hs : s < 2 ^ 32) (data : ByteArray) :
    bitwiseShr 224#256 (loadWord (Evm.selectorOf s ++ data) 0 32) = BitVec.ofNat 256 s := by
  have h := SolidCore.Refinement.Evm.bitwiseShr_loadWord_zero (Evm.selectorOf s ++ data) 4 (by decide) (by decide)
  rw [show BitVec.ofNat 256 (8 * (32 - 4)) = 224#256 from rfl] at h
  rw [h, SolidCore.Refinement.Evm.bufferRead_append_of_le _ _ (by simp [Evm.size_selectorOf])]
  have h4 := Evm.size_selectorOf s
  have : bufferRead (Evm.selectorOf s) 0 4 = (Evm.selectorOf s).data.toList := by
    rw [← h4]; exact bufferRead_zero_size _
  rw [this, Evm.bytesToNat_selectorOf s hs]

/-- CALLDATALOAD past the selector reads the bytes after it. -/
theorem loadWord_selectorOf_append (s : Nat) (data : ByteArray) (p : Nat) :
    loadWord (Evm.selectorOf s ++ data) (4 + p) 32 = loadWord data p 32 := by
  have h := Evm.bufferRead_append_add (Evm.selectorOf s) data p 32
  rw [Evm.size_selectorOf] at h
  simp only [loadWord, h]

theorem size_selectorOf_append (s : Nat) (data : ByteArray) :
    (Evm.selectorOf s ++ data).size = 4 + data.size := by
  simp [ByteArray.size_append, Evm.size_selectorOf]

/-- A dynamic argument that points past the end, stated on the words the bytecode reads:
the offset word at byte `4 + pos` of the call data, and the length word at the offset plus
4, read only once the offset leaves room for it. -/
theorem tailPastEnd_iff {s : Nat} {data cd : ByteArray} (hd : cd = Evm.selectorOf s ++ data)
    (hsz : data.size < 2 ^ 32) (pos k : Nat) :
    TailPastEnd data pos k ↔
      data.size < (loadWord cd (4 + pos) 32).toNat + 32 ∨
        ((loadWord cd (4 + pos) 32).toNat + 32 ≤ data.size ∧
          data.size < (loadWord cd (4 + pos) 32).toNat + 32 +
            (loadWord cd (loadWord cd (4 + pos) 32 + 4#256).toNat 32).toNat * k) := by
  subst hd
  simp only [TailPastEnd, wordAt, loadWord_selectorOf_append]
  generalize ho : loadWord data pos 32 = o
  constructor
  · rintro (h | h)
    · exact Or.inl h
    · by_cases hlt : data.size < o.toNat + 32
      · exact Or.inl hlt
      · refine Or.inr ⟨by omega, ?_⟩
        have : (o + 4#256).toNat = 4 + o.toNat := by
          rw [BitVec.toNat_add, BitVec.toNat_ofNat]
          omega
        rw [this, loadWord_selectorOf_append]
        exact h
  · rintro (h | ⟨h1, h2⟩)
    · exact Or.inl h
    · right
      have : (o + 4#256).toNat = 4 + o.toNat := by
        rw [BitVec.toNat_add, BitVec.toNat_ofNat]
        omega
      rw [this, loadWord_selectorOf_append] at h2
      exact h2

/-! ## Branch conditions -/

theorem ite_or_ite (p q : Prop) [Decidable p] [Decidable q] :
    ((if p then 1#256 else 0#256) ||| (if q then 1#256 else 0#256)) = if p ∨ q then 1#256 else 0#256 := by
  by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq]

theorem ite_eq_zero (p : Prop) [Decidable p] : ((if p then 1#256 else 0#256) = 0#256) ↔ ¬ p := by
  by_cases hp : p <;> simp [hp]

theorem ite_ne_zero (p : Prop) [Decidable p] : ((if p then 1#256 else 0#256) ≠ 0#256) ↔ p := by
  by_cases hp : p <;> simp [hp]

theorem ite_zero_eq_zero (p : Prop) [Decidable p] :
    ((if p then 0#256 else 1#256) = 0#256) ↔ p := by
  by_cases hp : p <;> simp [hp]

theorem ite_eq_zero' (p : Prop) [Decidable p] : ((if p then 1#256 else 0#256) = (0 : U256)) ↔ ¬ p := by
  by_cases hp : p <;> simp [hp]

theorem ite_ne_zero' (p : Prop) [Decidable p] : ((if p then 1#256 else 0#256) ≠ (0 : U256)) ↔ p := by
  by_cases hp : p <;> simp [hp]

theorem ite_zero_eq_zero' (p : Prop) [Decidable p] :
    ((if p then 0#256 else 1#256) = (0 : U256)) ↔ p := by
  by_cases hp : p <;> simp [hp]

/-! ## From the frame to `Target.run` -/

/-- The generic malformed-call-data theorem: if, for every malformed `data` shorter than
`2 ^ 32`, the frame of every message with no value and call data `selectorOf s ++ data`
reverts with empty output, then every such call shows the rejection, from any storage. -/
theorem malformed_of_frame (code : ByteArray) (s : Nat) (ps : List DParam)
    (h : ∀ data : ByteArray, data.size < 2 ^ 32 → Malformed ps data →
      ∀ msg : Message .fusaka, msg.value = 0 → msg.data = Evm.selectorOf s ++ data →
      ∀ st ss, Spec .fusaka (At code msg 0 [] .empty 10000000 st ss .empty) Reverted)
    (σ : List (Nat × Nat)) (data : ByteArray) (hsz : data.size < 2 ^ 32)
    (hm : Malformed ps data) :
    Target.run code (callOn s data σ) = some (Abi.rejected σ) :=
  run_of_reverts code _ rfl fun st ss => h data hsz hm _ rfl rfl st ss

/-! ## The tactic -/

open Lean.Parser.Tactic

/-- Closes a goal about the words of a run: by `bv_omega` once the conditions are
propositions, or by `bv_decide`. -/
syntax "dyn_close" ident : tactic

macro_rules
  | `(tactic| dyn_close $hf) => `(tactic| (
      (try simp only [ite_or_ite, ite_ne_zero, ite_ne_zero', ite_eq_zero, ite_eq_zero', ite_zero_eq_zero,
        ite_zero_eq_zero', not_or, not_and,
        not_lt, ne_eq, Decidable.not_not] at *)
      first
        | bv_omega
        | symex_bv $hf))

/-- One step of a symbolic run on free call data: `symex_one` with `dyn_close` deciding the
branches. -/
syntax "dyn_one" " [" simpLemma,* "]" " [" simpLemma,* "]" ident : tactic

macro_rules
  | `(tactic| dyn_one [$ls,*] [$ns,*] $hf) => `(tactic| ((try unfold Spec) <;> first
      | (refine revert_empty (by decide) ?lt ?op
         case lt => evm_code [$ls,*]
         case op => evm_code [$ls,*])
      | ((refine' Triple.seq (push0 (by decide) ?lt ?op ?gas ?room) ?next
          case lt => evm_code [$ls,*]
          case op => evm_code [$ls,*]
          case gas => evm_gas
          case room => evm_room) <;> evm_tidy)
      | ((refine' Triple.seq (jumpi_of_eq_zero ?lt ?op ?gas ?zero) ?next
          case lt => evm_code [$ls,*]
          case op => evm_code [$ls,*]
          case gas => evm_gas
          case zero => first | assumption | decide) <;> evm_tidy)
      | ((refine' Triple.seq (jumpi_taken ?lt ?op ?gas ?nz ?dest) ?next
          case lt => evm_code [$ls,*]
          case op => evm_code [$ls,*]
          case gas => evm_gas
          case nz => first | assumption | decide
          case dest => evm_dest [$ls,*]) <;> evm_tidy)
      | ((refine' Triple.seq (jumpi_of_eq_zero ?lt ?op ?gas ?zero) ?next
          case lt => evm_code [$ls,*]
          case op => evm_code [$ls,*]
          case gas => evm_gas
          case zero => dyn_close $hf) <;> evm_tidy)
      | ((refine' Triple.seq (jumpi_taken ?lt ?op ?gas ?nz ?dest) ?next
          case lt => evm_code [$ls,*]
          case op => evm_code [$ls,*]
          case gas => evm_gas
          case nz => dyn_close $hf
          case dest => evm_dest [$ls,*]) <;> evm_tidy)
      | ((refine jumpi_split ?lt ?op ?gas ?dest (fun _ => ?zero) (fun _ => ?taken)
          case lt => evm_code [$ls,*]
          case op => evm_code [$ls,*]
          case gas => evm_gas
          case dest => evm_dest [$ls,*]
          case zero => try (exfalso; dyn_close $hf)
          case taken => try (exfalso; dyn_close $hf)) <;> evm_tidy)
      | ((refine' Triple.seq (mstore ?lt ?op ?gas) ?next
          case lt => evm_code [$ls,*]
          case op => evm_code [$ls,*]
          case gas => simp only [extendMemory, memoryGasCost, wordCount, ceil32, MEMORY_PER_WORD,
            WORD_BYTES, ByteArray.size_empty, size_memoryExtend, BitVec.reduceToNat, BitVec.reduceEq,
            ↓reduceIte, Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMul, Nat.reduceSub, Nat.reducePow,
            Nat.reduceLeDiff, Nat.reduceMod, Nat.reduceLT, Nat.reduceEqDiff] <;> omega) <;>
          (try simp only [extendMemory, memoryGasCost, wordCount, ceil32, MEMORY_PER_WORD,
            WORD_BYTES, ByteArray.size_empty, size_memoryExtend, BitVec.reduceToNat, BitVec.reduceEq,
            ↓reduceIte, Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMul, Nat.reduceSub, Nat.reducePow,
            Nat.reduceLeDiff, Nat.reduceMod, Nat.reduceLT, Nat.reduceEqDiff]) <;> evm_tidy)
      | evm_step [$ls,*]) <;> (try symex_norm [$ns,*]))

/-- Proves the frame hypothesis of `malformed_of_frame` for a code: every path of the code
on malformed call data reverts with empty output. `ls` are the rules that turn the code into
numbers, as for `evm_step`, and the definition of the selector. -/
syntax "dyn_symex" " [" simpLemma,* "]" : tactic

macro_rules
  | `(tactic| dyn_symex [$ls,*]) => `(tactic| (
      intro data hsz hmal msg hv hd st ss
      have hfork : Fork.fusaka ≤ Fork.fusaka := by decide
      have hsel := hd ▸ shr_selectorOf_append _ (by simp only [$ls,*]; decide) data
      have hsize : msg.data.size = 4 + data.size := by rw [hd, size_selectorOf_append]
      simp only [Malformed, dynHeads, DParam.stride?, DParam.headWords, headWords,
        List.take, List.mem_append, List.mem_cons, List.mem_nil_iff, List.nil_append,
        List.append_nil, or_false, exists_eq_or_imp, exists_eq_left, Nat.mul_zero, Nat.mul_one,
        List.length_cons, List.length_nil, false_and, exists_const, exists_false,
        Nat.add_zero, Nat.zero_add, Nat.reduceMul, Nat.reduceAdd,
        tailPastEnd_iff hd hsz] at hmal
      try simp only [$ls,*] at hsel
      clear hd
      repeat dyn_one [$ls,*] [hsel, hsize, hv] hfork))

end SolidCore.Refinement.Dyn

import SolidCore.Refinement.Solar.Assemble
import EthLib.Execution.Proofs.Evm.Machine.JumpDest

/-!
# The assembler check, in one pass over the code

The kernel evaluates `Assemble.check` on a contract's bytecode to prove its assembly stage. Two of
its parts read the code at random offsets of a list: the walk (`SolarTV.Assembly.walk`) decodes
each instruction at its offset with `code[pc]?`, and the labels' check (`labelsValid`) runs
EthLib's scan of the valid jump destinations, which reads each byte with `byteAt`. Each of those
reads walks the list from its head, and the kernel keeps every step it took: for bank's 454 bytes
the walk costs 0.7 GB and the scan 1.1 GB.

`checkFast` is the same check in one pass: its walk (`walkS`) carries the rest of the code from
the offset it reached, so each instruction decodes from the list's head, and it has no labels'
check, which the walk implies. `check_eq_checkFast` proves the two equal on every program, code and
certificate, so a kernel evaluation of `checkFast` proves `check` true or false.

* `decodeS`, `walkS`: `decode` and `walk` on the rest of the code (`decodeS_drop`, `walkS_drop`).
* `labelsValid_of_walk`: each label the walk reaches is a valid jump destination by EthLib's own
  analysis: the walk steps from opcode to opcode as EthLib's scan does (`next_eq_nextOpcode`, by
  `opLen`, the bytes the scan steps over at each of the 256 bytes), from offset 0, and finds
  JUMPDEST at each label.
-/

namespace SolidCore.Refinement.Solar.Assemble

open SolarTV.Assembly
open EthLib.Base EthLib.Execution EthLib.Execution.Evm GasCosts

/-! ## Decoding from the rest of the code -/

/-- `decode` at offset `pc` of the code whose rest from `pc` is the list: the instruction, the
offset after it and the rest of the code from there. -/
def decodeS : List Nat → Nat → Option (SolarTV.Assembly.Instr × Nat × List Nat)
  | [], _ => none
  | byte :: tl, pc =>
    if byte = PUSH0 then some (.push 0, pc + 1, tl)
    else if PUSH1 ≤ byte ∧ byte ≤ PUSH32 then
      if (tl.take (byte - PUSH1 + 1)).length = byte - PUSH1 + 1 then
        some (.push (bigEndian (tl.take (byte - PUSH1 + 1))), pc + 1 + (byte - PUSH1 + 1),
          tl.drop (byte - PUSH1 + 1))
      else none
    else some (.op byte, pc + 1, tl)

/-- `walk` from offset `pc` of the code whose rest from `pc` is the list: whether the walk
succeeds. -/
def walkS (offset : Nat → Nat) : List Nat → Nat → List Item → Bool
  | rest, _, [] => rest.isEmpty
  | rest, pc, item :: items =>
    match decodeS rest pc with
    | none => false
    | some (instr, next, rest') =>
      instr == item.expected offset && labelAt offset pc item && walkS offset rest' next items

/-- The checker `check`, with the walk on the rest of the code and without the labels' check,
which the walk implies. -/
def checkFast (p : Program) (code : ByteArray) (c : Cert) : Bool :=
  walkS c.offset (bytesOf code) 0 (lower p c) && blocksOk p c 0 p.blocks &&
    decide (c.need 0 = 0) && decide (c.top % 32 = 0) &&
    decide (cost p c 0 ≤ 1000) && decide (c.top ≤ 2 ^ 32) &&
    decide (22100 * cost p c 0 + memoryGasCost c.top ≤ 10000000) && decide (code.size < 2 ^ 32)

theorem decodeS_drop (code : List Nat) (pc : Nat) :
    decodeS (code.drop pc) pc = (decode code pc).map fun x => (x.1, x.2, code.drop x.2) := by
  unfold decode
  rcases h : code.drop pc with _ | ⟨byte, tl⟩
  · have hle : code.length ≤ pc := List.drop_eq_nil_iff.1 h
    rw [List.getElem?_eq_none hle]
    rfl
  · have hget : code[pc]? = some byte := by
      rw [← List.head?_drop, h]
      rfl
    have htl : code.drop (pc + 1) = tl := by
      rw [← List.drop_drop, h]
      rfl
    have hlen : code.length = pc + 1 + tl.length := by
      have := congrArg List.length h
      simp only [List.length_drop, List.length_cons] at this
      omega
    rw [hget]
    simp only [decodeS]
    by_cases h0 : byte = PUSH0
    · simp [h0, htl]
    · by_cases h1 : PUSH1 ≤ byte ∧ byte ≤ PUSH32
      · have hd : ∀ n, code.drop (pc + 1 + n) = tl.drop n := fun n => by
          rw [← htl, List.drop_drop]
        by_cases h2 : pc + 1 + (byte - PUSH1 + 1) ≤ code.length
        · have h2' : (tl.take (byte - PUSH1 + 1)).length = byte - PUSH1 + 1 := by
            rw [List.length_take]
            omega
          simp [h0, h1, h2, h2', htl, hd]
        · have h2' : ¬(tl.take (byte - PUSH1 + 1)).length = byte - PUSH1 + 1 := by
            rw [List.length_take]
            omega
          have h3 : ¬byte - PUSH1 + 1 ≤ tl.length := by omega
          simp [h0, h1, h3]
          omega
      · simp [h0, h1, htl]

/-- A successful decode ends within the code. -/
theorem decode_next_le {code : List Nat} {pc next : Nat} {i : SolarTV.Assembly.Instr}
    (h : decode code pc = some (i, next)) : next ≤ code.length := by
  unfold decode at h
  split at h
  · cases h
  · rename_i byte hb
    have hlt := (List.getElem?_eq_some_iff.1 hb).1
    split at h
    · cases h
      omega
    · split at h
      · split at h
        · cases h
          assumption
        · cases h
      · cases h
        omega

theorem walkS_drop (code : List Nat) (offset : Nat → Nat) :
    ∀ (items : List Item) (pc : Nat), pc ≤ code.length →
      walkS offset (code.drop pc) pc items = (walk code offset pc items).isSome
  | [], pc, hpc => by
    simp only [walkS, walk]
    by_cases h : pc = code.length
    · subst h
      simp
    · simp only [h, ↓reduceIte]
      cases e : code.drop pc with
      | nil => have := List.drop_eq_nil_iff.1 e; omega
      | cons x l => rfl
  | item :: items, pc, hpc => by
    simp only [walkS, walk, decodeS_drop]
    cases hd : decode code pc with
    | none => rfl
    | some x =>
      obtain ⟨instr, next⟩ := x
      simp only [Option.map_some]
      rw [walkS_drop code offset items next (decode_next_le hd)]
      cases h1 : instr == item.expected offset <;> cases h2 : labelAt offset pc item <;>
        cases walk code offset next items <;>
        simp only [beq_iff_eq, beq_eq_false_iff_ne] at h1 <;>
        simp only [h1, Bool.and_false, Bool.and_true, and_true, and_false, ↓reduceIte,
          Option.isSome_none, Option.isSome_some, Bool.and_self, reduceCtorEq, and_self]

/-! ## The walk implies the labels' check -/

/-- The bytes EthLib's scan steps over at an opcode: PUSHn's opcode and its `n` bytes of data, one
byte for every other opcode. -/
def opLen (b : UInt8) : Nat :=
  match Op.decode b with
  | some (.push n) => n.val + 1
  | _ => 1

theorem nextOpcode_eq_opLen (code : ByteArray) (pc : Nat) :
    nextOpcode code pc = pc + opLen (byteAt code pc) := by
  unfold nextOpcode opLen
  rcases Op.decode (byteAt code pc) with _ | op
  · rfl
  · cases op <;> rfl

theorem opLen_ofNat : ∀ n, n < 256 → opLen (UInt8.ofNat n) =
    1 + if 0x60 ≤ n ∧ n ≤ 0x7f then n - 0x5f else 0 := by
  decide +kernel

/-- The bytes EthLib's scan steps over by the byte alone, as the walk decodes it. -/
theorem opLen_eq (b : UInt8) :
    opLen b = 1 + if 0x60 ≤ b.toNat ∧ b.toNat ≤ 0x7f then b.toNat - 0x5f else 0 := by
  have h := opLen_ofNat b.toNat b.toNat_lt
  rwa [UInt8.ofNat_toNat] at h

/-- The walk steps from an instruction to the next opcode, as EthLib's scan does. -/
theorem next_eq_nextOpcode {code : ByteArray} {pc next : Nat} {i : SolarTV.Assembly.Instr}
    (h : decode (bytesOf code) pc = some (i, next)) : next = nextOpcode code pc ∧ pc < code.size := by
  unfold decode at h
  split at h
  · cases h
  · rename_i byte hb
    have hlt := (List.getElem?_eq_some_iff.1 hb).1
    rw [length_bytesOf] at hlt
    have hbyte : (byteAt code pc).toNat = byte := by
      rw [byteAt_toNat, List.getD_eq_getElem?_getD, hb]
      rfl
    refine ⟨?_, hlt⟩
    rw [nextOpcode_eq_opLen, opLen_eq, hbyte]
    unfold PUSH0 PUSH1 PUSH32 at h
    split at h
    · cases h
      rename_i h0
      simp [h0]
    · split at h
      · split at h
        · cases h
          rename_i h0 h1 _
          simp only [h1, and_self, ↓reduceIte]
          omega
        · cases h
      · cases h
        rename_i h1
        simp only [h1, ↓reduceIte]

theorem boundary_next {code : ByteArray} {s p : Nat} (h : BoundaryFrom code s p)
    (hn : nextOpcode code p < code.size) : BoundaryFrom code s (nextOpcode code p) := by
  induction h with
  | here hs => exact .step hs (.here hn)
  | step hs _ ih => exact .step hs (ih hn)

/-- Each label a successful walk from an opcode boundary reaches is a valid jump destination. -/
theorem walk_labels {code : ByteArray} {offset : Nat → Nat} :
    ∀ (items : List Item) (pc : Nat), (walk (bytesOf code) offset pc items).isSome = true →
      (pc < code.size → BoundaryFrom code 0 pc) →
      ∀ l, Item.label l ∈ items → isValidJumpDest (validJumpDestinations code) (offset l) = true
  | [], _, _, _, l, hl => absurd hl (by simp)
  | item :: items, pc, hw, hb, l, hl => by
    simp only [walk] at hw
    cases hd : decode (bytesOf code) pc with
    | none => rw [hd] at hw; simp at hw
    | some x =>
      obtain ⟨instr, next⟩ := x
      rw [hd] at hw
      simp only at hw
      by_cases ok : instr = item.expected offset ∧ labelAt offset pc item = true
      · simp only [ok, and_self, ↓reduceIte] at hw
        have hw' : (walk (bytesOf code) offset next items).isSome = true := by
          cases h' : walk (bytesOf code) offset next items <;> simp [h'] at hw ⊢
        obtain ⟨hnext, hpc⟩ := next_eq_nextOpcode hd
        have hbpc := hb hpc
        rcases List.mem_cons.1 hl with rfl | hl
        · have hoff : offset l = pc := by simpa [labelAt] using ok.2
          have hi : instr = .op SolarTV.Assembly.JUMPDEST := by simpa [Item.expected] using ok.1
          rw [hi] at hd
          obtain ⟨hbyte, -⟩ := decode_op hd
          rw [hoff, isValidJumpDest_iff_boundaryFrom]
          refine ⟨hbpc, ?_⟩
          apply UInt8.toNat_inj.mp
          rw [byteAt_toNat, List.getD_eq_getElem?_getD, hbyte]
          rfl
        · refine walk_labels items next hw' (fun hn => ?_) l hl
          rw [hnext] at hn ⊢
          exact boundary_next hbpc hn
      · simp only [ok, ↓reduceIte] at hw
        simp at hw

theorem label_mem_lowerFrom (p : Program) (c : Cert) {t : Nat} (ht : isTarget p c t = true) :
    ∀ (l : List (List Instr)) (b : Nat), b ≤ t → t < b + l.length →
      Item.label t ∈ lowerFrom p c b l
  | [], b, h1, h2 => by simp at h2; omega
  | x :: l, b, h1, h2 => by
    simp only [lowerFrom, List.mem_append]
    by_cases e : t = b
    · subst e
      left
      simp [lowerBlock, ht]
    · right
      exact label_mem_lowerFrom p c ht l (b + 1) (by omega) (by simp at h2; omega)

/-- The walk of the lowered program implies the labels' check. -/
theorem labelsValid_of_walk {p : Program} {c : Cert} {code : ByteArray}
    (hw : (walk (bytesOf code) c.offset 0 (lower p c)).isSome = true) :
    labelsValid p c code = true := by
  simp only [labelsValid, List.all_eq_true, List.mem_range]
  intro b hb
  cases ht : isTarget p c b
  · rfl
  · simp only [Bool.not_true, Bool.false_or]
    exact walk_labels _ 0 hw (fun h => .here h) b
      (label_mem_lowerFrom p c ht p.blocks 0 (by omega) (by omega))

/-- The two checkers agree on every program, code and certificate. -/
theorem check_eq_checkFast (p : Program) (code : ByteArray) (c : Cert) :
    check p code c = checkFast p code c := by
  have hw : walkS c.offset (bytesOf code) 0 (lower p c) =
      (walk (bytesOf code) c.offset 0 (lower p c)).isSome := by
    simpa using walkS_drop (bytesOf code) c.offset (lower p c) 0 (Nat.zero_le _)
  unfold check checkFast
  rw [hw]
  cases h : (walk (bytesOf code) c.offset 0 (lower p c)).isSome
  · simp
  · rw [labelsValid_of_walk h]
    simp

/-- info: 'SolidCore.Refinement.Solar.Assemble.check_eq_checkFast' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms check_eq_checkFast

end SolidCore.Refinement.Solar.Assemble

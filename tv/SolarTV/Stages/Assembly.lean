import SolarTV.Sem

/-! The stage from assembly to bytecode, which `-Zvalidate-assembly` checks.

The assembler solves a program of opcodes, pushes of constants and of label offsets, and label
definitions to a layout and emits bytes. `-Zvalidate-assembly` (`validate_assembly.rs`) decodes the
bytes in lockstep with the program: `Walk` is that walk, with the checker's conditions as its
constructors. Each item decodes, at the offset the walk reached, to the instruction it is at the
layout (`Item.expected`): an opcode to its byte, a constant push to a PUSH of the constant, so its
width suffices, a label push to a PUSH of the label's offset, and a label to a `JUMPDEST` at the
label's offset; and the walk ends exactly at the end of the code. Jump tables
(`indexed_jump.rs`) add two items: a packed table, a PUSH of a word of one-byte label offsets
that `BYTE` picks from, each offset below 256 so that its byte is the offset, and the entry
stubs of a stride table, each a `JUMPDEST` at the table's offset plus its index times the
stride (`Item.placed`).

From the walk, `walk_decodes` proves that linear decoding of the bytes from offset 0 is exactly the
program's instructions at their offsets, `jump_targets` that every pushed label is the offset of a
`JUMPDEST` that decoding reaches as an instruction, and `stage` that assembly to bytecode is a
stage for any bytecode semantics that runs the code's linear decoding, against the assembly program
run at the layout the walk found. No axioms.

An immutable's placeholder is an item of its own, a push of zeros of its width, which the
deployment code links with the immutable's value: `SolarTV.Stages.Link` shows that linear
decoding of the linked code is the walk's instructions with each placeholder pushing its value.

Outside this model, as in the checker's limits: program data and library placeholders, which the checker checks byte for byte against the artifact's records,
and the data flow of the deployment code's copy of the runtime code. The bytecode semantics
running the linear decoding is a hypothesis: legacy EVM code runs instruction by instruction from
offset 0 and jumps only to a `JUMPDEST` that starts an instruction, which is what the decoding
lists. -/

namespace SolarTV.Assembly

/-- An instruction as bytecode decodes it: an opcode, or a push of its immediate's value. -/
inductive Instr where
  | op (byte : Nat)
  | push (value : Nat)
  /-- An opcode that reads the byte after it as its immediate: DUPN, SWAPN or EXCHANGE
  (EIP-8024). -/
  | opImm (byte imm : Nat)
  deriving DecidableEq, Repr

def PUSH0 : Nat := 0x5f
def PUSH1 : Nat := 0x60
def PUSH32 : Nat := 0x7f
def JUMPDEST : Nat := 0x5b
def DUPN : Nat := 0xe6
def SWAPN : Nat := 0xe7
def EXCHANGE : Nat := 0xe8

/-- Whether an opcode reads the byte after it as an immediate (EIP-8024's DUPN, SWAPN and
EXCHANGE), so that decoding steps over two bytes. -/
def hasImmediate (byte : Nat) : Bool := byte == DUPN || byte == SWAPN || byte == EXCHANGE

/-! ### EIP-8024 immediates

The immediates of DUPN, SWAPN and EXCHANGE as solar's assembler writes them
(`encode_stack_depth` and `encode_exchange` in `crates/evmir/src/op.rs`) and as EIP-8024 decodes
them (EthLib's `decodeSingle` and `decodePair`). A depth counts from 1 at the top: DUPN of depth
`n` pushes a copy of the `n`th word and SWAPN of depth `n` exchanges the top with the word `n`
below it, so EVM IR's `dup i` and `swap i` are depth `i + 1`. EXCHANGE exchanges the words at two
depths `n < m` below the top, with `n + m ≤ 30`: EVM IR's `exchange n m`. -/

/-- The immediate of DUPN or SWAPN for a depth from 17 to 235. -/
def encodeDepth (n : Nat) : Nat := (n + 111) % 256

/-- The depth a DUPN or SWAPN immediate encodes, from 17 to 235; none for 91 to 127. -/
def decodeDepth (x : Nat) : Option Nat :=
  if 90 < x ∧ x < 128 then none else some ((x + 145) % 256)

/-- Whether DUPN and SWAPN reach a depth. -/
def depthOk (n : Nat) : Bool := 17 ≤ n && n ≤ 235

/-- The immediate of EXCHANGE for the depths `n < m` with `n + m ≤ 30`. -/
def encodePair (n m : Nat) : Nat :=
  (if m ≤ 16 then 16 * (n - 1) + (m - 1) else 16 * (29 - m) + (n - 1)) ^^^ 143

/-- The depths an EXCHANGE immediate encodes; none for 82 to 127. -/
def decodePair (x : Nat) : Option (Nat × Nat) :=
  if 81 < x ∧ x < 128 then none
  else
    let k := x ^^^ 143
    if k / 16 < k % 16 then some (k / 16 + 1, k % 16 + 1) else some (k % 16 + 1, 29 - k / 16)

/-- Whether EXCHANGE reaches a pair of depths. -/
def pairOk (n m : Nat) : Bool := 1 ≤ n && n < m && n + m ≤ 30

/-- Whether the byte after an opcode with an immediate encodes an operand of it. -/
def immediateOk (byte imm : Nat) : Bool :=
  if byte = EXCHANGE then (decodePair imm).isSome else (decodeDepth imm).isSome

/-- Each immediate that decodes is the encoding of what it decodes to. -/
def depthRound (x : Nat) : Bool :=
  match decodeDepth x with
  | some n => depthOk n && encodeDepth n == x
  | none => true

/-- Each EXCHANGE immediate that decodes is the encoding of the pair it decodes to. -/
def pairRound (x : Nat) : Bool :=
  match decodePair x with
  | some (n, m) => pairOk n m && encodePair n m == x
  | none => true

set_option maxRecDepth 8000 in
theorem decodeDepth_encodeDepth_all :
    ∀ n < 256, depthOk n = true → decodeDepth (encodeDepth n) = some n := by
  decide

/-- Decoding the immediate of a depth DUPN and SWAPN reach gives the depth. -/
theorem decodeDepth_encodeDepth {n : Nat} (h : depthOk n = true) :
    decodeDepth (encodeDepth n) = some n :=
  decodeDepth_encodeDepth_all n (by simp [depthOk] at h; omega) h

theorem encodeDepth_lt (n : Nat) : encodeDepth n < 256 := Nat.mod_lt _ (by decide)

set_option maxRecDepth 8000 in
theorem depthRound_all : ∀ x < 256, depthRound x = true := by decide

/-- A byte that decodes to a depth is that depth's encoding, and DUPN and SWAPN reach it. -/
theorem encodeDepth_decodeDepth {x n : Nat} (hx : x < 256) (h : decodeDepth x = some n) :
    depthOk n = true ∧ encodeDepth n = x := by
  have := depthRound_all x hx
  simp only [depthRound, h, Bool.and_eq_true, beq_iff_eq] at this
  exact this

theorem decodePair_encodePair_all :
    ∀ n < 32, ∀ m < 32, pairOk n m = true →
      decodePair (encodePair n m) = some (n, m) ∧ encodePair n m < 256 := by
  decide

/-- Decoding the immediate of a pair EXCHANGE reaches gives the pair. -/
theorem decodePair_encodePair {n m : Nat} (h : pairOk n m = true) :
    decodePair (encodePair n m) = some (n, m) ∧ encodePair n m < 256 :=
  decodePair_encodePair_all n (by simp [pairOk] at h; omega) m (by simp [pairOk] at h; omega) h

set_option maxRecDepth 8000 in
theorem pairRound_all : ∀ x < 256, pairRound x = true := by decide

/-- A byte that decodes to a pair is that pair's encoding, and EXCHANGE reaches it. -/
theorem encodePair_decodePair {x n m : Nat} (hx : x < 256) (h : decodePair x = some (n, m)) :
    pairOk n m = true ∧ encodePair n m = x := by
  have := pairRound_all x hx
  simp only [pairRound, h, Bool.and_eq_true, beq_iff_eq] at this
  exact this

/-- No immediate that decodes is a PUSH opcode (PUSH0 to PUSH32) or JUMPDEST, so a scan for
jump destinations that steps over the immediate as an opcode of its own (as EIP-8024 keeps it)
stays on the same boundaries. -/
theorem immediateOk_not_push {byte imm : Nat} (h : immediateOk byte imm = true) :
    ¬(0x5b ≤ imm ∧ imm ≤ 0x7f) := by
  intro ⟨h1, h2⟩
  unfold immediateOk at h
  cases Nat.decEq byte EXCHANGE with
  | isTrue hb =>
    rw [if_pos hb] at h
    unfold decodePair at h
    rw [if_pos ⟨by omega, by omega⟩] at h
    exact Bool.false_ne_true h
  | isFalse hb =>
    rw [if_neg hb] at h
    unfold decodeDepth at h
    rw [if_pos ⟨by omega, by omega⟩] at h
    exact Bool.false_ne_true h

/-- The big-endian value of `bytes`. -/
def bigEndian (bytes : List Nat) : Nat :=
  bytes.foldl (fun value byte => value * 256 + byte) 0

/-- The instruction at `pc` of `code` and the offset after it, or `none` past the end of the
code or for a push or an opcode whose immediate runs past it, as the checker reads it. -/
def decode (code : List Nat) (pc : Nat) : Option (Instr × Nat) :=
  match code[pc]? with
  | none => none
  | some byte =>
    if byte = PUSH0 then some (.push 0, pc + 1)
    else if PUSH1 ≤ byte ∧ byte ≤ PUSH32 then
      if pc + 1 + (byte - PUSH1 + 1) ≤ code.length then
        some (.push (bigEndian ((code.drop (pc + 1)).take (byte - PUSH1 + 1))),
          pc + 1 + (byte - PUSH1 + 1))
      else none
    else if hasImmediate byte then
      -- NOTE: EthLib reads 0 past the end of the code and halts on an immediate that encodes no
      -- depth; the walk refuses both, as solar's assembler does.
      match code[pc + 1]? with
      | some imm => if immediateOk byte imm then some (.opImm byte imm, pc + 2) else none
      | none => none
    else some (.op byte, pc + 1)

/-- Linear decoding of `code` from `pc`, each instruction at its offset, for at most `fuel`
instructions. -/
def decodeFrom (code : List Nat) : Nat → Nat → List (Nat × Instr)
  | 0, _ => []
  | fuel + 1, pc =>
    match decode code pc with
    | some (instr, next) => (pc, instr) :: decodeFrom code fuel next
    | none => []

/-- An instruction of the assembly program: an opcode, a push of a constant or of a label's
offset, a label's definition, or the `PUSH<bytes>` placeholder of immutable `id`, zeros until a
deployment links it. -/
inductive Item where
  | op (byte : Nat)
  | push (value : Nat)
  | pushLabel (label : Nat)
  | label (label : Nat)
  | immutable (id bytes : Nat)
  /-- A push of a word of one-byte label offsets, the first label's in the word's highest byte
  of the push: a packed jump table, which `BYTE` picks an entry of. -/
  | pushTable (labels : List Nat)
  /-- Entry `index` of a stride table whose first entry is label `table`: a `JUMPDEST`
  `index` strides past the table's offset. -/
  | entry (table index stride : Nat)
  /-- An opcode with its one-byte immediate: DUPN, SWAPN or EXCHANGE (EIP-8024). -/
  | opImm (byte imm : Nat)
  deriving DecidableEq, Repr

/-- The instruction an item is at a layout that puts each label at `offset`. -/
def Item.expected (offset : Nat → Nat) : Item → Instr
  | .op byte => .op byte
  | .push value => .push value
  | .pushLabel l => .push (offset l)
  | .label _ => .op JUMPDEST
  | .immutable _ _ => .push 0
  | .pushTable labels => .push (bigEndian (labels.map offset))
  | .entry _ _ _ => .op JUMPDEST
  | .opImm byte imm => .opImm byte imm

/-- Whether an item is placed where the layout says at `pc` of `code`: a label at its offset, a
packed table's every offset in one byte, so that the word's bytes are the offsets, a stride table's
entry its index of strides past the table's offset, and an immutable's placeholder a
`PUSH<bytes>` of its width, `1 ≤ bytes ≤ 32`, which a deployment's linking overwrites byte for
byte: a `PUSH0` or a narrower push of zero decodes to the same push but is no placeholder. -/
def Item.placed (code : List Nat) (offset : Nat → Nat) (pc : Nat) : Item → Bool
  | .label l => offset l == pc
  | .immutable _ bytes =>
    decide (1 ≤ bytes) && decide (bytes ≤ 32) && code[pc]? == some (PUSH1 + bytes - 1)
  | .pushTable labels => labels.all (offset · < 256)
  | .entry table index stride => offset table + index * stride == pc
  | _ => true

/-- The checker's walk: decoding `code` from `pc` in lockstep with `items` gives each item's
instruction at the layout `offset`, with each item placed as the layout says (`Item.placed`),
and ends at the end of the code. `stream` is the program's instructions at the offsets the walk reached. -/
inductive Walk (code : List Nat) (offset : Nat → Nat) :
    Nat → List Item → List (Nat × Instr) → Prop
  | nil : Walk code offset code.length [] []
  | cons {pc next : Nat} {item : Item} {items : List Item} {stream : List (Nat × Instr)} :
      decode code pc = some (item.expected offset, next) →
      item.placed code offset pc = true →
      Walk code offset next items stream →
      Walk code offset pc (item :: items) ((pc, item.expected offset) :: stream)

theorem decode_advances {code : List Nat} {pc next : Nat} {instr : Instr}
    (h : decode code pc = some (instr, next)) : pc < next := by
  unfold decode at h
  split at h
  · simp at h
  · repeat' split at h
    all_goals first
      | (simp at h; done)
      | (simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h; omega)

/-- An instruction decodes to an opcode only from its byte, one byte on, when the byte is no
push and takes no immediate. -/
theorem decode_op_inv {code : List Nat} {pc next byte : Nat}
    (h : decode code pc = some (.op byte, next)) :
    code[pc]? = some byte ∧ byte ≠ PUSH0 ∧ ¬(PUSH1 ≤ byte ∧ byte ≤ PUSH32) ∧
      hasImmediate byte = false ∧ next = pc + 1 := by
  unfold decode at h
  split at h
  · simp at h
  · rename_i b hb
    repeat' split at h
    all_goals simp only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq, Instr.op.injEq,
      false_and] at h
    all_goals first
      | (rename_i h0 h1 hi; obtain ⟨rfl, rfl⟩ := h; exact ⟨hb, h0, h1, by simpa using hi, rfl⟩)
      | skip
    all_goals simp_all

/-- An opcode with an immediate decodes from its byte and the next, two bytes on, when the
next byte encodes an operand of it. -/
theorem decode_opImm_inv {code : List Nat} {pc next byte imm : Nat}
    (h : decode code pc = some (.opImm byte imm, next)) :
    code[pc]? = some byte ∧ hasImmediate byte = true ∧ code[pc + 1]? = some imm ∧
      immediateOk byte imm = true ∧ next = pc + 2 := by
  unfold decode at h
  split at h
  · simp at h
  · rename_i b hb
    repeat' split at h
    all_goals simp only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq, Instr.opImm.injEq,
      false_and] at h
    all_goals simp_all

/-- Each item takes at least a byte. -/
theorem walk_length {code : List Nat} {offset : Nat → Nat} {pc : Nat} {items : List Item}
    {stream : List (Nat × Instr)} (w : Walk code offset pc items stream) :
    pc + items.length ≤ code.length := by
  induction w with
  | nil => simp
  | cons decoded _ _ ih =>
    have := decode_advances decoded
    simp only [List.length_cons]
    omega

/-- Linear decoding is the program's instructions at their offsets. -/
theorem walk_decodes {code : List Nat} {offset : Nat → Nat} {pc : Nat} {items : List Item}
    {stream : List (Nat × Instr)} (w : Walk code offset pc items stream) :
    ∀ fuel, items.length < fuel → decodeFrom code fuel pc = stream := by
  induction w with
  | nil =>
    intro fuel h
    cases fuel with
    | zero => simp at h
    | succ fuel =>
      simp [decodeFrom, decode]
  | cons decoded _ _ ih =>
    intro fuel h
    cases fuel with
    | zero => simp at h
    | succ fuel =>
      simp only [List.length_cons] at h
      simp only [decodeFrom, decoded]
      rw [ih fuel (by omega)]

/-- The decoded instructions are the program's items at the layout. -/
theorem walk_instructions {code : List Nat} {offset : Nat → Nat} {pc : Nat} {items : List Item}
    {stream : List (Nat × Instr)} (w : Walk code offset pc items stream) :
    stream.map Prod.snd = items.map (Item.expected offset) := by
  induction w with
  | nil => rfl
  | cons _ _ _ ih => simp [ih]

/-- A defined label's offset holds a `JUMPDEST` that starts an instruction. -/
theorem walk_label {code : List Nat} {offset : Nat → Nat} {pc : Nat} {items : List Item}
    {stream : List (Nat × Instr)} (w : Walk code offset pc items stream) {label : Nat}
    (defined : Item.label label ∈ items) : (offset label, Instr.op JUMPDEST) ∈ stream := by
  induction w with
  | nil => simp at defined
  | @cons pc next item items stream _ labels _ ih =>
    rcases List.mem_cons.1 defined with here | later
    · subst here
      simp only [Item.placed, beq_iff_eq] at labels
      rw [labels]
      simp [Item.expected]
    · exact List.mem_cons_of_mem _ (ih later)

/-- A stride table's entry, its index of strides past the table's offset, holds a `JUMPDEST`
that starts an instruction. -/
theorem walk_entry {code : List Nat} {offset : Nat → Nat} {pc : Nat} {items : List Item}
    {stream : List (Nat × Instr)} (w : Walk code offset pc items stream) {table index stride : Nat}
    (defined : Item.entry table index stride ∈ items) :
    (offset table + index * stride, Instr.op JUMPDEST) ∈ stream := by
  induction w with
  | nil => simp at defined
  | @cons pc next item items stream _ placed _ ih =>
    rcases List.mem_cons.1 defined with here | later
    · subst here
      simp only [Item.placed, beq_iff_eq] at placed
      rw [placed]
      simp [Item.expected]
    · exact List.mem_cons_of_mem _ (ih later)

/-- Every label the program pushes and defines is the offset of a `JUMPDEST` that the code's
linear decoding reaches as an instruction. -/
theorem jump_targets {code : List Nat} {offset : Nat → Nat} {items : List Item}
    {stream : List (Nat × Instr)} (w : Walk code offset 0 items stream) {label : Nat}
    (defined : Item.label label ∈ items) :
    (offset label, Instr.op JUMPDEST) ∈ decodeFrom code (code.length + 1) 0 := by
  have := walk_length w
  rw [walk_decodes w _ (by omega)]
  exact walk_label w defined

/-- Assembly to bytecode is a stage: the program `p`, run at the layout the walk found, and the
code, run by a bytecode semantics that runs its linear decoding, give the same result. -/
theorem stage {A B : Sem} {p : A.Prog} {code : B.Prog} {scope : Call → Prop}
    (bytes : List Nat) (items : List Item) (offset : Nat → Nat) (stream : List (Nat × Instr))
    (run : List (Nat × Instr) → Call → Option Observable)
    (assembly : ∀ call, A.run p call = run stream call)
    (bytecode : ∀ call, B.run code call = run (decodeFrom bytes (bytes.length + 1) 0) call)
    (checked : Walk bytes offset 0 items stream) : Stage A B p code scope := by
  intro call _ obs ran
  have := walk_length checked
  rw [bytecode, walk_decodes checked _ (by omega), ← assembly]
  exact ran

/-! A jump over a label push: `PUSH1 3; JUMP; JUMPDEST; STOP`, with label 0 at offset 3. -/

def example_items : List Item := [.pushLabel 0, .op 0x56, .label 0, .op 0x00]

def example_code : List Nat := [0x60, 3, 0x56, 0x5b, 0x00]

theorem example_walk :
    Walk example_code (fun _ => 3) 0 example_items
      [(0, .push 3), (2, .op 0x56), (3, .op 0x5b), (4, .op 0x00)] :=
  .cons (by rfl) rfl (.cons (by rfl) rfl (.cons (by rfl) rfl (.cons (by rfl) rfl .nil)))

/-- Off by one, the label push misses the label: no walk exists, as the checker reports. -/
theorem example_fault (stream : List (Nat × Instr)) :
    ¬ Walk [0x60, 4, 0x56, 0x5b, 0x00] (fun _ => 3) 0 example_items stream := by
  intro w
  cases w with
  | cons decoded _ _ =>
    simp [decode, bigEndian, Item.expected, PUSH0, PUSH1, PUSH32] at decoded

/-! DUPN of depth 17 (`dup 16`): the immediate 0x80, two bytes on. A JUMPDEST byte or no byte
after DUPN encodes no depth, which the walk refuses. -/

theorem example_dupn :
    Walk [0xe6, 0x80, 0x00] (fun _ => 0) 0 [.opImm DUPN (encodeDepth 17), .op 0x00]
      [(0, .opImm 0xe6 0x80), (2, .op 0x00)] :=
  .cons (by rfl) rfl (.cons (by rfl) rfl .nil)

theorem example_dupn_jumpdest : decode [0xe6, 0x5b] 0 = none := by decide

theorem example_dupn_short : decode [0xe6] 0 = none := by decide

theorem example_exchange : decodePair (encodePair 1 29) = some (1, 29) := by decide

/-- An immutable's placeholder is a push of its width: a 32-byte placeholder walks as PUSH32 of
zeros, and a PUSH0 or PUSH1 0 in its place, which decodes to the same push of zero, has no walk. -/
theorem example_immutable :
    Walk (0x7f :: List.replicate 32 0) (fun _ => 0) 0 [.immutable 0 32] [(0, .push 0)] :=
  .cons (by decide) (by decide) .nil

theorem example_immutable_push0 (stream : List (Nat × Instr)) :
    ¬ Walk [0x5f] (fun _ => 0) 0 [.immutable 0 32] stream := by
  intro w
  cases w with
  | cons _ placed _ => exact absurd placed (by decide)

theorem example_immutable_push1 (stream : List (Nat × Instr)) :
    ¬ Walk [0x60, 0x00] (fun _ => 0) 0 [.immutable 0 32] stream := by
  intro w
  cases w with
  | cons _ placed _ => exact absurd placed (by decide)

/-- A wrong immediate fails: DUPN with 0x81 (depth 18) where the item is depth 17's 0x80 has no
walk, though 0x81 is a valid immediate, as the checker reports. -/
theorem example_dupn_wrong (stream : List (Nat × Instr)) :
    ¬ Walk [0xe6, 0x81, 0x00] (fun _ => 0) 0 [.opImm DUPN (encodeDepth 17), .op 0x00] stream := by
  intro w
  cases w with
  | cons decoded _ _ =>
    have e : decode [0xe6, 0x81, 0x00] 0 = some (.opImm 0xe6 0x81, 2) := by decide
    rw [e] at decoded
    simp [Item.expected, DUPN, encodeDepth] at decoded

/-- A wrong EXCHANGE immediate fails the same way: pair (1, 3)'s byte where (1, 2)'s is due. -/
theorem example_exchange_wrong (stream : List (Nat × Instr)) :
    ¬ Walk [0xe8, encodePair 1 3, 0x00] (fun _ => 0) 0
      [.opImm EXCHANGE (encodePair 1 2), .op 0x00] stream := by
  intro w
  cases w with
  | cons decoded _ _ =>
    have e : decode [0xe8, encodePair 1 3, 0x00] 0 = some (.opImm 0xe8 (encodePair 1 3), 2) := by
      decide
    rw [e] at decoded
    simp only [Item.expected, Option.some.injEq, Prod.mk.injEq, Instr.opImm.injEq] at decoded
    exact absurd decoded.1.2 (by decide)

end SolarTV.Assembly

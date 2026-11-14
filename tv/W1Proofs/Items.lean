import SolarTV.Stages.AssemblyCheck
import SolarTV.EVMIR.Program

/-! EVM IR programs as the assembly items the assembler solves.

`itemsOf` spells an EVM IR program as the assembly the assembler solves: each instruction as
its opcode, a push as a push of its constant, a static jump as a push of its target's label
and the jump, a pushed label as its push, a dynamic jump as `JUMP`, and a `JUMPDEST` label
at the start of each block some pushed label targets. A
block's transfer to the block after it is spelled as `lower_terminator` in
`crates/codegen/src/backend/assembler/assembly/lower.rs` spells it: a final `jump` to the next
block is no instruction, and of a final `jumpi then; jump else` that falls through, only the
`JUMPI` to the other block stays, after an `ISZERO` when `then` is the one that follows. The
EVM IR semantics enters the next block past the end of a block, so the spelling runs the same
blocks. The last block's final `stop` is no instruction either, as `lower_terminator` leaves
it out of runtime code that nothing follows: the code ends there, which halts as STOP does. An
environment read the oracle answers (`.env`) is spelled as the opcode of the mnemonic the
exporter names it with, as solar lowers it. It is partial: an effect outside the EVM's
opcodes or with another arity than its opcode's has no item, so a program outside that scope
fails the check. Every contract's `Assembly` module (w1's and the ones
`milestone/certify.py` writes) evaluates `SolarTV.Assembly.walk` over its bytecode against
these items.

A jump table (`jumpTable`) is spelled as `indexed_jump.rs` lowers it, in the encoding the
bytecode shows (`Spelling`), which `itemsWith` takes for each table in layout order: packed,
a word of one-byte offsets, the first target's in its high byte, that `BYTE` picks the entry the
index numbers from, after adding the zero bytes above it (`PUSH 32-n; ADD; PUSHn table; SWAP1;
BYTE; JUMP`); or a stride table, `PUSH stride; MUL; PUSH entry0; ADD; JUMP` into entry stubs
`JUMPDEST; PUSH target; JUMP` laid out after the last block, `stride` bytes apart, each named by
a label past every block's. The walk checks that each packed offset fits its byte and that each
stub sits its index of strides past the first, so that the pick lands on the entry's target. With
stubs after it, the last block's final `stop` is a `STOP` again. The other encodings, relative
to a base or packed wider than a byte (`-Zpack-wide-jump-tables`, the size objective), have no
spelling, so the check refuses them, as it does a table with no spelling given. EVM IR requires a
table's index to be in range, as every lowering of a switch checks before the jump; out of range
the EVM IR semantics halts, while the bytecode jumps wherever the pick lands. -/

namespace SolarTV.Milestone.W1

open SolarTV.Assembly

/-- The opcode of a stack operation, or `none` for one no opcode reaches: `dup` and `swap` of the
first sixteen words are DUP1 to DUP16 and SWAP1 to SWAP16, deeper ones DUPN and SWAPN with the
depth's immediate up to depth 235, and `exchange` EXCHANGE with its pair's immediate, as solar's
assembler encodes them where the EVM version has EIP-8024's opcodes. Where it has not, the
assembler writes no such opcode and the walk finds none. -/
def stackItem : EVM.Op → Option Item
  | .add => some (.op 0x01) | .mul => some (.op 0x02) | .sub => some (.op 0x03)
  | .div => some (.op 0x04) | .sdiv => some (.op 0x05) | .mod => some (.op 0x06)
  | .smod => some (.op 0x07) | .addmod => some (.op 0x08) | .mulmod => some (.op 0x09)
  | .exp => some (.op 0x0a) | .signextend => some (.op 0x0b)
  | .lt => some (.op 0x10) | .gt => some (.op 0x11) | .slt => some (.op 0x12)
  | .sgt => some (.op 0x13) | .eq => some (.op 0x14) | .iszero => some (.op 0x15)
  | .and => some (.op 0x16) | .or => some (.op 0x17) | .xor => some (.op 0x18)
  | .not => some (.op 0x19) | .byte => some (.op 0x1a) | .shl => some (.op 0x1b)
  | .shr => some (.op 0x1c) | .sar => some (.op 0x1d) | .clz => some (.op 0x1e)
  | .calldatasize => some (.op 0x36) | .returndatasize => some (.op 0x3d)
  | .pop => some (.op 0x50)
  | .push value => some (.push value.toNat)
  | .dup index =>
    if index.val < 16 then some (.op (0x80 + index.val))
    else if depthOk (index.val + 1) then some (.opImm DUPN (encodeDepth (index.val + 1)))
    else none
  | .swap index =>
    if index.val < 16 then some (.op (0x90 + index.val))
    else if depthOk (index.val + 1) then some (.opImm SWAPN (encodeDepth (index.val + 1)))
    else none
  | .exchange first second =>
    if pairOk first.val second.val then some (.opImm EXCHANGE (encodePair first.val second.val))
    else none

/-! The immediates `stackItem` writes decode back to the operation: DUPN and SWAPN to the
depth `index + 1`, EXCHANGE to its pair, each a valid immediate, so the walk's decoding of the
bytes (`decode`) reads the item and nothing else. -/

theorem stackItem_dup_opImm {index : Fin 256} {byte imm : Nat}
    (h : stackItem (.dup index) = some (.opImm byte imm)) :
    byte = DUPN ∧ decodeDepth imm = some (index.val + 1) ∧ immediateOk byte imm = true := by
  simp only [stackItem] at h
  split at h
  · cases h
  · split at h
    · rename_i hd
      cases h
      have := decodeDepth_encodeDepth hd
      exact ⟨rfl, this, by simp [immediateOk, DUPN, EXCHANGE, this]⟩
    · cases h

theorem stackItem_swap_opImm {index : Fin 256} {byte imm : Nat}
    (h : stackItem (.swap index) = some (.opImm byte imm)) :
    byte = SWAPN ∧ decodeDepth imm = some (index.val + 1) ∧ immediateOk byte imm = true := by
  simp only [stackItem] at h
  split at h
  · cases h
  · split at h
    · rename_i hd
      cases h
      have := decodeDepth_encodeDepth hd
      exact ⟨rfl, this, by simp [immediateOk, SWAPN, EXCHANGE, this]⟩
    · cases h

theorem stackItem_exchange_opImm {first second : Fin 32} {byte imm : Nat}
    (h : stackItem (.exchange first second) = some (.opImm byte imm)) :
    byte = EXCHANGE ∧ decodePair imm = some (first.val, second.val) ∧
      immediateOk byte imm = true := by
  simp only [stackItem] at h
  split at h
  · rename_i hp
    cases h
    have := (decodePair_encodePair hp).1
    exact ⟨rfl, this, by simp [immediateOk, this]⟩
  · cases h

/-- The bytes of an item `stackItem` writes with an immediate decode to that item, two bytes on. -/
theorem decode_opImm_of_valid {code : List Nat} {pc byte imm : Nat}
    (hb : code[pc]? = some byte) (hi : code[pc + 1]? = some imm) (hh : hasImmediate byte = true)
    (ok : immediateOk byte imm = true) : decode code pc = some (.opImm byte imm, pc + 2) := by
  have h0 : byte ≠ PUSH0 := by
    intro e; subst e; simp [hasImmediate, PUSH0, DUPN, SWAPN, EXCHANGE] at hh
  have h1 : ¬(PUSH1 ≤ byte ∧ byte ≤ PUSH32) := by
    simp only [hasImmediate, Bool.or_eq_true, beq_iff_eq, DUPN, SWAPN, EXCHANGE] at hh
    simp only [PUSH1, PUSH32]; omega
  simp [decode, hb, hi, h0, h1, hh, ok]

/-- The opcode of a memory instruction, or `none` for a copy or hash, which the program runs
as effects. -/
def memoryItem : EVM.Memory.Op → Option Item
  | .stack op => stackItem op
  | .load => some (.op 0x51)
  | .store => some (.op 0x52)
  | .storeByte => some (.op 0x53)
  | .size => some (.op 0x59)
  | .copy | .hash => none

/-- The opcode of an effect with its arity, or `none` for one that is no opcode. -/
def effectItem : Machine.Effect → Nat → Option Item
  | .address, 0 => some (.op 0x30)
  | .caller, 0 => some (.op 0x33)
  | .callvalue, 0 => some (.op 0x34)
  | .calldataload, 1 => some (.op 0x35)
  | .calldatasize, 0 => some (.op 0x36)
  | .returndatasize, 0 => some (.op 0x3d)
  | .mload, 1 => some (.op 0x51)
  | .mstore, 2 => some (.op 0x52)
  | .mstore8, 2 => some (.op 0x53)
  | .sload, 1 => some (.op 0x54)
  | .sstore, 2 => some (.op 0x55)
  | .msize, 0 => some (.op 0x59)
  | .tload, 1 => some (.op 0x5c)
  | .tstore, 2 => some (.op 0x5d)
  | .keccak256, 2 => some (.op 0x20)
  | .calldatacopy, 3 => some (.op 0x37)
  | .returndatacopy, 3 => some (.op 0x3e)
  | .gas, 0 => some (.op 0x5a)
  | .mcopy, 3 => some (.op 0x5e)
  | .call .call, 7 => some (.op 0xf1)
  | .call .callcode, 7 => some (.op 0xf2)
  | .call .delegatecall, 6 => some (.op 0xf4)
  | .call .staticcall, 6 => some (.op 0xfa)
  -- NOTE: the runtime code's placeholder, a PUSH<bytes> of zeros that the manifest lists, which
  -- the deployment code links with the immutable (`SolarTV.Assembly.link`).
  | .immutable id bytes .word, 0 => some (.immutable id bytes)
  | .codecopy, 3 => some (.op 0x39)
  | .create, 3 => some (.op 0xf0)
  | .create2, 4 => some (.op 0xf5)
  | .log n, arity => if n ≤ 4 ∧ arity = n + 2 then some (.op (0xa0 + n)) else none
  -- The oracle's environment reads, by the mnemonic the exporter names each with.
  | .env "balance", 1 => some (.op 0x31)
  | .env "origin", 0 => some (.op 0x32)
  | .env "codesize", 0 => some (.op 0x38)
  | .env "gasprice", 0 => some (.op 0x3a)
  | .env "extcodesize", 1 => some (.op 0x3b)
  | .env "extcodehash", 1 => some (.op 0x3f)
  | .env "blockhash", 1 => some (.op 0x40)
  | .env "coinbase", 0 => some (.op 0x41)
  | .env "timestamp", 0 => some (.op 0x42)
  | .env "number", 0 => some (.op 0x43)
  | .env "prevrandao", 0 => some (.op 0x44)
  | .env "gaslimit", 0 => some (.op 0x45)
  | .env "chainid", 0 => some (.op 0x46)
  | .env "selfbalance", 0 => some (.op 0x47)
  | .env "basefee", 0 => some (.op 0x48)
  | .env "blobhash", 1 => some (.op 0x49)
  | .env "blobbasefee", 0 => some (.op 0x4a)
  | _, _ => none

/-- The items of an instruction. -/
def instrItems : EVM.Program.Instr → Option (List Item)
  | .op op => (memoryItem op).map ([·])
  | .effect effect arity => (effectItem effect arity).map ([·])
  | .jump target => some [.pushLabel target, .op 0x56]
  | .jumpi target => some [.pushLabel target, .op 0x57]
  | .pushLabel target => some [.pushLabel target]
  | .jumpDyn => some [.op 0x56]
  | .jumpiDyn => some [.op 0x57]
  -- NOTE: a jump table's items depend on its encoding, which `tableItems` spells.
  | .jumpTable _ => none
  | .stop => some [.op 0x00]
  | .ret => some [.op 0xf3]
  | .revert => some [.op 0xfd]
  | .invalid => some [.op 0xfe]

/-- How the assembler encoded a jump table, as the bytecode shows: `packed`, one-byte offsets
in a word that `BYTE` picks from, or `stride`, entry stubs whose target pushes are `width`
bytes wide. -/
inductive Spelling where
  | packed
  | stride (width : Nat)
  deriving DecidableEq, Repr

def Spelling.isStride : Spelling → Bool
  | .stride _ => true
  | .packed => false

/-- The jump tables' spellings not yet used, the label of the next stride table's first entry,
and the entry stubs of the stride tables so far, in layout order. -/
structure Tables where
  spellings : List Spelling
  fresh : Nat
  stubs : List Item

/-- The entry stubs of a stride table from entry `index`: `JUMPDEST; PUSH target; JUMP`. -/
def entries (table stride : Nat) : Nat → List Nat → List Item
  | _, [] => []
  | index, target :: rest =>
    [.entry table index stride, .pushLabel target, .op 0x56] ++ entries table stride (index + 1) rest

/-- The items of a jump table in the next spelling, as `indexed_jump::lower` writes it. -/
def tableItems (targets : List Nat) (t : Tables) : Option (List Item × Tables) :=
  match t.spellings with
  | [] => none
  | .packed :: rest =>
    if 2 ≤ targets.length ∧ targets.length ≤ 32 then
      -- PUSH 32-n; ADD (when n < 32); PUSHn table; SWAP1; BYTE; JUMP
      some ((if targets.length < 32 then [.push (32 - targets.length), .op 0x01] else [])
          ++ [.pushTable targets, .op 0x90, .op 0x1a, .op 0x56], { t with spellings := rest })
    else none
  | .stride width :: rest =>
    if 1 ≤ width ∧ width ≤ 32 ∧ targets ≠ [] then
      -- PUSH stride; MUL; PUSH entry0; ADD; JUMP
      some ([.push (width + 3), .op 0x02, .pushLabel t.fresh, .op 0x01, .op 0x56],
        { spellings := rest, fresh := t.fresh + 1,
          stubs := t.stubs ++ entries t.fresh (width + 3) 0 targets })
    else none

/-- The items of an instruction, a jump table in the next spelling. -/
def instrTableItems (t : Tables) : EVM.Program.Instr → Option (List Item × Tables)
  | .jumpTable targets => tableItems targets t
  | instr => (instrItems instr).map (·, t)

/-- The items of a list of instructions. -/
def instrsItems : List EVM.Program.Instr → Option (List Item)
  | [] => some []
  | instr :: rest => do
    let head ← instrItems instr
    let tail ← instrsItems rest
    pure (head ++ tail)

/-- The items of a block, given the block that follows it in the layout (none for the last
block) and whether the code ends after it: a final transfer to `next` falls through instead of
jumping, and a final stop where the code ends is the end of the code. -/
def blockItems (next : Option Nat) (ends : Bool) (t : Tables) :
    List EVM.Program.Instr → Option (List Item × Tables)
  | [] => some ([], t)
  | [.stop] =>
    -- the last block's stop: the code ends
    if ends then some ([], t)
    -- STOP
    else some ([.op 0x00], t)
  | [.jump target] =>
    -- jump next
    if next = some target then some ([], t)
    -- push target; JUMP
    else some ([.pushLabel target, .op 0x56], t)
  | [.jumpi yes, .jump no] =>
    -- push yes; JUMPI
    if next = some no then some ([.pushLabel yes, .op 0x57], t)
    -- ISZERO; push no; JUMPI
    else if next = some yes then some ([.op 0x15, .pushLabel no, .op 0x57], t)
    -- push yes; JUMPI; push no; JUMP
    else some ([.pushLabel yes, .op 0x57, .pushLabel no, .op 0x56], t)
  | instr :: rest => do
    let (head, t) ← instrTableItems t instr
    let (tail, t) ← blockItems next ends t rest
    pure (head ++ tail, t)

/-- The blocks' items in layout order from block `index`, each with the block after it; the code
ends after the last block when `ends`. -/
def bodiesOf (ends : Bool) : Nat → Tables → List (List EVM.Program.Instr) →
    Option (List (List Item) × Tables)
  | _, t, [] => some ([], t)
  | index, t, block :: rest => do
    let (body, t) ←
      blockItems (if rest.isEmpty then none else some (index + 1)) (ends && rest.isEmpty) t block
    let (tail, t) ← bodiesOf ends (index + 1) t rest
    pure (body :: tail, t)

/-- The labels some item pushes, a packed table's each. -/
def pushedLabels (bodies : List (List Item)) : List Nat :=
  bodies.flatMap fun body => body.flatMap fun
    | .pushLabel label => [label]
    | .pushTable labels => labels
    | _ => []

/-- Each body from block `index` on, opening with its label when some item pushes it. -/
def labelBodies (pushed : List Nat) : Nat → List (List Item) → List Item
  | _, [] => []
  | index, body :: rest =>
    (if index ∈ pushed then [.label index] else []) ++ body ++ labelBodies pushed (index + 1) rest

/-- The program as assembly items in layout order, each block some item jumps to opening with
its label, its jump tables in `spellings`, one each in layout order, and the stride tables'
entry stubs after the last block. -/
def itemsWith (spellings : List Spelling) (p : EVM.Program.Program) : Option (List Item) := do
  let (bodies, t) ←
    bodiesOf (!spellings.any Spelling.isStride) 0 ⟨spellings, p.blocks.length, []⟩ p.blocks
  if t.spellings.isEmpty then
    pure (labelBodies (pushedLabels (bodies ++ [t.stubs])) 0 bodies ++ t.stubs)
  else none

/-- The program as assembly items, without jump tables. -/
def itemsOf (p : EVM.Program.Program) : Option (List Item) := itemsWith [] p

/-! Refusals: a jump table without its encoding has no items, and a packed table whose offsets do
not fit their bytes is placed nowhere, so no walk accepts code for it (`SolarTV.Assembly.no_walk`). -/

theorem table_unspelled : itemsOf ⟨[[.jumpTable [1, 1]], [.stop]]⟩ = none := by decide

/-- A packed table: the bytes above its two entries added to the index, then the BYTE pick. -/
theorem table_spelled :
    itemsWith [.packed] ⟨[[.jumpTable [1, 1]], [.stop]]⟩ =
      some [.push 30, .op 0x01, .pushTable [1, 1], .op 0x90, .op 0x1a, .op 0x56, .label 1] := by
  decide

/-- A stride table: its entry stubs after the last block, whose final stop is a STOP again. -/
theorem table_stride :
    itemsWith [.stride 2] ⟨[[.jumpTable [1, 1]], [.stop]]⟩ =
      some [.push 5, .op 0x02, .pushLabel 2, .op 0x01, .op 0x56, .label 1, .op 0x00,
        .entry 2 0 5, .pushLabel 1, .op 0x56, .entry 2 1 5, .pushLabel 1, .op 0x56] := by
  decide

/-- A table of one entry is never packed. -/
theorem table_too_few : itemsWith [.packed] ⟨[[.jumpTable [1]], [.stop]]⟩ = none := by decide

/-- An offset of 256 does not fit its byte. -/
theorem table_wide (pc : Nat) : (Item.pushTable [1]).placed [] (fun _ => 256) pc = false := rfl

end SolarTV.Milestone.W1

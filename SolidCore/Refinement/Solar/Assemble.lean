import SolidCore.Refinement.Evm.Wide
import SolarTV.Composition
import SolarTV.Stages.AssemblyCheck
import SolidCore.Refinement.Solar.AssembleStackN

/-!
# EVM IR to bytecode, once for every program

solar's last backend stage lays out the final EVM IR program as assembly and assembles it to
bytecode. This file proves that stage once, for every program and every bytecode a decidable
check accepts: `stage_of_check_env` gives `Stage (evmirSem o) ethLib p code scope` on every call,
with any value, from any storage, from `check p code cert = true`, for every oracle when the
certificate says the program reads neither the caller nor a hash (`stage_of_check_all`,
`stage_of_check`), and otherwise for every oracle whose CALLER is the caller of EthLib's calls and
whose hash is EthLib's KECCAK256 (`OracleOk`, `stage_of_check_eth`).

* `lower` is the lowering of EVM IR to assembly items, as solar's assembler lays it out:
  each block is its instructions, with a label (a JUMPDEST) when the code pushes it; a jump is
  a push of its label and the jump, except that a final jump to the next block is left out (the
  code falls into it), so is the last block's final STOP (the code ends), and a final
  `jumpi t; jump e` with `t` the next block that the certificate lists as turned is
  `ISZERO; PUSH e; JUMPI`, falling into `t`. A pushed return label is a PUSH of its block's
  offset and a dynamic jump is JUMP.
* `check` is the checker: the code's linear decoding is the lowered program at the layout of
  the certificate (`SolarTV.Assembly.walk`, as -Zvalidate-assembly decodes it), each label is
  a valid jump destination of the code by EthLib's own analysis, stack reads never pass the
  entry heights of the certificate, each memory access (MSTORE, KECCAK256, LOGn, RETURN,
  REVERT) has a constant offset and size (pushed, or a DUP of a pushed one) below the
  certificate's memory bound, and the code is
  below 2^32 bytes. Each block has a potential, a bound on the items its runs execute (the
  certificate's, or by default the items from it to the end of the layout): each item takes one
  unit, and a jump or a fall goes to a block whose potential is at most what is left, so a run
  executes at most the first block's potential in items, and gas for 22100 per item (the most
  SSTORE costs, and a bound the check puts on each hash and log) plus the memory fits in the
  call's 10M. With the default potentials this is every jump going forward.
* Return labels: SolarTV's label of a block is its number where the code has its offset, so the
  checker types the stack words (`Ty`): data, the same word on both sides, which every operation
  that computes, stores, hashes, logs or branches on must read; a return label, which only
  PUSH (from `pushLabel`), DUP, SWAP, POP and a dynamic jump touch; or unknown. The certificate
  gives each block's entry types and the blocks a return label can name (`rets`); a dynamic
  jump needs a return label on top and checks the jump to each of them, and every jump checks
  that its stack has the types its target claims.
* The proof is a simulation of SolarTV's EVM IR semantics by EthLib's interpreter, opcode by
  opcode, with EthLib's own rules for each opcode (`EthLib.Execution.Evm.Logic`), relating the two
  stacks word by word at their types. SolarTV's storage is the storage of EthLib's account of
  the frame throughout: SLOAD reads it and SSTORE writes it, at any price EthLib charges for a
  cold or warm slot; SolarTV's logs are EthLib's, topic by topic and byte by byte.

The fragment: PUSH, POP, DUP, SWAP, ADD, MUL, SUB, DIV, MOD, LT, GT, EQ, ISZERO, AND, OR, XOR, NOT, BYTE,
SHL, SHR, CALLDATASIZE, CALLVALUE, CALLDATALOAD, CALLER, KECCAK256, MSTORE, SLOAD, SSTORE,
LOG0 to LOG4, JUMP (static and to a return label), JUMPI, STOP, RETURN and REVERT. Anything
else (a conditional jump to a label on the stack, a jump table, ...) makes the check false.
-/

namespace SolidCore.Refinement.Solar.Assemble

open SolarTV.Assembly
open EthLib.Base EthLib.Execution EthLib.Execution.Evm EthLib.Execution.Evm.Logic GasCosts

abbrev Instr := SolarTV.EVM.Program.Instr
abbrev Program := SolarTV.EVM.Program.Program
abbrev Word := EvmRules.Word

/-! ## The certificate -/

/-- What the checker knows of a stack word: data (`some false`), the same word on both sides; a
return label (`some true`), a block number in SolarTV where the code has the block's offset; or
nothing (`none`), a word the block never reads. -/
abbrev Ty := Option Bool

/-- What the checker needs beside the program and the code: each block's offset in the code
(the layout), the stack height each block needs on entry, a bound on memory, the blocks whose
final branch the assembler turned around, a bound on the items each block's runs execute, which
words are return labels on each block's entry, the blocks an internal call returns to, and
whether the program reads the caller or hashes. -/
structure Cert where
  offsets : List Nat
  needs : List Nat
  top : Nat
  /-- The blocks whose final `jumpi t; jump e`, with `t` the next block, solar's assembler lays
  out turned around, as `ISZERO; PUSH e; JUMPI` falling into `t` (what it does for a `JumpI` terminator
  whose then block is next; the exported program cannot tell it from a `push t; jumpi` that
  the assembler keeps). -/
  turned : List Nat := []
  /-- For each block, a bound on the items any run from its entry executes (its potential), or
  empty for the items from the block to the end of the layout, which bounds them when every
  jump goes forward. -/
  costs : List Nat := []
  /-- For each block, what the words on top of its entry stack are (`Ty`), the rest unknown;
  empty for a block that reads nothing it does not push. -/
  types : List (List Ty) := []
  /-- The blocks a pushed label names, where a dynamic jump may go: each `pushLabel` names one. -/
  rets : List Nat := []
  /-- Whether the program reads CALLER and hashes with KECCAK256, which holds only under an oracle
  whose caller and hash are EthLib's (`OracleOk`). -/
  env : Bool := false
  /-- Whether the program reads the block or the transaction (TIMESTAMP, NUMBER, CHAINID,
  COINBASE, GASLIMIT, GASPRICE, ORIGIN), which holds only under an oracle whose reads are those of
  EthLib's environment of the call (`EnvOk`). -/
  reads : Bool := false
  /-- Whether the program makes STATICCALLs, which the checker cuts at (`AssembleCutSim.blockOkC`)
  and only the checker of runs with calls (`AssembleCutCall`) accepts, under a runner of messages
  meeting `AssembleCallCut.StaticOk`. -/
  calls : Bool := false
  deriving Repr

def Cert.offset (c : Cert) (b : Nat) : Nat := c.offsets.getD b 0

def Cert.need (c : Cert) (b : Nat) : Nat := c.needs.getD b 0

def Cert.entry (c : Cert) (b : Nat) : List Ty := c.types.getD b []

/-! ## Lowering EVM IR to assembly -/

/-- The opcode of each stack operation of the fragment. `dup` and `swap` take a `Fin 256` position,
as SolarTV's EVM IR does; only DUP1 to DUP16 and SWAP1 to SWAP16 are one-byte opcodes, so a deeper
position (DUPN and SWAPN, which take an immediate) is outside the fragment. -/
def opByte : SolarTV.EVM.Op → Option Nat
  | .add => some 0x01 | .mul => some 0x02 | .sub => some 0x03 | .div => some 0x04
  | .mod => some 0x06 | .lt => some 0x10 | .gt => some 0x11 | .slt => some 0x12 | .sgt => some 0x13
  | .eq => some 0x14 | .iszero => some 0x15 | .and => some 0x16 | .or => some 0x17
  | .xor => some 0x18 | .not => some 0x19 | .byte => some 0x1a | .shl => some 0x1b
  | .shr => some 0x1c
  | .calldatasize => some 0x36 | .pop => some 0x50
  | .dup i => if i.val < 16 then some (0x80 + i.val) else none
  | .swap i => if i.val < 16 then some (0x90 + i.val) else none
  | _ => none

/-- The environment reads of the fragment, by the name the exporter gives each: its opcode and
the word it reads in EthLib's environment of the call (`Target.blockEnv` and `Target.txEnv`),
the oracle's answer under `EnvOk`. -/
def envRead : String → Option (Nat × Nat)
  | "origin" => some (0x32, 0x2000)
  | "gasprice" => some (0x3a, 0)
  | "coinbase" => some (0x41, 0)
  | "timestamp" => some (0x42, 1)
  | "number" => some (0x43, 1)
  | "gaslimit" => some (0x45, 30000000)
  | "chainid" => some (0x46, 1)
  | _ => none

/-- The assembly items of an instruction. Outside the fragment it is INVALID, which the check
rejects. -/
def lowerInstr : Instr → List Item
  | .op (.stack (.push v)) => [.push v.toNat]
  | .op (.stack op) => [.op ((opByte op).getD 0xfe)]
  | .op .store => [.op 0x52]
  | .op .load => [.op 0x51]
  | .op _ => [.op 0xfe]
  | .effect .callvalue _ => [.op 0x34]
  | .effect .calldataload _ => [.op 0x35]
  | .effect .calldatasize _ => [.op 0x36]
  | .effect .caller _ => [.op 0x33]
  | .effect .address _ => [.op 0x30]
  | .effect .gas _ => [.op 0x5a]
  | .effect (.env name) _ => [.op (((envRead name).map Prod.fst).getD 0xfe)]
  | .effect .keccak256 _ => [.op 0x20]
  | .effect (.log n) _ => [.op (if n ≤ 4 then 0xa0 + n else 0xfe)]
  | .effect .sload _ => [.op 0x54]
  | .effect .sstore _ => [.op 0x55]
  | .effect .calldatacopy _ => [.op 0x37]
  | .effect .returndatasize _ => [.op 0x3d]
  | .effect .returndatacopy _ => [.op 0x3e]
  | .effect (.call .staticcall) _ => [.op 0xfa]
  | .effect _ _ => [.op 0xfe]
  | .jump t => [.pushLabel t, .op 0x56]
  | .jumpi t => [.pushLabel t, .op 0x57]
  | .pushLabel t => [.pushLabel t]
  | .jumpDyn => [.op 0x56]
  | .jumpiDyn => [.op 0xfe]
  | .jumpTable _ => [.op 0xfe]
  | .stop => [.op 0x00]
  | .ret => [.op 0xf3]
  | .revert => [.op 0xfd]
  | .invalid => [.op 0xfe]

/-- The else block of block `b`'s final `jumpi t; jump e` when the certificate lists `b` as turned and `t`
is the next block: the code tests the condition's `ISZERO`, jumps to `e` and falls into `t`. -/
def turnedElse (c : Cert) (b : Nat) : Instr → List Instr → Option Nat
  | .jumpi t, [.jump e] => if c.turned.contains b && t == b + 1 then some e else none
  | _, _ => none

/-- Whether the assembler leaves out an instruction that ends block `b`: a jump to the next
block, which the code falls into, or the last block's STOP, where the code ends. -/
def dropped (p : Program) (b : Nat) : Instr → List Instr → Bool
  | .jump t, [] => t == b + 1
  | .stop, [] => b + 1 == p.blocks.length
  | _, _ => false

/-- The items of block `b`'s instructions, as solar's assembler lays them out: each
instruction's items, except that a final jump to the next block and the last block's final STOP
are left out and a turned final branch is `ISZERO; PUSH e; JUMPI`. -/
def lowerInstrs (p : Program) (c : Cert) (b : Nat) : List Instr → List Item
  | [] => []
  | i :: rest =>
    match turnedElse c b i rest with
    | some e => [.op 0x15, .pushLabel e, .op 0x57]
    | none => if dropped p b i rest then [] else lowerInstr i ++ lowerInstrs p c b rest

/-- The items of the blocks' instructions from block `b`, without labels. -/
def bodies (p : Program) (c : Cert) : Nat → List (List Instr) → List Item
  | _, [] => []
  | b, instrs :: rest => lowerInstrs p c b instrs ++ bodies p c (b + 1) rest

/-- Whether the code pushes block `b`'s label, to jump to it or to return to it, so that the
block has one. -/
def isTarget (p : Program) (c : Cert) (b : Nat) : Bool :=
  (bodies p c 0 p.blocks).contains (.pushLabel b)

/-- A block's items: its label when a jump targets it, then its instructions. -/
def lowerBlock (p : Program) (c : Cert) (b : Nat) (instrs : List Instr) : List Item :=
  (if isTarget p c b then [.label b] else []) ++ lowerInstrs p c b instrs

/-- The items of the blocks from block `b`, in layout order. -/
def lowerFrom (p : Program) (c : Cert) : Nat → List (List Instr) → List Item
  | _, [] => []
  | b, instrs :: rest => lowerBlock p c b instrs ++ lowerFrom p c (b + 1) rest

/-- The assembly program of an EVM IR program. -/
def lower (p : Program) (c : Cert) : List Item := lowerFrom p c 0 p.blocks

/-! ## Stack types -/

/-- What the checker knows of the word at depth `i`: nothing below the words it lists. -/
def tyAt (ty : List Ty) (i : Nat) : Ty := ty.getD i none

/-- The top `n` words are data. -/
def isData (ty : List Ty) (n : Nat) : Bool := (List.range n).all fun i => tyAt ty i == some false

/-- What `known` types covers what `want` claims: each word `want` types, `known` types the
same. -/
def tyLe (known want : List Ty) : Bool :=
  (List.range want.length).all fun i => tyAt want i == none || tyAt want i == tyAt known i

/-- The types after SWAP of the top word and the word at depth `i + 1`. -/
def tySwap (ty : List Ty) (i : Nat) : List Ty :=
  List.ofFn (n := max ty.length (i + 2)) fun j =>
    if j.val = 0 then tyAt ty (i + 1) else if j.val = i + 1 then tyAt ty 0 else tyAt ty j.val

/-! ## The checker -/

/-- Block `t`'s potential: the certificate's, or the items from it to the end of the layout. -/
def cost (p : Program) (c : Cert) (t : Nat) : Nat :=
  if c.costs.isEmpty then (lowerFrom p c t (p.blocks.drop t)).length else c.costs.getD t 0

/-- The items a block's label takes. -/
def labelItems (p : Program) (c : Cert) (t : Nat) : Nat := if isTarget p c t then 1 else 0

/-- The bytes of the code. -/
def bytesOf (code : ByteArray) : List Nat := code.data.toList.map (·.toNat)

/-- The stack height a stack operation of the fragment needs, and the height after it, from
height `h`. -/
def stackNeed : SolarTV.EVM.Op → Option (Nat × Int)
  | .add | .mul | .sub | .div | .mod | .lt | .gt | .slt | .sgt | .eq | .and | .or | .xor | .byte
  | .shl | .shr => some (2, -1)
  | .iszero | .not => some (1, 0)
  | .calldatasize => some (0, 1)
  | .pop => some (1, -1)
  | .dup i => if i.val < 16 then some (i.val + 1, 1) else none
  | .swap i => if i.val < 16 then some (i.val + 2, 0) else none
  | _ => none

/-- A jump to block `t` with a stack of at least `h` words typed `ty` and potential `k` left: `t` is a
labelled block, finds the height and the types it needs, and its potential is at most `k`. -/
def jumpOk (p : Program) (c : Cert) (t h : Nat) (ty : List Ty) (k : Nat) : Bool :=
  decide (t < p.blocks.length) && isTarget p c t && decide (c.need t ≤ h) && tyLe ty (c.entry t) &&
    decide (cost p c t ≤ k)

/-- Block `b` falls into the next one with a stack of at least `h` words typed `ty` and potential
`k` left. -/
def fallOk (p : Program) (c : Cert) (b h : Nat) (ty : List Ty) (k : Nat) : Bool :=
  (decide (p.blocks.length ≤ b + 1) || decide (c.need (b + 1) ≤ h)) && tyLe ty (c.entry (b + 1)) &&
    decide (cost p c (b + 1) ≤ k)

/-- A memory range of constant offset and size within the certificate's bound. -/
def rangeOk (c : Cert) (o s : Word) : Bool := decide (s.toNat = 0) || decide (o.toNat + s.toNat ≤ c.top)

/-- The constants on top of the stack after DUP of the word at depth `i`, from the constants
`known` on top before it: that word, when it is one of them, on top of the constant below it. -/
def dupKnown (known : List Word) (i : Nat) : List Word :=
  match known[i]? with
  | some v => v :: known.take 1
  | none => []

/-- The check of one instruction from a stack of at least `h` words whose top words are
`known`, constants just pushed, typed `ty`, with potential `k`, and `ok` for the rest of the block:
each item takes one unit of potential, each instruction finds the words it reads, as data
where it computes with them, each memory access has constant operands within `top`, each
jump goes to a labelled block (`jumpOk`), and a dynamic jump to a return label goes to a
block the certificate lists, each of which it checks. -/
def blockStep (p : Program) (c : Cert) (ok : Nat → List Word → List Ty → Nat → Bool) :
    Nat → List Word → List Ty → Nat → Instr → Bool
  | h, known, ty, k, .op (.stack op) =>
    match op with
    | .push v => decide (1 ≤ k) && ok (h + 1) (v :: known.take 1) (some false :: ty) (k - 1)
    | .dup i => decide (1 ≤ k) && decide (i.val < 16) && decide (i.val + 1 ≤ h) &&
      ok (h + 1) (dupKnown known i.val) (tyAt ty i.val :: ty) (k - 1)
    | .swap i => decide (1 ≤ k) && decide (i.val < 16) && decide (i.val + 2 ≤ h) &&
      ok h [] (tySwap ty i.val) (k - 1)
    | .pop => decide (1 ≤ k) && decide (1 ≤ h) && ok (h - 1) [] ty.tail (k - 1)
    | op =>
      match stackNeed op with
      | some (need, d) => decide (1 ≤ k) && decide (need ≤ h) && isData ty need &&
          ok (h + d).toNat [] (some false :: ty.drop need) (k - 1)
      | none => false
  | h, known, ty, k, .op .store =>
    match known with
    | o :: _ => decide (1 ≤ k) && decide (2 ≤ h) && decide (o.toNat + 32 ≤ c.top) && isData ty 2 &&
      ok (h - 2) [] (ty.drop 2) (k - 1)
    | [] => false
  | h, _, ty, k, .effect .callvalue 0 => decide (1 ≤ k) && ok (h + 1) [] (some false :: ty) (k - 1)
  | h, _, ty, k, .effect .calldatasize 0 => decide (1 ≤ k) && ok (h + 1) [] (some false :: ty) (k - 1)
  | h, _, ty, k, .effect .caller 0 =>
    c.env && decide (1 ≤ k) && ok (h + 1) [] (some false :: ty) (k - 1)
  | h, _, ty, k, .effect .calldataload 1 => decide (1 ≤ k) && decide (1 ≤ h) && isData ty 1 &&
    ok h [] (some false :: ty.drop 1) (k - 1)
  | h, _, ty, k, .effect .sload 1 => decide (1 ≤ k) && decide (1 ≤ h) && isData ty 1 &&
    ok h [] (some false :: ty.drop 1) (k - 1)
  | h, _, ty, k, .effect .sstore 2 => decide (1 ≤ k) && decide (2 ≤ h) && isData ty 2 &&
    ok (h - 2) [] (ty.drop 2) (k - 1)
  | h, known, ty, k, .effect .keccak256 2 =>
    match known with
    | o :: s :: _ => c.env && decide (1 ≤ k) && decide (2 ≤ h) && isData ty 2 && rangeOk c o s &&
      decide (keccak256Cost s ≤ 22100) && ok (h - 1) [] (some false :: ty.drop 2) (k - 1)
    | _ => false
  | h, known, ty, k, .effect (.log n) a =>
    match known with
    | o :: s :: _ => decide (n ≤ 4) && decide (a = n + 2) && decide (1 ≤ k) && decide (n + 2 ≤ h) &&
      isData ty (n + 2) && rangeOk c o s && decide (logCost n s ≤ 22100) &&
      ok (h - (n + 2)) [] (ty.drop (n + 2)) (k - 1)
    | _ => false
  | h, _, ty, k, .jump t => decide (2 ≤ k) && jumpOk p c t h ty (k - 2)
  | h, _, ty, k, .jumpi t =>
    decide (2 ≤ k) && decide (1 ≤ h) && isData ty 1 && jumpOk p c t (h - 1) ty.tail (k - 2) &&
      ok (h - 1) [] ty.tail (k - 2)
  | h, _, ty, k, .pushLabel t =>
    decide (1 ≤ k) && c.rets.contains t && decide (t < 2 ^ 32) && ok (h + 1) [] (some true :: ty) (k - 1)
  | h, _, ty, k, .jumpDyn =>
    decide (1 ≤ k) && decide (1 ≤ h) && tyAt ty 0 == some true &&
      c.rets.all fun t => jumpOk p c t (h - 1) ty.tail (k - 1)
  | _, _, _, _, .stop => true
  | _, known, ty, _, .ret | _, known, ty, _, .revert =>
    match known with
    | o :: s :: _ => isData ty 2 && rangeOk c o s
    | _ => false
  | _, _, _, _, _ => false

/-- The check of block `b`'s instructions as `lowerInstrs` lays them out: each instruction by
`blockStep`, a turned branch jumps to its else block and falls into the next one, a left out
jump falls into the next block, and the end of the block falls through to the next one. -/
def blockOk (p : Program) (c : Cert) (b : Nat) : Nat → List Word → List Ty → Nat → List Instr → Bool
  | h, _, ty, k, [] => fallOk p c b h ty k
  | h, known, ty, k, i :: rest =>
    match turnedElse c b i rest with
    | some e =>
      decide (3 ≤ k) && decide (1 ≤ h) && isData ty 1 && jumpOk p c e (h - 1) ty.tail (k - 3) &&
        fallOk p c b (h - 1) ty.tail (k - 3)
    | none =>
      if dropped p b i rest then
        match i with
        | .stop => true
        | _ => fallOk p c b h ty k
      else blockStep p c (fun h known ty k => blockOk p c b h known ty k rest) h known ty k i

/-- Every block checks from the height and the types it needs, with its potential less its
label's item. -/
def blocksOk (p : Program) (c : Cert) : Nat → List (List Instr) → Bool
  | _, [] => true
  | b, instrs :: rest =>
    decide (labelItems p c b ≤ cost p c b) &&
      blockOk p c b (c.need b) [] (c.entry b) (cost p c b - labelItems p c b) instrs &&
      blocksOk p c (b + 1) rest

/-- Every labelled block's offset is a valid jump destination of the code. -/
def labelsValid (p : Program) (c : Cert) (code : ByteArray) : Bool :=
  (List.range p.blocks.length).all fun b =>
    !isTarget p c b || isValidJumpDest (validJumpDestinations code) (c.offset b)

/-- The checker. -/
def check (p : Program) (code : ByteArray) (c : Cert) : Bool :=
  (walk (bytesOf code) c.offset 0 (lower p c)).isSome && blocksOk p c 0 p.blocks &&
    labelsValid p c code && decide (c.need 0 = 0) && decide (c.top % 32 = 0) &&
    decide (cost p c 0 ≤ 1000) && decide (c.top ≤ 2 ^ 32) &&
    decide (22100 * cost p c 0 + memoryGasCost c.top ≤ 10000000) && decide (code.size < 2 ^ 32)

/-! ## Decoding -/

theorem length_bytesOf (code : ByteArray) : (bytesOf code).length = code.size := by
  unfold bytesOf
  rw [List.length_map, Array.length_toList]
  rfl

theorem getElem?_bytesOf {code : ByteArray} {pc byte : Nat}
    (h : (bytesOf code)[pc]? = some byte) :
    ∃ hlt : pc < code.size, code[pc] = UInt8.ofNat byte := by
  unfold bytesOf at h
  rw [List.getElem?_map] at h
  obtain ⟨u, hu, rfl⟩ := Option.map_eq_some_iff.1 h
  rw [Array.getElem?_toList, Array.getElem?_eq_some_iff] at hu
  obtain ⟨hlt, hu⟩ := hu
  refine ⟨hlt, ?_⟩
  rw [ByteArray.getElem_eq_getElem_data, hu]
  simp

theorem byteAt_toNat (code : ByteArray) (i : Nat) :
    (byteAt code i).toNat = (bytesOf code).getD i 0 := by
  unfold byteAt
  rw [List.getD_eq_getElem?_getD]
  split
  · rename_i h
    have h' : i < (bytesOf code).length := by rw [length_bytesOf]; exact h
    rw [List.getElem?_eq_getElem h']
    simp only [bytesOf, List.getElem_map, Array.getElem_toList, Option.getD_some]
    rfl
  · rename_i h
    rw [List.getElem?_eq_none (by rw [length_bytesOf]; omega)]
    rfl

theorem decode_op {code : List Nat} {pc next byte : Nat}
    (h : decode code pc = some (.op byte, next)) : code[pc]? = some byte ∧ next = pc + 1 := by
  obtain ⟨hb, -, -, -, hn⟩ := decode_op_inv h
  exact ⟨hb, hn⟩

theorem decode_push {code : List Nat} {pc next v : Nat}
    (h : decode code pc = some (.push v, next)) :
    ∃ byte, code[pc]? = some byte ∧
      ((byte = PUSH0 ∧ v = 0 ∧ next = pc + 1) ∨
       (PUSH1 ≤ byte ∧ byte ≤ PUSH32 ∧ next = pc + 1 + (byte - PUSH1 + 1) ∧
        next ≤ code.length ∧ v = bigEndian ((code.drop (pc + 1)).take (byte - PUSH1 + 1)))) := by
  unfold decode at h
  split at h
  · cases h
  · rename_i b hb
    refine ⟨b, hb, ?_⟩
    by_cases h0 : b = PUSH0
    · rw [if_pos h0] at h
      simp only [Option.some.injEq, Prod.mk.injEq, Instr.push.injEq] at h
      exact .inl ⟨h0, h.1.symm, h.2.symm⟩
    · by_cases h1 : PUSH1 ≤ b ∧ b ≤ PUSH32
      · rw [if_neg h0, if_pos h1] at h
        split at h
        · simp only [Option.some.injEq, Prod.mk.injEq, Instr.push.injEq] at h
          exact .inr ⟨h1.1, h1.2, h.2.symm, by omega, h.1.symm⟩
        · cases h
      · rw [if_neg h0, if_neg h1] at h
        repeat' split at h
        all_goals simp at h

theorem decode_pushByte : ∀ b : Fin 32,
    Op.decode (UInt8.ofNat (0x60 + b.val)) = some (.push ⟨b.val + 1, by omega⟩) := by
  decide

/-- The bytes PUSHn reads are its immediate as the checker decodes it. -/
theorem pushData_eq {code : ByteArray} {pc n : Nat} (h : pc + 1 + n ≤ code.size) :
    pushData code pc n =
      BitVec.ofNat 256 (bigEndian (((bytesOf code).drop (pc + 1)).take n)) := by
  unfold pushData bytesToNat bigEndian
  congr 1
  rw [← List.foldl_map (f := UInt8.toNat) (g := fun acc b => acc * 256 + b)]
  congr 1
  apply List.ext_getElem
  · simp [bufferRead, length_bytesOf]; omega
  · intro i h1 h2
    simp only [bufferRead, List.getElem_map, List.getElem_range, List.getElem_take,
      List.getElem_drop]
    rw [byteAt_toNat, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem]
    · rfl

/-! ## Memory -/

open SolarTV.Machine in
/-- SolarTV's memory and EthLib's agree: EthLib's size is the active words', and every byte is
the same, zero past the size on both sides. -/
def MemRel (m : Mem) (M : ByteArray) : Prop :=
  M.size = 32 * m.words.toNat ∧ ∀ i, (byteAt M i).toBitVec = m.bytes i

open SolarTV.Machine in
theorem memRel_initial : MemRel Mem.initial .empty := by
  refine ⟨rfl, fun i => ?_⟩
  simp [byteAt, Mem.initial]

theorem natToBytes_toNat (len n : Nat) :
    (natToBytes len n).map (·.toNat) = (List.range len).map (fun i => (n / 256 ^ (len - 1 - i)) % 256) := by
  induction len generalizing n with
  | zero => rfl
  | succ len ih =>
    rw [natToBytes_succ, List.map_append, ih, List.range_succ, List.map_append]
    congr 1
    · apply List.map_congr_left
      intro i hi
      simp only [List.mem_range] at hi
      rw [Nat.div_div_eq_div_mul, ← Nat.pow_succ']
      congr 3
      omega
    · simp

theorem byte_toNat (v : Word) (i : Nat) (hi : i < 32) :
    (SolarTV.Memory.byte v i).toNat = v.toNat / 256 ^ (31 - i) % 256 := by
  unfold SolarTV.Memory.byte
  rw [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.pow_mul]

theorem byteAt_wordBytes (v : Word) (j : Nat) (hj : j < 32) :
    (byteAt (wordBytes v) j).toBitVec = SolarTV.Memory.byte v j := by
  apply BitVec.eq_of_toNat_eq
  rw [UInt8.toNat_toBitVec, byte_toNat v j hj, byteAt_toNat]
  have h := congrArg (fun l => l.getD j 0) (natToBytes_toNat 32 v.toNat)
  have hb : bytesOf (wordBytes v) = (natToBytes 32 v.toNat).map (·.toNat) := by
    simp [bytesOf, wordBytes, U256.toBeBytes]
  rw [hb, h, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hj]
  simp only [Option.map_some, Option.getD_some]

theorem ceil32_eq (n : Nat) : ceil32 n = 32 * ((n + 31) / 32) := by
  unfold ceil32 WORD_BYTES
  split <;> omega

/-! The growth of memory for one range, as EthLib's `Logic/Region.lean` states it (that module
is not in this library's imports). -/

theorem extendMemory_of_le' {size : Nat} {start length : U256}
    (h : start.toNat + length.toNat ≤ size) : extendMemory size [(start, length)] = ⟨0, 0⟩ :=
  extendMemory_eq_zero size _ fun p hp => by
    rw [List.mem_singleton.mp hp]
    exact .inr (ceil32_le (ceil32_mod size) (Nat.le_trans h (le_ceil32 size)))

theorem extendMemory_zero' (size : Nat) (start : U256) :
    extendMemory size [(start, 0)] = ⟨0, 0⟩ :=
  extendMemory_cons_zero size start []

theorem extendMemory_of_lt' {size : Nat} {start length : U256} (hmod : size % 32 = 0)
    (hz : length ≠ 0) (h : size < start.toNat + length.toNat) :
    extendMemory size [(start, length)] =
      ⟨memoryGasCost (ceil32 (start.toNat + length.toNat)) - memoryGasCost size,
        ceil32 (start.toNat + length.toNat) - size⟩ := by
  have hup := le_ceil32 (start.toNat + length.toNat)
  have hz' : ¬length = 0#256 := hz
  have grows : ¬ceil32 (start.toNat + length.toNat) ≤ size := by omega
  simp [extendMemory, hz', ceil32_of_mod hmod, grows]

theorem size_memoryExtend_extendMemory' {memory : ByteArray} {start length : U256}
    (hmod : memory.size % 32 = 0) (hz : length ≠ 0) :
    (memoryExtend memory (extendMemory memory.size [(start, length)]).expandBy).size =
      max memory.size (ceil32 (start.toNat + length.toNat)) := by
  rw [size_memoryExtend]
  by_cases h : memory.size < start.toNat + length.toNat
  · rw [extendMemory_of_lt' hmod hz h]
    have := le_ceil32 (start.toNat + length.toNat)
    simp only
    omega
  · rw [extendMemory_of_le' (by omega)]
    have := ceil32_le hmod (Nat.le_of_not_lt h)
    simp only
    omega

open SolarTV.Machine in
theorem memRel_store {m : Mem} {M : ByteArray} {o v : Word} (hm : MemRel m M)
    (hbound : o.toNat + 32 ≤ 2 ^ 32) :
    MemRel (m.store o.toNat v)
      (memoryWrite (memoryExtend M (extendMemory M.size [(o, 32)]).expandBy) o.toNat (wordBytes v)) ∧
    (memoryWrite (memoryExtend M (extendMemory M.size [(o, 32)]).expandBy) o.toNat
      (wordBytes v)).size = max M.size (ceil32 (o.toNat + 32)) := by
  have hmod : M.size % 32 = 0 := by rw [hm.1]; omega
  have hext := size_memoryExtend_extendMemory' (memory := M) (start := o) (length := 32) hmod
    (by decide)
  have h32 : (32 : U256).toNat = 32 := rfl
  rw [h32] at hext
  have hfit : o.toNat + (wordBytes v).size ≤
      (memoryExtend M (extendMemory M.size [(o, 32)]).expandBy).size := by
    rw [size_wordBytes, hext]
    have := le_ceil32 (o.toNat + 32)
    omega
  have hsize : (memoryWrite (memoryExtend M (extendMemory M.size [(o, 32)]).expandBy) o.toNat
      (wordBytes v)).size = max M.size (ceil32 (o.toNat + 32)) := by
    rw [size_memoryWrite_of_fit (fun _ => hfit), hext]
  refine ⟨⟨?_, fun i => ?_⟩, hsize⟩
  · rw [hsize, hm.1, ceil32_eq]
    unfold Mem.store Mem.expand SolarTV.Memory.grow
    simp only [show (32 = 0) = False from by decide, ite_false]
    have hlt : (o.toNat + 32 + 31) / 32 < 2 ^ 251 := by omega
    split
    · rename_i h
      rw [BitVec.ult_iff_toNat_lt, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt] at h
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
      omega
    · rename_i h
      rw [BitVec.ult_iff_toNat_lt, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt] at h
      omega
  · rw [byteAt_memoryWrite hfit, byteAt_memoryExtend, size_wordBytes]
    have hb : (m.store o.toNat v).bytes i =
        if o.toNat ≤ i ∧ i < o.toNat + 32 then SolarTV.Memory.byte v (i - o.toNat) else m.bytes i := by
      unfold Mem.store Mem.expand
      simp only [show (32 = 0) = False from by decide, ite_false]
    rw [hb]
    split
    · rename_i h
      exact byteAt_wordBytes v _ (by omega)
    · exact hm.2 i

/-- A byte array is its bytes. -/
theorem toList_map_toNat (B : ByteArray) :
    B.toList.map (·.toNat) = (List.range B.size).map (fun i => (byteAt B i).toNat) := by
  have e : B.toList = B.data.toList := by simp
  rw [e]
  apply List.ext_getElem
  · simp only [List.length_map, Array.length_toList, List.length_range]; rfl
  · intro i h1 h2
    simp only [List.getElem_map, List.getElem_range]
    rw [byteAt_toNat, List.getD_eq_getElem?_getD]
    have hi : i < (bytesOf B).length := by
      rw [length_bytesOf]; simpa using h2
    rw [List.getElem?_eq_getElem hi]
    simp [bytesOf]

open SolarTV.Machine in
/-- RETURN and REVERT give the bytes SolarTV's semantics reads. -/
theorem read_eq {m : Mem} {M : ByteArray} {o sz : Word} (hm : MemRel m M) :
    (memoryReadBytes (memoryExtend M (extendMemory M.size [(o, sz)]).expandBy) o.toNat
        sz.toNat).toList.map (·.toNat) =
      ((m.expand o.toNat sz.toNat).read o.toNat sz.toNat).map BitVec.toNat := by
  have hmod : M.size % 32 = 0 := by rw [hm.1]; omega
  by_cases hz : sz = 0
  · subst hz
    simp [memoryReadBytes, Mem.read]
  · have hext := size_memoryExtend_extendMemory' (memory := M) (start := o) (length := sz) hmod hz
    have hfit : o.toNat + sz.toNat ≤
        (memoryExtend M (extendMemory M.size [(o, sz)]).expandBy).size := by
      rw [hext]; have := le_ceil32 (o.toNat + sz.toNat); omega
    rw [toList_map_toNat, size_memoryReadBytes hfit]
    have hb : (m.expand o.toNat sz.toNat).bytes = m.bytes := by
      unfold Mem.expand; split <;> rfl
    simp only [Mem.read, hb, List.map_map]
    apply List.map_congr_left
    intro i hi
    simp only [List.mem_range] at hi
    rw [byteAt_memoryReadBytes hfit, if_pos hi, byteAt_memoryExtend, Function.comp_apply,
      ← hm.2 (o.toNat + i), UInt8.toNat_toBitVec]

/-- The growth for a range within `top` costs the price of the new size less the old one. -/
theorem extend_cost {size top : Nat} {o sz : Word} (hmod : size % 32 = 0) (htop : top % 32 = 0)
    (hle : size ≤ top) (hin : sz = 0 ∨ o.toNat + sz.toNat ≤ top) :
    size + (extendMemory size [(o, sz)]).expandBy ≤ top ∧
    (extendMemory size [(o, sz)]).cost + (memoryGasCost top -
        memoryGasCost (size + (extendMemory size [(o, sz)]).expandBy)) =
      memoryGasCost top - memoryGasCost size := by
  by_cases hz : sz = 0
  · subst hz
    rw [extendMemory_zero']
    simp [hle]
  · have hin : o.toNat + sz.toNat ≤ top := hin.resolve_left hz
    by_cases hlt : size < o.toNat + sz.toNat
    · rw [extendMemory_of_lt' hmod hz hlt]
      simp only
      have hc := ceil32_le htop hin
      have hc' := le_ceil32 (o.toNat + sz.toNat)
      have m1 := memoryGasCost_mono (show size ≤ ceil32 (o.toNat + sz.toNat) by omega)
      have m2 := memoryGasCost_mono hc
      refine ⟨by omega, ?_⟩
      rw [show size + (ceil32 (o.toNat + sz.toNat) - size) = ceil32 (o.toNat + sz.toNat) by omega]
      omega
    · rw [extendMemory_of_le' (by omega)]
      simp [hle]

/-! ## EthLib's rules for the items -/

section Rules

variable {code : ByteArray} {msg : Message .fusaka} {pc gas : Nat} {M : ByteArray}
  {st : State.TransactionState} {ss : Substate}

/-- PUSH of a decoded constant, PUSH0 or PUSHn. -/
theorem push_item {v next : Nat} {stack : List Word}
    (h : decode (bytesOf code) pc = some (.push v, next)) (hgas : 3 ≤ gas)
    (hstack : stack.length < 1024) :
    ∃ g, gas - 3 ≤ g ∧ Hoare .fusaka (At code msg pc stack M gas st ss .empty)
      (At code msg next (BitVec.ofNat 256 v :: stack) M g st ss .empty) := by
  obtain ⟨byte, hb, h⟩ := decode_push h
  obtain ⟨hlt, hcode⟩ := getElem?_bytesOf hb
  rcases h with ⟨rfl, rfl, rfl⟩ | ⟨h1, h2, rfl, hle, rfl⟩
  · exact ⟨gas - 2, by omega, SolidCore.Refinement.Evm.Logic.push0 (by decide) hlt hcode (by omega) hstack⟩
  · have hn : byte - PUSH1 < 32 := by unfold PUSH1 PUSH32 at *; omega
    have hdec := decode_pushByte ⟨byte - PUSH1, hn⟩
    have hbyte : 0x60 + (byte - PUSH1) = byte := by unfold PUSH1 at *; omega
    simp only [hbyte] at hdec
    refine ⟨gas - 3, le_refl _, ?_⟩
    have hle' : pc + 1 + (byte - PUSH1 + 1) ≤ code.size := by rw [← length_bytesOf]; exact hle
    have := push_of_decode (fork := .fusaka) (message := msg) (memory := M) (state := st)
      (substate := ss) (returnData := .empty) hlt hcode hdec (by simp)
      (pushData_eq hle') hgas hstack
    simpa [Nat.add_assoc] using this

/-- An opcode item decodes from the byte at the counter. -/
theorem op_item {byte next : Nat} (h : decode (bytesOf code) pc = some (.op byte, next)) :
    ∃ hlt : pc < code.size, code[pc] = UInt8.ofNat byte ∧ next = pc + 1 := by
  obtain ⟨hb, rfl⟩ := decode_op h
  obtain ⟨hlt, hcode⟩ := getElem?_bytesOf hb
  exact ⟨hlt, hcode, rfl⟩

theorem add_agree (x y : Word) : add x y = EvmRules.Evm.add x y := rfl
theorem sub_agree (x y : Word) : sub x y = EvmRules.Evm.sub x y := rfl
theorem mul_agree (x y : Word) : mul x y = EvmRules.Evm.mul x y := rfl

theorem div_agree (x y : Word) : div x y = EvmRules.Evm.div x y := by
  unfold div EvmRules.Evm.div
  by_cases h : y = 0
  · simp [h]
  · rw [if_neg h]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat, BitVec.toNat_udiv]
    exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) x.isLt)
theorem and_agree (x y : Word) : bitwiseAnd x y = EvmRules.Evm.and x y := rfl
theorem or_agree (x y : Word) : bitwiseOr x y = EvmRules.Evm.or x y := rfl
theorem xor_agree (x y : Word) : bitwiseXor x y = EvmRules.Evm.xor x y := rfl
theorem not_agree (x : Word) : bitwiseNot x = EvmRules.Evm.not x := rfl

theorem mod_agree (x y : Word) : mod x y = EvmRules.Evm.mod x y := by
  unfold mod EvmRules.Evm.mod
  by_cases h : y = 0
  · simp [h]
  · have hb : (y == 0) = false := by simpa using h
    rw [if_neg h, hb, cond_false]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat, BitVec.toNat_umod]
    exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.mod_le _ _) x.isLt)

theorem lt_agree (x y : Word) : lessThan x y = EvmRules.Evm.lt x y := by
  unfold lessThan EvmRules.Evm.lt
  by_cases h : x.toNat < y.toNat <;> simp [h, BitVec.ult]

theorem slt_agree (x y : Word) : signedLessThan x y = EvmRules.Evm.slt x y := by
  unfold signedLessThan EvmRules.Evm.slt
  rw [U256.toSigned_eq_toInt, U256.toSigned_eq_toInt]
  by_cases h : x.toInt < y.toInt <;> simp [h, BitVec.slt_iff_toInt_lt]

theorem sgt_agree (x y : Word) : signedGreaterThan x y = EvmRules.Evm.sgt x y := by
  unfold signedGreaterThan EvmRules.Evm.sgt
  rw [U256.toSigned_eq_toInt, U256.toSigned_eq_toInt]
  by_cases h : y.toInt < x.toInt <;> simp [h, BitVec.slt_iff_toInt_lt]

theorem gt_agree (x y : Word) : greaterThan x y = EvmRules.Evm.gt x y := by
  unfold greaterThan EvmRules.Evm.gt
  by_cases h : y.toNat < x.toNat <;> simp [h, BitVec.ult]

theorem eq_agree (x y : Word) : equal x y = EvmRules.Evm.eq x y := by
  unfold equal EvmRules.Evm.eq
  by_cases h : x = y <;> simp [h]

theorem iszero_agree (x : Word) : isZero x = EvmRules.Evm.iszero x := by
  unfold isZero EvmRules.Evm.iszero
  by_cases h : x = 0 <;> simp [h]

theorem ult_256 (x : Word) : x.ult (256 : Word) = decide (x.toNat < 256) := by
  simp [BitVec.ult]

theorem shr_agree (x y : Word) : bitwiseShr x y = EvmRules.Evm.shr x y := by
  unfold bitwiseShr EvmRules.Evm.shr
  rw [ult_256]
  by_cases h : x.toNat < 256 <;> simp [h, BitVec.ushiftRight_eq']

theorem shl_agree (x y : Word) : bitwiseShl x y = EvmRules.Evm.shl x y := by
  unfold bitwiseShl EvmRules.Evm.shl
  rw [ult_256]
  by_cases h : x.toNat < 256 <;> simp [h, BitVec.shiftLeft_eq']

theorem byte_agree (i v : Word) : getByte i v = EvmRules.Evm.byte i v := by
  unfold getByte EvmRules.Evm.byte
  by_cases h : i.toNat < 32
  · have hu : i.ult (32 : Word) = true := by simp [BitVec.ult, h]
    have hs : ((31 - i) * 8 : Word).toNat = (31 - i.toNat) * 8 := by bv_omega
    rw [if_neg (by omega), hu, Bool.cond_true, BitVec.ushiftRight_eq' v ((31 - i) * 8), hs]
  · have hu : i.ult (32 : Word) = false := by simp [BitVec.ult]; omega
    simp only [show i.toNat ≥ 32 by omega, ↓reduceIte, hu, Bool.cond_false]

theorem instr_stack (op : Op) (run : Evm .fusaka Nat → Except EvmError (Evm .fusaka Nat))
    (h : stackOnlyStep (Meter := Nat) .fusaka op = some run) : instruction .fusaka op = some run := by
  simp [instruction, h, HOrElse.hOrElse, OrElse.orElse, Option.orElse]

set_option hygiene false in
/-- A two-operand stack operation: EthLib's rule, with its function shown to be SolarTV's. -/
local macro "bin_rule" agree:term : tactic => `(tactic| (
  rcases stack with _ | ⟨x, _ | ⟨y, rest⟩⟩ <;> simp only [SolarTV.EVM.step, reduceCtorEq,
    Option.some.injEq] at hstep
  subst hstep
  refine ⟨_, le_refl _, ?_⟩
  rw [← $agree x y]
  exact binary hlt hcode rfl (instr_stack _ _ rfl) (Nat.le_trans (m := 3) (by decide) hgas)))

set_option hygiene false in
/-- A one-operand stack operation. -/
local macro "un_rule" agree:term : tactic => `(tactic| (
  rcases stack with _ | ⟨x, rest⟩ <;> simp only [SolarTV.EVM.step, reduceCtorEq,
    Option.some.injEq] at hstep
  subst hstep
  refine ⟨_, le_refl _, ?_⟩
  rw [← $agree x]
  exact unary hlt hcode rfl (instr_stack _ _ rfl) (Nat.le_trans (m := 3) (by decide) hgas)))

/-- Whether a stack operation of the fragment costs 5 gas (MUL, DIV and MOD) rather than 3. -/
def low : SolarTV.EVM.Op → Bool
  | .mul | .div | .mod => true
  | _ => false

/-- A stack operation of the fragment other than MUL, DIV and MOD, at its opcode, does what
SolarTV's semantics does. -/
theorem stack_rule_cheap {op : SolarTV.EVM.Op} {byte : Nat} {stack next : List Word}
    {r : Word} (hm : low op = false) (hb : opByte op = some byte) (hlt : pc < code.size)
    (hcode : code[pc] = UInt8.ofNat byte)
    (hstep : SolarTV.EVM.step ⟨BitVec.ofNat 256 msg.data.size, r⟩ op stack = some next)
    (hgas : 3 ≤ gas) (hlen : stack.length < 1024) :
    ∃ g, gas - 3 ≤ g ∧ Hoare .fusaka (At code msg pc stack M gas st ss .empty)
      (At code msg (pc + 1) next M g st ss .empty) := by
  cases op <;> simp only [opByte, reduceCtorEq, Option.some.injEq] at hb <;> try subst hb
  case mod | mul | div => simp [low] at hm
  case add => bin_rule add_agree
  case sub => bin_rule sub_agree
  case lt => bin_rule lt_agree
  case gt => bin_rule gt_agree
  case slt => bin_rule slt_agree
  case sgt => bin_rule sgt_agree
  case eq => bin_rule eq_agree
  case and => bin_rule and_agree
  case or => bin_rule or_agree
  case xor => bin_rule xor_agree
  case byte => bin_rule byte_agree
  case shl => bin_rule shl_agree
  case shr => bin_rule shr_agree
  case iszero => un_rule iszero_agree
  case not => un_rule not_agree
  case pop =>
    rcases stack with _ | ⟨x, rest⟩ <;> simp only [SolarTV.EVM.step, reduceCtorEq,
      Option.some.injEq] at hstep
    subst hstep
    exact ⟨_, by omega, pop hlt hcode (by omega)⟩
  case calldatasize =>
    simp only [SolarTV.EVM.step, Option.some.injEq] at hstep
    subst hstep
    exact ⟨_, by omega, calldatasize hlt hcode (by omega) hlen⟩
  case dup i =>
    split at hb
    · rename_i hi
      simp only [Option.some.injEq] at hb
      subst hb
      simp only [SolarTV.EVM.step, Option.map_eq_some_iff] at hstep
      obtain ⟨x, hx, rfl⟩ := hstep
      exact ⟨_, le_refl _, dup (⟨i.val, hi⟩ : Fin 16) hlt hcode hx hgas hlen⟩
    · simp at hb
  case swap i =>
    split at hb
    · rename_i hi
      simp only [Option.some.injEq] at hb
      subst hb
      rcases stack with _ | ⟨top, rest⟩
      · simp [SolarTV.EVM.step] at hstep
      · simp only [SolarTV.EVM.step, Option.map_eq_some_iff] at hstep
        obtain ⟨x, hx, rfl⟩ := hstep
        exact ⟨_, le_refl _, swap_of_decode hlt hcode (decode_swap ⟨i.val, hi⟩) hx hgas⟩
    · simp at hb

/-- A stack operation of the fragment, at its opcode, does what SolarTV's semantics does, for at
most 5 gas (the price of MUL, DIV and MOD; the rest cost 3). -/
theorem stack_rule {op : SolarTV.EVM.Op} {byte : Nat} {stack next : List Word}
    {r : Word} (hb : opByte op = some byte) (hlt : pc < code.size)
    (hcode : code[pc] = UInt8.ofNat byte)
    (hstep : SolarTV.EVM.step ⟨BitVec.ofNat 256 msg.data.size, r⟩ op stack = some next)
    (hgas : 5 ≤ gas) (hlen : stack.length < 1024) :
    ∃ g, gas - 5 ≤ g ∧ Hoare .fusaka (At code msg pc stack M gas st ss .empty)
      (At code msg (pc + 1) next M g st ss .empty) := by
  cases hm : low op
  · obtain ⟨g, hg, H⟩ := stack_rule_cheap hm hb hlt hcode hstep (Nat.le_trans (by decide) hgas) hlen
    exact ⟨g, by omega, H⟩
  · cases op <;> simp [low] at hm <;> simp only [opByte, Option.some.injEq] at hb <;> subst hb <;>
      rcases stack with _ | ⟨x, _ | ⟨y, rest⟩⟩ <;> simp only [SolarTV.EVM.step, reduceCtorEq,
        Option.some.injEq] at hstep <;> subst hstep <;> refine ⟨_, le_refl _, ?_⟩
    all_goals first
      | (rw [← mul_agree x y]; exact binary hlt hcode rfl (instr_stack _ _ rfl) hgas)
      | (rw [← div_agree x y]; exact binary hlt hcode rfl (instr_stack _ _ rfl) hgas)
      | (rw [← mod_agree x y]; exact binary hlt hcode rfl (instr_stack _ _ rfl) hgas)

end Rules

/-! ## DUPN, SWAPN and EXCHANGE are outside the fragment

The fragment runs at Fusaka, where EIP-8024's DUPN, SWAPN and EXCHANGE are no instruction
(`stackN_fusaka`), so the check refuses every `dup` and `swap` past the sixteenth word and every
`exchange`: the program solar's assembler lowers with them is not the bytecode this stage proves. -/

theorem blockStep_dup {p : Program} {c : Cert} {ok : Nat → List Word → List Ty → Nat → Bool}
    {h : Nat} {known : List Word} {ty : List Ty} {k : Nat} {i : Fin 256}
    (hc : blockStep p c ok h known ty k (.op (.stack (.dup i))) = true) : i.val < 16 := by
  simp only [blockStep, Bool.and_eq_true, decide_eq_true_eq] at hc
  exact hc.1.1.2

theorem blockStep_swap {p : Program} {c : Cert} {ok : Nat → List Word → List Ty → Nat → Bool}
    {h : Nat} {known : List Word} {ty : List Ty} {k : Nat} {i : Fin 256}
    (hc : blockStep p c ok h known ty k (.op (.stack (.swap i))) = true) : i.val < 16 := by
  simp only [blockStep, Bool.and_eq_true, decide_eq_true_eq] at hc
  exact hc.1.1.2

theorem blockStep_exchange {p : Program} {c : Cert} {ok : Nat → List Word → List Ty → Nat → Bool}
    {h : Nat} {known : List Word} {ty : List Ty} {k : Nat} {n m : Fin 32} :
    blockStep p c ok h known ty k (.op (.stack (.exchange n m))) = false := by
  simp [blockStep, stackNeed]

/-- The lowering never spells an instruction with an immediate: `dup` and `swap` past the
sixteenth word and `exchange` are INVALID, which the check refuses. -/
theorem lowerInstr_no_opImm (i : Instr) (b imm : Nat) : Item.opImm b imm ∉ lowerInstr i := by
  cases i <;> simp [lowerInstr] <;> split <;> simp

end SolidCore.Refinement.Solar.Assemble

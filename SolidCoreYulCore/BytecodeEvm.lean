import SharedSemantics.External

namespace SolidCoreYulCore

open SharedSemantics

namespace BytecodeEvm

/--
Bytecode-level EVM execution with gas accounting deliberately excluded.
`Opcode.gas` is the single decoded opcode that reports an unsupported semantic
boundary; `KECCAK256` and external call/create effects are supplied by explicit
external tables so single-contract execution remains deterministic and
executable.
-/

abbrev Byte := SharedSemantics.External.Byte
abbrev Bytes := List Byte
abbrev Stack := List Word
abbrev WordMap := List (Word × Word)
abbrev ByteMap := List (Word × Byte)
abbrev HashMap := SharedSemantics.External.HashMap
abbrev BytesMap := SharedSemantics.External.BytesMap
abbrev BytesSet := SharedSemantics.External.BytesSet

def maxStackDepth : Nat := 1024
def addressModulus : Nat :=
  SharedSemantics.External.addressModulus

def byte (n : Nat) : Byte :=
  SharedSemantics.External.byte n

def readByte (code : Bytes) (pc : Nat) : Byte :=
  byte ((code[pc]?).getD 0)

def normalizeBytes (bytes : Bytes) : Bytes :=
  SharedSemantics.External.normalizeBytes bytes

def zeroBytes : Nat → Bytes
  | 0 => []
  | size + 1 => 0 :: zeroBytes size

def readBytes (bytes : Bytes) (offset size : Nat) : Bytes :=
  (List.range size).map (fun ix => readByte bytes (offset + ix))

def lookupByte? : ByteMap → Word → Option Byte
  | [], _ => none
  | (candidate, value) :: rest, key =>
      if norm candidate = norm key then some (byte value) else lookupByte? rest key

def writeByteMap : ByteMap → Word → Byte → ByteMap
  | [], key, value => [(norm key, byte value)]
  | (candidate, oldValue) :: rest, key, value =>
      if norm candidate = norm key then
        (candidate, byte value) :: rest
      else
        (candidate, oldValue) :: writeByteMap rest key value

structure Memory where
  size : Nat := 0
  bytes : ByteMap := []
deriving DecidableEq, Repr

def roundUpMemorySize (size : Nat) : Nat :=
  ((size + 31) / 32) * 32

def expandMemory (memory : Memory) (offset size : Word) : Memory :=
  if norm size = 0 then
    memory
  else
    { memory with
      size := max memory.size (roundUpMemorySize (norm offset + norm size)) }

def readMemoryByte (memory : Memory) (offset : Word) : Byte :=
  (lookupByte? memory.bytes offset).getD 0

def readMemoryBytes (memory : Memory) (offset size : Word) : Bytes :=
  (List.range (norm size)).map (fun ix => readMemoryByte memory (norm offset + ix))

def writeMemoryBytesAux : Memory → Word → Bytes → Memory
  | memory, _, [] => memory
  | memory, offset, value :: rest =>
      writeMemoryBytesAux
        { memory with bytes := writeByteMap memory.bytes offset value }
        (offset + 1)
        rest

def writeMemoryBytes (memory : Memory) (offset : Word) (values : Bytes) : Memory :=
  expandMemory (writeMemoryBytesAux memory (norm offset) values) offset values.length

def wordByteBE (word ix : Word) : Byte :=
  byte (norm word / (256 ^ (31 - ix)))

def wordToBytes32 (word : Word) : Bytes :=
  (List.range 32).map (fun ix => wordByteBE word ix)

def bytesToWordBE (bytes : Bytes) : Word :=
  bytes.foldl (fun acc value => norm (acc * 256 + byte value)) 0

def readWordFromBytes (bytes : Bytes) (offset : Word) : Word :=
  bytesToWordBE (readBytes bytes (norm offset) 32)

def readMemoryWord (memory : Memory) (offset : Word) : Word :=
  bytesToWordBE (readMemoryBytes memory offset 32)

def writeMemoryWord (memory : Memory) (offset value : Word) : Memory :=
  writeMemoryBytes memory offset (wordToBytes32 value)

def writeMemoryByte (memory : Memory) (offset value : Word) : Memory :=
  writeMemoryBytes memory offset [byte value]

def copyBytesToMemory (memory : Memory) (dest : Word) (source : Bytes)
    (sourceOffset size : Word) : Memory :=
  writeMemoryBytes memory dest (readBytes source (norm sourceOffset) (norm size))

def lookupHash? : HashMap → Bytes → Option Word :=
  SharedSemantics.External.lookupHash?

def lookupBytes? : BytesMap → Bytes → Option Bytes :=
  SharedSemantics.External.lookupBytes?

def containsBytes : BytesSet → Bytes → Bool :=
  SharedSemantics.External.containsBytes

inductive Opcode where
  | stop
  | add
  | mul
  | sub
  | div
  | sdiv
  | modOp
  | smod
  | addmod
  | mulmod
  | exp
  | signextend
  | lt
  | gt
  | slt
  | sgt
  | eq
  | iszero
  | andOp
  | orOp
  | xor
  | notOp
  | byteOp
  | shl
  | shr
  | sar
  | clz
  | keccak256
  | address
  | balance
  | origin
  | caller
  | callvalue
  | calldataload
  | calldatasize
  | calldatacopy
  | codesize
  | codecopy
  | gasprice
  | extcodesize
  | extcodecopy
  | returndatasize
  | returndatacopy
  | extcodehash
  | blockhash
  | coinbase
  | timestamp
  | number
  | prevrandao
  | gaslimit
  | chainid
  | selfbalance
  | basefee
  | blobhash
  | blobbasefee
  | pop
  | mload
  | mstore
  | mstore8
  | sload
  | sstore
  | jump
  | jumpi
  | pc
  | msize
  | gas
  | jumpdest
  | tload
  | tstore
  | mcopy
  | push (width : Nat)
  | dup (index : Nat)
  | swap (index : Nat)
  | log (topics : Nat)
  | create
  | call
  | callcode
  | returnOp
  | delegatecall
  | create2
  | staticcall
  | revert
  | invalid
  | selfdestruct
deriving DecidableEq, Repr

def inRange (lo hi value : Nat) : Bool :=
  decide (lo <= value ∧ value <= hi)

def decodeOpcode (op : Byte) : Option Opcode :=
  let b := byte op
  if b = 0x00 then some Opcode.stop
  else if b = 0x01 then some Opcode.add
  else if b = 0x02 then some Opcode.mul
  else if b = 0x03 then some Opcode.sub
  else if b = 0x04 then some Opcode.div
  else if b = 0x05 then some Opcode.sdiv
  else if b = 0x06 then some Opcode.modOp
  else if b = 0x07 then some Opcode.smod
  else if b = 0x08 then some Opcode.addmod
  else if b = 0x09 then some Opcode.mulmod
  else if b = 0x0a then some Opcode.exp
  else if b = 0x0b then some Opcode.signextend
  else if b = 0x10 then some Opcode.lt
  else if b = 0x11 then some Opcode.gt
  else if b = 0x12 then some Opcode.slt
  else if b = 0x13 then some Opcode.sgt
  else if b = 0x14 then some Opcode.eq
  else if b = 0x15 then some Opcode.iszero
  else if b = 0x16 then some Opcode.andOp
  else if b = 0x17 then some Opcode.orOp
  else if b = 0x18 then some Opcode.xor
  else if b = 0x19 then some Opcode.notOp
  else if b = 0x1a then some Opcode.byteOp
  else if b = 0x1b then some Opcode.shl
  else if b = 0x1c then some Opcode.shr
  else if b = 0x1d then some Opcode.sar
  else if b = 0x1e then some Opcode.clz
  else if b = 0x20 then some Opcode.keccak256
  else if b = 0x30 then some Opcode.address
  else if b = 0x31 then some Opcode.balance
  else if b = 0x32 then some Opcode.origin
  else if b = 0x33 then some Opcode.caller
  else if b = 0x34 then some Opcode.callvalue
  else if b = 0x35 then some Opcode.calldataload
  else if b = 0x36 then some Opcode.calldatasize
  else if b = 0x37 then some Opcode.calldatacopy
  else if b = 0x38 then some Opcode.codesize
  else if b = 0x39 then some Opcode.codecopy
  else if b = 0x3a then some Opcode.gasprice
  else if b = 0x3b then some Opcode.extcodesize
  else if b = 0x3c then some Opcode.extcodecopy
  else if b = 0x3d then some Opcode.returndatasize
  else if b = 0x3e then some Opcode.returndatacopy
  else if b = 0x3f then some Opcode.extcodehash
  else if b = 0x40 then some Opcode.blockhash
  else if b = 0x41 then some Opcode.coinbase
  else if b = 0x42 then some Opcode.timestamp
  else if b = 0x43 then some Opcode.number
  else if b = 0x44 then some Opcode.prevrandao
  else if b = 0x45 then some Opcode.gaslimit
  else if b = 0x46 then some Opcode.chainid
  else if b = 0x47 then some Opcode.selfbalance
  else if b = 0x48 then some Opcode.basefee
  else if b = 0x49 then some Opcode.blobhash
  else if b = 0x4a then some Opcode.blobbasefee
  else if b = 0x50 then some Opcode.pop
  else if b = 0x51 then some Opcode.mload
  else if b = 0x52 then some Opcode.mstore
  else if b = 0x53 then some Opcode.mstore8
  else if b = 0x54 then some Opcode.sload
  else if b = 0x55 then some Opcode.sstore
  else if b = 0x56 then some Opcode.jump
  else if b = 0x57 then some Opcode.jumpi
  else if b = 0x58 then some Opcode.pc
  else if b = 0x59 then some Opcode.msize
  else if b = 0x5a then some Opcode.gas
  else if b = 0x5b then some Opcode.jumpdest
  else if b = 0x5c then some Opcode.tload
  else if b = 0x5d then some Opcode.tstore
  else if b = 0x5e then some Opcode.mcopy
  else if b = 0x5f then some (Opcode.push 0)
  else if inRange 0x60 0x7f b then some (Opcode.push (b - 0x5f))
  else if inRange 0x80 0x8f b then some (Opcode.dup (b - 0x7f))
  else if inRange 0x90 0x9f b then some (Opcode.swap (b - 0x8f))
  else if inRange 0xa0 0xa4 b then some (Opcode.log (b - 0xa0))
  else if b = 0xf0 then some Opcode.create
  else if b = 0xf1 then some Opcode.call
  else if b = 0xf2 then some Opcode.callcode
  else if b = 0xf3 then some Opcode.returnOp
  else if b = 0xf4 then some Opcode.delegatecall
  else if b = 0xf5 then some Opcode.create2
  else if b = 0xfa then some Opcode.staticcall
  else if b = 0xfd then some Opcode.revert
  else if b = 0xfe then some Opcode.invalid
  else if b = 0xff then some Opcode.selfdestruct
  else none

def opcodeSize : Opcode → Nat
  | Opcode.push width => width + 1
  | _ => 1

def lookupWord? : WordMap → Word → Option Word
  | [], _ => none
  | (candidate, value) :: rest, key =>
      if norm candidate = norm key then some value else lookupWord? rest key

def writeWord : WordMap → Word → Word → WordMap
  | [], key, value => [(norm key, norm value)]
  | (candidate, oldValue) :: rest, key, value =>
      if norm candidate = norm key then
        (candidate, norm value) :: rest
      else
        (candidate, oldValue) :: writeWord rest key value

abbrev CheatcodeSignature :=
  SharedSemantics.External.EcrecoverSignature

abbrev CheatcodeSignatureMap := List (Word × Word × CheatcodeSignature)

def lookupCheatcodeSignature? :
    CheatcodeSignatureMap → Word → Word → Option CheatcodeSignature
  | [], _, _ => none
  | (candidateKey, candidateDigest, signature) :: rest, key, digest =>
      if norm candidateKey = norm key ∧ norm candidateDigest = norm digest then
        some signature
      else
        lookupCheatcodeSignature? rest key digest

def lookupCheatcodeSignatureSigner? :
    CheatcodeSignatureMap → Word → CheatcodeSignature → Option Word
  | [], _, _ => none
  | (candidateKey, candidateDigest, candidateSignature) :: rest, digest, signature =>
      if norm candidateDigest = norm digest ∧
          norm candidateSignature.v = norm signature.v ∧
          norm candidateSignature.r = norm signature.r ∧
          norm candidateSignature.s = norm signature.s then
        some candidateKey
      else
        lookupCheatcodeSignatureSigner? rest digest signature

def addressWord (address : Word) : Word :=
  SharedSemantics.External.addressWord address

structure Account where
  nonce : Word := 0
  balance : Word := 0
  code : Bytes := []
  codeHash : Word := 0
  storage : WordMap := []
  transientStorage : WordMap := []
  createdInTransaction : Bool := false
  destroyed : Bool := false
deriving DecidableEq, Repr

abbrev AccountMap := List (Word × Account)

def lookupAccount? : AccountMap → Word → Option Account
  | [], _ => none
  | (candidate, account) :: rest, address =>
      if addressWord candidate = addressWord address then
        some account
      else
        lookupAccount? rest address

def writeAccount : AccountMap → Word → Account → AccountMap
  | [], address, account => [(addressWord address, account)]
  | (candidate, oldAccount) :: rest, address, account =>
      if addressWord candidate = addressWord address then
        (addressWord address, account) :: rest
      else
        (candidate, oldAccount) :: writeAccount rest address account

structure TxContext where
  origin : Word := 0
  gasprice : Word := 0
  blobhashes : List Word := []
deriving DecidableEq, Repr

structure BlockContext where
  coinbase : Word := 0
  timestamp : Word := 0
  number : Word := 0
  prevrandao : Word := 0
  gaslimit : Word := 0
  chainid : Word := 1
  basefee : Word := 0
  blobbasefee : Word := 0
  blockhashes : WordMap := []
  blobhashes : WordMap := []
deriving DecidableEq, Repr

structure CallContext where
  address : Word := 0
  caller : Word := 0
  callvalue : Word := 0
  calldata : Bytes := []
  returndata : Bytes := []
  isStatic : Bool := false
deriving DecidableEq, Repr

structure LogEntry where
  address : Word
  topics : List Word
  data : Bytes
deriving DecidableEq, Repr

abbrev ExternalCallKind := SharedSemantics.External.ExternalCallKind
namespace ExternalCallKind

abbrev call : ExternalCallKind :=
  SharedSemantics.External.ExternalCallKind.call

abbrev callcode : ExternalCallKind :=
  SharedSemantics.External.ExternalCallKind.callcode

abbrev delegatecall : ExternalCallKind :=
  SharedSemantics.External.ExternalCallKind.delegatecall

abbrev staticcall : ExternalCallKind :=
  SharedSemantics.External.ExternalCallKind.staticcall

end ExternalCallKind

notation "ExternalCallKind.call" => SharedSemantics.External.ExternalCallKind.call
notation "ExternalCallKind.callcode" =>
  SharedSemantics.External.ExternalCallKind.callcode
notation "ExternalCallKind.delegatecall" =>
  SharedSemantics.External.ExternalCallKind.delegatecall
notation "ExternalCallKind.staticcall" =>
  SharedSemantics.External.ExternalCallKind.staticcall

abbrev ExternalCreateKind := SharedSemantics.External.ExternalCreateKind
namespace ExternalCreateKind

abbrev create : ExternalCreateKind :=
  SharedSemantics.External.ExternalCreateKind.create

abbrev create2 : ExternalCreateKind :=
  SharedSemantics.External.ExternalCreateKind.create2

end ExternalCreateKind

notation "ExternalCreateKind.create" =>
  SharedSemantics.External.ExternalCreateKind.create
notation "ExternalCreateKind.create2" =>
  SharedSemantics.External.ExternalCreateKind.create2

structure ExternalCall where
  kind : ExternalCallKind
  gas : Word
  to : Word
  value : Word := 0
  input : Bytes
  retOffset : Word
  retSize : Word
  caller : Word
  address : Word
  isStatic : Bool
deriving DecidableEq, Repr

structure ExternalCreate where
  kind : ExternalCreateKind
  value : Word
  initCode : Bytes
  salt? : Option Word := none
  creator : Word
deriving DecidableEq, Repr

inductive ExternalAction where
  | call : ExternalCall → ExternalAction
  | create : ExternalCreate → ExternalAction
deriving DecidableEq, Repr

structure ExternalResult where
  success : Bool := false
  returndata : Bytes := []
  createdAddress : Word := 0
  accounts? : Option AccountMap := none
  gasRemaining : Word := 0
deriving DecidableEq, Repr

inductive HaltKind where
  | stopped
  | returned
  | reverted
  | selfdestructed
  | exceptional
deriving DecidableEq, Repr

inductive StepError where
  | invalidOpcode (byte : Byte)
  | invalidInstruction
  | missingHash (data : Bytes)
  | missingExternalResult (action : ExternalAction)
  | returnDataOutOfBounds (offset size : Word)
  | staticStateChange
  | stackUnderflow
  | stackOverflow
  | badJumpDestination (destination : Word)
  | unsupportedOpcode (opcode : Opcode)
  | unsupportedCheatcode (selector : Bytes)
  | missingCheatcodeAddress (privateKey : Word)
  | missingCheatcodeSignature (privateKey digest : Word)
deriving DecidableEq, Repr

structure CheatcodeSnapshot where
  accounts : AccountMap := []
  tx : TxContext := {}
  block : BlockContext := {}
  logs : List LogEntry := []
deriving DecidableEq, Repr

structure CheatcodeContext where
  prankCaller? : Option Word := none
  persistentPrankCaller? : Option Word := none
  expectRevert : Bool := false
  recordingLogs : Bool := false
  recordedLogs : List LogEntry := []
  nextSnapshotId : Word := 1
  snapshots : List (Word × CheatcodeSnapshot) := []
deriving DecidableEq, Repr

structure State where
  pc : Nat := 0
  stack : Stack := []
  memory : Memory := {}
  code : Bytes := []
  keccakHashes : HashMap := []
  sha256Hashes : HashMap := []
  ripemd160Hashes : HashMap := []
  modexpResults : BytesMap := []
  blake2fResults : BytesMap := []
  ecaddResults : BytesMap := []
  ecmulResults : BytesMap := []
  ecpairingResults : BytesMap := []
  ecaddFailures : BytesSet := []
  ecmulFailures : BytesSet := []
  ecpairingFailures : BytesSet := []
  pointEvaluationProofs : BytesSet := []
  pointEvaluationFailures : BytesSet := []
  p256VerifyProofs : BytesSet := []
  p256VerifyFailures : BytesSet := []
  blsG1AddResults : BytesMap := []
  blsG1MsmResults : BytesMap := []
  blsG2AddResults : BytesMap := []
  blsG2MsmResults : BytesMap := []
  blsPairingResults : BytesMap := []
  blsMapFpToG1Results : BytesMap := []
  blsMapFp2ToG2Results : BytesMap := []
  blsG1AddFailures : BytesSet := []
  blsG1MsmFailures : BytesSet := []
  blsG2AddFailures : BytesSet := []
  blsG2MsmFailures : BytesSet := []
  blsPairingFailures : BytesSet := []
  blsMapFpToG1Failures : BytesSet := []
  blsMapFp2ToG2Failures : BytesSet := []
  cheatcodeAddresses : WordMap := []
  cheatcodeSignatures : CheatcodeSignatureMap := []
  accounts : AccountMap := []
  tx : TxContext := {}
  block : BlockContext := {}
  call : CallContext := {}
  cheatcodes : CheatcodeContext := {}
  logs : List LogEntry := []
  externalActions : List ExternalAction := []
  externalResults : List ExternalResult := []
  externalTrace : List (ExternalAction × ExternalResult) := []
  output : Bytes := []
  halt? : Option HaltKind := none
  error? : Option StepError := none
deriving DecidableEq, Repr

def State.empty : State := {}

def setError (state : State) (error : StepError) : State :=
  { state with halt? := some HaltKind.exceptional, error? := some error }

def currentAccount (state : State) : Account :=
  match lookupAccount? state.accounts state.call.address with
  | some account => account
  | none => {}

def updateCurrentAccount (state : State) (account : Account) : State :=
  { state with accounts := writeAccount state.accounts state.call.address account }

def rawAccount (state : State) (address : Word) : Account :=
  match lookupAccount? state.accounts address with
  | some account => account
  | none => {}

def updateAccount (state : State) (address : Word) (account : Account) : State :=
  { state with accounts := writeAccount state.accounts address account }

def accountAt? (state : State) (address : Word) : Option Account :=
  lookupAccount? state.accounts address

def accountBalance (state : State) (address : Word) : Word :=
  match accountAt? state address with
  | some account => norm account.balance
  | none => 0

def accountCode (state : State) (address : Word) : Bytes :=
  match accountAt? state address with
  | some account => account.code
  | none => []

def emptyCodeHash : Word :=
  0xc5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470

/-- `EXTCODEHASH` uses the external Keccak table for non-empty code when no
explicit account `codeHash` was installed in the world state. -/
def accountCodeHash? (state : State) (address : Word) : Option Word :=
  match accountAt? state address with
  | none => some 0
  | some account =>
      if norm account.codeHash ≠ 0 then
        some (norm account.codeHash)
      else if account.code = [] then
        some emptyCodeHash
      else
        SharedSemantics.External.lookupHash? state.keccakHashes account.code

def accountCodeHash (state : State) (address : Word) : Word :=
  (accountCodeHash? state address).getD 0

def setAccountBalance (state : State) (address balance : Word) : State :=
  let account := rawAccount state address
  updateAccount state address { account with balance := norm balance, destroyed := false }

def blobHashAt (tx : TxContext) (index : Word) : Word :=
  SharedSemantics.External.blobHashAt tx.blobhashes index

def blockhashNumberInRange (current requested : Word) : Bool :=
  SharedSemantics.External.blockhashNumberInRange current requested

def returndataInBounds (returndata : Bytes) (offset size : Word) : Bool :=
  decide (norm offset + norm size <= returndata.length)

def successWord (success : Bool) : Word :=
  if success then 1 else 0

def accountsAfterExternalResult (state : State) (result : ExternalResult) :
    AccountMap :=
  match result.accounts? with
  | some accounts => accounts
  | none => state.accounts

def pushStack (value : Word) (stack : Stack) : Option Stack :=
  if stack.length < maxStackDepth then some (norm value :: stack) else none

def popStack : Stack → Option (Word × Stack)
  | [] => none
  | value :: rest => some (value, rest)

def popWords : Nat → Stack → Option (List Word × Stack)
  | 0, stack => some ([], stack)
  | count + 1, stack =>
      match popStack stack with
      | none => none
      | some (value, rest) =>
          match popWords count rest with
          | some (values, stack') => some (value :: values, stack')
          | none => none

def dupStack (index : Nat) (stack : Stack) : Option Stack :=
  if index = 0 then
    none
  else
    match stack[index - 1]? with
    | some value => pushStack value stack
    | none => none

def replaceNth {α : Type} : List α → Nat → α → Option (List α)
  | [], _, _ => none
  | _ :: rest, 0, value => some (value :: rest)
  | head :: rest, index + 1, value =>
      match replaceNth rest index value with
      | some rest' => some (head :: rest')
      | none => none

def swapStack : Nat → Stack → Option Stack
  | 0, _ => none
  | _, [] => none
  | index, top :: rest =>
      match rest[index - 1]? with
      | none => none
      | some other =>
          match replaceNth rest (index - 1) top with
          | some rest' => some (other :: rest')
          | none => none

def readPushValueAux (code : Bytes) : Nat → Nat → Nat → Word
  | _, 0, acc => norm acc
  | index, remaining + 1, acc =>
      readPushValueAux code (index + 1) remaining (acc * 256 + readByte code index)

def readPushValue (code : Bytes) (pc width : Nat) : Word :=
  readPushValueAux code (pc + 1) width 0

def isJumpDestAtFuel (code : Bytes) (target : Nat) : Nat → Nat → Bool
  | 0, _ => false
  | fuel + 1, pc =>
      if code.length <= pc then
        false
      else
        match decodeOpcode (readByte code pc) with
        | some Opcode.jumpdest =>
            if pc = target then true else isJumpDestAtFuel code target fuel (pc + 1)
        | some (Opcode.push width) =>
            if pc = target then false else isJumpDestAtFuel code target fuel (pc + opcodeSize (Opcode.push width))
        | _ =>
            if pc = target then false else isJumpDestAtFuel code target fuel (pc + 1)

def isJumpDest (code : Bytes) (target : Nat) : Bool :=
  isJumpDestAtFuel code target (code.length + 1) 0

def continueWithStack (state : State) (nextPc : Nat) (stack : Stack) : State :=
  { state with pc := nextPc, stack := stack }

def pushWithStackOrError (state : State) (nextPc : Nat)
    (stack : Stack) (value : Word) : State :=
  match pushStack value stack with
  | some stack' => continueWithStack state nextPc stack'
  | none => setError state StepError.stackOverflow

def pushOrError (state : State) (nextPc : Nat) (value : Word) : State :=
  pushWithStackOrError state nextPc state.stack value

def unaryWordOp (state : State) (nextPc : Nat) (op : Word → Word) : State :=
  match popStack state.stack with
  | none => setError state StepError.stackUnderflow
  | some (value, stack) =>
      match pushStack (op value) stack with
      | some stack' => continueWithStack state nextPc stack'
      | none => setError state StepError.stackOverflow

def binaryWordOp (state : State) (nextPc : Nat) (op : Word → Word → Word) : State :=
  match popStack state.stack with
  | none => setError state StepError.stackUnderflow
  | some (lhs, stackAfterLhs) =>
      match popStack stackAfterLhs with
      | none => setError state StepError.stackUnderflow
      | some (rhs, stack) =>
          match pushStack (op lhs rhs) stack with
          | some stack' => continueWithStack state nextPc stack'
          | none => setError state StepError.stackOverflow

def ternaryWordOp (state : State) (nextPc : Nat)
    (op : Word → Word → Word → Word) : State :=
  match popStack state.stack with
  | none => setError state StepError.stackUnderflow
  | some (first, stackAfterFirst) =>
      match popStack stackAfterFirst with
      | none => setError state StepError.stackUnderflow
      | some (second, stackAfterSecond) =>
          match popStack stackAfterSecond with
          | none => setError state StepError.stackUnderflow
          | some (third, stack) =>
              match pushStack (op first second third) stack with
              | some stack' => continueWithStack state nextPc stack'
              | none => setError state StepError.stackOverflow

def jumpOrError (state : State) (destination : Word) (stack : Stack) : State :=
  let target := norm destination
  if isJumpDest state.code target then
    { state with pc := target, stack := stack }
  else
    setError state (StepError.badJumpDestination destination)

def keccakOrError (state : State) (nextPc : Nat)
    (stack : Stack) (data : Bytes) : State :=
  match SharedSemantics.External.lookupHash? state.keccakHashes data with
  | some hash => pushWithStackOrError state nextPc stack hash
  | none => setError state (StepError.missingHash data)

def stepKeccak256 (state : State) (nextPc : Nat) : State :=
  match popStack state.stack with
  | none => setError state StepError.stackUnderflow
  | some (offset, stackAfterOffset) =>
      match popStack stackAfterOffset with
      | none => setError state StepError.stackUnderflow
      | some (size, stack) =>
          let data := readMemoryBytes state.memory offset size
          let memory := expandMemory state.memory offset size
          keccakOrError { state with memory := memory } nextPc stack data

def stepMload (state : State) (nextPc : Nat) : State :=
  match popStack state.stack with
  | none => setError state StepError.stackUnderflow
  | some (offset, stack) =>
      let memory := expandMemory state.memory offset 32
      pushWithStackOrError { state with memory := memory } nextPc stack
        (readMemoryWord memory offset)

def stepMstore (state : State) (nextPc : Nat) : State :=
  match popStack state.stack with
  | none => setError state StepError.stackUnderflow
  | some (offset, stackAfterOffset) =>
      match popStack stackAfterOffset with
      | none => setError state StepError.stackUnderflow
      | some (value, stack) =>
          continueWithStack
            { state with memory := writeMemoryWord state.memory offset value }
            nextPc
            stack

def stepMstore8 (state : State) (nextPc : Nat) : State :=
  match popStack state.stack with
  | none => setError state StepError.stackUnderflow
  | some (offset, stackAfterOffset) =>
      match popStack stackAfterOffset with
      | none => setError state StepError.stackUnderflow
      | some (value, stack) =>
          continueWithStack
            { state with memory := writeMemoryByte state.memory offset value }
            nextPc
            stack

def stepMemoryCopyFromBytes (state : State) (nextPc : Nat)
    (source : Bytes) : State :=
  match popStack state.stack with
  | none => setError state StepError.stackUnderflow
  | some (dest, stackAfterDest) =>
      match popStack stackAfterDest with
      | none => setError state StepError.stackUnderflow
      | some (sourceOffset, stackAfterSourceOffset) =>
          match popStack stackAfterSourceOffset with
          | none => setError state StepError.stackUnderflow
          | some (size, stack) =>
              continueWithStack
                { state with
                  memory := copyBytesToMemory state.memory dest source sourceOffset size }
                nextPc
                stack

def stepReturndatacopy (state : State) (nextPc : Nat) : State :=
  match popStack state.stack with
  | none => setError state StepError.stackUnderflow
  | some (dest, stackAfterDest) =>
      match popStack stackAfterDest with
      | none => setError state StepError.stackUnderflow
      | some (sourceOffset, stackAfterSourceOffset) =>
          match popStack stackAfterSourceOffset with
          | none => setError state StepError.stackUnderflow
          | some (size, stack) =>
              if returndataInBounds state.call.returndata sourceOffset size then
                continueWithStack
                  { state with
                    memory :=
                      copyBytesToMemory state.memory dest state.call.returndata
                        sourceOffset size }
                  nextPc
                  stack
              else
                setError state (StepError.returnDataOutOfBounds sourceOffset size)

def stepMcopy (state : State) (nextPc : Nat) : State :=
  match popStack state.stack with
  | none => setError state StepError.stackUnderflow
  | some (dest, stackAfterDest) =>
      match popStack stackAfterDest with
      | none => setError state StepError.stackUnderflow
      | some (sourceOffset, stackAfterSourceOffset) =>
          match popStack stackAfterSourceOffset with
          | none => setError state StepError.stackUnderflow
          | some (size, stack) =>
              let copied := readMemoryBytes state.memory sourceOffset size
              let memory := expandMemory state.memory sourceOffset size
              continueWithStack
                { state with memory := writeMemoryBytes memory dest copied }
                nextPc
                stack

def stepSload (state : State) (nextPc : Nat) : State :=
  match popStack state.stack with
  | none => setError state StepError.stackUnderflow
  | some (key, stack) =>
      pushWithStackOrError state nextPc stack
        ((lookupWord? (currentAccount state).storage key).getD 0)

def stepSstore (state : State) (nextPc : Nat) : State :=
  match popStack state.stack with
  | none => setError state StepError.stackUnderflow
  | some (key, stackAfterKey) =>
      match popStack stackAfterKey with
      | none => setError state StepError.stackUnderflow
      | some (value, stack) =>
          if state.call.isStatic then
            setError state StepError.staticStateChange
          else
            let account := currentAccount state
            let account' := { account with storage := writeWord account.storage key value }
            continueWithStack (updateCurrentAccount state account') nextPc stack

def stepTload (state : State) (nextPc : Nat) : State :=
  match popStack state.stack with
  | none => setError state StepError.stackUnderflow
  | some (key, stack) =>
      pushWithStackOrError state nextPc stack
        ((lookupWord? (currentAccount state).transientStorage key).getD 0)

def stepTstore (state : State) (nextPc : Nat) : State :=
  match popStack state.stack with
  | none => setError state StepError.stackUnderflow
  | some (key, stackAfterKey) =>
      match popStack stackAfterKey with
      | none => setError state StepError.stackUnderflow
      | some (value, stack) =>
          if state.call.isStatic then
            setError state StepError.staticStateChange
          else
            let account := currentAccount state
            let account' :=
              { account with transientStorage := writeWord account.transientStorage key value }
            continueWithStack (updateCurrentAccount state account') nextPc stack

def stepAccountUnary (state : State) (nextPc : Nat)
    (op : State → Word → Word) : State :=
  match popStack state.stack with
  | none => setError state StepError.stackUnderflow
  | some (address, stack) =>
      pushWithStackOrError state nextPc stack (op state (addressWord address))

def stepExtcodehash (state : State) (nextPc : Nat) : State :=
  match popStack state.stack with
  | none => setError state StepError.stackUnderflow
  | some (address, stack) =>
      let address := addressWord address
      match accountCodeHash? state address with
      | some hash => pushWithStackOrError state nextPc stack hash
      | none => setError state (StepError.missingHash (accountCode state address))

def stepExtcodecopy (state : State) (nextPc : Nat) : State :=
  match popStack state.stack with
  | none => setError state StepError.stackUnderflow
  | some (address, stackAfterAddress) =>
      let address := addressWord address
      match popStack stackAfterAddress with
      | none => setError state StepError.stackUnderflow
      | some (dest, stackAfterDest) =>
          match popStack stackAfterDest with
          | none => setError state StepError.stackUnderflow
          | some (sourceOffset, stackAfterSourceOffset) =>
              match popStack stackAfterSourceOffset with
              | none => setError state StepError.stackUnderflow
              | some (size, stack) =>
                  continueWithStack
                    { state with
                      memory :=
                        copyBytesToMemory state.memory dest (accountCode state address)
                          sourceOffset size }
                    nextPc
                    stack

def stepBlockhash (state : State) (nextPc : Nat) : State :=
  match popStack state.stack with
  | none => setError state StepError.stackUnderflow
  | some (blockNumber, stack) =>
      pushWithStackOrError state nextPc stack
        (if blockhashNumberInRange state.block.number blockNumber then
          (lookupWord? state.block.blockhashes blockNumber).getD 0
        else
          0)

def stepBlobhash (state : State) (nextPc : Nat) : State :=
  match popStack state.stack with
  | none => setError state StepError.stackUnderflow
  | some (index, stack) =>
      pushWithStackOrError state nextPc stack (blobHashAt state.tx index)

def stepReturnLike (state : State) (nextPc : Nat) (kind : HaltKind) : State :=
  match popStack state.stack with
  | none => setError state StepError.stackUnderflow
  | some (offset, stackAfterOffset) =>
      match popStack stackAfterOffset with
      | none => setError state StepError.stackUnderflow
      | some (size, stack) =>
          let output := readMemoryBytes state.memory offset size
          let memory := expandMemory state.memory offset size
          { state with
            pc := nextPc,
            stack := stack,
            memory := memory,
            output := output,
            halt? := some kind }

def stepLog (state : State) (nextPc topics : Nat) : State :=
  match popStack state.stack with
  | none => setError state StepError.stackUnderflow
  | some (offset, stackAfterOffset) =>
      match popStack stackAfterOffset with
      | none => setError state StepError.stackUnderflow
      | some (size, stackAfterSize) =>
          match popWords topics stackAfterSize with
          | none => setError state StepError.stackUnderflow
          | some (topicValues, stack) =>
              if state.call.isStatic then
                setError state StepError.staticStateChange
              else
                let data := readMemoryBytes state.memory offset size
                let memory := expandMemory state.memory offset size
                let logEntry : LogEntry :=
                  { address := state.call.address,
                    topics := topicValues,
                    data := data }
                let cheatcodes :=
                  if state.cheatcodes.recordingLogs then
                    { state.cheatcodes with
                      recordedLogs := logEntry :: state.cheatcodes.recordedLogs }
                  else
                    state.cheatcodes
                continueWithStack
                  { state with
                    memory := memory,
                    cheatcodes := cheatcodes,
                    logs := logEntry :: state.logs }
                  nextPc
                  stack

def stepSelfdestruct (state : State) (nextPc : Nat) : State :=
  match popStack state.stack with
  | none => setError state StepError.stackUnderflow
  | some (beneficiary, stack) =>
      let beneficiary := addressWord beneficiary
      if state.call.isStatic then
        setError state StepError.staticStateChange
      else
        let currentAddress := state.call.address
        let current := rawAccount state currentAddress
        let amount := norm current.balance
        let sameAddress := norm beneficiary = norm currentAddress
        let stateAfterTransfer :=
          if sameAddress then
            state
          else
            match accountAt? state beneficiary with
            | none =>
                if norm amount = 0 then
                  state
                else
                  setAccountBalance state beneficiary amount
            | some beneficiaryAccount =>
                setAccountBalance state beneficiary
                  (addWord beneficiaryAccount.balance amount)
        let currentAfterTransfer := rawAccount stateAfterTransfer currentAddress
        let currentFinal :=
          if current.createdInTransaction then
            { currentAfterTransfer with
              balance := 0,
              destroyed := true }
          else if sameAddress then
            currentAfterTransfer
          else
            { currentAfterTransfer with balance := 0 }
        { updateAccount stateAfterTransfer currentAddress currentFinal with
          pc := nextPc,
          stack := stack,
          halt? := some HaltKind.selfdestructed }

def applyExternalCallResult (state : State) (nextPc : Nat) (stack : Stack)
    (action : ExternalAction) (result : ExternalResult)
    (remainingResults : List ExternalResult) (memory : Memory)
    (retOffset retSize : Word) : State :=
  let copiedReturndata := result.returndata.take (norm retSize)
  let memory' := writeMemoryBytes memory retOffset copiedReturndata
  let call' := { state.call with returndata := result.returndata }
  let state' :=
    { state with
      memory := memory',
      accounts := accountsAfterExternalResult state result,
      call := call',
      externalActions := action :: state.externalActions,
      externalResults := remainingResults,
      externalTrace := (action, result) :: state.externalTrace }
  pushWithStackOrError state' nextPc stack (successWord result.success)

def applyExternalCreateResult (state : State) (nextPc : Nat) (stack : Stack)
    (action : ExternalAction) (result : ExternalResult)
    (remainingResults : List ExternalResult) (memory : Memory) : State :=
  let call' := { state.call with returndata := result.returndata }
  let state' :=
    { state with
      memory := memory,
      accounts := accountsAfterExternalResult state result,
      call := call',
      externalActions := action :: state.externalActions,
      externalResults := remainingResults,
      externalTrace := (action, result) :: state.externalTrace }
  pushWithStackOrError state' nextPc stack
    (if result.success then result.createdAddress else 0)

def missingExternalResult (state : State) (action : ExternalAction) : State :=
  setError { state with externalActions := action :: state.externalActions }
    (StepError.missingExternalResult action)

def stepExternalCallWithValue (state : State) (nextPc : Nat)
    (kind : ExternalCallKind) : State :=
  match popStack state.stack with
  | none => setError state StepError.stackUnderflow
  | some (gas, stackAfterGas) =>
      match popStack stackAfterGas with
      | none => setError state StepError.stackUnderflow
      | some (to, stackAfterTo) =>
          let target := addressWord to
          match popStack stackAfterTo with
          | none => setError state StepError.stackUnderflow
          | some (value, stackAfterValue) =>
              match popStack stackAfterValue with
              | none => setError state StepError.stackUnderflow
              | some (argsOffset, stackAfterArgsOffset) =>
                  match popStack stackAfterArgsOffset with
                  | none => setError state StepError.stackUnderflow
                  | some (argsSize, stackAfterArgsSize) =>
                      match popStack stackAfterArgsSize with
                      | none => setError state StepError.stackUnderflow
                      | some (retOffset, stackAfterRetOffset) =>
                          match popStack stackAfterRetOffset with
                          | none => setError state StepError.stackUnderflow
                          | some (retSize, stack) =>
                              if state.call.isStatic = true ∧
                                  kind = ExternalCallKind.call ∧
                                  norm value ≠ 0 then
                                setError state StepError.staticStateChange
                              else
                                let input := readMemoryBytes state.memory argsOffset argsSize
                                let memory :=
                                  expandMemory
                                    (expandMemory state.memory argsOffset argsSize)
                                    retOffset retSize
                                let action : ExternalAction :=
                                  ExternalAction.call
                                    { kind := kind,
                                      gas := gas,
                                      to := target,
                                      value := value,
                                      input := input,
                                      retOffset := retOffset,
                                      retSize := retSize,
                                      caller := state.call.address,
                                      address :=
                                        if kind = ExternalCallKind.call then
                                          target
                                        else
                                          state.call.address,
                                      isStatic := state.call.isStatic }
                                match state.externalResults with
                                | [] => missingExternalResult state action
                                | result :: rest =>
                                    applyExternalCallResult state nextPc stack action result
                                      rest memory retOffset retSize

def stepExternalCallNoValue (state : State) (nextPc : Nat)
    (kind : ExternalCallKind) : State :=
  match popStack state.stack with
  | none => setError state StepError.stackUnderflow
  | some (gas, stackAfterGas) =>
      match popStack stackAfterGas with
      | none => setError state StepError.stackUnderflow
      | some (to, stackAfterTo) =>
          let target := addressWord to
          match popStack stackAfterTo with
          | none => setError state StepError.stackUnderflow
          | some (argsOffset, stackAfterArgsOffset) =>
              match popStack stackAfterArgsOffset with
              | none => setError state StepError.stackUnderflow
              | some (argsSize, stackAfterArgsSize) =>
                  match popStack stackAfterArgsSize with
                  | none => setError state StepError.stackUnderflow
                  | some (retOffset, stackAfterRetOffset) =>
                      match popStack stackAfterRetOffset with
                      | none => setError state StepError.stackUnderflow
                      | some (retSize, stack) =>
                          let input := readMemoryBytes state.memory argsOffset argsSize
                          let memory :=
                            expandMemory
                              (expandMemory state.memory argsOffset argsSize)
                              retOffset retSize
                          let actionCaller :=
                            if kind = ExternalCallKind.delegatecall then
                              state.call.caller
                            else
                              state.call.address
                          let actionAddress :=
                            if kind = ExternalCallKind.delegatecall then
                              state.call.address
                            else
                              target
                          let actionStatic :=
                            if kind = ExternalCallKind.staticcall then
                              true
                            else
                              state.call.isStatic
                          let actionValue :=
                            if kind = ExternalCallKind.delegatecall then
                              state.call.callvalue
                            else
                              0
                          let action : ExternalAction :=
                            ExternalAction.call
                              { kind := kind,
                                gas := gas,
                                to := target,
                                value := actionValue,
                                input := input,
                                retOffset := retOffset,
                                retSize := retSize,
                                caller := actionCaller,
                                address := actionAddress,
                                isStatic := actionStatic }
                          match state.externalResults with
                          | [] => missingExternalResult state action
                          | result :: rest =>
                              applyExternalCallResult state nextPc stack action result
                                rest memory retOffset retSize

def stepExternalCreate (state : State) (nextPc : Nat)
    (kind : ExternalCreateKind) : State :=
  match popStack state.stack with
  | none => setError state StepError.stackUnderflow
  | some (value, stackAfterValue) =>
      match popStack stackAfterValue with
      | none => setError state StepError.stackUnderflow
      | some (offset, stackAfterOffset) =>
          match popStack stackAfterOffset with
          | none => setError state StepError.stackUnderflow
          | some (size, stackAfterSize) =>
              match kind with
              | ExternalCreateKind.create =>
                  if state.call.isStatic then
                    setError state StepError.staticStateChange
                  else
                    let initCode := readMemoryBytes state.memory offset size
                    let memory := expandMemory state.memory offset size
                    let action : ExternalAction :=
                      ExternalAction.create
                        { kind := kind,
                          value := value,
                          initCode := initCode,
                          creator := state.call.address }
                    match state.externalResults with
                    | [] => missingExternalResult state action
                    | result :: rest =>
                        applyExternalCreateResult state nextPc stackAfterSize action
                          result rest memory
              | ExternalCreateKind.create2 =>
                  match popStack stackAfterSize with
                  | none => setError state StepError.stackUnderflow
                  | some (salt, stack) =>
                      if state.call.isStatic then
                        setError state StepError.staticStateChange
                      else
                        let initCode := readMemoryBytes state.memory offset size
                        let memory := expandMemory state.memory offset size
                        let action : ExternalAction :=
                          ExternalAction.create
                            { kind := kind,
                              value := value,
                              initCode := initCode,
                              salt? := some salt,
                              creator := state.call.address }
                        match state.externalResults with
                        | [] => missingExternalResult state action
                        | result :: rest =>
                            applyExternalCreateResult state nextPc stack action result
                              rest memory

def stepOpcode (opcode : Opcode) (state : State) : State :=
  let nextPc := state.pc + opcodeSize opcode
  match opcode with
  | Opcode.stop =>
      { state with halt? := some HaltKind.stopped }
  | Opcode.invalid =>
      setError state StepError.invalidInstruction
  | Opcode.add =>
      binaryWordOp state nextPc addWord
  | Opcode.mul =>
      binaryWordOp state nextPc mulWord
  | Opcode.sub =>
      binaryWordOp state nextPc subWord
  | Opcode.div =>
      binaryWordOp state nextPc divWord
  | Opcode.sdiv =>
      binaryWordOp state nextPc sdivWord
  | Opcode.modOp =>
      binaryWordOp state nextPc modWord
  | Opcode.smod =>
      binaryWordOp state nextPc smodWord
  | Opcode.addmod =>
      ternaryWordOp state nextPc addmodWord
  | Opcode.mulmod =>
      ternaryWordOp state nextPc mulmodWord
  | Opcode.exp =>
      binaryWordOp state nextPc expWord
  | Opcode.signextend =>
      binaryWordOp state nextPc signextendWord
  | Opcode.lt =>
      binaryWordOp state nextPc ltWord
  | Opcode.gt =>
      binaryWordOp state nextPc gtWord
  | Opcode.slt =>
      binaryWordOp state nextPc sltWord
  | Opcode.sgt =>
      binaryWordOp state nextPc sgtWord
  | Opcode.eq =>
      binaryWordOp state nextPc eqWord
  | Opcode.iszero =>
      unaryWordOp state nextPc iszeroWord
  | Opcode.andOp =>
      binaryWordOp state nextPc andWord
  | Opcode.orOp =>
      binaryWordOp state nextPc orWord
  | Opcode.xor =>
      binaryWordOp state nextPc xorWord
  | Opcode.notOp =>
      unaryWordOp state nextPc notWord
  | Opcode.byteOp =>
      binaryWordOp state nextPc byteWord
  | Opcode.shl =>
      binaryWordOp state nextPc shlWord
  | Opcode.shr =>
      binaryWordOp state nextPc shrWord
  | Opcode.sar =>
      binaryWordOp state nextPc sarWord
  | Opcode.clz =>
      unaryWordOp state nextPc clzWord
  | Opcode.keccak256 =>
      stepKeccak256 state nextPc
  | Opcode.address =>
      pushOrError state nextPc state.call.address
  | Opcode.balance =>
      stepAccountUnary state nextPc accountBalance
  | Opcode.origin =>
      pushOrError state nextPc state.tx.origin
  | Opcode.caller =>
      pushOrError state nextPc state.call.caller
  | Opcode.callvalue =>
      pushOrError state nextPc state.call.callvalue
  | Opcode.calldataload =>
      match popStack state.stack with
      | none => setError state StepError.stackUnderflow
      | some (offset, stack) =>
          pushWithStackOrError state nextPc stack
            (readWordFromBytes state.call.calldata offset)
  | Opcode.calldatasize =>
      pushOrError state nextPc state.call.calldata.length
  | Opcode.calldatacopy =>
      stepMemoryCopyFromBytes state nextPc state.call.calldata
  | Opcode.codesize =>
      pushOrError state nextPc state.code.length
  | Opcode.codecopy =>
      stepMemoryCopyFromBytes state nextPc state.code
  | Opcode.gasprice =>
      pushOrError state nextPc state.tx.gasprice
  | Opcode.extcodesize =>
      stepAccountUnary state nextPc (fun state address => (accountCode state address).length)
  | Opcode.extcodecopy =>
      stepExtcodecopy state nextPc
  | Opcode.returndatasize =>
      pushOrError state nextPc state.call.returndata.length
  | Opcode.returndatacopy =>
      stepReturndatacopy state nextPc
  | Opcode.extcodehash =>
      stepExtcodehash state nextPc
  | Opcode.blockhash =>
      stepBlockhash state nextPc
  | Opcode.coinbase =>
      pushOrError state nextPc state.block.coinbase
  | Opcode.timestamp =>
      pushOrError state nextPc state.block.timestamp
  | Opcode.number =>
      pushOrError state nextPc state.block.number
  | Opcode.prevrandao =>
      pushOrError state nextPc state.block.prevrandao
  | Opcode.gaslimit =>
      pushOrError state nextPc state.block.gaslimit
  | Opcode.chainid =>
      pushOrError state nextPc state.block.chainid
  | Opcode.selfbalance =>
      pushOrError state nextPc (accountBalance state state.call.address)
  | Opcode.basefee =>
      pushOrError state nextPc state.block.basefee
  | Opcode.blobhash =>
      stepBlobhash state nextPc
  | Opcode.blobbasefee =>
      pushOrError state nextPc state.block.blobbasefee
  | Opcode.push width =>
      pushOrError state nextPc (readPushValue state.code state.pc width)
  | Opcode.pop =>
      match popStack state.stack with
      | some (_, stack) => continueWithStack state nextPc stack
      | none => setError state StepError.stackUnderflow
  | Opcode.mload =>
      stepMload state nextPc
  | Opcode.mstore =>
      stepMstore state nextPc
  | Opcode.mstore8 =>
      stepMstore8 state nextPc
  | Opcode.sload =>
      stepSload state nextPc
  | Opcode.sstore =>
      stepSstore state nextPc
  | Opcode.dup index =>
      match dupStack index state.stack with
      | some stack => continueWithStack state nextPc stack
      | none => setError state StepError.stackUnderflow
  | Opcode.swap index =>
      match swapStack index state.stack with
      | some stack => continueWithStack state nextPc stack
      | none => setError state StepError.stackUnderflow
  | Opcode.pc =>
      pushOrError state nextPc state.pc
  | Opcode.msize =>
      pushOrError state nextPc state.memory.size
  | Opcode.gas =>
      setError state (StepError.unsupportedOpcode Opcode.gas)
  | Opcode.jumpdest =>
      { state with pc := nextPc }
  | Opcode.tload =>
      stepTload state nextPc
  | Opcode.tstore =>
      stepTstore state nextPc
  | Opcode.mcopy =>
      stepMcopy state nextPc
  | Opcode.log topics =>
      stepLog state nextPc topics
  | Opcode.create =>
      stepExternalCreate state nextPc ExternalCreateKind.create
  | Opcode.call =>
      stepExternalCallWithValue state nextPc ExternalCallKind.call
  | Opcode.callcode =>
      stepExternalCallWithValue state nextPc ExternalCallKind.callcode
  | Opcode.returnOp =>
      stepReturnLike state nextPc HaltKind.returned
  | Opcode.delegatecall =>
      stepExternalCallNoValue state nextPc ExternalCallKind.delegatecall
  | Opcode.create2 =>
      stepExternalCreate state nextPc ExternalCreateKind.create2
  | Opcode.staticcall =>
      stepExternalCallNoValue state nextPc ExternalCallKind.staticcall
  | Opcode.revert =>
      stepReturnLike state nextPc HaltKind.reverted
  | Opcode.selfdestruct =>
      stepSelfdestruct state nextPc
  | Opcode.jump =>
      match popStack state.stack with
      | some (destination, stack) => jumpOrError state destination stack
      | none => setError state StepError.stackUnderflow
  | Opcode.jumpi =>
      match popStack state.stack with
      | none => setError state StepError.stackUnderflow
      | some (destination, stackAfterDestination) =>
          match popStack stackAfterDestination with
          | none => setError state StepError.stackUnderflow
          | some (condition, stack) =>
              if norm condition = 0 then
                continueWithStack state nextPc stack
              else
                jumpOrError state destination stack

def step (state : State) : State :=
  if state.halt?.isSome || state.error?.isSome then
    state
  else
    match state.code[state.pc]? with
    | none => { state with halt? := some HaltKind.stopped }
    | some op =>
        match decodeOpcode op with
        | some opcode => stepOpcode opcode state
        | none => setError state (StepError.invalidOpcode op)

def runFuel : Nat → State → State
  | 0, state => state
  | fuel + 1, state =>
      if state.halt?.isSome || state.error?.isSome then
        state
      else
        runFuel fuel (step state)

example : decodeOpcode 0x5f = some (Opcode.push 0) := by
  native_decide

example : decodeOpcode 0x7f = some (Opcode.push 32) := by
  native_decide

example : decodeOpcode 0x80 = some (Opcode.dup 1) := by
  native_decide

example : decodeOpcode 0x8f = some (Opcode.dup 16) := by
  native_decide

example : decodeOpcode 0x90 = some (Opcode.swap 1) := by
  native_decide

example : decodeOpcode 0x9f = some (Opcode.swap 16) := by
  native_decide

example :
    (runFuel 3 { State.empty with code := [0x60, 0x2a, 0x00] }).stack = [0x2a] := by
  native_decide

example :
    (runFuel 3 { State.empty with code := [0x60, 0x2a, 0x00] }).halt? = some HaltKind.stopped := by
  native_decide

example :
    (runFuel 4 { State.empty with code := [0x60, 0x02, 0x60, 0x06, 0x03, 0x00] }).stack =
      [0x04] := by
  native_decide

example :
    (runFuel 4 { State.empty with code := [0x60, 0x02, 0x60, 0x06, 0x04, 0x00] }).stack =
      [0x03] := by
  native_decide

example :
    (runFuel 4 { State.empty with code := [0x60, 0x08, 0x60, 0x01, 0x1b, 0x00] }).stack =
      [0x10] := by
  native_decide

example : decodeOpcode 0x1e = some Opcode.clz := by
  native_decide

example :
    (runFuel 3 { State.empty with code := [0x60, 0x01, 0x1e, 0x00] }).stack =
      [255] := by
  native_decide

example :
    (runFuel 3 { State.empty with code := [0x5f, 0x15, 0x00] }).stack = [1] := by
  native_decide

example :
    (runFuel 6
      { State.empty with code := [0x60, 0x2a, 0x5f, 0x52, 0x5f, 0x51, 0x00] }).stack =
      [0x2a] := by
  native_decide

example :
    (runFuel 6
      { State.empty with code := [0x60, 0x2a, 0x5f, 0x52, 0x5f, 0x51, 0x00] }).memory.size =
      32 := by
  native_decide

example :
    (runFuel 6
      { State.empty with code := [0x60, 0x2a, 0x60, 0x01, 0x55, 0x60, 0x01, 0x54, 0x00] }).stack =
      [0x2a] := by
  native_decide

example :
    (runFuel 3
      { State.empty with
        code := [0x5f, 0x35, 0x00],
        call := { ({} : CallContext) with calldata := wordToBytes32 0x2a } }).stack =
      [0x2a] := by
  native_decide

example :
    (runFuel 6
      { State.empty with code := [0x60, 0x2a, 0x5f, 0x52, 0x60, 0x20, 0x5f, 0xf3] }).halt? =
      some HaltKind.returned := by
  native_decide

example :
    (runFuel 6
      { State.empty with code := [0x60, 0x2a, 0x5f, 0x52, 0x60, 0x20, 0x5f, 0xf3] }).output =
      wordToBytes32 0x2a := by
  native_decide

example :
    (runFuel 8
      { State.empty with
        code := [0x60, 0x2a, 0x5f, 0x52, 0x60, 0x07, 0x60, 0x20, 0x5f, 0xa1, 0x00] }).logs =
      [{ address := 0, topics := [7], data := wordToBytes32 0x2a }] := by
  native_decide

def selfdestructExampleState : State :=
  { State.empty with
    code := [0x60, 0x02, 0xff],
    call := { ({} : CallContext) with address := 1 },
    accounts :=
      [ (1, { ({} : Account) with balance := 5 }),
        (2, { ({} : Account) with balance := 7 }) ] }

example :
    (runFuel 2 selfdestructExampleState).halt? = some HaltKind.selfdestructed := by
  native_decide

example :
    accountBalance (runFuel 2 selfdestructExampleState) 2 = 12 := by
  native_decide

example :
    (rawAccount (runFuel 2 selfdestructExampleState) 1).balance = 0 := by
  native_decide

def callExampleState : State :=
  { State.empty with
    code := [0x5f, 0x5f, 0x5f, 0x5f, 0x5f, 0x60, 0x02, 0x5f, 0xf1, 0x00],
    call := { ({} : CallContext) with address := 1 },
    externalResults := [{ success := true }] }

example :
    (runFuel 9 callExampleState).stack = [1] := by
  native_decide

example :
    (runFuel 9 callExampleState).externalActions =
      [ExternalAction.call
        { kind := ExternalCallKind.call,
          gas := 0,
          to := 2,
          value := 0,
          input := [],
          retOffset := 0,
          retSize := 0,
          caller := 1,
          address := 2,
          isStatic := false }] := by
  native_decide

def createExampleState : State :=
  { State.empty with
    code := [0x5f, 0x5f, 0x5f, 0xf0, 0x00],
    externalResults := [{ success := true, createdAddress := 9 }] }

example :
    (runFuel 5 createExampleState).stack = [9] := by
  native_decide

example :
    (step { State.empty with code := [0x0c] }).error? =
      some (StepError.invalidOpcode 0x0c) := by
  native_decide

example :
    (step { State.empty with code := [0x5a] }).error? =
      some (StepError.unsupportedOpcode Opcode.gas) := by
  native_decide

example :
    (runFuel 3 { State.empty with code := [0x60, 0x5b, 0x60, 0x01, 0x56] }).error? =
      some (StepError.badJumpDestination 1) := by
  native_decide

example :
    (runFuel 4 { State.empty with code := [0x60, 0x03, 0x56, 0x5b, 0x00] }).halt? =
      some HaltKind.stopped := by
  native_decide

def keccakExampleState : State :=
  { State.empty with
    code := [0x60, 0x2a, 0x5f, 0x52, 0x60, 0x20, 0x5f, 0x20, 0x00],
    keccakHashes := [(wordToBytes32 0x2a, 0xabc)] }

example :
    (runFuel 7 keccakExampleState).stack = [0xabc] := by
  native_decide

def callReturndataCopyExampleState : State :=
  { State.empty with
    code := [0x60, 0x01, 0x5f, 0x5f, 0x5f, 0x5f, 0x60, 0x02, 0x5f, 0xf1, 0x00],
    call := { ({} : CallContext) with address := 1 },
    externalResults := [{ success := true, returndata := [0xaa, 0xbb] }] }

example :
    readMemoryBytes (runFuel 9 callReturndataCopyExampleState).memory 0 1 =
      [0xaa] := by
  native_decide

example :
    (runFuel 9 callReturndataCopyExampleState).call.returndata =
      [0xaa, 0xbb] := by
  native_decide

def mcopyOverlapExampleState : State :=
  { State.empty with
    code := [0x60, 0x02, 0x5f, 0x60, 0x01, 0x5e, 0x00],
    memory :=
      { size := 32,
        bytes := [(0, 0xaa), (1, 0xbb), (2, 0xcc)] } }

example :
    readMemoryBytes (runFuel 5 mcopyOverlapExampleState).memory 0 3 =
      [0xaa, 0xaa, 0xbb] := by
  native_decide

end BytecodeEvm
end SolidCoreYulCore

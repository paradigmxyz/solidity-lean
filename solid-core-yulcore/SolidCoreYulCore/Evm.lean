import Std

set_option maxHeartbeats 1000000

namespace SolidCoreYulCore

def wordModulus : Nat := 2 ^ 256

def halfWordModulus : Nat := 2 ^ 255

abbrev Word := Nat

def norm (n : Nat) : Word :=
  n % wordModulus

def addWord (a b : Word) : Word :=
  norm (a + b)

def mulWord (a b : Word) : Word :=
  norm (a * b)

def divWord (a b : Word) : Word :=
  if norm b = 0 then 0 else norm (norm a / norm b)

def modWord (a b : Word) : Word :=
  if norm b = 0 then 0 else norm (norm a % norm b)

def addmodWord (a b n : Word) : Word :=
  if norm n = 0 then 0 else norm ((norm a + norm b) % norm n)

def mulmodWord (a b n : Word) : Word :=
  if norm n = 0 then 0 else norm ((norm a * norm b) % norm n)

def expWord (base exponent : Word) : Word :=
  norm ((norm base) ^ (norm exponent))

def subWord (a b : Word) : Word :=
  norm (wordModulus + norm a - norm b)

def iszeroWord (a : Word) : Word :=
  if norm a = 0 then 1 else 0

def eqWord (a b : Word) : Word :=
  if norm a = norm b then 1 else 0

def ltWord (a b : Word) : Word :=
  if norm a < norm b then 1 else 0

def gtWord (a b : Word) : Word :=
  if norm b < norm a then 1 else 0

def signedValue (a : Word) : Int :=
  if norm a < halfWordModulus then
    Int.ofNat (norm a)
  else
    Int.ofNat (norm a) - Int.ofNat wordModulus

def sltWord (a b : Word) : Word :=
  if signedValue a < signedValue b then 1 else 0

def sgtWord (a b : Word) : Word :=
  if signedValue b < signedValue a then 1 else 0

def signedToWord (value : Int) : Word :=
  if value < 0 then norm (wordModulus - Int.natAbs value) else norm value.toNat

def sdivWord (a b : Word) : Word :=
  if norm b = 0 then
    0
  else
    let lhs := signedValue a
    let rhs := signedValue b
    let quotient := (Int.natAbs lhs) / (Int.natAbs rhs)
    if (lhs < 0) = (rhs < 0) then
      signedToWord (Int.ofNat quotient)
    else
      signedToWord (-(Int.ofNat quotient))

def smodWord (a b : Word) : Word :=
  if norm b = 0 then
    0
  else
    let lhs := signedValue a
    let rhs := signedValue b
    let unsignedMod := (Int.natAbs lhs) % (Int.natAbs rhs)
    if lhs < 0 then
      signedToWord (-(Int.ofNat unsignedMod))
    else
      signedToWord (Int.ofNat unsignedMod)

def andWord (a b : Word) : Word :=
  norm (Nat.land (norm a) (norm b))

def orWord (a b : Word) : Word :=
  norm (Nat.lor (norm a) (norm b))

def xorWord (a b : Word) : Word :=
  norm (Nat.xor (norm a) (norm b))

def notWord (a : Word) : Word :=
  norm (wordModulus - 1 - norm a)

def shlWord (shift value : Word) : Word :=
  if 256 <= norm shift then 0 else norm (Nat.shiftLeft (norm value) (norm shift))

def shrWord (shift value : Word) : Word :=
  if 256 <= norm shift then 0 else norm (Nat.shiftRight (norm value) (norm shift))

def sarWord (shift value : Word) : Word :=
  if 256 <= norm shift then
    if signedValue value < 0 then norm (wordModulus - 1) else 0
  else
    signedToWord (Int.shiftRight (signedValue value) (norm shift))

def byteWord (ix value : Word) : Word :=
  if norm ix < 32 then
    norm (Nat.land (Nat.shiftRight (norm value) (8 * (31 - norm ix))) 255)
  else
    0

def signextendWord (ix value : Word) : Word :=
  if norm ix < 32 then
    let bitPos := 8 * norm ix + 7
    let modulus := 2 ^ (bitPos + 1)
    let signBit := 2 ^ bitPos
    let low := norm value % modulus
    if signBit <= low then norm (wordModulus - modulus + low) else norm low
  else
    norm value

def clzWordAux : Nat -> Nat -> Word -> Word
  | 0, _, _ => 256
  | remaining + 1, bit, value =>
      if 0 < Nat.land (norm value) (2 ^ bit) then
        255 - bit
      else
        clzWordAux remaining (bit - 1) value

def clzWord (value : Word) : Word :=
  norm (clzWordAux 256 255 value)

def ceil32 (n : Nat) : Nat :=
  if n = 0 then 0 else ((n + 31) / 32) * 32

def memorySizeAfter (current offset size : Word) : Word :=
  if norm size = 0 then
    norm current
  else
    Nat.max (norm current) (ceil32 (norm offset + norm size))

theorem memorySizeAfter_zero_size (current offset : Word) :
    memorySizeAfter current offset 0 = norm current := by
  rfl

theorem memorySizeAfter_empty_word :
    memorySizeAfter 0 0 32 = 32 := by
  rfl

namespace Evm

inductive HaltKind where
  | stop
  | returned
  | reverted
  | invalid
  deriving DecidableEq, Repr

structure BuiltinSignature where
  paramCount : Nat
  resultCount : Nat
  deriving DecidableEq, Repr

inductive ClaimKind where
  | exactYul
  | symbolic
  | abstractedBuiltin
  | deferredToLowering
  deriving DecidableEq, Repr

inductive SemanticCoverage where
  | controlHalt
  | pureWord
  | discard
  | contextWord
  | loweringEnvironment
  | bufferRead
  | bufferSize
  | bufferCopy
  | objectDataCopy
  | memoryHash
  | memoryRead
  | memoryWrite
  | memoryCopy
  | storage
  | transientStorage
  | externalQuery
  | log
  | externalCall
  | contractCreation
  | selfdestruct
  | compilerBuiltin
  | verbatim
  deriving DecidableEq, Repr

inductive Builtin where
  | stopOp
  | add
  | mul
  | divOp
  | sdivOp
  | modOp
  | smodOp
  | addmodOp
  | mulmodOp
  | expOp
  | sub
  | iszero
  | eqOp
  | ltOp
  | gtOp
  | sltOp
  | sgtOp
  | andOp
  | orOp
  | xorOp
  | notOp
  | shlOp
  | shrOp
  | sarOp
  | signextendOp
  | byteOp
  | clzOp
  | popOp
  | addressOp
  | originOp
  | callerOp
  | callvalueOp
  | gaspriceOp
  | calldataloadOp
  | calldatasizeOp
  | calldatacopyOp
  | returndataloadOp
  | returndatasizeOp
  | returndatacopyOp
  | blockhashOp
  | coinbaseOp
  | timestampOp
  | numberOp
  | difficultyOp
  | prevrandaoOp
  | gaslimitOp
  | chainidOp
  | balanceOp
  | selfbalanceOp
  | extcodesizeOp
  | extcodehashOp
  | extcodecopyOp
  | codecopyOp
  | datacopyOp
  | codesizeOp
  | pcOp
  | msizeOp
  | basefeeOp
  | gasOp
  | keccak256Op
  | log0Op
  | log1Op
  | log2Op
  | log3Op
  | log4Op
  | callOp
  | callcodeOp
  | delegatecallOp
  | staticcallOp
  | returnOp
  | revertOp
  | invalidOp
  | createOp
  | create2Op
  | selfdestructOp
  | sload
  | sstore
  | mload
  | mstore
  | mstore8
  | tloadOp
  | tstoreOp
  | mcopyOp
  | blobhashOp
  | blobbasefeeOp
  | setimmutableOp
  | loadimmutableOp
  | linkersymbolOp
  | memoryguardOp
  | verbatimOp : Nat -> Nat -> Builtin
  | opaque : Nat -> Builtin
  deriving DecidableEq, Repr

def Builtin.signature? : Builtin -> Option BuiltinSignature
  | Builtin.stopOp => some { paramCount := 0, resultCount := 0 }
  | Builtin.add => some { paramCount := 2, resultCount := 1 }
  | Builtin.mul => some { paramCount := 2, resultCount := 1 }
  | Builtin.divOp => some { paramCount := 2, resultCount := 1 }
  | Builtin.sdivOp => some { paramCount := 2, resultCount := 1 }
  | Builtin.modOp => some { paramCount := 2, resultCount := 1 }
  | Builtin.smodOp => some { paramCount := 2, resultCount := 1 }
  | Builtin.addmodOp => some { paramCount := 3, resultCount := 1 }
  | Builtin.mulmodOp => some { paramCount := 3, resultCount := 1 }
  | Builtin.expOp => some { paramCount := 2, resultCount := 1 }
  | Builtin.sub => some { paramCount := 2, resultCount := 1 }
  | Builtin.iszero => some { paramCount := 1, resultCount := 1 }
  | Builtin.eqOp => some { paramCount := 2, resultCount := 1 }
  | Builtin.ltOp => some { paramCount := 2, resultCount := 1 }
  | Builtin.gtOp => some { paramCount := 2, resultCount := 1 }
  | Builtin.sltOp => some { paramCount := 2, resultCount := 1 }
  | Builtin.sgtOp => some { paramCount := 2, resultCount := 1 }
  | Builtin.andOp => some { paramCount := 2, resultCount := 1 }
  | Builtin.orOp => some { paramCount := 2, resultCount := 1 }
  | Builtin.xorOp => some { paramCount := 2, resultCount := 1 }
  | Builtin.notOp => some { paramCount := 1, resultCount := 1 }
  | Builtin.shlOp => some { paramCount := 2, resultCount := 1 }
  | Builtin.shrOp => some { paramCount := 2, resultCount := 1 }
  | Builtin.sarOp => some { paramCount := 2, resultCount := 1 }
  | Builtin.signextendOp => some { paramCount := 2, resultCount := 1 }
  | Builtin.byteOp => some { paramCount := 2, resultCount := 1 }
  | Builtin.clzOp => some { paramCount := 1, resultCount := 1 }
  | Builtin.popOp => some { paramCount := 1, resultCount := 0 }
  | Builtin.addressOp => some { paramCount := 0, resultCount := 1 }
  | Builtin.originOp => some { paramCount := 0, resultCount := 1 }
  | Builtin.callerOp => some { paramCount := 0, resultCount := 1 }
  | Builtin.callvalueOp => some { paramCount := 0, resultCount := 1 }
  | Builtin.gaspriceOp => some { paramCount := 0, resultCount := 1 }
  | Builtin.calldataloadOp => some { paramCount := 1, resultCount := 1 }
  | Builtin.calldatasizeOp => some { paramCount := 0, resultCount := 1 }
  | Builtin.calldatacopyOp => some { paramCount := 3, resultCount := 0 }
  | Builtin.returndataloadOp => some { paramCount := 1, resultCount := 1 }
  | Builtin.returndatasizeOp => some { paramCount := 0, resultCount := 1 }
  | Builtin.returndatacopyOp => some { paramCount := 3, resultCount := 0 }
  | Builtin.blockhashOp => some { paramCount := 1, resultCount := 1 }
  | Builtin.coinbaseOp => some { paramCount := 0, resultCount := 1 }
  | Builtin.timestampOp => some { paramCount := 0, resultCount := 1 }
  | Builtin.numberOp => some { paramCount := 0, resultCount := 1 }
  | Builtin.difficultyOp => some { paramCount := 0, resultCount := 1 }
  | Builtin.prevrandaoOp => some { paramCount := 0, resultCount := 1 }
  | Builtin.gaslimitOp => some { paramCount := 0, resultCount := 1 }
  | Builtin.chainidOp => some { paramCount := 0, resultCount := 1 }
  | Builtin.balanceOp => some { paramCount := 1, resultCount := 1 }
  | Builtin.selfbalanceOp => some { paramCount := 0, resultCount := 1 }
  | Builtin.extcodesizeOp => some { paramCount := 1, resultCount := 1 }
  | Builtin.extcodehashOp => some { paramCount := 1, resultCount := 1 }
  | Builtin.extcodecopyOp => some { paramCount := 4, resultCount := 0 }
  | Builtin.codecopyOp => some { paramCount := 3, resultCount := 0 }
  | Builtin.datacopyOp => some { paramCount := 3, resultCount := 0 }
  | Builtin.codesizeOp => some { paramCount := 0, resultCount := 1 }
  | Builtin.pcOp => some { paramCount := 0, resultCount := 1 }
  | Builtin.msizeOp => some { paramCount := 0, resultCount := 1 }
  | Builtin.basefeeOp => some { paramCount := 0, resultCount := 1 }
  | Builtin.gasOp => some { paramCount := 0, resultCount := 1 }
  | Builtin.keccak256Op => some { paramCount := 2, resultCount := 1 }
  | Builtin.log0Op => some { paramCount := 2, resultCount := 0 }
  | Builtin.log1Op => some { paramCount := 3, resultCount := 0 }
  | Builtin.log2Op => some { paramCount := 4, resultCount := 0 }
  | Builtin.log3Op => some { paramCount := 5, resultCount := 0 }
  | Builtin.log4Op => some { paramCount := 6, resultCount := 0 }
  | Builtin.callOp => some { paramCount := 7, resultCount := 1 }
  | Builtin.callcodeOp => some { paramCount := 7, resultCount := 1 }
  | Builtin.delegatecallOp => some { paramCount := 6, resultCount := 1 }
  | Builtin.staticcallOp => some { paramCount := 6, resultCount := 1 }
  | Builtin.returnOp => some { paramCount := 2, resultCount := 0 }
  | Builtin.revertOp => some { paramCount := 2, resultCount := 0 }
  | Builtin.invalidOp => some { paramCount := 0, resultCount := 0 }
  | Builtin.createOp => some { paramCount := 3, resultCount := 1 }
  | Builtin.create2Op => some { paramCount := 4, resultCount := 1 }
  | Builtin.selfdestructOp => some { paramCount := 1, resultCount := 0 }
  | Builtin.sload => some { paramCount := 1, resultCount := 1 }
  | Builtin.sstore => some { paramCount := 2, resultCount := 0 }
  | Builtin.mload => some { paramCount := 1, resultCount := 1 }
  | Builtin.mstore => some { paramCount := 2, resultCount := 0 }
  | Builtin.mstore8 => some { paramCount := 2, resultCount := 0 }
  | Builtin.tloadOp => some { paramCount := 1, resultCount := 1 }
  | Builtin.tstoreOp => some { paramCount := 2, resultCount := 0 }
  | Builtin.mcopyOp => some { paramCount := 3, resultCount := 0 }
  | Builtin.blobhashOp => some { paramCount := 1, resultCount := 1 }
  | Builtin.blobbasefeeOp => some { paramCount := 0, resultCount := 1 }
  | Builtin.setimmutableOp => some { paramCount := 3, resultCount := 0 }
  | Builtin.loadimmutableOp => some { paramCount := 1, resultCount := 1 }
  | Builtin.linkersymbolOp => some { paramCount := 1, resultCount := 1 }
  | Builtin.memoryguardOp => some { paramCount := 1, resultCount := 1 }
  | Builtin.verbatimOp inputs outputs =>
      some { paramCount := inputs, resultCount := outputs }
  | Builtin.opaque _ => none

def Builtin.claim? : Builtin -> Option ClaimKind
  | Builtin.stopOp => some ClaimKind.exactYul
  | Builtin.add => some ClaimKind.exactYul
  | Builtin.mul => some ClaimKind.exactYul
  | Builtin.divOp => some ClaimKind.exactYul
  | Builtin.sdivOp => some ClaimKind.exactYul
  | Builtin.modOp => some ClaimKind.exactYul
  | Builtin.smodOp => some ClaimKind.exactYul
  | Builtin.addmodOp => some ClaimKind.exactYul
  | Builtin.mulmodOp => some ClaimKind.exactYul
  | Builtin.expOp => some ClaimKind.exactYul
  | Builtin.sub => some ClaimKind.exactYul
  | Builtin.iszero => some ClaimKind.exactYul
  | Builtin.eqOp => some ClaimKind.exactYul
  | Builtin.ltOp => some ClaimKind.exactYul
  | Builtin.gtOp => some ClaimKind.exactYul
  | Builtin.sltOp => some ClaimKind.exactYul
  | Builtin.sgtOp => some ClaimKind.exactYul
  | Builtin.andOp => some ClaimKind.exactYul
  | Builtin.orOp => some ClaimKind.exactYul
  | Builtin.xorOp => some ClaimKind.exactYul
  | Builtin.notOp => some ClaimKind.exactYul
  | Builtin.shlOp => some ClaimKind.exactYul
  | Builtin.shrOp => some ClaimKind.exactYul
  | Builtin.sarOp => some ClaimKind.exactYul
  | Builtin.signextendOp => some ClaimKind.exactYul
  | Builtin.byteOp => some ClaimKind.exactYul
  | Builtin.clzOp => some ClaimKind.exactYul
  | Builtin.popOp => some ClaimKind.exactYul
  | Builtin.addressOp => some ClaimKind.exactYul
  | Builtin.originOp => some ClaimKind.exactYul
  | Builtin.callerOp => some ClaimKind.exactYul
  | Builtin.callvalueOp => some ClaimKind.exactYul
  | Builtin.gaspriceOp => some ClaimKind.exactYul
  | Builtin.calldataloadOp => some ClaimKind.exactYul
  | Builtin.calldatasizeOp => some ClaimKind.exactYul
  | Builtin.calldatacopyOp => some ClaimKind.exactYul
  | Builtin.returndataloadOp => some ClaimKind.exactYul
  | Builtin.returndatasizeOp => some ClaimKind.exactYul
  | Builtin.returndatacopyOp => some ClaimKind.exactYul
  | Builtin.blockhashOp => some ClaimKind.symbolic
  | Builtin.coinbaseOp => some ClaimKind.exactYul
  | Builtin.timestampOp => some ClaimKind.exactYul
  | Builtin.numberOp => some ClaimKind.exactYul
  | Builtin.difficultyOp => some ClaimKind.exactYul
  | Builtin.prevrandaoOp => some ClaimKind.exactYul
  | Builtin.gaslimitOp => some ClaimKind.exactYul
  | Builtin.chainidOp => some ClaimKind.exactYul
  | Builtin.balanceOp => some ClaimKind.abstractedBuiltin
  | Builtin.selfbalanceOp => some ClaimKind.exactYul
  | Builtin.extcodesizeOp => some ClaimKind.abstractedBuiltin
  | Builtin.extcodehashOp => some ClaimKind.symbolic
  | Builtin.extcodecopyOp => some ClaimKind.abstractedBuiltin
  | Builtin.codecopyOp => some ClaimKind.exactYul
  | Builtin.datacopyOp => some ClaimKind.exactYul
  | Builtin.codesizeOp => some ClaimKind.exactYul
  | Builtin.pcOp => some ClaimKind.deferredToLowering
  | Builtin.msizeOp => some ClaimKind.exactYul
  | Builtin.basefeeOp => some ClaimKind.exactYul
  | Builtin.gasOp => some ClaimKind.deferredToLowering
  | Builtin.keccak256Op => some ClaimKind.symbolic
  | Builtin.log0Op => some ClaimKind.abstractedBuiltin
  | Builtin.log1Op => some ClaimKind.abstractedBuiltin
  | Builtin.log2Op => some ClaimKind.abstractedBuiltin
  | Builtin.log3Op => some ClaimKind.abstractedBuiltin
  | Builtin.log4Op => some ClaimKind.abstractedBuiltin
  | Builtin.callOp => some ClaimKind.abstractedBuiltin
  | Builtin.callcodeOp => some ClaimKind.abstractedBuiltin
  | Builtin.delegatecallOp => some ClaimKind.abstractedBuiltin
  | Builtin.staticcallOp => some ClaimKind.abstractedBuiltin
  | Builtin.returnOp => some ClaimKind.exactYul
  | Builtin.revertOp => some ClaimKind.exactYul
  | Builtin.invalidOp => some ClaimKind.exactYul
  | Builtin.createOp => some ClaimKind.abstractedBuiltin
  | Builtin.create2Op => some ClaimKind.abstractedBuiltin
  | Builtin.selfdestructOp => some ClaimKind.abstractedBuiltin
  | Builtin.sload => some ClaimKind.exactYul
  | Builtin.sstore => some ClaimKind.exactYul
  | Builtin.mload => some ClaimKind.exactYul
  | Builtin.mstore => some ClaimKind.exactYul
  | Builtin.mstore8 => some ClaimKind.exactYul
  | Builtin.tloadOp => some ClaimKind.exactYul
  | Builtin.tstoreOp => some ClaimKind.exactYul
  | Builtin.mcopyOp => some ClaimKind.exactYul
  | Builtin.blobhashOp => some ClaimKind.symbolic
  | Builtin.blobbasefeeOp => some ClaimKind.exactYul
  | Builtin.setimmutableOp => some ClaimKind.abstractedBuiltin
  | Builtin.loadimmutableOp => some ClaimKind.abstractedBuiltin
  | Builtin.linkersymbolOp => some ClaimKind.abstractedBuiltin
  | Builtin.memoryguardOp => some ClaimKind.abstractedBuiltin
  | Builtin.verbatimOp _ _ => some ClaimKind.abstractedBuiltin
  | Builtin.opaque _ => none

def Builtin.semanticCoverage? : Builtin -> Option SemanticCoverage
  | Builtin.stopOp => some SemanticCoverage.controlHalt
  | Builtin.add => some SemanticCoverage.pureWord
  | Builtin.mul => some SemanticCoverage.pureWord
  | Builtin.divOp => some SemanticCoverage.pureWord
  | Builtin.sdivOp => some SemanticCoverage.pureWord
  | Builtin.modOp => some SemanticCoverage.pureWord
  | Builtin.smodOp => some SemanticCoverage.pureWord
  | Builtin.addmodOp => some SemanticCoverage.pureWord
  | Builtin.mulmodOp => some SemanticCoverage.pureWord
  | Builtin.expOp => some SemanticCoverage.pureWord
  | Builtin.sub => some SemanticCoverage.pureWord
  | Builtin.iszero => some SemanticCoverage.pureWord
  | Builtin.eqOp => some SemanticCoverage.pureWord
  | Builtin.ltOp => some SemanticCoverage.pureWord
  | Builtin.gtOp => some SemanticCoverage.pureWord
  | Builtin.sltOp => some SemanticCoverage.pureWord
  | Builtin.sgtOp => some SemanticCoverage.pureWord
  | Builtin.andOp => some SemanticCoverage.pureWord
  | Builtin.orOp => some SemanticCoverage.pureWord
  | Builtin.xorOp => some SemanticCoverage.pureWord
  | Builtin.notOp => some SemanticCoverage.pureWord
  | Builtin.shlOp => some SemanticCoverage.pureWord
  | Builtin.shrOp => some SemanticCoverage.pureWord
  | Builtin.sarOp => some SemanticCoverage.pureWord
  | Builtin.signextendOp => some SemanticCoverage.pureWord
  | Builtin.byteOp => some SemanticCoverage.pureWord
  | Builtin.clzOp => some SemanticCoverage.pureWord
  | Builtin.popOp => some SemanticCoverage.discard
  | Builtin.addressOp => some SemanticCoverage.contextWord
  | Builtin.originOp => some SemanticCoverage.contextWord
  | Builtin.callerOp => some SemanticCoverage.contextWord
  | Builtin.callvalueOp => some SemanticCoverage.contextWord
  | Builtin.gaspriceOp => some SemanticCoverage.contextWord
  | Builtin.calldataloadOp => some SemanticCoverage.bufferRead
  | Builtin.calldatasizeOp => some SemanticCoverage.bufferSize
  | Builtin.calldatacopyOp => some SemanticCoverage.bufferCopy
  | Builtin.returndataloadOp => some SemanticCoverage.bufferRead
  | Builtin.returndatasizeOp => some SemanticCoverage.bufferSize
  | Builtin.returndatacopyOp => some SemanticCoverage.bufferCopy
  | Builtin.blockhashOp => some SemanticCoverage.externalQuery
  | Builtin.coinbaseOp => some SemanticCoverage.contextWord
  | Builtin.timestampOp => some SemanticCoverage.contextWord
  | Builtin.numberOp => some SemanticCoverage.contextWord
  | Builtin.difficultyOp => some SemanticCoverage.contextWord
  | Builtin.prevrandaoOp => some SemanticCoverage.contextWord
  | Builtin.gaslimitOp => some SemanticCoverage.contextWord
  | Builtin.chainidOp => some SemanticCoverage.contextWord
  | Builtin.balanceOp => some SemanticCoverage.externalQuery
  | Builtin.selfbalanceOp => some SemanticCoverage.contextWord
  | Builtin.extcodesizeOp => some SemanticCoverage.externalQuery
  | Builtin.extcodehashOp => some SemanticCoverage.externalQuery
  | Builtin.extcodecopyOp => some SemanticCoverage.bufferCopy
  | Builtin.codecopyOp => some SemanticCoverage.bufferCopy
  | Builtin.datacopyOp => some SemanticCoverage.objectDataCopy
  | Builtin.codesizeOp => some SemanticCoverage.bufferSize
  | Builtin.pcOp => some SemanticCoverage.loweringEnvironment
  | Builtin.msizeOp => some SemanticCoverage.contextWord
  | Builtin.basefeeOp => some SemanticCoverage.contextWord
  | Builtin.gasOp => some SemanticCoverage.loweringEnvironment
  | Builtin.keccak256Op => some SemanticCoverage.memoryHash
  | Builtin.log0Op => some SemanticCoverage.log
  | Builtin.log1Op => some SemanticCoverage.log
  | Builtin.log2Op => some SemanticCoverage.log
  | Builtin.log3Op => some SemanticCoverage.log
  | Builtin.log4Op => some SemanticCoverage.log
  | Builtin.callOp => some SemanticCoverage.externalCall
  | Builtin.callcodeOp => some SemanticCoverage.externalCall
  | Builtin.delegatecallOp => some SemanticCoverage.externalCall
  | Builtin.staticcallOp => some SemanticCoverage.externalCall
  | Builtin.returnOp => some SemanticCoverage.controlHalt
  | Builtin.revertOp => some SemanticCoverage.controlHalt
  | Builtin.invalidOp => some SemanticCoverage.controlHalt
  | Builtin.createOp => some SemanticCoverage.contractCreation
  | Builtin.create2Op => some SemanticCoverage.contractCreation
  | Builtin.selfdestructOp => some SemanticCoverage.selfdestruct
  | Builtin.sload => some SemanticCoverage.storage
  | Builtin.sstore => some SemanticCoverage.storage
  | Builtin.mload => some SemanticCoverage.memoryRead
  | Builtin.mstore => some SemanticCoverage.memoryWrite
  | Builtin.mstore8 => some SemanticCoverage.memoryWrite
  | Builtin.tloadOp => some SemanticCoverage.transientStorage
  | Builtin.tstoreOp => some SemanticCoverage.transientStorage
  | Builtin.mcopyOp => some SemanticCoverage.memoryCopy
  | Builtin.blobhashOp => some SemanticCoverage.externalQuery
  | Builtin.blobbasefeeOp => some SemanticCoverage.contextWord
  | Builtin.setimmutableOp => some SemanticCoverage.compilerBuiltin
  | Builtin.loadimmutableOp => some SemanticCoverage.compilerBuiltin
  | Builtin.linkersymbolOp => some SemanticCoverage.compilerBuiltin
  | Builtin.memoryguardOp => some SemanticCoverage.compilerBuiltin
  | Builtin.verbatimOp _ _ => some SemanticCoverage.verbatim
  | Builtin.opaque _ => none

theorem Builtin.claim?_of_signature? {builtin : Builtin}
    {sig : BuiltinSignature} (h : builtin.signature? = some sig) :
    ∃ claim, builtin.claim? = some claim := by
  cases builtin <;> simp [Builtin.signature?, Builtin.claim?] at h ⊢

theorem Builtin.semanticCoverage?_of_signature? {builtin : Builtin}
    {sig : BuiltinSignature} (h : builtin.signature? = some sig) :
    ∃ coverage, builtin.semanticCoverage? = some coverage := by
  cases builtin <;> simp [Builtin.signature?, Builtin.semanticCoverage?] at h ⊢

theorem Builtin.signature?_of_claim? {builtin : Builtin}
    {claim : ClaimKind} (h : builtin.claim? = some claim) :
    ∃ sig, builtin.signature? = some sig := by
  cases builtin <;> simp [Builtin.claim?, Builtin.signature?] at h ⊢

theorem Builtin.semanticCoverage?_of_claim? {builtin : Builtin}
    {claim : ClaimKind} (h : builtin.claim? = some claim) :
    ∃ coverage, builtin.semanticCoverage? = some coverage := by
  cases builtin <;> simp [Builtin.claim?, Builtin.semanticCoverage?] at h ⊢

theorem Builtin.signature?_of_semanticCoverage? {builtin : Builtin}
    {coverage : SemanticCoverage}
    (h : builtin.semanticCoverage? = some coverage) :
    ∃ sig, builtin.signature? = some sig := by
  cases builtin <;> simp [Builtin.semanticCoverage?, Builtin.signature?] at h ⊢

theorem Builtin.claim?_of_semanticCoverage? {builtin : Builtin}
    {coverage : SemanticCoverage}
    (h : builtin.semanticCoverage? = some coverage) :
    ∃ claim, builtin.claim? = some claim := by
  cases builtin <;> simp [Builtin.semanticCoverage?, Builtin.claim?] at h ⊢

theorem Builtin.opaque_has_no_signature_or_claim (id : Nat) :
    (Builtin.opaque id).signature? = none ∧
      (Builtin.opaque id).claim? = none := by
  constructor <;> rfl

theorem Builtin.opaque_has_no_semanticCoverage (id : Nat) :
    (Builtin.opaque id).semanticCoverage? = none := by
  rfl

theorem Builtin.keccak256_semanticCoverage_memoryHash :
    Builtin.keccak256Op.semanticCoverage? =
      some SemanticCoverage.memoryHash := by
  rfl

theorem Builtin.call_semanticCoverage_externalCall :
    Builtin.callOp.semanticCoverage? =
      some SemanticCoverage.externalCall := by
  rfl

theorem Builtin.keccak256_claim_symbolic :
    Builtin.keccak256Op.claim? = some ClaimKind.symbolic := by
  rfl

theorem Builtin.call_claim_abstracted :
    Builtin.callOp.claim? = some ClaimKind.abstractedBuiltin := by
  rfl

theorem Builtin.gas_claim_deferred :
    Builtin.gasOp.claim? = some ClaimKind.deferredToLowering := by
  rfl

theorem Builtin.pc_claim_deferred :
    Builtin.pcOp.claim? = some ClaimKind.deferredToLowering := by
  rfl

theorem Builtin.gas_and_pc_deferred_to_lowering :
    Builtin.gasOp.claim? = some ClaimKind.deferredToLowering ∧
      Builtin.pcOp.claim? = some ClaimKind.deferredToLowering := by
  constructor <;> rfl

end Evm

end SolidCoreYulCore

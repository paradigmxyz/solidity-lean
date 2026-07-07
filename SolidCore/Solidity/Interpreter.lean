import SolidCore.Solidity.Shared.Account
import SolidCore.Solidity.Shared.External
import SolidCore.Solidity.Shared.Block
import SolidCore.Solidity.Shared.Call
import SolidCore.Solidity.Shared.Log
import SolidCore.Solidity.Shared.Precompile
import SolidCore.Solidity.Keccak
import SolidCore.Solidity.Interaction

namespace SolidCore
namespace Solidity
namespace Source

abbrev Word := SolidCore.Solidity.Shared.Word
abbrev Byte := SolidCore.Solidity.Shared.Account.Byte

def wordModulus : Nat :=
  SolidCore.Solidity.Shared.wordModulus

def normWord (value : Nat) : Word :=
  SolidCore.Solidity.Shared.norm value

def normByte (value : Nat) : Byte :=
  SolidCore.Solidity.Shared.Account.byte value

def bytesToWordBE (bytes : List Byte) : Word :=
  SolidCore.Solidity.Shared.norm
    (bytes.foldl (fun acc byte => acc * 256 + normByte byte) 0)

def readBytes? (bytes : List Byte) (offset size : Nat) :
    Option (List Byte) :=
  let rest := bytes.drop offset
  if size <= rest.length then
    some ((rest.take size).map normByte)
  else
    none

def wordToBytesBE : Nat -> Word -> List Byte
  | 0, _ => []
  | n + 1, value =>
      wordToBytesBE n (value / 256) ++ [normByte value]

def bytesPrefixRightPadded (size : Nat) (bytes : List Byte) : List Byte :=
  let chunk := (bytes.map normByte).take size
  chunk ++ List.replicate (size - chunk.length) 0

def selectorBytes : Nat := 4

def wordBytes : Nat := 32

def readWord? (bytes : List Byte) (offset : Nat) : Option Word :=
  match readBytes? bytes offset wordBytes with
  | some chunk => some (bytesToWordBE chunk)
  | none => none

def calldataSelectorWord (calldata : List Byte) : Word :=
  bytesToWordBE (bytesPrefixRightPadded selectorBytes calldata)

def boolWord (value : Bool) : Word :=
  if value then 1 else 0

def wordTruthy (value : Word) : Bool :=
  !(SolidCore.Solidity.Shared.norm value == 0)

def wordEq (lhs rhs : Word) : Bool :=
  SolidCore.Solidity.Shared.norm lhs == SolidCore.Solidity.Shared.norm rhs

inductive Ty where
  | bool : Ty
  | address : Ty
  | uint256 : Ty
  | int256 : Ty
  | fixedBytes : Nat -> Ty
  | bytesCalldata : Ty
  | externalFunction : Ty
  | fixedArray : Nat -> Ty -> Ty
  | dynamicArray : Ty -> Ty
  | tuple : List Ty -> Ty
  deriving Repr

inductive AbiCleanup where
  | none
  | uint : Nat -> AbiCleanup
  | int : Nat -> AbiCleanup
  | enum : Word -> AbiCleanup
  | fixedArray : Nat -> AbiCleanup -> AbiCleanup
  | dynamicArray : AbiCleanup -> AbiCleanup
  | tuple : List AbiCleanup -> AbiCleanup
  deriving Repr

inductive Value where
  | word : Word -> Value
  | int : Word -> Value
  | bytes : List Byte -> Value
  | externalFunction : Word -> Word -> Value
  | fixedArray : List Value -> Value
  | dynamicArray : List Value -> Value
  | tuple : List Value -> Value
  | storageRef : String -> Value
  | storagePathRef : String -> List Value -> Value
  | memoryRef : Nat -> Value
  | abiLazy : AbiCleanup -> Value -> Value
  deriving Repr

def Ty.defaultValue : Ty -> Value
  | Ty.bool => Value.word 0
  | Ty.address => Value.word 0
  | Ty.uint256 => Value.word 0
  | Ty.int256 => Value.int 0
  | Ty.fixedBytes _ => Value.word 0
  | Ty.bytesCalldata => Value.bytes []
  | Ty.externalFunction => Value.externalFunction 0 0
  | Ty.fixedArray size elementTy =>
      Value.fixedArray (List.replicate size elementTy.defaultValue)
  | Ty.dynamicArray _ => Value.dynamicArray []
  | Ty.tuple elements =>
      Value.tuple (elements.map Ty.defaultValue)

def externalFunctionSelectorModulus : Nat :=
  2 ^ (8 * selectorBytes)

def externalFunctionStorageWord? (addr selector : Word) : Option Word :=
  if SolidCore.Solidity.Shared.norm addr < SolidCore.Solidity.Shared.Account.addressModulus &&
      SolidCore.Solidity.Shared.norm selector < externalFunctionSelectorModulus then
    some
      (normWord
        (SolidCore.Solidity.Shared.Account.addressWord addr *
          externalFunctionSelectorModulus +
          SolidCore.Solidity.Shared.norm selector))
  else
    none

def externalFunctionValueFromStorageWord (word : Word) : Value :=
  Value.externalFunction
    (SolidCore.Solidity.Shared.Account.addressWord
      (SolidCore.Solidity.Shared.norm word / externalFunctionSelectorModulus))
    (SolidCore.Solidity.Shared.norm word % externalFunctionSelectorModulus)

def Value.asWord? : Value -> Option Word
  | Value.word value => some (SolidCore.Solidity.Shared.norm value)
  | _ => none

def Value.asStorageWord? : Value -> Option Word
  | Value.word value => some (SolidCore.Solidity.Shared.norm value)
  | Value.int value => some (SolidCore.Solidity.Shared.norm value)
  | _ => none

def Value.asBytes? : Value -> Option (List Byte)
  | Value.bytes bs => some (bs.map normByte)
  | _ => none

def Value.length? : Value -> Option Nat
  | Value.bytes bs => some bs.length
  | Value.fixedArray values => some values.length
  | Value.dynamicArray values => some values.length
  | Value.tuple values => some values.length
  | Value.word _ => none
  | Value.int _ => none
  | Value.externalFunction _ _ => none
  | Value.storageRef _ => none
  | Value.storagePathRef _ _ => none
  | Value.memoryRef _ => none
  | Value.abiLazy _ value => value.length?

def Value.storageArrayLength? : Value -> Option Nat
  | Value.word length => some (SolidCore.Solidity.Shared.norm length)
  | value => value.length?

def Value.defaultLike : Value -> Value
  | Value.word _ => Value.word 0
  | Value.int _ => Value.int 0
  | Value.bytes _ => Value.bytes []
  | Value.externalFunction _ _ => Value.externalFunction 0 0
  | Value.fixedArray values => Value.fixedArray (values.map Value.defaultLike)
  | Value.dynamicArray _ => Value.dynamicArray []
  | Value.tuple values => Value.tuple (values.map Value.defaultLike)
  | Value.storageRef target => Value.storageRef target
  | Value.storagePathRef target indexes => Value.storagePathRef target indexes
  | Value.memoryRef id => Value.memoryRef id
  | Value.abiLazy _ value => value.defaultLike

def Value.isMemoryObject : Value -> Bool
  | Value.bytes _ => true
  | Value.fixedArray _ => true
  | Value.dynamicArray _ => true
  | Value.tuple _ => true
  | Value.abiLazy _ value => value.isMemoryObject
  | _ => false

def Value.storageRefForPath (target : String) (indexes : List Value) :
    Value :=
  match indexes with
  | [] => Value.storageRef target
  | _ => Value.storagePathRef target indexes

def Value.concatBytes? : List Value -> Option (List Byte)
  | [] => some []
  | value :: rest =>
      match value.asBytes? with
      | some bs => do
          let tail ← Value.concatBytes? rest
          some (bs ++ tail)
      | none => none

def listUpdateAt? {α : Type} : List α -> Nat -> α -> Option (List α)
  | [], _, _ => none
  | _ :: rest, 0, value => some (value :: rest)
  | head :: rest, index + 1, value =>
      match listUpdateAt? rest index value with
      | some updated => some (head :: updated)
      | none => none

def listGet? {α : Type} : List α -> Nat -> Option α
  | [], _ => none
  | head :: _, 0 => some head
  | _ :: rest, index + 1 => listGet? rest index

inductive RevertData where
  | empty : RevertData
  | panic : Word -> RevertData
  | error : String -> RevertData
  | custom : String -> List Value -> RevertData
  | raw : List Byte -> RevertData
  deriving Repr

def RevertData.overflow : RevertData :=
  RevertData.panic 0x11

def RevertData.assertFailure : RevertData :=
  RevertData.panic 0x01

def RevertData.divByZero : RevertData :=
  RevertData.panic 0x12

def RevertData.enumConversion : RevertData :=
  RevertData.panic 0x21

def RevertData.invalidStorageByteArray : RevertData :=
  RevertData.panic 0x22

def RevertData.popEmptyArray : RevertData :=
  RevertData.panic 0x31

def RevertData.indexOutOfBounds : RevertData :=
  RevertData.panic 0x32

def RevertData.memoryAllocationTooLarge : RevertData :=
  RevertData.panic 0x41

def RevertData.typeMismatch : RevertData :=
  RevertData.panic 0

def RevertData.fromRawBytes (bytes : List Byte) : RevertData :=
  if bytes.map normByte == [] then
    RevertData.empty
  else
    RevertData.raw bytes

mutual

def AbiCleanup.accepts : AbiCleanup -> Value -> Bool
  | AbiCleanup.none, _ => true
  | AbiCleanup.uint bits, Value.word value =>
      0 < bits && bits <= 256 && SolidCore.Solidity.Shared.norm value < 2 ^ bits
  | AbiCleanup.int bits, Value.int value =>
      if 0 < bits && bits <= 256 then
        let modulus := 2 ^ bits
        let signBit := 2 ^ (bits - 1)
        let low := SolidCore.Solidity.Shared.norm value % modulus
        let canonical :=
          if signBit <= low then
            SolidCore.Solidity.Shared.norm (wordModulus - modulus + low)
          else
            SolidCore.Solidity.Shared.norm low
        wordEq canonical value
      else
        false
  | AbiCleanup.enum maxValue, Value.word value =>
      SolidCore.Solidity.Shared.norm value <= SolidCore.Solidity.Shared.norm maxValue
  | AbiCleanup.fixedArray size cleanup, Value.fixedArray values =>
      values.length == size && AbiCleanup.acceptsAll cleanup values
  | AbiCleanup.dynamicArray cleanup, Value.dynamicArray values =>
      AbiCleanup.acceptsAll cleanup values
  | AbiCleanup.tuple cleanups, Value.tuple values =>
      AbiCleanups.accept cleanups values
  | cleanup, Value.abiLazy inner value =>
      inner.accepts value && cleanup.accepts value
  | _, _ => false

def AbiCleanup.acceptsAll (cleanup : AbiCleanup) : List Value -> Bool
  | [] => true
  | value :: rest => cleanup.accepts value && cleanup.acceptsAll rest

def AbiCleanups.accept : List AbiCleanup -> List Value -> Bool
  | [], [] => true
  | cleanup :: cleanups, value :: values =>
      cleanup.accepts value && AbiCleanups.accept cleanups values
  | _, _ => false

end

def AbiCleanup.forceValue (cleanup : AbiCleanup)
    (value : Value) : Except RevertData Value :=
  if cleanup.accepts value then
    Except.ok value
  else
    Except.error RevertData.empty

def Value.forceAbiLazy : Value -> Except RevertData Value
  | Value.abiLazy cleanup value => cleanup.forceValue value
  | value => Except.ok value

def Value.expectWordRaw : Value -> Except RevertData Word
  | Value.word value => Except.ok (SolidCore.Solidity.Shared.norm value)
  | _ => Except.error RevertData.typeMismatch

def Value.expectWord : Value -> Except RevertData Word
  | Value.word value => Except.ok (SolidCore.Solidity.Shared.norm value)
  | Value.abiLazy cleanup value => do
      let forced ← cleanup.forceValue value
      forced.expectWordRaw
  | _ => Except.error RevertData.typeMismatch

mutual

def Ty.coerceValue? : Ty -> Value -> Option Value
  | ty, Value.abiLazy cleanup value => do
      let coerced ← Ty.coerceValue? ty value
      some (Value.abiLazy cleanup coerced)
  | Ty.bool, Value.word value =>
      if wordEq value 0 || wordEq value 1 then
        some (Value.word value)
      else
        none
  | Ty.address, Value.word value => some (Value.word value)
  | Ty.uint256, Value.word value => some (Value.word value)
  | Ty.int256, Value.int value => some (Value.int value)
  | Ty.int256, Value.word value => some (Value.int value)
  | Ty.fixedBytes _, Value.word value => some (Value.word value)
  | Ty.bytesCalldata, Value.bytes bytes => some (Value.bytes bytes)
  | Ty.externalFunction, Value.externalFunction addr selector =>
      some (Value.externalFunction addr selector)
  | Ty.fixedArray size elementTy, Value.fixedArray values =>
      if values.length == size then
        match Ty.coerceValueList? elementTy values with
        | some coerced => some (Value.fixedArray coerced)
        | none => none
      else
        none
  | Ty.dynamicArray elementTy, Value.dynamicArray values =>
      match Ty.coerceValueList? elementTy values with
      | some coerced => some (Value.dynamicArray coerced)
      | none => none
  | Ty.tuple tys, Value.tuple values =>
      match Ty.coerceTupleValues? tys values with
      | some coerced => some (Value.tuple coerced)
      | none => none
  | _, _ => none

def Ty.coerceValueList? (ty : Ty) : List Value -> Option (List Value)
  | [] => some []
  | value :: rest => do
      let head ← Ty.coerceValue? ty value
      let tail ← Ty.coerceValueList? ty rest
      some (head :: tail)

def Ty.coerceTupleValues? : List Ty -> List Value -> Option (List Value)
  | [], [] => some []
  | ty :: tys, value :: values => do
      let head ← Ty.coerceValue? ty value
      let tail ← Ty.coerceTupleValues? tys values
      some (head :: tail)
  | _, _ => none

end

def Ty.storageValueFromWord? : Ty -> Word -> Option Value
  | Ty.bool, value =>
      if wordEq value 0 || wordEq value 1 then
        some (Value.word value)
      else
        none
  | Ty.address, value => some (Value.word value)
  | Ty.uint256, value => some (Value.word value)
  | Ty.int256, value => some (Value.int value)
  | Ty.fixedBytes _, value => some (Value.word value)
  | Ty.externalFunction, value =>
      some (externalFunctionValueFromStorageWord value)
  | _, _ => none

mutual

def Value.coerceLike? : Value -> Value -> Option Value
  | template, Value.abiLazy cleanup value => do
      let coerced ← Value.coerceLike? template value
      some (Value.abiLazy cleanup coerced)
  | Value.abiLazy _ template, value =>
      Value.coerceLike? template value
  | Value.word _, Value.word value => some (Value.word value)
  | Value.int _, Value.int value => some (Value.int value)
  | Value.int _, Value.word value => some (Value.int value)
  | Value.bytes _, Value.bytes bs => some (Value.bytes bs)
  | Value.externalFunction _ _, Value.externalFunction addr selector =>
      some (Value.externalFunction addr selector)
  | Value.fixedArray oldValues, Value.fixedArray values =>
      match Value.coerceLikeList? oldValues values with
      | some coerced => some (Value.fixedArray coerced)
      | none => none
  | Value.dynamicArray oldValues, Value.dynamicArray values =>
      match Value.coerceDynamicArrayLike? oldValues values with
      | some coerced => some (Value.dynamicArray coerced)
      | none => none
  | Value.tuple oldValues, Value.tuple values =>
      match Value.coerceLikeList? oldValues values with
      | some coerced => some (Value.tuple coerced)
      | none => none
  | _, _ => none

def Value.coerceLikeList? : List Value -> List Value -> Option (List Value)
  | [], [] => some []
  | oldValue :: oldValues, value :: values => do
      let head ← Value.coerceLike? oldValue value
      let tail ← Value.coerceLikeList? oldValues values
      some (head :: tail)
  | _, _ => none

def Value.coerceDynamicArrayLike? :
    List Value -> List Value -> Option (List Value)
  | [], values => some values
  | _ :: _, [] => some []
  | template :: templates, value :: values => do
      let head ← Value.coerceLike? template value
      let tail ←
        Value.coerceDynamicArrayLike? (template :: templates) values
      some (head :: tail)

end

def Value.index? (container : Value) (index : Word) :
    Except RevertData Value :=
  match container with
  | Value.bytes bs =>
      match listGet? (bs.map normByte) (SolidCore.Solidity.Shared.norm index) with
      | some byte => Except.ok (Value.word byte)
      | none => Except.error RevertData.indexOutOfBounds
  | Value.fixedArray values =>
      match listGet? values (SolidCore.Solidity.Shared.norm index) with
      | some value => Except.ok value
      | none => Except.error RevertData.indexOutOfBounds
  | Value.dynamicArray values =>
      match listGet? values (SolidCore.Solidity.Shared.norm index) with
      | some value => Except.ok value
      | none => Except.error RevertData.indexOutOfBounds
  | Value.tuple values =>
      match listGet? values (SolidCore.Solidity.Shared.norm index) with
      | some value => Except.ok value
      | none => Except.error RevertData.indexOutOfBounds
  | Value.word _ =>
      Except.error RevertData.typeMismatch
  | Value.int _ =>
      Except.error RevertData.typeMismatch
  | Value.externalFunction _ _ =>
      Except.error RevertData.typeMismatch
  | Value.storageRef _ =>
      Except.error RevertData.typeMismatch
  | Value.storagePathRef _ _ =>
      Except.error RevertData.typeMismatch
  | Value.memoryRef _ =>
      Except.error RevertData.typeMismatch
  | Value.abiLazy _ _ =>
      Except.error RevertData.typeMismatch

def fixedBytesIndex? (size : Nat) (value index : Word) :
    Except RevertData Value :=
  if 0 < size && size <= wordBytes then
    match listGet? (wordToBytesBE size value) (SolidCore.Solidity.Shared.norm index) with
    | some byte => Except.ok (Value.word byte)
    | none => Except.error RevertData.indexOutOfBounds
  else
    Except.error RevertData.typeMismatch

def fixedBytesCast? (targetSize sourceSize : Nat) (value : Word) :
    Except RevertData Value :=
  if 0 < targetSize && targetSize <= wordBytes &&
      0 < sourceSize && sourceSize <= wordBytes then
    Except.ok
      (Value.word
        (bytesToWordBE
          (bytesPrefixRightPadded targetSize
            (wordToBytesBE sourceSize value))))
  else
    Except.error RevertData.typeMismatch

def fixedBytesFromBytes? (targetSize : Nat) (bytes : List Byte) :
    Except RevertData Value :=
  if 0 < targetSize && targetSize <= wordBytes then
    Except.ok
      (Value.word
        (bytesToWordBE
          (bytesPrefixRightPadded targetSize bytes)))
  else
    Except.error RevertData.typeMismatch

def uintCast? (bits : Nat) (value : Value) : Except RevertData Value :=
  if 0 < bits && bits <= 256 then
    match value.asStorageWord? with
    | some word => Except.ok (Value.word (SolidCore.Solidity.Shared.norm word % (2 ^ bits)))
    | none => Except.error RevertData.typeMismatch
  else
    Except.error RevertData.typeMismatch

def uintCleanup? (checked : Bool) (bits : Nat) (value : Value) :
    Except RevertData Value :=
  if 0 < bits && bits <= 256 then
    match value.asStorageWord? with
    | some word =>
        if checked && !(SolidCore.Solidity.Shared.norm word < 2 ^ bits) then
          Except.error RevertData.overflow
        else
          uintCast? bits value
    | none => Except.error RevertData.typeMismatch
  else
    Except.error RevertData.typeMismatch

def intCast? (bits : Nat) (value : Value) : Except RevertData Value :=
  if 0 < bits && bits <= 256 then
    match value.asStorageWord? with
    | some word =>
        let modulus := 2 ^ bits
        let signBit := 2 ^ (bits - 1)
        let low := SolidCore.Solidity.Shared.norm word % modulus
        let casted :=
          if signBit <= low then
            SolidCore.Solidity.Shared.norm (wordModulus - modulus + low)
          else
            SolidCore.Solidity.Shared.norm low
        Except.ok (Value.int casted)
    | none => Except.error RevertData.typeMismatch
  else
    Except.error RevertData.typeMismatch

def intCleanup? (checked : Bool) (bits : Nat) (value : Value) :
    Except RevertData Value :=
  if 0 < bits && bits <= 256 then
    match value.asStorageWord? with
    | some word =>
        let signed := SolidCore.Solidity.Shared.signedValue word
        let min := -(Int.ofNat (2 ^ (bits - 1)))
        let max := Int.ofNat ((2 ^ (bits - 1)) - 1)
        if checked && (signed < min || max < signed) then
          Except.error RevertData.overflow
        else
          intCast? bits value
    | none => Except.error RevertData.typeMismatch
  else
    Except.error RevertData.typeMismatch

def sliceListByWords? {α : Type} (values : List α)
    (start? stop? : Option Word) : Except RevertData (List α) :=
  let start :=
    match start? with
    | some value => SolidCore.Solidity.Shared.norm value
    | none => 0
  let stop :=
    match stop? with
    | some value => SolidCore.Solidity.Shared.norm value
    | none => values.length
  if start <= stop && stop <= values.length then
    Except.ok ((values.drop start).take (stop - start))
  else
    Except.error RevertData.indexOutOfBounds

def Value.slice? (container : Value) (start? stop? : Option Word) :
    Except RevertData Value :=
  match container with
  | Value.bytes bs =>
      let bytes := bs.map normByte
      match sliceListByWords? bytes start? stop? with
      | Except.ok sliced => Except.ok (Value.bytes sliced)
      | Except.error err => Except.error err
  | Value.fixedArray values =>
      match sliceListByWords? values start? stop? with
      | Except.ok sliced => Except.ok (Value.dynamicArray sliced)
      | Except.error err => Except.error err
  | Value.dynamicArray values =>
      match sliceListByWords? values start? stop? with
      | Except.ok sliced => Except.ok (Value.dynamicArray sliced)
      | Except.error err => Except.error err
  | _ => Except.error RevertData.typeMismatch

def Value.setIndex? (container : Value) (index : Word) (value : Value) :
    Except RevertData Value :=
  match container with
  | Value.fixedArray values =>
      match listUpdateAt? values (SolidCore.Solidity.Shared.norm index) value with
      | some updated => Except.ok (Value.fixedArray updated)
      | none => Except.error RevertData.indexOutOfBounds
  | Value.dynamicArray values =>
      match listUpdateAt? values (SolidCore.Solidity.Shared.norm index) value with
      | some updated => Except.ok (Value.dynamicArray updated)
      | none => Except.error RevertData.indexOutOfBounds
  | Value.bytes bs =>
      match value.asWord? with
      | some w =>
          match listUpdateAt? (bs.map normByte)
              (SolidCore.Solidity.Shared.norm index) (normByte w) with
          | some updated => Except.ok (Value.bytes updated)
          | none => Except.error RevertData.indexOutOfBounds
      | none => Except.error RevertData.typeMismatch
  | Value.tuple values =>
      match listUpdateAt? values (SolidCore.Solidity.Shared.norm index) value with
      | some updated => Except.ok (Value.tuple updated)
      | none => Except.error RevertData.indexOutOfBounds
  | Value.word _ =>
      Except.error RevertData.typeMismatch
  | Value.int _ =>
      Except.error RevertData.typeMismatch
  | Value.externalFunction _ _ =>
      Except.error RevertData.typeMismatch
  | Value.storageRef _ =>
      Except.error RevertData.typeMismatch
  | Value.storagePathRef _ _ =>
      Except.error RevertData.typeMismatch
  | Value.memoryRef _ =>
      Except.error RevertData.typeMismatch
  | Value.abiLazy _ _ =>
      Except.error RevertData.typeMismatch

abbrev WordMap := List (Word × Word)

def WordMap.lookup? : WordMap -> Word -> Option Word
  | [], _ => none
  | (key, value) :: rest, query =>
      if wordEq key query then
        some (SolidCore.Solidity.Shared.norm value)
      else
        WordMap.lookup? rest query

def WordMap.insertLoop : WordMap -> Word -> Word -> WordMap
  | [], key, value =>
      [(SolidCore.Solidity.Shared.norm key, SolidCore.Solidity.Shared.norm value)]
  | (entryKey, entryValue) :: rest, key, value =>
      if wordEq entryKey key then
        (SolidCore.Solidity.Shared.norm key, SolidCore.Solidity.Shared.norm value) :: rest
      else
        (entryKey, entryValue) :: WordMap.insertLoop rest key value

abbrev ByteMap := List (Word × List Byte)

def ByteMap.lookup? : ByteMap -> Word -> Option (List Byte)
  | [], _ => none
  | (key, value) :: rest, query =>
      if wordEq key query then
        some (value.map normByte)
      else
        ByteMap.lookup? rest query

abbrev MemoryMap := List (Nat × Value)

def MemoryMap.lookup? : MemoryMap -> Nat -> Option Value
  | [], _ => none
  | (key, value) :: rest, query =>
      if key == query then
        some value
      else
        MemoryMap.lookup? rest query

def MemoryMap.insertLoop : MemoryMap -> Nat -> Value -> MemoryMap
  | [], key, value => [(key, value)]
  | (entryKey, entryValue) :: rest, key, value =>
      if entryKey == key then
        (key, value) :: rest
      else
        (entryKey, entryValue) :: MemoryMap.insertLoop rest key value


abbrev ImmutableMap := List (String × Value)

def ImmutableMap.lookup? : ImmutableMap -> String -> Option Value
  | [], _ => none
  | (name, value) :: rest, query =>
      if name == query then
        some value
      else
        ImmutableMap.lookup? rest query

def ImmutableMap.insertLoop : ImmutableMap -> String -> Value -> ImmutableMap
  | [], name, value => [(name, value)]
  | (entryName, entryValue) :: rest, name, value =>
      if entryName == name then
        (name, value) :: rest
      else
        (entryName, entryValue) :: ImmutableMap.insertLoop rest name value

structure Event where
  name : String
  indexed : List Value
  data : List Value
  topics : List Word := []
  dataBytes : List Byte := []
  deriving Repr

def Event.toLogEntry (self : Word) (event : Event) :
    SolidCore.Solidity.Shared.Log.Entry :=
  { address := SolidCore.Solidity.Shared.Account.addressWord self
    topics := event.topics.map SolidCore.Solidity.Shared.norm
    data := SolidCore.Solidity.Shared.Account.normalizeBytes event.dataBytes }

abbrev SourceExternalCallResult :=
  SolidCore.Solidity.Shared.Call.Result SolidCore.Solidity.Shared.Call.ExternalCallKind

abbrev SourceContractCreationResult :=
  SolidCore.Solidity.Shared.Call.CreationResult

inductive ExternalInteraction where
  | lowLevelCall : SourceExternalCallResult -> ExternalInteraction
  | contractCreation :
      SourceContractCreationResult -> ExternalInteraction
  deriving Repr

structure State where
  storage : WordMap
  transient : WordMap := []
  immutables : ImmutableMap := []
  selfdestructs : List (Word × Word) := []
  selfdestructEffects : List SolidCore.Solidity.Shared.Account.SelfdestructRecord := []
  externalInteractions : List ExternalInteraction := []
  events : List Event
  deriving Repr

def State.empty : State :=
  { storage := [], transient := [], immutables := [], events := [] }

def State.logEntries (state : State) (self : Word) :
    List SolidCore.Solidity.Shared.Log.Entry :=
  state.events.map (Event.toLogEntry self)

def State.loadSlot (state : State) (slot : Word) : Word :=
  match WordMap.lookup? state.storage slot with
  | some value => value
  | none => 0

def State.storeSlot (state : State) (slot value : Word) : State :=
  { state with storage := WordMap.insertLoop state.storage slot value }

def State.loadTransientSlot (state : State) (slot : Word) : Word :=
  match WordMap.lookup? state.transient slot with
  | some value => value
  | none => 0

def State.storeTransientSlot (state : State) (slot value : Word) : State :=
  { state with transient := WordMap.insertLoop state.transient slot value }

def State.clearTransient (state : State) : State :=
  { state with transient := [] }

def State.immutable? (state : State) (name : String) : Option Value :=
  ImmutableMap.lookup? state.immutables name

def State.storeImmutable (state : State) (name : String)
    (value : Value) : State :=
  { state with
    immutables := ImmutableMap.insertLoop state.immutables name value }

def State.recordSelfdestruct (state : State)
    (evmVersion : SolidCore.Solidity.Shared.Block.EvmVersion)
    (createdAccounts : List Word) (self recipient : Word) : State :=
  let record :=
    SolidCore.Solidity.Shared.Account.selfdestructRecord
      evmVersion createdAccounts self recipient
  { state with
    selfdestructs :=
      state.selfdestructs ++
        [(record.fromAddress, record.recipient)]
    selfdestructEffects := state.selfdestructEffects ++ [record] }

abbrev Frame := List (String × Value)
abbrev LocalEnv := List Frame

def Frame.lookup? : Frame -> String -> Option Value
  | [], _ => none
  | (name, value) :: rest, query =>
      if name = query then
        some value
      else
        Frame.lookup? rest query

def Frame.assign? : Frame -> String -> Value -> Option Frame
  | [], _, _ => none
  | (name, oldValue) :: rest, query, value =>
      if name = query then
        some ((name, value) :: rest)
      else
        match Frame.assign? rest query value with
        | some updated => some ((name, oldValue) :: updated)
        | none => none

def LocalEnv.lookup? : LocalEnv -> String -> Option Value
  | [], _ => none
  | frame :: rest, name =>
      match Frame.lookup? frame name with
      | some value => some value
      | none => LocalEnv.lookup? rest name

def LocalEnv.assign? : LocalEnv -> String -> Value -> Option LocalEnv
  | [], _, _ => none
  | frame :: rest, name, value =>
      match Frame.assign? frame name value with
      | some updated => some (updated :: rest)
      | none =>
          match LocalEnv.assign? rest name value with
          | some updatedRest => some (frame :: updatedRest)
          | none => none

def LocalEnv.declare (locals : LocalEnv) (name : String) (value : Value) :
    LocalEnv :=
  match locals with
  | [] => [[(name, value)]]
  | frame :: rest => ((name, value) :: frame) :: rest

def Frame.visibleBindingsFrom (seen : List String) :
    Frame -> List String × Frame
  | [] => (seen, [])
  | (name, value) :: rest =>
      if seen.any (fun seenName => seenName == name) then
        Frame.visibleBindingsFrom seen rest
      else
        let (seen', visibleRest) :=
          Frame.visibleBindingsFrom (name :: seen) rest
        (seen', (name, value) :: visibleRest)

def LocalEnv.currentFrame : LocalEnv -> Frame
  | [] => []
  | frame :: _ => frame

def LocalEnv.visibleBindingsFrom (seen : List String) :
    LocalEnv -> Frame
  | [] => []
  | frame :: rest =>
      let (seen', visibleFrame) := Frame.visibleBindingsFrom seen frame
      visibleFrame ++ LocalEnv.visibleBindingsFrom seen' rest

def LocalEnv.visibleBindings (locals : LocalEnv) : Frame :=
  LocalEnv.visibleBindingsFrom [] locals

structure Runtime where
  state : State
  locals : LocalEnv
  memory : MemoryMap := []
  nextMemory : Nat := 0
  deriving Repr

def Runtime.ofState (state : State) : Runtime :=
  { state, locals := [[]] }

def Runtime.recordExternalInteraction
    (runtime : Runtime) (interaction : ExternalInteraction) : Runtime :=
  { runtime with
    state :=
      { runtime.state with
        externalInteractions :=
          runtime.state.externalInteractions ++ [interaction] } }

def Runtime.pushScope (runtime : Runtime) : Runtime :=
  { runtime with locals := [] :: runtime.locals }

def Runtime.popScope (runtime : Runtime) : Runtime :=
  { runtime with locals := runtime.locals.drop 1 }

def Runtime.lookupLocal? (runtime : Runtime) (name : String) :
    Option Value :=
  LocalEnv.lookup? runtime.locals name

def Runtime.loadMemory? (runtime : Runtime) (id : Nat) : Option Value :=
  MemoryMap.lookup? runtime.memory id

def Runtime.allocMemory (runtime : Runtime) (value : Value) :
    Runtime × Value :=
  let id := runtime.nextMemory
  ( { runtime with
      memory := MemoryMap.insertLoop runtime.memory id value
      nextMemory := id + 1 }
  , Value.memoryRef id )

def Runtime.derefMemoryValue (runtime : Runtime) (value : Value) :
    Except RevertData Value :=
  match value with
  | Value.memoryRef id =>
      match runtime.loadMemory? id with
      | some stored => Except.ok stored
      | none => Except.error RevertData.typeMismatch
  | Value.abiLazy cleanup value =>
      cleanup.forceValue value
  | _ => Except.ok value

mutual

def Runtime.derefMemoryValueWithFuel (runtime : Runtime) :
    Nat -> Value -> Except RevertData Value
  | 0, _ => Except.error RevertData.typeMismatch
  | fuel + 1, Value.memoryRef id =>
      match runtime.loadMemory? id with
      | some stored => runtime.derefMemoryValueWithFuel fuel stored
      | none => Except.error RevertData.typeMismatch
  | fuel + 1, Value.abiLazy cleanup value => do
      let value ← cleanup.forceValue value
      runtime.derefMemoryValueWithFuel fuel value
  | fuel + 1, Value.fixedArray values => do
      let values ← runtime.derefMemoryValuesWithFuel (fuel + 1) values
      Except.ok (Value.fixedArray values)
  | fuel + 1, Value.dynamicArray values => do
      let values ← runtime.derefMemoryValuesWithFuel (fuel + 1) values
      Except.ok (Value.dynamicArray values)
  | fuel + 1, Value.tuple values => do
      let values ← runtime.derefMemoryValuesWithFuel (fuel + 1) values
      Except.ok (Value.tuple values)
  | _fuel + 1, value => Except.ok value

def Runtime.derefMemoryValuesWithFuel (runtime : Runtime)
    (fuel : Nat) : List Value -> Except RevertData (List Value)
  | [] => Except.ok []
  | value :: rest => do
      let value ← runtime.derefMemoryValueWithFuel fuel value
      let rest ← runtime.derefMemoryValuesWithFuel fuel rest
      Except.ok (value :: rest)

end

def Runtime.derefMemoryValueDeep (runtime : Runtime)
    (value : Value) : Except RevertData Value :=
  runtime.derefMemoryValueWithFuel (runtime.nextMemory + 1) value

def Runtime.derefMemoryValuesDeep (runtime : Runtime)
    (values : List Value) : Except RevertData (List Value) :=
  runtime.derefMemoryValuesWithFuel (runtime.nextMemory + 1) values

def Runtime.storageMaterializedValue (runtime : Runtime)
    (value : Value) : Except RevertData Value :=
  runtime.derefMemoryValueDeep value

mutual

def Runtime.memoryStoredValue (runtime : Runtime) (value : Value) :
    Runtime × Value :=
  match value with
  | Value.fixedArray values =>
      let (runtime', storedValues) := runtime.memoryStoredValues values
      (runtime', Value.fixedArray storedValues)
  | Value.dynamicArray values =>
      let (runtime', storedValues) := runtime.memoryStoredValues values
      (runtime', Value.dynamicArray storedValues)
  | Value.tuple values =>
      let (runtime', storedValues) := runtime.memoryStoredValues values
      (runtime', Value.tuple storedValues)
  | _ => (runtime, value)

def Runtime.memoryStoredValues (runtime : Runtime) :
    List Value -> Runtime × List Value
  | [] => (runtime, [])
  | value :: rest =>
      let (runtime', storedValue) :=
        if value.isMemoryObject then
          let (nestedRuntime, nestedValue) :=
            runtime.memoryStoredValue value
          nestedRuntime.allocMemory nestedValue
        else
          (runtime, value)
      let (runtime'', storedRest) :=
        runtime'.memoryStoredValues rest
      (runtime'', storedValue :: storedRest)

end

def Runtime.storeMemory? (runtime : Runtime) (id : Nat)
    (value : Value) : Option Runtime :=
  match runtime.loadMemory? id with
  | some _ =>
      let (runtime', storedValue) := runtime.memoryStoredValue value
      some
        { runtime' with
          memory := MemoryMap.insertLoop runtime'.memory id storedValue }
  | none => none

def Runtime.memoryStoreValue (runtime : Runtime) (value : Value) :
    Runtime × Value :=
  match value with
  | Value.memoryRef _ => (runtime, value)
  | _ =>
      if value.isMemoryObject then
        let (runtime', storedValue) := runtime.memoryStoredValue value
        runtime'.allocMemory storedValue
      else
        (runtime, value)

def Runtime.lookupMemoryRef? (runtime : Runtime) (name : String) :
    Option Nat :=
  match runtime.lookupLocal? name with
  | some (Value.memoryRef id) => some id
  | _ => none

def Runtime.lookupStorageRef? (runtime : Runtime) (name : String) :
    Option String :=
  match runtime.lookupLocal? name with
  | some (Value.storageRef target) => some target
  | _ => none

def Runtime.lookupStoragePathRef? (runtime : Runtime) (name : String) :
    Option (String × List Value) :=
  match runtime.lookupLocal? name with
  | some (Value.storageRef target) => some (target, [])
  | some (Value.storagePathRef target indexes) => some (target, indexes)
  | _ => none

def Runtime.assignStorageRef?
    (runtime : Runtime) (name target : String) : Option Runtime :=
  match runtime.lookupLocal? name with
  | some (Value.storageRef _) | some (Value.storagePathRef _ _) =>
      match LocalEnv.assign? runtime.locals name (Value.storageRef target) with
      | some locals => some { runtime with locals }
      | none => none
  | _ => none

def Runtime.assignStoragePathRef?
    (runtime : Runtime) (name target : String) (indexes : List Value) :
    Option Runtime :=
  match runtime.lookupLocal? name with
  | some (Value.storageRef _) | some (Value.storagePathRef _ _) =>
      match
        LocalEnv.assign? runtime.locals name
          (Value.storageRefForPath target indexes)
      with
      | some locals => some { runtime with locals }
      | none => none
  | _ => none

def Runtime.declareLocal
    (runtime : Runtime) (name : String) (value : Value) : Runtime :=
  { runtime with locals := LocalEnv.declare runtime.locals name value }

def Runtime.assignLocalRaw?
    (runtime : Runtime) (name : String) (value : Value) :
    Option Runtime :=
  match LocalEnv.assign? runtime.locals name value with
  | some locals => some { runtime with locals }
  | none => none

def Runtime.assignLocal?
    (runtime : Runtime) (name : String) (value : Value) :
    Option Runtime :=
  match runtime.lookupLocal? name with
  | some (Value.memoryRef _) =>
      match value with
      | Value.memoryRef id =>
          runtime.assignLocalRaw? name (Value.memoryRef id)
      | _ =>
          if value.isMemoryObject then
            let (runtime', storedValue) := runtime.memoryStoredValue value
            let (runtime'', ref) := runtime'.allocMemory storedValue
            runtime''.assignLocalRaw? name ref
          else
            none
  | some oldValue =>
      match oldValue.coerceLike? value with
      | some coerced =>
          match LocalEnv.assign? runtime.locals name coerced with
          | some locals => some { runtime with locals }
          | none => none
      | none => none
  | none => none

def Runtime.assignNamedValues? (runtime : Runtime) :
    List String -> List Value -> Option Runtime
  | [], [] => some runtime
  | name :: names, value :: values =>
      match runtime.assignLocal? name value with
      | some updated => Runtime.assignNamedValues? updated names values
      | none => none
  | _, _ => none

def Runtime.declareMemoryLocal (runtime : Runtime) (ty : Ty)
    (name : String) (value : Value) : Option Runtime := do
  let coerced ← ty.coerceValue? value
  let (runtime', storedValue) := runtime.memoryStoredValue coerced
  let (runtime'', ref) := runtime'.allocMemory storedValue
  some (runtime''.declareLocal name ref)

def Runtime.localizeMemoryLocal (runtime : Runtime) (ty : Ty)
    (name : String) : Option Runtime := do
  match runtime.lookupLocal? name with
  | some (Value.memoryRef _) => some runtime
  | some value => do
      let coerced ← ty.coerceValue? value
      let (runtime', storedValue) := runtime.memoryStoredValue coerced
      let (runtime'', ref) := runtime'.allocMemory storedValue
      runtime''.assignLocalRaw? name ref
  | none => none

inductive StorageLayout where
  | scalar : Ty -> StorageLayout
  | packedScalar : Nat -> Nat -> Bool -> Ty -> StorageLayout
  | struct : List StorageLayout -> StorageLayout
  | fixedArray : Nat -> StorageLayout -> StorageLayout
  | dynamicArray : StorageLayout -> StorageLayout
  | bytes : StorageLayout
  | string : StorageLayout
  | mapping : Ty -> StorageLayout -> StorageLayout
  deriving Repr

structure StorageLayoutCursor where
  slot : Nat
  offset : Nat := 0
  deriving Repr

def StorageLayoutCursor.finishSlot (cursor : StorageLayoutCursor) : Nat :=
  if cursor.offset == 0 then cursor.slot else cursor.slot + 1

def StorageLayoutCursor.align (cursor : StorageLayoutCursor) :
    StorageLayoutCursor :=
  if cursor.offset == 0 then cursor
  else { slot := cursor.slot + 1, offset := 0 }

def natCeilDiv (n d : Nat) : Nat :=
  if d == 0 then 0 else (n + d - 1) / d

mutual

def StorageLayout.slotSpan : StorageLayout -> Nat
  | StorageLayout.scalar _ => 1
  | StorageLayout.packedScalar _ _ _ _ => 1
  | StorageLayout.struct layouts => StorageLayouts.slotSpan layouts
  | StorageLayout.fixedArray size
      (StorageLayout.packedScalar _ widthBytes _ _) =>
      natCeilDiv (size * widthBytes) wordBytes
  | StorageLayout.fixedArray size elementLayout =>
      size * StorageLayout.slotSpan elementLayout
  | StorageLayout.dynamicArray _ => 1
  | StorageLayout.bytes => 1
  | StorageLayout.string => 1
  | StorageLayout.mapping _ _ => 1

def StorageLayouts.slotSpan : List StorageLayout -> Nat
  | layouts =>
      (StorageLayouts.cursorAfter { slot := 0, offset := 0 }
        layouts).finishSlot

def StorageLayout.cursorStep (cursor : StorageLayoutCursor)
    (layout : StorageLayout) : Nat × StorageLayoutCursor :=
  match layout with
  | StorageLayout.packedScalar offset widthBytes _ _ =>
      let slot :=
        if offset < cursor.offset then cursor.slot + 1 else cursor.slot
      let nextOffset := offset + widthBytes
      let next :=
        if nextOffset == wordBytes then
          { slot := slot + 1, offset := 0 }
        else
          { slot := slot, offset := nextOffset }
      (slot, next)
  | StorageLayout.scalar _
  | StorageLayout.dynamicArray _
  | StorageLayout.bytes
  | StorageLayout.string
  | StorageLayout.mapping _ _ =>
      let aligned := cursor.align
      (aligned.slot, { slot := aligned.slot + 1, offset := 0 })
  | StorageLayout.struct layouts =>
      let aligned := cursor.align
      (aligned.slot,
        { slot := aligned.slot + StorageLayouts.slotSpan layouts
          offset := 0 })
  | StorageLayout.fixedArray size
      (StorageLayout.packedScalar _ widthBytes _ _) =>
      let aligned := cursor.align
      let span := natCeilDiv (size * widthBytes) wordBytes
      (aligned.slot, { slot := aligned.slot + span, offset := 0 })
  | StorageLayout.fixedArray size elementLayout =>
      let aligned := cursor.align
      let span := size * StorageLayout.slotSpan elementLayout
      (aligned.slot, { slot := aligned.slot + span, offset := 0 })

def StorageLayouts.cursorAfter (cursor : StorageLayoutCursor) :
    List StorageLayout -> StorageLayoutCursor
  | [] => cursor
  | layout :: rest =>
      StorageLayouts.cursorAfter
        (StorageLayout.cursorStep cursor layout).snd rest

end

mutual

def StorageLayout.depth : StorageLayout -> Nat
  | StorageLayout.scalar _
  | StorageLayout.packedScalar _ _ _ _
  | StorageLayout.bytes
  | StorageLayout.string => 1
  | StorageLayout.struct layouts => StorageLayouts.depth layouts + 1
  | StorageLayout.fixedArray _ elementLayout
  | StorageLayout.dynamicArray elementLayout
  | StorageLayout.mapping _ elementLayout => elementLayout.depth + 1

def StorageLayouts.depth : List StorageLayout -> Nat
  | [] => 0
  | layout :: rest => max layout.depth (StorageLayouts.depth rest)

end

def StorageLayouts.fieldOffsetAndLayoutFrom? :
    Nat -> StorageLayoutCursor -> List StorageLayout ->
      Option (Nat × StorageLayout)
  | _, _, [] => none
  | target, cursor, layout :: rest =>
      let (offset, nextCursor) := StorageLayout.cursorStep cursor layout
      if target == 0 then
        some (offset, layout)
      else
        StorageLayouts.fieldOffsetAndLayoutFrom? (target - 1)
          nextCursor rest

def StorageLayouts.fieldOffsetAndLayout? :
    Nat -> Nat -> List StorageLayout -> Option (Nat × StorageLayout)
  | target, offset, layouts =>
      StorageLayouts.fieldOffsetAndLayoutFrom? target
        { slot := offset, offset := 0 } layouts

def StorageLayout.arrayElementOffsetAndLayout?
    (index : Nat) (elementLayout : StorageLayout) :
    Option (Nat × StorageLayout) :=
  match elementLayout with
  | StorageLayout.packedScalar _ widthBytes signed ty =>
      if widthBytes == 0 then
        none
      else
        let byteOffset := index * widthBytes
        some
          ( byteOffset / wordBytes
          , StorageLayout.packedScalar
              (byteOffset % wordBytes) widthBytes signed ty )
  | _ =>
      some (index * StorageLayout.slotSpan elementLayout, elementLayout)


structure StorageField where
  name : String
  slot : Word
  ty? : Option Ty := none
  layout? : Option StorageLayout := none
  transient : Bool := false
  packedOffset : Nat := 0
  packedBytes : Nat := wordBytes
  packedSigned : Bool := false
  deriving Repr

structure ImmutableField where
  name : String
  ty : Ty
  deriving Repr

structure EventField where
  ty : Ty
  indexed : Bool := false
  deriving Repr

structure EventDecl where
  name : String
  indexedCount : Nat
  topic? : Option Word := none
  fields : List EventField := []
  deriving Repr

structure ErrorDecl where
  name : String
  selector : Word
  fields : List Ty
  deriving Repr

abbrev BlockEnv :=
  SolidCore.Solidity.Shared.Block.BlockEnv

def BlockEnv.empty : BlockEnv :=
  SolidCore.Solidity.Shared.Block.BlockEnv.empty

abbrev TxEnv :=
  SolidCore.Solidity.Shared.Block.TxEnv

def TxEnv.empty : TxEnv :=
  SolidCore.Solidity.Shared.Block.TxEnv.empty

abbrev EvmVersion :=
  SolidCore.Solidity.Shared.Block.EvmVersion

namespace EvmVersion

abbrev homestead : EvmVersion :=
  SolidCore.Solidity.Shared.Block.EvmVersion.homestead

abbrev tangerineWhistle : EvmVersion :=
  SolidCore.Solidity.Shared.Block.EvmVersion.tangerineWhistle

abbrev spuriousDragon : EvmVersion :=
  SolidCore.Solidity.Shared.Block.EvmVersion.spuriousDragon

abbrev byzantium : EvmVersion :=
  SolidCore.Solidity.Shared.Block.EvmVersion.byzantium

abbrev constantinople : EvmVersion :=
  SolidCore.Solidity.Shared.Block.EvmVersion.constantinople

abbrev petersburg : EvmVersion :=
  SolidCore.Solidity.Shared.Block.EvmVersion.petersburg

abbrev istanbul : EvmVersion :=
  SolidCore.Solidity.Shared.Block.EvmVersion.istanbul

abbrev berlin : EvmVersion :=
  SolidCore.Solidity.Shared.Block.EvmVersion.berlin

abbrev london : EvmVersion :=
  SolidCore.Solidity.Shared.Block.EvmVersion.london

abbrev paris : EvmVersion :=
  SolidCore.Solidity.Shared.Block.EvmVersion.paris

abbrev shanghai : EvmVersion :=
  SolidCore.Solidity.Shared.Block.EvmVersion.shanghai

abbrev cancun : EvmVersion :=
  SolidCore.Solidity.Shared.Block.EvmVersion.cancun

abbrev prague : EvmVersion :=
  SolidCore.Solidity.Shared.Block.EvmVersion.prague

abbrev osaka : EvmVersion :=
  SolidCore.Solidity.Shared.Block.EvmVersion.osaka

def default : EvmVersion :=
  SolidCore.Solidity.Shared.Block.EvmVersion.default

end EvmVersion

abbrev LowLevelCallKind :=
  SolidCore.Solidity.Shared.Call.ExternalCallKind

namespace LowLevelCallKind

abbrev call : LowLevelCallKind :=
  SolidCore.Solidity.Shared.Call.ExternalCallKind.call

abbrev staticcall : LowLevelCallKind :=
  SolidCore.Solidity.Shared.Call.ExternalCallKind.staticcall

abbrev delegatecall : LowLevelCallKind :=
  SolidCore.Solidity.Shared.Call.ExternalCallKind.delegatecall

end LowLevelCallKind

abbrev LowLevelCallResult :=
  SolidCore.Solidity.Shared.Call.Result LowLevelCallKind

abbrev ContractCreationResult :=
  SolidCore.Solidity.Shared.Call.CreationResult

inductive ExternalHashKind where
  | sha256
  | ripemd160
  deriving Repr, BEq

namespace ExternalHashKind

def precompileKind : ExternalHashKind -> SolidCore.Solidity.Shared.Precompile.Kind
  | ExternalHashKind.sha256 => SolidCore.Solidity.Shared.Precompile.Kind.sha256
  | ExternalHashKind.ripemd160 => SolidCore.Solidity.Shared.Precompile.Kind.ripemd160

end ExternalHashKind

def LowLevelCallResult.matches (result : LowLevelCallResult)
    (kind : LowLevelCallKind) (target : Word) (calldata : List Byte)
    (value : Word) (gas? : Option Word := none) : Bool :=
  SolidCore.Solidity.Shared.Call.Result.matchesRequest result kind target calldata value
    gas?

def ContractCreationResult.matches (result : ContractCreationResult)
    (contractName : String) (constructorArgs : List Byte)
    (value : Word) (salt? : Option Word) : Bool :=
  SolidCore.Solidity.Shared.Call.CreationResult.matchesRequest result contractName
    constructorArgs value salt?

def ContractCreationResult.failedRequest
    (contractName : String) (constructorArgs : List Byte)
    (value : Word) (salt? : Option Word) : ContractCreationResult :=
  { contractName := contractName
    constructorArgs := SolidCore.Solidity.Shared.Account.normalizeBytes constructorArgs
    value := SolidCore.Solidity.Shared.norm value
    salt? := salt?.map SolidCore.Solidity.Shared.norm
    success := false
    address := 0
    output := [] }

inductive ChildEvalOrder where
  | leftToRight
  | rightToLeft
  deriving Repr, BEq

structure Context where
  storageFields : List StorageField
  immutableFields : List ImmutableField := []
  eventDecls : List EventDecl
  checked : Bool
  construction : Bool := false
  calldata : List Byte
  sender : Word
  value : Word
  self : Word
  accountBalances : WordMap
  accountCodes : ByteMap
  accountCodehashes : WordMap
  contractAddresses : SolidCore.Solidity.Shared.Call.NamedWordMap := []
  contractCreationCodes : SolidCore.Solidity.Shared.Call.NamedBytesMap := []
  contractRuntimeCodes : SolidCore.Solidity.Shared.Call.NamedBytesMap := []
  blockEnv : BlockEnv
  txEnv : TxEnv
  evmVersion : EvmVersion := EvmVersion.default
  createdInTransactionAccounts : List Word := []
  gasleft : Word
  memoryAllocationLimit? : Option Nat := none
  childEvalOrder? : Option ChildEvalOrder := none
  deriving Repr

def Context.empty : Context :=
  { storageFields := []
    immutableFields := []
    eventDecls := []
    checked := true
    construction := false
    calldata := []
    sender := 0
    value := 0
    self := 0
    accountBalances := []
    accountCodes := []
    accountCodehashes := []
    contractAddresses := []
    contractCreationCodes := []
    contractRuntimeCodes := []
    blockEnv := BlockEnv.empty
    txEnv := TxEnv.empty
    evmVersion := EvmVersion.default
    createdInTransactionAccounts := []
    gasleft := 0
    memoryAllocationLimit? := none
    childEvalOrder? := none }

def Context.checkMemoryAllocation (context : Context) (length : Word) :
    Except RevertData Nat :=
  let size := SolidCore.Solidity.Shared.norm length
  match context.memoryAllocationLimit? with
  | some limit =>
      if size <= limit then
        Except.ok size
      else
        Except.error RevertData.memoryAllocationTooLarge
  | none => Except.ok size

def Context.storageField? (context : Context) (name : String) :
    Option StorageField :=
  context.storageFields.find? (fun field => field.name == name)

def Context.storageSlot? (context : Context) (name : String) :
    Option Word :=
  match context.storageField? name with
  | some field => some field.slot
  | none => none

def Context.immutableField? (context : Context) (name : String) :
    Option ImmutableField :=
  context.immutableFields.find? (fun field => field.name == name)

def keccakWord (bytes : List Byte) : Word :=
  bytesToWordBE (Keccak.keccak256Bytes bytes)

def storageWordBytes (value : Word) : List Byte :=
  wordToBytesBE wordBytes value

def erc7201AlignmentMask : Word :=
  wordModulus - 256

def erc7201Slot (id : List Byte) : Word :=
  let inner := keccakWord id
  let preimage := SolidCore.Solidity.Shared.subWord inner 1
  SolidCore.Solidity.Shared.andWord
    (keccakWord (storageWordBytes preimage))
    erc7201AlignmentMask

def mappingStorageSlot (slot key : Word) : Word :=
  keccakWord (storageWordBytes key ++ storageWordBytes slot)

def coerceMappingKeyWordAs (ty : Ty) (value : Value) :
    Except RevertData Word := do
  let coerced ←
    match ty.coerceValue? value with
    | some coerced => Except.ok coerced
    | none => Except.error RevertData.typeMismatch
  match coerced.asStorageWord? with
  | some word => Except.ok word
  | none => Except.error RevertData.typeMismatch

def mappingStorageSlotForKey (slot : Word) (keyTy : Ty)
    (key : Value) : Except RevertData Word :=
  match keyTy with
  | Ty.bytesCalldata =>
      match key.asBytes? with
      | some bytes =>
          Except.ok (keccakWord (bytes ++ storageWordBytes slot))
      | none => Except.error RevertData.typeMismatch
  | _ => do
      let word ← coerceMappingKeyWordAs keyTy key
      Except.ok (mappingStorageSlot slot word)

def dynamicArrayDataSlot (slot : Word) : Word :=
  keccakWord (storageWordBytes slot)

def dynamicArrayStorageSlot (slot index : Word) : Word :=
  normWord (SolidCore.Solidity.Shared.norm (dynamicArrayDataSlot slot) +
    SolidCore.Solidity.Shared.norm index)

def fixedArrayStorageSlot (slot index : Word) : Word :=
  normWord (SolidCore.Solidity.Shared.norm slot + SolidCore.Solidity.Shared.norm index)

def dynamicArrayLayoutStorageSlot
    (slot index : Word) (elementLayout : StorageLayout) : Word :=
  normWord (SolidCore.Solidity.Shared.norm (dynamicArrayDataSlot slot) +
    SolidCore.Solidity.Shared.norm index * StorageLayout.slotSpan elementLayout)

def fixedArrayLayoutStorageSlot
    (slot index : Word) (elementLayout : StorageLayout) : Word :=
  normWord (SolidCore.Solidity.Shared.norm slot +
    SolidCore.Solidity.Shared.norm index * StorageLayout.slotSpan elementLayout)

def dynamicArrayLayoutStorageSlotAndLayout?
    (slot index : Word) (elementLayout : StorageLayout) :
    Option (Word × StorageLayout) := do
  let (offset, layout) ←
    StorageLayout.arrayElementOffsetAndLayout?
      (SolidCore.Solidity.Shared.norm index) elementLayout
  some
    ( normWord
        (SolidCore.Solidity.Shared.norm (dynamicArrayDataSlot slot) + offset)
    , layout )

def fixedArrayLayoutStorageSlotAndLayout?
    (slot index : Word) (elementLayout : StorageLayout) :
    Option (Word × StorageLayout) := do
  let (offset, layout) ←
    StorageLayout.arrayElementOffsetAndLayout?
      (SolidCore.Solidity.Shared.norm index) elementLayout
  some (normWord (SolidCore.Solidity.Shared.norm slot + offset), layout)

def structFieldStorageSlot? (slot : Word)
    (layouts : List StorageLayout) (index : Nat) :
    Option (Word × StorageLayout) := do
  let (offset, layout) ←
    StorageLayouts.fieldOffsetAndLayout? index 0 layouts
  some (normWord (SolidCore.Solidity.Shared.norm slot + offset), layout)

def legacyIndexedStorageSlot (slot key : Word) : Word :=
  normWord
    (SolidCore.Solidity.Shared.norm slot * 16777619 +
      SolidCore.Solidity.Shared.norm key + 1)

def indexedStorageSlot (slot key : Word) : Word :=
  mappingStorageSlot slot key

def Context.eventDecl? (context : Context) (name : String) :
    Option EventDecl :=
  context.eventDecls.find? (fun event => event.name == name)

def LowLevelCallResult.failedRequest
    (kind : LowLevelCallKind) (target : Word) (calldata : List Byte)
    (value : Word) (gas? : Option Word) : LowLevelCallResult :=
  { kind := kind
    target := SolidCore.Solidity.Shared.Account.addressWord target
    calldata := SolidCore.Solidity.Shared.Account.normalizeBytes calldata
    value := SolidCore.Solidity.Shared.norm value
    gas? := gas?.map SolidCore.Solidity.Shared.norm
    success := false
    output := [] }

def Context.accountHasCode (context : Context) (target : Word) : Bool :=
  !(SolidCore.Solidity.Shared.Account.codeAt context.accountCodes target).isEmpty


inductive EnvWord where
  | blockBasefee : EnvWord
  | blockBlobbasefee : EnvWord
  | blockChainid : EnvWord
  | blockCoinbase : EnvWord
  | blockDifficulty : EnvWord
  | blockGaslimit : EnvWord
  | blockNumber : EnvWord
  | blockPrevrandao : EnvWord
  | blockTimestamp : EnvWord
  | txGasprice : EnvWord
  | txOrigin : EnvWord
  | gasleft : EnvWord
  deriving Repr

def EnvWord.eval (which : EnvWord) (context : Context) : Word :=
  match which with
  | EnvWord.blockBasefee =>
      if context.evmVersion.londonOrLater then
        SolidCore.Solidity.Shared.Block.BlockEnv.evalWord context.blockEnv
          SolidCore.Solidity.Shared.Block.BlockEnv.WordField.basefee
      else
        0
  | EnvWord.blockBlobbasefee =>
      if context.evmVersion.cancunOrLater then
        SolidCore.Solidity.Shared.Block.BlockEnv.evalWord context.blockEnv
          SolidCore.Solidity.Shared.Block.BlockEnv.WordField.blobbasefee
      else
        0
  | EnvWord.blockChainid =>
      if context.evmVersion.istanbulOrLater then
        SolidCore.Solidity.Shared.Block.BlockEnv.evalWord context.blockEnv
          SolidCore.Solidity.Shared.Block.BlockEnv.WordField.chainid
      else
        0
  | EnvWord.blockCoinbase =>
      SolidCore.Solidity.Shared.Block.BlockEnv.evalWord context.blockEnv
        SolidCore.Solidity.Shared.Block.BlockEnv.WordField.coinbase
  | EnvWord.blockDifficulty =>
      if context.evmVersion.parisOrLater then
        SolidCore.Solidity.Shared.Block.BlockEnv.evalWord context.blockEnv
          SolidCore.Solidity.Shared.Block.BlockEnv.WordField.prevrandao
      else
        SolidCore.Solidity.Shared.Block.BlockEnv.evalWord context.blockEnv
          SolidCore.Solidity.Shared.Block.BlockEnv.WordField.difficulty
  | EnvWord.blockGaslimit =>
      SolidCore.Solidity.Shared.Block.BlockEnv.evalWord context.blockEnv
        SolidCore.Solidity.Shared.Block.BlockEnv.WordField.gaslimit
  | EnvWord.blockNumber =>
      SolidCore.Solidity.Shared.Block.BlockEnv.evalWord context.blockEnv
        SolidCore.Solidity.Shared.Block.BlockEnv.WordField.number
  | EnvWord.blockPrevrandao =>
      if context.evmVersion.parisOrLater then
        SolidCore.Solidity.Shared.Block.BlockEnv.evalWord context.blockEnv
          SolidCore.Solidity.Shared.Block.BlockEnv.WordField.prevrandao
      else
        SolidCore.Solidity.Shared.Block.BlockEnv.evalWord context.blockEnv
          SolidCore.Solidity.Shared.Block.BlockEnv.WordField.difficulty
  | EnvWord.blockTimestamp =>
      SolidCore.Solidity.Shared.Block.BlockEnv.evalWord context.blockEnv
        SolidCore.Solidity.Shared.Block.BlockEnv.WordField.timestamp
  | EnvWord.txGasprice =>
      SolidCore.Solidity.Shared.Block.TxEnv.evalWord context.txEnv
        SolidCore.Solidity.Shared.Block.TxEnv.WordField.gasprice
  | EnvWord.txOrigin =>
      SolidCore.Solidity.Shared.Block.TxEnv.evalWord context.txEnv
        SolidCore.Solidity.Shared.Block.TxEnv.WordField.origin
  | EnvWord.gasleft => context.gasleft

inductive EnvLookup where
  | blockhash : EnvLookup
  | blobhash : EnvLookup
  | accountBalance : EnvLookup
  | accountCodehash : EnvLookup
  deriving Repr

def EnvLookup.eval (which : EnvLookup) (context : Context) (key : Word) :
    Word :=
  match which with
  | EnvLookup.blockhash =>
      SolidCore.Solidity.Shared.Block.BlockEnv.blockhash context.blockEnv key
  | EnvLookup.blobhash =>
      if context.evmVersion.cancunOrLater then
        SolidCore.Solidity.Shared.Block.TxEnv.blobhash context.txEnv key
      else
        0
  | EnvLookup.accountBalance =>
      SolidCore.Solidity.Shared.Account.balanceAt context.accountBalances key
  | EnvLookup.accountCodehash =>
      if context.evmVersion.constantinopleOrLater then
        SolidCore.Solidity.Shared.Account.codehashAt context.accountCodehashes key
      else
        0

inductive EnvBytesLookup where
  | accountCode : EnvBytesLookup
  deriving Repr

def EnvBytesLookup.eval
    (which : EnvBytesLookup) (context : Context) (key : Word) :
    List Byte :=
  match which with
  | EnvBytesLookup.accountCode =>
      SolidCore.Solidity.Shared.Account.codeAt context.accountCodes key

/-!
## Phase 5 — external world as the shared interaction monad (foundation)

The interpreter's external boundary (low-level calls, contract creations) emits
into `EvmCompiler.Simulation.Interaction` over the shared `Query` alphabet.
`SolidityFailure` is the Solidity-owned failure payload; the only request nodes
are external calls/creates. This block is the foundation: the failure type, the
monad alias, total bridges to the shared alphabet, request/response mapping, the
emit helper, a replay-from-Context runner, and a runnable demo interaction tree.
Threading `SolI` through the `Expr`/`Stmt` evaluator (return-type change) is the
remaining sub-step-1 work; the live choke points are `Context.resolveLowLevelCall`
and `Context.resolveContractCreation`.
-/

/-- Distinguished interpreter failures: reverts and fuel exhaustion (the latter
    mirrors Yul's `.OutOfFuel` truncation arm). -/
inductive SolidityFailure where
  | revert : RevertData → SolidityFailure
  | outOfFuel : SolidityFailure
  deriving Repr

/-- The interaction monad the interpreter emits into: an interaction tree over
    the shared `Query` alphabet with Solidity-owned failures. -/
abbrev SolI := EvmCompiler.Simulation.Interaction SolidityFailure

/-- Lift a pure `Except RevertData` helper into the interaction monad. -/
def SolI.ofExcept {α : Type} : Except RevertData α → SolI α
  | .ok a => .done (.ok a)
  | .error e => .done (.error (.revert e))

/-- Auto-lift pure `Except RevertData` helpers inside `SolI` do-blocks. -/
instance : MonadLift (Except RevertData) SolI := ⟨SolI.ofExcept⟩

-- Total bridges to the shared alphabet.
def wordToU256 (w : Word) : EvmYul.UInt256 := EvmYul.UInt256.ofNat w
def u256ToWord (u : EvmYul.UInt256) : Word := u.toNat
def bytesToByteArray (bs : List Byte) : ByteArray :=
  ⟨Array.mk (bs.map (fun n => UInt8.ofNat n))⟩
def byteArrayToBytes (ba : ByteArray) : List Byte :=
  ba.toList.map UInt8.toNat
def wordToAddress (w : Word) : EvmYul.AccountAddress :=
  EvmYul.AccountAddress.ofUInt256 (wordToU256 w)
def addressToWord (a : EvmYul.AccountAddress) : Word := a.val

def lowLevelKindToCallKind :
    LowLevelCallKind → EvmCompiler.Simulation.CallKind
  | SolidCore.Solidity.Shared.Call.ExternalCallKind.call => .call
  | SolidCore.Solidity.Shared.Call.ExternalCallKind.callcode => .callcode
  | SolidCore.Solidity.Shared.Call.ExternalCallKind.staticcall => .staticcall
  | SolidCore.Solidity.Shared.Call.ExternalCallKind.delegatecall => .delegatecall

def callKindToLowLevel :
    EvmCompiler.Simulation.CallKind → LowLevelCallKind
  | .call => SolidCore.Solidity.Shared.Call.ExternalCallKind.call
  | .callcode => SolidCore.Solidity.Shared.Call.ExternalCallKind.callcode
  | .delegatecall => SolidCore.Solidity.Shared.Call.ExternalCallKind.delegatecall
  | .staticcall => SolidCore.Solidity.Shared.Call.ExternalCallKind.staticcall

/-- Build a shared `CallRequest` from the interpreter's low-level-call params.
    `requestedGas` is the explicit `{gas: …}` option else the ambient `gasleft`
    (exact gas alignment is the deferred `gasleft` work). -/
def buildCallRequest (context : Context) (kind : LowLevelCallKind)
    (target : Word) (calldata : List Byte) (value : Word) (gas? : Option Word) :
    EvmCompiler.Simulation.CallRequest :=
  -- Kind-dependent request fields (stage 2), matching EVM CALL/DELEGATECALL/
  -- STATICCALL frame construction. `codeAddress := target` always, so the
  -- oracle answerer recovers the real callee from `codeAddress` for every kind.
  --   * delegatecall: executes callee code in the caller's frame — `recipient`
  --     is the caller (`self`), no value is transferred (`transferValue := 0`),
  --     and `apparentValue` is the inherited ambient `context.value`.
  --   * staticcall: value transfer is forbidden (`transferValue := 0`).
  --   * call/callcode: recipient is the target, value transfers.
  match kind with
  | SolidCore.Solidity.Shared.Call.ExternalCallKind.delegatecall =>
      { kind := lowLevelKindToCallKind kind
        requestedGas := wordToU256 (gas?.getD context.gasleft)
        caller := wordToAddress context.self
        recipient := wordToAddress context.self
        codeAddress := wordToAddress target
        transferValue := wordToU256 0
        apparentValue := wordToU256 context.value
        calldata := bytesToByteArray calldata
        permission := true }
  | SolidCore.Solidity.Shared.Call.ExternalCallKind.staticcall =>
      { kind := lowLevelKindToCallKind kind
        requestedGas := wordToU256 (gas?.getD context.gasleft)
        caller := wordToAddress context.self
        recipient := wordToAddress target
        codeAddress := wordToAddress target
        transferValue := wordToU256 0
        apparentValue := wordToU256 value
        calldata := bytesToByteArray calldata
        permission := true }
  | _ =>
      { kind := lowLevelKindToCallKind kind
        requestedGas := wordToU256 (gas?.getD context.gasleft)
        caller := wordToAddress context.self
        recipient := wordToAddress target
        codeAddress := wordToAddress target
        transferValue := wordToU256 value
        apparentValue := wordToU256 value
        calldata := bytesToByteArray calldata
        permission := true }

/-- Decode a shared `CallResponse` (answer) into the interpreter's
    `LowLevelCallResult`; the request params are carried through so the result
    keys the fixture oracle exactly. `postWorld` is ignored at checkpoint 1. -/
def decodeCallResponse (response : EvmCompiler.Simulation.CallResponse)
    (kind : LowLevelCallKind) (target : Word) (calldata : List Byte)
    (value : Word) (gas? : Option Word) : LowLevelCallResult :=
  { kind := kind, target := target, calldata := calldata, value := value,
    gas? := gas?, success := response.success,
    output := byteArrayToBytes response.returnData }

/-- Emit an external low-level call as a `Query.external` node and resume on the
    `CallResponse`. Checkpoint-1: world snapshot is a placeholder `default`. -/
def emitLowLevelCall (context : Context) (kind : LowLevelCallKind)
    (target : Word) (calldata : List Byte) (value : Word) (gas? : Option Word) :
    SolI LowLevelCallResult :=
  let request := buildCallRequest context kind target calldata value gas?
  .request
    (EvmCompiler.Simulation.Query.external default
      (EvmCompiler.Simulation.ExternalRequest.call request))
    (fun response =>
      .done (.ok (decodeCallResponse response kind target calldata value gas?)))

/-- Emit a precompile builtin (ecrecover/sha256/ripemd160) as a `STATICCALL` to
    address 1/2/3 and decode its 32-byte output word. In the EVM these builtins
    ARE ordinary external calls (a staticcall to the precompile address), so they
    emit `Query.external` like any call; the deterministic result is computed in
    the responder (`answerCall` → `lookupLowLevelCall?`, which reads the same
    oracle rows `Precompile.lookup?` keyed). Mirrors `Precompile.outputWord?`: a
    failed call or short output yields `none`. `keccak256` is the KECCAK256
    opcode, computed in-EVM, so it stays local — no query. -/
def emitPrecompileWord (context : Context)
    (kind : SolidCore.Solidity.Shared.Precompile.Kind) (input : List Byte) :
    SolI (Option Word) := do
  let result ← emitLowLevelCall context LowLevelCallKind.staticcall
    (SolidCore.Solidity.Shared.Precompile.address kind) input 0 none
  pure (SolidCore.Solidity.Shared.Precompile.outputWord? result)

/-- Source-canonical initCode for a create: 32-byte big-endian UTF-8-name
    length ‖ name bytes ‖ constructor args. The source semantics creates by
    contract *name* (pre-compilation; fixtures key the oracle by name and do
    not populate `contractCreationCodes`), so this canonical name encoding —
    not compiled creation bytecode — is the initCode identity. Injective by
    construction. The residual "initCode is not compiled bytecode" transcript
    mismatch is a recorded, gas-like deferred limitation (see ROADMAP.md /
    docs/DECISIONS.md). -/
def creationInitCode (name : String) (args : List Byte) : ByteArray :=
  let nameBytes := name.toUTF8.toList.map UInt8.toNat
  bytesToByteArray (wordToBytesBE 32 nameBytes.length ++ nameBytes ++ args)

/-- Parse `creationInitCode` fail-closed: a length prefix that overruns the
    remaining bytes, or a non-UTF-8 name, yields `none`. Inverse of
    `creationInitCode`. -/
def decodeCreationInitCode? (initCode : ByteArray) :
    Option (String × List Byte) :=
  let bytes := byteArrayToBytes initCode
  match readBytes? bytes 0 32 with
  | none => none
  | some lenBytes =>
      let len := bytesToWordBE lenBytes
      match readBytes? bytes 32 len with
      | none => none
      | some nameBytes =>
          match String.fromUTF8? (bytesToByteArray nameBytes) with
          | none => none
          | some name => some (name, bytes.drop (32 + len))

/-- Build a shared `CreateRequest` from the interpreter's creation params.
    `kind` is `.create2` iff a salt is present; identity is carried entirely in
    the name-encoded `initCode`. -/
def buildCreateRequest (context : Context) (name : String) (args : List Byte)
    (value : Word) (salt? : Option Word) :
    EvmCompiler.Simulation.CreateRequest :=
  { kind := if salt?.isSome then EvmCompiler.Simulation.CreateKind.create2
            else EvmCompiler.Simulation.CreateKind.create
    creator := wordToAddress context.self
    value := wordToU256 value
    initCode := creationInitCode name args
    salt := salt?.map wordToU256
    permission := true }

/-- Decode a shared `CreateResponse` into the interpreter's
    `ContractCreationResult`. `CreateResponse` has no `success` field, so
    success is the EVM convention `address ≠ 0`; the request params (name,
    args, value, salt) are carried through to key the fixture oracle and
    `recordExternalInteraction`, mirroring `decodeCallResponse`. -/
def decodeCreateResponse (response : EvmCompiler.Simulation.CreateResponse)
    (name : String) (args : List Byte) (value : Word) (salt? : Option Word) :
    ContractCreationResult :=
  let address := u256ToWord response.address
  { contractName := name
    constructorArgs := args
    value := value
    salt? := salt?
    success := address != 0
    address := address
    output := byteArrayToBytes response.returnData }

/-- Emit a contract creation as a `Query.external` node and resume on the
    `CreateResponse`. Checkpoint-1: world snapshot is a placeholder `default`. -/
def emitContractCreation (context : Context) (name : String) (args : List Byte)
    (value : Word) (salt? : Option Word) : SolI ContractCreationResult :=
  let request := buildCreateRequest context name args value salt?
  .request
    (EvmCompiler.Simulation.Query.external default
      (EvmCompiler.Simulation.ExternalRequest.create request))
    (fun response =>
      .done (.ok (decodeCreateResponse response name args value salt?)))

/-- Fuel-bounded fold answering every query with the canonical
    `Query.defaultAnswer` (stage 3: the fixture oracle left `Context`; external
    answers come from scripted responders — `SolI.runWith`/`runFailOpen`).
    `defaultAnswer`'s call/create shapes decode to exactly the old fail-open
    `failedRequest` (success = false / address = 0, empty output), so this is
    bit-identical to the retired replay-from-Context fold on the row-less
    contexts that remain. Kept fuel-bounded for the transcript utilities and
    `foldExpr` (constant-expression evaluation). -/
def SolI.runFromContext {α : Type} (fuel : Nat) (context : Context) :
    SolI α → Except SolidityFailure α
  | .done r => r
  | .request query k =>
      match fuel with
      | 0 => .error .outOfFuel
      | Nat.succ fuel' =>
          SolI.runFromContext fuel' context
            (k (EvmCompiler.Simulation.Query.defaultAnswer query))

/-- The stage-3 context answerer: every query gets `Query.defaultAnswer` (the
    context no longer carries oracle rows; see `SolI.runFromContext`). -/
def contextAnswer (_context : Context) :
    (q : EvmCompiler.Simulation.Query) → EvmCompiler.Simulation.Answer q :=
  EvmCompiler.Simulation.Query.defaultAnswer

/-- Fold a `SolI` interaction tree to its final `Except SolidityFailure` result
    by answering every query from `Context` (`contextAnswer`). Unlike
    `SolI.runFromContext` this needs **no fuel**: `Interaction` is a plain
    inductive whose `request` continuation `k answer` is a structural subterm, so
    the recursion is structural and total.

    Termination note (R9): this depends on `Interaction` being an *inductive*; a
    representation change upstream (coinductive/quotiented) would break the
    structural recursion, and no honest Stmt-level fuel bound exists (loops emit
    one query per iteration), so such a change must revisit this fold. -/
def SolI.run {α : Type} (context : Context) :
    SolI α → Except SolidityFailure α
  | .done r => r
  | .request q k => SolI.run context (k (contextAnswer context q))

/-! ## Stage 2 — scripted responders (open-world, fail-closed).

A `ScriptedResponder` is an ordered list of oracle rows (calls/creates) that
answers external-call/create queries **fail-closed**: an external request with
no matching row aborts the fold with `ResponderFailure.unmatched` (carrying the
request for an expected-vs-actual diff) instead of the old fail-open
`failedRequest`. Matching mirrors `answerCall`/`answerCreate` keying exactly
(exact-gas-first then no-gas; target recovered from `codeAddress`), so on any
tree whose every external request has a matching row the responder answers
identically to `contextAnswer` — the stage-2 equivalence gate. The `OpenWorld`
snapshot in the query is ignored (checkpoint-1); `postWorld := default`. -/

inductive OracleRow where
  | call : LowLevelCallResult → OracleRow
  | create : ContractCreationResult → OracleRow
  deriving Repr

abbrev ScriptedResponder := List OracleRow

def ScriptedResponder.callRows (responder : ScriptedResponder) :
    List LowLevelCallResult :=
  responder.filterMap (fun row =>
    match row with | OracleRow.call c => some c | _ => none)

def ScriptedResponder.createRows (responder : ScriptedResponder) :
    List ContractCreationResult :=
  responder.filterMap (fun row =>
    match row with | OracleRow.create c => some c | _ => none)

/-- Answer a call request from the responder's call rows; `none` on a total
    miss. Keying + gas fallback mirror `answerCall` exactly. -/
def ScriptedResponder.answerCall? (responder : ScriptedResponder)
    (request : EvmCompiler.Simulation.CallRequest) :
    Option EvmCompiler.Simulation.CallResponse :=
  let kind := callKindToLowLevel request.kind
  let target := addressToWord request.codeAddress
  let calldata := byteArrayToBytes request.calldata
  let value := u256ToWord request.transferValue
  let rows := responder.callRows
  let result? :=
    match SolidCore.Solidity.Shared.Call.Result.lookup? rows kind target calldata
        value (some (u256ToWord request.requestedGas)) with
    | some r => some r
    | none =>
        SolidCore.Solidity.Shared.Call.Result.lookup? rows kind target calldata
          value none
  result?.map (fun result =>
    { success := result.success
      returnData := bytesToByteArray result.output
      postWorld := default
      returnedGas := request.requestedGas })

/-- Answer a create request from the responder's create rows; `none` on a total
    miss OR a malformed name-encoded initCode (fail-closed — `answerCreate`
    fail-opened on a malformed name). Keying mirrors `answerCreate`. -/
def ScriptedResponder.answerCreate? (responder : ScriptedResponder)
    (request : EvmCompiler.Simulation.CreateRequest) :
    Option EvmCompiler.Simulation.CreateResponse := do
  let (name, args) ← decodeCreationInitCode? request.initCode
  let value := u256ToWord request.value
  let salt? := request.salt.map u256ToWord
  let result ←
    SolidCore.Solidity.Shared.Call.CreationResult.lookup?
      responder.createRows name args value salt?
  some
    { address := wordToU256 (if result.success then result.address else 0)
      returnData := bytesToByteArray result.output
      postWorld := default
      returnedGas := wordToU256 0 }

/-- Fold failure under a responder: a Solidity failure (revert/outOfFuel — for
    `CallResult` trees only `outOfFuel` is reachable, reverts being caught into
    values), or a fail-closed unmatched external request (carried for the diff). -/
inductive ResponderFailure where
  | solidity : SolidityFailure → ResponderFailure
  | unmatched : EvmCompiler.Simulation.ExternalRequest → ResponderFailure

/-- Fold a `SolI` tree against a scripted responder, fail-closed. Structural
    recursion through the continuation (like `SolI.run`), no fuel. Non-external
    (resource) queries take the canonical default answer (checkpoint-1). -/
def SolI.runWith {α : Type} (responder : ScriptedResponder) :
    SolI α → Except ResponderFailure α
  | .done (.ok a) => .ok a
  | .done (.error e) => .error (ResponderFailure.solidity e)
  | .request
      (EvmCompiler.Simulation.Query.external _
        (EvmCompiler.Simulation.ExternalRequest.call request)) k =>
      match responder.answerCall? request with
      | some response => SolI.runWith responder (k response)
      | none =>
          .error (ResponderFailure.unmatched
            (EvmCompiler.Simulation.ExternalRequest.call request))
  | .request
      (EvmCompiler.Simulation.Query.external _
        (EvmCompiler.Simulation.ExternalRequest.create request)) k =>
      match responder.answerCreate? request with
      | some response => SolI.runWith responder (k response)
      | none =>
          .error (ResponderFailure.unmatched
            (EvmCompiler.Simulation.ExternalRequest.create request))
  | .request query k =>
      SolI.runWith responder (k (EvmCompiler.Simulation.Query.defaultAnswer query))

/-- Assemble a responder from plain oracle-row lists (witness/manifest helper). -/
def responderOfResults (calls : List LowLevelCallResult)
    (creates : List ContractCreationResult) : ScriptedResponder :=
  calls.map OracleRow.call ++ creates.map OracleRow.create

/-- Fail-open answerer over a responder: matched external requests answer from
    the rows (find-first, same keying as `ScriptedResponder.answerCall?`/
    `answerCreate?`); anything unmatched gets the canonical
    `Query.defaultAnswer`, whose call/create shapes decode to exactly the
    retired context oracle's fail-open `failedRequest` (success = false /
    address = 0, empty output). Witness sentinels fold with this to preserve
    their recorded truth values — several deliberately exercise the miss path;
    the corpus replay uses the fail-closed `SolI.runWith`. -/
def ScriptedResponder.answer (responder : ScriptedResponder) :
    (q : EvmCompiler.Simulation.Query) → EvmCompiler.Simulation.Answer q
  | EvmCompiler.Simulation.Query.external world
      (EvmCompiler.Simulation.ExternalRequest.call request) =>
      match responder.answerCall? request with
      | some response => response
      | none =>
          EvmCompiler.Simulation.Query.defaultAnswer
            (EvmCompiler.Simulation.Query.external world
              (EvmCompiler.Simulation.ExternalRequest.call request))
  | EvmCompiler.Simulation.Query.external world
      (EvmCompiler.Simulation.ExternalRequest.create request) =>
      match responder.answerCreate? request with
      | some response => response
      | none =>
          EvmCompiler.Simulation.Query.defaultAnswer
            (EvmCompiler.Simulation.Query.external world
              (EvmCompiler.Simulation.ExternalRequest.create request))
  | q => EvmCompiler.Simulation.Query.defaultAnswer q

/-- Fold a tree under the fail-open responder answerer (structural, no fuel). -/
def SolI.runFailOpen {α : Type} (responder : ScriptedResponder) :
    SolI α → Except SolidityFailure α
  | .done r => r
  | .request q k => SolI.runFailOpen responder (k (responder.answer q))

/-- Reify a (throw-revert) interaction tree's revert leaf into an
    `Except RevertData` *value*, while re-throwing `outOfFuel` (truncation must
    keep propagating). Statement sites consume Expr trees through this helper.

    Correctness rests on the two threading laws of the shared monad
    (`Interaction.lean` `bind`/`tryCatch`): both thread `request` nodes, so an
    in-flight external-call query inside an expression survives the catch and
    propagates upward; only the `done (.error …)` leaf is intercepted.

    Greppable invariant: `caught` is the ONLY `tryCatch` use in this
    interpreter — every Expr-tree bind inside the Stmt block goes through it. -/
def SolI.caught {α : Type} (tree : SolI α) : SolI (Except RevertData α) :=
  tryCatch (Except.ok <$> tree) (fun failure =>
    match failure with
    | SolidityFailure.revert e => pure (Except.error e)
    | SolidityFailure.outOfFuel => throw SolidityFailure.outOfFuel)

/-- The ordered query transcript of a `SolI` tree under a given answerer. -/
def SolI.queryTranscript {α : Type} (fuel : Nat)
    (answer : (q : EvmCompiler.Simulation.Query) → EvmCompiler.Simulation.Answer q) :
    SolI α → List EvmCompiler.Simulation.Query
  | .done _ => []
  | .request query k =>
      match fuel with
      | 0 => []
      | Nat.succ fuel' =>
          query :: SolI.queryTranscript fuel' answer (k (answer query))

def loadStorageWordAs (state : State) (slot : Word) (ty : Ty) :
    Except RevertData Value :=
  match ty.storageValueFromWord? (state.loadSlot slot) with
  | some value => Except.ok value
  | none => Except.error RevertData.typeMismatch

def coerceStorageWordAs (ty : Ty) (value : Value) :
    Except RevertData Word := do
  let coerced ←
    match ty.coerceValue? value with
    | some coerced => Except.ok coerced
    | none => Except.error RevertData.typeMismatch
  match ty, coerced with
  | Ty.externalFunction, Value.externalFunction addr selector =>
      match externalFunctionStorageWord? addr selector with
      | some word => Except.ok word
      | none => Except.error RevertData.typeMismatch
  | _, _ =>
      match coerced.asStorageWord? with
      | some word => Except.ok word
      | none => Except.error RevertData.typeMismatch

def State.storeFixedArraySlots (state : State)
    (slot : Word) (elementTy : Ty) : Nat -> List Value ->
    Except RevertData State
  | _, [] => Except.ok state
  | index, value :: rest => do
      let word ← coerceStorageWordAs elementTy value
      State.storeFixedArraySlots
        (state.storeSlot (fixedArrayStorageSlot slot index) word)
        slot elementTy (index + 1) rest

def State.storeDynamicArraySlots (state : State)
    (slot : Word) (elementTy : Ty) : Nat -> List Value ->
    Except RevertData State
  | _, [] => Except.ok state
  | index, value :: rest => do
      let word ← coerceStorageWordAs elementTy value
      State.storeDynamicArraySlots
        (state.storeSlot (dynamicArrayStorageSlot slot index) word)
        slot elementTy (index + 1) rest

def State.storeBytesSlots (state : State) (slot : Word) :
    Nat -> List Byte -> State
  | _, [] => state
  | index, byte :: rest =>
      State.storeBytesSlots
        (state.storeSlot (dynamicArrayStorageSlot slot index)
          (normByte byte))
        slot (index + 1) rest

def State.loadBytesSlots (state : State) (slot : Word) :
    Nat -> Nat -> List Byte
  | _, 0 => []
  | index, remaining + 1 =>
      normByte (state.loadSlot (dynamicArrayStorageSlot slot index)) ::
        State.loadBytesSlots state slot (index + 1) remaining

def wordBitRange (offset width : Nat) (value : Word) : Word :=
  if width == 0 then
    0
  else
    let shifted := SolidCore.Solidity.Shared.norm value / (2 ^ offset)
    SolidCore.Solidity.Shared.norm (shifted % (2 ^ width))

def wordReplaceBitRange
    (offset width : Nat) (current value : Word) : Word :=
  if width == 0 then
    SolidCore.Solidity.Shared.norm current
  else
    let shift := 2 ^ offset
    let modulus := 2 ^ width
    let currentNorm := SolidCore.Solidity.Shared.norm current
    let currentPart := ((currentNorm / shift) % modulus) * shift
    let valuePart := (SolidCore.Solidity.Shared.norm value % modulus) * shift
    SolidCore.Solidity.Shared.norm (currentNorm - currentPart + valuePart)

structure StorageBytesHeader where
  length : Nat
  long : Bool
  deriving Repr

def storageBytesHeader? (word : Word) :
    Except RevertData StorageBytesHeader :=
  let raw := SolidCore.Solidity.Shared.norm word
  let lowByte := raw % 256
  if lowByte % 2 == 0 then
    let length := lowByte / 2
    if length <= 31 then
      Except.ok { length := length, long := false }
    else
      Except.error RevertData.invalidStorageByteArray
  else
    Except.ok { length := (raw - 1) / 2, long := true }

def storageBytesLongHeader (length : Nat) : Word :=
  normWord (length * 2 + 1)

def storageBytesShortWord (bytes : List Byte) : Word :=
  bytesToWordBE
    (bytesPrefixRightPadded (wordBytes - 1) bytes ++
      [normByte (bytes.length * 2)])

def storageBytesLongDataSlot (slot : Word) (chunk : Nat) : Word :=
  normWord
    (SolidCore.Solidity.Shared.norm (dynamicArrayDataSlot slot) + chunk)

def storageBytesLongChunkCount (length : Nat) : Nat :=
  if length <= 31 then
    0
  else
    (length + wordBytes - 1) / wordBytes

def wordByteBE? (word : Word) (index : Nat) : Option Byte :=
  listGet? (wordToBytesBE wordBytes word) index

def wordReplaceByteBE? (word : Word) (index : Nat) (byte : Byte) :
    Option Word := do
  let bytes ← listUpdateAt? (wordToBytesBE wordBytes word)
    index (normByte byte)
  some (bytesToWordBE bytes)

def State.storeStorageBytesLongSlotsFuel :
    Nat -> State -> Word -> Nat -> List Byte -> State
  | 0, state, _, _, _ => state
  | _ + 1, state, _, _, [] => state
  | fuel + 1, state, slot, chunkIndex, bytes =>
      let chunk := bytesPrefixRightPadded wordBytes bytes
      let rest := bytes.drop wordBytes
      State.storeStorageBytesLongSlotsFuel fuel
        (state.storeSlot
          (storageBytesLongDataSlot slot chunkIndex)
          (bytesToWordBE chunk))
        slot (chunkIndex + 1) rest

def State.storeStorageBytesLongSlots (state : State) (slot : Word)
    (bytes : List Byte) : State :=
  State.storeStorageBytesLongSlotsFuel
    (bytes.length + 1) state slot 0 bytes

def State.clearStorageBytesLongSlotsFuel :
    Nat -> State -> Word -> Nat -> State
  | 0, state, _, _ => state
  | fuel + 1, state, slot, chunkIndex =>
      State.clearStorageBytesLongSlotsFuel fuel
        (state.storeSlot
          (storageBytesLongDataSlot slot chunkIndex)
          0)
        slot (chunkIndex + 1)

def State.clearStorageBytesLongSlots (state : State) (slot : Word)
    (start count : Nat) : State :=
  State.clearStorageBytesLongSlotsFuel count state slot start

def State.loadStorageBytesLongSlots (state : State) (slot : Word) :
    Nat -> Nat -> List Byte
  | _, 0 => []
  | index, remaining + 1 =>
      let word :=
        state.loadSlot
          (storageBytesLongDataSlot slot (index / wordBytes))
      let byte := (wordByteBE? word (index % wordBytes)).getD 0
      normByte byte ::
        State.loadStorageBytesLongSlots state slot
          (index + 1) remaining

def State.loadStorageBytesAt (state : State) (slot : Word) :
    Except RevertData (List Byte) := do
  let header ← storageBytesHeader? (state.loadSlot slot)
  if header.long then
    Except.ok (State.loadStorageBytesLongSlots state slot 0 header.length)
  else
    Except.ok
      ((wordToBytesBE wordBytes (state.loadSlot slot)).take
        header.length |>.map normByte)

def State.storeStorageBytesAt (state : State) (slot : Word)
    (bytes : List Byte) : State :=
  let bytes := bytes.map normByte
  let oldLongChunks :=
    match storageBytesHeader? (state.loadSlot slot) with
    | Except.ok header =>
        if header.long then
          storageBytesLongChunkCount header.length
        else
          0
    | Except.error _ => 0
  let newLongChunks := storageBytesLongChunkCount bytes.length
  let written :=
    if bytes.length <= 31 then
      state.storeSlot slot (storageBytesShortWord bytes)
    else
      (State.storeStorageBytesLongSlots state slot bytes)
        |>.storeSlot slot (storageBytesLongHeader bytes.length)
  State.clearStorageBytesLongSlots written slot
    newLongChunks (oldLongChunks - newLongChunks)

def State.storageBytesLengthAt (state : State) (slot : Word) :
    Except RevertData Nat := do
  let header ← storageBytesHeader? (state.loadSlot slot)
  Except.ok header.length

def State.storageBytesElementSlotAndOffset (state : State) (slot key : Word) :
    Except RevertData (Word × Nat) := do
  let header ← storageBytesHeader? (state.loadSlot slot)
  let index := SolidCore.Solidity.Shared.norm key
  if header.length <= index then
    Except.error RevertData.indexOutOfBounds
  else if header.long then
    Except.ok
      ( storageBytesLongDataSlot slot (index / wordBytes)
      , wordBytes - 1 - (index % wordBytes) )
  else
    Except.ok (slot, wordBytes - 1 - index)

def State.loadStorageByteAt (state : State) (slot key : Word) :
    Except RevertData Word := do
  let (elementSlot, offset) ←
    State.storageBytesElementSlotAndOffset state slot key
  Except.ok (wordBitRange (offset * 8) 8 (state.loadSlot elementSlot))

def State.storeStorageByteAt (state : State) (slot key : Word)
    (byte : Word) : Except RevertData State := do
  let (elementSlot, offset) ←
    State.storageBytesElementSlotAndOffset state slot key
  Except.ok
    (state.storeSlot elementSlot
      (wordReplaceBitRange (offset * 8) 8
        (state.loadSlot elementSlot) byte))

def State.clearStorageByteAt (state : State) (slot key : Word) :
    Except RevertData State :=
  State.storeStorageByteAt state slot key 0

def State.pushStorageByteAt (state : State) (slot : Word) (byte : Word) :
    Except RevertData State := do
  let bytes ← State.loadStorageBytesAt state slot
  let newLength := bytes.length + 1
  if wordModulus <= newLength then
    Except.error RevertData.overflow
  else
    Except.ok
      (State.storeStorageBytesAt state slot
        (bytes ++ [normByte byte]))

def State.popStorageByteAt (state : State) (slot : Word) :
    Except RevertData State := do
  let bytes ← State.loadStorageBytesAt state slot
  if bytes.isEmpty then
    Except.error RevertData.popEmptyArray
  else
    Except.ok
      (State.storeStorageBytesAt state slot
        (bytes.take (bytes.length - 1)))

def packedStorageValueFromWord? (signed : Bool) (bytes : Nat)
    (ty : Ty) (word : Word) : Option Value :=
  match ty with
  | Ty.int256 =>
      if signed && bytes < wordBytes then
        match intCast? (bytes * 8) (Value.word word) with
        | Except.ok (Value.int signedWord) => some (Value.int signedWord)
        | _ => none
      else
        ty.storageValueFromWord? word
  | _ => ty.storageValueFromWord? word

mutual

def State.loadStorageLayoutAtFuel :
    Nat -> State -> Word -> StorageLayout -> Except RevertData Value
  | 0, _, _, _ => Except.error RevertData.typeMismatch
  | fuel + 1, state, slot, layout =>
      match layout with
      | StorageLayout.scalar ty =>
          loadStorageWordAs state slot ty
      | StorageLayout.packedScalar offset bytes signed ty =>
          let word :=
            wordBitRange (offset * 8) (bytes * 8) (state.loadSlot slot)
          match packedStorageValueFromWord? signed bytes ty word with
          | some value => Except.ok value
          | none => Except.error RevertData.typeMismatch
      | StorageLayout.struct layouts => do
          let values ←
            State.loadStructSlotsFuel fuel state slot
              { slot := 0, offset := 0 } layouts
          Except.ok (Value.tuple values)
      | StorageLayout.bytes => do
          let bytes ← State.loadStorageBytesAt state slot
          Except.ok (Value.bytes bytes)
      | StorageLayout.string => do
          let bytes ← State.loadStorageBytesAt state slot
          Except.ok (Value.bytes bytes)
      | StorageLayout.fixedArray size elementLayout => do
          let values ←
            State.loadFixedArrayLayoutSlotsFuel
              fuel state slot elementLayout 0 size
          Except.ok (Value.fixedArray values)
      | StorageLayout.dynamicArray elementLayout => do
          let length := SolidCore.Solidity.Shared.norm (state.loadSlot slot)
          let values ←
            State.loadDynamicArrayLayoutSlotsFuel
              fuel state slot elementLayout 0 length
          Except.ok (Value.dynamicArray values)
      | StorageLayout.mapping _ _ =>
          Except.error RevertData.typeMismatch
termination_by fuel _ _ _ => (fuel, 0, 0)

def State.loadStructSlotsFuel (fuel : Nat) (state : State) (slot : Word) :
    StorageLayoutCursor -> List StorageLayout ->
      Except RevertData (List Value)
  | _, [] => Except.ok []
  | cursor, layout :: rest => do
      let (offset, nextCursor) := StorageLayout.cursorStep cursor layout
      let fieldSlot :=
        normWord (SolidCore.Solidity.Shared.norm slot + offset)
      let value ←
        State.loadStorageLayoutAtFuel fuel state fieldSlot layout
      let tail ←
        State.loadStructSlotsFuel fuel state slot nextCursor rest
      Except.ok (value :: tail)
termination_by _ layouts => (fuel, 1, sizeOf layouts)

def State.loadFixedArrayLayoutSlotsFuel (fuel : Nat)
    (state : State) (slot : Word) (elementLayout : StorageLayout) :
    Nat -> Nat -> Except RevertData (List Value)
  | _, 0 => Except.ok []
  | index, remaining + 1 => do
      let (elementSlot, elementSlotLayout) ←
        match fixedArrayLayoutStorageSlotAndLayout?
          slot index elementLayout with
        | some pair => Except.ok pair
        | none => Except.error RevertData.typeMismatch
      let value ←
        State.loadStorageLayoutAtFuel
          fuel state elementSlot elementSlotLayout
      let rest ←
        State.loadFixedArrayLayoutSlotsFuel
          fuel state slot elementLayout (index + 1) remaining
      Except.ok (value :: rest)
termination_by _ remaining => (fuel, 1, remaining)

def State.loadDynamicArrayLayoutSlotsFuel (fuel : Nat)
    (state : State) (slot : Word) (elementLayout : StorageLayout) :
    Nat -> Nat -> Except RevertData (List Value)
  | _, 0 => Except.ok []
  | index, remaining + 1 => do
      let (elementSlot, elementSlotLayout) ←
        match dynamicArrayLayoutStorageSlotAndLayout?
          slot index elementLayout with
        | some pair => Except.ok pair
        | none => Except.error RevertData.typeMismatch
      let value ←
        State.loadStorageLayoutAtFuel
          fuel state elementSlot elementSlotLayout
      let rest ←
        State.loadDynamicArrayLayoutSlotsFuel
          fuel state slot elementLayout (index + 1) remaining
      Except.ok (value :: rest)
termination_by _ remaining => (fuel, 1, remaining)

end

def State.loadStorageLayoutAt (state : State) (slot : Word)
    (layout : StorageLayout) : Except RevertData Value :=
  State.loadStorageLayoutAtFuel (layout.depth + 1) state slot layout

def State.loadStructSlots (state : State) (slot : Word)
    (cursor : StorageLayoutCursor) (layouts : List StorageLayout) :
    Except RevertData (List Value) :=
  State.loadStructSlotsFuel
    (StorageLayouts.depth layouts + 1)
    state slot cursor layouts

mutual

def State.storeStorageLayoutAt (state : State) (slot : Word)
    (layout : StorageLayout) (value : Value) : Except RevertData State :=
  match layout with
  | StorageLayout.scalar ty => do
      let word ← coerceStorageWordAs ty value
      Except.ok (state.storeSlot slot word)
  | StorageLayout.packedScalar offset bytes _ ty => do
      let word ← coerceStorageWordAs ty value
      let current := state.loadSlot slot
      Except.ok
        (state.storeSlot slot
          (wordReplaceBitRange (offset * 8) (bytes * 8)
            current word))
  | StorageLayout.struct layouts =>
      match value with
      | Value.tuple values =>
          State.storeStructSlots state slot
            { slot := 0, offset := 0 } layouts values
      | _ => Except.error RevertData.typeMismatch
  | StorageLayout.bytes =>
      match value with
      | Value.bytes bytes =>
          Except.ok (State.storeStorageBytesAt state slot bytes)
      | _ => Except.error RevertData.typeMismatch
  | StorageLayout.string =>
      match value with
      | Value.bytes bytes =>
          Except.ok (State.storeStorageBytesAt state slot bytes)
      | _ => Except.error RevertData.typeMismatch
  | StorageLayout.fixedArray size elementLayout =>
      match value with
      | Value.fixedArray values =>
          if values.length == size then
            State.storeFixedArrayLayoutSlots
              state slot elementLayout 0 values
          else
            Except.error RevertData.typeMismatch
      | _ => Except.error RevertData.typeMismatch
  | StorageLayout.dynamicArray elementLayout =>
      match value with
      | Value.dynamicArray values => do
          let state ←
            State.storeDynamicArrayLayoutSlots
              state slot elementLayout 0 values
          Except.ok (state.storeSlot slot values.length)
      | _ => Except.error RevertData.typeMismatch
  | StorageLayout.mapping _ _ =>
      Except.error RevertData.typeMismatch

def State.storeStructSlots (state : State) (slot : Word) :
    StorageLayoutCursor -> List StorageLayout -> List Value ->
    Except RevertData State
  | _, [], [] => Except.ok state
  | cursor, layout :: layouts, value :: values => do
      let (offset, nextCursor) := StorageLayout.cursorStep cursor layout
      let fieldSlot :=
        normWord (SolidCore.Solidity.Shared.norm slot + offset)
      let state ←
        State.storeStorageLayoutAt state fieldSlot layout value
      State.storeStructSlots
        state slot nextCursor layouts values
  | _, _, _ => Except.error RevertData.typeMismatch

def State.storeFixedArrayLayoutSlots (state : State) (slot : Word)
    (elementLayout : StorageLayout) :
    Nat -> List Value -> Except RevertData State
  | _, [] => Except.ok state
  | index, value :: rest => do
      let (elementSlot, elementSlotLayout) ←
        match fixedArrayLayoutStorageSlotAndLayout?
          slot index elementLayout with
        | some pair => Except.ok pair
        | none => Except.error RevertData.typeMismatch
      let state ←
        State.storeStorageLayoutAt state elementSlot elementSlotLayout value
      State.storeFixedArrayLayoutSlots state slot elementLayout
        (index + 1) rest

def State.storeDynamicArrayLayoutSlots (state : State) (slot : Word)
    (elementLayout : StorageLayout) :
    Nat -> List Value -> Except RevertData State
  | _, [] => Except.ok state
  | index, value :: rest => do
      let (elementSlot, elementSlotLayout) ←
        match dynamicArrayLayoutStorageSlotAndLayout?
          slot index elementLayout with
        | some pair => Except.ok pair
        | none => Except.error RevertData.typeMismatch
      let state ←
        State.storeStorageLayoutAt state elementSlot elementSlotLayout value
      State.storeDynamicArrayLayoutSlots state slot elementLayout
        (index + 1) rest

end

def StorageField.scalarTy? (field : StorageField) : Option Ty :=
  match field.layout? with
  | some (StorageLayout.scalar ty) => some ty
  | some _ => none
  | none => field.ty?

def StorageLayout.scalarTy? : StorageLayout -> Option Ty
  | StorageLayout.scalar ty => some ty
  | _ => none

def State.loadFieldSlot (state : State) (field : StorageField) : Word :=
  if field.transient then
    state.loadTransientSlot field.slot
  else
    state.loadSlot field.slot

def State.storeFieldSlot (state : State) (field : StorageField)
    (value : Word) : State :=
  if field.transient then
    state.storeTransientSlot field.slot value
  else
    state.storeSlot field.slot value

def StorageField.packedBitOffset (field : StorageField) : Nat :=
  field.packedOffset * 8

def StorageField.packedBitWidth (field : StorageField) : Nat :=
  field.packedBytes * 8

def StorageField.isPacked (field : StorageField) : Bool :=
  field.packedOffset != 0 || field.packedBytes != wordBytes

def State.loadFieldWord (state : State) (field : StorageField) : Word :=
  if field.isPacked then
    wordBitRange field.packedBitOffset field.packedBitWidth
      (state.loadFieldSlot field)
  else
    state.loadFieldSlot field

def State.storeFieldWord (state : State) (field : StorageField)
    (value : Word) : State :=
  if field.isPacked then
    let current := state.loadFieldSlot field
    let updated :=
      wordReplaceBitRange field.packedBitOffset field.packedBitWidth
        current value
    state.storeFieldSlot field updated
  else
    state.storeFieldSlot field value

def StorageField.storageValueFromWord? (field : StorageField)
    (ty : Ty) (word : Word) : Option Value :=
  match ty with
  | Ty.int256 =>
      if field.packedSigned && field.packedBytes < wordBytes then
        match intCast? field.packedBitWidth (Value.word word) with
        | Except.ok (Value.int signedWord) => some (Value.int signedWord)
        | _ => none
      else
        ty.storageValueFromWord? word
  | _ => ty.storageValueFromWord? word

def Runtime.loadStorageField (context : Context)
    (runtime : Runtime) (name : String) : Except RevertData Value :=
  match context.storageField? name with
  | some field =>
      match field.layout? with
      | some (StorageLayout.dynamicArray _) =>
          Except.ok (Value.word (runtime.state.loadFieldSlot field))
      | some StorageLayout.bytes => do
          let length ← State.storageBytesLengthAt runtime.state field.slot
          Except.ok (Value.word length)
      | some StorageLayout.string =>
          Except.error RevertData.typeMismatch
      | some (StorageLayout.struct tys) => do
          let values ←
            State.loadStructSlots runtime.state field.slot
              { slot := 0, offset := 0 } tys
          Except.ok (Value.tuple values)
      | some (StorageLayout.fixedArray _ _) =>
          Except.error RevertData.typeMismatch
      | some (StorageLayout.mapping _ _) =>
          Except.error RevertData.typeMismatch
      | some layout@(StorageLayout.packedScalar _ _ _ _) =>
          State.loadStorageLayoutAt runtime.state field.slot layout
      | some (StorageLayout.scalar ty) =>
          match
            field.storageValueFromWord? ty
              (runtime.state.loadFieldWord field)
          with
          | some value => Except.ok value
          | none => Except.error RevertData.typeMismatch
      | none =>
          match field.ty? with
          | some ty =>
              match
                field.storageValueFromWord? ty
                  (runtime.state.loadFieldWord field)
              with
              | some value => Except.ok value
              | none => Except.error RevertData.typeMismatch
          | none => Except.ok (Value.word (runtime.state.loadFieldWord field))
  | none => Except.error RevertData.typeMismatch

def Runtime.loadImmutableField (context : Context)
    (runtime : Runtime) (name : String) : Except RevertData Value :=
  match context.immutableField? name with
  | some field =>
      match runtime.state.immutable? name with
      | some value =>
          match field.ty.coerceValue? value with
          | some coerced => Except.ok coerced
          | none => Except.error RevertData.typeMismatch
      | none => Except.ok field.ty.defaultValue
  | none => Except.error RevertData.typeMismatch

def Runtime.storeStorageField (context : Context)
    (runtime : Runtime) (name : String) (value : Value) :
    Except RevertData Runtime := do
  let field ←
    match context.storageField? name with
    | some field => Except.ok field
    | none => Except.error RevertData.typeMismatch
  let value ← runtime.storageMaterializedValue value
  match field.layout? with
  | some layout@(StorageLayout.dynamicArray _) => do
      let state ←
        State.storeStorageLayoutAt runtime.state field.slot layout value
      Except.ok { runtime with state }
  | some StorageLayout.bytes =>
      match value with
      | Value.bytes bytes =>
          Except.ok
            { runtime with
              state :=
                State.storeStorageBytesAt runtime.state field.slot bytes }
      | _ => Except.error RevertData.typeMismatch
  | some StorageLayout.string =>
      match value with
      | Value.bytes bytes =>
          Except.ok
            { runtime with
              state :=
                State.storeStorageBytesAt runtime.state field.slot bytes }
      | _ => Except.error RevertData.typeMismatch
  | some layout@(StorageLayout.struct _) => do
      let state ←
        State.storeStorageLayoutAt runtime.state field.slot layout value
      Except.ok { runtime with state }
  | some layout@(StorageLayout.fixedArray _ _) => do
      let state ←
        State.storeStorageLayoutAt runtime.state field.slot layout value
      Except.ok { runtime with state }
  | some (StorageLayout.mapping _ _) =>
      Except.error RevertData.typeMismatch
  | some layout@(StorageLayout.packedScalar _ _ _ _) => do
      let state ← State.storeStorageLayoutAt runtime.state field.slot layout value
      Except.ok { runtime with state }
  | some (StorageLayout.scalar ty) => do
      let word ← coerceStorageWordAs ty value
      Except.ok
        { runtime with state := runtime.state.storeFieldWord field word }
  | none =>
      let word ← coerceStorageWordAs Ty.uint256 value
      Except.ok
        { runtime with state := runtime.state.storeFieldWord field word }

def Runtime.storeImmutableField (context : Context)
    (runtime : Runtime) (name : String) (value : Value) :
    Except RevertData Runtime := do
  if !context.construction then
    Except.error RevertData.typeMismatch
  else
    pure ()
  let field ←
    match context.immutableField? name with
    | some field => Except.ok field
    | none => Except.error RevertData.typeMismatch
  let coerced ←
    match field.ty.coerceValue? value with
    | some coerced => Except.ok coerced
    | none => Except.error RevertData.typeMismatch
  Except.ok
    { runtime with state := runtime.state.storeImmutable name coerced }

def Runtime.loadStorageByteStringField (context : Context)
    (runtime : Runtime) (name : String) : Except RevertData Value := do
  let field ←
    match context.storageField? name with
    | some field => Except.ok field
    | none => Except.error RevertData.typeMismatch
  match field.layout? with
  | some StorageLayout.bytes =>
      let bytes ← State.loadStorageBytesAt runtime.state field.slot
      Except.ok (Value.bytes bytes)
  | some StorageLayout.string =>
      let bytes ← State.loadStorageBytesAt runtime.state field.slot
      Except.ok (Value.bytes bytes)
  | _ => Except.error RevertData.typeMismatch

def State.clearFixedArraySlots (state : State) (slot defaultWord : Word) :
    Nat -> Nat -> State
  | _, 0 => state
  | index, remaining + 1 =>
      State.clearFixedArraySlots
        (state.storeSlot (fixedArrayStorageSlot slot index) defaultWord)
        slot defaultWord (index + 1) remaining

def State.clearLayoutSpanSlots (state : State) (slot : Word) :
    Nat -> Nat -> State
  | _, 0 => state
  | offset, remaining + 1 =>
      State.clearLayoutSpanSlots
        (state.storeSlot (normWord (SolidCore.Solidity.Shared.norm slot + offset)) 0)
        slot (offset + 1) remaining

mutual

def State.clearStorageLayoutAt (state : State) (slot : Word) :
    StorageLayout -> Except RevertData State
  | StorageLayout.scalar ty => do
      let defaultWord ← coerceStorageWordAs ty ty.defaultValue
      Except.ok (state.storeSlot slot defaultWord)
  | StorageLayout.packedScalar offset bytes _ ty => do
      let defaultWord ← coerceStorageWordAs ty ty.defaultValue
      Except.ok
        (state.storeSlot slot
          (wordReplaceBitRange (offset * 8) (bytes * 8)
            (state.loadSlot slot) defaultWord))
  | StorageLayout.struct layouts =>
      State.clearStructLayoutSlots state slot { slot := 0, offset := 0 } layouts
  | StorageLayout.bytes =>
      Except.ok (State.storeStorageBytesAt state slot [])
  | StorageLayout.string =>
      Except.ok (State.storeStorageBytesAt state slot [])
  | StorageLayout.dynamicArray _ =>
      Except.ok (state.storeSlot slot 0)
  | StorageLayout.mapping _ _ =>
      Except.ok state
  | StorageLayout.fixedArray size elementLayout =>
      Except.ok
        (State.clearLayoutSpanSlots state slot 0
          (StorageLayout.slotSpan
            (StorageLayout.fixedArray size elementLayout)))

def State.clearStructLayoutSlots (state : State) (slot : Word) :
    StorageLayoutCursor -> List StorageLayout -> Except RevertData State
  | _, [] => Except.ok state
  | cursor, layout :: rest => do
      let (offset, nextCursor) := StorageLayout.cursorStep cursor layout
      let state ←
        State.clearStorageLayoutAt state
          (normWord (SolidCore.Solidity.Shared.norm slot + offset)) layout
      State.clearStructLayoutSlots state slot
        nextCursor rest

end

def State.clearDynamicArrayLayoutSlots (state : State) (slot : Word)
    (elementLayout : StorageLayout) :
    Nat -> Nat -> Except RevertData State
  | _, 0 => Except.ok state
  | index, remaining + 1 => do
      let (elementSlot, elementSlotLayout) ←
        match dynamicArrayLayoutStorageSlotAndLayout?
          slot index elementLayout with
        | some pair => Except.ok pair
        | none => Except.error RevertData.typeMismatch
      let state ←
        State.clearStorageLayoutAt state
          elementSlot elementSlotLayout
      State.clearDynamicArrayLayoutSlots
        state slot elementLayout (index + 1) remaining

def State.clearDynamicArrayLayoutAt (state : State) (slot : Word)
    (elementLayout : StorageLayout) : Except RevertData State := do
  let length := SolidCore.Solidity.Shared.norm (state.loadSlot slot)
  let state ←
    State.clearDynamicArrayLayoutSlots state slot elementLayout 0 length
  Except.ok (state.storeSlot slot 0)

mutual

def StorageLayout.clearDepth : StorageLayout -> Nat
  | StorageLayout.scalar _ => 1
  | StorageLayout.packedScalar _ _ _ _ => 1
  | StorageLayout.struct layouts => StorageLayouts.clearDepth layouts + 1
  | StorageLayout.fixedArray _ elementLayout =>
      StorageLayout.clearDepth elementLayout + 1
  | StorageLayout.dynamicArray elementLayout =>
      StorageLayout.clearDepth elementLayout + 1
  | StorageLayout.bytes => 1
  | StorageLayout.string => 1
  | StorageLayout.mapping _ _ => 1

def StorageLayouts.clearDepth : List StorageLayout -> Nat
  | [] => 1
  | layout :: rest =>
      Nat.max (StorageLayout.clearDepth layout)
        (StorageLayouts.clearDepth rest)

end

def State.clearStorageLayoutAtFuel :
    Nat -> State -> Word -> StorageLayout -> Except RevertData State
  | 0, state, slot, layout =>
      State.clearStorageLayoutAt state slot layout
  | fuel + 1, state, slot, layout =>
      match layout with
      | StorageLayout.scalar ty => do
          let defaultWord ← coerceStorageWordAs ty ty.defaultValue
          Except.ok (state.storeSlot slot defaultWord)
      | StorageLayout.packedScalar offset bytes _ ty => do
          let defaultWord ← coerceStorageWordAs ty ty.defaultValue
          Except.ok
            (state.storeSlot slot
              (wordReplaceBitRange (offset * 8) (bytes * 8)
                (state.loadSlot slot) defaultWord))
      | StorageLayout.struct layouts => do
          let (state, _) ←
            layouts.foldlM
              (fun (acc : State × StorageLayoutCursor) layout => do
                let (state, cursor) := acc
                let (offset, nextCursor) :=
                  StorageLayout.cursorStep cursor layout
                let fieldSlot :=
                  normWord (SolidCore.Solidity.Shared.norm slot + offset)
                let state ←
                  State.clearStorageLayoutAtFuel fuel
                    state fieldSlot layout
                Except.ok
                  (state, nextCursor))
              (state, { slot := 0, offset := 0 })
          Except.ok state
      | StorageLayout.bytes =>
          Except.ok (State.storeStorageBytesAt state slot [])
      | StorageLayout.string =>
          Except.ok (State.storeStorageBytesAt state slot [])
      | StorageLayout.dynamicArray elementLayout => do
          let length := SolidCore.Solidity.Shared.norm (state.loadSlot slot)
          let state ←
            (List.range length).foldlM
              (fun state index => do
                let (elementSlot, elementSlotLayout) ←
                  match dynamicArrayLayoutStorageSlotAndLayout?
                    slot index elementLayout with
                  | some pair => Except.ok pair
                  | none => Except.error RevertData.typeMismatch
                let state ←
                  State.clearStorageLayoutAtFuel fuel state
                    elementSlot elementSlotLayout
                Except.ok state)
              state
          Except.ok (state.storeSlot slot 0)
      | StorageLayout.mapping _ _ =>
          Except.ok state
      | StorageLayout.fixedArray size elementLayout =>
          (List.range size).foldlM
            (fun state index => do
              let (elementSlot, elementSlotLayout) ←
                match fixedArrayLayoutStorageSlotAndLayout?
                  slot index elementLayout with
                | some pair => Except.ok pair
                | none => Except.error RevertData.typeMismatch
              let state ←
                State.clearStorageLayoutAtFuel fuel state
                  elementSlot elementSlotLayout
              Except.ok state)
            state

def State.clearStorageLayoutAtDeep (state : State) (slot : Word)
    (layout : StorageLayout) : Except RevertData State :=
  State.clearStorageLayoutAtFuel
    (StorageLayout.clearDepth layout) state slot layout

def State.clearDynamicArrayLayoutTail (state : State) (slot : Word)
    (elementLayout : StorageLayout) (start count : Nat) :
    Except RevertData State :=
  (List.range count).foldlM
    (fun state offset => do
      let (elementSlot, elementSlotLayout) ←
        match dynamicArrayLayoutStorageSlotAndLayout?
          slot (start + offset) elementLayout with
        | some pair => Except.ok pair
        | none => Except.error RevertData.typeMismatch
      State.clearStorageLayoutAtDeep state
        elementSlot elementSlotLayout)
    state

def State.storeStorageLayoutAtWithDeepClearFuel :
    Nat -> State -> Word -> StorageLayout -> Value ->
    Except RevertData State
  | 0, state, slot, layout, value =>
      State.storeStorageLayoutAt state slot layout value
  | fuel + 1, state, slot, layout, value =>
      match layout, value with
      | StorageLayout.struct layouts, Value.tuple values => do
          if layouts.length == values.length then
            let (state, _) ←
              (layouts.zip values).foldlM
                (fun (acc : State × StorageLayoutCursor) pair => do
                  let (state, cursor) := acc
                  let (layout, value) := pair
                  let (offset, nextCursor) :=
                    StorageLayout.cursorStep cursor layout
                  let fieldSlot :=
                    normWord (SolidCore.Solidity.Shared.norm slot + offset)
                  let state ←
                    State.storeStorageLayoutAtWithDeepClearFuel
                      fuel state fieldSlot layout value
                  Except.ok
                    (state, nextCursor))
                (state, { slot := 0, offset := 0 })
            Except.ok state
          else
            Except.error RevertData.typeMismatch
      | StorageLayout.fixedArray size elementLayout,
          Value.fixedArray values => do
          if values.length == size then
            (List.range values.length).zip values |>.foldlM
              (fun state pair => do
                let (index, value) := pair
                let (elementSlot, elementSlotLayout) ←
                  match fixedArrayLayoutStorageSlotAndLayout?
                    slot index elementLayout with
                  | some pair => Except.ok pair
                  | none => Except.error RevertData.typeMismatch
                State.storeStorageLayoutAtWithDeepClearFuel fuel state
                  elementSlot elementSlotLayout value)
              state
          else
            Except.error RevertData.typeMismatch
      | StorageLayout.dynamicArray elementLayout,
          Value.dynamicArray values => do
          let oldLength := SolidCore.Solidity.Shared.norm (state.loadSlot slot)
          let state ←
            (List.range values.length).zip values |>.foldlM
              (fun state pair => do
                let (index, value) := pair
                let (elementSlot, elementSlotLayout) ←
                  match dynamicArrayLayoutStorageSlotAndLayout?
                    slot index elementLayout with
                  | some pair => Except.ok pair
                  | none => Except.error RevertData.typeMismatch
                State.storeStorageLayoutAtWithDeepClearFuel fuel state
                  elementSlot elementSlotLayout value)
              state
          let newLength := values.length
          let state ←
            if newLength < oldLength then
              State.clearDynamicArrayLayoutTail state slot elementLayout
                newLength (oldLength - newLength)
            else
              Except.ok state
          Except.ok (state.storeSlot slot values.length)
      | _, _ =>
          State.storeStorageLayoutAt state slot layout value

def State.storeStorageLayoutAtWithDeepClear (state : State) (slot : Word)
    (layout : StorageLayout) (value : Value) : Except RevertData State :=
  State.storeStorageLayoutAtWithDeepClearFuel
    (StorageLayout.clearDepth layout) state slot layout value

def Runtime.storeStorageFieldWithDeepClear (context : Context)
    (runtime : Runtime) (name : String) (value : Value) :
    Except RevertData Runtime := do
  let field ←
    match context.storageField? name with
    | some field => Except.ok field
    | none => Except.error RevertData.typeMismatch
  let value ← runtime.storageMaterializedValue value
  match field.layout?, value with
  | some (StorageLayout.dynamicArray elementLayout),
      Value.dynamicArray _ => do
      let state ←
        State.storeStorageLayoutAtWithDeepClear runtime.state
          field.slot (StorageLayout.dynamicArray elementLayout)
          value
      Except.ok { runtime with state }
  | _, _ =>
      Runtime.storeStorageField context runtime name value

def Runtime.storeStorageIndexWithDeepClear (context : Context)
    (runtime : Runtime) (name : String) (index value : Value) :
    Except RevertData Runtime := do
  let field ←
    match context.storageField? name with
    | some field => Except.ok field
    | none => Except.error RevertData.typeMismatch
  let value ← runtime.storageMaterializedValue value
  match field.layout? with
  | some (StorageLayout.mapping keyTy valueLayout) => do
      let slot ← mappingStorageSlotForKey field.slot keyTy index
      let state ←
        State.storeStorageLayoutAtWithDeepClear
          runtime.state slot valueLayout value
      Except.ok { runtime with state }
  | some StorageLayout.bytes => do
      let key ← index.expectWord
      let word ← coerceStorageWordAs (Ty.fixedBytes 1) value
      let state ←
        State.storeStorageByteAt runtime.state field.slot key word
      Except.ok { runtime with state }
  | some StorageLayout.string =>
      Except.error RevertData.typeMismatch
  | some (StorageLayout.dynamicArray elementLayout) => do
      let key ← index.expectWord
      let length := runtime.state.loadSlot field.slot
      if SolidCore.Solidity.Shared.norm length <= SolidCore.Solidity.Shared.norm key then
        Except.error RevertData.indexOutOfBounds
      else
        let (elementSlot, elementSlotLayout) ←
          match dynamicArrayLayoutStorageSlotAndLayout?
            field.slot key elementLayout with
          | some pair => Except.ok pair
          | none => Except.error RevertData.typeMismatch
        let state ←
          State.storeStorageLayoutAtWithDeepClear runtime.state
            elementSlot elementSlotLayout value
        Except.ok { runtime with state }
  | some (StorageLayout.fixedArray size elementLayout) => do
      let key ← index.expectWord
      if size <= SolidCore.Solidity.Shared.norm key then
        Except.error RevertData.indexOutOfBounds
      else
        let (elementSlot, elementSlotLayout) ←
          match fixedArrayLayoutStorageSlotAndLayout?
            field.slot key elementLayout with
          | some pair => Except.ok pair
          | none => Except.error RevertData.typeMismatch
        let state ←
          State.storeStorageLayoutAtWithDeepClear runtime.state
            elementSlot elementSlotLayout value
        Except.ok { runtime with state }
  | some (StorageLayout.struct layouts) => do
      let key ← index.expectWord
      match
        structFieldStorageSlot? field.slot layouts
          (SolidCore.Solidity.Shared.norm key)
      with
      | some (fieldSlot, fieldLayout) => do
          let state ←
            State.storeStorageLayoutAtWithDeepClear runtime.state
              fieldSlot fieldLayout value
          Except.ok { runtime with state }
      | none => Except.error RevertData.indexOutOfBounds
  | some (StorageLayout.scalar _) =>
      Except.error RevertData.typeMismatch
  | some (StorageLayout.packedScalar _ _ _ _) =>
      Except.error RevertData.typeMismatch
  | none => do
      let key ← index.expectWord
      let word ← coerceStorageWordAs Ty.uint256 value
      Except.ok
        { runtime with
          state :=
            runtime.state.storeSlot
              (legacyIndexedStorageSlot field.slot key) word }

def Runtime.deleteStorageField (context : Context)
    (runtime : Runtime) (name : String) :
    Except RevertData Runtime := do
  let field ←
    match context.storageField? name with
    | some field => Except.ok field
    | none => Except.error RevertData.typeMismatch
  match field.layout? with
  | some (StorageLayout.dynamicArray elementLayout) => do
      let state ←
        State.clearStorageLayoutAtDeep runtime.state field.slot
          (StorageLayout.dynamicArray elementLayout)
      Except.ok { runtime with state }
  | some StorageLayout.bytes =>
      Except.ok
        { runtime with
          state :=
            State.storeStorageBytesAt runtime.state field.slot [] }
  | some StorageLayout.string =>
      Except.ok
        { runtime with
          state :=
            State.storeStorageBytesAt runtime.state field.slot [] }
  | some (StorageLayout.struct layouts) => do
      let state ←
        State.clearStorageLayoutAtDeep runtime.state field.slot
          (StorageLayout.struct layouts)
      Except.ok { runtime with state }
  | some (StorageLayout.fixedArray size elementLayout) => do
      let state ←
        State.clearStorageLayoutAtDeep runtime.state field.slot
          (StorageLayout.fixedArray size elementLayout)
      Except.ok { runtime with state }
  | some (StorageLayout.mapping _ _) =>
      Except.ok runtime
  | some layout@(StorageLayout.packedScalar _ _ _ _) => do
      let state ← State.clearStorageLayoutAtDeep runtime.state field.slot layout
      Except.ok { runtime with state }
  | some (StorageLayout.scalar ty) => do
      let defaultWord ← coerceStorageWordAs ty ty.defaultValue
      Except.ok
        { runtime with
          state := runtime.state.storeFieldWord field defaultWord }
  | none =>
      Except.ok
        { runtime with state := runtime.state.storeFieldWord field 0 }

def Runtime.deleteStorageIndex (context : Context)
    (runtime : Runtime) (name : String) (index : Value) :
    Except RevertData Runtime := do
  let field ←
    match context.storageField? name with
    | some field => Except.ok field
    | none => Except.error RevertData.typeMismatch
  match field.layout? with
  | some (StorageLayout.mapping keyTy valueLayout) => do
      let slot ← mappingStorageSlotForKey field.slot keyTy index
      let state ←
        State.clearStorageLayoutAtDeep runtime.state slot valueLayout
      Except.ok { runtime with state }
  | some StorageLayout.bytes => do
      let key ← index.expectWord
      let state ← State.clearStorageByteAt runtime.state field.slot key
      Except.ok { runtime with state }
  | some StorageLayout.string =>
      Except.error RevertData.typeMismatch
  | some (StorageLayout.dynamicArray elementLayout) => do
      let key ← index.expectWord
      let length := runtime.state.loadSlot field.slot
      if SolidCore.Solidity.Shared.norm length <= SolidCore.Solidity.Shared.norm key then
        Except.error RevertData.indexOutOfBounds
      else
        let (elementSlot, elementSlotLayout) ←
          match dynamicArrayLayoutStorageSlotAndLayout?
            field.slot key elementLayout with
          | some pair => Except.ok pair
          | none => Except.error RevertData.typeMismatch
        let state ←
          State.clearStorageLayoutAtDeep runtime.state
            elementSlot elementSlotLayout
        Except.ok { runtime with state }
  | some (StorageLayout.fixedArray size elementLayout) => do
      let key ← index.expectWord
      if size <= SolidCore.Solidity.Shared.norm key then
        Except.error RevertData.indexOutOfBounds
      else
        let (elementSlot, elementSlotLayout) ←
          match fixedArrayLayoutStorageSlotAndLayout?
            field.slot key elementLayout with
          | some pair => Except.ok pair
          | none => Except.error RevertData.typeMismatch
        let state ←
          State.clearStorageLayoutAtDeep runtime.state
            elementSlot elementSlotLayout
        Except.ok { runtime with state }
  | some (StorageLayout.struct layouts) => do
      let key ← index.expectWord
      match
        structFieldStorageSlot? field.slot layouts
          (SolidCore.Solidity.Shared.norm key)
      with
      | some (fieldSlot, fieldLayout) => do
          let state ←
            State.clearStorageLayoutAtDeep runtime.state
              fieldSlot fieldLayout
          Except.ok { runtime with state }
      | none => Except.error RevertData.indexOutOfBounds
  | some (StorageLayout.scalar _) =>
      Except.error RevertData.typeMismatch
  | some (StorageLayout.packedScalar _ _ _ _) =>
      Except.error RevertData.typeMismatch
  | none => do
      let key ← index.expectWord
      Except.ok
        { runtime with
          state :=
            runtime.state.storeSlot
              (legacyIndexedStorageSlot field.slot key) 0 }

def State.resolveStoragePathSlot (state : State) :
    Word -> StorageLayout -> List Value ->
    Except RevertData (Word × StorageLayout)
  | slot, layout, [] => Except.ok (slot, layout)
  | slot, StorageLayout.mapping keyTy valueLayout, key :: rest => do
      let nextSlot ← mappingStorageSlotForKey slot keyTy key
      State.resolveStoragePathSlot state nextSlot valueLayout rest
  | slot, StorageLayout.dynamicArray elementLayout, index :: rest => do
      let key ← index.expectWord
      let length := state.loadSlot slot
      if SolidCore.Solidity.Shared.norm length <= SolidCore.Solidity.Shared.norm key then
        Except.error RevertData.indexOutOfBounds
      else
        let (elementSlot, elementSlotLayout) ←
          match dynamicArrayLayoutStorageSlotAndLayout?
            slot key elementLayout with
          | some pair => Except.ok pair
          | none => Except.error RevertData.typeMismatch
        State.resolveStoragePathSlot state
          elementSlot elementSlotLayout rest
  | slot, StorageLayout.fixedArray size elementLayout, index :: rest => do
      let key ← index.expectWord
      if size <= SolidCore.Solidity.Shared.norm key then
        Except.error RevertData.indexOutOfBounds
      else
        let (elementSlot, elementSlotLayout) ←
          match fixedArrayLayoutStorageSlotAndLayout?
            slot key elementLayout with
          | some pair => Except.ok pair
          | none => Except.error RevertData.typeMismatch
        State.resolveStoragePathSlot state
          elementSlot elementSlotLayout rest
  | slot, StorageLayout.bytes, index :: rest => do
      let key ← index.expectWord
      let (elementSlot, offset) ←
        State.storageBytesElementSlotAndOffset state slot key
      State.resolveStoragePathSlot state elementSlot
        (StorageLayout.packedScalar offset 1 false (Ty.fixedBytes 1))
        rest
  | slot, StorageLayout.struct layouts, index :: rest => do
      let key ← index.expectWord
      match structFieldStorageSlot? slot layouts (SolidCore.Solidity.Shared.norm key) with
      | some (fieldSlot, fieldLayout) =>
          State.resolveStoragePathSlot state
            fieldSlot fieldLayout rest
      | none => Except.error RevertData.indexOutOfBounds
  | _, _, _ :: _ =>
      Except.error RevertData.typeMismatch

def Runtime.loadStoragePath (context : Context)
    (runtime : Runtime) (name : String) (indexes : List Value) :
    Except RevertData Value := do
  let field ←
    match context.storageField? name with
    | some field => Except.ok field
    | none => Except.error RevertData.typeMismatch
  if field.transient && !indexes.isEmpty then
    Except.error RevertData.typeMismatch
  else
    pure ()
  let layout ←
    match field.layout? with
    | some layout => Except.ok layout
    | none =>
        match field.ty? with
        | some ty => Except.ok (StorageLayout.scalar ty)
        | none => Except.error RevertData.typeMismatch
  let (slot, valueLayout) ←
    State.resolveStoragePathSlot runtime.state field.slot layout indexes
  runtime.state.loadStorageLayoutAt slot valueLayout

def Runtime.loadStorageRefPathValue (context : Context)
    (runtime : Runtime) (name : String) (indexes : List Value) :
    Except RevertData Value :=
  runtime.loadStoragePath context name indexes

def Runtime.storeStoragePathWithDeepClear (context : Context)
    (runtime : Runtime) (name : String) (indexes : List Value)
    (value : Value) : Except RevertData Runtime := do
  let field ←
    match context.storageField? name with
    | some field => Except.ok field
    | none => Except.error RevertData.typeMismatch
  let value ← runtime.storageMaterializedValue value
  if field.transient && !indexes.isEmpty then
    Except.error RevertData.typeMismatch
  else
    pure ()
  let layout ←
    match field.layout? with
    | some layout => Except.ok layout
    | none =>
        match field.ty? with
        | some ty => Except.ok (StorageLayout.scalar ty)
        | none => Except.error RevertData.typeMismatch
  let (slot, valueLayout) ←
    State.resolveStoragePathSlot runtime.state field.slot layout indexes
  let state ←
    State.storeStorageLayoutAtWithDeepClear
      runtime.state slot valueLayout value
  Except.ok { runtime with state }

def Runtime.deleteStoragePath (context : Context)
    (runtime : Runtime) (name : String) (indexes : List Value) :
    Except RevertData Runtime := do
  let field ←
    match context.storageField? name with
    | some field => Except.ok field
    | none => Except.error RevertData.typeMismatch
  if field.transient && !indexes.isEmpty then
    Except.error RevertData.typeMismatch
  else
    pure ()
  let layout ←
    match field.layout? with
    | some layout => Except.ok layout
    | none =>
        match field.ty? with
        | some ty => Except.ok (StorageLayout.scalar ty)
        | none => Except.error RevertData.typeMismatch
  let (slot, valueLayout) ←
    State.resolveStoragePathSlot runtime.state field.slot layout indexes
  let state ←
    State.clearStorageLayoutAtDeep runtime.state slot valueLayout
  Except.ok { runtime with state }

def Runtime.loadStorageIndex (context : Context)
    (runtime : Runtime) (name : String) (index : Value) :
    Except RevertData Value := do
  let field ←
    match context.storageField? name with
    | some field => Except.ok field
    | none => Except.error RevertData.typeMismatch
  match field.layout? with
  | some (StorageLayout.mapping keyTy valueLayout) => do
      let slot ← mappingStorageSlotForKey field.slot keyTy index
      runtime.state.loadStorageLayoutAt slot valueLayout
  | some StorageLayout.bytes => do
      let key ← index.expectWord
      let byte ← State.loadStorageByteAt runtime.state field.slot key
      Except.ok (Value.word byte)
  | some StorageLayout.string =>
      Except.error RevertData.typeMismatch
  | some (StorageLayout.dynamicArray elementLayout) => do
      let key ← index.expectWord
      let length := runtime.state.loadSlot field.slot
      if SolidCore.Solidity.Shared.norm length <= SolidCore.Solidity.Shared.norm key then
        Except.error RevertData.indexOutOfBounds
      else
        let (elementSlot, elementSlotLayout) ←
          match dynamicArrayLayoutStorageSlotAndLayout?
            field.slot key elementLayout with
          | some pair => Except.ok pair
          | none => Except.error RevertData.typeMismatch
        runtime.state.loadStorageLayoutAt
          elementSlot elementSlotLayout
  | some (StorageLayout.fixedArray size elementLayout) => do
      let key ← index.expectWord
      if size <= SolidCore.Solidity.Shared.norm key then
        Except.error RevertData.indexOutOfBounds
      else
        let (elementSlot, elementSlotLayout) ←
          match fixedArrayLayoutStorageSlotAndLayout?
            field.slot key elementLayout with
          | some pair => Except.ok pair
          | none => Except.error RevertData.typeMismatch
        runtime.state.loadStorageLayoutAt
          elementSlot elementSlotLayout
  | some (StorageLayout.struct layouts) => do
      let key ← index.expectWord
      match structFieldStorageSlot? field.slot layouts (SolidCore.Solidity.Shared.norm key) with
      | some (fieldSlot, fieldLayout) =>
          runtime.state.loadStorageLayoutAt
            fieldSlot fieldLayout
      | none => Except.error RevertData.indexOutOfBounds
  | some (StorageLayout.scalar _) =>
      Except.error RevertData.typeMismatch
  | some (StorageLayout.packedScalar _ _ _ _) =>
      Except.error RevertData.typeMismatch
  | none => do
      let key ← index.expectWord
      Except.ok
        (Value.word
          (runtime.state.loadSlot (legacyIndexedStorageSlot field.slot key)))

def Runtime.storeStorageIndex (context : Context)
    (runtime : Runtime) (name : String) (index value : Value) :
    Except RevertData Runtime := do
  let field ←
    match context.storageField? name with
    | some field => Except.ok field
    | none => Except.error RevertData.typeMismatch
  let value ← runtime.storageMaterializedValue value
  match field.layout? with
  | some (StorageLayout.mapping keyTy valueLayout) => do
      let slot ← mappingStorageSlotForKey field.slot keyTy index
      let state ←
        State.storeStorageLayoutAt runtime.state slot valueLayout value
      Except.ok { runtime with state }
  | some StorageLayout.bytes => do
      let key ← index.expectWord
      let word ← coerceStorageWordAs (Ty.fixedBytes 1) value
      let state ←
        State.storeStorageByteAt runtime.state field.slot key word
      Except.ok { runtime with state }
  | some StorageLayout.string =>
      Except.error RevertData.typeMismatch
  | some (StorageLayout.dynamicArray elementLayout) => do
      let key ← index.expectWord
      let length := runtime.state.loadSlot field.slot
      if SolidCore.Solidity.Shared.norm length <= SolidCore.Solidity.Shared.norm key then
        Except.error RevertData.indexOutOfBounds
      else
        let (elementSlot, elementSlotLayout) ←
          match dynamicArrayLayoutStorageSlotAndLayout?
            field.slot key elementLayout with
          | some pair => Except.ok pair
          | none => Except.error RevertData.typeMismatch
        let state ←
          State.storeStorageLayoutAt runtime.state
            elementSlot elementSlotLayout value
        Except.ok { runtime with state }
  | some (StorageLayout.fixedArray size elementLayout) => do
      let key ← index.expectWord
      if size <= SolidCore.Solidity.Shared.norm key then
        Except.error RevertData.indexOutOfBounds
      else
        let (elementSlot, elementSlotLayout) ←
          match fixedArrayLayoutStorageSlotAndLayout?
            field.slot key elementLayout with
          | some pair => Except.ok pair
          | none => Except.error RevertData.typeMismatch
        let state ←
          State.storeStorageLayoutAt runtime.state
            elementSlot elementSlotLayout value
        Except.ok { runtime with state }
  | some (StorageLayout.struct layouts) => do
      let key ← index.expectWord
      match
        structFieldStorageSlot? field.slot layouts
          (SolidCore.Solidity.Shared.norm key)
      with
      | some (fieldSlot, fieldLayout) => do
          let state ←
            State.storeStorageLayoutAt runtime.state
              fieldSlot fieldLayout value
          Except.ok { runtime with state }
      | none => Except.error RevertData.indexOutOfBounds
  | some (StorageLayout.scalar _) =>
      Except.error RevertData.typeMismatch
  | some (StorageLayout.packedScalar _ _ _ _) =>
      Except.error RevertData.typeMismatch
  | none => do
      let key ← index.expectWord
      let word ← coerceStorageWordAs Ty.uint256 value
      Except.ok
        { runtime with
          state :=
            runtime.state.storeSlot
              (legacyIndexedStorageSlot field.slot key) word }

def Runtime.storageArrayPush (context : Context)
    (runtime : Runtime) (name : String) (value? : Option Value) :
    Except RevertData Runtime := do
  let field ←
    match context.storageField? name with
    | some field => Except.ok field
    | none => Except.error RevertData.typeMismatch
  match field.layout? with
    | some (StorageLayout.dynamicArray elementLayout) => do
        let length := runtime.state.loadSlot field.slot
        let rawLength := SolidCore.Solidity.Shared.norm length + 1
        if wordModulus <= rawLength then
          Except.error RevertData.overflow
        else
          pure ()
        let (elementSlot, elementSlotLayout) ←
          match dynamicArrayLayoutStorageSlotAndLayout?
            field.slot length elementLayout with
          | some pair => Except.ok pair
          | none => Except.error RevertData.typeMismatch
        let state ←
          match value? with
          | some value =>
              let value ← runtime.storageMaterializedValue value
              State.storeStorageLayoutAtWithDeepClear runtime.state
                elementSlot elementSlotLayout value
          | none =>
              State.clearStorageLayoutAtDeep runtime.state
                elementSlot elementSlotLayout
        Except.ok
          { runtime with
            state := state.storeSlot field.slot (normWord rawLength) }
    | some StorageLayout.bytes => do
        let word ←
          match value? with
          | some value => coerceStorageWordAs (Ty.fixedBytes 1) value
          | none => Except.ok 0
        let state ←
          State.pushStorageByteAt runtime.state field.slot word
        Except.ok
          { runtime with state }
    | some StorageLayout.string =>
        Except.error RevertData.typeMismatch
    | none => do
        let length := runtime.state.loadSlot field.slot
        let rawLength := SolidCore.Solidity.Shared.norm length + 1
        if wordModulus <= rawLength then
          Except.error RevertData.overflow
        else
          pure ()
        let word ←
          match value? with
          | some value => coerceStorageWordAs Ty.uint256 value
          | none => Except.ok 0
        Except.ok
          { runtime with
            state :=
              (runtime.state.storeSlot
                (legacyIndexedStorageSlot field.slot length) word)
                |>.storeSlot field.slot (normWord rawLength) }
    | _ => Except.error RevertData.typeMismatch

def Runtime.storageArrayPop (context : Context)
    (runtime : Runtime) (name : String) :
    Except RevertData Runtime := do
  let field ←
    match context.storageField? name with
    | some field => Except.ok field
    | none => Except.error RevertData.typeMismatch
  match field.layout? with
  | some (StorageLayout.dynamicArray _) => Except.ok ()
  | some StorageLayout.bytes => Except.ok ()
  | some StorageLayout.string => Except.error RevertData.typeMismatch
  | none => Except.ok ()
  | _ => Except.error RevertData.typeMismatch
  match field.layout? with
    | some (StorageLayout.dynamicArray elementLayout) => do
        let length := runtime.state.loadSlot field.slot
        if wordEq length 0 then
          Except.error RevertData.popEmptyArray
        else
          pure ()
        let newLength := SolidCore.Solidity.Shared.subWord length 1
        let (elementSlot, elementSlotLayout) ←
          match dynamicArrayLayoutStorageSlotAndLayout?
            field.slot newLength elementLayout with
          | some pair => Except.ok pair
          | none => Except.error RevertData.typeMismatch
        let state ←
          State.clearStorageLayoutAtDeep runtime.state
            elementSlot elementSlotLayout
        Except.ok
          { runtime with state := state.storeSlot field.slot newLength }
    | some StorageLayout.bytes => do
        let state ← State.popStorageByteAt runtime.state field.slot
        Except.ok { runtime with state }
    | none => do
        let length := runtime.state.loadSlot field.slot
        if wordEq length 0 then
          Except.error RevertData.popEmptyArray
        else
          pure ()
        let newLength := SolidCore.Solidity.Shared.subWord length 1
        Except.ok
          { runtime with
            state :=
              (runtime.state.storeSlot
                (legacyIndexedStorageSlot field.slot newLength) 0)
                |>.storeSlot field.slot newLength }
    | _ => Except.error RevertData.typeMismatch

def Runtime.storageArrayPushPath (context : Context)
    (runtime : Runtime) (name : String) (indexes : List Value)
    (value? : Option Value) :
    Except RevertData Runtime := do
  match indexes with
  | [] => runtime.storageArrayPush context name value?
  | _ =>
      let field ←
        match context.storageField? name with
        | some field => Except.ok field
        | none => Except.error RevertData.typeMismatch
      if field.transient then
        Except.error RevertData.typeMismatch
      else
        pure ()
      let layout ←
        match field.layout? with
        | some layout => Except.ok layout
        | none => Except.error RevertData.typeMismatch
      let (slot, valueLayout) ←
        State.resolveStoragePathSlot runtime.state field.slot layout indexes
      match valueLayout with
        | StorageLayout.dynamicArray elementLayout => do
            let length := runtime.state.loadSlot slot
            let rawLength := SolidCore.Solidity.Shared.norm length + 1
            if wordModulus <= rawLength then
              Except.error RevertData.overflow
            else
              pure ()
            let (elementSlot, elementSlotLayout) ←
              match dynamicArrayLayoutStorageSlotAndLayout?
                slot length elementLayout with
              | some pair => Except.ok pair
              | none => Except.error RevertData.typeMismatch
            let state ←
              match value? with
              | some value =>
                  let value ← runtime.storageMaterializedValue value
                  State.storeStorageLayoutAtWithDeepClear runtime.state
                    elementSlot elementSlotLayout value
              | none =>
                  State.clearStorageLayoutAtDeep runtime.state
                    elementSlot elementSlotLayout
            Except.ok
              { runtime with
                state := state.storeSlot slot (normWord rawLength) }
        | StorageLayout.bytes => do
            let word ←
              match value? with
              | some value => coerceStorageWordAs (Ty.fixedBytes 1) value
              | none => Except.ok 0
            let state ← State.pushStorageByteAt runtime.state slot word
            Except.ok { runtime with state }
        | StorageLayout.string =>
            Except.error RevertData.typeMismatch
        | _ => Except.error RevertData.typeMismatch

def Runtime.storageArrayPopPath (context : Context)
    (runtime : Runtime) (name : String) (indexes : List Value) :
    Except RevertData Runtime := do
  match indexes with
  | [] => runtime.storageArrayPop context name
  | _ =>
      let field ←
        match context.storageField? name with
        | some field => Except.ok field
        | none => Except.error RevertData.typeMismatch
      if field.transient then
        Except.error RevertData.typeMismatch
      else
        pure ()
      let layout ←
        match field.layout? with
        | some layout => Except.ok layout
        | none => Except.error RevertData.typeMismatch
      let (slot, valueLayout) ←
        State.resolveStoragePathSlot runtime.state field.slot layout indexes
      match valueLayout with
        | StorageLayout.dynamicArray elementLayout => do
            let length := runtime.state.loadSlot slot
            if wordEq length 0 then
              Except.error RevertData.popEmptyArray
            else
              pure ()
            let newLength := SolidCore.Solidity.Shared.subWord length 1
            let (elementSlot, elementSlotLayout) ←
              match dynamicArrayLayoutStorageSlotAndLayout?
                slot newLength elementLayout with
              | some pair => Except.ok pair
              | none => Except.error RevertData.typeMismatch
            let state ←
              State.clearStorageLayoutAtDeep runtime.state
                elementSlot elementSlotLayout
            Except.ok
              { runtime with state := state.storeSlot slot newLength }
        | StorageLayout.bytes => do
            let state ← State.popStorageByteAt runtime.state slot
            Except.ok { runtime with state }
        | StorageLayout.string =>
            Except.error RevertData.typeMismatch
        | _ => Except.error RevertData.typeMismatch

def abiAddressFits (value : Word) : Bool :=
  SolidCore.Solidity.Shared.norm value < 2 ^ 160

def abiSelectorFits (value : Word) : Bool :=
  SolidCore.Solidity.Shared.norm value < 2 ^ (8 * selectorBytes)

def abiFixedBytesFits (size : Nat) (value : Word) : Bool :=
  0 < size && size <= wordBytes &&
    SolidCore.Solidity.Shared.norm value < 2 ^ (8 * size)

def abiAllZeroBytes : List Byte -> Bool
  | [] => true
  | byte :: rest => normByte byte == 0 && abiAllZeroBytes rest

def abiStaticBytes? : Ty -> Value -> Option (List Byte)
  | Ty.bool, Value.word value =>
      if wordEq value 0 || wordEq value 1 then
        some (wordToBytesBE wordBytes value)
      else
        none
  | Ty.address, Value.word value =>
      if abiAddressFits value then
        some (wordToBytesBE wordBytes value)
      else
        none
  | Ty.uint256, Value.word value => some (wordToBytesBE wordBytes value)
  | Ty.int256, Value.int value => some (wordToBytesBE wordBytes value)
  | Ty.fixedBytes size, Value.word value =>
      if abiFixedBytesFits size value then
        some
          (wordToBytesBE size value ++
            List.replicate (wordBytes - size) 0)
      else
        none
  | Ty.externalFunction, Value.externalFunction addr selector =>
      if abiAddressFits addr && abiSelectorFits selector then
        some
          (wordToBytesBE 20 addr ++
            wordToBytesBE selectorBytes selector ++
            List.replicate (wordBytes - 20 - selectorBytes) 0)
      else
        none
  | _, _ => none

def abiPaddingLength (length : Nat) : Nat :=
  (wordBytes - length % wordBytes) % wordBytes

def abiPadRightWord (bytes : List Byte) : List Byte :=
  bytes.map normByte ++ List.replicate (abiPaddingLength bytes.length) 0

mutual

def Ty.isDynamicAbi : Ty -> Bool
  | Ty.bytesCalldata => true
  | Ty.dynamicArray _ => true
  | Ty.fixedArray _ elementTy => Ty.isDynamicAbi elementTy
  | Ty.tuple elements => Ty.listHasDynamicAbi elements
  | _ => false

def Ty.listHasDynamicAbi : List Ty -> Bool
  | [] => false
  | ty :: rest => Ty.isDynamicAbi ty || Ty.listHasDynamicAbi rest

end

def Ty.isHashedEventIndexed : Ty -> Bool
  | Ty.bytesCalldata => true
  | Ty.dynamicArray _ => true
  | Ty.fixedArray _ _ => true
  | Ty.tuple _ => true
  | _ => false

mutual

def Ty.staticAbiHeadWords? : Ty -> Option Nat
  | Ty.bool => some 1
  | Ty.address => some 1
  | Ty.uint256 => some 1
  | Ty.int256 => some 1
  | Ty.fixedBytes _ => some 1
  | Ty.externalFunction => some 1
  | Ty.fixedArray size elementTy =>
      if Ty.isDynamicAbi elementTy then
        none
      else
        match Ty.staticAbiHeadWords? elementTy with
        | some words => some (size * words)
        | none => none
  | Ty.tuple elements =>
      if Ty.listHasDynamicAbi elements then
        none
      else
        Ty.listStaticAbiHeadWords? elements
  | _ => none

def Ty.listStaticAbiHeadWords? : List Ty -> Option Nat
  | [] => some 0
  | ty :: rest => do
      let head ← Ty.staticAbiHeadWords? ty
      let tail ← Ty.listStaticAbiHeadWords? rest
      some (head + tail)

end

def Ty.abiHeadWords? (ty : Ty) : Option Nat :=
  if Ty.isDynamicAbi ty then
    some 1
  else
    Ty.staticAbiHeadWords? ty

def Ty.listAbiHeadWords? : List Ty -> Option Nat
  | [] => some 0
  | ty :: rest => do
      let head ← Ty.abiHeadWords? ty
      let tail ← Ty.listAbiHeadWords? rest
      some (head + tail)

mutual

def abiEncodeStaticValue? : Ty -> Value -> Option (List Byte)
  | Ty.fixedArray size elementTy, Value.fixedArray values =>
      if values.length == size && !Ty.isDynamicAbi elementTy then
        abiEncodeStaticValueList? elementTy values
      else
        none
  | Ty.tuple elementTys, Value.tuple values =>
      if values.length == elementTys.length &&
          !Ty.listHasDynamicAbi elementTys then
        abiEncodeStaticTupleValues? elementTys values
      else
        none
  | ty, value => abiStaticBytes? ty value

def abiEncodeStaticValueList? (ty : Ty) :
    List Value -> Option (List Byte)
  | [] => some []
  | value :: rest => do
      let head ← abiEncodeStaticValue? ty value
      let tail ← abiEncodeStaticValueList? ty rest
      some (head ++ tail)

def abiEncodeStaticTupleValues? :
    List Ty -> List Value -> Option (List Byte)
  | [], [] => some []
  | ty :: tys, value :: values => do
      let head ← abiEncodeStaticValue? ty value
      let tail ← abiEncodeStaticTupleValues? tys values
      some (head ++ tail)
  | _, _ => none

end

mutual

def abiEncodeDynamicPayload? : Ty -> Value -> Option (List Byte)
  | Ty.bytesCalldata, Value.bytes bytes =>
      some (wordToBytesBE wordBytes bytes.length ++ abiPadRightWord bytes)
  | Ty.dynamicArray elementTy, Value.dynamicArray values =>
      let rec encodeValues :
          List Value -> Nat -> Option (List Byte × List Byte × Nat)
        | [], offset => some ([], [], offset)
        | value :: rest, offset =>
            if Ty.isDynamicAbi elementTy then
              match abiEncodeDynamicPayload? elementTy value with
              | some payload =>
                  match encodeValues rest (offset + payload.length) with
                  | some (heads, tails, finalOffset) =>
                      some (wordToBytesBE wordBytes offset ++ heads,
                        payload ++ tails, finalOffset)
                  | none => none
              | none => none
            else
              match abiEncodeStaticValue? elementTy value,
                  encodeValues rest offset with
              | some head, some (heads, tails, finalOffset) =>
                  some (head ++ heads, tails, finalOffset)
              | _, _ => none
      match Ty.abiHeadWords? elementTy with
      | some elementWords =>
          let initialOffset := wordBytes * values.length * elementWords
          match encodeValues values initialOffset with
          | some (heads, tails, _) =>
              some (wordToBytesBE wordBytes values.length ++ heads ++ tails)
          | none => none
      | none => none
  | Ty.fixedArray size elementTy, Value.fixedArray values =>
      if values.length == size && Ty.isDynamicAbi elementTy then
        let rec encodeFixedValues :
            List Value -> Nat -> Option (List Byte × List Byte × Nat)
          | [], offset => some ([], [], offset)
          | value :: rest, offset => do
              let payload ← abiEncodeDynamicPayload? elementTy value
              let encodedRest ← encodeFixedValues rest (offset + payload.length)
              match encodedRest with
              | (heads, tails, finalOffset) =>
                  some (wordToBytesBE wordBytes offset ++ heads,
                    payload ++ tails, finalOffset)
        match encodeFixedValues values (wordBytes * size) with
        | some (heads, tails, _) => some (heads ++ tails)
        | none => none
      else
        none
  | Ty.tuple elementTys, Value.tuple values =>
      if values.length == elementTys.length &&
          Ty.listHasDynamicAbi elementTys then
        let rec encodeTupleValues :
            List Ty -> List Value -> Nat ->
              Option (List Byte × List Byte × Nat)
          | [], [], offset => some ([], [], offset)
          | ty :: tys, value :: rest, offset =>
              if Ty.isDynamicAbi ty then
                match abiEncodeDynamicPayload? ty value with
                | some payload =>
                    match encodeTupleValues tys rest
                        (offset + payload.length) with
                    | some (heads, tails, finalOffset) =>
                        some (wordToBytesBE wordBytes offset ++ heads,
                          payload ++ tails, finalOffset)
                    | none => none
                | none => none
              else
                match abiEncodeStaticValue? ty value,
                    encodeTupleValues tys rest offset with
                | some head, some (heads, tails, finalOffset) =>
                    some (head ++ heads, tails, finalOffset)
                | _, _ => none
          | _, _, _ => none
        match Ty.listAbiHeadWords? elementTys with
        | some headWords =>
            match encodeTupleValues elementTys values (wordBytes * headWords) with
            | some (heads, tails, _) => some (heads ++ tails)
            | none => none
        | none => none
      else
        none
  | _, _ => none

end

def abiEncodeValuesAux? :
    List Ty -> List Value -> Nat -> Option (List Byte × List Byte × Nat)
  | [], [], offset => some ([], [], offset)
  | ty :: tys, value :: values, offset =>
      if Ty.isDynamicAbi ty then
        match abiEncodeDynamicPayload? ty value with
        | some payload =>
            match abiEncodeValuesAux? tys values
                (offset + payload.length) with
            | some (heads, tails, finalOffset) =>
                some (wordToBytesBE wordBytes offset ++ heads,
                  payload ++ tails, finalOffset)
            | none => none
        | none => none
      else
        match abiEncodeStaticValue? ty value,
            abiEncodeValuesAux? tys values offset with
        | some head, some (heads, tails, finalOffset) =>
            some (head ++ heads, tails, finalOffset)
        | _, _ => none
  | _, _, _ => none

def abiEncodeValues? (tys : List Ty) (values : List Value) :
    Option (List Byte) := do
  let headWords ← Ty.listAbiHeadWords? tys
  match abiEncodeValuesAux? tys values (wordBytes * headWords) with
  | some (heads, tails, _) => some (heads ++ tails)
  | none => none

mutual

def Ty.abiDecodeFuel : Ty -> Nat
  | Ty.fixedArray _ elementTy => Ty.abiDecodeFuel elementTy + 1
  | Ty.dynamicArray elementTy => Ty.abiDecodeFuel elementTy + 1
  | Ty.tuple elements => Ty.listAbiDecodeFuel elements + 1
  | _ => 1

def Ty.listAbiDecodeFuel : List Ty -> Nat
  | [] => 0
  | ty :: rest => Ty.abiDecodeFuel ty + Ty.listAbiDecodeFuel rest

end

def abiDecodeValueAtWithFuel? :
    Nat -> List Byte -> Nat -> Ty -> Option Value
  | 0, _, _, _ => none
  | _fuel + 1, argData, headIndex, Ty.bool => do
      let value ← readWord? argData (wordBytes * headIndex)
      if wordEq value 0 || wordEq value 1 then
        some (Value.word value)
      else
        none
  | _fuel + 1, argData, headIndex, Ty.address => do
      let value ← readWord? argData (wordBytes * headIndex)
      if abiAddressFits value then
        some (Value.word value)
      else
        none
  | _fuel + 1, argData, headIndex, Ty.uint256 => do
      let value ← readWord? argData (wordBytes * headIndex)
      some (Value.word value)
  | _fuel + 1, argData, headIndex, Ty.int256 => do
      let value ← readWord? argData (wordBytes * headIndex)
      some (Value.int value)
  | _fuel + 1, argData, headIndex, Ty.fixedBytes size =>
      if 0 < size && size <= wordBytes then
        do
        let slot ← readBytes? argData (wordBytes * headIndex) wordBytes
        let bytes ← readBytes? slot 0 size
        let padding ← readBytes? slot size (wordBytes - size)
        if abiAllZeroBytes padding then
          some (Value.word (bytesToWordBE bytes))
        else
          none
      else
        none
  | _fuel + 1, argData, headIndex, Ty.externalFunction => do
      let slot ← readBytes? argData (wordBytes * headIndex) wordBytes
      let addressBytes ← readBytes? slot 0 20
      let selectorPart ← readBytes? slot 20 selectorBytes
      let padding ←
        readBytes? slot (20 + selectorBytes)
          (wordBytes - 20 - selectorBytes)
      if abiAllZeroBytes padding then
        some
          (Value.externalFunction
            (bytesToWordBE addressBytes) (bytesToWordBE selectorPart))
      else
        none
  | _fuel + 1, argData, headIndex, Ty.bytesCalldata => do
      let offset ← readWord? argData (wordBytes * headIndex)
      let length ← readWord? argData offset
      let bytes ← readBytes? argData (offset + wordBytes) length
      some (Value.bytes bytes)
  | fuel + 1, argData, headIndex, Ty.dynamicArray elementTy => do
      let offset ← readWord? argData (wordBytes * headIndex)
      let length ← readWord? argData offset
      let rec decodeDynamicValues? : Nat -> Nat -> Option (List Value)
        | 0, _ => some []
        | remaining + 1, index => do
            let value ←
              abiDecodeValueAtWithFuel? fuel
                (argData.drop (offset + wordBytes)) index elementTy
            let step ← Ty.abiHeadWords? elementTy
            let rest ← decodeDynamicValues? remaining (index + step)
            some (value :: rest)
      let values ← decodeDynamicValues? length 0
      some (Value.dynamicArray values)
  | fuel + 1, argData, headIndex, Ty.fixedArray size elementTy =>
      let rec decodeFixedValues? (arrayData : List Byte) :
          Nat -> Nat -> Option (List Value)
        | 0, _ => some []
        | remaining + 1, index => do
            let value ←
              abiDecodeValueAtWithFuel? fuel arrayData index elementTy
            let step ← Ty.abiHeadWords? elementTy
            let rest ← decodeFixedValues? arrayData remaining (index + step)
            some (value :: rest)
      if Ty.isDynamicAbi elementTy then
        do
        let offset ← readWord? argData (wordBytes * headIndex)
        let values ← decodeFixedValues? (argData.drop offset) size 0
        some (Value.fixedArray values)
      else
        do
        let values ← decodeFixedValues? argData size headIndex
        some (Value.fixedArray values)
  | fuel + 1, argData, headIndex, Ty.tuple elementTys =>
      let rec decodeTupleValues? (tupleData : List Byte) :
          List Ty -> Nat -> Option (List Value)
        | [], _ => some []
        | ty :: tys, index => do
            let value ← abiDecodeValueAtWithFuel? fuel tupleData index ty
            let step ← Ty.abiHeadWords? ty
            let rest ← decodeTupleValues? tupleData tys (index + step)
            some (value :: rest)
      if Ty.listHasDynamicAbi elementTys then
        do
        let offset ← readWord? argData (wordBytes * headIndex)
        let values ← decodeTupleValues? (argData.drop offset) elementTys 0
        some (Value.tuple values)
      else
        do
        let values ← decodeTupleValues? argData elementTys headIndex
        some (Value.tuple values)

def abiDecodeValueAt? (argData : List Byte) (headIndex : Nat)
    (ty : Ty) : Option Value :=
  abiDecodeValueAtWithFuel? (Ty.abiDecodeFuel ty) argData headIndex ty

def abiDecodeValuesAux? (argData : List Byte) :
    List Ty -> Nat -> Option (List Value)
  | [], _ => some []
  | ty :: tys, index => do
      let value ← abiDecodeValueAt? argData index ty
      let headWords ← Ty.abiHeadWords? ty
      let values ← abiDecodeValuesAux? argData tys (index + headWords)
      some (value :: values)

def abiDecodeValues? (tys : List Ty) (argData : List Byte) :
    Option (List Value) :=
  abiDecodeValuesAux? argData tys 0

mutual

def abiEventIndexedBytes? (padDynamic : Bool) :
    Ty -> Value -> Option (List Byte)
  | Ty.bytesCalldata, Value.bytes bytes =>
      if padDynamic then
        some (abiPadRightWord bytes)
      else
        some (bytes.map normByte)
  | Ty.dynamicArray elementTy, Value.dynamicArray values =>
      abiEventIndexedArrayBytes? elementTy values
  | Ty.fixedArray size elementTy, Value.fixedArray values =>
      if values.length == size then
        abiEventIndexedArrayBytes? elementTy values
      else
        none
  | Ty.tuple tys, Value.tuple values =>
      abiEventIndexedTupleBytes? tys values
  | ty, value => abiStaticBytes? ty value

def abiEventIndexedArrayBytes? (ty : Ty) :
    List Value -> Option (List Byte)
  | [] => some []
  | value :: rest => do
      let head ← abiEventIndexedBytes? true ty value
      let tail ← abiEventIndexedArrayBytes? ty rest
      some (head ++ tail)

def abiEventIndexedTupleBytes? :
    List Ty -> List Value -> Option (List Byte)
  | [], [] => some []
  | ty :: tys, value :: values => do
      let head ← abiEventIndexedBytes? true ty value
      let tail ← abiEventIndexedTupleBytes? tys values
      some (head ++ tail)
  | _, _ => none

end

def abiEventTopic? (ty : Ty) (value : Value) : Option Word :=
  if Ty.isHashedEventIndexed ty then
    match abiEventIndexedBytes? false ty value with
    | some bytes => some (keccakWord bytes)
    | none => none
  else
    match abiStaticBytes? ty value with
    | some bytes => some (bytesToWordBE bytes)
    | none => none

structure EventEncoding where
  topics : List Word
  dataBytes : List Byte
  indexedValues : List Value
  dataValues : List Value
  deriving Repr

def EventDecl.encodeFields? (decl : EventDecl)
    (values : List Value) : Option EventEncoding :=
  let rec encode (fields : List EventField) (values : List Value) :
      Option (List Word × List Ty × List Value × List Value × List Value) :=
    match fields, values with
    | [], [] => some ([], [], [], [], [])
    | field :: fields, value :: rest => do
        let (topics, dataTys, dataValues, indexedValues, sourceDataValues) ←
          encode fields rest
        if field.indexed then
          let topic ← abiEventTopic? field.ty value
          some (topic :: topics, dataTys, dataValues,
            value :: indexedValues, sourceDataValues)
        else
          some (topics, field.ty :: dataTys, value :: dataValues,
            indexedValues, value :: sourceDataValues)
    | _, _ => none
  match encode decl.fields values with
  | some (indexedTopics, dataTys, dataValues, indexedValues, sourceDataValues) =>
      match abiEncodeValues? dataTys dataValues with
      | some dataBytes =>
          some
            { topics := decl.topic?.toList ++ indexedTopics
              dataBytes := dataBytes
              indexedValues := indexedValues
              dataValues := sourceDataValues }
      | none => none
  | none => none

mutual

def abiEncodePackedValue? : Ty -> Value -> Option (List Byte)
  | Ty.bool, Value.word value =>
      if wordEq value 0 then
        some [0]
      else if wordEq value 1 then
        some [1]
      else
        none
  | Ty.address, Value.word value => some (wordToBytesBE 20 value)
  | Ty.uint256, Value.word value => some (wordToBytesBE wordBytes value)
  | Ty.int256, Value.int value => some (wordToBytesBE wordBytes value)
  | Ty.fixedBytes size, Value.word value =>
      if 0 < size && size <= wordBytes then
        some (wordToBytesBE size value)
      else
        none
  | Ty.externalFunction, Value.externalFunction addr selector =>
      some
        (wordToBytesBE 20 addr ++
          wordToBytesBE selectorBytes selector)
  | Ty.bytesCalldata, Value.bytes bytes => some (bytes.map normByte)
  | Ty.fixedArray size elementTy, Value.fixedArray values =>
      if values.length == size then
        abiEncodePackedArrayValues? elementTy values
      else
        none
  | Ty.dynamicArray elementTy, Value.dynamicArray values =>
      abiEncodePackedArrayValues? elementTy values
  | _, _ => none

def abiEncodePackedArrayElement? (ty : Ty) (value : Value) :
    Option (List Byte) :=
  match ty with
  | Ty.fixedArray _ _ => none
  | Ty.dynamicArray _ => none
  | Ty.tuple _ => none
  | _ => abiEventIndexedBytes? true ty value

def abiEncodePackedArrayValues? (ty : Ty) :
    List Value -> Option (List Byte)
  | [] => some []
  | value :: rest => do
      let head ← abiEncodePackedArrayElement? ty value
      let tail ← abiEncodePackedArrayValues? ty rest
      some (head ++ tail)

end

-- Pack a narrow (`uintN`/`intN`/`enum`) top-level scalar to `byteWidth` bytes.
-- `abi.encodePacked` uses each top-level value's true width (N/8) instead of the
-- 32-byte ABI padding; the two's-complement low bytes are exactly what solc
-- emits for both `uintN` and `intN` (e.g. `int8(-1)` -> `0xff`).
def abiEncodePackedNarrowScalar? (byteWidth : Nat) : Value -> Option (List Byte)
  | Value.word value => some (wordToBytesBE byteWidth value)
  | Value.int value => some (wordToBytesBE byteWidth value)
  | _ => none

-- `widths` carries, per top-level argument, the packed byte width for a narrow
-- scalar (`0` means "use the type-directed packing", which is correct for
-- `bool`/`address`/`bytesN`/`bytes`/`string`/arrays/`uint256`/`int256`). Array
-- and struct elements are intentionally left to the 32-byte-padded path, which
-- matches solc's packed encoding of aggregates.
def abiEncodePackedValues? :
    List Nat -> List Ty -> List Value -> Option (List Byte)
  | [], [], [] => some []
  | width :: widths, ty :: tys, value :: values => do
      let head ←
        if width == 0 then
          abiEncodePackedValue? ty value
        else
          abiEncodePackedNarrowScalar? width value
      let tail ← abiEncodePackedValues? widths tys values
      some (head ++ tail)
  | _, _, _ => none

inductive UnaryOp where
  | bitNot : UnaryOp
  | logicalNot : UnaryOp
  | neg : UnaryOp
  deriving Repr

inductive BinaryOp where
  | add : BinaryOp
  | sub : BinaryOp
  | mul : BinaryOp
  | div : BinaryOp
  | mod : BinaryOp
  | exp : BinaryOp
  | bitAnd : BinaryOp
  | bitOr : BinaryOp
  | bitXor : BinaryOp
  | shl : BinaryOp
  | shr : BinaryOp
  | sar : BinaryOp
  | lt : BinaryOp
  | gt : BinaryOp
  | le : BinaryOp
  | ge : BinaryOp
  | eq : BinaryOp
  | ne : BinaryOp
  | boolAnd : BinaryOp
  | boolOr : BinaryOp
  deriving Repr

inductive ValueCleanup where
  | none
  | uint : Nat -> ValueCleanup
  | int : Nat -> ValueCleanup
  deriving Repr

def ValueCleanup.apply (checked : Bool) (cleanup : ValueCleanup)
    (value : Value) : Except RevertData Value :=
  match cleanup with
  | ValueCleanup.none => Except.ok value
  | ValueCleanup.uint bits => uintCleanup? checked bits value
  | ValueCleanup.int bits => intCleanup? checked bits value

def AbiCleanups.acceptOrUnspecified
    (cleanups : List AbiCleanup) (values : List Value) : Bool :=
  cleanups.isEmpty || AbiCleanups.accept cleanups values

mutual

def AbiCleanup.lazyValue : AbiCleanup -> Value -> Option Value
  | AbiCleanup.none, value => some value
  | AbiCleanup.fixedArray size cleanup, Value.fixedArray values =>
      if values.length == size then
        match AbiCleanup.lazyValues cleanup values with
        | some values => some (Value.fixedArray values)
        | none => none
      else
        none
  | AbiCleanup.dynamicArray cleanup, Value.dynamicArray values =>
      match AbiCleanup.lazyValues cleanup values with
      | some values => some (Value.dynamicArray values)
      | none => none
  | AbiCleanup.tuple cleanups, Value.tuple values =>
      match AbiCleanups.lazyValues cleanups values with
      | some values => some (Value.tuple values)
      | none => none
  | cleanup, value => some (Value.abiLazy cleanup value)

def AbiCleanup.lazyValues (cleanup : AbiCleanup) :
    List Value -> Option (List Value)
  | [] => some []
  | value :: rest => do
      let value ← cleanup.lazyValue value
      let rest ← cleanup.lazyValues rest
      some (value :: rest)

def AbiCleanups.lazyValues : List AbiCleanup -> List Value ->
    Option (List Value)
  | [], [] => some []
  | cleanup :: cleanups, value :: values => do
      let value ← cleanup.lazyValue value
      let values ← AbiCleanups.lazyValues cleanups values
      some (value :: values)
  | _, _ => none

end

def AbiCleanup.lazyParamValue : AbiCleanup -> Value -> Option Value
  | AbiCleanup.none, value => some value
  | AbiCleanup.fixedArray size cleanup, Value.fixedArray values =>
      if values.length == size then
        match AbiCleanup.lazyValues cleanup values with
        | some values => some (Value.fixedArray values)
        | Option.none => Option.none
      else
        Option.none
  | AbiCleanup.dynamicArray cleanup, Value.dynamicArray values =>
      match AbiCleanup.lazyValues cleanup values with
      | some values => some (Value.dynamicArray values)
      | Option.none => Option.none
  | AbiCleanup.tuple cleanups, Value.tuple values =>
      match AbiCleanups.lazyValues cleanups values with
      | some values => some (Value.tuple values)
      | Option.none => Option.none
  | cleanup, value =>
      if cleanup.accepts value then
        some value
      else
        Option.none

def AbiCleanups.lazyParamValues : List AbiCleanup -> List Value ->
    Option (List Value)
  | [], [] => some []
  | cleanup :: cleanups, value :: values => do
      let value ← cleanup.lazyParamValue value
      let values ← AbiCleanups.lazyParamValues cleanups values
      some (value :: values)
  | _, _ => none

inductive Expr where
  | word : Word -> Expr
  | intWord : Word -> Expr
  | byteArray : List Byte -> Expr
  | contractAddress : String -> Expr
  | contractCreationCode : String -> Expr
  | contractRuntimeCode : String -> Expr
  | calldata : Expr
  | msgSig : Expr
  | caller : Expr
  | callValue : Expr
  | self : Expr
  | env : EnvWord -> Expr
  | envLookup : EnvLookup -> Expr -> Expr
  | envBytesLookup : EnvBytesLookup -> Expr -> Expr
  | var : String -> Expr
  | immutable : String -> Expr
  | storage : String -> Expr
  | storageBytes : String -> Expr
  | storageIndex : String -> Expr -> Expr
  | storagePath : String -> List Expr -> Expr
  | externalFunctionValue : Expr -> Word -> Expr
  | externalFunctionSelector : Expr -> Expr
  | externalFunctionAddress : Expr -> Expr
  | unary : UnaryOp -> Expr -> Expr
  | preIncrement : Expr -> Expr
  | preDecrement : Expr -> Expr
  | postIncrement : Expr -> Expr
  | postDecrement : Expr -> Expr
  | incDecCleanup : Expr -> BinaryOp -> Bool -> ValueCleanup -> Expr
  | assignExpr : Expr -> Expr -> Expr
  | assignOpExpr : Expr -> BinaryOp -> Expr -> Expr
  | assignOpCleanupExpr : Expr -> BinaryOp -> Expr -> ValueCleanup -> Expr
  | binary : BinaryOp -> Expr -> Expr -> Expr
  | addMod : Expr -> Expr -> Expr -> Expr
  | mulMod : Expr -> Expr -> Expr -> Expr
  | concatBytes : List Expr -> Expr
  | fixedBytesIndex : Nat -> Expr -> Expr -> Expr
  | fixedBytesCast : Nat -> Nat -> Expr -> Expr
  | fixedBytesFromBytes : Nat -> Expr -> Expr
  | uintCast : Nat -> Expr -> Expr
  | intCast : Nat -> Expr -> Expr
  | uintCleanup : Nat -> Expr -> Expr
  | intCleanup : Nat -> Expr -> Expr
  | keccak256 : Expr -> Expr
  | erc7201 : Expr -> Expr
  | tuple : List Expr -> Expr
  | abiEncode : List Ty -> List Expr -> Expr
  | abiEncodeWithSelector : Expr -> List Ty -> List Expr -> Expr
  | abiEncodePacked : List Nat -> List Ty -> List Expr -> Expr
  | abiDecode : List Ty -> List AbiCleanup -> Expr -> Expr
  | lowLevelCall :
      LowLevelCallKind -> Expr -> Expr -> Expr -> Option Expr -> Bool -> Expr
  | contractCreate : String -> Expr -> Expr -> Option Expr -> Expr
  | newBytes : Expr -> Expr
  | newDynamicArray : Ty -> Expr -> Expr
  | externalHash : ExternalHashKind -> Expr -> Expr
  | ecrecover : Expr -> Expr -> Expr -> Expr -> Expr
  | enumFromUInt : Word -> Expr -> Expr
  | ternary : Expr -> Expr -> Expr -> Expr
  | fixedArray : List Expr -> Expr
  | length : Expr -> Expr
  | index : Expr -> Expr -> Expr
  | slice : Expr -> Option Expr -> Option Expr -> Expr
  deriving Repr

def Expr.hasStorageRoot : Expr -> Bool
  | Expr.storage _ => true
  | Expr.storageIndex _ _ => true
  | Expr.storagePath _ _ => true
  | Expr.index base _ => Expr.hasStorageRoot base
  | _ => false

def Expr.hasStorageRefRoot (runtime : Runtime) : Expr -> Bool
  | Expr.var name => runtime.lookupStoragePathRef? name |>.isSome
  | Expr.index base _ => Expr.hasStorageRefRoot runtime base
  | _ => false

inductive LValue where
  | var : String -> LValue
  | immutable : String -> LValue
  | storage : String -> LValue
  | storageIndex : String -> Expr -> LValue
  | index : LValue -> Expr -> LValue
  deriving Repr

def LValue.toExpr : LValue -> Expr
  | LValue.var name => Expr.var name
  | LValue.immutable name => Expr.immutable name
  | LValue.storage name => Expr.storage name
  | LValue.storageIndex name idx => Expr.storageIndex name idx
  | LValue.index base idx => Expr.index base.toExpr idx

def Expr.toLValue? : Expr -> Option LValue
  | Expr.var name => some (LValue.var name)
  | Expr.immutable name => some (LValue.immutable name)
  | Expr.storage name => some (LValue.storage name)
  | Expr.storageIndex name idx => some (LValue.storageIndex name idx)
  | Expr.index base idx => do
      let baseTarget ← Expr.toLValue? base
      some (LValue.index baseTarget idx)
  | _ => none

def checkedAdd (checked : Bool) (lhs rhs : Word) :
    Except RevertData Word :=
  let raw := SolidCore.Solidity.Shared.norm lhs + SolidCore.Solidity.Shared.norm rhs
  if checked && (wordModulus <= raw) then
    Except.error RevertData.overflow
  else
    Except.ok (SolidCore.Solidity.Shared.addWord lhs rhs)

def checkedSub (checked : Bool) (lhs rhs : Word) :
    Except RevertData Word :=
  if checked && (SolidCore.Solidity.Shared.norm lhs < SolidCore.Solidity.Shared.norm rhs) then
    Except.error RevertData.overflow
  else
    Except.ok (SolidCore.Solidity.Shared.subWord lhs rhs)

def checkedMul (checked : Bool) (lhs rhs : Word) :
    Except RevertData Word :=
  let raw := SolidCore.Solidity.Shared.norm lhs * SolidCore.Solidity.Shared.norm rhs
  if checked && (wordModulus <= raw) then
    Except.error RevertData.overflow
  else
    Except.ok (SolidCore.Solidity.Shared.mulWord lhs rhs)

def checkedDiv (_checked : Bool) (lhs rhs : Word) :
    Except RevertData Word :=
  if SolidCore.Solidity.Shared.norm rhs = 0 then
    Except.error RevertData.divByZero
  else
    Except.ok (SolidCore.Solidity.Shared.divWord lhs rhs)

def checkedMod (_checked : Bool) (lhs rhs : Word) :
    Except RevertData Word :=
  if SolidCore.Solidity.Shared.norm rhs = 0 then
    Except.error RevertData.divByZero
  else
    Except.ok (SolidCore.Solidity.Shared.modWord lhs rhs)

def checkedExpLoop (checked : Bool) (base : Word) :
    Nat -> Word -> Except RevertData Word
  | 0, acc => Except.ok (SolidCore.Solidity.Shared.norm acc)
  | remaining + 1, acc =>
      let raw := SolidCore.Solidity.Shared.norm acc * SolidCore.Solidity.Shared.norm base
      if checked && wordModulus <= raw then
        Except.error RevertData.overflow
      else
        checkedExpLoop checked base remaining (normWord raw)

def checkedExp (checked : Bool) (base exponent : Word) :
    Except RevertData Word :=
  checkedExpLoop checked base (SolidCore.Solidity.Shared.norm exponent) 1

def signedIntMin : Int :=
  -Int.ofNat SolidCore.Solidity.Shared.halfWordModulus

def signedIntMax : Int :=
  Int.ofNat SolidCore.Solidity.Shared.halfWordModulus - 1

def signedInt256InRange (value : Int) : Bool :=
  decide (signedIntMin <= value) && decide (value <= signedIntMax)

def checkedSignedWord (checked : Bool) (value : Int) (wrapped : Word) :
    Except RevertData Word :=
  if checked && !(signedInt256InRange value) then
    Except.error RevertData.overflow
  else if checked then
    Except.ok (SolidCore.Solidity.Shared.signedToWord value)
  else
    Except.ok wrapped

def checkedSignedAdd (checked : Bool) (lhs rhs : Word) :
    Except RevertData Word :=
  checkedSignedWord checked
    (SolidCore.Solidity.Shared.signedValue lhs + SolidCore.Solidity.Shared.signedValue rhs)
    (SolidCore.Solidity.Shared.addWord lhs rhs)

def checkedSignedSub (checked : Bool) (lhs rhs : Word) :
    Except RevertData Word :=
  checkedSignedWord checked
    (SolidCore.Solidity.Shared.signedValue lhs - SolidCore.Solidity.Shared.signedValue rhs)
    (SolidCore.Solidity.Shared.subWord lhs rhs)

def checkedSignedMul (checked : Bool) (lhs rhs : Word) :
    Except RevertData Word :=
  checkedSignedWord checked
    (SolidCore.Solidity.Shared.signedValue lhs * SolidCore.Solidity.Shared.signedValue rhs)
    (SolidCore.Solidity.Shared.mulWord lhs rhs)

def checkedSignedNeg (checked : Bool) (value : Word) :
    Except RevertData Word :=
  checkedSignedWord checked (-(SolidCore.Solidity.Shared.signedValue value))
    (SolidCore.Solidity.Shared.subWord 0 value)

def isSignedMinWord (value : Word) : Bool :=
  wordEq value SolidCore.Solidity.Shared.halfWordModulus

def isSignedNegOneWord (value : Word) : Bool :=
  wordEq value (wordModulus - 1)

def checkedSignedDiv (checked : Bool) (lhs rhs : Word) :
    Except RevertData Word :=
  if wordEq rhs 0 then
    Except.error RevertData.divByZero
  else if checked && isSignedMinWord lhs && isSignedNegOneWord rhs then
    Except.error RevertData.overflow
  else
    Except.ok (SolidCore.Solidity.Shared.sdivWord lhs rhs)

def checkedSignedMod (_checked : Bool) (lhs rhs : Word) :
    Except RevertData Word :=
  if wordEq rhs 0 then
    Except.error RevertData.divByZero
  else
    Except.ok (SolidCore.Solidity.Shared.smodWord lhs rhs)

-- Signed exponentiation with two's-complement wrapping. The exponent is a
-- non-negative magnitude (Solidity rejects negative exponents), so we iterate
-- it as a `Nat`. In checked mode each intermediate product is validated against
-- the int256 range (panic 0x11 on overflow); in unchecked mode the accumulator
-- wraps mod 2^256 through `signedToWord`. Narrow-type (`intN`) result overflow
-- is enforced by the enclosing `intCleanup` the importer inserts.
def checkedSignedExpLoop (checked : Bool) (base : Word) :
    Nat -> Word -> Except RevertData Word
  | 0, acc => Except.ok acc
  | remaining + 1, acc =>
      let product :=
        SolidCore.Solidity.Shared.signedValue acc *
          SolidCore.Solidity.Shared.signedValue base
      if checked && !(signedInt256InRange product) then
        Except.error RevertData.overflow
      else
        checkedSignedExpLoop checked base remaining
          (SolidCore.Solidity.Shared.signedToWord product)

def checkedSignedExp (checked : Bool) (base exponent : Word) :
    Except RevertData Word :=
  checkedSignedExpLoop checked base
    (SolidCore.Solidity.Shared.norm exponent)
    (SolidCore.Solidity.Shared.signedToWord 1)

def checkedAddMod (lhs rhs modulus : Word) :
    Except RevertData Word :=
  if wordEq modulus 0 then
    Except.error RevertData.divByZero
  else
    Except.ok (SolidCore.Solidity.Shared.addmodWord lhs rhs modulus)

def checkedMulMod (lhs rhs modulus : Word) :
    Except RevertData Word :=
  if wordEq modulus 0 then
    Except.error RevertData.divByZero
  else
    Except.ok (SolidCore.Solidity.Shared.mulmodWord lhs rhs modulus)

def BinaryOp.applyWord
    (checked : Bool) (op : BinaryOp) (lhs rhs : Word) :
    Except RevertData Word :=
  match op with
  | BinaryOp.add => checkedAdd checked lhs rhs
  | BinaryOp.sub => checkedSub checked lhs rhs
  | BinaryOp.mul => checkedMul checked lhs rhs
  | BinaryOp.div => checkedDiv checked lhs rhs
  | BinaryOp.mod => checkedMod checked lhs rhs
  | BinaryOp.exp => checkedExp checked lhs rhs
  | BinaryOp.bitAnd => Except.ok (SolidCore.Solidity.Shared.andWord lhs rhs)
  | BinaryOp.bitOr => Except.ok (SolidCore.Solidity.Shared.orWord lhs rhs)
  | BinaryOp.bitXor => Except.ok (SolidCore.Solidity.Shared.xorWord lhs rhs)
  | BinaryOp.shl => Except.ok (SolidCore.Solidity.Shared.shlWord rhs lhs)
  | BinaryOp.shr => Except.ok (SolidCore.Solidity.Shared.shrWord rhs lhs)
  | BinaryOp.sar => Except.ok (SolidCore.Solidity.Shared.sarWord rhs lhs)
  | BinaryOp.lt => Except.ok (SolidCore.Solidity.Shared.ltWord lhs rhs)
  | BinaryOp.gt => Except.ok (SolidCore.Solidity.Shared.gtWord lhs rhs)
  | BinaryOp.le =>
      Except.ok (boolWord (!(wordTruthy (SolidCore.Solidity.Shared.gtWord lhs rhs))))
  | BinaryOp.ge =>
      Except.ok (boolWord (!(wordTruthy (SolidCore.Solidity.Shared.ltWord lhs rhs))))
  | BinaryOp.eq => Except.ok (boolWord (wordEq lhs rhs))
  | BinaryOp.ne => Except.ok (boolWord (!(wordEq lhs rhs)))
  | BinaryOp.boolAnd => Except.ok (boolWord (wordTruthy lhs && wordTruthy rhs))
  | BinaryOp.boolOr => Except.ok (boolWord (wordTruthy lhs || wordTruthy rhs))

def BinaryOp.applySignedWord
    (checked : Bool) (op : BinaryOp) (lhs rhs : Word) :
    Except RevertData Value :=
  match op with
  | BinaryOp.add => do
      let value ← checkedSignedAdd checked lhs rhs
      Except.ok (Value.int value)
  | BinaryOp.sub => do
      let value ← checkedSignedSub checked lhs rhs
      Except.ok (Value.int value)
  | BinaryOp.mul => do
      let value ← checkedSignedMul checked lhs rhs
      Except.ok (Value.int value)
  | BinaryOp.div => do
      let value ← checkedSignedDiv checked lhs rhs
      Except.ok (Value.int value)
  | BinaryOp.mod => do
      let value ← checkedSignedMod checked lhs rhs
      Except.ok (Value.int value)
  | BinaryOp.exp => do
      let value ← checkedSignedExp checked lhs rhs
      Except.ok (Value.int value)
  | BinaryOp.bitAnd =>
      Except.ok (Value.int (SolidCore.Solidity.Shared.andWord lhs rhs))
  | BinaryOp.bitOr =>
      Except.ok (Value.int (SolidCore.Solidity.Shared.orWord lhs rhs))
  | BinaryOp.bitXor =>
      Except.ok (Value.int (SolidCore.Solidity.Shared.xorWord lhs rhs))
  | BinaryOp.shl =>
      Except.ok (Value.int (SolidCore.Solidity.Shared.shlWord rhs lhs))
  | BinaryOp.shr =>
      Except.ok (Value.int (SolidCore.Solidity.Shared.sarWord rhs lhs))
  | BinaryOp.sar =>
      Except.ok (Value.int (SolidCore.Solidity.Shared.sarWord rhs lhs))
  | BinaryOp.lt => Except.ok (Value.word (SolidCore.Solidity.Shared.sltWord lhs rhs))
  | BinaryOp.gt => Except.ok (Value.word (SolidCore.Solidity.Shared.sgtWord lhs rhs))
  | BinaryOp.le =>
      Except.ok
        (Value.word
          (boolWord
            (!(wordTruthy (SolidCore.Solidity.Shared.sgtWord lhs rhs)))))
  | BinaryOp.ge =>
      Except.ok
        (Value.word
          (boolWord
            (!(wordTruthy (SolidCore.Solidity.Shared.sltWord lhs rhs)))))
  | BinaryOp.eq => Except.ok (Value.word (boolWord (wordEq lhs rhs)))
  | BinaryOp.ne => Except.ok (Value.word (boolWord (!(wordEq lhs rhs))))
  | _ => Except.error RevertData.typeMismatch

def BinaryOp.apply
    (checked : Bool) (op : BinaryOp) (lhs rhs : Value) :
    Except RevertData Value :=
  match op with
  | BinaryOp.eq =>
      match lhs, rhs with
      | Value.word lhsWord, Value.word rhsWord =>
          Except.ok (Value.word (boolWord (wordEq lhsWord rhsWord)))
      | Value.int lhsWord, Value.int rhsWord =>
          Except.ok (Value.word (boolWord (wordEq lhsWord rhsWord)))
      | Value.externalFunction lhsAddr lhsSelector,
          Value.externalFunction rhsAddr rhsSelector =>
          Except.ok
            (Value.word
              (boolWord
                (wordEq lhsAddr rhsAddr &&
                  wordEq lhsSelector rhsSelector)))
      | _, _ => Except.error RevertData.typeMismatch
  | BinaryOp.ne =>
      match lhs, rhs with
      | Value.word lhsWord, Value.word rhsWord =>
          Except.ok (Value.word (boolWord (!(wordEq lhsWord rhsWord))))
      | Value.int lhsWord, Value.int rhsWord =>
          Except.ok (Value.word (boolWord (!(wordEq lhsWord rhsWord))))
      | Value.externalFunction lhsAddr lhsSelector,
          Value.externalFunction rhsAddr rhsSelector =>
          Except.ok
            (Value.word
              (boolWord
                (!(wordEq lhsAddr rhsAddr &&
                  wordEq lhsSelector rhsSelector))))
      | _, _ => Except.error RevertData.typeMismatch
  | _ =>
      match lhs, rhs with
      | Value.word lhsWord, Value.word rhsWord => do
          let value ← op.applyWord checked lhsWord rhsWord
          Except.ok (Value.word value)
      | Value.int lhsWord, Value.int rhsWord =>
          op.applySignedWord checked lhsWord rhsWord
      | Value.int lhsWord, Value.word rhsWord =>
          match op with
          | BinaryOp.shl =>
              Except.ok (Value.int (SolidCore.Solidity.Shared.shlWord rhsWord lhsWord))
          | BinaryOp.shr =>
              Except.ok (Value.int (SolidCore.Solidity.Shared.sarWord rhsWord lhsWord))
          | BinaryOp.sar =>
              Except.ok (Value.int (SolidCore.Solidity.Shared.sarWord rhsWord lhsWord))
          | BinaryOp.exp => do
              let value ← checkedSignedExp checked lhsWord rhsWord
              Except.ok (Value.int value)
          | _ => Except.error RevertData.typeMismatch
      | _, _ => Except.error RevertData.typeMismatch

inductive BinaryArithmeticOperandMode where
  | unsignedWord
  | signedWord
  | signedAndWord
  | unsupported
  deriving Repr, BEq

def BinaryArithmeticOperandMode.ofValues
    (lhs rhs : Value) : BinaryArithmeticOperandMode :=
  match lhs, rhs with
  | Value.word _, Value.word _ =>
      BinaryArithmeticOperandMode.unsignedWord
  | Value.int _, Value.int _ =>
      BinaryArithmeticOperandMode.signedWord
  | Value.int _, Value.word _ =>
      BinaryArithmeticOperandMode.signedAndWord
  | _, _ =>
      BinaryArithmeticOperandMode.unsupported

def UnaryOp.apply (checked : Bool) (op : UnaryOp) (value : Value) :
    Except RevertData Value :=
  match op with
  | UnaryOp.bitNot =>
      match value with
      | Value.word word =>
          Except.ok (Value.word (SolidCore.Solidity.Shared.notWord word))
      | Value.int word =>
          Except.ok (Value.int (SolidCore.Solidity.Shared.notWord word))
      | _ => Except.error RevertData.typeMismatch
  | UnaryOp.logicalNot =>
      match value with
      | Value.word word =>
          Except.ok (Value.word (boolWord (!(wordTruthy word))))
      | _ => Except.error RevertData.typeMismatch
  | UnaryOp.neg =>
      match value with
      | Value.int word => do
          let negated ← checkedSignedNeg checked word
          Except.ok (Value.int negated)
      | Value.word word =>
          if checked && wordTruthy word then
            Except.error RevertData.overflow
          else
            Except.ok (Value.word (SolidCore.Solidity.Shared.subWord 0 word))
      | _ => Except.error RevertData.typeMismatch

def enumFromUIntValue (maxValue : Word) : Value -> Except RevertData Value
  | Value.word word =>
      if SolidCore.Solidity.Shared.norm word <= SolidCore.Solidity.Shared.norm maxValue then
        Except.ok (Value.word word)
      else
        Except.error RevertData.enumConversion
  | Value.int word =>
      let signed := SolidCore.Solidity.Shared.signedValue word
      if signed < 0 then
        Except.error RevertData.enumConversion
      else if Int.ofNat (SolidCore.Solidity.Shared.norm maxValue) < signed then
        Except.error RevertData.enumConversion
      else
        Except.ok (Value.word word)
  | _ => Except.error RevertData.typeMismatch


def Value.oneLike? : Value -> Except RevertData Value
  | Value.word _ => Except.ok (Value.word 1)
  | Value.int _ => Except.ok (Value.int 1)
  | _ => Except.error RevertData.typeMismatch

inductive ResolvedLValue where
  | local : String -> ResolvedLValue
  | memoryCell : Nat -> ResolvedLValue
  | immutable : String -> ResolvedLValue
  | storageField : String -> ResolvedLValue
  | storageIndex : String -> Value -> ResolvedLValue
  | storagePath : String -> List Value -> ResolvedLValue
  | valueIndex : ResolvedLValue -> Word -> ResolvedLValue
  deriving Repr

def ResolvedLValue.asStoragePath? :
    ResolvedLValue -> Option (String × List Value)
  | ResolvedLValue.storageField name => some (name, [])
  | ResolvedLValue.storageIndex name index => some (name, [index])
  | ResolvedLValue.storagePath name indexes => some (name, indexes)
  | _ => none

mutual

def ResolvedLValue.readRaw (context : Context) (runtime : Runtime) :
    ResolvedLValue -> Except RevertData Value
  | ResolvedLValue.local name =>
      match runtime.lookupLocal? name with
      | some value => Except.ok value
      | none => Except.error RevertData.typeMismatch
  | ResolvedLValue.memoryCell id =>
      match runtime.loadMemory? id with
      | some value => Except.ok value
      | none => Except.error RevertData.typeMismatch
  | ResolvedLValue.immutable name =>
      runtime.loadImmutableField context name
  | ResolvedLValue.storageField name =>
      runtime.loadStorageField context name
  | ResolvedLValue.storageIndex name index =>
      runtime.loadStorageIndex context name index
  | ResolvedLValue.storagePath name indexes =>
      runtime.loadStoragePath context name indexes
  | ResolvedLValue.valueIndex base index => do
      let baseValue ← base.read context runtime
      let baseValue ← runtime.derefMemoryValue baseValue
      baseValue.index? index

def ResolvedLValue.read (context : Context) (runtime : Runtime) :
    ResolvedLValue -> Except RevertData Value
  | target => do
      let value ← target.readRaw context runtime
      runtime.derefMemoryValue value

end

def ResolvedLValue.writeContainer (context : Context) (runtime : Runtime)
    (target : ResolvedLValue) (value : Value) :
    Except RevertData Runtime :=
  match target with
  | ResolvedLValue.local name =>
      match runtime.lookupMemoryRef? name with
      | some id =>
          match runtime.storeMemory? id value with
          | some updated => Except.ok updated
              | none => Except.error RevertData.typeMismatch
      | none =>
          match runtime.assignLocal? name value with
          | some updated => Except.ok updated
          | none => Except.error RevertData.typeMismatch
  | ResolvedLValue.memoryCell id =>
      match runtime.storeMemory? id value with
      | some updated => Except.ok updated
      | none => Except.error RevertData.typeMismatch
  | ResolvedLValue.immutable name =>
      runtime.storeImmutableField context name value
  | ResolvedLValue.storageField name =>
      runtime.storeStorageFieldWithDeepClear context name value
  | ResolvedLValue.storageIndex name index =>
      runtime.storeStorageIndexWithDeepClear context name index value
  | ResolvedLValue.storagePath name indexes =>
      runtime.storeStoragePathWithDeepClear context name indexes value
  | ResolvedLValue.valueIndex base index => do
      let baseValue ← base.read context runtime
      let baseValue ← runtime.derefMemoryValue baseValue
      let (runtime', storedValue) := runtime.memoryStoreValue value
      let updatedBase ← baseValue.setIndex? index storedValue
      base.writeContainer context runtime' updatedBase

def ResolvedLValue.write (context : Context) (runtime : Runtime)
    (target : ResolvedLValue) (value : Value) :
    Except RevertData Runtime :=
  match target with
  | ResolvedLValue.local name =>
      match runtime.assignLocal? name value with
      | some updated => Except.ok updated
      | none => Except.error RevertData.typeMismatch
  | ResolvedLValue.memoryCell id =>
      match runtime.storeMemory? id value with
      | some updated => Except.ok updated
      | none => Except.error RevertData.typeMismatch
  | ResolvedLValue.immutable name =>
      runtime.storeImmutableField context name value
  | ResolvedLValue.storageField name =>
      runtime.storeStorageFieldWithDeepClear context name value
  | ResolvedLValue.storageIndex name index =>
      runtime.storeStorageIndexWithDeepClear context name index value
  | ResolvedLValue.storagePath name indexes =>
      runtime.storeStoragePathWithDeepClear context name indexes value
  | ResolvedLValue.valueIndex base index => do
      let baseValue ← base.read context runtime
      let baseValue ← runtime.derefMemoryValue baseValue
      let (runtime', storedValue) := runtime.memoryStoreValue value
      let updatedBase ← baseValue.setIndex? index storedValue
      base.writeContainer context runtime' updatedBase

def ResolvedLValue.delete (context : Context) (runtime : Runtime) :
    ResolvedLValue -> Except RevertData Runtime
  | ResolvedLValue.local name =>
      match runtime.lookupLocal? name with
      | some (Value.memoryRef id) => do
          let value ←
            match runtime.loadMemory? id with
            | some value => Except.ok value
            | none => Except.error RevertData.typeMismatch
          let (runtime', defaultValue) :=
            runtime.memoryStoreValue value.defaultLike
          match runtime'.assignLocal? name defaultValue with
          | some updated => Except.ok updated
          | none => Except.error RevertData.typeMismatch
      | some value =>
          match runtime.assignLocal? name value.defaultLike with
          | some updated => Except.ok updated
          | none => Except.error RevertData.typeMismatch
      | none => Except.error RevertData.typeMismatch
  | ResolvedLValue.memoryCell id =>
      match runtime.loadMemory? id with
      | some value =>
          match runtime.storeMemory? id value.defaultLike with
          | some updated => Except.ok updated
          | none => Except.error RevertData.typeMismatch
      | none => Except.error RevertData.typeMismatch
  | ResolvedLValue.immutable name => do
      let value ← runtime.loadImmutableField context name
      runtime.storeImmutableField context name value.defaultLike
  | ResolvedLValue.storageField name =>
      runtime.deleteStorageField context name
  | ResolvedLValue.storageIndex name index =>
      runtime.deleteStorageIndex context name index
  | ResolvedLValue.storagePath name indexes =>
      runtime.deleteStoragePath context name indexes
  | ResolvedLValue.valueIndex base index => do
      let baseValue ← base.read context runtime
      let baseValue ← runtime.derefMemoryValue baseValue
      let oldValue ← baseValue.index? index
      let updatedBase ← baseValue.setIndex? index oldValue.defaultLike
      base.writeContainer context runtime updatedBase

def ResolvedLValue.applyIncDec (context : Context) (runtime : Runtime)
    (target : ResolvedLValue) (op : BinaryOp) (returnOld : Bool) :
    Except RevertData (Value × Runtime) := do
  let oldValue ← target.read context runtime
  let one ← oldValue.oneLike?
  let newValue ← BinaryOp.apply context.checked op oldValue one
  let updated ← target.write context runtime newValue
  if returnOld then
    Except.ok (oldValue, updated)
  else
    Except.ok (newValue, updated)

def ResolvedLValue.applyIncDecCleanup (context : Context)
    (runtime : Runtime) (target : ResolvedLValue) (op : BinaryOp)
    (returnOld : Bool) (cleanup : ValueCleanup) :
    Except RevertData (Value × Runtime) := do
  let oldValue ← target.read context runtime
  let one ← oldValue.oneLike?
  let newValue ← BinaryOp.apply context.checked op oldValue one
  let cleaned ← cleanup.apply context.checked newValue
  let updated ← target.write context runtime cleaned
  if returnOld then
    Except.ok (oldValue, updated)
  else
    Except.ok (cleaned, updated)


mutual

def Expr.orderFuel : Expr -> Nat
  | Expr.word _ => 1
  | Expr.intWord _ => 1
  | Expr.byteArray _ => 1
  | Expr.contractAddress _ => 1
  | Expr.contractCreationCode _ => 1
  | Expr.contractRuntimeCode _ => 1
  | Expr.calldata => 1
  | Expr.msgSig => 1
  | Expr.caller => 1
  | Expr.callValue => 1
  | Expr.self => 1
  | Expr.env _ => 1
  | Expr.envLookup _ expr => Expr.orderFuel expr + 1
  | Expr.envBytesLookup _ expr => Expr.orderFuel expr + 1
  | Expr.var _ => 1
  | Expr.immutable _ => 1
  | Expr.storage _ => 1
  | Expr.storageBytes _ => 1
  | Expr.storageIndex _ idx => Expr.orderFuel idx + 1
  | Expr.storagePath _ indexes => Expr.listEvalFuel indexes + 1
  | Expr.externalFunctionValue addressExpr _ => Expr.orderFuel addressExpr + 1
  | Expr.externalFunctionSelector expr => Expr.orderFuel expr + 1
  | Expr.externalFunctionAddress expr => Expr.orderFuel expr + 1
  | Expr.unary _ expr => Expr.orderFuel expr + 1
  | Expr.preIncrement target => Expr.orderFuel target + 1
  | Expr.preDecrement target => Expr.orderFuel target + 1
  | Expr.postIncrement target => Expr.orderFuel target + 1
  | Expr.postDecrement target => Expr.orderFuel target + 1
  | Expr.incDecCleanup target _ _ _ => Expr.orderFuel target + 1
  | Expr.assignExpr target rhs =>
      Expr.orderFuel target + Expr.orderFuel rhs + 1
  | Expr.assignOpExpr target _ rhs =>
      Expr.orderFuel target + Expr.orderFuel rhs + 1
  | Expr.assignOpCleanupExpr target _ rhs _ =>
      Expr.orderFuel target + Expr.orderFuel rhs + 1
  | Expr.binary _ lhs rhs =>
      Expr.orderFuel lhs + Expr.orderFuel rhs + 1
  | Expr.addMod lhs rhs modulus =>
      Expr.orderFuel lhs + Expr.orderFuel rhs +
        Expr.orderFuel modulus + 1
  | Expr.mulMod lhs rhs modulus =>
      Expr.orderFuel lhs + Expr.orderFuel rhs +
        Expr.orderFuel modulus + 1
  | Expr.concatBytes exprs => Expr.listEvalFuel exprs + 1
  | Expr.fixedBytesIndex _ base idx =>
      Expr.orderFuel base + Expr.orderFuel idx + 1
  | Expr.fixedBytesCast _ _ expr => Expr.orderFuel expr + 1
  | Expr.fixedBytesFromBytes _ expr => Expr.orderFuel expr + 1
  | Expr.uintCast _ expr => Expr.orderFuel expr + 1
  | Expr.intCast _ expr => Expr.orderFuel expr + 1
  | Expr.uintCleanup _ expr => Expr.orderFuel expr + 1
  | Expr.intCleanup _ expr => Expr.orderFuel expr + 1
  | Expr.keccak256 expr => Expr.orderFuel expr + 1
  | Expr.erc7201 expr => Expr.orderFuel expr + 1
  | Expr.tuple exprs => Expr.listEvalFuel exprs + 1
  | Expr.abiEncode _ exprs => Expr.listEvalFuel exprs + 1
  | Expr.abiEncodeWithSelector selectorExpr _ exprs =>
      Expr.orderFuel selectorExpr + Expr.listEvalFuel exprs + 1
  | Expr.abiEncodePacked _ _ exprs => Expr.listEvalFuel exprs + 1
  | Expr.abiDecode _ _ expr => Expr.orderFuel expr + 1
  | Expr.lowLevelCall _ targetExpr calldataExpr valueExpr gas? _ =>
      Expr.orderFuel targetExpr + Expr.orderFuel calldataExpr +
        Expr.orderFuel valueExpr +
          (match gas? with
          | some gas => Expr.orderFuel gas
          | none => 0) + 1
  | Expr.contractCreate _ args value salt? =>
      Expr.orderFuel args + Expr.orderFuel value +
        (match salt? with
        | some salt => Expr.orderFuel salt
        | none => 0) + 1
  | Expr.newBytes expr => Expr.orderFuel expr + 1
  | Expr.newDynamicArray _ expr => Expr.orderFuel expr + 1
  | Expr.externalHash _ expr => Expr.orderFuel expr + 1
  | Expr.ecrecover digest v r s =>
      Expr.orderFuel digest + Expr.orderFuel v +
        Expr.orderFuel r + Expr.orderFuel s + 1
  | Expr.enumFromUInt _ expr => Expr.orderFuel expr + 1
  | Expr.ternary cond thenExpr elseExpr =>
      Expr.orderFuel cond + Expr.orderFuel thenExpr +
        Expr.orderFuel elseExpr + 1
  | Expr.fixedArray exprs => Expr.listEvalFuel exprs + 1
  | Expr.length expr => Expr.orderFuel expr + 1
  | Expr.index base idx => Expr.orderFuel base + Expr.orderFuel idx + 1
  | Expr.slice base start stop =>
      Expr.orderFuel base +
        (match start with
        | some expr => Expr.orderFuel expr
        | none => 0) +
        (match stop with
        | some expr => Expr.orderFuel expr
        | none => 0) + 1

def Expr.listEvalFuel : List Expr -> Nat
  | [] => 1
  | expr :: rest => Expr.orderFuel expr + Expr.listEvalFuel rest + 1

end

mutual

def Expr.evalWithRuntimeOrderFuel (fuel : Nat) (order : ChildEvalOrder)
    (context : Context) : Runtime -> Expr ->
    SolI (Value × Runtime)
  | runtime, expr =>
      match fuel with
      | 0 => throw <| SolidityFailure.revert RevertData.typeMismatch
      | fuel + 1 =>
          match expr with
          | Expr.word value =>
              pure (Value.word (normWord value), runtime)
          | Expr.intWord value =>
              pure (Value.int (normWord value), runtime)
          | Expr.byteArray bytes =>
              pure (Value.bytes (bytes.map normByte), runtime)
          | Expr.contractAddress name =>
              pure
                ( Value.word
                    (SolidCore.Solidity.Shared.Call.namedWordAt
                      context.contractAddresses name)
                , runtime )
          | Expr.contractCreationCode name =>
              pure
                ( Value.bytes
                    (SolidCore.Solidity.Shared.Call.namedBytesAt
                      context.contractCreationCodes name)
                , runtime )
          | Expr.contractRuntimeCode name =>
              pure
                ( Value.bytes
                    (SolidCore.Solidity.Shared.Call.namedBytesAt
                      context.contractRuntimeCodes name)
                , runtime )
          | Expr.calldata =>
              pure (Value.bytes (context.calldata.map normByte), runtime)
          | Expr.msgSig =>
              pure
                (Value.word (calldataSelectorWord context.calldata), runtime)
          | Expr.caller =>
              pure (Value.word context.sender, runtime)
          | Expr.callValue =>
              pure (Value.word context.value, runtime)
          | Expr.self =>
              pure (Value.word context.self, runtime)
          | Expr.env which =>
              pure (Value.word (which.eval context), runtime)
          | Expr.envLookup which keyExpr => do
              let (keyValue, runtime') ←
                Expr.evalWithRuntimeOrderFuel fuel order context runtime keyExpr
              let key ← keyValue.expectWord
              pure (Value.word (which.eval context key), runtime')
          | Expr.envBytesLookup which keyExpr => do
              let (keyValue, runtime') ←
                Expr.evalWithRuntimeOrderFuel fuel order context runtime keyExpr
              let key ← keyValue.expectWord
              pure (Value.bytes (which.eval context key), runtime')
          | Expr.var name =>
              match runtime.lookupStoragePathRef? name with
              | some (target, indexes) => do
                  let value ←
                    runtime.loadStorageRefPathValue context target indexes
                  pure (value, runtime)
              | none =>
                  match runtime.lookupLocal? name with
                  | some value => do
                      let value ← runtime.derefMemoryValue value
                      pure (value, runtime)
                  | none => throw <| SolidityFailure.revert RevertData.typeMismatch
          | Expr.immutable name => do
              let value ← runtime.loadImmutableField context name
              pure (value, runtime)
          | Expr.storage name => do
              let value ← runtime.loadStorageField context name
              pure (value, runtime)
          | Expr.storageBytes name => do
              let value ← runtime.loadStorageByteStringField context name
              pure (value, runtime)
          | Expr.storageIndex name idx => do
              let (indexValue, runtime') ←
                Expr.evalWithRuntimeOrderFuel fuel order context runtime idx
              let value ← runtime'.loadStorageIndex context name indexValue
              pure (value, runtime')
          | Expr.storagePath name indexes => do
              let (indexValues, runtime') ←
                Expr.evalListWithRuntimeOrderFuel fuel order context runtime
                  indexes
              let value ← runtime'.loadStoragePath context name indexValues
              pure (value, runtime')
          | Expr.externalFunctionValue addressExpr selector => do
              let (value, runtime') ←
                Expr.evalWithRuntimeOrderFuel fuel order context runtime
                  addressExpr
              let addr ← value.expectWord
              pure (Value.externalFunction addr selector, runtime')
          | Expr.externalFunctionSelector expr => do
              let (value, runtime') ←
                Expr.evalWithRuntimeOrderFuel fuel order context runtime expr
              match value with
              | Value.externalFunction _ selector =>
                  pure (Value.word selector, runtime')
              | _ => throw <| SolidityFailure.revert RevertData.typeMismatch
          | Expr.externalFunctionAddress expr => do
              let (value, runtime') ←
                Expr.evalWithRuntimeOrderFuel fuel order context runtime expr
              match value with
              | Value.externalFunction addr _ =>
                  pure (Value.word addr, runtime')
              | _ => throw <| SolidityFailure.revert RevertData.typeMismatch
          | Expr.unary op expr => do
              let (value, runtime') ←
                Expr.evalWithRuntimeOrderFuel fuel order context runtime expr
              let result ← op.apply context.checked value
              pure (result, runtime')
          | Expr.preIncrement target => do
              let (resolved, runtime') ←
                Expr.resolveLValueWithRuntimeOrderFuel fuel order context
                  runtime target
              resolved.applyIncDec context runtime' BinaryOp.add false
          | Expr.preDecrement target => do
              let (resolved, runtime') ←
                Expr.resolveLValueWithRuntimeOrderFuel fuel order context
                  runtime target
              resolved.applyIncDec context runtime' BinaryOp.sub false
          | Expr.postIncrement target => do
              let (resolved, runtime') ←
                Expr.resolveLValueWithRuntimeOrderFuel fuel order context
                  runtime target
              resolved.applyIncDec context runtime' BinaryOp.add true
          | Expr.postDecrement target => do
              let (resolved, runtime') ←
                Expr.resolveLValueWithRuntimeOrderFuel fuel order context
                  runtime target
              resolved.applyIncDec context runtime' BinaryOp.sub true
          | Expr.incDecCleanup target op returnOld cleanup => do
              let (resolved, runtime') ←
                Expr.resolveLValueWithRuntimeOrderFuel fuel order context
                  runtime target
              resolved.applyIncDecCleanup context runtime' op returnOld cleanup
          | Expr.assignExpr target rhs => do
              let (resolved, value, runtime'') ←
                match order with
                | ChildEvalOrder.leftToRight => do
                    let (resolved, runtime') ←
                      Expr.resolveLValueWithRuntimeOrderFuel fuel order
                        context runtime target
                    let (value, runtime'') ←
                      Expr.evalWithRuntimeOrderFuel fuel order context
                        runtime' rhs
                    pure (resolved, value, runtime'')
                | ChildEvalOrder.rightToLeft => do
                    let (value, runtime') ←
                      Expr.evalWithRuntimeOrderFuel fuel order context
                        runtime rhs
                    let (resolved, runtime'') ←
                      Expr.resolveLValueWithRuntimeOrderFuel fuel order
                        context runtime' target
                    pure (resolved, value, runtime'')
              let updated ← resolved.write context runtime'' value
              pure (value, updated)
          | Expr.assignOpExpr target op rhs => do
              let (resolved, lhsValue, rhsValue, runtime'') ←
                match order with
                | ChildEvalOrder.leftToRight => do
                    let (resolved, runtime') ←
                      Expr.resolveLValueWithRuntimeOrderFuel fuel order
                        context runtime target
                    let lhsValue ← resolved.read context runtime'
                    let (rhsValue, runtime'') ←
                      Expr.evalWithRuntimeOrderFuel fuel order context
                        runtime' rhs
                    pure (resolved, lhsValue, rhsValue, runtime'')
                | ChildEvalOrder.rightToLeft => do
                    let (rhsValue, runtime') ←
                      Expr.evalWithRuntimeOrderFuel fuel order context
                        runtime rhs
                    let (resolved, runtime'') ←
                      Expr.resolveLValueWithRuntimeOrderFuel fuel order
                        context runtime' target
                    let lhsValue ← resolved.read context runtime''
                    pure (resolved, lhsValue, rhsValue, runtime'')
              let value ← BinaryOp.apply context.checked op lhsValue rhsValue
              let updated ← resolved.write context runtime'' value
              pure (value, updated)
          | Expr.assignOpCleanupExpr target op rhs cleanup => do
              let (resolved, lhsValue, rhsValue, runtime'') ←
                match order with
                | ChildEvalOrder.leftToRight => do
                    let (resolved, runtime') ←
                      Expr.resolveLValueWithRuntimeOrderFuel fuel order
                        context runtime target
                    let lhsValue ← resolved.read context runtime'
                    let (rhsValue, runtime'') ←
                      Expr.evalWithRuntimeOrderFuel fuel order context
                        runtime' rhs
                    pure (resolved, lhsValue, rhsValue, runtime'')
                | ChildEvalOrder.rightToLeft => do
                    let (rhsValue, runtime') ←
                      Expr.evalWithRuntimeOrderFuel fuel order context
                        runtime rhs
                    let (resolved, runtime'') ←
                      Expr.resolveLValueWithRuntimeOrderFuel fuel order
                        context runtime' target
                    let lhsValue ← resolved.read context runtime''
                    pure (resolved, lhsValue, rhsValue, runtime'')
              let value ← BinaryOp.apply context.checked op lhsValue rhsValue
              -- Left shifts truncate to the operand width with no overflow
              -- check, even inside a checked block, so the compound-assign
              -- cleanup for `<<=` must be applied unchecked.
              let cleanupChecked :=
                match op with
                | BinaryOp.shl => false
                | _ => context.checked
              let cleaned ← cleanup.apply cleanupChecked value
              let updated ← resolved.write context runtime'' cleaned
              pure (cleaned, updated)
          | Expr.binary BinaryOp.boolAnd lhs rhs => do
              let (lhsValue, runtime') ←
                Expr.evalWithRuntimeOrderFuel fuel order context runtime lhs
              let lhsWord ← lhsValue.expectWord
              if wordTruthy lhsWord then
                let (rhsValue, runtime'') ←
                  Expr.evalWithRuntimeOrderFuel fuel order context runtime' rhs
                let rhsWord ← rhsValue.expectWord
                pure
                  (Value.word (boolWord (wordTruthy rhsWord)), runtime'')
              else
                pure (Value.word 0, runtime')
          | Expr.binary BinaryOp.boolOr lhs rhs => do
              let (lhsValue, runtime') ←
                Expr.evalWithRuntimeOrderFuel fuel order context runtime lhs
              let lhsWord ← lhsValue.expectWord
              if wordTruthy lhsWord then
                pure (Value.word 1, runtime')
              else
                let (rhsValue, runtime'') ←
                  Expr.evalWithRuntimeOrderFuel fuel order context runtime' rhs
                let rhsWord ← rhsValue.expectWord
                pure
                  (Value.word (boolWord (wordTruthy rhsWord)), runtime'')
          | Expr.binary op lhs rhs => do
              let ((lhsValue, rhsValue), runtime'') ←
                match order with
                | ChildEvalOrder.leftToRight => do
                    let (lhsValue, runtime') ←
                      Expr.evalWithRuntimeOrderFuel fuel order context runtime
                        lhs
                    let (rhsValue, runtime'') ←
                      Expr.evalWithRuntimeOrderFuel fuel order context runtime'
                        rhs
                    pure ((lhsValue, rhsValue), runtime'')
                | ChildEvalOrder.rightToLeft => do
                    let (rhsValue, runtime') ←
                      Expr.evalWithRuntimeOrderFuel fuel order context runtime
                        rhs
                    let (lhsValue, runtime'') ←
                      Expr.evalWithRuntimeOrderFuel fuel order context runtime'
                        lhs
                    pure ((lhsValue, rhsValue), runtime'')
              let value ← BinaryOp.apply context.checked op lhsValue rhsValue
              pure (value, runtime'')
          | Expr.addMod lhs rhs modulus => do
              let (values, runtime') ←
                Expr.evalListWithRuntimeOrderFuel fuel order context runtime
                  [lhs, rhs, modulus]
              match values with
              | [lhsValue, rhsValue, modulusValue] => do
                  let lhsWord ← lhsValue.expectWord
                  let rhsWord ← rhsValue.expectWord
                  let modulusWord ← modulusValue.expectWord
                  let value ← checkedAddMod lhsWord rhsWord modulusWord
                  pure (Value.word value, runtime')
              | _ => throw <| SolidityFailure.revert RevertData.typeMismatch
          | Expr.mulMod lhs rhs modulus => do
              let (values, runtime') ←
                Expr.evalListWithRuntimeOrderFuel fuel order context runtime
                  [lhs, rhs, modulus]
              match values with
              | [lhsValue, rhsValue, modulusValue] => do
                  let lhsWord ← lhsValue.expectWord
                  let rhsWord ← rhsValue.expectWord
                  let modulusWord ← modulusValue.expectWord
                  let value ← checkedMulMod lhsWord rhsWord modulusWord
                  pure (Value.word value, runtime')
              | _ => throw <| SolidityFailure.revert RevertData.typeMismatch
          | Expr.concatBytes exprs => do
              let (values, runtime') ←
                Expr.evalListWithRuntimeOrderFuel fuel order context runtime
                  exprs
              match Value.concatBytes? values with
              | some bs => pure (Value.bytes bs, runtime')
              | none => throw <| SolidityFailure.revert RevertData.typeMismatch
          | Expr.fixedBytesIndex size base idx => do
              let (values, runtime') ←
                Expr.evalListWithRuntimeOrderFuel fuel order context runtime
                  [base, idx]
              match values with
              | [baseValue, indexValue] => do
                  let word ← baseValue.expectWord
                  let indexWord ← indexValue.expectWord
                  let value ← fixedBytesIndex? size word indexWord
                  pure (value, runtime')
              | _ => throw <| SolidityFailure.revert RevertData.typeMismatch
          | Expr.fixedBytesCast targetSize sourceSize expr => do
              let (value, runtime') ←
                Expr.evalWithRuntimeOrderFuel fuel order context runtime expr
              let word ← value.expectWord
              let casted ← fixedBytesCast? targetSize sourceSize word
              pure (casted, runtime')
          | Expr.fixedBytesFromBytes targetSize expr => do
              let (value, runtime') ←
                Expr.evalWithRuntimeOrderFuel fuel order context runtime expr
              match value.asBytes? with
              | some bytes => do
                  let casted ← fixedBytesFromBytes? targetSize bytes
                  pure (casted, runtime')
              | none => throw <| SolidityFailure.revert RevertData.typeMismatch
          | Expr.uintCast bits expr => do
              let (value, runtime') ←
                Expr.evalWithRuntimeOrderFuel fuel order context runtime expr
              let casted ← uintCast? bits value
              pure (casted, runtime')
          | Expr.intCast bits expr => do
              let (value, runtime') ←
                Expr.evalWithRuntimeOrderFuel fuel order context runtime expr
              let casted ← intCast? bits value
              pure (casted, runtime')
          | Expr.uintCleanup bits expr => do
              let (value, runtime') ←
                Expr.evalWithRuntimeOrderFuel fuel order context runtime expr
              let casted ← uintCleanup? context.checked bits value
              pure (casted, runtime')
          | Expr.intCleanup bits expr => do
              let (value, runtime') ←
                Expr.evalWithRuntimeOrderFuel fuel order context runtime expr
              let casted ← intCleanup? context.checked bits value
              pure (casted, runtime')
          | Expr.keccak256 expr => do
              let (value, runtime') ←
                Expr.evalWithRuntimeOrderFuel fuel order context runtime expr
              match value.asBytes? with
              | some bytes =>
                  pure (Value.word (keccakWord bytes), runtime')
              | none => throw <| SolidityFailure.revert RevertData.typeMismatch
          | Expr.erc7201 expr => do
              let (value, runtime') ←
                Expr.evalWithRuntimeOrderFuel fuel order context runtime expr
              match value.asBytes? with
              | some bytes =>
                  pure (Value.word (erc7201Slot bytes), runtime')
              | none => throw <| SolidityFailure.revert RevertData.typeMismatch
          | Expr.externalHash kind expr => do
              let (value, runtime') ←
                Expr.evalWithRuntimeOrderFuel fuel order context runtime expr
              match value.asBytes? with
              | some bytes =>
                  match ← emitPrecompileWord context kind.precompileKind bytes with
                  | some hash => pure (Value.word hash, runtime')
                  | none => throw <| SolidityFailure.revert RevertData.typeMismatch
              | none => throw <| SolidityFailure.revert RevertData.typeMismatch
          | Expr.ecrecover digestExpr vExpr rExpr sExpr => do
              let (values, runtime') ←
                Expr.evalListWithRuntimeOrderFuel fuel order context runtime
                  [digestExpr, vExpr, rExpr, sExpr]
              match values with
              | [digestValue, vValue, rValue, sValue] => do
                  let digest ← digestValue.expectWord
                  let v ← vValue.expectWord
                  let r ← rValue.expectWord
                  let s ← sValue.expectWord
                  let address ← emitPrecompileWord context
                    SolidCore.Solidity.Shared.Precompile.Kind.ecrecover
                    (SolidCore.Solidity.Shared.Precompile.ecrecoverInput digest v r s)
                  pure (Value.word (address.getD 0), runtime')
              | _ => throw <| SolidityFailure.revert RevertData.typeMismatch
          | Expr.tuple exprs => do
              let (values, runtime') ←
                Expr.evalListWithRuntimeOrderFuel fuel order context runtime
                  exprs
              pure (Value.tuple values, runtime')
          | Expr.fixedArray exprs => do
              let (values, runtime') ←
                Expr.evalListWithRuntimeOrderFuel fuel order context runtime
                  exprs
              pure (Value.fixedArray values, runtime')
          | Expr.abiEncode tys exprs => do
              let (values, runtime') ←
                Expr.evalListWithRuntimeOrderFuel fuel order context runtime
                  exprs
              match abiEncodeValues? tys values with
              | some bytes => pure (Value.bytes bytes, runtime')
              | none => throw <| SolidityFailure.revert RevertData.typeMismatch
          | Expr.abiEncodeWithSelector selectorExpr tys exprs => do
              let (values, runtime') ←
                Expr.evalListWithRuntimeOrderFuel fuel order context runtime
                  (selectorExpr :: exprs)
              match values with
              | selectorValue :: argValues => do
                  let selector ← selectorValue.expectWord
                  match abiEncodeValues? tys argValues with
                  | some bytes =>
                      pure
                        ( Value.bytes
                            (wordToBytesBE selectorBytes selector ++ bytes)
                        , runtime' )
                  | none => throw <| SolidityFailure.revert RevertData.typeMismatch
              | _ => throw <| SolidityFailure.revert RevertData.typeMismatch
          | Expr.abiEncodePacked widths tys exprs => do
              let (values, runtime') ←
                Expr.evalListWithRuntimeOrderFuel fuel order context runtime
                  exprs
              match abiEncodePackedValues? widths tys values with
              | some bytes => pure (Value.bytes bytes, runtime')
              | none => throw <| SolidityFailure.revert RevertData.typeMismatch
          | Expr.abiDecode tys cleanups expr => do
              let (value, runtime') ←
                Expr.evalWithRuntimeOrderFuel fuel order context runtime expr
              match value.asBytes? with
              | some bytes =>
                  match abiDecodeValues? tys bytes with
                  | some decoded =>
                      if AbiCleanups.acceptOrUnspecified cleanups decoded then
                        match decoded with
                        | [value] => pure (value, runtime')
                        | values =>
                            pure (Value.tuple values, runtime')
                      else
                        throw <| SolidityFailure.revert RevertData.empty
                  | none => throw <| SolidityFailure.revert RevertData.empty
              | none => throw <| SolidityFailure.revert RevertData.typeMismatch
          | Expr.lowLevelCall kind targetExpr calldataExpr valueExpr
              gasExpr? _gasFirst => do
              let (values, runtime') ←
                match gasExpr? with
                | none =>
                    Expr.evalListWithRuntimeOrderFuel fuel order context
                      runtime [targetExpr, calldataExpr, valueExpr]
                | some gasExpr =>
                    Expr.evalListWithRuntimeOrderFuel fuel order context
                      runtime [targetExpr, calldataExpr, valueExpr, gasExpr]
              match values with
              | [targetValue, calldataValue, valueValue] => do
                  let target ← targetValue.expectWord
                  let calldata ←
                    match calldataValue.asBytes? with
                    | some bytes => pure bytes
                    | none => throw <| SolidityFailure.revert RevertData.typeMismatch
                  let value ← valueValue.expectWord
                  let result ←
                    emitLowLevelCall context
                      kind target calldata value none
                  pure
                    ( Value.tuple
                        [ Value.word (boolWord result.success)
                        , Value.bytes result.output ]
                    , runtime'.recordExternalInteraction
                        (ExternalInteraction.lowLevelCall result) )
              | [targetValue, calldataValue, valueValue, gasValue] => do
                  let target ← targetValue.expectWord
                  let calldata ←
                    match calldataValue.asBytes? with
                    | some bytes => pure bytes
                    | none => throw <| SolidityFailure.revert RevertData.typeMismatch
                  let value ← valueValue.expectWord
                  let gas ← gasValue.expectWord
                  let result ←
                    emitLowLevelCall context
                      kind target calldata value (some gas)
                  pure
                    ( Value.tuple
                        [ Value.word (boolWord result.success)
                        , Value.bytes result.output ]
                    , runtime'.recordExternalInteraction
                        (ExternalInteraction.lowLevelCall result) )
              | _ => throw <| SolidityFailure.revert RevertData.typeMismatch
          | Expr.contractCreate contractName constructorArgsExpr valueExpr
              saltExpr? => do
              let (values, runtime') ←
                match saltExpr? with
                | none =>
                    Expr.evalListWithRuntimeOrderFuel fuel order context
                      runtime [constructorArgsExpr, valueExpr]
                | some saltExpr =>
                    Expr.evalListWithRuntimeOrderFuel fuel order context
                      runtime [constructorArgsExpr, valueExpr, saltExpr]
              match values with
              | [argsValue, valueValue] => do
                  let constructorArgs ←
                    match argsValue.asBytes? with
                    | some bytes => pure bytes
                    | none => throw <| SolidityFailure.revert RevertData.typeMismatch
                  let value ← valueValue.expectWord
                  let result ←
                    emitContractCreation context
                      contractName constructorArgs value none
                  if result.success then
                    pure
                      ( Value.word result.address
                      , runtime'.recordExternalInteraction
                          (ExternalInteraction.contractCreation result) )
                  else
                    throw <| SolidityFailure.revert (RevertData.fromRawBytes result.output)
              | [argsValue, valueValue, saltValue] => do
                  let constructorArgs ←
                    match argsValue.asBytes? with
                    | some bytes => pure bytes
                    | none => throw <| SolidityFailure.revert RevertData.typeMismatch
                  let value ← valueValue.expectWord
                  let salt ← saltValue.expectWord
                  let result ←
                    emitContractCreation context
                      contractName constructorArgs value (some salt)
                  if result.success then
                    pure
                      ( Value.word result.address
                      , runtime'.recordExternalInteraction
                          (ExternalInteraction.contractCreation result) )
                  else
                    throw <| SolidityFailure.revert (RevertData.fromRawBytes result.output)
              | _ => throw <| SolidityFailure.revert RevertData.typeMismatch
          | Expr.newBytes lengthExpr => do
              let (lengthValue, runtime') ←
                Expr.evalWithRuntimeOrderFuel fuel order context runtime
                  lengthExpr
              let length ← lengthValue.expectWord
              let size ← context.checkMemoryAllocation length
              pure (Value.bytes (List.replicate size 0), runtime')
          | Expr.newDynamicArray elementTy lengthExpr => do
              let (lengthValue, runtime') ←
                Expr.evalWithRuntimeOrderFuel fuel order context runtime
                  lengthExpr
              let length ← lengthValue.expectWord
              let size ← context.checkMemoryAllocation length
              pure
                ( Value.dynamicArray
                    (List.replicate size elementTy.defaultValue)
                , runtime' )
          | Expr.enumFromUInt maxValue expr => do
              let (value, runtime') ←
                Expr.evalWithRuntimeOrderFuel fuel order context runtime expr
              let coerced ← enumFromUIntValue maxValue value
              pure (coerced, runtime')
          | Expr.ternary cond thenExpr elseExpr => do
              let (condValue, runtime') ←
                Expr.evalWithRuntimeOrderFuel fuel order context runtime cond
              let condWord ← condValue.expectWord
              if wordTruthy condWord then
                Expr.evalWithRuntimeOrderFuel fuel order context runtime'
                  thenExpr
              else
                Expr.evalWithRuntimeOrderFuel fuel order context runtime'
                  elseExpr
          | Expr.length expr => do
              let lengthValue (value : Value) : SolI Value :=
                match value with
                | Value.word len => pure (Value.word len)
                | _ =>
                    match value.length? with
                    | some len => pure (Value.word len)
                    | none => throw <| SolidityFailure.revert RevertData.typeMismatch
              match expr with
              | Expr.var name =>
                  match runtime.lookupStoragePathRef? name with
                  | some (target, indexes) => do
                      let value ←
                        runtime.loadStorageRefPathValue context target indexes
                      let len ← lengthValue value
                      pure (len, runtime)
                  | none =>
                      let (value, runtime') ←
                        Expr.evalWithRuntimeOrderFuel fuel order context
                          runtime expr
                      let len ← lengthValue value
                      pure (len, runtime')
              | _ =>
                  if expr.hasStorageRoot || expr.hasStorageRefRoot runtime then
                    let (target, runtime') ←
                      Expr.resolveLValueWithRuntimeOrderFuel fuel order
                        context runtime expr
                    match target.asStoragePath? with
                    | some (name, indexes) => do
                        let value ←
                          runtime'.loadStorageRefPathValue context name indexes
                        let len ← lengthValue value
                        pure (len, runtime')
                    | none => throw <| SolidityFailure.revert RevertData.typeMismatch
                  else
                    let (value, runtime') ←
                      Expr.evalWithRuntimeOrderFuel fuel order context runtime
                        expr
                    let len ← lengthValue value
                    pure (len, runtime')
          | Expr.index base idx => do
              if base.hasStorageRoot then
                let (baseTarget, runtime') ←
                  Expr.resolveLValueWithRuntimeOrderFuel fuel order
                    context runtime base
                match baseTarget.asStoragePath? with
                | some (name, indexes) =>
                    let (indexValue, runtime'') ←
                      Expr.evalWithRuntimeOrderFuel fuel order context
                        runtime' idx
                    let value ←
                      runtime''.loadStoragePath context name
                        (indexes ++ [indexValue])
                    pure (value, runtime'')
                | none => throw <| SolidityFailure.revert RevertData.typeMismatch
              else if base.hasStorageRefRoot runtime then
                let (resolved, runtime') ←
                  Expr.resolveLValueWithRuntimeOrderFuel fuel order context
                    runtime (Expr.index base idx)
                let value ← resolved.read context runtime'
                pure (value, runtime')
              else
                match base with
                | Expr.var name =>
                    match runtime.lookupStoragePathRef? name with
                    | some (target, indexes) =>
                        let (indexValue, runtime') ←
                          Expr.evalWithRuntimeOrderFuel fuel order context
                            runtime idx
                        let value ←
                          runtime'.loadStoragePath context target
                            (indexes ++ [indexValue])
                        pure (value, runtime')
                    | none =>
                        let (values, runtime') ←
                          Expr.evalListWithRuntimeOrderFuel fuel order
                            context runtime [base, idx]
                        match values with
                        | [baseValue, indexValue] => do
                            let indexWord ← indexValue.expectWord
                            let baseValue ←
                              runtime'.derefMemoryValue baseValue
                            let value ← baseValue.index? indexWord
                            let value ← runtime'.derefMemoryValue value
                            pure (value, runtime')
                        | _ => throw <| SolidityFailure.revert RevertData.typeMismatch
                | _ =>
                    let (values, runtime') ←
                      Expr.evalListWithRuntimeOrderFuel fuel order context
                        runtime [base, idx]
                    match values with
                    | [baseValue, indexValue] => do
                        let indexWord ← indexValue.expectWord
                        let baseValue ← runtime'.derefMemoryValue baseValue
                        let value ← baseValue.index? indexWord
                        let value ← runtime'.derefMemoryValue value
                        pure (value, runtime')
                    | _ => throw <| SolidityFailure.revert RevertData.typeMismatch
          | Expr.slice base start stop => do
              let readSlice (baseValue : Value)
                  (startValue? stopValue? : Option Value)
                  (runtime' : Runtime) :
                  SolI (Value × Runtime) := do
                let startWord? ←
                  match startValue? with
                  | some value => do
                      let word ← value.expectWord
                      pure (some word)
                  | none => pure none
                let stopWord? ←
                  match stopValue? with
                  | some value => do
                      let word ← value.expectWord
                      pure (some word)
                  | none => pure none
                let value ← baseValue.slice? startWord? stopWord?
                pure (value, runtime')
              match start, stop with
              | none, none => do
                  let (baseValue, runtime') ←
                    Expr.evalWithRuntimeOrderFuel fuel order context
                      runtime base
                  readSlice baseValue none none runtime'
              | some startExpr, none => do
                  let (values, runtime') ←
                    Expr.evalListWithRuntimeOrderFuel fuel order context
                      runtime [base, startExpr]
                  match values with
                  | [baseValue, startValue] =>
                      readSlice baseValue (some startValue) none runtime'
                  | _ => throw <| SolidityFailure.revert RevertData.typeMismatch
              | none, some stopExpr => do
                  let (values, runtime') ←
                    Expr.evalListWithRuntimeOrderFuel fuel order context
                      runtime [base, stopExpr]
                  match values with
                  | [baseValue, stopValue] =>
                      readSlice baseValue none (some stopValue) runtime'
                  | _ => throw <| SolidityFailure.revert RevertData.typeMismatch
              | some startExpr, some stopExpr => do
                  let (values, runtime') ←
                    Expr.evalListWithRuntimeOrderFuel fuel order context
                      runtime [base, startExpr, stopExpr]
                  match values with
                  | [baseValue, startValue, stopValue] =>
                      readSlice baseValue (some startValue) (some stopValue)
                        runtime'
                  | _ => throw <| SolidityFailure.revert RevertData.typeMismatch

def Expr.evalListWithRuntimeOrderFuel (fuel : Nat) (order : ChildEvalOrder)
    (context : Context) : Runtime -> List Expr ->
    SolI (List Value × Runtime)
  | runtime, exprs =>
      match fuel with
      | 0 => throw <| SolidityFailure.revert RevertData.typeMismatch
      | fuel + 1 =>
          match exprs with
          | [] => pure ([], runtime)
          | expr :: rest =>
              match order with
              | ChildEvalOrder.leftToRight => do
                  let (value, runtime') ←
                    Expr.evalWithRuntimeOrderFuel fuel order context runtime
                      expr
                  let (values, runtime'') ←
                    Expr.evalListWithRuntimeOrderFuel fuel order context
                      runtime' rest
                  pure (value :: values, runtime'')
              | ChildEvalOrder.rightToLeft => do
                  let (values, runtime') ←
                    Expr.evalListWithRuntimeOrderFuel fuel order context
                      runtime rest
                    let (value, runtime'') ←
                      Expr.evalWithRuntimeOrderFuel fuel order context
                        runtime' expr
                    pure (value :: values, runtime'')

def Expr.memoryRefOrValueWithRuntimeOrderFuel
    (fuel : Nat) (order : ChildEvalOrder) (context : Context) :
    Runtime -> Expr -> SolI (Option Nat × Option Value × Runtime)
  | runtime, expr =>
      match fuel with
      | 0 => throw <| SolidityFailure.revert RevertData.typeMismatch
      | fuel + 1 =>
          match expr with
          | Expr.var name =>
              pure (runtime.lookupMemoryRef? name, none, runtime)
          | Expr.index base idx => do
              let finish (baseValue indexValue : Value)
                  (runtime' : Runtime) :
                  Except RevertData
                    (Option Nat × Option Value × Runtime) := do
                let indexWord ← indexValue.expectWord
                let baseValue ← runtime'.derefMemoryValue baseValue
                let value ← baseValue.index? indexWord
                match value with
                | Value.memoryRef id =>
                    pure (some id, none, runtime')
                | _ => pure (none, some value, runtime')
              match order with
              | ChildEvalOrder.leftToRight => do
                  let (baseValue, runtime') ←
                    Expr.evalWithRuntimeOrderFuel fuel order context
                      runtime base
                  let (indexValue, runtime'') ←
                    Expr.evalWithRuntimeOrderFuel fuel order context
                      runtime' idx
                  finish baseValue indexValue runtime''
              | ChildEvalOrder.rightToLeft => do
                  let (indexValue, runtime') ←
                    Expr.evalWithRuntimeOrderFuel fuel order context
                      runtime idx
                  let (baseValue, runtime'') ←
                    Expr.evalWithRuntimeOrderFuel fuel order context
                      runtime' base
                  finish baseValue indexValue runtime''
          | _ => pure (none, none, runtime)

def Expr.resolveLValueWithRuntimeOrderFuel
    (fuel : Nat) (order : ChildEvalOrder) (context : Context) :
    Runtime -> Expr -> SolI (ResolvedLValue × Runtime)
  | runtime, expr =>
      match fuel with
      | 0 => throw <| SolidityFailure.revert RevertData.typeMismatch
      | fuel + 1 =>
          match expr with
          | Expr.var name =>
              match runtime.lookupStoragePathRef? name with
              | some (target, []) =>
                  pure (ResolvedLValue.storageField target, runtime)
              | some (target, indexes) =>
                  pure (ResolvedLValue.storagePath target indexes,
                    runtime)
              | none =>
                  match runtime.lookupLocal? name with
                  | some _ => pure (ResolvedLValue.local name, runtime)
                  | none => throw <| SolidityFailure.revert RevertData.typeMismatch
          | Expr.immutable name =>
              pure (ResolvedLValue.immutable name, runtime)
          | Expr.storage name =>
              pure (ResolvedLValue.storageField name, runtime)
          | Expr.storageIndex name idx => do
              let (indexValue, runtime') ←
                Expr.evalWithRuntimeOrderFuel fuel order context runtime idx
              pure (ResolvedLValue.storageIndex name indexValue,
                runtime')
          | Expr.index base idx => do
              let finish (baseTarget : ResolvedLValue)
                  (indexValue : Value) (runtime' : Runtime) :
                  SolI (ResolvedLValue × Runtime) := do
                match baseTarget with
                | ResolvedLValue.storageField name =>
                    pure
                      (ResolvedLValue.storageIndex name indexValue,
                        runtime')
                | ResolvedLValue.storageIndex name firstIndex =>
                    pure
                      (ResolvedLValue.storagePath name
                          [firstIndex, indexValue],
                        runtime')
                | ResolvedLValue.storagePath name indexes =>
                    pure
                      (ResolvedLValue.storagePath name
                          (indexes ++ [indexValue]),
                        runtime')
                | _ =>
                    let indexWord ← indexValue.expectWord
                    let rawValue ← baseTarget.readRaw context runtime'
                    let target :=
                      match rawValue with
                      | Value.memoryRef id =>
                          ResolvedLValue.valueIndex
                            (ResolvedLValue.memoryCell id) indexWord
                      | _ =>
                          ResolvedLValue.valueIndex baseTarget indexWord
                    pure (target, runtime')
              match order with
              | ChildEvalOrder.leftToRight => do
                  let (baseTarget, runtime') ←
                    Expr.resolveLValueWithRuntimeOrderFuel fuel order
                      context runtime base
                  let (indexValue, runtime'') ←
                    Expr.evalWithRuntimeOrderFuel fuel order context
                      runtime' idx
                  finish baseTarget indexValue runtime''
              | ChildEvalOrder.rightToLeft => do
                  let (indexValue, runtime') ←
                    Expr.evalWithRuntimeOrderFuel fuel order context
                      runtime idx
                  let (baseTarget, runtime'') ←
                    Expr.resolveLValueWithRuntimeOrderFuel fuel order
                      context runtime' base
                  finish baseTarget indexValue runtime''
          | _ => throw <| SolidityFailure.revert RevertData.typeMismatch

end

def Expr.evalWithRuntimeOrder
    (order : ChildEvalOrder) (context : Context) (runtime : Runtime)
    (expr : Expr) : SolI (Value × Runtime) :=
  Expr.evalWithRuntimeOrderFuel (Expr.orderFuel expr + 1)
    order context runtime expr

def Expr.evalListWithRuntimeOrder
    (order : ChildEvalOrder) (context : Context) (runtime : Runtime)
    (exprs : List Expr) : SolI (List Value × Runtime) :=
  Expr.evalListWithRuntimeOrderFuel (Expr.listEvalFuel exprs)
    order context runtime exprs

def Expr.memoryRefOrValueWithRuntimeOrder
    (order : ChildEvalOrder) (context : Context) (runtime : Runtime)
    (expr : Expr) : SolI (Option Nat × Option Value × Runtime) :=
  Expr.memoryRefOrValueWithRuntimeOrderFuel (Expr.orderFuel expr + 1)
    order context runtime expr

def Expr.resolveLValueWithRuntimeOrder
    (order : ChildEvalOrder) (context : Context) (runtime : Runtime)
    (expr : Expr) : SolI (ResolvedLValue × Runtime) :=
  Expr.resolveLValueWithRuntimeOrderFuel (Expr.orderFuel expr + 1)
    order context runtime expr

def Expr.evalBinaryWithRuntimeOrder
    (order : ChildEvalOrder) (context : Context) (runtime : Runtime)
    (op : BinaryOp) (lhs rhs : Expr) :
    SolI (Value × Runtime) :=
  Expr.evalWithRuntimeOrder order context runtime (Expr.binary op lhs rhs)

def Context.withChildEvalOrder
    (context : Context) (order : ChildEvalOrder) : Context :=
  { context with childEvalOrder? := some order }

def Context.withoutChildEvalOrder (context : Context) : Context :=
  { context with childEvalOrder? := none }

def ChildEvalOrder.yulCompatible : ChildEvalOrder :=
  ChildEvalOrder.rightToLeft

def Context.effectiveChildEvalOrder (context : Context) : ChildEvalOrder :=
  context.childEvalOrder?.getD ChildEvalOrder.yulCompatible

def ChildEvalOrder.unspecifiedOrders : List ChildEvalOrder :=
  [ChildEvalOrder.yulCompatible]

def Context.withUnspecifiedChildEvalOrders
    (context : Context) : List Context :=
  ChildEvalOrder.unspecifiedOrders.map context.withChildEvalOrder

/-- Fold an *expression*-level `SolI` tree back to `Except RevertData`, answering
    queries from `Context`. `fuel` is safe because the number of queries an
    expression can emit is bounded by its syntactic external-request node count
    (`lowLevelCall` **+ contractCreate** nodes) ≤ `Expr.orderFuel` — the whole-
    call execution path is fuel-free (`SolI.run`); this stays only for
    constant-expression evaluation and transcript utilities. -/
def SolI.foldExpr {α : Type} (fuel : Nat) (context : Context) (tree : SolI α) :
    Except RevertData α :=
  match SolI.runFromContext fuel context tree with
  | .ok v => .ok v
  | .error (.revert e) => .error e
  | .error .outOfFuel => .error RevertData.typeMismatch

def Expr.evalWithRuntimeByContext
    (expr : Expr) (context : Context) (runtime : Runtime) :
    Except RevertData (Value × Runtime) :=
  SolI.foldExpr (Expr.orderFuel expr + 1) context
    (Expr.evalWithRuntimeOrder context.effectiveChildEvalOrder context runtime expr)

def Expr.evalListWithRuntimeByContext
    (context : Context) (runtime : Runtime) (exprs : List Expr) :
    Except RevertData (List Value × Runtime) :=
  SolI.foldExpr (Expr.listEvalFuel exprs + 1) context
    (Expr.evalListWithRuntimeOrder context.effectiveChildEvalOrder context runtime exprs)

inductive TernaryBranch where
  | thenBranch
  | elseBranch
  deriving Repr, BEq

def Expr.memoryRefOrValueWithRuntimeByContext
    (expr : Expr) (context : Context) (runtime : Runtime) :
    Except RevertData (Option Nat × Option Value × Runtime) :=
  SolI.foldExpr (Expr.orderFuel expr + 1) context
    (Expr.memoryRefOrValueWithRuntimeOrder
      context.effectiveChildEvalOrder context runtime expr)

def Expr.resolveLValueWithRuntimeByContext
    (expr : Expr) (context : Context) (runtime : Runtime) :
    Except RevertData (ResolvedLValue × Runtime) :=
  SolI.foldExpr (Expr.orderFuel expr + 1) context
    (Expr.resolveLValueWithRuntimeOrder
      context.effectiveChildEvalOrder context runtime expr)

def Expr.evalReturnValueWithRuntimeOrder
    (order : ChildEvalOrder) (context : Context) (runtime : Runtime)
    (expr : Expr) : SolI (Value × Runtime) :=
  match expr with
  | Expr.var name =>
      match runtime.lookupMemoryRef? name with
      | some id => pure (Value.memoryRef id, runtime)
      | none => Expr.evalWithRuntimeOrder order context runtime expr
  | _ => Expr.evalWithRuntimeOrder order context runtime expr

def Expr.evalReturnListWithRuntimeOrderFuel
    (fuel : Nat) (order : ChildEvalOrder) (context : Context) :
    Runtime -> List Expr -> SolI (List Value × Runtime)
  | runtime, exprs =>
      match fuel with
      | 0 => throw <| SolidityFailure.revert RevertData.typeMismatch
      | fuel + 1 =>
          match exprs with
          | [] => pure ([], runtime)
          | expr :: rest =>
              match order with
              | ChildEvalOrder.leftToRight => do
                  let (value, runtime') ←
                    Expr.evalReturnValueWithRuntimeOrder order context
                      runtime expr
                  let (values, runtime'') ←
                    Expr.evalReturnListWithRuntimeOrderFuel fuel order
                      context runtime' rest
                  pure (value :: values, runtime'')
              | ChildEvalOrder.rightToLeft => do
                  let (values, runtime') ←
                    Expr.evalReturnListWithRuntimeOrderFuel fuel order
                      context runtime rest
                  let (value, runtime'') ←
                    Expr.evalReturnValueWithRuntimeOrder order context
                      runtime' expr
                  pure (value :: values, runtime'')

def Expr.evalReturnListWithRuntimeOrder
    (order : ChildEvalOrder) (context : Context) (runtime : Runtime)
    (exprs : List Expr) : SolI (List Value × Runtime) :=
  Expr.evalReturnListWithRuntimeOrderFuel (Expr.listEvalFuel exprs)
    order context runtime exprs

def Expr.evalReturnListWithRuntimeByContext
    (context : Context) (runtime : Runtime) (exprs : List Expr) :
    Except RevertData (List Value × Runtime) :=
  SolI.foldExpr (Expr.listEvalFuel exprs + 1) context
    (Expr.evalReturnListWithRuntimeOrder
      context.effectiveChildEvalOrder context runtime exprs)

def LValue.resolveWithRuntime (target : LValue) (context : Context)
    (runtime : Runtime) : SolI (ResolvedLValue × Runtime) :=
  Expr.resolveLValueWithRuntimeOrder context.effectiveChildEvalOrder context
    runtime target.toExpr

def LValues.writeTupleWithRuntime (context : Context) :
    Runtime -> List (Option LValue) -> List Value -> SolI Runtime
  | runtime, [], [] => pure runtime
  | runtime, some target :: targets, value :: values => do
      let (resolved, runtime') ← target.resolveWithRuntime context runtime
      let updated ← resolved.write context runtime' value
      LValues.writeTupleWithRuntime context updated targets values
  | runtime, none :: targets, _ :: values =>
      LValues.writeTupleWithRuntime context runtime targets values
  | _, _, _ => throw (SolidityFailure.revert RevertData.typeMismatch)

structure BindingDecl where
  name : String
  ty : Ty
  deriving Repr

mutual

inductive Stmt where
  | skip : Stmt
  | block : List Stmt -> Stmt
  | varDecl : Ty -> String -> Option Expr -> Stmt
  | memoryVarDecl : Ty -> String -> Option Expr -> Stmt
  | memoryLocalize : Ty -> String -> Stmt
  | storageAlias : String -> String -> Stmt
  | storageAliasPath : String -> String -> List Expr -> Stmt
  | storageAliasFrom : String -> String -> Stmt
  | storageAliasFromPath : String -> String -> List Expr -> Stmt
  | storageAliasAssign : String -> String -> Stmt
  | storageAliasAssignPath : String -> String -> List Expr -> Stmt
  | storageAliasAssignFrom : String -> String -> Stmt
  | storageAliasAssignFromPath : String -> String -> List Expr -> Stmt
  | exprStmt : Expr -> Stmt
  | assign : LValue -> Expr -> Stmt
  | assignTuple : List (Option LValue) -> Expr -> Stmt
  | assignOp : LValue -> BinaryOp -> Expr -> Stmt
  | assignOpCleanup : LValue -> BinaryOp -> Expr -> ValueCleanup -> Stmt
  | deleteValue : LValue -> Stmt
  | storageArrayPush : String -> Option Expr -> Stmt
  | storageArrayPushRef : String -> Option Expr -> Stmt
  | storageArrayPushRefPath : String -> List Expr -> Option Expr -> Stmt
  | storageArrayPushPath : String -> List Expr -> Option Expr -> Stmt
  | storageArrayPushPathAssign : String -> List Expr -> Expr -> Stmt
  | storageArrayPushRefPathAssign : String -> List Expr -> Expr -> Stmt
  | storageArrayPop : String -> Stmt
  | storageArrayPopRef : String -> Stmt
  | storageArrayPopRefPath : String -> List Expr -> Stmt
  | storageArrayPopPath : String -> List Expr -> Stmt
  | panic : Word -> Stmt
  | assertStmt : Expr -> Stmt
  | requireStmt : Expr -> Option String -> Stmt
  | requireErrorExpr : Expr -> Expr -> Stmt
  | requireCustom : Expr -> String -> List Expr -> Stmt
  | captureReturn : List String -> Stmt -> Stmt
  | internalCall : List String -> String -> List Expr -> Stmt
  | ifElse : Expr -> Stmt -> Stmt -> Stmt
  | switch : Expr -> List (Word × Stmt) -> Option Stmt -> Stmt
  | whileLoop : Expr -> Stmt -> Stmt
  | doWhile : Stmt -> Expr -> Stmt
  | forLoop : Stmt -> Expr -> Stmt -> Stmt -> Stmt
  | tryExternalCall :
      LowLevelCallKind -> Expr -> Expr -> Expr -> Option Expr -> Bool ->
      Bool -> List BindingDecl -> List AbiCleanup -> Stmt ->
      List TryCatchClause -> Stmt
  | tryContractCreate :
      String -> Expr -> Expr -> Option Expr -> List BindingDecl -> Stmt ->
      List TryCatchClause -> Stmt
  | break : Stmt
  | continue : Stmt
  | returnValues : List Expr -> Stmt
  | revertError : Option String -> Stmt
  | revertErrorExpr : Expr -> Stmt
  | revert : String -> List Expr -> Stmt
  | emitEvent : String -> List Expr -> Stmt
  | selfdestruct : Expr -> Stmt
  | checked : Stmt -> Stmt
  | unchecked : Stmt -> Stmt
  deriving Repr

inductive TryCatchClause where
  | clause : Option String -> List BindingDecl -> Stmt -> TryCatchClause
  deriving Repr

end

inductive Result where
  | normal : Runtime -> Result
  | returned : Runtime -> List Value -> Result
  | selfdestructed : Runtime -> Result
  | reverted : Runtime -> RevertData -> Result
  | broke : Runtime -> Result
  | continued : Runtime -> Result
  deriving Repr

inductive RevertPayloadSource where
  | empty
  | errorString : String -> RevertPayloadSource
  | errorBytesExpression : Expr -> RevertPayloadSource
  | customError : String -> List Expr -> RevertPayloadSource
  deriving Repr

inductive RequireCheckSource where
  | assert : Expr -> RequireCheckSource
  | requireEmpty : Expr -> RequireCheckSource
  | requireString : Expr -> String -> RequireCheckSource
  | requireBytesExpression : Expr -> Expr -> RequireCheckSource
  | requireCustom : Expr -> String -> List Expr -> RequireCheckSource
  deriving Repr

inductive TryCatchMatchKind where
  | errorString
  | panic
  | lowLevel
  deriving Repr, BEq

inductive SwitchBranchSelection where
  | caseBranch : Word -> SwitchBranchSelection
  | defaultBranch
  | noBranch
  deriving Repr, BEq

def Result.mapRuntime (f : Runtime -> Runtime) : Result -> Result
  | Result.normal runtime => Result.normal (f runtime)
  | Result.returned runtime values => Result.returned (f runtime) values
  | Result.selfdestructed runtime => Result.selfdestructed (f runtime)
  | Result.reverted runtime data => Result.reverted (f runtime) data
  | Result.broke runtime => Result.broke (f runtime)
  | Result.continued runtime => Result.continued (f runtime)

def Result.runtime : Result -> Runtime
  | Result.normal runtime => runtime
  | Result.returned runtime _ => runtime
  | Result.selfdestructed runtime => runtime
  | Result.reverted runtime _ => runtime
  | Result.broke runtime => runtime
  | Result.continued runtime => runtime

def BindingDecl.defaultBinding (decl : BindingDecl) : String × Value :=
  (decl.name, decl.ty.defaultValue)

def BindingDecl.bindArg? (decl : BindingDecl) (value : Value) :
    Option (String × Value) := do
  let coerced ← decl.ty.coerceValue? value
  some (decl.name, coerced)

def BindingDecl.bindArgs? :
    List BindingDecl -> List Value -> Option Frame
  | [], [] => some []
  | decl :: decls, value :: values => do
      let head ← decl.bindArg? value
      let tail ← BindingDecl.bindArgs? decls values
      some (head :: tail)
  | _, _ => none

def Runtime.withFrame (runtime : Runtime) (frame : Frame) : Runtime :=
  { runtime with locals := frame :: runtime.locals }

def Runtime.emitEvent (context : Context)
    (runtime : Runtime) (name : String) (values : List Value) :
    Except RevertData Runtime :=
  match context.eventDecl? name with
  | some decl =>
      let event? : Option Event :=
        if decl.fields.isEmpty && decl.topic?.isNone then
          some
            { name := name
              indexed := values.take decl.indexedCount
              data := values.drop decl.indexedCount }
        else
          match decl.encodeFields? values with
          | some encoded =>
              some
                { name := name
                  indexed := encoded.indexedValues
                  data := encoded.dataValues
                  topics := encoded.topics
                  dataBytes := encoded.dataBytes }
          | none => none
      match event? with
      | some event =>
          Except.ok
            { runtime with
              state := { runtime.state with
                events := SolidCore.Solidity.Shared.Log.append
                  runtime.state.events event } }
      | none => Except.error RevertData.typeMismatch
  | none => Except.error RevertData.typeMismatch

def externalErrorSelector : Word := 0x08c379a0

def externalPanicSelector : Word := 0x4e487b71

def errorStringBytesRevert? (value : Value) : Option RevertData := do
  let bytes ← value.asBytes?
  let encoded ← abiEncodeValues? [Ty.bytesCalldata] [Value.bytes bytes]
  some
    (RevertData.raw
      (wordToBytesBE selectorBytes externalErrorSelector ++ encoded))

def revertBytesSelector? (bytes : List Byte) : Option Word :=
  match readBytes? bytes 0 selectorBytes with
  | some selector => some (bytesToWordBE selector)
  | none => none

def TryCatchClause.matchLowLevel? (raw : List Byte)
    (params : List BindingDecl) : Option Frame :=
  match params with
  | [] => some []
  | [_] => BindingDecl.bindArgs? params [Value.bytes raw]
  | _ => none

def TryCatchClause.match? (raw : List Byte) :
    TryCatchClause -> Option (Frame × Stmt)
  | TryCatchClause.clause (some "Error") params body => do
      let selector ← revertBytesSelector? raw
      if wordEq selector externalErrorSelector then
        let values ← abiDecodeValues? [Ty.bytesCalldata] (raw.drop selectorBytes)
        let frame ← BindingDecl.bindArgs? params values
        some (frame, body)
      else
        none
  | TryCatchClause.clause (some "Panic") params body => do
      let selector ← revertBytesSelector? raw
      if wordEq selector externalPanicSelector then
        let values ← abiDecodeValues? [Ty.uint256] (raw.drop selectorBytes)
        let frame ← BindingDecl.bindArgs? params values
        some (frame, body)
      else
        none
  | TryCatchClause.clause (some _) _ _ => none
  | TryCatchClause.clause none params body => do
      let frame ← TryCatchClause.matchLowLevel? raw params
      some (frame, body)

def TryCatchClause.findMatch? (raw : List Byte) :
    List TryCatchClause -> Option (Frame × Stmt)
  | [] => none
  | head :: rest =>
      match head.match? raw with
      | some matched => some matched
      | none => TryCatchClause.findMatch? raw rest

def TryCatchClause.name? : TryCatchClause -> Option String
  | TryCatchClause.clause name? _ _ => name?

def TryCatchClause.matchKind? : TryCatchClause -> Option TryCatchMatchKind
  | TryCatchClause.clause (some "Error") _ _ =>
      some TryCatchMatchKind.errorString
  | TryCatchClause.clause (some "Panic") _ _ =>
      some TryCatchMatchKind.panic
  | TryCatchClause.clause none _ _ =>
      some TryCatchMatchKind.lowLevel
  | TryCatchClause.clause (some _) _ _ => none

def Stmt.findSwitchCase? (value : Word) :
    List (Word × Stmt) -> Option (Word × Stmt)
  | [] => none
  | (label, body) :: rest =>
      if wordEq label value then
        some (label, body)
      else
        Stmt.findSwitchCase? value rest

def Stmt.findSwitchBranch? (value : Word)
    (cases : List (Word × Stmt)) : Option Stmt :=
  (Stmt.findSwitchCase? value cases).map Prod.snd

/-- The evaluator-visible representation of an internal-linkage function
    (contract-internal / free / library-internal / `using` / `super`). Distinct
    from `FunctionDef`, which additionally carries entry-only concerns
    (`selector?`, `payable`, `paramAbiCleanups`). Introduced by the
    function-boundary refactor (`docs/function-boundary-refactor-plan.md` §2.2):
    internal calls become `Stmt.internalCall` nodes keyed by `name` into a
    `FunctionTable`, instead of being spliced inline at elaboration. -/
structure InternalFunction where
  name : String
  params : List BindingDecl
  returns : List BindingDecl
  body : Stmt
  deriving Repr

/-- The evaluator-visible table of internal-linkage functions, looked up by
    name. Threaded as an explicit parameter of the `Stmt.eval` mutual block: it
    cannot live in `Context` (defined long before `Stmt`/`FunctionDef`, and
    `InternalFunction.body : Stmt`). -/
abbrev FunctionTable := List InternalFunction

def FunctionTable.lookup? (table : FunctionTable) (name : String) :
    Option InternalFunction :=
  List.find? (fun fn => fn.name == name) table

def InternalFunction.returnDefaultBindings (fn : InternalFunction) : Frame :=
  fn.returns.map BindingDecl.defaultBinding

/-- Build the isolated callee frame: parameters bound to (coerced) argument
    values, followed by named/return locals defaulted. Mirrors
    `FunctionDef.initialFrame?` (the entry-frame builder) exactly. -/
def InternalFunction.initialFrame? (fn : InternalFunction)
    (args : List Value) : Option Frame :=
  match BindingDecl.bindArgs? fn.params args with
  | some params => some (params ++ fn.returnDefaultBindings)
  | none => none

/-- Collect the *named* return values from a finished callee runtime, coercing
    each to its declared type. Shared by the entry mapping
    (`FunctionDef.callBodyResult`, via `FunctionDef.collectReturns`) and the
    in-frame internal-call arm so the two cannot drift (refactor risk R3). -/
def collectReturnBindings (returns : List BindingDecl)
    (runtime : Runtime) : Except RevertData (List Value) :=
  let rec collect : List BindingDecl -> Except RevertData (List Value)
    | [] => Except.ok []
    | decl :: rest => do
        let value ←
          match runtime.lookupLocal? decl.name with
          | some value => runtime.derefMemoryValueDeep value
          | none => Except.error RevertData.typeMismatch
        let value ←
          match decl.ty.coerceValue? value with
          | some coerced => Except.ok coerced
          | none => Except.error RevertData.typeMismatch
        let values ← collect rest
        Except.ok (value :: values)
  collect returns

/-- Coerce *explicitly returned* values to the declared return types. Shared by
    the entry mapping (via `FunctionDef.coerceReturnValues`) and the
    internal-call arm (refactor risk R3). -/
def coerceReturnBindings (returns : List BindingDecl)
    (runtime : Runtime) (values : List Value) :
    Except RevertData (List Value) :=
  let rec coerce :
      List BindingDecl -> List Value -> Except RevertData (List Value)
    | [], [] => Except.ok []
    | decl :: decls, value :: rest => do
        let value ← runtime.derefMemoryValueDeep value
        let head ←
          match decl.ty.coerceValue? value with
          | some coerced => Except.ok coerced
          | none => Except.error RevertData.typeMismatch
        let tail ← coerce decls rest
        Except.ok (head :: tail)
    | _, _ => Except.error RevertData.typeMismatch
  coerce returns values

/-- Write an internal call's coerced return values into the caller's target
    locals (already declared by elaboration). Empty targets discard the values
    (statement-position call). Mirrors `Stmt.captureReturn`'s assignment. -/
def internalCallAssign (runtime : Runtime) (targets : List String)
    (values : List Value) : SolI Result :=
  if targets.isEmpty then
    pure (Result.normal runtime)
  else
    match runtime.assignNamedValues? targets values with
    | some updated => pure (Result.normal updated)
    | none => pure (Result.reverted runtime RevertData.typeMismatch)

mutual

def Stmt.eval (fuel : Nat) (table : FunctionTable) (context : Context)
    (runtime : Runtime) : Stmt -> SolI Result :=
  match fuel with
  | 0 => fun _ => throw SolidityFailure.outOfFuel
  | fuel + 1 => fun stmt =>
      match stmt with
      | Stmt.skip => pure (Result.normal runtime)
      | Stmt.block body => do
          let result ← Stmt.evalList fuel table context runtime.pushScope body
          pure (result.mapRuntime Runtime.popScope)
      | Stmt.varDecl ty name init =>
          match init with
          | some expr => do
              match ← (Expr.evalWithRuntimeOrder context.effectiveChildEvalOrder
                  context runtime expr).caught with
              | Except.ok (value, runtime') =>
                  match ty.coerceValue? value with
                  | some coerced =>
                      pure
                        (Result.normal
                          (runtime'.declareLocal name coerced))
                  | none =>
                      pure (Result.reverted runtime RevertData.typeMismatch)
              | Except.error err =>
                  pure (Result.reverted runtime err)
          | none =>
              pure
                (Result.normal
                  (runtime.declareLocal name ty.defaultValue))
      | Stmt.memoryVarDecl ty name init =>
          match init with
          | some expr => do
              match ←
                (Expr.memoryRefOrValueWithRuntimeOrder
                  context.effectiveChildEvalOrder context runtime expr).caught
              with
              | Except.ok (some id, _, runtime') =>
                  pure
                    (Result.normal
                      (runtime'.declareLocal name (Value.memoryRef id)))
              | Except.ok (none, some value, runtime') =>
                  match runtime'.declareMemoryLocal ty name value with
                  | some updated => pure (Result.normal updated)
                  | none =>
                      pure (Result.reverted runtime RevertData.typeMismatch)
              | Except.ok (none, none, runtime') =>
                  match ← (Expr.evalWithRuntimeOrder context.effectiveChildEvalOrder
                      context runtime' expr).caught with
                  | Except.ok (value, runtime'') =>
                      match runtime''.declareMemoryLocal ty name value with
                      | some updated => pure (Result.normal updated)
                      | none =>
                          pure (Result.reverted runtime RevertData.typeMismatch)
                  | Except.error err => pure (Result.reverted runtime err)
              | Except.error err => pure (Result.reverted runtime err)
          | none =>
              match runtime.declareMemoryLocal ty name ty.defaultValue with
              | some updated => pure (Result.normal updated)
              | none => pure (Result.reverted runtime RevertData.typeMismatch)
      | Stmt.memoryLocalize ty name =>
          match runtime.localizeMemoryLocal ty name with
          | some updated => pure (Result.normal updated)
          | none => pure (Result.reverted runtime RevertData.typeMismatch)
      | Stmt.storageAlias name target =>
          pure
            (Result.normal
              (runtime.declareLocal name (Value.storageRef target)))
      | Stmt.storageAliasPath name target indexes => do
          match ← (Expr.evalListWithRuntimeOrder context.effectiveChildEvalOrder
              context runtime indexes).caught with
          | Except.ok (indexValues, runtime') =>
              pure
                (Result.normal
                  (runtime'.declareLocal name
                    (Value.storageRefForPath target indexValues)))
          | Except.error err => pure (Result.reverted runtime err)
      | Stmt.storageAliasFrom name source =>
          match runtime.lookupStoragePathRef? source with
          | some (target, indexes) =>
              pure
                (Result.normal
                  (runtime.declareLocal name
                    (Value.storageRefForPath target indexes)))
          | none => pure (Result.reverted runtime RevertData.typeMismatch)
      | Stmt.storageAliasFromPath name source extraIndexes =>
          match runtime.lookupStoragePathRef? source with
          | some (target, indexes) => do
              match ←
                (Expr.evalListWithRuntimeOrder context.effectiveChildEvalOrder
                  context runtime extraIndexes).caught
              with
              | Except.ok (extraIndexValues, runtime') =>
                  pure
                    (Result.normal
                      (runtime'.declareLocal name
                        (Value.storageRefForPath target
                          (indexes ++ extraIndexValues))))
              | Except.error err => pure (Result.reverted runtime err)
          | none => pure (Result.reverted runtime RevertData.typeMismatch)
      | Stmt.storageAliasAssign name target =>
          match runtime.assignStorageRef? name target with
          | some updated => pure (Result.normal updated)
          | none => pure (Result.reverted runtime RevertData.typeMismatch)
      | Stmt.storageAliasAssignPath name target indexes => do
          match ← (Expr.evalListWithRuntimeOrder context.effectiveChildEvalOrder
              context runtime indexes).caught with
          | Except.ok (indexValues, runtime') =>
              match
                runtime'.assignStoragePathRef? name target indexValues
              with
              | some updated => pure (Result.normal updated)
              | none => pure (Result.reverted runtime RevertData.typeMismatch)
          | Except.error err => pure (Result.reverted runtime err)
      | Stmt.storageAliasAssignFrom name source =>
          match runtime.lookupStoragePathRef? source with
          | some (target, indexes) =>
              match runtime.assignStoragePathRef? name target indexes with
              | some updated => pure (Result.normal updated)
              | none => pure (Result.reverted runtime RevertData.typeMismatch)
          | none => pure (Result.reverted runtime RevertData.typeMismatch)
      | Stmt.storageAliasAssignFromPath name source extraIndexes =>
          match runtime.lookupStoragePathRef? source with
          | some (target, indexes) => do
              match ←
                (Expr.evalListWithRuntimeOrder context.effectiveChildEvalOrder
                  context runtime extraIndexes).caught
              with
              | Except.ok (extraIndexValues, runtime') =>
                  match
                    runtime'.assignStoragePathRef? name target
                      (indexes ++ extraIndexValues)
                  with
                  | some updated => pure (Result.normal updated)
                  | none => pure (Result.reverted runtime RevertData.typeMismatch)
              | Except.error err => pure (Result.reverted runtime err)
          | none => pure (Result.reverted runtime RevertData.typeMismatch)
      | Stmt.exprStmt expr => do
          match ← (Expr.evalWithRuntimeOrder context.effectiveChildEvalOrder
              context runtime expr).caught with
          | Except.ok (_, runtime') => pure (Result.normal runtime')
          | Except.error err => pure (Result.reverted runtime err)
      | Stmt.assign target expr =>
          let writeAssigned
              (resolved : ResolvedLValue) (value : Value)
              (runtime' : Runtime) : SolI Result :=
            match resolved.write context runtime' value with
            | Except.ok updated => pure (Result.normal updated)
            | Except.error err => pure (Result.reverted runtime err)
          let evalTargetThenRhs : SolI Result := do
            match ← (target.resolveWithRuntime context runtime).caught with
            | Except.ok (resolved, runtime') =>
                match ← (Expr.evalWithRuntimeOrder context.effectiveChildEvalOrder
                    context runtime' expr).caught with
                | Except.ok (value, runtime'') =>
                    writeAssigned resolved value runtime''
                | Except.error err => pure (Result.reverted runtime err)
            | Except.error err => pure (Result.reverted runtime err)
          let evalRhsThenTarget : SolI Result := do
            match ← (Expr.evalWithRuntimeOrder context.effectiveChildEvalOrder
                context runtime expr).caught with
            | Except.ok (value, runtime') =>
                match ← (target.resolveWithRuntime context runtime').caught with
                | Except.ok (resolved, runtime'') =>
                    writeAssigned resolved value runtime''
                | Except.error err => pure (Result.reverted runtime err)
            | Except.error err => pure (Result.reverted runtime err)
          match target, expr with
          | LValue.var name, Expr.var source =>
              match runtime.lookupMemoryRef? name,
                  runtime.lookupMemoryRef? source with
              | some _, some sourceId =>
                  match
                    runtime.assignLocalRaw? name (Value.memoryRef sourceId)
                  with
                  | some updated => pure (Result.normal updated)
                  | none =>
                      pure (Result.reverted runtime RevertData.typeMismatch)
              | _, _ =>
                  match context.effectiveChildEvalOrder with
                  | ChildEvalOrder.leftToRight => evalTargetThenRhs
                  | ChildEvalOrder.rightToLeft => evalRhsThenTarget
          | _, _ =>
              match context.effectiveChildEvalOrder with
              | ChildEvalOrder.leftToRight => evalTargetThenRhs
              | ChildEvalOrder.rightToLeft => evalRhsThenTarget
      | Stmt.assignTuple targets expr => do
          match ← (Expr.evalWithRuntimeOrder context.effectiveChildEvalOrder
              context runtime expr).caught with
          | Except.ok (Value.tuple values, runtime') =>
              match ← (LValues.writeTupleWithRuntime context runtime' targets
                  values).caught with
              | Except.ok updated => pure (Result.normal updated)
              | Except.error err => pure (Result.reverted runtime err)
          | Except.ok _ => pure (Result.reverted runtime RevertData.typeMismatch)
          | Except.error err => pure (Result.reverted runtime err)
      | Stmt.assignOp target op expr =>
          let writeApplied
              (resolved : ResolvedLValue) (lhs rhs : Value)
              (runtime' : Runtime) : SolI Result :=
            match BinaryOp.apply context.checked op lhs rhs with
            | Except.ok value =>
                match resolved.write context runtime' value with
                | Except.ok updated => pure (Result.normal updated)
                | Except.error err => pure (Result.reverted runtime err)
            | Except.error err => pure (Result.reverted runtime err)
          let evalTargetThenRhs : SolI Result := do
            match ← (target.resolveWithRuntime context runtime).caught with
            | Except.ok (resolved, runtime') =>
                match resolved.read context runtime' with
                | Except.ok lhs =>
                    match ← (Expr.evalWithRuntimeOrder context.effectiveChildEvalOrder
                        context runtime' expr).caught with
                    | Except.ok (rhs, runtime'') =>
                        writeApplied resolved lhs rhs runtime''
                    | Except.error err => pure (Result.reverted runtime err)
                | Except.error err => pure (Result.reverted runtime err)
            | Except.error err => pure (Result.reverted runtime err)
          let evalRhsThenTarget : SolI Result := do
            match ← (Expr.evalWithRuntimeOrder context.effectiveChildEvalOrder
                context runtime expr).caught with
            | Except.ok (rhs, runtime') =>
                match ← (target.resolveWithRuntime context runtime').caught with
                | Except.ok (resolved, runtime'') =>
                    match resolved.read context runtime'' with
                    | Except.ok lhs =>
                        writeApplied resolved lhs rhs runtime''
                    | Except.error err => pure (Result.reverted runtime err)
                | Except.error err => pure (Result.reverted runtime err)
            | Except.error err => pure (Result.reverted runtime err)
          match context.effectiveChildEvalOrder with
          | ChildEvalOrder.leftToRight => evalTargetThenRhs
          | ChildEvalOrder.rightToLeft => evalRhsThenTarget
      | Stmt.assignOpCleanup target op expr cleanup =>
          let writeApplied
              (resolved : ResolvedLValue) (lhs rhs : Value)
              (runtime' : Runtime) : SolI Result :=
            match BinaryOp.apply context.checked op lhs rhs with
            | Except.ok value =>
                match cleanup.apply context.checked value with
                | Except.ok cleaned =>
                    match resolved.write context runtime' cleaned with
                    | Except.ok updated => pure (Result.normal updated)
                    | Except.error err => pure (Result.reverted runtime err)
                | Except.error err => pure (Result.reverted runtime err)
            | Except.error err => pure (Result.reverted runtime err)
          let evalTargetThenRhs : SolI Result := do
            match ← (target.resolveWithRuntime context runtime).caught with
            | Except.ok (resolved, runtime') =>
                match resolved.read context runtime' with
                | Except.ok lhs =>
                    match ← (Expr.evalWithRuntimeOrder context.effectiveChildEvalOrder
                        context runtime' expr).caught with
                    | Except.ok (rhs, runtime'') =>
                        writeApplied resolved lhs rhs runtime''
                    | Except.error err => pure (Result.reverted runtime err)
                | Except.error err => pure (Result.reverted runtime err)
            | Except.error err => pure (Result.reverted runtime err)
          let evalRhsThenTarget : SolI Result := do
            match ← (Expr.evalWithRuntimeOrder context.effectiveChildEvalOrder
                context runtime expr).caught with
            | Except.ok (rhs, runtime') =>
                match ← (target.resolveWithRuntime context runtime').caught with
                | Except.ok (resolved, runtime'') =>
                    match resolved.read context runtime'' with
                    | Except.ok lhs =>
                        writeApplied resolved lhs rhs runtime''
                    | Except.error err => pure (Result.reverted runtime err)
                | Except.error err => pure (Result.reverted runtime err)
            | Except.error err => pure (Result.reverted runtime err)
          match context.effectiveChildEvalOrder with
          | ChildEvalOrder.leftToRight => evalTargetThenRhs
          | ChildEvalOrder.rightToLeft => evalRhsThenTarget
      | Stmt.deleteValue target =>
          match target with
          | LValue.storage name =>
              match runtime.deleteStorageField context name with
              | Except.ok updated => pure (Result.normal updated)
              | Except.error err => pure (Result.reverted runtime err)
          | LValue.var name =>
              match runtime.lookupStoragePathRef? name with
              | some _ =>
                  pure (Result.reverted runtime RevertData.typeMismatch)
              | none => do
                  match ← (target.resolveWithRuntime context runtime).caught with
                  | Except.ok (resolved, runtime') =>
                      match resolved.delete context runtime' with
                      | Except.ok updated => pure (Result.normal updated)
                      | Except.error err => pure (Result.reverted runtime err)
                  | Except.error err => pure (Result.reverted runtime err)
          | _ => do
              match ← (target.resolveWithRuntime context runtime).caught with
              | Except.ok (resolved, runtime') =>
                  match resolved.delete context runtime' with
                  | Except.ok updated => pure (Result.normal updated)
                  | Except.error err => pure (Result.reverted runtime err)
              | Except.error err => pure (Result.reverted runtime err)
      | Stmt.storageArrayPush name value? =>
          match value? with
          | some expr => do
              match ← (Expr.evalWithRuntimeOrder context.effectiveChildEvalOrder
                  context runtime expr).caught with
              | Except.ok (value, runtime') =>
                  match runtime'.storageArrayPush context name (some value) with
                  | Except.ok updated => pure (Result.normal updated)
                  | Except.error err => pure (Result.reverted runtime err)
              | Except.error err => pure (Result.reverted runtime err)
          | none =>
              match runtime.storageArrayPush context name none with
              | Except.ok updated => pure (Result.normal updated)
              | Except.error err => pure (Result.reverted runtime err)
      | Stmt.storageArrayPushRef name value? =>
          match runtime.lookupStoragePathRef? name, value? with
          | some (target, indexes), some expr => do
              match ← (Expr.evalWithRuntimeOrder context.effectiveChildEvalOrder
                  context runtime expr).caught with
              | Except.ok (value, runtime') =>
                  match
                    runtime'.storageArrayPushPath context target indexes
                      (some value)
                  with
                  | Except.ok updated => pure (Result.normal updated)
                  | Except.error err => pure (Result.reverted runtime err)
              | Except.error err => pure (Result.reverted runtime err)
          | some (target, indexes), none =>
              match runtime.storageArrayPushPath context target indexes none with
              | Except.ok updated => pure (Result.normal updated)
              | Except.error err => pure (Result.reverted runtime err)
          | none, _ => pure (Result.reverted runtime RevertData.typeMismatch)
      | Stmt.storageArrayPushRefPath name extraIndexes value? =>
          match runtime.lookupStoragePathRef? name with
          | some (target, indexes) => do
              match ←
                (Expr.evalListWithRuntimeOrder context.effectiveChildEvalOrder
                  context runtime extraIndexes).caught
              with
              | Except.ok (extraIndexValues, runtime') =>
                  let allIndexes := indexes ++ extraIndexValues
                  match value? with
                  | some expr =>
                      match ← (Expr.evalWithRuntimeOrder
                          context.effectiveChildEvalOrder context runtime'
                          expr).caught with
                      | Except.ok (value, runtime'') =>
                          match
                            runtime''.storageArrayPushPath context target
                              allIndexes (some value)
                          with
                          | Except.ok updated => pure (Result.normal updated)
                          | Except.error err =>
                              pure (Result.reverted runtime err)
                      | Except.error err => pure (Result.reverted runtime' err)
                  | none =>
                      match
                        runtime'.storageArrayPushPath context target
                          allIndexes none
                      with
                      | Except.ok updated => pure (Result.normal updated)
                      | Except.error err => pure (Result.reverted runtime err)
              | Except.error err => pure (Result.reverted runtime err)
          | none => pure (Result.reverted runtime RevertData.typeMismatch)
      | Stmt.storageArrayPushPath name indexes value? => do
          match ← (Expr.evalListWithRuntimeOrder context.effectiveChildEvalOrder
              context runtime indexes).caught with
          | Except.ok (indexValues, runtime') =>
              match value? with
              | some expr =>
                  match ← (Expr.evalWithRuntimeOrder
                      context.effectiveChildEvalOrder context runtime'
                      expr).caught with
                  | Except.ok (value, runtime'') =>
                      match
                        runtime''.storageArrayPushPath context name indexValues
                          (some value)
                      with
                      | Except.ok updated => pure (Result.normal updated)
                      | Except.error err => pure (Result.reverted runtime err)
                  | Except.error err => pure (Result.reverted runtime' err)
              | none =>
                  match
                    runtime'.storageArrayPushPath context name indexValues none
                  with
                  | Except.ok updated => pure (Result.normal updated)
                  | Except.error err => pure (Result.reverted runtime err)
          | Except.error err => pure (Result.reverted runtime err)
      | Stmt.storageArrayPushPathAssign name indexes rhs => do
          match ← (Expr.evalListWithRuntimeOrder context.effectiveChildEvalOrder
              context runtime indexes).caught with
          | Except.ok (indexValues, runtime') =>
              match runtime'.storageArrayPushPath context name indexValues none with
              | Except.ok pushed => do
                  match ← (Expr.evalWithRuntimeOrder
                      context.effectiveChildEvalOrder context pushed rhs).caught with
                  | Except.ok (value, runtime'') =>
                      match
                        runtime''.loadStorageRefPathValue
                          context name indexValues
                      with
                      | Except.ok container =>
                          match container.storageArrayLength? with
                          | some length =>
                              let last := length - 1
                              match
                                runtime''.storeStoragePathWithDeepClear
                                  context name
                                  (indexValues ++ [Value.word last])
                                  value
                              with
                              | Except.ok updated =>
                                  pure (Result.normal updated)
                              | Except.error err =>
                                  pure (Result.reverted runtime'' err)
                          | none =>
                              pure
                                (Result.reverted runtime''
                                  RevertData.typeMismatch)
                      | Except.error err =>
                          pure (Result.reverted runtime'' err)
                  | Except.error err => pure (Result.reverted pushed err)
              | Except.error err => pure (Result.reverted runtime err)
          | Except.error err => pure (Result.reverted runtime err)
      | Stmt.storageArrayPushRefPathAssign name extraIndexes rhs =>
          match runtime.lookupStoragePathRef? name with
          | some (target, indexes) => do
              match ←
                (Expr.evalListWithRuntimeOrder context.effectiveChildEvalOrder
                  context runtime extraIndexes).caught
              with
              | Except.ok (extraIndexValues, runtime') =>
                  let allIndexes := indexes ++ extraIndexValues
                  match
                    runtime'.storageArrayPushPath context target allIndexes none
                  with
                  | Except.ok pushed => do
                      match ← (Expr.evalWithRuntimeOrder
                          context.effectiveChildEvalOrder context pushed
                          rhs).caught with
                      | Except.ok (value, runtime'') =>
                          match
                            runtime''.loadStorageRefPathValue
                              context target allIndexes
                          with
                          | Except.ok container =>
                              match container.storageArrayLength? with
                              | some length =>
                                  let last := length - 1
                                  match
                                    runtime''.storeStoragePathWithDeepClear
                                      context target
                                      (allIndexes ++ [Value.word last])
                                      value
                                  with
                                  | Except.ok updated =>
                                      pure (Result.normal updated)
                                  | Except.error err =>
                                      pure (Result.reverted runtime'' err)
                              | none =>
                                  pure
                                    (Result.reverted runtime''
                                      RevertData.typeMismatch)
                          | Except.error err =>
                              pure (Result.reverted runtime'' err)
                      | Except.error err => pure (Result.reverted pushed err)
                  | Except.error err => pure (Result.reverted runtime' err)
              | Except.error err => pure (Result.reverted runtime err)
          | none => pure (Result.reverted runtime RevertData.typeMismatch)
      | Stmt.storageArrayPop name =>
          match runtime.storageArrayPop context name with
          | Except.ok updated => pure (Result.normal updated)
          | Except.error err => pure (Result.reverted runtime err)
      | Stmt.storageArrayPopRef name =>
          match runtime.lookupStoragePathRef? name with
          | some (target, indexes) =>
              match runtime.storageArrayPopPath context target indexes with
              | Except.ok updated => pure (Result.normal updated)
              | Except.error err => pure (Result.reverted runtime err)
          | none => pure (Result.reverted runtime RevertData.typeMismatch)
      | Stmt.storageArrayPopRefPath name extraIndexes =>
          match runtime.lookupStoragePathRef? name with
          | some (target, indexes) => do
              match ←
                (Expr.evalListWithRuntimeOrder context.effectiveChildEvalOrder
                  context runtime extraIndexes).caught
              with
              | Except.ok (extraIndexValues, runtime') =>
                  match
                    runtime'.storageArrayPopPath context target
                      (indexes ++ extraIndexValues)
                  with
                  | Except.ok updated => pure (Result.normal updated)
                  | Except.error err => pure (Result.reverted runtime err)
              | Except.error err => pure (Result.reverted runtime err)
          | none => pure (Result.reverted runtime RevertData.typeMismatch)
      | Stmt.storageArrayPopPath name indexes => do
          match ← (Expr.evalListWithRuntimeOrder context.effectiveChildEvalOrder
              context runtime indexes).caught with
          | Except.ok (indexValues, runtime') =>
              match runtime'.storageArrayPopPath context name indexValues with
              | Except.ok updated => pure (Result.normal updated)
              | Except.error err => pure (Result.reverted runtime err)
          | Except.error err => pure (Result.reverted runtime err)
      | Stmt.panic code =>
          pure (Result.reverted runtime (RevertData.panic code))
      | Stmt.assertStmt cond => do
          match ← (Expr.evalWithRuntimeOrder context.effectiveChildEvalOrder
              context runtime cond).caught with
          | Except.ok (value, runtime') =>
              match value.expectWord with
              | Except.ok word =>
                  if wordTruthy word then
                    pure (Result.normal runtime')
                  else
                    pure (Result.reverted runtime' RevertData.assertFailure)
              | Except.error err => pure (Result.reverted runtime' err)
          | Except.error err => pure (Result.reverted runtime err)
      | Stmt.requireStmt cond reason => do
          match ← (Expr.evalWithRuntimeOrder context.effectiveChildEvalOrder
              context runtime cond).caught with
          | Except.ok (value, runtime') =>
              match value.expectWord with
              | Except.ok word =>
                  if wordTruthy word then
                    pure (Result.normal runtime')
                  else
                    match reason with
                    | some message =>
                        pure (Result.reverted runtime' (RevertData.error message))
                    | none =>
                        pure (Result.reverted runtime' RevertData.empty)
              | Except.error err => pure (Result.reverted runtime' err)
          | Except.error err => pure (Result.reverted runtime err)
      | Stmt.requireErrorExpr cond reasonExpr => do
          match ← (Expr.evalWithRuntimeOrder context.effectiveChildEvalOrder
              context runtime cond).caught with
          | Except.ok (value, runtime') =>
              match ← (Expr.evalWithRuntimeOrder context.effectiveChildEvalOrder
                  context runtime' reasonExpr).caught with
              | Except.ok (reasonValue, runtime'') =>
                  match value.expectWord with
                  | Except.ok word =>
                      if wordTruthy word then
                        pure (Result.normal runtime'')
                      else
                        match errorStringBytesRevert? reasonValue with
                        | some payload =>
                            pure (Result.reverted runtime'' payload)
                        | none =>
                            pure (Result.reverted runtime''
                              RevertData.typeMismatch)
                  | Except.error err => pure (Result.reverted runtime'' err)
              | Except.error err => pure (Result.reverted runtime' err)
          | Except.error err => pure (Result.reverted runtime err)
      | Stmt.requireCustom cond name exprs => do
          match ← (Expr.evalWithRuntimeOrder context.effectiveChildEvalOrder
              context runtime cond).caught with
          | Except.ok (value, runtime') =>
              match ← (Expr.evalListWithRuntimeOrder context.effectiveChildEvalOrder
                  context runtime' exprs).caught with
              | Except.ok (args, runtime'') =>
                  match value.expectWord with
                  | Except.ok word =>
                      if wordTruthy word then
                        pure (Result.normal runtime'')
                      else
                        pure
                          (Result.reverted runtime''
                            (RevertData.custom name args))
                  | Except.error err => pure (Result.reverted runtime'' err)
              | Except.error err => pure (Result.reverted runtime' err)
          | Except.error err => pure (Result.reverted runtime err)
      | Stmt.captureReturn returnNames body => do
          match ← Stmt.eval fuel table context runtime body with
          | Result.returned runtime' values =>
              if values.isEmpty || returnNames.isEmpty then
                pure (Result.normal runtime')
              else
                match runtime'.assignNamedValues? returnNames values with
                | some updated => pure (Result.normal updated)
                | none => pure (Result.reverted runtime' RevertData.typeMismatch)
          | result => pure result
      | Stmt.internalCall targets callee args => do
          -- In-monad framed internal call (no query emitted; transcript
          -- invariant). See `docs/function-boundary-refactor-plan.md` §3.1.
          match ← (Expr.evalListWithRuntimeOrder context.effectiveChildEvalOrder
              context runtime args).caught with
          | Except.error err => pure (Result.reverted runtime err)
          | Except.ok (argValues, runtime') =>
              match table.lookup? callee with
              | none => pure (Result.reverted runtime' RevertData.typeMismatch)
              | some fn =>
                  match fn.initialFrame? argValues with
                  | none => pure (Result.reverted runtime' RevertData.typeMismatch)
                  | some frame =>
                      -- Frame isolation: REPLACE locals (not pushScope); state
                      -- (storage/memory/events/transient) is shared. Checked-ness
                      -- is lexical per function in Solidity: the callee body
                      -- starts CHECKED regardless of the caller's enclosing
                      -- checked/unchecked block (its own `Stmt.unchecked` nodes
                      -- opt out locally) — the splice era guaranteed this by
                      -- wrapping callee bodies in `Stmt.checked`.
                      let savedLocals := runtime'.locals
                      let calleeRuntime := { runtime' with locals := [frame] }
                      match ← Stmt.eval fuel table { context with checked := true }
                          calleeRuntime fn.body with
                      | Result.returned r values =>
                          -- Map exactly as `FunctionDef.callBodyResult` (R3):
                          -- bare `return;` (empty) collects named returns;
                          -- explicit values are coerced to declared returns.
                          match
                            (if values.isEmpty then
                                collectReturnBindings fn.returns r
                              else
                                coerceReturnBindings fn.returns r values)
                          with
                          | Except.ok values =>
                              internalCallAssign
                                { r with locals := savedLocals } targets values
                          | Except.error err => pure (Result.reverted r err)
                      | Result.normal r =>
                          match collectReturnBindings fn.returns r with
                          | Except.ok values =>
                              internalCallAssign
                                { r with locals := savedLocals } targets values
                          | Except.error err => pure (Result.reverted r err)
                      | Result.selfdestructed r =>
                          -- Halts the whole external frame; propagate until the
                          -- entry `callBodyResult` maps it to `returned []`.
                          pure (Result.selfdestructed r)
                      | Result.reverted r err =>
                          -- Propagate; rollback happens at the entry snapshot.
                          pure (Result.reverted r err)
                      | Result.broke r =>
                          -- A callee cannot break the caller's loop; fixes the
                          -- latent `captureReturn` passthrough (§1.2 / R3).
                          pure (Result.reverted r RevertData.typeMismatch)
                      | Result.continued r =>
                          pure (Result.reverted r RevertData.typeMismatch)
      | Stmt.ifElse cond thenBranch elseBranch => do
          match ← (Expr.evalWithRuntimeOrder context.effectiveChildEvalOrder
              context runtime cond).caught with
          | Except.ok (value, runtime') =>
              match value.expectWord with
              | Except.ok word =>
                  if wordTruthy word then
                    Stmt.eval fuel table context runtime' thenBranch
                  else
                    Stmt.eval fuel table context runtime' elseBranch
              | Except.error err => pure (Result.reverted runtime' err)
          | Except.error err => pure (Result.reverted runtime err)
      | Stmt.switch discr cases defaultBranch => do
          match ← (Expr.evalWithRuntimeOrder context.effectiveChildEvalOrder
              context runtime discr).caught with
          | Except.ok (value, runtime') =>
              match value.expectWord with
              | Except.ok word =>
                  match Stmt.findSwitchBranch? word cases, defaultBranch with
                  | some branch, _ => Stmt.eval fuel table context runtime' branch
                  | none, some branch => Stmt.eval fuel table context runtime' branch
                  | none, none => pure (Result.normal runtime')
              | Except.error err => pure (Result.reverted runtime' err)
          | Except.error err => pure (Result.reverted runtime err)
      | Stmt.whileLoop cond body =>
          Stmt.evalWhile fuel table context runtime cond body
      | Stmt.doWhile body cond =>
          Stmt.evalDoWhile fuel table context runtime body cond
      | Stmt.forLoop init cond post body => do
          let loopRuntime := runtime.pushScope
          match ← Stmt.eval fuel table context loopRuntime init with
          | Result.normal initialized =>
              let result ← Stmt.evalFor fuel table context initialized cond post body
              pure (result.mapRuntime Runtime.popScope)
          | result => pure (result.mapRuntime Runtime.popScope)
        | Stmt.tryExternalCall kind targetExpr calldataExpr valueExpr
            gasExpr? gasFirst checkTargetCode returns returnAbiCleanups successBody
            catchClauses =>
            match targetExpr.evalWithRuntimeByContext context runtime with
            | Except.ok (targetValue, runtime') =>
                match targetValue.expectWord with
                | Except.ok target =>
                    match calldataExpr.evalWithRuntimeByContext context runtime' with
                    | Except.ok (calldataValue, runtime'') =>
                        match calldataValue.asBytes? with
                        | some calldata =>
                            let valueGasResult? :
                                Except (Runtime × RevertData)
                                  (Word × Option Word × Runtime) :=
                              match gasExpr? with
                              | none =>
                                  match valueExpr.evalWithRuntimeByContext context runtime'' with
                                  | Except.ok (valueValue, runtimeValue) =>
                                      match valueValue.expectWord with
                                      | Except.ok value =>
                                          Except.ok (value, none, runtimeValue)
                                      | Except.error err =>
                                          Except.error (runtimeValue, err)
                                  | Except.error err =>
                                      Except.error (runtime'', err)
                              | some gasExpr =>
                                  if gasFirst then
                                    match gasExpr.evalWithRuntimeByContext context runtime'' with
                                    | Except.ok (gasValue, runtimeGas) =>
                                        match gasValue.expectWord with
                                        | Except.ok gas =>
                                            match valueExpr.evalWithRuntimeByContext
                                                context runtimeGas with
                                            | Except.ok
                                                (valueValue, runtimeValue) =>
                                                match valueValue.expectWord with
                                                | Except.ok value =>
                                                    Except.ok
                                                      (value, some gas,
                                                        runtimeValue)
                                                | Except.error err =>
                                                    Except.error
                                                      (runtimeValue, err)
                                            | Except.error err =>
                                                Except.error (runtimeGas, err)
                                        | Except.error err =>
                                            Except.error (runtimeGas, err)
                                    | Except.error err =>
                                        Except.error (runtime'', err)
                                  else
                                    match valueExpr.evalWithRuntimeByContext
                                        context runtime'' with
                                    | Except.ok (valueValue, runtimeValue) =>
                                        match valueValue.expectWord with
                                        | Except.ok value =>
                                            match gasExpr.evalWithRuntimeByContext
                                                context runtimeValue with
                                            | Except.ok (gasValue, runtimeGas) =>
                                                match gasValue.expectWord with
                                                | Except.ok gas =>
                                                    Except.ok
                                                      (value, some gas,
                                                        runtimeGas)
                                                | Except.error err =>
                                                    Except.error
                                                      (runtimeGas, err)
                                            | Except.error err =>
                                                Except.error
                                                  (runtimeValue, err)
                                        | Except.error err =>
                                            Except.error (runtimeValue, err)
                                    | Except.error err =>
                                        Except.error (runtime'', err)
                            match valueGasResult? with
                            | Except.ok (value, gas?, runtime''') => do
                                    let missingCode :=
                                      checkTargetCode &&
                                        !(context.accountHasCode target)
                                    let callResult ←
                                      if missingCode then
                                        pure (LowLevelCallResult.failedRequest
                                          kind target calldata value gas?)
                                      else
                                        emitLowLevelCall context
                                          kind target calldata value gas?
                                    let runtimeWithInteraction :=
                                      runtime'''.recordExternalInteraction
                                        (ExternalInteraction.lowLevelCall
                                          callResult)
                                    let success := callResult.success
                                    let output := callResult.output.map normByte
                                    if success then
                                      match abiDecodeValues?
                                          (returns.map BindingDecl.ty) output with
                                        | some decoded =>
                                            if AbiCleanups.acceptOrUnspecified
                                                returnAbiCleanups decoded then
                                              match BindingDecl.bindArgs?
                                                  returns decoded with
                                              | some frame => do
                                                  let result ← Stmt.eval fuel table context
                                                      (runtimeWithInteraction.withFrame
                                                        frame)
                                                      successBody
                                                  pure
                                                    (result.mapRuntime
                                                      Runtime.popScope)
                                              | none =>
                                                  pure
                                                    (Result.reverted
                                                      runtimeWithInteraction
                                                      RevertData.typeMismatch)
                                            else
                                                pure
                                                  (Result.reverted
                                                    runtimeWithInteraction
                                                    RevertData.empty)
                                        | none =>
                                            pure
                                              (Result.reverted
                                                runtimeWithInteraction
                                                RevertData.empty)
                                    else
                                        match TryCatchClause.findMatch?
                                            output catchClauses with
                                        | some (frame, body) => do
                                            let result ← Stmt.eval fuel table context
                                                (runtimeWithInteraction.withFrame
                                                  frame) body
                                            pure
                                              (result.mapRuntime
                                                Runtime.popScope)
                                        | none =>
                                            pure
                                              (Result.reverted
                                                runtimeWithInteraction
                                                (RevertData.fromRawBytes output))
                            | Except.error (runtimeFailed, err) =>
                                pure (Result.reverted runtimeFailed err)
                        | none =>
                            pure (Result.reverted runtime'' RevertData.typeMismatch)
                    | Except.error err => pure (Result.reverted runtime' err)
                | Except.error err => pure (Result.reverted runtime' err)
            | Except.error err => pure (Result.reverted runtime err)
        | Stmt.tryContractCreate contractName constructorArgsExpr valueExpr
            saltExpr? returns successBody catchClauses =>
            match constructorArgsExpr.evalWithRuntimeByContext context runtime with
            | Except.ok (argsValue, runtime') =>
                match argsValue.asBytes? with
                | some constructorArgs =>
                    match valueExpr.evalWithRuntimeByContext context runtime' with
                    | Except.ok (valueValue, runtime'') =>
                        match valueValue.expectWord with
                        | Except.ok value =>
                            let saltResult? :
                                Except RevertData (Option Word × Runtime) :=
                              match saltExpr? with
                              | some saltExpr => do
                                  let (saltValue, runtime''') ←
                                    saltExpr.evalWithRuntimeByContext context runtime''
                                  let salt ← saltValue.expectWord
                                  Except.ok (some salt, runtime''')
                              | none => Except.ok (none, runtime'')
                            match saltResult? with
                            | Except.ok (salt?, runtime''') =>
                                emitContractCreation context
                                    contractName constructorArgs value salt? >>=
                                  fun createResult =>
                              let runtimeWithInteraction :=
                                runtime'''.recordExternalInteraction
                                  (ExternalInteraction.contractCreation
                                    createResult)
                              let success := createResult.success
                              let output := createResult.output.map normByte
                              if success then
                                let address := createResult.address
                                let values :=
                                  if returns.isEmpty then
                                    []
                                  else
                                    [Value.word address]
                                match BindingDecl.bindArgs? returns values with
                                | some frame => do
                                    let result ← Stmt.eval fuel table context
                                          (runtimeWithInteraction.withFrame frame)
                                          successBody
                                    pure
                                      (result.mapRuntime
                                        Runtime.popScope)
                                  | none =>
                                      pure
                                        (Result.reverted runtimeWithInteraction
                                          RevertData.typeMismatch)
                                else
                                  match TryCatchClause.findMatch?
                                      output catchClauses with
                                  | some (frame, body) => do
                                      let result ← Stmt.eval fuel table context
                                          (runtimeWithInteraction.withFrame frame)
                                          body
                                      pure
                                        (result.mapRuntime
                                          Runtime.popScope)
                                  | none =>
                                      pure
                                        (Result.reverted runtimeWithInteraction
                                          (RevertData.fromRawBytes output))
                            | Except.error err =>
                                pure (Result.reverted runtime'' err)
                        | Except.error err => pure (Result.reverted runtime'' err)
                    | Except.error err => pure (Result.reverted runtime' err)
                | none =>
                    pure (Result.reverted runtime' RevertData.typeMismatch)
            | Except.error err => pure (Result.reverted runtime err)
      | Stmt.break => pure (Result.broke runtime)
      | Stmt.continue => pure (Result.continued runtime)
      | Stmt.returnValues exprs => do
          match ← (Expr.evalReturnListWithRuntimeOrder
              context.effectiveChildEvalOrder context runtime exprs).caught with
          | Except.ok (values, runtime') =>
              pure (Result.returned runtime' values)
          | Except.error err => pure (Result.reverted runtime err)
      | Stmt.revertError reason =>
          match reason with
          | some message =>
              pure (Result.reverted runtime (RevertData.error message))
          | none =>
              pure (Result.reverted runtime RevertData.empty)
      | Stmt.revertErrorExpr reasonExpr => do
          match ← (Expr.evalWithRuntimeOrder context.effectiveChildEvalOrder
              context runtime reasonExpr).caught with
          | Except.ok (reasonValue, runtime') =>
              match errorStringBytesRevert? reasonValue with
              | some payload =>
                  pure (Result.reverted runtime' payload)
              | none =>
                  pure (Result.reverted runtime' RevertData.typeMismatch)
          | Except.error err => pure (Result.reverted runtime err)
      | Stmt.revert name exprs => do
          match ← (Expr.evalListWithRuntimeOrder context.effectiveChildEvalOrder
              context runtime exprs).caught with
          | Except.ok (values, runtime') =>
              pure (Result.reverted runtime' (RevertData.custom name values))
          | Except.error err => pure (Result.reverted runtime err)
      | Stmt.emitEvent name exprs => do
          match ← (Expr.evalListWithRuntimeOrder context.effectiveChildEvalOrder
              context runtime exprs).caught with
          | Except.ok (values, runtime') =>
              match runtime'.emitEvent context name values with
              | Except.ok updated => pure (Result.normal updated)
              | Except.error err => pure (Result.reverted runtime err)
          | Except.error err => pure (Result.reverted runtime err)
      | Stmt.selfdestruct recipientExpr => do
          match ← (Expr.evalWithRuntimeOrder context.effectiveChildEvalOrder
              context runtime recipientExpr).caught with
          | Except.ok (recipientValue, runtime') =>
              match recipientValue.expectWord with
              | Except.ok recipient =>
                  pure
                    (Result.selfdestructed
                      { runtime' with
                        state :=
                          runtime'.state.recordSelfdestruct
                            context.evmVersion
                            context.createdInTransactionAccounts
                            context.self recipient })
              | Except.error err => pure (Result.reverted runtime' err)
          | Except.error err => pure (Result.reverted runtime err)
      | Stmt.checked body =>
          Stmt.eval fuel table { context with checked := true } runtime body
      | Stmt.unchecked body =>
          Stmt.eval fuel table { context with checked := false } runtime body

def Stmt.evalList (fuel : Nat) (table : FunctionTable) (context : Context)
    (runtime : Runtime) : List Stmt -> SolI Result
  | [] => pure (Result.normal runtime)
  | stmt :: rest => do
      match ← Stmt.eval fuel table context runtime stmt with
      | Result.normal runtime' =>
          Stmt.evalList fuel table context runtime' rest
      | result => pure result

def Stmt.evalWhile (fuel : Nat) (table : FunctionTable) (context : Context)
    (runtime : Runtime) (cond : Expr) (body : Stmt) :
    SolI Result :=
  match fuel with
  | 0 => throw SolidityFailure.outOfFuel
  | fuel + 1 => do
      match ← (Expr.evalWithRuntimeOrder context.effectiveChildEvalOrder
          context runtime cond).caught with
      | Except.ok (value, runtime') =>
          match value.expectWord with
          | Except.ok word =>
              if wordTruthy word then
                match ← Stmt.eval fuel table context runtime' body with
                | Result.normal runtime' =>
                    Stmt.evalWhile fuel table context runtime' cond body
                | Result.continued runtime' =>
                    Stmt.evalWhile fuel table context runtime' cond body
                | Result.broke runtime' =>
                    pure (Result.normal runtime')
                | result => pure result
              else
                pure (Result.normal runtime')
          | Except.error err => pure (Result.reverted runtime' err)
      | Except.error err => pure (Result.reverted runtime err)

def Stmt.evalDoWhile (fuel : Nat) (table : FunctionTable) (context : Context)
    (runtime : Runtime) (body : Stmt) (cond : Expr) :
    SolI Result :=
  match fuel with
  | 0 => throw SolidityFailure.outOfFuel
  | fuel + 1 => do
      match ← Stmt.eval fuel table context runtime body with
      | Result.normal runtime' =>
          match ← (Expr.evalWithRuntimeOrder context.effectiveChildEvalOrder
              context runtime' cond).caught with
          | Except.ok (value, runtime'') =>
              match value.expectWord with
              | Except.ok word =>
                  if wordTruthy word then
                    Stmt.evalDoWhile fuel table context runtime'' body cond
                  else
                    pure (Result.normal runtime'')
              | Except.error err => pure (Result.reverted runtime'' err)
          | Except.error err => pure (Result.reverted runtime' err)
      | Result.continued runtime' =>
          match ← (Expr.evalWithRuntimeOrder context.effectiveChildEvalOrder
              context runtime' cond).caught with
          | Except.ok (value, runtime'') =>
              match value.expectWord with
              | Except.ok word =>
                  if wordTruthy word then
                    Stmt.evalDoWhile fuel table context runtime'' body cond
                  else
                    pure (Result.normal runtime'')
              | Except.error err => pure (Result.reverted runtime'' err)
          | Except.error err => pure (Result.reverted runtime' err)
      | Result.broke runtime' =>
          pure (Result.normal runtime')
      | result => pure result

def Stmt.evalFor (fuel : Nat) (table : FunctionTable) (context : Context)
    (runtime : Runtime) (cond : Expr) (post : Stmt) (body : Stmt) :
    SolI Result :=
  match fuel with
  | 0 => throw SolidityFailure.outOfFuel
  | fuel + 1 => do
      match ← (Expr.evalWithRuntimeOrder context.effectiveChildEvalOrder
          context runtime cond).caught with
      | Except.ok (value, runtime') =>
          match value.expectWord with
          | Except.ok word =>
              if wordTruthy word then
                match ← Stmt.eval fuel table context runtime' body with
                | Result.normal runtime' =>
                    match ← Stmt.eval fuel table context runtime' post with
                    | Result.normal posted =>
                        Stmt.evalFor fuel table context posted cond post body
                    | result => pure result
                | Result.continued runtime' =>
                    match ← Stmt.eval fuel table context runtime' post with
                    | Result.normal posted =>
                        Stmt.evalFor fuel table context posted cond post body
                    | result => pure result
                | Result.broke runtime' =>
                    pure (Result.normal runtime')
                | result => pure result
              else
                pure (Result.normal runtime')
          | Except.error err => pure (Result.reverted runtime' err)
      | Except.error err => pure (Result.reverted runtime err)

end

structure FunctionDef where
  name : String
  selector? : Option Word
  payable : Bool := false
  params : List BindingDecl
  paramAbiCleanups : List AbiCleanup := []
  returns : List BindingDecl
  body : Stmt
  deriving Repr

inductive CallResult where
  | returned : State -> List Value -> CallResult
  | reverted : State -> RevertData -> CallResult
  deriving Repr

/-- The post-execution state carried by a call result (the plain replacement for
    the former `CallResult.observe`, whose observation state copied this state's
    fields verbatim). -/
def CallResult.resultState : CallResult -> State
  | CallResult.returned state _ => state
  | CallResult.reverted state _ => state

def CallResult.clearTransient : CallResult -> CallResult
  | CallResult.returned state values =>
      CallResult.returned state.clearTransient values
  | CallResult.reverted state revert =>
      CallResult.reverted state.clearTransient revert

def FunctionDef.acceptsValue (function : FunctionDef) (value : Word) : Bool :=
  function.payable || wordEq value 0

def FunctionDef.returnDefaultBindings (function : FunctionDef) : Frame :=
  function.returns.map BindingDecl.defaultBinding

def FunctionDef.initialFrame? (function : FunctionDef)
    (args : List Value) : Option Frame :=
  match BindingDecl.bindArgs? function.params args with
  | some params =>
      some (params ++ function.returnDefaultBindings)
  | none => none

def FunctionDef.entryInitialFrame? (function : FunctionDef)
    (context : Context) (args : List Value) : Option Frame :=
  if function.acceptsValue context.value then
    function.initialFrame? args
  else
    none

-- Return-value extraction is shared with the internal-call arm via
-- `collectReturnBindings`/`coerceReturnBindings` (single source of truth so the
-- entry mapping and the framed internal call cannot drift — refactor risk R3).
def FunctionDef.collectReturns (function : FunctionDef)
    (runtime : Runtime) : Except RevertData (List Value) :=
  collectReturnBindings function.returns runtime

def FunctionDef.coerceReturnValues (function : FunctionDef)
    (runtime : Runtime) (values : List Value) :
    Except RevertData (List Value) :=
  coerceReturnBindings function.returns runtime values

/-- Project the entry-only `FunctionDef` onto the evaluator-visible
    `InternalFunction` used as a `FunctionTable` key (drops `selector?`,
    `payable`, `paramAbiCleanups`). -/
def FunctionDef.toInternal (function : FunctionDef) : InternalFunction :=
  { name := function.name
    params := function.params
    returns := function.returns
    body := function.body }

def FunctionDef.callBodyResult (function : FunctionDef)
    (state : State) : Result -> CallResult
  | Result.normal runtime' =>
      match function.collectReturns runtime' with
      | Except.ok values => CallResult.returned runtime'.state values
      | Except.error err => CallResult.reverted state err
  | Result.returned runtime' values =>
      if values.isEmpty then
        match function.collectReturns runtime' with
        | Except.ok namedValues =>
            CallResult.returned runtime'.state namedValues
        | Except.error err => CallResult.reverted state err
      else
        match function.coerceReturnValues runtime' values with
        | Except.ok coerced => CallResult.returned runtime'.state coerced
        | Except.error err => CallResult.reverted state err
  | Result.selfdestructed runtime' =>
      CallResult.returned runtime'.state []
  | Result.reverted runtime' revert =>
      let _ := runtime'
      CallResult.reverted state revert
  | Result.broke runtime' =>
      let _ := runtime'
      CallResult.reverted state RevertData.typeMismatch
  | Result.continued runtime' =>
      let _ := runtime'
      CallResult.reverted state RevertData.typeMismatch

/-- Enter a function body. `none` means a *static* absence (value not accepted
    or arity/frame construction failed) — NOT an effect; the returned tree
    encodes execution. -/
def FunctionDef.evalBodyEntry (fuel : Nat) (table : FunctionTable)
    (context : Context)
    (function : FunctionDef) (state : State) (args : List Value) :
    Option (SolI Result) :=
  if function.acceptsValue context.value then
    match function.initialFrame? args with
    | some frame =>
        let runtime : Runtime := { state, locals := [frame] }
        some (Stmt.eval fuel table context runtime function.body)
    | none => none
  else
    some
      (pure (Result.reverted (Runtime.ofState state) RevertData.empty))

/-- Execute a function call as an interaction tree; `none` is static absence.
    `table` is the internal-linkage function table the body's `internalCall`
    nodes resolve against (§2.2). -/
def FunctionDef.call (fuel : Nat) (table : FunctionTable) (context : Context)
    (function : FunctionDef) (state : State) (args : List Value) :
    Option (SolI CallResult) :=
  (function.evalBodyEntry fuel table context state args).map
    (Functor.map (function.callBodyResult state))

/-- Frozen adapter: fold the call tree **fail-closed** under an empty responder
    (`SolI.runWith []`) to an `Option CallResult`. These entry points execute no
    external effects on the paths that reach them (no query is emitted), so
    folding fail-closed is behaviour-identical to the old `SolI.run context`
    fold today; the point is that a future fixture edit that routes an external
    call through a non-responder entry fails **loudly** (`.error (unmatched …)`
    → `none`) instead of silently continuing on a fail-open failed call. On the
    query-free paths `.error` can only be `.outOfFuel` by construction (reverts
    are caught into `Result.reverted` values below); both are matched totally. -/
def FunctionDef.call? (fuel : Nat) (table : FunctionTable) (context : Context)
    (function : FunctionDef) (state : State) (args : List Value) :
    Option CallResult :=
  (function.call fuel table context state args).bind fun tree =>
    match SolI.runWith [] tree with
    | .ok result => some result
    | .error _ => none

/-- Witness adapter: fold the call tree under a fail-open responder
    (`SolI.runFailOpen`) — rows answer matched requests, misses fail-open to
    the default (failure) answer, mirroring the retired context oracle. -/
-- `table` is last with a default so the ~24 external-effect witness call sites
-- (which pass no table) keep compiling. Correct while elaboration still splices
-- (stages 0–1: bodies contain no `internalCall` nodes, so the table is unused);
-- the stage-2 switch to node emission passes the real `contract.table` at the
-- sites whose bodies gain internal calls, guarded by the full replay.
def FunctionDef.callFailOpen? (fuel : Nat) (responder : ScriptedResponder)
    (context : Context) (function : FunctionDef) (state : State)
    (args : List Value) (table : FunctionTable := []) : Option CallResult :=
  (function.call fuel table context state args).bind fun tree =>
    match SolI.runFailOpen responder tree with
    | .ok result => some result
    | .error _ => none

inductive FunctionExitKind where
  | fallthroughNamedReturns
  | bareReturnCollectsNamedReturns
  | explicitReturnValues
  | selfdestructReturnsEmpty
  | revertRollsBack
  | invalidControlReverts
  deriving Repr, BEq

def FunctionExitKind.ofBodyResult : Result -> FunctionExitKind
  | Result.normal _ => FunctionExitKind.fallthroughNamedReturns
  | Result.returned _ values =>
      if values.isEmpty then
        FunctionExitKind.bareReturnCollectsNamedReturns
      else
        FunctionExitKind.explicitReturnValues
  | Result.selfdestructed _ => FunctionExitKind.selfdestructReturnsEmpty
  | Result.reverted _ _ => FunctionExitKind.revertRollsBack
  | Result.broke _ => FunctionExitKind.invalidControlReverts
  | Result.continued _ => FunctionExitKind.invalidControlReverts

def FunctionDef.callUnspecifiedResults (fuel : Nat) (table : FunctionTable)
    (context : Context)
    (function : FunctionDef) (state : State) (args : List Value) :
    List CallResult :=
  context.withUnspecifiedChildEvalOrders.filterMap
    (fun orderedContext =>
      function.call? fuel table orderedContext state args)

def FunctionDef.CallsUnspecified (fuel : Nat) (table : FunctionTable)
    (context : Context)
    (function : FunctionDef) (state : State) (args : List Value)
    (result : CallResult) : Prop :=
  function.call? fuel table
      (context.withChildEvalOrder ChildEvalOrder.yulCompatible)
      state args =
    some result

theorem FunctionDef.call?_reverted_rolls_back
    {fuel : Nat} {table : FunctionTable} {context : Context}
    {function : FunctionDef}
    {state : State} {args : List Value} {frame : Frame}
    {runtime : Runtime} {revert : RevertData}
    (hAccepts : function.acceptsValue context.value = true)
    (hFrame : function.initialFrame? args = some frame)
  (hEval :
      Stmt.eval fuel table context { state := state, locals := [frame] }
          function.body =
        pure (Result.reverted runtime revert)) :
    function.call? fuel table context state args =
      some (CallResult.reverted state revert) := by
  simp [FunctionDef.call?, FunctionDef.call, FunctionDef.evalBodyEntry,
    FunctionDef.callBodyResult, SolI.runWith, Functor.map, Pure.pure,
    EvmCompiler.Simulation.Interaction.pure,
    EvmCompiler.Simulation.Interaction.map,
    EvmCompiler.Simulation.Interaction.bind, hAccepts, hFrame, hEval]

structure Contract where
  storageFields : List StorageField := []
  immutableFields : List ImmutableField := []
  eventDecls : List EventDecl := []
  errorDecls : List ErrorDecl := []
  functions : List FunctionDef := []
  deriving Repr

def Contract.context (contract : Contract) : Context :=
  { storageFields := contract.storageFields
    immutableFields := contract.immutableFields
    eventDecls := contract.eventDecls
    checked := true
    construction := false
    calldata := []
    sender := 0
    value := 0
    self := 0
    accountBalances := []
    accountCodes := []
    accountCodehashes := []
    contractAddresses := []
    contractCreationCodes := []
    contractRuntimeCodes := []
    blockEnv := BlockEnv.empty
    txEnv := TxEnv.empty
    gasleft := 0 }

/-- The internal-linkage function table the evaluator threads into
    `Stmt.eval`: every function of the contract, projected onto its
    evaluator-visible `InternalFunction`. Contract-internal calls resolve
    against this by name (§2.2). Selector dispatch is unaffected — it reads
    `functions` directly (`findFunctionBySelector?`). -/
def Contract.table (contract : Contract) : FunctionTable :=
  contract.functions.map FunctionDef.toInternal

def Contract.findFunctionByName? (contract : Contract)
    (name : String) : Option FunctionDef :=
  contract.functions.find? (fun function => function.name == name)

def Contract.findCallableFunctionByName? (contract : Contract)
    (name : String) (args : List Value) : Option FunctionDef :=
  contract.functions.find? (fun function =>
    function.name == name && (function.initialFrame? args).isSome)

def Contract.findFunctionBySelector? (contract : Contract)
    (selector : Word) : Option FunctionDef :=
  contract.functions.find? (fun function =>
    match function.selector? with
    | some candidate => wordEq candidate selector
    | none => false)

inductive CallTarget where
  | name : String -> CallTarget
  | selector : Word -> CallTarget
  deriving Repr

def Contract.findFunction? (contract : Contract) :
    CallTarget -> Option FunctionDef
  | CallTarget.name name => contract.findFunctionByName? name
  | CallTarget.selector selector => contract.findFunctionBySelector? selector

def Contract.resolveCallFunction? (contract : Contract)
    (target : CallTarget) (args : List Value) : Option FunctionDef :=
  match target with
  | CallTarget.name name =>
      contract.findCallableFunctionByName? name args
  | CallTarget.selector selector =>
      contract.findFunctionBySelector? selector

/-- Execute a contract call as an interaction tree; `none` is static absence
    (function not resolvable). -/
def Contract.call (fuel : Nat) (contract : Contract)
    (target : CallTarget) (state : State) (args : List Value) :
    Option (SolI CallResult) :=
  match contract.resolveCallFunction? target args with
  | some function =>
      function.call fuel contract.table contract.context state args
  | none => none

/-- Frozen adapter: fold the contract-call tree **fail-closed** under an empty
    responder (`SolI.runWith []`; see `FunctionDef.call?`). -/
def Contract.call? (fuel : Nat) (contract : Contract)
    (target : CallTarget) (state : State) (args : List Value) :
    Option CallResult :=
  (contract.call fuel target state args).bind fun tree =>
    match SolI.runWith [] tree with
    | .ok result => some result
    | .error _ => none

/-- Transaction-scoped contract call as a tree: clear transient state before,
    and map `CallResult.clearTransient` over the resulting tree. -/
def Contract.callTransaction (fuel : Nat) (contract : Contract)
    (target : CallTarget) (state : State) (args : List Value) :
    Option (SolI CallResult) :=
  (Contract.call fuel contract target state.clearTransient args).map
    (Functor.map CallResult.clearTransient)

/-- Frozen adapter over `Contract.callTransaction`, fail-closed under an empty
    responder (`SolI.runWith []`; see `FunctionDef.call?`). -/
def Contract.callTransaction? (fuel : Nat) (contract : Contract)
    (target : CallTarget) (state : State) (args : List Value) :
    Option CallResult :=
  (contract.callTransaction fuel target state args).bind fun tree =>
    match SolI.runWith [] tree with
    | .ok result => some result
    | .error _ => none

inductive ContractCallKind where
  | messageCall
  | transaction
  deriving Repr, BEq

def ContractCallKind.executionState (kind : ContractCallKind)
    (state : State) : State :=
  match kind with
  | ContractCallKind.messageCall => state
  | ContractCallKind.transaction => state.clearTransient

def ContractCallKind.result? (kind : ContractCallKind)
    (fuel : Nat) (contract : Contract) (target : CallTarget)
    (state : State) (args : List Value) : Option CallResult :=
  match kind with
  | ContractCallKind.messageCall =>
      contract.call? fuel target state args
  | ContractCallKind.transaction =>
      contract.callTransaction? fuel target state args

end Source
end Solidity
end SolidCore

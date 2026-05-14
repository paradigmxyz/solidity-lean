import SharedSemantics.Account
import SharedSemantics.External
import SharedSemantics.Block
import SharedSemantics.Call
import SharedSemantics.Log
import SharedSemantics.Precompile
import SolidCore.Solidity.Keccak

namespace SolidCore
namespace Solidity
namespace Source

abbrev Word := SharedSemantics.Word
abbrev Byte := SharedSemantics.Account.Byte

def wordModulus : Nat :=
  SharedSemantics.wordModulus

def normWord (value : Nat) : Word :=
  SharedSemantics.norm value

def normByte (value : Nat) : Byte :=
  SharedSemantics.Account.byte value

def bytesToWordBE (bytes : List Byte) : Word :=
  SharedSemantics.norm
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
  !(SharedSemantics.norm value == 0)

def wordEq (lhs rhs : Word) : Bool :=
  SharedSemantics.norm lhs == SharedSemantics.norm rhs

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

inductive Value where
  | word : Word -> Value
  | int : Word -> Value
  | bytes : List Byte -> Value
  | externalFunction : Word -> Word -> Value
  | fixedArray : List Value -> Value
  | dynamicArray : List Value -> Value
  | tuple : List Value -> Value
  | storageRef : String -> Value
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

def Value.asWord? : Value -> Option Word
  | Value.word value => some (SharedSemantics.norm value)
  | _ => none

def Value.asStorageWord? : Value -> Option Word
  | Value.word value => some (SharedSemantics.norm value)
  | Value.int value => some (SharedSemantics.norm value)
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

def Value.defaultLike : Value -> Value
  | Value.word _ => Value.word 0
  | Value.int _ => Value.int 0
  | Value.bytes _ => Value.bytes []
  | Value.externalFunction _ _ => Value.externalFunction 0 0
  | Value.fixedArray values => Value.fixedArray (values.map Value.defaultLike)
  | Value.dynamicArray _ => Value.dynamicArray []
  | Value.tuple values => Value.tuple (values.map Value.defaultLike)
  | Value.storageRef target => Value.storageRef target

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

def RevertData.popEmptyArray : RevertData :=
  RevertData.panic 0x31

def RevertData.indexOutOfBounds : RevertData :=
  RevertData.panic 0x32

def RevertData.typeMismatch : RevertData :=
  RevertData.panic 0

def RevertData.fromRawBytes (bytes : List Byte) : RevertData :=
  if bytes.map normByte == [] then
    RevertData.empty
  else
    RevertData.raw bytes

def Value.expectWord : Value -> Except RevertData Word
  | Value.word value => Except.ok (SharedSemantics.norm value)
  | _ => Except.error RevertData.typeMismatch

mutual

def Ty.coerceValue? : Ty -> Value -> Option Value
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
  | _, _ => none

mutual

def Value.coerceLike? : Value -> Value -> Option Value
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
      match Value.coerceLikeList? oldValues values with
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

end

def Value.index? (container : Value) (index : Word) :
    Except RevertData Value :=
  match container with
  | Value.bytes bs =>
      match listGet? (bs.map normByte) (SharedSemantics.norm index) with
      | some byte => Except.ok (Value.word byte)
      | none => Except.error RevertData.indexOutOfBounds
  | Value.fixedArray values =>
      match listGet? values (SharedSemantics.norm index) with
      | some value => Except.ok value
      | none => Except.error RevertData.indexOutOfBounds
  | Value.dynamicArray values =>
      match listGet? values (SharedSemantics.norm index) with
      | some value => Except.ok value
      | none => Except.error RevertData.indexOutOfBounds
  | Value.tuple values =>
      match listGet? values (SharedSemantics.norm index) with
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

def fixedBytesIndex? (size : Nat) (value index : Word) :
    Except RevertData Value :=
  if 0 < size && size <= wordBytes then
    match listGet? (wordToBytesBE size value) (SharedSemantics.norm index) with
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
    | some word => Except.ok (Value.word (SharedSemantics.norm word % (2 ^ bits)))
    | none => Except.error RevertData.typeMismatch
  else
    Except.error RevertData.typeMismatch

def intCast? (bits : Nat) (value : Value) : Except RevertData Value :=
  if 0 < bits && bits <= 256 then
    match value.asStorageWord? with
    | some word =>
        let modulus := 2 ^ bits
        let signBit := 2 ^ (bits - 1)
        let low := SharedSemantics.norm word % modulus
        let casted :=
          if signBit <= low then
            SharedSemantics.norm (wordModulus - modulus + low)
          else
            SharedSemantics.norm low
        Except.ok (Value.int casted)
    | none => Except.error RevertData.typeMismatch
  else
    Except.error RevertData.typeMismatch

def sliceListByWords? {α : Type} (values : List α)
    (start? stop? : Option Word) : Except RevertData (List α) :=
  let start :=
    match start? with
    | some value => SharedSemantics.norm value
    | none => 0
  let stop :=
    match stop? with
    | some value => SharedSemantics.norm value
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
      match listUpdateAt? values (SharedSemantics.norm index) value with
      | some updated => Except.ok (Value.fixedArray updated)
      | none => Except.error RevertData.indexOutOfBounds
  | Value.dynamicArray values =>
      match listUpdateAt? values (SharedSemantics.norm index) value with
      | some updated => Except.ok (Value.dynamicArray updated)
      | none => Except.error RevertData.indexOutOfBounds
  | Value.bytes bs =>
      match value.asWord? with
      | some w =>
          match listUpdateAt? (bs.map normByte)
              (SharedSemantics.norm index) (normByte w) with
          | some updated => Except.ok (Value.bytes updated)
          | none => Except.error RevertData.indexOutOfBounds
      | none => Except.error RevertData.typeMismatch
  | Value.tuple values =>
      match listUpdateAt? values (SharedSemantics.norm index) value with
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

abbrev WordMap := List (Word × Word)

def WordMap.lookup? : WordMap -> Word -> Option Word
  | [], _ => none
  | (key, value) :: rest, query =>
      if wordEq key query then
        some (SharedSemantics.norm value)
      else
        WordMap.lookup? rest query

def WordMap.insertLoop : WordMap -> Word -> Word -> WordMap
  | [], key, value =>
      [(SharedSemantics.norm key, SharedSemantics.norm value)]
  | (entryKey, entryValue) :: rest, key, value =>
      if wordEq entryKey key then
        (SharedSemantics.norm key, SharedSemantics.norm value) :: rest
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

structure State where
  storage : WordMap
  transient : WordMap := []
  immutables : ImmutableMap := []
  selfdestructs : List (Word × Word) := []
  events : List Event
  deriving Repr

def State.empty : State :=
  { storage := [], transient := [], immutables := [], events := [] }

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

def State.recordSelfdestruct
    (state : State) (self recipient : Word) : State :=
  { state with
    selfdestructs :=
      state.selfdestructs ++
        [ ( SharedSemantics.Account.addressWord self
          , SharedSemantics.Account.addressWord recipient) ] }

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

structure Runtime where
  state : State
  locals : LocalEnv
  deriving Repr

def Runtime.ofState (state : State) : Runtime :=
  { state, locals := [[]] }

def Runtime.pushScope (runtime : Runtime) : Runtime :=
  { runtime with locals := [] :: runtime.locals }

def Runtime.popScope (runtime : Runtime) : Runtime :=
  { runtime with locals := runtime.locals.drop 1 }

def Runtime.lookupLocal? (runtime : Runtime) (name : String) :
    Option Value :=
  LocalEnv.lookup? runtime.locals name

def Runtime.lookupStorageRef? (runtime : Runtime) (name : String) :
    Option String :=
  match runtime.lookupLocal? name with
  | some (Value.storageRef target) => some target
  | _ => none

def Runtime.assignStorageRef?
    (runtime : Runtime) (name target : String) : Option Runtime :=
  match runtime.lookupLocal? name with
  | some (Value.storageRef _) =>
      match LocalEnv.assign? runtime.locals name (Value.storageRef target) with
      | some locals => some { runtime with locals }
      | none => none
  | _ => none

def Runtime.declareLocal
    (runtime : Runtime) (name : String) (value : Value) : Runtime :=
  { runtime with locals := LocalEnv.declare runtime.locals name value }

def Runtime.assignLocal?
    (runtime : Runtime) (name : String) (value : Value) :
    Option Runtime :=
  match runtime.lookupLocal? name with
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

inductive StorageLayout where
  | scalar : Ty -> StorageLayout
  | struct : List StorageLayout -> StorageLayout
  | fixedArray : Nat -> StorageLayout -> StorageLayout
  | dynamicArray : StorageLayout -> StorageLayout
  | bytes : StorageLayout
  | string : StorageLayout
  | mapping : Ty -> StorageLayout -> StorageLayout
  deriving Repr

mutual

def StorageLayout.slotSpan : StorageLayout -> Nat
  | StorageLayout.scalar _ => 1
  | StorageLayout.struct layouts => StorageLayouts.slotSpan layouts
  | StorageLayout.fixedArray size elementLayout =>
      size * StorageLayout.slotSpan elementLayout
  | StorageLayout.dynamicArray _ => 1
  | StorageLayout.bytes => 1
  | StorageLayout.string => 1
  | StorageLayout.mapping _ _ => 1

def StorageLayouts.slotSpan : List StorageLayout -> Nat
  | [] => 0
  | layout :: rest =>
      StorageLayout.slotSpan layout + StorageLayouts.slotSpan rest

end

def StorageLayouts.fieldOffsetAndLayout? :
    Nat -> Nat -> List StorageLayout -> Option (Nat × StorageLayout)
  | _, _, [] => none
  | target, offset, layout :: rest =>
      if target == 0 then
        some (offset, layout)
      else
        StorageLayouts.fieldOffsetAndLayout? (target - 1)
          (offset + StorageLayout.slotSpan layout) rest

structure StorageField where
  name : String
  slot : Word
  ty? : Option Ty := none
  layout? : Option StorageLayout := none
  transient : Bool := false
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
  SharedSemantics.Block.BlockEnv

def BlockEnv.empty : BlockEnv :=
  SharedSemantics.Block.BlockEnv.empty

abbrev TxEnv :=
  SharedSemantics.Block.TxEnv

def TxEnv.empty : TxEnv :=
  SharedSemantics.Block.TxEnv.empty

abbrev LowLevelCallKind :=
  SharedSemantics.Call.ExternalCallKind

namespace LowLevelCallKind

abbrev call : LowLevelCallKind :=
  SharedSemantics.Call.ExternalCallKind.call

abbrev staticcall : LowLevelCallKind :=
  SharedSemantics.Call.ExternalCallKind.staticcall

abbrev delegatecall : LowLevelCallKind :=
  SharedSemantics.Call.ExternalCallKind.delegatecall

end LowLevelCallKind

abbrev LowLevelCallResult :=
  SharedSemantics.Call.Result LowLevelCallKind

abbrev ContractCreationResult :=
  SharedSemantics.Call.CreationResult

inductive ExternalHashKind where
  | sha256
  | ripemd160
  deriving Repr, BEq

namespace ExternalHashKind

def precompileKind : ExternalHashKind -> SharedSemantics.Precompile.Kind
  | ExternalHashKind.sha256 => SharedSemantics.Precompile.Kind.sha256
  | ExternalHashKind.ripemd160 => SharedSemantics.Precompile.Kind.ripemd160

end ExternalHashKind

def LowLevelCallResult.matches (result : LowLevelCallResult)
    (kind : LowLevelCallKind) (target : Word) (calldata : List Byte)
    (value : Word) (gas? : Option Word := none) : Bool :=
  SharedSemantics.Call.Result.matchesRequest result kind target calldata value
    gas?

def ContractCreationResult.matches (result : ContractCreationResult)
    (contractName : String) (constructorArgs : List Byte)
    (value : Word) (salt? : Option Word) : Bool :=
  SharedSemantics.Call.CreationResult.matchesRequest result contractName
    constructorArgs value salt?

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
  contractAddresses : SharedSemantics.Call.NamedWordMap := []
  contractCreationCodes : SharedSemantics.Call.NamedBytesMap := []
  contractRuntimeCodes : SharedSemantics.Call.NamedBytesMap := []
  lowLevelCallResults : List LowLevelCallResult
  contractCreationResults : List ContractCreationResult
  blockEnv : BlockEnv
  txEnv : TxEnv
  gasleft : Word
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
    lowLevelCallResults := []
    contractCreationResults := []
    blockEnv := BlockEnv.empty
    txEnv := TxEnv.empty
    gasleft := 0 }

def Context.lookupPrecompileCall? (context : Context)
    (kind : SharedSemantics.Precompile.Kind) (input : List Byte)
    (gas? : Option Word := none) :
    Option (SharedSemantics.Precompile.Result) :=
  SharedSemantics.Precompile.lookup?
    context.lowLevelCallResults kind input (gas? := gas?)

def Context.lookupPrecompileOutputWord? (context : Context)
    (kind : SharedSemantics.Precompile.Kind) (input : List Byte)
    (gas? : Option Word := none) : Option Word := do
  let result ← context.lookupPrecompileCall? kind input (gas? := gas?)
  SharedSemantics.Precompile.outputWord? result

def Context.ecrecoverAt (context : Context) (digest v r s : Word) : Word :=
  (context.lookupPrecompileOutputWord?
    SharedSemantics.Precompile.Kind.ecrecover
    (SharedSemantics.Precompile.ecrecoverInput digest v r s)).getD 0

def ExternalHashKind.lookup? (kind : ExternalHashKind)
    (context : Context) (bytes : List Byte) : Option Word :=
  context.lookupPrecompileOutputWord? kind.precompileKind bytes

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
  let preimage := SharedSemantics.subWord inner 1
  SharedSemantics.andWord
    (keccakWord (storageWordBytes preimage))
    erc7201AlignmentMask

def mappingStorageSlot (slot key : Word) : Word :=
  keccakWord (storageWordBytes key ++ storageWordBytes slot)

def mappingStorageSlotForKey (slot : Word) (keyTy : Ty)
    (key : Value) : Except RevertData Word :=
  match keyTy with
  | Ty.bytesCalldata =>
      match key.asBytes? with
      | some bytes =>
          Except.ok (keccakWord (bytes ++ storageWordBytes slot))
      | none => Except.error RevertData.typeMismatch
  | _ => do
      let word ← key.expectWord
      Except.ok (mappingStorageSlot slot word)

def dynamicArrayDataSlot (slot : Word) : Word :=
  keccakWord (storageWordBytes slot)

def dynamicArrayStorageSlot (slot index : Word) : Word :=
  normWord (SharedSemantics.norm (dynamicArrayDataSlot slot) +
    SharedSemantics.norm index)

def fixedArrayStorageSlot (slot index : Word) : Word :=
  normWord (SharedSemantics.norm slot + SharedSemantics.norm index)

def dynamicArrayLayoutStorageSlot
    (slot index : Word) (elementLayout : StorageLayout) : Word :=
  normWord (SharedSemantics.norm (dynamicArrayDataSlot slot) +
    SharedSemantics.norm index * StorageLayout.slotSpan elementLayout)

def fixedArrayLayoutStorageSlot
    (slot index : Word) (elementLayout : StorageLayout) : Word :=
  normWord (SharedSemantics.norm slot +
    SharedSemantics.norm index * StorageLayout.slotSpan elementLayout)

def structFieldStorageSlot? (slot : Word)
    (layouts : List StorageLayout) (index : Nat) :
    Option (Word × StorageLayout) := do
  let (offset, layout) ←
    StorageLayouts.fieldOffsetAndLayout? index 0 layouts
  some (normWord (SharedSemantics.norm slot + offset), layout)

def legacyIndexedStorageSlot (slot key : Word) : Word :=
  normWord
    (SharedSemantics.norm slot * 16777619 +
      SharedSemantics.norm key + 1)

def indexedStorageSlot (slot key : Word) : Word :=
  mappingStorageSlot slot key

def Context.eventDecl? (context : Context) (name : String) :
    Option EventDecl :=
  context.eventDecls.find? (fun event => event.name == name)

def Context.lookupLowLevelCall? (context : Context)
    (kind : LowLevelCallKind) (target : Word) (calldata : List Byte)
    (value : Word) (gas? : Option Word) : Option LowLevelCallResult :=
  SharedSemantics.Call.Result.lookup?
    context.lowLevelCallResults kind target calldata value gas?

def Context.accountHasCode (context : Context) (target : Word) : Bool :=
  !(SharedSemantics.Account.codeAt context.accountCodes target).isEmpty

def Context.lookupContractCreation? (context : Context)
    (contractName : String) (constructorArgs : List Byte)
    (value : Word) (salt? : Option Word) : Option ContractCreationResult :=
  SharedSemantics.Call.CreationResult.lookup?
    context.contractCreationResults contractName constructorArgs value salt?

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
      SharedSemantics.Block.BlockEnv.evalWord context.blockEnv
        SharedSemantics.Block.BlockEnv.WordField.basefee
  | EnvWord.blockBlobbasefee =>
      SharedSemantics.Block.BlockEnv.evalWord context.blockEnv
        SharedSemantics.Block.BlockEnv.WordField.blobbasefee
  | EnvWord.blockChainid =>
      SharedSemantics.Block.BlockEnv.evalWord context.blockEnv
        SharedSemantics.Block.BlockEnv.WordField.chainid
  | EnvWord.blockCoinbase =>
      SharedSemantics.Block.BlockEnv.evalWord context.blockEnv
        SharedSemantics.Block.BlockEnv.WordField.coinbase
  | EnvWord.blockDifficulty =>
      SharedSemantics.Block.BlockEnv.evalWord context.blockEnv
        SharedSemantics.Block.BlockEnv.WordField.prevrandao
  | EnvWord.blockGaslimit =>
      SharedSemantics.Block.BlockEnv.evalWord context.blockEnv
        SharedSemantics.Block.BlockEnv.WordField.gaslimit
  | EnvWord.blockNumber =>
      SharedSemantics.Block.BlockEnv.evalWord context.blockEnv
        SharedSemantics.Block.BlockEnv.WordField.number
  | EnvWord.blockPrevrandao =>
      SharedSemantics.Block.BlockEnv.evalWord context.blockEnv
        SharedSemantics.Block.BlockEnv.WordField.prevrandao
  | EnvWord.blockTimestamp =>
      SharedSemantics.Block.BlockEnv.evalWord context.blockEnv
        SharedSemantics.Block.BlockEnv.WordField.timestamp
  | EnvWord.txGasprice =>
      SharedSemantics.Block.TxEnv.evalWord context.txEnv
        SharedSemantics.Block.TxEnv.WordField.gasprice
  | EnvWord.txOrigin =>
      SharedSemantics.Block.TxEnv.evalWord context.txEnv
        SharedSemantics.Block.TxEnv.WordField.origin
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
      SharedSemantics.Block.BlockEnv.blockhash context.blockEnv key
  | EnvLookup.blobhash =>
      SharedSemantics.Block.TxEnv.blobhash context.txEnv key
  | EnvLookup.accountBalance =>
      SharedSemantics.Account.balanceAt context.accountBalances key
  | EnvLookup.accountCodehash =>
      SharedSemantics.Account.codehashAt context.accountCodehashes key

inductive EnvBytesLookup where
  | accountCode : EnvBytesLookup
  deriving Repr

def EnvBytesLookup.eval
    (which : EnvBytesLookup) (context : Context) (key : Word) :
    List Byte :=
  match which with
  | EnvBytesLookup.accountCode =>
      SharedSemantics.Account.codeAt context.accountCodes key

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

mutual

def State.loadStorageLayoutAt (state : State) (slot : Word) :
    StorageLayout -> Except RevertData Value
  | StorageLayout.scalar ty =>
      loadStorageWordAs state slot ty
  | StorageLayout.struct layouts => do
      let values ← State.loadStructSlots state slot 0 layouts
      Except.ok (Value.tuple values)
  | StorageLayout.bytes =>
      let length := SharedSemantics.norm (state.loadSlot slot)
      Except.ok
        (Value.bytes (State.loadBytesSlots state slot 0 length))
  | StorageLayout.string =>
      let length := SharedSemantics.norm (state.loadSlot slot)
      Except.ok
        (Value.bytes (State.loadBytesSlots state slot 0 length))
  | StorageLayout.fixedArray _ _
  | StorageLayout.dynamicArray _
  | StorageLayout.mapping _ _ =>
      Except.error RevertData.typeMismatch

def State.loadStructSlots (state : State) (slot : Word) :
    Nat -> List StorageLayout -> Except RevertData (List Value)
  | _, [] => Except.ok []
  | offset, layout :: rest => do
      let fieldSlot :=
        normWord (SharedSemantics.norm slot + offset)
      let value ←
        State.loadStorageLayoutAt state fieldSlot layout
      let tail ← State.loadStructSlots state slot
        (offset + StorageLayout.slotSpan layout) rest
      Except.ok (value :: tail)

end

mutual

def State.storeStorageLayoutAt (state : State) (slot : Word)
    (layout : StorageLayout) (value : Value) : Except RevertData State :=
  match layout with
  | StorageLayout.scalar ty => do
      let word ← coerceStorageWordAs ty value
      Except.ok (state.storeSlot slot word)
  | StorageLayout.struct layouts =>
      match value with
      | Value.tuple values =>
          State.storeStructSlots state slot 0 layouts values
      | _ => Except.error RevertData.typeMismatch
  | StorageLayout.bytes =>
      match value with
      | Value.bytes bytes =>
          Except.ok
            ((State.storeBytesSlots state slot 0 bytes)
              |>.storeSlot slot bytes.length)
      | _ => Except.error RevertData.typeMismatch
  | StorageLayout.string =>
      match value with
      | Value.bytes bytes =>
          Except.ok
            ((State.storeBytesSlots state slot 0 bytes)
              |>.storeSlot slot bytes.length)
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
    Nat -> List StorageLayout -> List Value -> Except RevertData State
  | _, [], [] => Except.ok state
  | offset, layout :: layouts, value :: values => do
      let fieldSlot :=
        normWord (SharedSemantics.norm slot + offset)
      let state ←
        State.storeStorageLayoutAt state fieldSlot layout value
      State.storeStructSlots
        state slot (offset + StorageLayout.slotSpan layout) layouts values
  | _, _, _ => Except.error RevertData.typeMismatch

def State.storeFixedArrayLayoutSlots (state : State) (slot : Word)
    (elementLayout : StorageLayout) :
    Nat -> List Value -> Except RevertData State
  | _, [] => Except.ok state
  | index, value :: rest => do
      let state ←
        State.storeStorageLayoutAt state
          (fixedArrayLayoutStorageSlot slot index elementLayout)
          elementLayout value
      State.storeFixedArrayLayoutSlots state slot elementLayout
        (index + 1) rest

def State.storeDynamicArrayLayoutSlots (state : State) (slot : Word)
    (elementLayout : StorageLayout) :
    Nat -> List Value -> Except RevertData State
  | _, [] => Except.ok state
  | index, value :: rest => do
      let state ←
        State.storeStorageLayoutAt state
          (dynamicArrayLayoutStorageSlot slot index elementLayout)
          elementLayout value
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

def Runtime.loadStorageField (context : Context)
    (runtime : Runtime) (name : String) : Except RevertData Value :=
  match context.storageField? name with
  | some field =>
      match field.layout? with
      | some (StorageLayout.dynamicArray _) =>
          Except.ok (Value.word (runtime.state.loadFieldSlot field))
      | some StorageLayout.bytes =>
          Except.ok (Value.word (runtime.state.loadFieldSlot field))
      | some StorageLayout.string =>
          Except.error RevertData.typeMismatch
      | some (StorageLayout.struct tys) => do
          let values ← State.loadStructSlots runtime.state field.slot 0 tys
          Except.ok (Value.tuple values)
      | some (StorageLayout.fixedArray _ _) =>
          Except.error RevertData.typeMismatch
      | some (StorageLayout.mapping _ _) =>
          Except.error RevertData.typeMismatch
      | some (StorageLayout.scalar ty) =>
          match ty.storageValueFromWord? (runtime.state.loadFieldSlot field) with
          | some value => Except.ok value
          | none => Except.error RevertData.typeMismatch
      | none =>
          match field.ty? with
          | some ty =>
              match ty.storageValueFromWord? (runtime.state.loadFieldSlot field) with
              | some value => Except.ok value
              | none => Except.error RevertData.typeMismatch
          | none => Except.ok (Value.word (runtime.state.loadFieldSlot field))
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
                (State.storeBytesSlots runtime.state field.slot 0 bytes)
                  |>.storeSlot field.slot bytes.length }
      | _ => Except.error RevertData.typeMismatch
  | some StorageLayout.string =>
      match value with
      | Value.bytes bytes =>
          Except.ok
            { runtime with
              state :=
                (State.storeBytesSlots runtime.state field.slot 0 bytes)
                  |>.storeSlot field.slot bytes.length }
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
  | some (StorageLayout.scalar ty) => do
      let word ← coerceStorageWordAs ty value
      Except.ok
        { runtime with state := runtime.state.storeFieldSlot field word }
  | none =>
      let word ← coerceStorageWordAs Ty.uint256 value
      Except.ok
        { runtime with state := runtime.state.storeFieldSlot field word }

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
      let length := SharedSemantics.norm (runtime.state.loadSlot field.slot)
      Except.ok
        (Value.bytes
          (State.loadBytesSlots runtime.state field.slot 0 length))
  | some StorageLayout.string =>
      let length := SharedSemantics.norm (runtime.state.loadSlot field.slot)
      Except.ok
        (Value.bytes
          (State.loadBytesSlots runtime.state field.slot 0 length))
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
        (state.storeSlot (normWord (SharedSemantics.norm slot + offset)) 0)
        slot (offset + 1) remaining

def State.clearFixedArrayLayoutSlots (state : State) (slot : Word)
    (elementLayout : StorageLayout) :
    Nat -> Nat -> State
  | _, 0 => state
  | index, remaining + 1 =>
      State.clearFixedArrayLayoutSlots
        (State.clearLayoutSpanSlots state
          (fixedArrayLayoutStorageSlot slot index elementLayout)
          0 (StorageLayout.slotSpan elementLayout))
        slot elementLayout (index + 1) remaining

mutual

def State.clearStorageLayoutAt (state : State) (slot : Word) :
    StorageLayout -> Except RevertData State
  | StorageLayout.scalar ty => do
      let defaultWord ← coerceStorageWordAs ty ty.defaultValue
      Except.ok (state.storeSlot slot defaultWord)
  | StorageLayout.struct layouts =>
      State.clearStructLayoutSlots state slot 0 layouts
  | StorageLayout.bytes =>
      Except.ok (state.storeSlot slot 0)
  | StorageLayout.string =>
      Except.ok (state.storeSlot slot 0)
  | StorageLayout.dynamicArray _ =>
      Except.ok (state.storeSlot slot 0)
  | StorageLayout.mapping _ _ =>
      Except.ok state
  | StorageLayout.fixedArray size elementLayout =>
      Except.ok
        (State.clearFixedArrayLayoutSlots
          state slot elementLayout 0 size)

def State.clearStructLayoutSlots (state : State) (slot : Word) :
    Nat -> List StorageLayout -> Except RevertData State
  | _, [] => Except.ok state
  | offset, layout :: rest => do
      let state ←
        State.clearStorageLayoutAt state
          (normWord (SharedSemantics.norm slot + offset)) layout
      State.clearStructLayoutSlots state slot
        (offset + StorageLayout.slotSpan layout) rest

end

def State.clearDynamicArrayLayoutSlots (state : State) (slot : Word)
    (elementLayout : StorageLayout) :
    Nat -> Nat -> Except RevertData State
  | _, 0 => Except.ok state
  | index, remaining + 1 => do
      let state ←
        State.clearStorageLayoutAt state
          (dynamicArrayLayoutStorageSlot slot index elementLayout)
          elementLayout
      State.clearDynamicArrayLayoutSlots
        state slot elementLayout (index + 1) remaining

def State.clearDynamicArrayLayoutAt (state : State) (slot : Word)
    (elementLayout : StorageLayout) : Except RevertData State := do
  let length := SharedSemantics.norm (state.loadSlot slot)
  let state ←
    State.clearDynamicArrayLayoutSlots state slot elementLayout 0 length
  Except.ok (state.storeSlot slot 0)

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
        State.clearDynamicArrayLayoutAt
          runtime.state field.slot elementLayout
      Except.ok { runtime with state }
  | some StorageLayout.bytes =>
      Except.ok
        { runtime with state := runtime.state.storeSlot field.slot 0 }
  | some StorageLayout.string =>
      Except.ok
        { runtime with state := runtime.state.storeSlot field.slot 0 }
  | some (StorageLayout.struct layouts) => do
      let state ←
        State.clearStorageLayoutAt runtime.state field.slot
          (StorageLayout.struct layouts)
      Except.ok { runtime with state }
  | some (StorageLayout.fixedArray size elementLayout) => do
      let state ←
        State.clearStorageLayoutAt runtime.state field.slot
          (StorageLayout.fixedArray size elementLayout)
      Except.ok { runtime with state }
  | some (StorageLayout.mapping _ _) =>
      Except.ok runtime
  | some (StorageLayout.scalar ty) => do
      let defaultWord ← coerceStorageWordAs ty ty.defaultValue
      Except.ok
        { runtime with
          state := runtime.state.storeFieldSlot field defaultWord }
  | none =>
      Except.ok
        { runtime with state := runtime.state.storeFieldSlot field 0 }

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
      if SharedSemantics.norm length <= SharedSemantics.norm key then
        Except.error RevertData.indexOutOfBounds
      else
        State.resolveStoragePathSlot state
          (dynamicArrayLayoutStorageSlot slot key elementLayout)
          elementLayout rest
  | slot, StorageLayout.fixedArray size elementLayout, index :: rest => do
      let key ← index.expectWord
      if size <= SharedSemantics.norm key then
        Except.error RevertData.indexOutOfBounds
      else
        State.resolveStoragePathSlot state
          (fixedArrayLayoutStorageSlot slot key elementLayout)
          elementLayout rest
  | slot, StorageLayout.struct layouts, index :: rest => do
      let key ← index.expectWord
      match structFieldStorageSlot? slot layouts (SharedSemantics.norm key) with
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
      let length := runtime.state.loadSlot field.slot
      if SharedSemantics.norm length <= SharedSemantics.norm key then
        Except.error RevertData.indexOutOfBounds
      else
        Except.ok
          (Value.word
            (normByte
              (runtime.state.loadSlot
                (dynamicArrayStorageSlot field.slot key))))
  | some StorageLayout.string =>
      Except.error RevertData.typeMismatch
  | some (StorageLayout.dynamicArray elementLayout) => do
      let key ← index.expectWord
      let length := runtime.state.loadSlot field.slot
      if SharedSemantics.norm length <= SharedSemantics.norm key then
        Except.error RevertData.indexOutOfBounds
      else
        runtime.state.loadStorageLayoutAt
          (dynamicArrayLayoutStorageSlot field.slot key elementLayout)
          elementLayout
  | some (StorageLayout.fixedArray size elementLayout) => do
      let key ← index.expectWord
      if size <= SharedSemantics.norm key then
        Except.error RevertData.indexOutOfBounds
      else
        runtime.state.loadStorageLayoutAt
          (fixedArrayLayoutStorageSlot field.slot key elementLayout)
          elementLayout
  | some (StorageLayout.struct layouts) => do
      let key ← index.expectWord
      match structFieldStorageSlot? field.slot layouts (SharedSemantics.norm key) with
      | some (fieldSlot, fieldLayout) =>
          runtime.state.loadStorageLayoutAt
            fieldSlot fieldLayout
      | none => Except.error RevertData.indexOutOfBounds
  | some (StorageLayout.scalar _) =>
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
  match field.layout? with
  | some (StorageLayout.mapping keyTy valueLayout) => do
      let slot ← mappingStorageSlotForKey field.slot keyTy index
      let state ←
        State.storeStorageLayoutAt runtime.state slot valueLayout value
      Except.ok { runtime with state }
  | some StorageLayout.bytes => do
      let key ← index.expectWord
      let length := runtime.state.loadSlot field.slot
      if SharedSemantics.norm length <= SharedSemantics.norm key then
        Except.error RevertData.indexOutOfBounds
      else
        let word ← coerceStorageWordAs (Ty.fixedBytes 1) value
        Except.ok
          { runtime with
            state :=
              runtime.state.storeSlot
                (dynamicArrayStorageSlot field.slot key) word }
  | some StorageLayout.string =>
      Except.error RevertData.typeMismatch
  | some (StorageLayout.dynamicArray elementLayout) => do
      let key ← index.expectWord
      let length := runtime.state.loadSlot field.slot
      if SharedSemantics.norm length <= SharedSemantics.norm key then
        Except.error RevertData.indexOutOfBounds
      else
        let state ←
          State.storeStorageLayoutAt runtime.state
            (dynamicArrayLayoutStorageSlot field.slot key elementLayout)
            elementLayout value
        Except.ok { runtime with state }
  | some (StorageLayout.fixedArray size elementLayout) => do
      let key ← index.expectWord
      if size <= SharedSemantics.norm key then
        Except.error RevertData.indexOutOfBounds
      else
        let state ←
          State.storeStorageLayoutAt runtime.state
            (fixedArrayLayoutStorageSlot field.slot key elementLayout)
            elementLayout value
        Except.ok { runtime with state }
  | some (StorageLayout.struct layouts) => do
      let key ← index.expectWord
      match
        structFieldStorageSlot? field.slot layouts
          (SharedSemantics.norm key)
      with
      | some (fieldSlot, fieldLayout) => do
          let state ←
            State.storeStorageLayoutAt runtime.state
              fieldSlot fieldLayout value
          Except.ok { runtime with state }
      | none => Except.error RevertData.indexOutOfBounds
  | some (StorageLayout.scalar _) =>
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
  let length := runtime.state.loadSlot field.slot
  let rawLength := SharedSemantics.norm length + 1
  if wordModulus <= rawLength then
    Except.error RevertData.overflow
  else
    match field.layout? with
    | some (StorageLayout.dynamicArray elementLayout) => do
        let elementSlot :=
          dynamicArrayLayoutStorageSlot field.slot length elementLayout
        let state ←
          match value? with
          | some value =>
              State.storeStorageLayoutAt runtime.state
                elementSlot elementLayout value
          | none =>
              State.clearStorageLayoutAt runtime.state
                elementSlot elementLayout
        Except.ok
          { runtime with
            state := state.storeSlot field.slot (normWord rawLength) }
    | some StorageLayout.bytes => do
        let word ←
          match value? with
          | some value => coerceStorageWordAs (Ty.fixedBytes 1) value
          | none => Except.ok 0
        Except.ok
          { runtime with
            state :=
              (runtime.state.storeSlot
                (dynamicArrayStorageSlot field.slot length) word)
                |>.storeSlot field.slot (normWord rawLength) }
    | some StorageLayout.string =>
        Except.error RevertData.typeMismatch
    | none => do
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
  let length := runtime.state.loadSlot field.slot
  if wordEq length 0 then
    Except.error RevertData.popEmptyArray
  else
    let newLength := SharedSemantics.subWord length 1
    match field.layout? with
    | some (StorageLayout.dynamicArray elementLayout) => do
        let state ←
          State.clearStorageLayoutAt runtime.state
            (dynamicArrayLayoutStorageSlot
              field.slot newLength elementLayout)
            elementLayout
        Except.ok
          { runtime with state := state.storeSlot field.slot newLength }
    | some StorageLayout.bytes =>
        Except.ok
          { runtime with
            state :=
              (runtime.state.storeSlot
                (dynamicArrayStorageSlot field.slot newLength) 0)
                |>.storeSlot field.slot newLength }
    | none =>
        Except.ok
          { runtime with
            state :=
              (runtime.state.storeSlot
                (legacyIndexedStorageSlot field.slot newLength) 0)
                |>.storeSlot field.slot newLength }
    | _ => Except.error RevertData.typeMismatch

def abiStaticBytes? : Ty -> Value -> Option (List Byte)
  | Ty.bool, Value.word value =>
      if wordEq value 0 || wordEq value 1 then
        some (wordToBytesBE wordBytes value)
      else
        none
  | Ty.address, Value.word value => some (wordToBytesBE wordBytes value)
  | Ty.uint256, Value.word value => some (wordToBytesBE wordBytes value)
  | Ty.int256, Value.int value => some (wordToBytesBE wordBytes value)
  | Ty.fixedBytes size, Value.word value =>
      if 0 < size && size <= wordBytes then
        some
          (wordToBytesBE size value ++
            List.replicate (wordBytes - size) 0)
      else
        none
  | Ty.externalFunction, Value.externalFunction addr selector =>
      some
        (wordToBytesBE 20 addr ++
          wordToBytesBE selectorBytes selector ++
          List.replicate (wordBytes - 20 - selectorBytes) 0)
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
      some (Value.word value)
  | _fuel + 1, argData, headIndex, Ty.uint256 => do
      let value ← readWord? argData (wordBytes * headIndex)
      some (Value.word value)
  | _fuel + 1, argData, headIndex, Ty.int256 => do
      let value ← readWord? argData (wordBytes * headIndex)
      some (Value.int value)
  | _fuel + 1, argData, headIndex, Ty.fixedBytes size =>
      if 0 < size && size <= wordBytes then
        do
        let bytes ← readBytes? argData (wordBytes * headIndex) size
        some (Value.word (bytesToWordBE bytes))
      else
        none
  | _fuel + 1, argData, headIndex, Ty.externalFunction => do
      let bytes ← readBytes? argData (wordBytes * headIndex) 24
      let addressBytes ← readBytes? bytes 0 20
      let selectorPart ← readBytes? bytes 20 selectorBytes
      some
        (Value.externalFunction
          (bytesToWordBE addressBytes) (bytesToWordBE selectorPart))
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
  if Ty.isDynamicAbi ty then
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

def abiEncodePackedValues? :
    List Ty -> List Value -> Option (List Byte)
  | [], [] => some []
  | ty :: tys, value :: values => do
      let head ← abiEncodePackedValue? ty value
      let tail ← abiEncodePackedValues? tys values
      some (head ++ tail)
  | _, _ => none

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
  | externalFunctionSelector : Expr -> Expr
  | externalFunctionAddress : Expr -> Expr
  | unary : UnaryOp -> Expr -> Expr
  | preIncrement : Expr -> Expr
  | preDecrement : Expr -> Expr
  | postIncrement : Expr -> Expr
  | postDecrement : Expr -> Expr
  | assignExpr : Expr -> Expr -> Expr
  | assignOpExpr : Expr -> BinaryOp -> Expr -> Expr
  | binary : BinaryOp -> Expr -> Expr -> Expr
  | addMod : Expr -> Expr -> Expr -> Expr
  | mulMod : Expr -> Expr -> Expr -> Expr
  | concatBytes : List Expr -> Expr
  | fixedBytesIndex : Nat -> Expr -> Expr -> Expr
  | fixedBytesCast : Nat -> Nat -> Expr -> Expr
  | fixedBytesFromBytes : Nat -> Expr -> Expr
  | uintCast : Nat -> Expr -> Expr
  | intCast : Nat -> Expr -> Expr
  | keccak256 : Expr -> Expr
  | erc7201 : Expr -> Expr
  | tuple : List Expr -> Expr
  | abiEncode : List Ty -> List Expr -> Expr
  | abiEncodeWithSelector : Expr -> List Ty -> List Expr -> Expr
  | abiEncodePacked : List Ty -> List Expr -> Expr
  | abiDecode : List Ty -> Expr -> Expr
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
  let raw := SharedSemantics.norm lhs + SharedSemantics.norm rhs
  if checked && (wordModulus <= raw) then
    Except.error RevertData.overflow
  else
    Except.ok (SharedSemantics.addWord lhs rhs)

def checkedSub (checked : Bool) (lhs rhs : Word) :
    Except RevertData Word :=
  if checked && (SharedSemantics.norm lhs < SharedSemantics.norm rhs) then
    Except.error RevertData.overflow
  else
    Except.ok (SharedSemantics.subWord lhs rhs)

def checkedMul (checked : Bool) (lhs rhs : Word) :
    Except RevertData Word :=
  let raw := SharedSemantics.norm lhs * SharedSemantics.norm rhs
  if checked && (wordModulus <= raw) then
    Except.error RevertData.overflow
  else
    Except.ok (SharedSemantics.mulWord lhs rhs)

def checkedDiv (_checked : Bool) (lhs rhs : Word) :
    Except RevertData Word :=
  if SharedSemantics.norm rhs = 0 then
    Except.error RevertData.divByZero
  else
    Except.ok (SharedSemantics.divWord lhs rhs)

def checkedMod (_checked : Bool) (lhs rhs : Word) :
    Except RevertData Word :=
  if SharedSemantics.norm rhs = 0 then
    Except.error RevertData.divByZero
  else
    Except.ok (SharedSemantics.modWord lhs rhs)

def checkedExpLoop (checked : Bool) (base : Word) :
    Nat -> Word -> Except RevertData Word
  | 0, acc => Except.ok (SharedSemantics.norm acc)
  | remaining + 1, acc =>
      let raw := SharedSemantics.norm acc * SharedSemantics.norm base
      if checked && wordModulus <= raw then
        Except.error RevertData.overflow
      else
        checkedExpLoop checked base remaining (normWord raw)

def checkedExp (checked : Bool) (base exponent : Word) :
    Except RevertData Word :=
  checkedExpLoop checked base (SharedSemantics.norm exponent) 1

def signedIntMin : Int :=
  -Int.ofNat SharedSemantics.halfWordModulus

def signedIntMax : Int :=
  Int.ofNat SharedSemantics.halfWordModulus - 1

def signedInt256InRange (value : Int) : Bool :=
  decide (signedIntMin <= value) && decide (value <= signedIntMax)

def checkedSignedWord (checked : Bool) (value : Int) (wrapped : Word) :
    Except RevertData Word :=
  if checked && !(signedInt256InRange value) then
    Except.error RevertData.overflow
  else if checked then
    Except.ok (SharedSemantics.signedToWord value)
  else
    Except.ok wrapped

def checkedSignedAdd (checked : Bool) (lhs rhs : Word) :
    Except RevertData Word :=
  checkedSignedWord checked
    (SharedSemantics.signedValue lhs + SharedSemantics.signedValue rhs)
    (SharedSemantics.addWord lhs rhs)

def checkedSignedSub (checked : Bool) (lhs rhs : Word) :
    Except RevertData Word :=
  checkedSignedWord checked
    (SharedSemantics.signedValue lhs - SharedSemantics.signedValue rhs)
    (SharedSemantics.subWord lhs rhs)

def checkedSignedMul (checked : Bool) (lhs rhs : Word) :
    Except RevertData Word :=
  checkedSignedWord checked
    (SharedSemantics.signedValue lhs * SharedSemantics.signedValue rhs)
    (SharedSemantics.mulWord lhs rhs)

def checkedSignedNeg (checked : Bool) (value : Word) :
    Except RevertData Word :=
  checkedSignedWord checked (-(SharedSemantics.signedValue value))
    (SharedSemantics.subWord 0 value)

def isSignedMinWord (value : Word) : Bool :=
  wordEq value SharedSemantics.halfWordModulus

def isSignedNegOneWord (value : Word) : Bool :=
  wordEq value (wordModulus - 1)

def checkedSignedDiv (checked : Bool) (lhs rhs : Word) :
    Except RevertData Word :=
  if wordEq rhs 0 then
    Except.error RevertData.divByZero
  else if checked && isSignedMinWord lhs && isSignedNegOneWord rhs then
    Except.error RevertData.overflow
  else
    Except.ok (SharedSemantics.sdivWord lhs rhs)

def checkedSignedMod (_checked : Bool) (lhs rhs : Word) :
    Except RevertData Word :=
  if wordEq rhs 0 then
    Except.error RevertData.divByZero
  else
    Except.ok (SharedSemantics.smodWord lhs rhs)

def checkedAddMod (lhs rhs modulus : Word) :
    Except RevertData Word :=
  if wordEq modulus 0 then
    Except.error RevertData.divByZero
  else
    Except.ok (SharedSemantics.addmodWord lhs rhs modulus)

def checkedMulMod (lhs rhs modulus : Word) :
    Except RevertData Word :=
  if wordEq modulus 0 then
    Except.error RevertData.divByZero
  else
    Except.ok (SharedSemantics.mulmodWord lhs rhs modulus)

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
  | BinaryOp.bitAnd => Except.ok (SharedSemantics.andWord lhs rhs)
  | BinaryOp.bitOr => Except.ok (SharedSemantics.orWord lhs rhs)
  | BinaryOp.bitXor => Except.ok (SharedSemantics.xorWord lhs rhs)
  | BinaryOp.shl => Except.ok (SharedSemantics.shlWord rhs lhs)
  | BinaryOp.shr => Except.ok (SharedSemantics.shrWord rhs lhs)
  | BinaryOp.sar => Except.ok (SharedSemantics.sarWord rhs lhs)
  | BinaryOp.lt => Except.ok (SharedSemantics.ltWord lhs rhs)
  | BinaryOp.gt => Except.ok (SharedSemantics.gtWord lhs rhs)
  | BinaryOp.le =>
      Except.ok (boolWord (!(wordTruthy (SharedSemantics.gtWord lhs rhs))))
  | BinaryOp.ge =>
      Except.ok (boolWord (!(wordTruthy (SharedSemantics.ltWord lhs rhs))))
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
  | BinaryOp.bitAnd =>
      Except.ok (Value.int (SharedSemantics.andWord lhs rhs))
  | BinaryOp.bitOr =>
      Except.ok (Value.int (SharedSemantics.orWord lhs rhs))
  | BinaryOp.bitXor =>
      Except.ok (Value.int (SharedSemantics.xorWord lhs rhs))
  | BinaryOp.shl =>
      Except.ok (Value.int (SharedSemantics.shlWord rhs lhs))
  | BinaryOp.shr =>
      Except.ok (Value.int (SharedSemantics.sarWord rhs lhs))
  | BinaryOp.sar =>
      Except.ok (Value.int (SharedSemantics.sarWord rhs lhs))
  | BinaryOp.lt => Except.ok (Value.word (SharedSemantics.sltWord lhs rhs))
  | BinaryOp.gt => Except.ok (Value.word (SharedSemantics.sgtWord lhs rhs))
  | BinaryOp.le =>
      Except.ok
        (Value.word
          (boolWord
            (!(wordTruthy (SharedSemantics.sgtWord lhs rhs)))))
  | BinaryOp.ge =>
      Except.ok
        (Value.word
          (boolWord
            (!(wordTruthy (SharedSemantics.sltWord lhs rhs)))))
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
      | _, _ => Except.error RevertData.typeMismatch
  | BinaryOp.ne =>
      match lhs, rhs with
      | Value.word lhsWord, Value.word rhsWord =>
          Except.ok (Value.word (boolWord (!(wordEq lhsWord rhsWord))))
      | Value.int lhsWord, Value.int rhsWord =>
          Except.ok (Value.word (boolWord (!(wordEq lhsWord rhsWord))))
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
              Except.ok (Value.int (SharedSemantics.shlWord rhsWord lhsWord))
          | BinaryOp.shr =>
              Except.ok (Value.int (SharedSemantics.sarWord rhsWord lhsWord))
          | BinaryOp.sar =>
              Except.ok (Value.int (SharedSemantics.sarWord rhsWord lhsWord))
          | _ => Except.error RevertData.typeMismatch
      | _, _ => Except.error RevertData.typeMismatch

def UnaryOp.apply (checked : Bool) (op : UnaryOp) (value : Value) :
    Except RevertData Value :=
  match op with
  | UnaryOp.bitNot =>
      match value with
      | Value.word word =>
          Except.ok (Value.word (SharedSemantics.notWord word))
      | Value.int word =>
          Except.ok (Value.int (SharedSemantics.notWord word))
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
            Except.ok (Value.word (SharedSemantics.subWord 0 word))
      | _ => Except.error RevertData.typeMismatch

def enumFromUIntValue (maxValue : Word) : Value -> Except RevertData Value
  | Value.word word =>
      if SharedSemantics.norm word <= SharedSemantics.norm maxValue then
        Except.ok (Value.word word)
      else
        Except.error RevertData.enumConversion
  | Value.int word =>
      let signed := SharedSemantics.signedValue word
      if signed < 0 then
        Except.error RevertData.enumConversion
      else if Int.ofNat (SharedSemantics.norm maxValue) < signed then
        Except.error RevertData.enumConversion
      else
        Except.ok (Value.word word)
  | _ => Except.error RevertData.typeMismatch

mutual

def Expr.eval (context : Context) (runtime : Runtime) :
    Expr -> Except RevertData Value
  | Expr.word value => Except.ok (Value.word (normWord value))
  | Expr.intWord value => Except.ok (Value.int (normWord value))
  | Expr.byteArray bytes => Except.ok (Value.bytes (bytes.map normByte))
  | Expr.contractAddress name =>
      Except.ok
        (Value.word
          (SharedSemantics.Call.namedWordAt
            context.contractAddresses name))
  | Expr.contractCreationCode name =>
      Except.ok
        (Value.bytes
          (SharedSemantics.Call.namedBytesAt
            context.contractCreationCodes name))
  | Expr.contractRuntimeCode name =>
      Except.ok
        (Value.bytes
          (SharedSemantics.Call.namedBytesAt
            context.contractRuntimeCodes name))
  | Expr.calldata => Except.ok (Value.bytes (context.calldata.map normByte))
  | Expr.msgSig => Except.ok (Value.word (calldataSelectorWord context.calldata))
  | Expr.caller => Except.ok (Value.word context.sender)
  | Expr.callValue => Except.ok (Value.word context.value)
  | Expr.self => Except.ok (Value.word context.self)
  | Expr.env which => Except.ok (Value.word (which.eval context))
  | Expr.envLookup which keyExpr => do
      let keyValue ← keyExpr.eval context runtime
      let key ← keyValue.expectWord
      Except.ok (Value.word (which.eval context key))
  | Expr.envBytesLookup which keyExpr => do
      let keyValue ← keyExpr.eval context runtime
      let key ← keyValue.expectWord
      Except.ok (Value.bytes (which.eval context key))
  | Expr.var name =>
      match runtime.lookupStorageRef? name with
      | some target => runtime.loadStorageField context target
      | none =>
          match runtime.lookupLocal? name with
          | some value => Except.ok value
          | none => Except.error RevertData.typeMismatch
  | Expr.immutable name =>
      runtime.loadImmutableField context name
  | Expr.storage name =>
      runtime.loadStorageField context name
  | Expr.storageBytes name =>
      runtime.loadStorageByteStringField context name
  | Expr.storageIndex name idx => do
      let indexValue ← idx.eval context runtime
      runtime.loadStorageIndex context name indexValue
  | Expr.storagePath name indexes => do
      let indexValues ← Expr.evalList context runtime indexes
      runtime.loadStoragePath context name indexValues
  | Expr.externalFunctionSelector expr => do
      let value ← expr.eval context runtime
      match value with
      | Value.externalFunction _ selector => Except.ok (Value.word selector)
      | _ => Except.error RevertData.typeMismatch
  | Expr.externalFunctionAddress expr => do
      let value ← expr.eval context runtime
      match value with
      | Value.externalFunction addr _ => Except.ok (Value.word addr)
      | _ => Except.error RevertData.typeMismatch
  | Expr.unary op expr => do
      let value ← expr.eval context runtime
      op.apply context.checked value
  | Expr.preIncrement _ =>
      Except.error RevertData.typeMismatch
  | Expr.preDecrement _ =>
      Except.error RevertData.typeMismatch
  | Expr.postIncrement _ =>
      Except.error RevertData.typeMismatch
  | Expr.postDecrement _ =>
      Except.error RevertData.typeMismatch
  | Expr.assignExpr _ _ =>
      Except.error RevertData.typeMismatch
  | Expr.assignOpExpr _ _ _ =>
      Except.error RevertData.typeMismatch
  | Expr.binary BinaryOp.boolAnd lhs rhs => do
      let lhsValue ← lhs.eval context runtime
      let lhsWord ← lhsValue.expectWord
      if wordTruthy lhsWord then
        let rhsValue ← rhs.eval context runtime
        let rhsWord ← rhsValue.expectWord
        Except.ok (Value.word (boolWord (wordTruthy rhsWord)))
      else
        Except.ok (Value.word 0)
  | Expr.binary BinaryOp.boolOr lhs rhs => do
      let lhsValue ← lhs.eval context runtime
      let lhsWord ← lhsValue.expectWord
      if wordTruthy lhsWord then
        Except.ok (Value.word 1)
      else
        let rhsValue ← rhs.eval context runtime
        let rhsWord ← rhsValue.expectWord
        Except.ok (Value.word (boolWord (wordTruthy rhsWord)))
  | Expr.binary op lhs rhs => do
      let lhsValue ← lhs.eval context runtime
      let rhsValue ← rhs.eval context runtime
      BinaryOp.apply context.checked op lhsValue rhsValue
  | Expr.addMod lhs rhs modulus => do
      let lhsValue ← lhs.eval context runtime
      let rhsValue ← rhs.eval context runtime
      let modulusValue ← modulus.eval context runtime
      let lhsWord ← lhsValue.expectWord
      let rhsWord ← rhsValue.expectWord
      let modulusWord ← modulusValue.expectWord
      let value ← checkedAddMod lhsWord rhsWord modulusWord
      Except.ok (Value.word value)
  | Expr.mulMod lhs rhs modulus => do
      let lhsValue ← lhs.eval context runtime
      let rhsValue ← rhs.eval context runtime
      let modulusValue ← modulus.eval context runtime
      let lhsWord ← lhsValue.expectWord
      let rhsWord ← rhsValue.expectWord
      let modulusWord ← modulusValue.expectWord
      let value ← checkedMulMod lhsWord rhsWord modulusWord
      Except.ok (Value.word value)
  | Expr.concatBytes exprs => do
      let values ← Expr.evalList context runtime exprs
      match Value.concatBytes? values with
      | some bs => Except.ok (Value.bytes bs)
      | none => Except.error RevertData.typeMismatch
  | Expr.fixedBytesIndex size base idx => do
      let baseValue ← base.eval context runtime
      let word ← baseValue.expectWord
      let indexValue ← idx.eval context runtime
      let indexWord ← indexValue.expectWord
      fixedBytesIndex? size word indexWord
  | Expr.fixedBytesCast targetSize sourceSize expr => do
      let value ← expr.eval context runtime
      let word ← value.expectWord
      fixedBytesCast? targetSize sourceSize word
  | Expr.fixedBytesFromBytes targetSize expr => do
      let value ← expr.eval context runtime
      match value.asBytes? with
      | some bytes => fixedBytesFromBytes? targetSize bytes
      | none => Except.error RevertData.typeMismatch
  | Expr.uintCast bits expr => do
      let value ← expr.eval context runtime
      uintCast? bits value
  | Expr.intCast bits expr => do
      let value ← expr.eval context runtime
      intCast? bits value
  | Expr.keccak256 expr => do
      let value ← expr.eval context runtime
      match value.asBytes? with
      | some bytes => Except.ok (Value.word (keccakWord bytes))
      | none => Except.error RevertData.typeMismatch
  | Expr.erc7201 expr => do
      let value ← expr.eval context runtime
      match value.asBytes? with
      | some bytes => Except.ok (Value.word (erc7201Slot bytes))
      | none => Except.error RevertData.typeMismatch
  | Expr.externalHash kind expr => do
      let value ← expr.eval context runtime
      match value.asBytes? with
      | some bytes =>
          match kind.lookup? context bytes with
          | some hash => Except.ok (Value.word hash)
          | Option.none => Except.error RevertData.typeMismatch
      | Option.none => Except.error RevertData.typeMismatch
  | Expr.ecrecover digestExpr vExpr rExpr sExpr => do
      let digestValue ← digestExpr.eval context runtime
      let vValue ← vExpr.eval context runtime
      let rValue ← rExpr.eval context runtime
      let sValue ← sExpr.eval context runtime
      let digest ← digestValue.expectWord
      let v ← vValue.expectWord
      let r ← rValue.expectWord
      let s ← sValue.expectWord
      let address := context.ecrecoverAt digest v r s
      Except.ok (Value.word address)
  | Expr.tuple exprs => do
      let values ← Expr.evalList context runtime exprs
      Except.ok (Value.tuple values)
  | Expr.fixedArray exprs => do
      let values ← Expr.evalList context runtime exprs
      Except.ok (Value.fixedArray values)
  | Expr.abiEncode tys exprs => do
      let values ← Expr.evalList context runtime exprs
      match abiEncodeValues? tys values with
      | some bytes => Except.ok (Value.bytes bytes)
      | none => Except.error RevertData.typeMismatch
  | Expr.abiEncodeWithSelector selectorExpr tys exprs => do
      let selectorValue ← selectorExpr.eval context runtime
      let selector ← selectorValue.expectWord
      let values ← Expr.evalList context runtime exprs
      match abiEncodeValues? tys values with
      | some bytes =>
          Except.ok
            (Value.bytes
              (wordToBytesBE selectorBytes selector ++ bytes))
      | none => Except.error RevertData.typeMismatch
  | Expr.abiEncodePacked tys exprs => do
      let values ← Expr.evalList context runtime exprs
      match abiEncodePackedValues? tys values with
      | some bytes => Except.ok (Value.bytes bytes)
      | none => Except.error RevertData.typeMismatch
  | Expr.abiDecode tys expr => do
      let value ← expr.eval context runtime
      match value.asBytes? with
      | some bytes =>
          match abiDecodeValues? tys bytes with
          | some [decoded] => Except.ok decoded
          | some decoded => Except.ok (Value.tuple decoded)
          | none => Except.error RevertData.typeMismatch
      | none => Except.error RevertData.typeMismatch
  | Expr.lowLevelCall kind targetExpr calldataExpr valueExpr gasExpr? gasFirst => do
      let targetValue ← targetExpr.eval context runtime
      let target ← targetValue.expectWord
      let calldataValue ← calldataExpr.eval context runtime
      let calldata ←
        match calldataValue.asBytes? with
        | some bytes => Except.ok bytes
        | none => Except.error RevertData.typeMismatch
      let (value, gas?) ←
        match gasExpr? with
        | none => do
            let valueValue ← valueExpr.eval context runtime
            let value ← valueValue.expectWord
            Except.ok (value, none)
        | some gasExpr =>
            if gasFirst then do
              let gasValue ← gasExpr.eval context runtime
              let gas ← gasValue.expectWord
              let valueValue ← valueExpr.eval context runtime
              let value ← valueValue.expectWord
              Except.ok (value, some gas)
            else do
              let valueValue ← valueExpr.eval context runtime
              let value ← valueValue.expectWord
              let gasValue ← gasExpr.eval context runtime
              let gas ← gasValue.expectWord
              Except.ok (value, some gas)
      match context.lookupLowLevelCall? kind target calldata value gas? with
      | some result =>
          Except.ok
            (Value.tuple
              [ Value.word (boolWord result.success)
              , Value.bytes result.output ])
      | none =>
          Except.ok (Value.tuple [Value.word 0, Value.bytes []])
  | Expr.contractCreate contractName constructorArgsExpr valueExpr (some saltExpr) => do
      let argsValue ← constructorArgsExpr.eval context runtime
      let constructorArgs ←
        match argsValue.asBytes? with
        | some bytes => Except.ok bytes
        | none => Except.error RevertData.typeMismatch
      let valueValue ← valueExpr.eval context runtime
      let value ← valueValue.expectWord
      let saltValue ← saltExpr.eval context runtime
      let salt ← saltValue.expectWord
      match context.lookupContractCreation?
          contractName constructorArgs value (some salt) with
      | some result =>
          if result.success then
            Except.ok (Value.word result.address)
          else
            Except.error (RevertData.fromRawBytes result.output)
      | none =>
          Except.error RevertData.empty
  | Expr.contractCreate contractName constructorArgsExpr valueExpr none => do
      let argsValue ← constructorArgsExpr.eval context runtime
      let constructorArgs ←
        match argsValue.asBytes? with
        | some bytes => Except.ok bytes
        | none => Except.error RevertData.typeMismatch
      let valueValue ← valueExpr.eval context runtime
      let value ← valueValue.expectWord
      match context.lookupContractCreation?
          contractName constructorArgs value none with
      | some result =>
          if result.success then
            Except.ok (Value.word result.address)
          else
            Except.error (RevertData.fromRawBytes result.output)
      | none =>
          Except.error RevertData.empty
  | Expr.newBytes lengthExpr => do
      let lengthValue ← lengthExpr.eval context runtime
      let length ← lengthValue.expectWord
      Except.ok
        (Value.bytes
          (List.replicate (SharedSemantics.norm length) 0))
  | Expr.newDynamicArray elementTy lengthExpr => do
      let lengthValue ← lengthExpr.eval context runtime
      let length ← lengthValue.expectWord
      Except.ok
        (Value.dynamicArray
          (List.replicate (SharedSemantics.norm length)
            elementTy.defaultValue))
  | Expr.enumFromUInt maxValue expr => do
      let value : Value ← expr.eval context runtime
      enumFromUIntValue maxValue value
  | Expr.ternary cond thenExpr elseExpr => do
      let condValue ← cond.eval context runtime
      let condWord ← condValue.expectWord
      if wordTruthy condWord then
        thenExpr.eval context runtime
      else
        elseExpr.eval context runtime
  | Expr.length expr => do
      match expr with
      | Expr.var name =>
          match runtime.lookupStorageRef? name with
          | some target => runtime.loadStorageField context target
          | none =>
              let value ← expr.eval context runtime
              match value.length? with
              | some len => Except.ok (Value.word len)
              | none => Except.error RevertData.typeMismatch
      | _ =>
          let value ← expr.eval context runtime
          match value.length? with
          | some len => Except.ok (Value.word len)
          | none => Except.error RevertData.typeMismatch
  | Expr.index base idx => do
      match base with
      | Expr.var name =>
          match runtime.lookupStorageRef? name with
          | some target =>
              let indexValue ← idx.eval context runtime
              runtime.loadStorageIndex context target indexValue
          | none =>
              let baseValue ← base.eval context runtime
              let indexValue ← idx.eval context runtime
              let indexWord ← indexValue.expectWord
              baseValue.index? indexWord
      | _ =>
          let baseValue ← base.eval context runtime
          let indexValue ← idx.eval context runtime
          let indexWord ← indexValue.expectWord
          baseValue.index? indexWord
  | Expr.slice base start stop => do
      let baseValue ← base.eval context runtime
      let startWord? ←
        match start with
        | some expr => do
            let value ← expr.eval context runtime
            let word ← value.expectWord
            Except.ok (some word)
        | none => Except.ok none
      let stopWord? ←
        match stop with
        | some expr => do
            let value ← expr.eval context runtime
            let word ← value.expectWord
            Except.ok (some word)
        | none => Except.ok none
      baseValue.slice? startWord? stopWord?

def Expr.evalList (context : Context) (runtime : Runtime) :
    List Expr -> Except RevertData (List Value)
  | [] => Except.ok []
  | expr :: rest => do
      let value ← expr.eval context runtime
      let values ← Expr.evalList context runtime rest
      Except.ok (value :: values)

end

def LValue.read (context : Context) (runtime : Runtime) :
    LValue -> Except RevertData Value
  | LValue.var name =>
      match runtime.lookupStorageRef? name with
      | some target => runtime.loadStorageField context target
      | none =>
          match runtime.lookupLocal? name with
          | some value => Except.ok value
          | none => Except.error RevertData.typeMismatch
  | LValue.immutable name =>
      runtime.loadImmutableField context name
  | LValue.storage name =>
      runtime.loadStorageField context name
  | LValue.storageIndex name idx => do
      let indexValue ← idx.eval context runtime
      runtime.loadStorageIndex context name indexValue
  | LValue.index base idx => do
      match base with
      | LValue.var name =>
          match runtime.lookupStorageRef? name with
          | some target =>
              let indexValue ← idx.eval context runtime
              runtime.loadStorageIndex context target indexValue
          | none =>
              let baseValue ← base.read context runtime
              let indexValue ← idx.eval context runtime
              let indexWord ← indexValue.expectWord
              baseValue.index? indexWord
      | _ =>
          let baseValue ← base.read context runtime
          let indexValue ← idx.eval context runtime
          let indexWord ← indexValue.expectWord
          baseValue.index? indexWord

def LValue.write (context : Context) (runtime : Runtime)
    (target : LValue) (value : Value) : Except RevertData Runtime :=
  match target with
  | LValue.var name =>
      match runtime.lookupStorageRef? name with
      | some target => runtime.storeStorageField context target value
      | none =>
          match runtime.assignLocal? name value with
          | some updated => Except.ok updated
          | none => Except.error RevertData.typeMismatch
  | LValue.immutable name =>
      runtime.storeImmutableField context name value
  | LValue.storage name =>
      runtime.storeStorageField context name value
  | LValue.storageIndex name idx => do
      let indexValue ← idx.eval context runtime
      runtime.storeStorageIndex context name indexValue value
  | LValue.index base idx => do
      match base with
      | LValue.var name =>
          match runtime.lookupStorageRef? name with
          | some target =>
              let indexValue ← idx.eval context runtime
              runtime.storeStorageIndex context target indexValue value
          | none =>
              let baseValue ← base.read context runtime
              let indexValue ← idx.eval context runtime
              let indexWord ← indexValue.expectWord
              let updatedBase ← baseValue.setIndex? indexWord value
              base.write context runtime updatedBase
        | _ =>
            let baseValue ← base.read context runtime
            let indexValue ← idx.eval context runtime
            let indexWord ← indexValue.expectWord
            let updatedBase ← baseValue.setIndex? indexWord value
            base.write context runtime updatedBase

def Value.oneLike? : Value -> Except RevertData Value
  | Value.word _ => Except.ok (Value.word 1)
  | Value.int _ => Except.ok (Value.int 1)
  | _ => Except.error RevertData.typeMismatch

def LValue.applyIncDec (context : Context) (runtime : Runtime)
    (target : LValue) (op : BinaryOp) (returnOld : Bool) :
    Except RevertData (Value × Runtime) := do
  let oldValue ← target.read context runtime
  let one ← oldValue.oneLike?
  let newValue ← BinaryOp.apply context.checked op oldValue one
  let updated ← target.write context runtime newValue
  if returnOld then
    Except.ok (oldValue, updated)
  else
    Except.ok (newValue, updated)

def LValues.writeTuple? (context : Context) :
    Runtime -> List (Option LValue) -> List Value -> Except RevertData Runtime
  | runtime, [], [] => Except.ok runtime
  | runtime, some target :: targets, value :: values => do
      let updated ← target.write context runtime value
      LValues.writeTuple? context updated targets values
  | runtime, none :: targets, _ :: values =>
      LValues.writeTuple? context runtime targets values
  | _, _, _ => Except.error RevertData.typeMismatch

inductive ResolvedLValue where
  | local : String -> ResolvedLValue
  | immutable : String -> ResolvedLValue
  | storageField : String -> ResolvedLValue
  | storageIndex : String -> Value -> ResolvedLValue
  | valueIndex : ResolvedLValue -> Word -> ResolvedLValue
  deriving Repr

def ResolvedLValue.read (context : Context) (runtime : Runtime) :
    ResolvedLValue -> Except RevertData Value
  | ResolvedLValue.local name =>
      match runtime.lookupLocal? name with
      | some value => Except.ok value
      | none => Except.error RevertData.typeMismatch
  | ResolvedLValue.immutable name =>
      runtime.loadImmutableField context name
  | ResolvedLValue.storageField name =>
      runtime.loadStorageField context name
  | ResolvedLValue.storageIndex name index =>
      runtime.loadStorageIndex context name index
  | ResolvedLValue.valueIndex base index => do
      let baseValue ← base.read context runtime
      baseValue.index? index

def ResolvedLValue.write (context : Context) (runtime : Runtime)
    (target : ResolvedLValue) (value : Value) :
    Except RevertData Runtime :=
  match target with
  | ResolvedLValue.local name =>
      match runtime.assignLocal? name value with
      | some updated => Except.ok updated
      | none => Except.error RevertData.typeMismatch
  | ResolvedLValue.immutable name =>
      runtime.storeImmutableField context name value
  | ResolvedLValue.storageField name =>
      runtime.storeStorageField context name value
  | ResolvedLValue.storageIndex name index =>
      runtime.storeStorageIndex context name index value
  | ResolvedLValue.valueIndex base index => do
      let baseValue ← base.read context runtime
      let updatedBase ← baseValue.setIndex? index value
      base.write context runtime updatedBase

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

mutual

def Expr.resolveLValueWithRuntime (context : Context) :
    Runtime -> Expr -> Except RevertData (ResolvedLValue × Runtime)
  | runtime, Expr.var name =>
      match runtime.lookupStorageRef? name with
      | some target =>
          Except.ok (ResolvedLValue.storageField target, runtime)
      | none =>
          match runtime.lookupLocal? name with
          | some _ => Except.ok (ResolvedLValue.local name, runtime)
          | none => Except.error RevertData.typeMismatch
  | runtime, Expr.immutable name =>
      Except.ok (ResolvedLValue.immutable name, runtime)
  | runtime, Expr.storage name =>
      Except.ok (ResolvedLValue.storageField name, runtime)
  | runtime, Expr.storageIndex name idx => do
      let (indexValue, runtime') ← idx.evalWithRuntime context runtime
      Except.ok (ResolvedLValue.storageIndex name indexValue, runtime')
  | runtime, Expr.index base idx => do
      let (baseTarget, runtime') ← base.resolveLValueWithRuntime context runtime
      let (indexValue, runtime'') ← idx.evalWithRuntime context runtime'
      match baseTarget with
      | ResolvedLValue.storageField name =>
          Except.ok (ResolvedLValue.storageIndex name indexValue, runtime'')
      | _ =>
          let indexWord ← indexValue.expectWord
          Except.ok
            (ResolvedLValue.valueIndex baseTarget indexWord, runtime'')
  | _, _ => Except.error RevertData.typeMismatch

def Expr.evalWithRuntime (context : Context) :
    Runtime -> Expr -> Except RevertData (Value × Runtime)
  | runtime, Expr.word value =>
      Except.ok (Value.word (normWord value), runtime)
  | runtime, Expr.intWord value =>
      Except.ok (Value.int (normWord value), runtime)
  | runtime, Expr.byteArray bytes =>
      Except.ok (Value.bytes (bytes.map normByte), runtime)
  | runtime, Expr.contractAddress name =>
      Except.ok
        ( Value.word
            (SharedSemantics.Call.namedWordAt
              context.contractAddresses name)
        , runtime )
  | runtime, Expr.contractCreationCode name =>
      Except.ok
        ( Value.bytes
            (SharedSemantics.Call.namedBytesAt
              context.contractCreationCodes name)
        , runtime )
  | runtime, Expr.contractRuntimeCode name =>
      Except.ok
        ( Value.bytes
            (SharedSemantics.Call.namedBytesAt
              context.contractRuntimeCodes name)
        , runtime )
  | runtime, Expr.calldata =>
      Except.ok (Value.bytes (context.calldata.map normByte), runtime)
  | runtime, Expr.msgSig =>
      Except.ok (Value.word (calldataSelectorWord context.calldata), runtime)
  | runtime, Expr.caller =>
      Except.ok (Value.word context.sender, runtime)
  | runtime, Expr.callValue =>
      Except.ok (Value.word context.value, runtime)
  | runtime, Expr.self =>
      Except.ok (Value.word context.self, runtime)
  | runtime, Expr.env which =>
      Except.ok (Value.word (which.eval context), runtime)
  | runtime, Expr.envLookup which keyExpr => do
      let (keyValue, runtime') ← keyExpr.evalWithRuntime context runtime
      let key ← keyValue.expectWord
      Except.ok (Value.word (which.eval context key), runtime')
  | runtime, Expr.envBytesLookup which keyExpr => do
      let (keyValue, runtime') ← keyExpr.evalWithRuntime context runtime
      let key ← keyValue.expectWord
      Except.ok (Value.bytes (which.eval context key), runtime')
  | runtime, Expr.var name =>
      match runtime.lookupStorageRef? name with
      | some target => do
          let value ← runtime.loadStorageField context target
          Except.ok (value, runtime)
      | none =>
          match runtime.lookupLocal? name with
          | some value => Except.ok (value, runtime)
          | none => Except.error RevertData.typeMismatch
  | runtime, Expr.immutable name => do
      let value ← runtime.loadImmutableField context name
      Except.ok (value, runtime)
  | runtime, Expr.storage name => do
      let value ← runtime.loadStorageField context name
      Except.ok (value, runtime)
  | runtime, Expr.storageBytes name => do
      let value ← runtime.loadStorageByteStringField context name
      Except.ok (value, runtime)
  | runtime, Expr.storageIndex name idx => do
      let (indexValue, runtime') ← idx.evalWithRuntime context runtime
      let value ← runtime'.loadStorageIndex context name indexValue
      Except.ok (value, runtime')
  | runtime, Expr.storagePath name indexes => do
      let (indexValues, runtime') ←
        Expr.evalListWithRuntime context runtime indexes
      let value ← runtime'.loadStoragePath context name indexValues
      Except.ok (value, runtime')
  | runtime, Expr.externalFunctionSelector expr => do
      let (value, runtime') ← expr.evalWithRuntime context runtime
      match value with
      | Value.externalFunction _ selector =>
          Except.ok (Value.word selector, runtime')
      | _ => Except.error RevertData.typeMismatch
  | runtime, Expr.externalFunctionAddress expr => do
      let (value, runtime') ← expr.evalWithRuntime context runtime
      match value with
      | Value.externalFunction addr _ =>
          Except.ok (Value.word addr, runtime')
      | _ => Except.error RevertData.typeMismatch
  | runtime, Expr.unary op expr => do
      let (value, runtime') ← expr.evalWithRuntime context runtime
      let result ← op.apply context.checked value
      Except.ok (result, runtime')
  | runtime, Expr.preIncrement target => do
      let (resolved, runtime') ←
        target.resolveLValueWithRuntime context runtime
      resolved.applyIncDec context runtime' BinaryOp.add false
  | runtime, Expr.preDecrement target => do
      let (resolved, runtime') ←
        target.resolveLValueWithRuntime context runtime
      resolved.applyIncDec context runtime' BinaryOp.sub false
  | runtime, Expr.postIncrement target => do
      let (resolved, runtime') ←
        target.resolveLValueWithRuntime context runtime
      resolved.applyIncDec context runtime' BinaryOp.add true
  | runtime, Expr.postDecrement target => do
      let (resolved, runtime') ←
        target.resolveLValueWithRuntime context runtime
      resolved.applyIncDec context runtime' BinaryOp.sub true
  | runtime, Expr.assignExpr target rhs => do
      let (value, runtime') ← rhs.evalWithRuntime context runtime
      let (resolved, runtime'') ←
        target.resolveLValueWithRuntime context runtime'
      let updated ← resolved.write context runtime'' value
      Except.ok (value, updated)
  | runtime, Expr.assignOpExpr target op rhs => do
      let (resolved, runtime') ←
        target.resolveLValueWithRuntime context runtime
      let lhsValue ← resolved.read context runtime'
      let (rhsValue, runtime'') ← rhs.evalWithRuntime context runtime'
      let value ← BinaryOp.apply context.checked op lhsValue rhsValue
      let updated ← resolved.write context runtime'' value
      Except.ok (value, updated)
  | runtime, Expr.binary BinaryOp.boolAnd lhs rhs => do
      let (lhsValue, runtime') ← lhs.evalWithRuntime context runtime
      let lhsWord ← lhsValue.expectWord
      if wordTruthy lhsWord then
        let (rhsValue, runtime'') ← rhs.evalWithRuntime context runtime'
        let rhsWord ← rhsValue.expectWord
        Except.ok (Value.word (boolWord (wordTruthy rhsWord)), runtime'')
      else
        Except.ok (Value.word 0, runtime')
  | runtime, Expr.binary BinaryOp.boolOr lhs rhs => do
      let (lhsValue, runtime') ← lhs.evalWithRuntime context runtime
      let lhsWord ← lhsValue.expectWord
      if wordTruthy lhsWord then
        Except.ok (Value.word 1, runtime')
      else
        let (rhsValue, runtime'') ← rhs.evalWithRuntime context runtime'
        let rhsWord ← rhsValue.expectWord
        Except.ok (Value.word (boolWord (wordTruthy rhsWord)), runtime'')
  | runtime, Expr.binary op lhs rhs => do
      let (lhsValue, runtime') ← lhs.evalWithRuntime context runtime
      let (rhsValue, runtime'') ← rhs.evalWithRuntime context runtime'
      let value ← BinaryOp.apply context.checked op lhsValue rhsValue
      Except.ok (value, runtime'')
  | runtime, Expr.addMod lhs rhs modulus => do
      let (lhsValue, runtime') ← lhs.evalWithRuntime context runtime
      let (rhsValue, runtime'') ← rhs.evalWithRuntime context runtime'
      let (modulusValue, runtime''') ← modulus.evalWithRuntime context runtime''
      let lhsWord ← lhsValue.expectWord
      let rhsWord ← rhsValue.expectWord
      let modulusWord ← modulusValue.expectWord
      let value ← checkedAddMod lhsWord rhsWord modulusWord
      Except.ok (Value.word value, runtime''')
  | runtime, Expr.mulMod lhs rhs modulus => do
      let (lhsValue, runtime') ← lhs.evalWithRuntime context runtime
      let (rhsValue, runtime'') ← rhs.evalWithRuntime context runtime'
      let (modulusValue, runtime''') ← modulus.evalWithRuntime context runtime''
      let lhsWord ← lhsValue.expectWord
      let rhsWord ← rhsValue.expectWord
      let modulusWord ← modulusValue.expectWord
      let value ← checkedMulMod lhsWord rhsWord modulusWord
      Except.ok (Value.word value, runtime''')
  | runtime, Expr.concatBytes exprs => do
      let (values, runtime') ← Expr.evalListWithRuntime context runtime exprs
      match Value.concatBytes? values with
      | some bs => Except.ok (Value.bytes bs, runtime')
      | none => Except.error RevertData.typeMismatch
  | runtime, Expr.fixedBytesIndex size base idx => do
      let (baseValue, runtime') ← base.evalWithRuntime context runtime
      let word ← baseValue.expectWord
      let (indexValue, runtime'') ← idx.evalWithRuntime context runtime'
      let indexWord ← indexValue.expectWord
      let value ← fixedBytesIndex? size word indexWord
      Except.ok (value, runtime'')
  | runtime, Expr.fixedBytesCast targetSize sourceSize expr => do
      let (value, runtime') ← expr.evalWithRuntime context runtime
      let word ← value.expectWord
      let casted ← fixedBytesCast? targetSize sourceSize word
      Except.ok (casted, runtime')
  | runtime, Expr.fixedBytesFromBytes targetSize expr => do
      let (value, runtime') ← expr.evalWithRuntime context runtime
      match value.asBytes? with
      | some bytes => do
          let casted ← fixedBytesFromBytes? targetSize bytes
          Except.ok (casted, runtime')
      | none => Except.error RevertData.typeMismatch
  | runtime, Expr.uintCast bits expr => do
      let (value, runtime') ← expr.evalWithRuntime context runtime
      let casted ← uintCast? bits value
      Except.ok (casted, runtime')
  | runtime, Expr.intCast bits expr => do
      let (value, runtime') ← expr.evalWithRuntime context runtime
      let casted ← intCast? bits value
      Except.ok (casted, runtime')
  | runtime, Expr.keccak256 expr => do
      let (value, runtime') ← expr.evalWithRuntime context runtime
      match value.asBytes? with
      | some bytes => Except.ok (Value.word (keccakWord bytes), runtime')
      | none => Except.error RevertData.typeMismatch
  | runtime, Expr.erc7201 expr => do
      let (value, runtime') ← expr.evalWithRuntime context runtime
      match value.asBytes? with
      | some bytes => Except.ok (Value.word (erc7201Slot bytes), runtime')
      | none => Except.error RevertData.typeMismatch
  | runtime, Expr.externalHash kind expr => do
      let (value, runtime') ← expr.evalWithRuntime context runtime
      match value.asBytes? with
      | some bytes =>
          match kind.lookup? context bytes with
          | some hash => Except.ok (Value.word hash, runtime')
          | none => Except.error RevertData.typeMismatch
      | none => Except.error RevertData.typeMismatch
  | runtime, Expr.ecrecover digestExpr vExpr rExpr sExpr => do
      let (digestValue, runtime') ← digestExpr.evalWithRuntime context runtime
      let (vValue, runtime'') ← vExpr.evalWithRuntime context runtime'
      let (rValue, runtime''') ← rExpr.evalWithRuntime context runtime''
      let (sValue, runtime'''') ← sExpr.evalWithRuntime context runtime'''
      let digest ← digestValue.expectWord
      let v ← vValue.expectWord
      let r ← rValue.expectWord
      let s ← sValue.expectWord
      let address := context.ecrecoverAt digest v r s
      Except.ok (Value.word address, runtime'''')
  | runtime, Expr.tuple exprs => do
      let (values, runtime') ← Expr.evalListWithRuntime context runtime exprs
      Except.ok (Value.tuple values, runtime')
  | runtime, Expr.fixedArray exprs => do
      let (values, runtime') ← Expr.evalListWithRuntime context runtime exprs
      Except.ok (Value.fixedArray values, runtime')
  | runtime, Expr.abiEncode tys exprs => do
      let (values, runtime') ← Expr.evalListWithRuntime context runtime exprs
      match abiEncodeValues? tys values with
      | some bytes => Except.ok (Value.bytes bytes, runtime')
      | none => Except.error RevertData.typeMismatch
  | runtime, Expr.abiEncodeWithSelector selectorExpr tys exprs => do
      let (selectorValue, runtime') ←
        selectorExpr.evalWithRuntime context runtime
      let selector ← selectorValue.expectWord
      let (values, runtime'') ←
        Expr.evalListWithRuntime context runtime' exprs
      match abiEncodeValues? tys values with
      | some bytes =>
          Except.ok
            ( Value.bytes (wordToBytesBE selectorBytes selector ++ bytes)
            , runtime'' )
      | none => Except.error RevertData.typeMismatch
  | runtime, Expr.abiEncodePacked tys exprs => do
      let (values, runtime') ← Expr.evalListWithRuntime context runtime exprs
      match abiEncodePackedValues? tys values with
      | some bytes => Except.ok (Value.bytes bytes, runtime')
      | none => Except.error RevertData.typeMismatch
  | runtime, Expr.abiDecode tys expr => do
      let (value, runtime') ← expr.evalWithRuntime context runtime
      match value.asBytes? with
      | some bytes =>
          match abiDecodeValues? tys bytes with
          | some [decoded] => Except.ok (decoded, runtime')
          | some decoded => Except.ok (Value.tuple decoded, runtime')
          | none => Except.error RevertData.typeMismatch
      | none => Except.error RevertData.typeMismatch
  | runtime, Expr.lowLevelCall kind targetExpr calldataExpr valueExpr
      gasExpr? gasFirst => do
      let (targetValue, runtime') ← targetExpr.evalWithRuntime context runtime
      let target ← targetValue.expectWord
      let (calldataValue, runtime'') ←
        calldataExpr.evalWithRuntime context runtime'
      let calldata ←
        match calldataValue.asBytes? with
        | some bytes => Except.ok bytes
        | none => Except.error RevertData.typeMismatch
      let (value, gas?, runtime''') ←
        match gasExpr? with
        | none => do
            let (valueValue, runtime''') ←
              valueExpr.evalWithRuntime context runtime''
            let value ← valueValue.expectWord
            Except.ok (value, none, runtime''')
        | some gasExpr =>
            if gasFirst then do
              let (gasValue, runtimeGas) ←
                gasExpr.evalWithRuntime context runtime''
              let gas ← gasValue.expectWord
              let (valueValue, runtimeValue) ←
                valueExpr.evalWithRuntime context runtimeGas
              let value ← valueValue.expectWord
              Except.ok (value, some gas, runtimeValue)
            else do
              let (valueValue, runtimeValue) ←
                valueExpr.evalWithRuntime context runtime''
              let value ← valueValue.expectWord
              let (gasValue, runtimeGas) ←
                gasExpr.evalWithRuntime context runtimeValue
              let gas ← gasValue.expectWord
              Except.ok (value, some gas, runtimeGas)
      match context.lookupLowLevelCall? kind target calldata value gas? with
      | some result =>
          Except.ok
            ( Value.tuple
                [ Value.word (boolWord result.success)
                , Value.bytes result.output ]
            , runtime''' )
      | none =>
          Except.ok (Value.tuple [Value.word 0, Value.bytes []], runtime''')
  | runtime, Expr.contractCreate contractName constructorArgsExpr valueExpr
      (some saltExpr) => do
      let (argsValue, runtime') ←
        constructorArgsExpr.evalWithRuntime context runtime
      let constructorArgs ←
        match argsValue.asBytes? with
        | some bytes => Except.ok bytes
        | none => Except.error RevertData.typeMismatch
      let (valueValue, runtime'') ← valueExpr.evalWithRuntime context runtime'
      let value ← valueValue.expectWord
      let (saltValue, runtime''') ← saltExpr.evalWithRuntime context runtime''
      let salt ← saltValue.expectWord
      match context.lookupContractCreation?
          contractName constructorArgs value (some salt) with
      | some result =>
          if result.success then
            Except.ok (Value.word result.address, runtime''')
          else
            Except.error (RevertData.fromRawBytes result.output)
      | none => Except.error RevertData.empty
  | runtime, Expr.contractCreate contractName constructorArgsExpr valueExpr none => do
      let (argsValue, runtime') ←
        constructorArgsExpr.evalWithRuntime context runtime
      let constructorArgs ←
        match argsValue.asBytes? with
        | some bytes => Except.ok bytes
        | none => Except.error RevertData.typeMismatch
      let (valueValue, runtime'') ← valueExpr.evalWithRuntime context runtime'
      let value ← valueValue.expectWord
      match context.lookupContractCreation?
          contractName constructorArgs value none with
      | some result =>
          if result.success then
            Except.ok (Value.word result.address, runtime'')
          else
            Except.error (RevertData.fromRawBytes result.output)
      | none => Except.error RevertData.empty
  | runtime, Expr.newBytes lengthExpr => do
      let (lengthValue, runtime') ← lengthExpr.evalWithRuntime context runtime
      let length ← lengthValue.expectWord
      Except.ok
        ( Value.bytes (List.replicate (SharedSemantics.norm length) 0)
        , runtime' )
  | runtime, Expr.newDynamicArray elementTy lengthExpr => do
      let (lengthValue, runtime') ← lengthExpr.evalWithRuntime context runtime
      let length ← lengthValue.expectWord
      Except.ok
        ( Value.dynamicArray
            (List.replicate (SharedSemantics.norm length)
              elementTy.defaultValue)
        , runtime' )
  | runtime, Expr.enumFromUInt maxValue expr => do
      let (value, runtime') ← expr.evalWithRuntime context runtime
      let coerced ← enumFromUIntValue maxValue value
      Except.ok (coerced, runtime')
  | runtime, Expr.ternary cond thenExpr elseExpr => do
      let (condValue, runtime') ← cond.evalWithRuntime context runtime
      let condWord ← condValue.expectWord
      if wordTruthy condWord then
        thenExpr.evalWithRuntime context runtime'
      else
        elseExpr.evalWithRuntime context runtime'
  | runtime, Expr.length expr => do
      match expr with
      | Expr.var name =>
          match runtime.lookupStorageRef? name with
          | some target => do
              let value ← runtime.loadStorageField context target
              match value.length? with
              | some len => Except.ok (Value.word len, runtime)
              | none => Except.error RevertData.typeMismatch
          | none =>
              let (value, runtime') ← expr.evalWithRuntime context runtime
              match value.length? with
              | some len => Except.ok (Value.word len, runtime')
              | none => Except.error RevertData.typeMismatch
      | _ =>
          let (value, runtime') ← expr.evalWithRuntime context runtime
          match value.length? with
          | some len => Except.ok (Value.word len, runtime')
          | none => Except.error RevertData.typeMismatch
  | runtime, Expr.index base idx => do
      match base with
      | Expr.var name =>
          match runtime.lookupStorageRef? name with
          | some target =>
              let (indexValue, runtime') ← idx.evalWithRuntime context runtime
              let value ← runtime'.loadStorageIndex context target indexValue
              Except.ok (value, runtime')
          | none =>
              let (baseValue, runtime') ← base.evalWithRuntime context runtime
              let (indexValue, runtime'') ← idx.evalWithRuntime context runtime'
              let indexWord ← indexValue.expectWord
              let value ← baseValue.index? indexWord
              Except.ok (value, runtime'')
      | _ =>
          let (baseValue, runtime') ← base.evalWithRuntime context runtime
          let (indexValue, runtime'') ← idx.evalWithRuntime context runtime'
          let indexWord ← indexValue.expectWord
          let value ← baseValue.index? indexWord
          Except.ok (value, runtime'')
  | runtime, Expr.slice base start stop => do
      let (baseValue, runtime') ← base.evalWithRuntime context runtime
      let (startWord?, runtime'') ←
        match start with
        | some expr => do
            let (value, updated) ← expr.evalWithRuntime context runtime'
            let word ← value.expectWord
            Except.ok (some word, updated)
        | none => Except.ok (none, runtime')
      let (stopWord?, runtime''') ←
        match stop with
        | some expr => do
            let (value, updated) ← expr.evalWithRuntime context runtime''
            let word ← value.expectWord
            Except.ok (some word, updated)
        | none => Except.ok (none, runtime'')
      let value ← baseValue.slice? startWord? stopWord?
      Except.ok (value, runtime''')

def Expr.evalListWithRuntime (context : Context) :
    Runtime -> List Expr -> Except RevertData (List Value × Runtime)
  | runtime, [] => Except.ok ([], runtime)
  | runtime, expr :: rest => do
      let (value, runtime') ← expr.evalWithRuntime context runtime
      let (values, runtime'') ← Expr.evalListWithRuntime context runtime' rest
      Except.ok (value :: values, runtime'')

end

def LValue.resolveWithRuntime (target : LValue) (context : Context)
    (runtime : Runtime) : Except RevertData (ResolvedLValue × Runtime) :=
  target.toExpr.resolveLValueWithRuntime context runtime

def LValues.writeTupleWithRuntime? (context : Context) :
    Runtime -> List (Option LValue) -> List Value -> Except RevertData Runtime
  | runtime, [], [] => Except.ok runtime
  | runtime, some target :: targets, value :: values => do
      let (resolved, runtime') ← target.resolveWithRuntime context runtime
      let updated ← resolved.write context runtime' value
      LValues.writeTupleWithRuntime? context updated targets values
  | runtime, none :: targets, _ :: values =>
      LValues.writeTupleWithRuntime? context runtime targets values
  | _, _, _ => Except.error RevertData.typeMismatch

structure BindingDecl where
  name : String
  ty : Ty
  deriving Repr

mutual

inductive Stmt where
  | skip : Stmt
  | block : List Stmt -> Stmt
  | varDecl : Ty -> String -> Option Expr -> Stmt
  | storageAlias : String -> String -> Stmt
  | storageAliasFrom : String -> String -> Stmt
  | storageAliasAssign : String -> String -> Stmt
  | storageAliasAssignFrom : String -> String -> Stmt
  | exprStmt : Expr -> Stmt
  | assign : LValue -> Expr -> Stmt
  | assignTuple : List (Option LValue) -> Expr -> Stmt
  | assignOp : LValue -> BinaryOp -> Expr -> Stmt
  | deleteValue : LValue -> Stmt
  | storageArrayPush : String -> Option Expr -> Stmt
  | storageArrayPushRef : String -> Option Expr -> Stmt
  | storageArrayPop : String -> Stmt
  | storageArrayPopRef : String -> Stmt
  | assertStmt : Expr -> Stmt
  | requireStmt : Expr -> Option String -> Stmt
  | requireErrorExpr : Expr -> Expr -> Stmt
  | requireCustom : Expr -> String -> List Expr -> Stmt
  | captureReturn : List String -> Stmt -> Stmt
  | ifElse : Expr -> Stmt -> Stmt -> Stmt
  | switch : Expr -> List (Word × Stmt) -> Option Stmt -> Stmt
  | whileLoop : Expr -> Stmt -> Stmt
  | doWhile : Stmt -> Expr -> Stmt
  | forLoop : Stmt -> Expr -> Stmt -> Stmt -> Stmt
  | tryExternalCall :
      LowLevelCallKind -> Expr -> Expr -> Expr -> Option Expr -> Bool ->
      Bool -> List BindingDecl -> Stmt -> List TryCatchClause -> Stmt
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
                events := SharedSemantics.Log.append
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

def Stmt.findSwitchBranch? (value : Word) :
    List (Word × Stmt) -> Option Stmt
  | [] => none
  | (label, body) :: rest =>
      if wordEq label value then
        some body
      else
        Stmt.findSwitchBranch? value rest

mutual

def Stmt.eval (fuel : Nat) (context : Context)
    (runtime : Runtime) : Stmt -> Option Result :=
  match fuel with
  | 0 => fun _ => none
  | fuel + 1 => fun stmt =>
      match stmt with
      | Stmt.skip => some (Result.normal runtime)
      | Stmt.block body =>
          match Stmt.evalList fuel context runtime.pushScope body with
          | some result => some (result.mapRuntime Runtime.popScope)
          | none => none
      | Stmt.varDecl ty name init =>
          match init with
          | some expr =>
              match expr.evalWithRuntime context runtime with
              | Except.ok (value, runtime') =>
                  match ty.coerceValue? value with
                  | some coerced =>
                      some
                        (Result.normal
                          (runtime'.declareLocal name coerced))
                  | none =>
                      some (Result.reverted runtime RevertData.typeMismatch)
              | Except.error err =>
                  some (Result.reverted runtime err)
          | none =>
              some
                (Result.normal
                  (runtime.declareLocal name ty.defaultValue))
      | Stmt.storageAlias name target =>
          some
            (Result.normal
              (runtime.declareLocal name (Value.storageRef target)))
      | Stmt.storageAliasFrom name source =>
          match runtime.lookupStorageRef? source with
          | some target =>
              some
                (Result.normal
                  (runtime.declareLocal name (Value.storageRef target)))
          | none => some (Result.reverted runtime RevertData.typeMismatch)
      | Stmt.storageAliasAssign name target =>
          match runtime.assignStorageRef? name target with
          | some updated => some (Result.normal updated)
          | none => some (Result.reverted runtime RevertData.typeMismatch)
      | Stmt.storageAliasAssignFrom name source =>
          match runtime.lookupStorageRef? source with
          | some target =>
              match runtime.assignStorageRef? name target with
              | some updated => some (Result.normal updated)
              | none => some (Result.reverted runtime RevertData.typeMismatch)
          | none => some (Result.reverted runtime RevertData.typeMismatch)
      | Stmt.exprStmt expr =>
          match expr.evalWithRuntime context runtime with
          | Except.ok (_, runtime') => some (Result.normal runtime')
          | Except.error err => some (Result.reverted runtime err)
      | Stmt.assign target expr =>
          match expr.evalWithRuntime context runtime with
          | Except.ok (value, runtime') =>
              match target.resolveWithRuntime context runtime' with
              | Except.ok (resolved, runtime'') =>
                  match resolved.write context runtime'' value with
                  | Except.ok updated => some (Result.normal updated)
                  | Except.error err => some (Result.reverted runtime err)
              | Except.error err => some (Result.reverted runtime err)
          | Except.error err => some (Result.reverted runtime err)
      | Stmt.assignTuple targets expr =>
          match expr.evalWithRuntime context runtime with
          | Except.ok (Value.tuple values, runtime') =>
              match LValues.writeTupleWithRuntime? context runtime' targets values with
              | Except.ok updated => some (Result.normal updated)
              | Except.error err => some (Result.reverted runtime err)
          | Except.ok _ => some (Result.reverted runtime RevertData.typeMismatch)
          | Except.error err => some (Result.reverted runtime err)
      | Stmt.assignOp target op expr =>
          match target.resolveWithRuntime context runtime with
          | Except.ok (resolved, runtime') =>
              match resolved.read context runtime' with
              | Except.ok lhs =>
                  match expr.evalWithRuntime context runtime' with
                  | Except.ok (rhs, runtime'') =>
                      match BinaryOp.apply context.checked op lhs rhs with
                      | Except.ok value =>
                          match resolved.write context runtime'' value with
                          | Except.ok updated => some (Result.normal updated)
                          | Except.error err => some (Result.reverted runtime err)
                      | Except.error err => some (Result.reverted runtime err)
                  | Except.error err => some (Result.reverted runtime err)
              | Except.error err => some (Result.reverted runtime err)
          | Except.error err => some (Result.reverted runtime err)
      | Stmt.deleteValue target =>
          match target with
          | LValue.storage name =>
              match runtime.deleteStorageField context name with
              | Except.ok updated => some (Result.normal updated)
              | Except.error err => some (Result.reverted runtime err)
          | LValue.var name =>
              match runtime.lookupStorageRef? name with
              | some _ =>
                  some (Result.reverted runtime RevertData.typeMismatch)
              | none =>
                  match target.resolveWithRuntime context runtime with
                  | Except.ok (resolved, runtime') =>
                      match resolved.read context runtime' with
                      | Except.ok value =>
                        match resolved.write context runtime' value.defaultLike with
                        | Except.ok updated => some (Result.normal updated)
                        | Except.error err => some (Result.reverted runtime err)
                      | Except.error err => some (Result.reverted runtime err)
                  | Except.error err => some (Result.reverted runtime err)
          | _ =>
              match target.resolveWithRuntime context runtime with
              | Except.ok (resolved, runtime') =>
                  match resolved.read context runtime' with
                  | Except.ok value =>
                      match resolved.write context runtime' value.defaultLike with
                      | Except.ok updated => some (Result.normal updated)
                      | Except.error err => some (Result.reverted runtime err)
                  | Except.error err => some (Result.reverted runtime err)
              | Except.error err => some (Result.reverted runtime err)
      | Stmt.storageArrayPush name value? =>
          match value? with
          | some expr =>
              match expr.evalWithRuntime context runtime with
              | Except.ok (value, runtime') =>
                  match runtime'.storageArrayPush context name (some value) with
                  | Except.ok updated => some (Result.normal updated)
                  | Except.error err => some (Result.reverted runtime err)
              | Except.error err => some (Result.reverted runtime err)
          | none =>
              match runtime.storageArrayPush context name none with
              | Except.ok updated => some (Result.normal updated)
              | Except.error err => some (Result.reverted runtime err)
      | Stmt.storageArrayPushRef name value? =>
          match runtime.lookupStorageRef? name, value? with
          | some target, some expr =>
              match expr.evalWithRuntime context runtime with
              | Except.ok (value, runtime') =>
                  match runtime'.storageArrayPush context target (some value) with
                  | Except.ok updated => some (Result.normal updated)
                  | Except.error err => some (Result.reverted runtime err)
              | Except.error err => some (Result.reverted runtime err)
          | some target, none =>
              match runtime.storageArrayPush context target none with
              | Except.ok updated => some (Result.normal updated)
              | Except.error err => some (Result.reverted runtime err)
          | none, _ => some (Result.reverted runtime RevertData.typeMismatch)
      | Stmt.storageArrayPop name =>
          match runtime.storageArrayPop context name with
          | Except.ok updated => some (Result.normal updated)
          | Except.error err => some (Result.reverted runtime err)
      | Stmt.storageArrayPopRef name =>
          match runtime.lookupStorageRef? name with
          | some target =>
              match runtime.storageArrayPop context target with
              | Except.ok updated => some (Result.normal updated)
              | Except.error err => some (Result.reverted runtime err)
          | none => some (Result.reverted runtime RevertData.typeMismatch)
      | Stmt.assertStmt cond =>
          match cond.evalWithRuntime context runtime with
          | Except.ok (value, runtime') =>
              match value.expectWord with
              | Except.ok word =>
                  if wordTruthy word then
                    some (Result.normal runtime')
                  else
                    some (Result.reverted runtime' RevertData.assertFailure)
              | Except.error err => some (Result.reverted runtime' err)
          | Except.error err => some (Result.reverted runtime err)
      | Stmt.requireStmt cond reason =>
          match cond.evalWithRuntime context runtime with
          | Except.ok (value, runtime') =>
              match value.expectWord with
              | Except.ok word =>
                  if wordTruthy word then
                    some (Result.normal runtime')
                  else
                    match reason with
                    | some message =>
                        some (Result.reverted runtime' (RevertData.error message))
                    | none =>
                        some (Result.reverted runtime' RevertData.empty)
              | Except.error err => some (Result.reverted runtime' err)
          | Except.error err => some (Result.reverted runtime err)
      | Stmt.requireErrorExpr cond reasonExpr =>
          match cond.evalWithRuntime context runtime with
          | Except.ok (value, runtime') =>
              match reasonExpr.evalWithRuntime context runtime' with
              | Except.ok (reasonValue, runtime'') =>
                  match value.expectWord with
                  | Except.ok word =>
                      if wordTruthy word then
                        some (Result.normal runtime'')
                      else
                        match errorStringBytesRevert? reasonValue with
                        | some payload =>
                            some (Result.reverted runtime'' payload)
                        | none =>
                            some (Result.reverted runtime''
                              RevertData.typeMismatch)
                  | Except.error err => some (Result.reverted runtime'' err)
              | Except.error err => some (Result.reverted runtime' err)
          | Except.error err => some (Result.reverted runtime err)
      | Stmt.requireCustom cond name exprs =>
          match cond.evalWithRuntime context runtime with
          | Except.ok (value, runtime') =>
              match Expr.evalListWithRuntime context runtime' exprs with
              | Except.ok (args, runtime'') =>
                  match value.expectWord with
                  | Except.ok word =>
                      if wordTruthy word then
                        some (Result.normal runtime'')
                      else
                        some
                          (Result.reverted runtime''
                            (RevertData.custom name args))
                  | Except.error err => some (Result.reverted runtime'' err)
              | Except.error err => some (Result.reverted runtime' err)
          | Except.error err => some (Result.reverted runtime err)
      | Stmt.captureReturn returnNames body =>
          match Stmt.eval fuel context runtime body with
          | some (Result.returned runtime' values) =>
              if values.isEmpty || returnNames.isEmpty then
                some (Result.normal runtime')
              else
                match runtime'.assignNamedValues? returnNames values with
                | some updated => some (Result.normal updated)
                | none => some (Result.reverted runtime' RevertData.typeMismatch)
          | some result => some result
          | none => none
      | Stmt.ifElse cond thenBranch elseBranch =>
          match cond.evalWithRuntime context runtime with
          | Except.ok (value, runtime') =>
              match value.expectWord with
              | Except.ok word =>
                  if wordTruthy word then
                    Stmt.eval fuel context runtime' thenBranch
                  else
                    Stmt.eval fuel context runtime' elseBranch
              | Except.error err => some (Result.reverted runtime' err)
          | Except.error err => some (Result.reverted runtime err)
      | Stmt.switch discr cases defaultBranch =>
          match discr.evalWithRuntime context runtime with
          | Except.ok (value, runtime') =>
              match value.expectWord with
              | Except.ok word =>
                  match Stmt.findSwitchBranch? word cases, defaultBranch with
                  | some branch, _ => Stmt.eval fuel context runtime' branch
                  | none, some branch => Stmt.eval fuel context runtime' branch
                  | none, none => some (Result.normal runtime')
              | Except.error err => some (Result.reverted runtime' err)
          | Except.error err => some (Result.reverted runtime err)
      | Stmt.whileLoop cond body =>
          Stmt.evalWhile fuel context runtime cond body
      | Stmt.doWhile body cond =>
          Stmt.evalDoWhile fuel context runtime body cond
      | Stmt.forLoop init cond post body =>
          let loopRuntime := runtime.pushScope
          match Stmt.eval fuel context loopRuntime init with
          | some (Result.normal initialized) =>
              match Stmt.evalFor fuel context initialized cond post body with
              | some result => some (result.mapRuntime Runtime.popScope)
              | none => none
          | some result => some (result.mapRuntime Runtime.popScope)
          | none => none
        | Stmt.tryExternalCall kind targetExpr calldataExpr valueExpr
            gasExpr? gasFirst checkTargetCode returns successBody
            catchClauses =>
            match targetExpr.evalWithRuntime context runtime with
            | Except.ok (targetValue, runtime') =>
                match targetValue.expectWord with
                | Except.ok target =>
                    match calldataExpr.evalWithRuntime context runtime' with
                    | Except.ok (calldataValue, runtime'') =>
                        match calldataValue.asBytes? with
                        | some calldata =>
                            let valueGasResult? :
                                Except (Runtime × RevertData)
                                  (Word × Option Word × Runtime) :=
                              match gasExpr? with
                              | none =>
                                  match valueExpr.evalWithRuntime context runtime'' with
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
                                    match gasExpr.evalWithRuntime context runtime'' with
                                    | Except.ok (gasValue, runtimeGas) =>
                                        match gasValue.expectWord with
                                        | Except.ok gas =>
                                            match valueExpr.evalWithRuntime
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
                                    match valueExpr.evalWithRuntime
                                        context runtime'' with
                                    | Except.ok (valueValue, runtimeValue) =>
                                        match valueValue.expectWord with
                                        | Except.ok value =>
                                            match gasExpr.evalWithRuntime
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
                            | Except.ok (value, gas?, runtime''') =>
                                    let missingCode :=
                                      checkTargetCode &&
                                        !(context.accountHasCode target)
                                    let callResult? :=
                                      if missingCode then
                                        none
                                      else
                                        context.lookupLowLevelCall?
                                          kind target calldata value gas?
                                    let success :=
                                      match callResult? with
                                      | some result => result.success
                                      | none => false
                                    let output :=
                                      match callResult? with
                                      | some result => result.output.map normByte
                                      | none => []
                                    if success then
                                      match abiDecodeValues?
                                          (returns.map BindingDecl.ty) output with
                                        | some decoded =>
                                            match BindingDecl.bindArgs?
                                                returns decoded with
                                            | some frame =>
                                                match Stmt.eval fuel context
                                                    (runtime'''.withFrame frame)
                                                    successBody with
                                                | some result =>
                                                    some
                                                    (result.mapRuntime
                                                      Runtime.popScope)
                                                | none => none
                                            | none =>
                                                some
                                                  (Result.reverted runtime'''
                                                    RevertData.typeMismatch)
                                        | none =>
                                            some
                                              (Result.reverted runtime'''
                                                RevertData.typeMismatch)
                                    else
                                        match TryCatchClause.findMatch?
                                            output catchClauses with
                                        | some (frame, body) =>
                                            match Stmt.eval fuel context
                                                (runtime'''.withFrame frame) body with
                                            | some result =>
                                                some
                                                (result.mapRuntime
                                                  Runtime.popScope)
                                            | none => none
                                        | none =>
                                            some
                                              (Result.reverted runtime'''
                                                (RevertData.fromRawBytes output))
                            | Except.error (runtimeFailed, err) =>
                                some (Result.reverted runtimeFailed err)
                        | none =>
                            some (Result.reverted runtime'' RevertData.typeMismatch)
                    | Except.error err => some (Result.reverted runtime' err)
                | Except.error err => some (Result.reverted runtime' err)
            | Except.error err => some (Result.reverted runtime err)
        | Stmt.tryContractCreate contractName constructorArgsExpr valueExpr
            saltExpr? returns successBody catchClauses =>
            match constructorArgsExpr.evalWithRuntime context runtime with
            | Except.ok (argsValue, runtime') =>
                match argsValue.asBytes? with
                | some constructorArgs =>
                    match valueExpr.evalWithRuntime context runtime' with
                    | Except.ok (valueValue, runtime'') =>
                        match valueValue.expectWord with
                        | Except.ok value =>
                            let saltResult? :
                                Except RevertData (Option Word × Runtime) :=
                              match saltExpr? with
                              | some saltExpr => do
                                  let (saltValue, runtime''') ←
                                    saltExpr.evalWithRuntime context runtime''
                                  let salt ← saltValue.expectWord
                                  Except.ok (some salt, runtime''')
                              | none => Except.ok (none, runtime'')
                            match saltResult? with
                            | Except.ok (salt?, runtime''') =>
                                let createResult? :=
                                  context.lookupContractCreation?
                                  contractName constructorArgs value salt?
                              let success :=
                                match createResult? with
                                | some result => result.success
                                | none => false
                              let output :=
                                match createResult? with
                                | some result => result.output.map normByte
                                | none => []
                              if success then
                                let address :=
                                  match createResult? with
                                  | some result => result.address
                                  | none => 0
                                let values :=
                                  if returns.isEmpty then
                                    []
                                  else
                                    [Value.word address]
                                  match BindingDecl.bindArgs? returns values with
                                  | some frame =>
                                      match Stmt.eval fuel context
                                          (runtime'''.withFrame frame)
                                          successBody with
                                      | some result =>
                                        some
                                          (result.mapRuntime
                                            Runtime.popScope)
                                      | none => none
                                  | none =>
                                      some
                                        (Result.reverted runtime'''
                                          RevertData.typeMismatch)
                                else
                                  match TryCatchClause.findMatch?
                                      output catchClauses with
                                  | some (frame, body) =>
                                      match Stmt.eval fuel context
                                          (runtime'''.withFrame frame) body with
                                      | some result =>
                                        some
                                          (result.mapRuntime
                                            Runtime.popScope)
                                      | none => none
                                  | none =>
                                      some
                                        (Result.reverted runtime'''
                                          (RevertData.fromRawBytes output))
                            | Except.error err =>
                                some (Result.reverted runtime'' err)
                        | Except.error err => some (Result.reverted runtime'' err)
                    | Except.error err => some (Result.reverted runtime' err)
                | none =>
                    some (Result.reverted runtime' RevertData.typeMismatch)
            | Except.error err => some (Result.reverted runtime err)
      | Stmt.break => some (Result.broke runtime)
      | Stmt.continue => some (Result.continued runtime)
      | Stmt.returnValues exprs =>
          match Expr.evalListWithRuntime context runtime exprs with
          | Except.ok (values, runtime') =>
              some (Result.returned runtime' values)
          | Except.error err => some (Result.reverted runtime err)
      | Stmt.revertError reason =>
          match reason with
          | some message =>
              some (Result.reverted runtime (RevertData.error message))
          | none =>
              some (Result.reverted runtime RevertData.empty)
      | Stmt.revertErrorExpr reasonExpr =>
          match reasonExpr.evalWithRuntime context runtime with
          | Except.ok (reasonValue, runtime') =>
              match errorStringBytesRevert? reasonValue with
              | some payload =>
                  some (Result.reverted runtime' payload)
              | none =>
                  some (Result.reverted runtime' RevertData.typeMismatch)
          | Except.error err => some (Result.reverted runtime err)
      | Stmt.revert name exprs =>
          match Expr.evalListWithRuntime context runtime exprs with
          | Except.ok (values, runtime') =>
              some (Result.reverted runtime' (RevertData.custom name values))
          | Except.error err => some (Result.reverted runtime err)
      | Stmt.emitEvent name exprs =>
          match Expr.evalListWithRuntime context runtime exprs with
          | Except.ok (values, runtime') =>
              match runtime'.emitEvent context name values with
              | Except.ok updated => some (Result.normal updated)
              | Except.error err => some (Result.reverted runtime err)
          | Except.error err => some (Result.reverted runtime err)
      | Stmt.selfdestruct recipientExpr =>
          match recipientExpr.evalWithRuntime context runtime with
          | Except.ok (recipientValue, runtime') =>
              match recipientValue.expectWord with
              | Except.ok recipient =>
                  some
                    (Result.selfdestructed
                      { runtime' with
                        state :=
                          runtime'.state.recordSelfdestruct
                            context.self recipient })
              | Except.error err => some (Result.reverted runtime' err)
          | Except.error err => some (Result.reverted runtime err)
      | Stmt.unchecked body =>
          Stmt.eval fuel { context with checked := false } runtime body

def Stmt.evalList (fuel : Nat) (context : Context)
    (runtime : Runtime) : List Stmt -> Option Result
  | [] => some (Result.normal runtime)
  | stmt :: rest =>
      match Stmt.eval fuel context runtime stmt with
      | some (Result.normal runtime') =>
          Stmt.evalList fuel context runtime' rest
      | some result => some result
      | none => none

def Stmt.evalWhile (fuel : Nat) (context : Context)
    (runtime : Runtime) (cond : Expr) (body : Stmt) :
    Option Result :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
      match cond.evalWithRuntime context runtime with
      | Except.ok (value, runtime') =>
          match value.expectWord with
          | Except.ok word =>
              if wordTruthy word then
                match Stmt.eval fuel context runtime' body with
                | some (Result.normal runtime') =>
                    Stmt.evalWhile fuel context runtime' cond body
                | some (Result.continued runtime') =>
                    Stmt.evalWhile fuel context runtime' cond body
                | some (Result.broke runtime') =>
                    some (Result.normal runtime')
                | some result => some result
                | none => none
              else
                some (Result.normal runtime')
          | Except.error err => some (Result.reverted runtime' err)
      | Except.error err => some (Result.reverted runtime err)

def Stmt.evalDoWhile (fuel : Nat) (context : Context)
    (runtime : Runtime) (body : Stmt) (cond : Expr) :
    Option Result :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
      match Stmt.eval fuel context runtime body with
      | some (Result.normal runtime') =>
          match cond.evalWithRuntime context runtime' with
          | Except.ok (value, runtime'') =>
              match value.expectWord with
              | Except.ok word =>
                  if wordTruthy word then
                    Stmt.evalDoWhile fuel context runtime'' body cond
                  else
                    some (Result.normal runtime'')
              | Except.error err => some (Result.reverted runtime'' err)
          | Except.error err => some (Result.reverted runtime' err)
      | some (Result.continued runtime') =>
          match cond.evalWithRuntime context runtime' with
          | Except.ok (value, runtime'') =>
              match value.expectWord with
              | Except.ok word =>
                  if wordTruthy word then
                    Stmt.evalDoWhile fuel context runtime'' body cond
                  else
                    some (Result.normal runtime'')
              | Except.error err => some (Result.reverted runtime'' err)
          | Except.error err => some (Result.reverted runtime' err)
      | some (Result.broke runtime') =>
          some (Result.normal runtime')
      | some result => some result
      | none => none

def Stmt.evalFor (fuel : Nat) (context : Context)
    (runtime : Runtime) (cond : Expr) (post : Stmt) (body : Stmt) :
    Option Result :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
      match cond.evalWithRuntime context runtime with
      | Except.ok (value, runtime') =>
          match value.expectWord with
          | Except.ok word =>
              if wordTruthy word then
                match Stmt.eval fuel context runtime' body with
                | some (Result.normal runtime') =>
                    match Stmt.eval fuel context runtime' post with
                    | some (Result.normal posted) =>
                        Stmt.evalFor fuel context posted cond post body
                    | some result => some result
                    | none => none
                | some (Result.continued runtime') =>
                    match Stmt.eval fuel context runtime' post with
                    | some (Result.normal posted) =>
                        Stmt.evalFor fuel context posted cond post body
                    | some result => some result
                    | none => none
                | some (Result.broke runtime') =>
                    some (Result.normal runtime')
                | some result => some result
                | none => none
              else
                some (Result.normal runtime')
          | Except.error err => some (Result.reverted runtime' err)
      | Except.error err => some (Result.reverted runtime err)

end

structure FunctionDef where
  name : String
  selector? : Option Word
  payable : Bool := false
  params : List BindingDecl
  returns : List BindingDecl
  body : Stmt
  deriving Repr

inductive CallResult where
  | returned : State -> List Value -> CallResult
  | reverted : State -> RevertData -> CallResult
  deriving Repr

def CallResult.clearTransient : CallResult -> CallResult
  | CallResult.returned state values =>
      CallResult.returned state.clearTransient values
  | CallResult.reverted state revert =>
      CallResult.reverted state.clearTransient revert

def FunctionDef.acceptsValue (function : FunctionDef) (value : Word) : Bool :=
  function.payable || wordEq value 0

def FunctionDef.initialFrame? (function : FunctionDef)
    (args : List Value) : Option Frame :=
  match BindingDecl.bindArgs? function.params args with
  | some params =>
      some (params ++ function.returns.map BindingDecl.defaultBinding)
  | none => none

def FunctionDef.collectReturns (function : FunctionDef)
    (runtime : Runtime) : Except RevertData (List Value) :=
  let rec collect : List BindingDecl -> Except RevertData (List Value)
    | [] => Except.ok []
    | decl :: rest => do
        let value ←
          match runtime.lookupLocal? decl.name with
          | some value => Except.ok value
          | none => Except.error RevertData.typeMismatch
        let value ←
          match decl.ty.coerceValue? value with
          | some coerced => Except.ok coerced
          | none => Except.error RevertData.typeMismatch
        let values ← collect rest
        Except.ok (value :: values)
  collect function.returns

def FunctionDef.coerceReturnValues? (function : FunctionDef)
    (values : List Value) : Option (List Value) :=
  let rec coerce : List BindingDecl -> List Value -> Option (List Value)
    | [], [] => some []
    | decl :: decls, value :: rest => do
        let head ← decl.ty.coerceValue? value
        let tail ← coerce decls rest
        some (head :: tail)
    | _, _ => none
  coerce function.returns values

def FunctionDef.call? (fuel : Nat) (context : Context)
    (function : FunctionDef) (state : State) (args : List Value) :
    Option CallResult :=
  if function.acceptsValue context.value then
    match function.initialFrame? args with
    | some frame =>
        let runtime : Runtime := { state, locals := [frame] }
        match Stmt.eval fuel context runtime function.body with
        | some (Result.normal runtime') =>
            match function.collectReturns runtime' with
            | Except.ok values => some (CallResult.returned runtime'.state values)
            | Except.error err =>
                some (CallResult.reverted state err)
        | some (Result.returned runtime' values) =>
            if values.isEmpty then
              match function.collectReturns runtime' with
              | Except.ok namedValues =>
                  some (CallResult.returned runtime'.state namedValues)
              | Except.error err =>
                  some (CallResult.reverted state err)
            else
              match function.coerceReturnValues? values with
              | some coerced =>
                  some (CallResult.returned runtime'.state coerced)
              | none =>
                  some (CallResult.reverted state RevertData.typeMismatch)
        | some (Result.selfdestructed runtime') =>
            some (CallResult.returned runtime'.state [])
        | some (Result.reverted runtime' revert) =>
            let _ := runtime'
            some (CallResult.reverted state revert)
        | some (Result.broke runtime') =>
            let _ := runtime'
            some (CallResult.reverted state RevertData.typeMismatch)
        | some (Result.continued runtime') =>
            let _ := runtime'
            some (CallResult.reverted state RevertData.typeMismatch)
        | none => none
    | none => none
  else
    some (CallResult.reverted state RevertData.empty)

theorem FunctionDef.call?_reverted_rolls_back
    {fuel : Nat} {context : Context} {function : FunctionDef}
    {state : State} {args : List Value} {frame : Frame}
    {runtime : Runtime} {revert : RevertData}
    (hAccepts : function.acceptsValue context.value = true)
    (hFrame : function.initialFrame? args = some frame)
    (hEval :
      Stmt.eval fuel context { state := state, locals := [frame] }
          function.body =
        some (Result.reverted runtime revert)) :
    function.call? fuel context state args =
      some (CallResult.reverted state revert) := by
  simp [FunctionDef.call?, hAccepts, hFrame, hEval]

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
    lowLevelCallResults := []
    contractCreationResults := []
    blockEnv := BlockEnv.empty
    txEnv := TxEnv.empty
    gasleft := 0 }

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

def Contract.call? (fuel : Nat) (contract : Contract)
    (target : CallTarget) (state : State) (args : List Value) :
    Option CallResult :=
  let function? :=
    match target with
    | CallTarget.name name =>
        contract.findCallableFunctionByName? name args
    | CallTarget.selector selector =>
        contract.findFunctionBySelector? selector
  match function? with
  | some function =>
      function.call? fuel contract.context state args
  | none => none

def Contract.callTransaction? (fuel : Nat) (contract : Contract)
    (target : CallTarget) (state : State) (args : List Value) :
    Option CallResult := do
  let result ← Contract.call? fuel contract target state.clearTransient args
  some result.clearTransient

def uint256 (name : String) : BindingDecl :=
  { name, ty := Ty.uint256 }

def int256 (name : String) : BindingDecl :=
  { name, ty := Ty.int256 }

def bool (name : String) : BindingDecl :=
  { name, ty := Ty.bool }

def address (name : String) : BindingDecl :=
  { name, ty := Ty.address }

def bytesCalldata (name : String) : BindingDecl :=
  { name, ty := Ty.bytesCalldata }

def fixedWordArray (size : Nat) : Ty :=
  Ty.fixedArray size Ty.uint256

def Expr.zero : Expr :=
  Expr.word 0

def Expr.one : Expr :=
  Expr.word 1

def Expr.bytesLiteral (bytes : List Byte) : Expr :=
  Expr.byteArray bytes

def Expr.add (lhs rhs : Expr) : Expr :=
  Expr.binary BinaryOp.add lhs rhs

def Expr.sub (lhs rhs : Expr) : Expr :=
  Expr.binary BinaryOp.sub lhs rhs

def Expr.mul (lhs rhs : Expr) : Expr :=
  Expr.binary BinaryOp.mul lhs rhs

def Expr.div (lhs rhs : Expr) : Expr :=
  Expr.binary BinaryOp.div lhs rhs

def Expr.lt (lhs rhs : Expr) : Expr :=
  Expr.binary BinaryOp.lt lhs rhs

def Expr.eq (lhs rhs : Expr) : Expr :=
  Expr.binary BinaryOp.eq lhs rhs

def Expr.bitAnd (lhs rhs : Expr) : Expr :=
  Expr.binary BinaryOp.bitAnd lhs rhs

def Stmt.seq (stmts : List Stmt) : Stmt :=
  Stmt.block stmts

def compositionalControlExample : Stmt :=
  Stmt.block
    [ Stmt.varDecl Ty.uint256 "x" (some (Expr.word 0))
    , Stmt.whileLoop
        (Expr.lt (Expr.var "x") (Expr.word 4))
        (Stmt.block
          [ Stmt.ifElse
              (Expr.eq
                (Expr.bitAnd (Expr.var "x") (Expr.word 1))
                Expr.zero)
              (Stmt.assignOp (LValue.var "x") BinaryOp.add (Expr.word 2))
              (Stmt.assignOp (LValue.var "x") BinaryOp.add Expr.one)
          ])
    , Stmt.returnValues [Expr.var "x"]
    ]

def compositionalControlResult : Option Result :=
  Stmt.eval 20 Context.empty (Runtime.ofState State.empty)
    compositionalControlExample

def ternarySkipsRejectedBranch : Stmt :=
  Stmt.returnValues
    [ Expr.ternary (Expr.word 1)
        (Expr.word 7)
        (Expr.div (Expr.word 1) (Expr.word 0)) ]

def ternarySkipsRejectedBranchResult : Option Result :=
  Stmt.eval 8 Context.empty (Runtime.ofState State.empty)
    ternarySkipsRejectedBranch

def doWhileRunsBeforeCondition : Stmt :=
  Stmt.block
    [ Stmt.varDecl Ty.uint256 "x" (some (Expr.word 0))
    , Stmt.doWhile
        (Stmt.assignOp (LValue.var "x") BinaryOp.add Expr.one)
        (Expr.lt (Expr.var "x") (Expr.word 1))
    , Stmt.returnValues [Expr.var "x"] ]

def doWhileRunsBeforeConditionResult : Option Result :=
  Stmt.eval 16 Context.empty (Runtime.ofState State.empty)
    doWhileRunsBeforeCondition

def expressionStatementFailure : Stmt :=
  Stmt.exprStmt (Expr.div (Expr.word 1) (Expr.word 0))

def expressionStatementFailureResult : Option Result :=
  Stmt.eval 4 Context.empty (Runtime.ofState State.empty)
    expressionStatementFailure

def deleteLocalExample : Stmt :=
  Stmt.block
    [ Stmt.varDecl Ty.uint256 "x" (some (Expr.word 5))
    , Stmt.deleteValue (LValue.var "x")
    , Stmt.returnValues [Expr.var "x"] ]

def deleteLocalResult : Option Result :=
  Stmt.eval 8 Context.empty (Runtime.ofState State.empty)
    deleteLocalExample

def defaultBoolExample : Stmt :=
  Stmt.block
    [ Stmt.varDecl Ty.bool "ok" none
    , Stmt.returnValues [Expr.var "ok"] ]

def defaultBoolResult : Option Result :=
  Stmt.eval 8 Context.empty (Runtime.ofState State.empty)
    defaultBoolExample

def signedArithmeticExample : Stmt :=
  Stmt.block
    [ Stmt.varDecl Ty.int256 "x"
        (some (Expr.intWord (SharedSemantics.signedToWord (-5))))
    , Stmt.varDecl Ty.int256 "y" (some (Expr.intWord 2))
    , Stmt.returnValues
        [ Expr.div (Expr.var "x") (Expr.var "y")
        , Expr.binary BinaryOp.mod (Expr.var "x") (Expr.var "y")
        , Expr.lt (Expr.var "x") (Expr.var "y") ] ]

def signedArithmeticResult : Option Result :=
  Stmt.eval 12 Context.empty (Runtime.ofState State.empty)
    signedArithmeticExample

def signedNegOverflowExample : Stmt :=
  Stmt.block
    [ Stmt.varDecl Ty.int256 "x"
        (some (Expr.intWord SharedSemantics.halfWordModulus))
    , Stmt.returnValues [Expr.unary UnaryOp.neg (Expr.var "x")] ]

def signedNegOverflowResult : Option Result :=
  Stmt.eval 8 Context.empty (Runtime.ofState State.empty)
    signedNegOverflowExample

def uncheckedSignedNegWrapExample : Stmt :=
  Stmt.block
    [ Stmt.varDecl Ty.int256 "x"
        (some (Expr.intWord SharedSemantics.halfWordModulus))
    , Stmt.unchecked
        (Stmt.returnValues [Expr.unary UnaryOp.neg (Expr.var "x")]) ]

def uncheckedSignedNegWrapResult : Option Result :=
  Stmt.eval 8 Context.empty (Runtime.ofState State.empty)
    uncheckedSignedNegWrapExample

def assertFailureExample : Stmt :=
  Stmt.assertStmt (Expr.word 0)

def assertFailureResult : Option Result :=
  Stmt.eval 4 Context.empty (Runtime.ofState State.empty)
    assertFailureExample

def requireFailureExample : Stmt :=
  Stmt.requireStmt (Expr.word 0) (some "Nope")

def requireFailureResult : Option Result :=
  Stmt.eval 4 Context.empty (Runtime.ofState State.empty)
    requireFailureExample

def revertStringExample : Stmt :=
  Stmt.revertError (some "Nope")

def revertStringResult : Option Result :=
  Stmt.eval 4 Context.empty (Runtime.ofState State.empty)
    revertStringExample

def captureReturnExample : Stmt :=
  Stmt.block
    [ Stmt.varDecl Ty.uint256 "ret" none
    , Stmt.varDecl Ty.uint256 "x" (some (Expr.word 0))
    , Stmt.captureReturn ["ret"]
        (Stmt.block
          [ Stmt.returnValues [Expr.word 7]
          , Stmt.assign (LValue.var "x") (Expr.word 99) ])
    , Stmt.assign (LValue.var "x") (Expr.word 1)
    , Stmt.returnValues [Expr.var "ret", Expr.var "x"] ]

def captureReturnResult : Option Result :=
  Stmt.eval 16 Context.empty (Runtime.ofState State.empty)
    captureReturnExample

def bytesReturnExample : Stmt :=
  Stmt.returnValues [Expr.byteArray [0x41, 0x42]]

def bytesReturnResult : Option Result :=
  Stmt.eval 4 Context.empty (Runtime.ofState State.empty)
    bytesReturnExample

def rollbackContext : Context :=
  { Context.empty with
    storageFields := [{ name := "x", slot := 0 }] }

def writesThenReverts : FunctionDef :=
  { name := "fail"
    selector? := none
    params := []
    returns := []
    body :=
      Stmt.block
        [ Stmt.assign (LValue.storage "x") (Expr.word 7)
        , Stmt.revert "Nope" [] ] }

def writesThenRevertsCall : Option CallResult :=
  writesThenReverts.call? 8 rollbackContext State.empty []

end Source
end Solidity
end SolidCore

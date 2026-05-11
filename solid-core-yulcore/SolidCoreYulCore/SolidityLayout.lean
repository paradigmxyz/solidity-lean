import SolidCoreYulCore.FullYul

set_option maxHeartbeats 1000000

namespace SolidCoreYulCore
namespace SolidityLayout

def wordBytes : Nat := 32

def selectorBytes : Nat := 4

def ceilBytesToWords (bytes : Nat) : Nat :=
  (bytes + wordBytes - 1) / wordBytes

inductive AbiType where
  | uint (bits : Nat)
  | int (bits : Nat)
  | bool
  | address
  | fixedBytes (bytes : Nat)
  | bytes
  | string
  | fixedArray (element : AbiType) (length : Nat)
  | dynamicArray (element : AbiType)
  | tuple (fields : List AbiType)

namespace AbiType

def uint256 : AbiType :=
  AbiType.uint 256

def uint8 : AbiType :=
  AbiType.uint 8

end AbiType

mutual
  def AbiType.isDynamic : AbiType -> Bool
    | AbiType.bytes => true
    | AbiType.string => true
    | AbiType.dynamicArray _ => true
    | AbiType.fixedArray element _ => AbiType.isDynamic element
    | AbiType.tuple fields => AbiTypes.anyDynamic fields
    | _ => false

  def AbiTypes.anyDynamic : List AbiType -> Bool
    | [] => false
    | ty :: rest => ty.isDynamic || AbiTypes.anyDynamic rest
end

mutual
  def AbiType.headWords : AbiType -> Nat
    | AbiType.fixedArray element length =>
        if element.isDynamic then 1 else length * element.headWords
    | AbiType.tuple fields =>
        if AbiTypes.anyDynamic fields then 1 else AbiTypes.headWords fields
    | AbiType.bytes => 1
    | AbiType.string => 1
    | AbiType.dynamicArray _ => 1
    | _ => 1

  def AbiTypes.headWords : List AbiType -> Nat
    | [] => 0
    | ty :: rest => ty.headWords + AbiTypes.headWords rest
end

def AbiType.headBytes (ty : AbiType) : Nat :=
  ty.headWords * wordBytes

def AbiTypes.headBytes (types : List AbiType) : Nat :=
  AbiTypes.headWords types * wordBytes

def AbiTypes.get? : List AbiType -> Nat -> Option AbiType
  | [], _ => none
  | ty :: _, 0 => some ty
  | _ :: rest, index + 1 => AbiTypes.get? rest index

inductive AbiSizeExpr where
  | zero
  | constWords (words : Nat)
  | argTailWords (index : Nat)
  | add (lhs rhs : AbiSizeExpr)
deriving DecidableEq, Repr

namespace AbiSizeExpr

def plus : AbiSizeExpr -> AbiSizeExpr -> AbiSizeExpr
  | zero, rhs => rhs
  | lhs, zero => lhs
  | lhs, rhs => add lhs rhs

end AbiSizeExpr

def sumNat : List Nat -> Nat
  | [] => 0
  | value :: rest => value + sumNat rest

def AlignedWordBytes (bytes : Nat) : Prop :=
  ∃ words, bytes = words * wordBytes

theorem AlignedWordBytes.add {lhs rhs : Nat}
    (hLhs : AlignedWordBytes lhs) (hRhs : AlignedWordBytes rhs) :
    AlignedWordBytes (lhs + rhs) := by
  rcases hLhs with ⟨lhsWords, rfl⟩
  rcases hRhs with ⟨rhsWords, rfl⟩
  exact ⟨lhsWords + rhsWords, by rw [Nat.add_mul]⟩

theorem alignedWordBytes_sumNat :
    ∀ values : List Nat,
      (∀ value, value ∈ values -> AlignedWordBytes value) ->
        AlignedWordBytes (sumNat values)
  | [], _ => by
      exact ⟨0, by simp [sumNat]⟩
  | value :: rest, hAligned => by
      exact
        AlignedWordBytes.add
          (hAligned value (by simp))
          (alignedWordBytes_sumNat rest
            (by
              intro tailValue hTail
              exact hAligned tailValue (by simp [hTail])))

def AbiTypes.dynamicTailWordsBeforeFrom :
    Nat -> List AbiType -> Nat -> AbiSizeExpr
  | _, [], _ => AbiSizeExpr.zero
  | _, _, 0 => AbiSizeExpr.zero
  | index, ty :: rest, limit + 1 =>
      let here :=
        if ty.isDynamic then
          AbiSizeExpr.argTailWords index
        else
          AbiSizeExpr.zero
      AbiSizeExpr.plus here
        (AbiTypes.dynamicTailWordsBeforeFrom (index + 1) rest limit)

def AbiTypes.dynamicTailWordsBefore
    (types : List AbiType) (index : Nat) : AbiSizeExpr :=
  AbiTypes.dynamicTailWordsBeforeFrom 0 types index

def AbiTypes.dynamicOffsetWords
    (types : List AbiType) (index : Nat) : AbiSizeExpr :=
  AbiSizeExpr.plus (AbiSizeExpr.constWords (AbiTypes.headWords types))
    (AbiTypes.dynamicTailWordsBefore types index)

inductive AbiHeadEntry where
  | inline (words : Nat)
  | offset (words : AbiSizeExpr)
deriving DecidableEq, Repr

def AbiTypes.headEntry? (types : List AbiType) (index : Nat) :
    Option AbiHeadEntry :=
  match AbiTypes.get? types index with
  | none => none
  | some ty =>
      if ty.isDynamic then
        some (AbiHeadEntry.offset (AbiTypes.dynamicOffsetWords types index))
      else
        some (AbiHeadEntry.inline ty.headWords)

namespace AbiStrict

def tailOffsetAfterPrefix
    (fullHeadBytes : Nat) (previousTailBytes : List Nat) : Nat :=
  fullHeadBytes + sumNat previousTailBytes

theorem tailOffset_aligned
    {fullHeadBytes : Nat} {previousTailBytes : List Nat}
    (hHead : AlignedWordBytes fullHeadBytes)
    (hTails :
      ∀ bytes, bytes ∈ previousTailBytes -> AlignedWordBytes bytes) :
    AlignedWordBytes
      (tailOffsetAfterPrefix fullHeadBytes previousTailBytes) := by
  exact AlignedWordBytes.add hHead
    (alignedWordBytes_sumNat previousTailBytes hTails)

theorem tailOffset_ge_head
    (fullHeadBytes : Nat) (previousTailBytes : List Nat) :
    fullHeadBytes ≤
      tailOffsetAfterPrefix fullHeadBytes previousTailBytes := by
  exact Nat.le.intro rfl

end AbiStrict

def AbiTypes.argumentHeadByteOffset
    (prefixBytes : Nat) (types : List AbiType) (index : Nat) : Nat :=
  prefixBytes + wordBytes * AbiTypes.headWords (types.take index)

def AbiTypes.calldataArgumentHeadByteOffset
    (types : List AbiType) (index : Nat) : Nat :=
  AbiTypes.argumentHeadByteOffset selectorBytes types index

def AbiTypes.returnArgumentHeadByteOffset
    (types : List AbiType) (index : Nat) : Nat :=
  AbiTypes.argumentHeadByteOffset 0 types index

def AbiTypes.errorArgumentHeadByteOffset
    (types : List AbiType) (index : Nat) : Nat :=
  AbiTypes.argumentHeadByteOffset selectorBytes types index

inductive AbiSelector where
  | function (signature : String)
  | error (signature : String)
  | eventTopic0 (signature : String)
deriving DecidableEq, Repr

inductive AbiIndexedEventPayload where
  | rawWord (ty : AbiType)
  | keccakEncoded (ty : AbiType)

def AbiType.indexedEventPayload (ty : AbiType) : AbiIndexedEventPayload :=
  match ty with
  | AbiType.uint _ => AbiIndexedEventPayload.rawWord ty
  | AbiType.int _ => AbiIndexedEventPayload.rawWord ty
  | AbiType.bool => AbiIndexedEventPayload.rawWord ty
  | AbiType.address => AbiIndexedEventPayload.rawWord ty
  | AbiType.fixedBytes _ => AbiIndexedEventPayload.rawWord ty
  | AbiType.bytes => AbiIndexedEventPayload.keccakEncoded ty
  | AbiType.string => AbiIndexedEventPayload.keccakEncoded ty
  | AbiType.fixedArray _ _ => AbiIndexedEventPayload.keccakEncoded ty
  | AbiType.dynamicArray _ => AbiIndexedEventPayload.keccakEncoded ty
  | AbiType.tuple _ => AbiIndexedEventPayload.keccakEncoded ty

theorem AbiType.string_dynamic :
    AbiType.string.isDynamic = true := by
  rfl

theorem AbiType.indexed_hash_of_dynamic
    {ty : AbiType} (h : ty.isDynamic = true) :
    ty.indexedEventPayload = AbiIndexedEventPayload.keccakEncoded ty := by
  cases ty <;> simp [AbiType.indexedEventPayload, AbiType.isDynamic] at h ⊢

theorem AbiType.fixedArray_indexed_hash
    (element : AbiType) (length : Nat) :
    (AbiType.fixedArray element length).indexedEventPayload =
      AbiIndexedEventPayload.keccakEncoded
        (AbiType.fixedArray element length) := by
  rfl

theorem AbiType.tuple_indexed_hash (fields : List AbiType) :
    (AbiType.tuple fields).indexedEventPayload =
      AbiIndexedEventPayload.keccakEncoded (AbiType.tuple fields) := by
  rfl

theorem AbiTypes.exampleFunctionHeadWords :
    AbiTypes.headWords
      [AbiType.uint256, AbiType.string,
        AbiType.dynamicArray AbiType.uint8] = 3 := by
  rfl

theorem AbiTypes.exampleStringHeadOffset :
    AbiTypes.dynamicOffsetWords
      [AbiType.uint256, AbiType.string,
        AbiType.dynamicArray AbiType.uint8] 1 =
      AbiSizeExpr.constWords 3 := by
  rfl

theorem AbiTypes.exampleArrayHeadOffset :
    AbiTypes.dynamicOffsetWords
      [AbiType.uint256, AbiType.string,
        AbiType.dynamicArray AbiType.uint8] 2 =
      AbiSizeExpr.add (AbiSizeExpr.constWords 3)
        (AbiSizeExpr.argTailWords 1) := by
  rfl

theorem AbiTypes.firstCalldataHeadOffset (types : List AbiType) :
    AbiTypes.calldataArgumentHeadByteOffset types 0 = selectorBytes := by
  simp [AbiTypes.calldataArgumentHeadByteOffset,
    AbiTypes.argumentHeadByteOffset, selectorBytes, AbiTypes.headWords,
    wordBytes]

theorem AbiTypes.firstReturnHeadOffset (types : List AbiType) :
    AbiTypes.returnArgumentHeadByteOffset types 0 = 0 := by
  simp [AbiTypes.returnArgumentHeadByteOffset,
    AbiTypes.argumentHeadByteOffset, AbiTypes.headWords, wordBytes]

inductive StorageKey where
  | word (value : Word)
  | signedWord (value : Int)
  | bool (value : Bool)
  | address (value : Word)
  | bytes (label : String)
  | string (label : String)
  | symbolic (label : String)
deriving DecidableEq, Repr

inductive SlotExpr where
  | literal (slot : Nat)
  | symbol (name : String)
  | addWords (base : SlotExpr) (words : Nat)
  | keccakSlot (slot : SlotExpr)
  | keccakMapping (key : StorageKey) (slot : SlotExpr)
deriving DecidableEq, Repr

namespace SlotExpr

def plusWords : SlotExpr -> Nat -> SlotExpr
  | slot, 0 => slot
  | slot, words => SlotExpr.addWords slot words

end SlotExpr

structure StorageLoc where
  slot : SlotExpr
  byteOffset : Nat
  byteSize : Nat
deriving DecidableEq, Repr

namespace StorageLoc

def atWholeSlot (slot : SlotExpr) : StorageLoc :=
  { slot := slot, byteOffset := 0, byteSize := wordBytes }

end StorageLoc

structure StorageCursor where
  slot : SlotExpr
  byteOffset : Nat
deriving DecidableEq, Repr

namespace StorageCursor

def ofSlot (slot : SlotExpr) : StorageCursor :=
  { slot := slot, byteOffset := 0 }

def freshSlot (cursor : StorageCursor) : StorageCursor :=
  if cursor.byteOffset = 0 then
    cursor
  else
    { slot := cursor.slot.plusWords 1, byteOffset := 0 }

def bumpSlots (cursor : StorageCursor) (slots : Nat) : StorageCursor :=
  { slot := cursor.slot.plusWords slots, byteOffset := 0 }

def allocPackable (bytes : Nat) (cursor : StorageCursor) :
    StorageLoc × StorageCursor :=
  let cursor :=
    if cursor.byteOffset + bytes <= wordBytes then
      cursor
    else
      cursor.freshSlot
  let loc :=
    { slot := cursor.slot, byteOffset := cursor.byteOffset,
      byteSize := bytes }
  let nextOffset := cursor.byteOffset + bytes
  let next :=
    if nextOffset = wordBytes then
      { slot := cursor.slot.plusWords 1, byteOffset := 0 }
    else
      { slot := cursor.slot, byteOffset := nextOffset }
  (loc, next)

def allocWholeSlots (slots : Nat) (cursor : StorageCursor) :
    StorageLoc × StorageCursor :=
  let cursor := cursor.freshSlot
  let loc :=
    { slot := cursor.slot, byteOffset := 0,
      byteSize := slots * wordBytes }
  (loc, cursor.bumpSlots slots)

end StorageCursor

inductive StorageItem where
  | packable (bytes : Nat)
  | wholeSlots (slots : Nat)
deriving DecidableEq, Repr

namespace StorageItem

def alloc (item : StorageItem) (cursor : StorageCursor) :
    StorageLoc × StorageCursor :=
  match item with
  | StorageItem.packable bytes => cursor.allocPackable bytes
  | StorageItem.wholeSlots slots => cursor.allocWholeSlots slots

end StorageItem

def StorageItems.layoutFrom :
    StorageCursor -> List (String × StorageItem) ->
      List (String × StorageLoc) × StorageCursor
  | cursor, [] => ([], cursor)
  | cursor, (name, item) :: rest =>
      let allocated := item.alloc cursor
      let tail := StorageItems.layoutFrom allocated.2 rest
      ((name, allocated.1) :: tail.1, tail.2)

inductive StorageType where
  | value (bytes : Nat)
  | bytes
  | string
  | staticArray (element : StorageType) (length : Nat) (reservedSlots : Nat)
  | dynamicArray (element : StorageType)
  | mapping (key : AbiType) (value : StorageType)
  | struct (members : List String) (reservedSlots : Nat)

namespace StorageType

def uint (bits : Nat) : StorageType :=
  StorageType.value ((bits + 7) / 8)

def uint256 : StorageType :=
  StorageType.value 32

def uint24 : StorageType :=
  StorageType.value 3

def bool : StorageType :=
  StorageType.value 1

def address : StorageType :=
  StorageType.value 20

def toItem : StorageType -> StorageItem
  | StorageType.value byteCount =>
      if byteCount <= wordBytes then
        StorageItem.packable byteCount
      else
        StorageItem.wholeSlots (ceilBytesToWords byteCount)
  | StorageType.bytes => StorageItem.wholeSlots 1
  | StorageType.string => StorageItem.wholeSlots 1
  | StorageType.staticArray _ _ reservedSlots =>
      StorageItem.wholeSlots reservedSlots
  | StorageType.dynamicArray _ => StorageItem.wholeSlots 1
  | StorageType.mapping _ _ => StorageItem.wholeSlots 1
  | StorageType.struct _ reservedSlots => StorageItem.wholeSlots reservedSlots

end StorageType

def elementsPerPackedSlot (elementBytes : Nat) : Nat :=
  wordBytes / elementBytes

def staticValueArraySlots (elementBytes length : Nat) : Nat :=
  let perSlot := elementsPerPackedSlot elementBytes
  if perSlot = 0 then
    length
  else
    (length + perSlot - 1) / perSlot

def packedElementLoc
    (base : SlotExpr) (elementBytes index : Nat) : StorageLoc :=
  let perSlot := elementsPerPackedSlot elementBytes
  let slotOffset := if perSlot = 0 then index else index / perSlot
  let byteOffset := if perSlot = 0 then 0 else (index % perSlot) * elementBytes
  { slot := base.plusWords slotOffset, byteOffset := byteOffset,
    byteSize := elementBytes }

def dynamicArrayLengthLoc (slot : SlotExpr) : StorageLoc :=
  StorageLoc.atWholeSlot slot

def dynamicArrayDataBase (slot : SlotExpr) : SlotExpr :=
  SlotExpr.keccakSlot slot

def dynamicArrayElementSlot (slot : SlotExpr) (index : Nat) : SlotExpr :=
  (dynamicArrayDataBase slot).plusWords index

def dynamicArrayPackedElementLoc
    (slot : SlotExpr) (elementBytes index : Nat) : StorageLoc :=
  packedElementLoc (dynamicArrayDataBase slot) elementBytes index

def nestedDynamicArrayPackedElementLoc
    (slot : SlotExpr) (outerIndex innerIndex elementBytes : Nat) :
    StorageLoc :=
  dynamicArrayPackedElementLoc
    (dynamicArrayElementSlot slot outerIndex) elementBytes innerIndex

def mappingValueSlot (key : StorageKey) (slot : SlotExpr) : SlotExpr :=
  SlotExpr.keccakMapping key slot

def mappingValueLoc (key : StorageKey) (slot : SlotExpr) : StorageLoc :=
  StorageLoc.atWholeSlot (mappingValueSlot key slot)

def structMemberSlot (base : SlotExpr) (slotOffset : Nat) : SlotExpr :=
  base.plusWords slotOffset

def shortBytesLengthTag (length : Nat) : Word :=
  length * 2

def longBytesLengthTag (length : Nat) : Word :=
  length * 2 + 1

def longBytesDataBase (slot : SlotExpr) : SlotExpr :=
  SlotExpr.keccakSlot slot

inductive StoragePathStep where
  | field (slotOffset byteOffset byteSize : Nat)
  | staticPackedIndex (elementBytes index : Nat)
  | dynamicPackedIndex (elementBytes index : Nat)
  | dynamicSlotIndex (index : Nat)
  | mappingKey (key : StorageKey)
deriving DecidableEq, Repr

def StoragePathStep.apply
    (step : StoragePathStep) (loc : StorageLoc) : StorageLoc :=
  match step with
  | StoragePathStep.field slotOffset byteOffset byteSize =>
      { slot := loc.slot.plusWords slotOffset, byteOffset := byteOffset,
        byteSize := byteSize }
  | StoragePathStep.staticPackedIndex elementBytes index =>
      packedElementLoc loc.slot elementBytes index
  | StoragePathStep.dynamicPackedIndex elementBytes index =>
      dynamicArrayPackedElementLoc loc.slot elementBytes index
  | StoragePathStep.dynamicSlotIndex index =>
      StorageLoc.atWholeSlot (dynamicArrayElementSlot loc.slot index)
  | StoragePathStep.mappingKey key =>
      mappingValueLoc key loc.slot

def StoragePath.resolve : StorageLoc -> List StoragePathStep -> StorageLoc
  | loc, [] => loc
  | loc, step :: rest => StoragePath.resolve (step.apply loc) rest

theorem packedTwoUint16_sameSlot (base : SlotExpr) :
    let first :=
      StorageItem.alloc (StorageItem.packable 2) (StorageCursor.ofSlot base)
    let second := StorageItem.alloc (StorageItem.packable 2) first.2
    first.1.slot = base ∧
      second.1.slot = base ∧
      first.1.byteOffset = 0 ∧
      second.1.byteOffset = 2 := by
  simp [StorageItem.alloc, StorageCursor.allocPackable, StorageCursor.ofSlot,
    wordBytes]

theorem wholeSlotAfterPackedField (base : SlotExpr) :
    let first :=
      StorageItem.alloc (StorageItem.packable 2) (StorageCursor.ofSlot base)
    let second := StorageItem.alloc (StorageItem.wholeSlots 1) first.2
    second.1.slot = base.plusWords 1 ∧
    second.1.byteOffset = 0 := by
  simp [StorageItem.alloc, StorageCursor.allocPackable,
    StorageCursor.allocWholeSlots, StorageCursor.freshSlot,
    StorageCursor.bumpSlots, StorageCursor.ofSlot, wordBytes,
    SlotExpr.plusWords]

theorem uint24_elementsPerSlot :
    elementsPerPackedSlot 3 = 10 := by
  rfl

theorem uint24NestedDynamicArrayElementLoc
    (slot : SlotExpr) (i j : Nat) :
    nestedDynamicArrayPackedElementLoc slot i j 3 =
      { slot :=
          (SlotExpr.keccakSlot
            ((SlotExpr.keccakSlot slot).plusWords i)).plusWords (j / 10),
        byteOffset := (j % 10) * 3,
        byteSize := 3 } := by
  rfl

theorem nestedMappingStructMemberSlot
    (slot : SlotExpr) :
    structMemberSlot
      (mappingValueSlot (StorageKey.word 9)
        (mappingValueSlot (StorageKey.word 4) slot)) 1 =
      (SlotExpr.keccakMapping (StorageKey.word 9)
        (SlotExpr.keccakMapping (StorageKey.word 4) slot)).plusWords 1 := by
  rfl

theorem shortBytesTag_lowBitClear (length : Nat) :
    shortBytesLengthTag length % 2 = 0 := by
  simp [shortBytesLengthTag]

theorem longBytesDataBase_eq (slot : SlotExpr) :
    longBytesDataBase slot = SlotExpr.keccakSlot slot := by
  rfl

theorem longBytesTag_lowBitSet (length : Nat) :
    longBytesLengthTag length % 2 = 1 := by
  simp [longBytesLengthTag]

theorem storagePath_nestedMappingStructMember
    (slot : SlotExpr) :
    StoragePath.resolve (StorageLoc.atWholeSlot slot)
      [ StoragePathStep.mappingKey (StorageKey.word 4)
      , StoragePathStep.mappingKey (StorageKey.word 9)
      , StoragePathStep.field 1 0 wordBytes ] =
      StorageLoc.atWholeSlot
        ((SlotExpr.keccakMapping (StorageKey.word 9)
          (SlotExpr.keccakMapping (StorageKey.word 4) slot)).plusWords 1) := by
  rfl

namespace BuiltinEvidence

theorem abiDispatch :
    FullYul.SolidityEmission.CanonicalBuiltinFeatureEvidence
      FullYul.SolidityEmission.AbiDispatchBuiltin :=
  FullYul.SolidityEmission.abiDispatchEvidence

theorem abiMemory :
    FullYul.SolidityEmission.CanonicalBuiltinFeatureEvidence
      FullYul.SolidityEmission.AbiMemoryBuiltin :=
  FullYul.SolidityEmission.abiMemoryEvidence

theorem storageLayout :
    FullYul.SolidityEmission.CanonicalBuiltinFeatureEvidence
      FullYul.SolidityEmission.StorageLayoutBuiltin :=
  FullYul.SolidityEmission.storageLayoutEvidence

theorem environmentQuery :
    FullYul.SolidityEmission.CanonicalBuiltinFeatureEvidence
      FullYul.SolidityEmission.EnvironmentQueryBuiltin :=
  FullYul.SolidityEmission.environmentQueryEvidence

end BuiltinEvidence

end SolidityLayout
end SolidCoreYulCore

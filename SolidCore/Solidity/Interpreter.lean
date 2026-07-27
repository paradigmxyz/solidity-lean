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
  /-- An internal function pointer (boundary-completion arc, stage C). The
      runtime value is a small sequential numeric ID (`Value.internalFunction`),
      matching solc via-IR's internal-dispatch model: ID 0 is the
      uninitialized/deleted pointer, IDs 1..n are assigned per contract to the
      dispatch-reachable internal functions, and the storage type is 8 bytes
      with a 64-bit-mask read cleanup (`docs/refs-completion-solc-research.md`
      §2). Validity is checked only at call time (`Stmt.internalCallPtr`):
      an ID with no table entry panics 0x51. -/
  | internalFunction : Ty
  | fixedArray : Nat -> Ty -> Ty
  | dynamicArray : Ty -> Ty
  | tuple : List Ty -> Ty
  /-- Enum in a *storage layout* position (max valid member index attached).
      solc reads enums from storage with `cleanup_from_storage = and(w,0xff)`
      (never reverting) and validates only at use sites via
      `validator_assert_t_enum` → `Panic(0x21)`. This constructor appears only
      as a storage-layout element type (lowered from the AST `Ty.enum`); ABI
      params/returns and locals stay `uint256` + `AbiCleanup.enum` exactly as
      before. -/
  | enumStorage : Word -> Ty
  deriving Repr, BEq

inductive AbiCleanup where
  | none
  | uint : Nat -> AbiCleanup
  | int : Nat -> AbiCleanup
  | enum : Word -> AbiCleanup
  /-- Use-site validator for an enum word loaded from storage. Same range
      check as `enum`, but a forced rejection is `Panic(0x21)`
      (solc `validator_assert_t_enum`), where the calldata-decode `enum`
      cleanup rejects with the empty revert (solc `validator_revert_t_enum`).
      Both are Forge-pinned (abi-malformed pins the empty calldata revert). -/
  | enumStorage : Word -> AbiCleanup
  | fixedArray : Nat -> AbiCleanup -> AbiCleanup
  | dynamicArray : AbiCleanup -> AbiCleanup
  | tuple : List AbiCleanup -> AbiCleanup
  /-- Wraps the cleanup of a `memory`-location aggregate ABI parameter. solc
      copies a memory reference-type parameter out of calldata at decode time,
      running each element's `<validator>` eagerly and reverting `revert(0,0)`
      immediately on a dirty narrow-int/enum/bool element — even one never read
      (verified: `f(uint8[] memory)` reverts on a dirty element when only
      `.length` is used, whereas `f(uint8[] calldata)` succeeds). Calldata
      aggregates keep the lazy per-access validation (`AbiCleanup.dynamicArray`
      etc.); only `memory` params carry this wrapper. `AbiCleanup.lazyParamValue`
      falls through to its eager `accepts`-based case for this constructor. -/
  | memoryEager : AbiCleanup -> AbiCleanup
  deriving Repr

/-- Storage layout of a state variable (or of the slot a storage POINTER is
    bound to). Moved above `Value` for WS2 (#146/#177): an early-bound storage
    reference (`Value.storageSlotRef`) carries the layout AT its captured slot
    so subsequent indexing/member access can resolve from the captured base. -/
inductive StorageLayout where
  | scalar : Ty -> StorageLayout
  | packedScalar : Nat -> Nat -> Bool -> Ty -> StorageLayout
  | struct : List StorageLayout -> StorageLayout
  | fixedArray : Nat -> StorageLayout -> StorageLayout
  | dynamicArray : StorageLayout -> StorageLayout
  | bytes : StorageLayout
  | string : StorageLayout
  | mapping : Ty -> StorageLayout -> StorageLayout
  deriving Repr, BEq

inductive Value where
  | word : Word -> Value
  /-- R3 (value typing): a `bytesN` value CARRYING its width. The `Word`
      payload keeps the internal right-aligned/numeric bytesN convention
      (meaningful bytes in the LOW `size` bytes; left-alignment happens only
      at the ABI boundary) — the tag adds the width so consumers (indexing,
      encoding) can dispatch structurally instead of relying on caller-side
      routing. `Value.word` remains legal for a bytesN value everywhere; all
      word accessors (`asWord?`/`expectWord`/…) unwrap this tag. -/
  | fixedBytes : Nat -> Word -> Value
  | int : Word -> Value
  | bytes : List Byte -> Value
  | externalFunction : Word -> Word -> Value
  /-- Internal function pointer: the per-contract dispatch ID (0 = invalid). -/
  | internalFunction : Word -> Value
  | fixedArray : List Value -> Value
  | dynamicArray : List Value -> Value
  | tuple : List Value -> Value
  | storageRef : String -> Value
  /-- WS2 (#146/#177) EARLY-BOUND storage pointer: the CONCRETE slot resolved
      ONCE at the binding site (`T storage p = arr[i]` — bounds check runs
      there, as solc does) plus the storage layout AT that slot. Dereference,
      write, delete, and further indexing all start from the captured slot
      with NO root re-resolution and NO dynamic-array length recheck for the
      already-bound prefix — matching solc/EVM, which raw-`sload`s a bound
      pointer even after the underlying array shrank. Whole-variable refs
      keep the `storageRef` name form (their base slot is static). -/
  | storageSlotRef : Word -> StorageLayout -> Value
  | memoryRef : Nat -> Value
  | abiLazy : AbiCleanup -> Value -> Value
  deriving Repr

def Ty.defaultValue : Ty -> Value
  | Ty.bool => Value.word 0
  | Ty.address => Value.word 0
  | Ty.uint256 => Value.word 0
  | Ty.int256 => Value.int 0
  | Ty.fixedBytes size => Value.fixedBytes size 0
  | Ty.bytesCalldata => Value.bytes []
  | Ty.externalFunction => Value.externalFunction 0 0
  | Ty.internalFunction => Value.internalFunction 0
  | Ty.fixedArray size elementTy =>
      Value.fixedArray (List.replicate size elementTy.defaultValue)
  | Ty.dynamicArray _ => Value.dynamicArray []
  | Ty.tuple elements =>
      Value.tuple (elements.map Ty.defaultValue)
  | Ty.enumStorage _ => Value.word 0

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

/-- Internal function pointers are an 8-byte storage type; the storage-read
    cleanup is `and(value, 0xffffffffffffffff)` — a 64-bit mask, nothing more
    (solc via-IR, `docs/refs-completion-solc-research.md` §2). No validity check
    at read time; invalid IDs surface only at call time as `Panic(0x51)`. This
    makes adoption-planted dirty words in fn-pointer slots behave exactly as
    solc: the read masks, a call either dispatches to a real function of that ID
    or panics. -/
def internalFunctionIdModulus : Nat := 2 ^ 64

def internalFunctionValueFromStorageWord (word : Word) : Value :=
  Value.internalFunction
    (SolidCore.Solidity.Shared.norm word % internalFunctionIdModulus)

def Value.asWord? : Value -> Option Word
  | Value.word value => some (SolidCore.Solidity.Shared.norm value)
  | Value.fixedBytes _ value => some (SolidCore.Solidity.Shared.norm value)
  | _ => none

def Value.asStorageWord? : Value -> Option Word
  | Value.word value => some (SolidCore.Solidity.Shared.norm value)
  | Value.fixedBytes _ value => some (SolidCore.Solidity.Shared.norm value)
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
  -- `bytesN.length` is the constant width N (solc folds it to `size`); the
  -- runtime member read must yield the same rather than dead-ending in a
  -- typeMismatch when the operand is non-constant (a local/param/storage/
  -- ternary value carries its width in the `fixedBytes` tag).
  | Value.fixedBytes size _ => some size
  | Value.int _ => none
  | Value.externalFunction _ _ => none
  | Value.internalFunction _ => none
  | Value.storageRef _ => none
  | Value.storageSlotRef _ _ => none
  | Value.memoryRef _ => none
  | Value.abiLazy _ value => value.length?

def Value.storageArrayLength? : Value -> Option Nat
  | Value.word length => some (SolidCore.Solidity.Shared.norm length)
  | value => value.length?

def Value.defaultLike : Value -> Value
  | Value.word _ => Value.word 0
  | Value.fixedBytes size _ => Value.fixedBytes size 0
  | Value.int _ => Value.int 0
  | Value.bytes _ => Value.bytes []
  | Value.externalFunction _ _ => Value.externalFunction 0 0
  | Value.internalFunction _ => Value.internalFunction 0
  | Value.fixedArray values => Value.fixedArray (values.map Value.defaultLike)
  | Value.dynamicArray _ => Value.dynamicArray []
  | Value.tuple values => Value.tuple (values.map Value.defaultLike)
  | Value.storageRef target => Value.storageRef target
  | Value.storageSlotRef slot layout => Value.storageSlotRef slot layout
  | Value.memoryRef id => Value.memoryRef id
  | Value.abiLazy _ value => value.defaultLike

/-- R3: strip bytesN width tags at PUBLIC observability boundaries (returned
    values, custom-error args, emitted event values). The tag
    (`Value.fixedBytes size w`) is an internal dispatch device; the externally
    observable value of a `bytesN` result is the same raw word it always was
    (the contest observable and the frozen lane fixtures render `Value.word`).
    Internal-call return capture does NOT route through these boundaries, so
    width/ref information keeps flowing across internal boundaries. -/
def Value.untagFixedBytes : Value -> Value
  | Value.fixedBytes _ w => Value.word w
  | Value.fixedArray vs => Value.fixedArray (vs.map Value.untagFixedBytes)
  | Value.dynamicArray vs =>
      Value.dynamicArray (vs.map Value.untagFixedBytes)
  | Value.tuple vs => Value.tuple (vs.map Value.untagFixedBytes)
  | Value.abiLazy cleanup v => Value.abiLazy cleanup v.untagFixedBytes
  | v => v

def Value.isMemoryObject : Value -> Bool
  | Value.bytes _ => true
  | Value.fixedArray _ => true
  | Value.dynamicArray _ => true
  | Value.tuple _ => true
  | Value.abiLazy _ value => value.isMemoryObject
  | _ => false

/-- WS2 (#146/#177): the base a storage POINTER (or a storage-rooted lvalue)
    is anchored at — either a whole state variable (name form; base slot is a
    compile-time constant) or an early-bound captured slot + its layout. All
    storage path helpers resolve extra indexes LIVE from this base; for a
    `.slot` base nothing before the base is ever re-resolved. -/
inductive StorageBase where
  | field : String -> StorageBase
  | slot : Word -> StorageLayout -> StorageBase
  deriving Repr

/-- The runtime `Value` a bound storage pointer with this base carries. -/
def StorageBase.toRefValue : StorageBase -> Value
  | StorageBase.field name => Value.storageRef name
  | StorageBase.slot s layout => Value.storageSlotRef s layout

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

/-- R3: custom-error ARGUMENTS are `Value`s too — strip bytesN width tags from
    revert data at the public boundary (`RevertData.custom` args of e.g.
    `AccessControlUnauthorizedAccount(account, bytes32 role)` are externally
    observable exactly like return values). -/
def RevertData.untagFixedBytes : RevertData -> RevertData
  | RevertData.custom name vs =>
      RevertData.custom name (vs.map Value.untagFixedBytes)
  | rd => rd

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
  | AbiCleanup.enumStorage maxValue, Value.word value =>
      SolidCore.Solidity.Shared.norm value <= SolidCore.Solidity.Shared.norm maxValue
  | AbiCleanup.fixedArray size cleanup, Value.fixedArray values =>
      values.length == size && AbiCleanup.acceptsAll cleanup values
  | AbiCleanup.dynamicArray cleanup, Value.dynamicArray values =>
      AbiCleanup.acceptsAll cleanup values
  | AbiCleanup.tuple cleanups, Value.tuple values =>
      AbiCleanups.accept cleanups values
  | AbiCleanup.memoryEager inner, value => inner.accepts value
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
    match cleanup with
    -- Storage-loaded enum use-site validator: solc `validator_assert_t_enum`
    -- panics 0x21. The calldata-decode cleanups below keep the empty revert
    -- (solc `validator_revert_*`), pinned by the abi-malformed Forge lanes.
    | AbiCleanup.enumStorage _ => Except.error RevertData.enumConversion
    | _ => Except.error RevertData.empty

def Value.forceAbiLazy : Value -> Except RevertData Value
  | Value.abiLazy cleanup value => cleanup.forceValue value
  | value => Except.ok value

/-- Deferred structural-decode failure for a nested *calldata* dynamic element
    (a `bytes`/`string`/nested dynamic array/dynamic struct member whose inner
    offset/length is malformed). solc validates such an inner element only when
    it is ACCESSED — decode returns a calldata pointer and never reads the inner
    offset, so a malformed one reverts empty (`validator_revert_*`) only on
    access, not at the boundary. We mirror that by placing this marker in the
    decoded aggregate spine: `.length`, sibling elements, and immediate
    structure stay usable, but forcing this element (access via
    `derefMemoryValue`) reverts empty exactly as solc's per-access validator.
    The wrapped cleanup (`uint 0`) rejects every dynamic-type value, so
    `forceValue` yields the empty revert; it is only ever produced for
    *calldata* params, so the memory-eager decode path (which reverts eagerly on
    any dirty element) never sees it. The placeholder is the element type's
    default value so that parameter binding's `coerceValue?` (which coerces each
    element to its declared type) accepts the marker WITHOUT forcing it — the
    aggregate stays usable for `.length`/sibling access — while an actual access
    (`derefMemoryValue`) forces the cleanup and reverts. -/
def Value.calldataDeferredInvalid (ty : Ty) : Value :=
  Value.abiLazy (AbiCleanup.uint 0) ty.defaultValue

def Value.expectWordRaw : Value -> Except RevertData Word
  | Value.word value => Except.ok (SolidCore.Solidity.Shared.norm value)
  | Value.fixedBytes _ value => Except.ok (SolidCore.Solidity.Shared.norm value)
  | _ => Except.error RevertData.typeMismatch

def Value.expectWord : Value -> Except RevertData Word
  | Value.word value => Except.ok (SolidCore.Solidity.Shared.norm value)
  | Value.fixedBytes _ value => Except.ok (SolidCore.Solidity.Shared.norm value)
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
  | Ty.fixedBytes size, Value.word value => some (Value.fixedBytes size value)
  | Ty.fixedBytes size, Value.fixedBytes _ value =>
      some (Value.fixedBytes size value)
  -- R3: coercion is TAG-AGNOSTIC — a width-tagged bytesN word meeting a
  -- word-shaped scalar slot coerces exactly like the bare word (several
  -- conversions, e.g. `address(bytes20 x)`, lower as IDENTITIES with no core
  -- node, so the tag legally reaches non-bytesN slots). Raw word unchanged.
  | Ty.bool, Value.fixedBytes _ value =>
      if wordEq value 0 || wordEq value 1 then
        some (Value.word value)
      else
        none
  | Ty.address, Value.fixedBytes _ value => some (Value.word value)
  | Ty.uint256, Value.fixedBytes _ value => some (Value.word value)
  | Ty.int256, Value.fixedBytes _ value => some (Value.int value)
  | Ty.enumStorage maxValue, Value.fixedBytes _ value =>
      if SolidCore.Solidity.Shared.norm value <=
          SolidCore.Solidity.Shared.norm maxValue then
        some (Value.word value)
      else
        none
  -- LIT-COERCION (#142 `.push(literal)` / #145 `bytesN`-keyed mapping key): a
  -- hex/string/bytes LITERAL flowing to a `bytesN` storage element or mapping key
  -- is lowered target-blind to a dynamic-`bytes` `Value.bytes`. solc coerces it to
  -- the fixed target — the ≤ n meaningful bytes packed as the internal
  -- (right-in-word) `bytesN` value, IDENTICAL to `Literal.toFixedBytesWord?` used
  -- on the clean assignment/return paths (`bytesToWordBE (bytes ‖ zero-pad to n)`).
  -- `coerceStorageWordAs` (push element) and `coerceMappingKeyWordAs` (mapping key)
  -- both route through here; the storage/mapping-slot machinery then aligns the
  -- word. Only a literal produces a `Value.bytes` for a `fixedBytes` target — solc
  -- rejects any implicit `bytes`→`bytesN` value conversion at compile time.
  | Ty.fixedBytes size, Value.bytes bytes =>
      if bytes.length ≤ size then
        some
          (Value.fixedBytes size
            (bytesToWordBE
              (bytes.map normByte ++
                List.replicate (size - bytes.length) 0)))
      else
        none
  | Ty.enumStorage maxValue, Value.word value =>
      -- Storage-write coercion of an enum value: solc's
      -- `update_storage_value_…_enum` routes through `cleanup_t_enum`
      -- (validator). Typed sources are already validated (`enumFromUInt`);
      -- lazily-wrapped dirty reads are forced (→ Panic 0x21) before this
      -- coercion by `coerceStorageWordAs`.
      if SolidCore.Solidity.Shared.norm value <=
          SolidCore.Solidity.Shared.norm maxValue then
        some (Value.word value)
      else
        none
  | Ty.bytesCalldata, Value.bytes bytes => some (Value.bytes bytes)
  | Ty.externalFunction, Value.externalFunction addr selector =>
      some (Value.externalFunction addr selector)
  | Ty.internalFunction, Value.internalFunction id =>
      some (Value.internalFunction id)
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
      -- solc `cleanup_from_storage_t_bool = and(w, 0xff)`, then every observable
      -- use applies `iszero(iszero(·))`. The read never reverts on a
      -- non-canonical word (only reachable via inline-assembly `sstore` or an
      -- adopted `postWorld`); truthiness depends solely on the low byte. We
      -- canonicalize to {0,1} on read, which is observationally identical to
      -- solc for every Solidity use site (a non-canonical bool is unobservable).
      some (Value.word
        (if SolidCore.Solidity.Shared.norm value % 256 == 0 then 0 else 1))
  | Ty.address, value =>
      -- solc `cleanup_from_storage_t_address = and(w, 2^160-1)`: the high 96
      -- bits are silently dropped on read, never reverting. Canonical corpus
      -- addresses already fit 160 bits, so this masks nothing there; it only
      -- normalizes non-canonical adopted/assembly-planted words.
      some (Value.word (SolidCore.Solidity.Shared.Account.addressWord value))
  | Ty.uint256, value => some (Value.word value)
  | Ty.int256, value => some (Value.int value)
  | Ty.fixedBytes n, value =>
      -- solc reads bytesN from storage as `shl(256-8N, w)` — the bits above
      -- the 8N-bit lane are dropped, never reverting. Our internal bytesN
      -- convention is right-aligned (meaningful bytes low; left-alignment
      -- happens only at the ABI boundary), so the equivalent total read is a
      -- mask to the low 8N bits. Canonical writes already fit, so this only
      -- normalizes non-canonical adopted/assembly-planted words.
      some
        (Value.fixedBytes n
          (SolidCore.Solidity.Shared.norm value % (2 ^ (8 * n))))
  | Ty.externalFunction, value =>
      some (externalFunctionValueFromStorageWord value)
  | Ty.enumStorage maxValue, value =>
      -- solc `cleanup_from_storage_t_enum = and(w, 0xff)`: read masks the lane
      -- byte and never reverts. Range validation happens only at USE sites
      -- (`validator_assert_t_enum` → Panic 0x21) — comparisons, conversions,
      -- storage writes, ABI-encoding of returns; a bare load-and-drop stays
      -- silent (verified against solc 0.8.35 --ir probes). In-range words stay
      -- bare (identical to the pre-enumStorage representation); out-of-range
      -- words carry the deferred use-site validator.
      let masked := SolidCore.Solidity.Shared.norm value % 256
      if masked <= SolidCore.Solidity.Shared.norm maxValue then
        some (Value.word masked)
      else
        some (Value.abiLazy (AbiCleanup.enumStorage maxValue)
          (Value.word masked))
  | Ty.internalFunction, value =>
      some (internalFunctionValueFromStorageWord value)
  | _, _ => none

mutual

def Value.coerceLike? : Value -> Value -> Option Value
  | template, Value.abiLazy cleanup value => do
      let coerced ← Value.coerceLike? template value
      some (Value.abiLazy cleanup coerced)
  | Value.abiLazy _ template, value =>
      Value.coerceLike? template value
  | Value.word _, Value.word value => some (Value.word value)
  -- R3: a width-tagged bytesN value meeting an untagged `word` slot keeps the
  -- pre-tag behaviour (stays a bare word); a `fixedBytes` slot keeps its width
  -- for either incoming shape. The payload word is never changed.
  | Value.word _, Value.fixedBytes _ value => some (Value.word value)
  | Value.fixedBytes size _, Value.fixedBytes _ value =>
      some (Value.fixedBytes size value)
  | Value.fixedBytes size _, Value.word value =>
      some (Value.fixedBytes size value)
  | Value.int _, Value.int value => some (Value.int value)
  | Value.int _, Value.word value => some (Value.int value)
  | Value.int _, Value.fixedBytes _ value => some (Value.int value)
  | Value.bytes _, Value.bytes bs => some (Value.bytes bs)
  -- R3 (#188): a storage-ref TEMPLATE meeting a storage-ref VALUE re-points
  -- structurally (an internal fn returning a storage pointer from an
  -- indexed/member path) instead of dead-ending in `none` → Panic 0.
  -- WS2: the incoming ref is already EARLY-BOUND (name form or captured
  -- slot); re-pointing adopts it unchanged.
  | Value.storageRef _, Value.storageRef target =>
      some (Value.storageRef target)
  | Value.storageRef _, Value.storageSlotRef slot layout =>
      some (Value.storageSlotRef slot layout)
  | Value.storageSlotRef _ _, Value.storageRef target =>
      some (Value.storageRef target)
  | Value.storageSlotRef _ _, Value.storageSlotRef slot layout =>
      some (Value.storageSlotRef slot layout)
  | Value.externalFunction _ _, Value.externalFunction addr selector =>
      some (Value.externalFunction addr selector)
  | Value.internalFunction _, Value.internalFunction id =>
      some (Value.internalFunction id)
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

def fixedBytesIndex? (size : Nat) (value index : Word) :
    Except RevertData Value :=
  if 0 < size && size <= wordBytes then
    match listGet? (wordToBytesBE size value) (SolidCore.Solidity.Shared.norm index) with
    | some byte => Except.ok (Value.fixedBytes 1 byte)
    | none => Except.error RevertData.indexOutOfBounds
  else
    Except.error RevertData.typeMismatch

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
  -- R3: bytesN indexing is INTRINSIC — the value carries its width, so a
  -- generic `index` on a width-tagged word extracts the byte (or panics 0x32
  -- out-of-bounds) without any caller-side routing to `fixedBytesIndex?`.
  | Value.fixedBytes size w =>
      fixedBytesIndex? size w index
  | Value.word _ =>
      Except.error RevertData.typeMismatch
  | Value.int _ =>
      Except.error RevertData.typeMismatch
  | Value.externalFunction _ _ =>
      Except.error RevertData.typeMismatch
  | Value.internalFunction _ =>
      Except.error RevertData.typeMismatch
  | Value.storageRef _ =>
      Except.error RevertData.typeMismatch
  | Value.storageSlotRef _ _ =>
      Except.error RevertData.typeMismatch
  | Value.memoryRef _ =>
      Except.error RevertData.typeMismatch
  | Value.abiLazy _ _ =>
      Except.error RevertData.typeMismatch

def fixedBytesCast? (targetSize sourceSize : Nat) (value : Word) :
    Except RevertData Value :=
  if 0 < targetSize && targetSize <= wordBytes &&
      0 < sourceSize && sourceSize <= wordBytes then
    Except.ok
      (Value.fixedBytes targetSize
        (bytesToWordBE
          (bytesPrefixRightPadded targetSize
            (wordToBytesBE sourceSize value))))
  else
    Except.error RevertData.typeMismatch

def fixedBytesFromBytes? (targetSize : Nat) (bytes : List Byte) :
    Except RevertData Value :=
  if 0 < targetSize && targetSize <= wordBytes then
    Except.ok
      (Value.fixedBytes targetSize
        (bytesToWordBE
          (bytesPrefixRightPadded targetSize bytes)))
  else
    Except.error RevertData.typeMismatch

def uintCast? (bits : Nat) (value : Value) : Except RevertData Value := do
  -- Conversion is a use site: force deferred cleanups (storage-loaded
  -- out-of-range enum → Panic 0x21, matching solc `convert_t_enum_to_t_uintN`
  -- routing through `cleanup_t_enum`).
  let value ← value.forceAbiLazy
  if 0 < bits && bits <= 256 then
    match value.asStorageWord? with
    | some word => Except.ok (Value.word (SolidCore.Solidity.Shared.norm word % (2 ^ bits)))
    | none => Except.error RevertData.typeMismatch
  else
    Except.error RevertData.typeMismatch

def uintCleanup? (checked : Bool) (bits : Nat) (value : Value) :
    Except RevertData Value := do
  let value ← value.forceAbiLazy
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

def intCast? (bits : Nat) (value : Value) : Except RevertData Value := do
  let value ← value.forceAbiLazy
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
    Except RevertData Value := do
  let value ← value.forceAbiLazy
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
    -- A calldata slice `a[i:j]` with `i > j` or `j > a.length` reverts with
    -- EMPTY data in solc's default (non-debug) mode: the slice bounds check
    -- (`YulUtilFunctions.cpp:2523-2539`) routes to `revertReasonIfDebugBody`
    -- (:4598-4605), which under `RevertStrings::Default` emits `revert(0, 0)`.
    -- This is distinct from an array/bytes INDEX access `a[i]` OOB, which panics
    -- 0x32 — that path (`Value.index?`/`setIndex?`) keeps `indexOutOfBounds`.
    Except.error RevertData.empty

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
  -- bytesN values are immutable words; `x[i] = b` is rejected upstream.
  | Value.fixedBytes _ _ =>
      Except.error RevertData.typeMismatch
  | Value.int _ =>
      Except.error RevertData.typeMismatch
  | Value.externalFunction _ _ =>
      Except.error RevertData.typeMismatch
  | Value.internalFunction _ =>
      Except.error RevertData.typeMismatch
  | Value.storageRef _ =>
      Except.error RevertData.typeMismatch
  | Value.storageSlotRef _ _ =>
      Except.error RevertData.typeMismatch
  | Value.memoryRef _ =>
      Except.error RevertData.typeMismatch
  | Value.abiLazy _ _ =>
      Except.error RevertData.typeMismatch

-- `WordMap` stays an assoc list: it backs only the small, cold `Context`
-- seed maps (`accountBalances`, `accountCodehashes`), which are iterated by
-- key at snapshot boundaries (`snapshotOtherAccounts`) and read via
-- `Account.lookupWord?`. The hot per-slot storage/transient maps use
-- `StorageMap` below.
abbrev WordMap := List (Word × Word)

-- PERF (2026-07-07, cause #1): storage/transient are keccak-hash-keyed and
-- read/written m·n times in mapping loops. Back them with `Std.HashMap`
-- (O(1) expected) instead of an O(n) assoc list that re-`norm`s a bignum on
-- every compare. CORRECTNESS: keys AND values are normalized (`% 2^256`) at
-- insert time, so two Nats equal mod 2^256 collide as one key (what the old
-- `wordEq`-on-compare guaranteed) and lookups never need to re-`norm`.
-- Iteration order is unobservable: the only consumers are `wordMapToStorage`
-- (folds into a key-addressed `EvmYul.Storage`; keys are unique so fold order
-- is irrelevant) and `storageToWordMap` (rebuilds from a key-addressed store).
abbrev StorageMap := Std.HashMap Word Word

def StorageMap.lookup? (m : StorageMap) (query : Word) : Option Word :=
  Std.HashMap.get? m (SolidCore.Solidity.Shared.norm query)

def StorageMap.insertLoop (m : StorageMap) (key value : Word) : StorageMap :=
  Std.HashMap.insert m (SolidCore.Solidity.Shared.norm key)
    (SolidCore.Solidity.Shared.norm value)

instance : Repr StorageMap where
  reprPrec m prec := reprPrec (Std.HashMap.toList m) prec

abbrev ByteMap := List (Word × List Byte)

def ByteMap.lookup? : ByteMap -> Word -> Option (List Byte)
  | [], _ => none
  | (key, value) :: rest, query =>
      if wordEq key query then
        some (value.map normByte)
      else
        ByteMap.lookup? rest query

-- PERF (2026-07-07, cause #1): memory refs are `Nat`-keyed and materialized
-- in bulk by EnumerableSet `.values()`; back them with `Std.HashMap`. Keys are
-- monotonic allocation ids (already canonical), never re-normalized. Memory is
-- only ever read/written by id (`Runtime.loadMemory?`/`allocMemory`/
-- `storeMemory?`) — never iterated — so order is unobservable.
abbrev MemoryMap := Std.HashMap Nat Value

def MemoryMap.lookup? (m : MemoryMap) (query : Nat) : Option Value :=
  Std.HashMap.get? m query

def MemoryMap.insertLoop (m : MemoryMap) (key : Nat) (value : Value) : MemoryMap :=
  Std.HashMap.insert m key value

instance : Repr MemoryMap where
  reprPrec m prec := reprPrec (Std.HashMap.toList m) prec


-- PERF (2026-07-07, cause #1): immutables are `String`-keyed and read by name
-- only (`State.immutable?`) — never iterated. Back with `Std.HashMap`.
abbrev ImmutableMap := Std.HashMap String Value

def ImmutableMap.lookup? (m : ImmutableMap) (query : String) : Option Value :=
  Std.HashMap.get? m query

def ImmutableMap.insertLoop (m : ImmutableMap) (name : String) (value : Value) :
    ImmutableMap :=
  Std.HashMap.insert m name value

instance : Repr ImmutableMap where
  reprPrec m prec := reprPrec (Std.HashMap.toList m) prec

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

/-- Opaque-ish `Repr` for the shared `OpenWorld` (RBMap-backed; no derived
    `Repr` upstream). Renders account count + substate log length — enough for
    witness diffs without dumping trees. -/
instance : Repr SolidCore.Solidity.Shared.OpenWorld :=
  ⟨fun w _ =>
    "OpenWorld(accounts := " ++ toString w.accounts.size ++
      ", logSeries := " ++ toString w.substate.logSeries.size ++
      ", created := " ++ toString w.createdAccounts.size ++ ")"⟩

structure State where
  storage : StorageMap
  transient : StorageMap := {}
  immutables : ImmutableMap := {}
  selfdestructs : List (Word × Word) := []
  selfdestructEffects : List SolidCore.Solidity.Shared.Account.SelfdestructRecord := []
  externalInteractions : List ExternalInteraction := []
  -- A2 (intra-frame balance accounting): the dynamic balance of `self` (this
  -- contract) during a call. Re-based at each external entry to the environment
  -- fact `balanceAt accountBalances self` plus the credited `msg.value`
  -- (`FunctionDef.evalBodyEntry`), and read by `address(this).balance` /
  -- `selfbalance`. openworld/postworld Stage 3: the outgoing-call debit is
  -- folded into the responder's echo answer and arrives through `adoptWorld`
  -- — balance flows only through adoption. Other addresses are adopted-world
  -- facts (`State.env*`), seeded from the Context maps.
  selfBalance : Word := 0
  -- openworld/postworld: the self-account nonce. Nothing in the interpreter
  -- reads it (create addresses come from `CreateResponse.address`); it is
  -- carried so the outgoing `OpenWorld` snapshot covers every `OpenAccount`
  -- field and the adoption round-trip law holds field-wise.
  selfNonce : Word := 0
  events : List Event
  -- openworld/postworld Stage 2 — the adopted environment view.
  -- After an external answer is adopted, `envWorld?` holds the answered
  -- `postWorld` VERBATIM: it owns the other-accounts facts, self code, the
  -- substate extras (access sets/refund), and `createdAccounts`; the existing
  -- State fields above own the live self account (storage/transient/balance/
  -- nonce). `worldMutatedSinceAdoption = false` means no State mutation has
  -- happened since adoption, so the next outgoing snapshot returns
  -- `envWorld?` verbatim — this is what makes the round-trip law
  -- `snapshotWorld context (adoptWorld w context s) = w` exact (mirror of
  -- `ofYulShared_installYulShared`).
  envWorld? : Option SolidCore.Solidity.Shared.OpenWorld := none
  worldMutatedSinceAdoption : Bool := true
  -- Canonical log series = `adoptedLogPrefix ++ (events.drop adoptedEventCount)`
  -- projection: `events` stays CUMULATIVE (existing witness assertions on
  -- `state.events` are untouched — plan risk R1's split-point variant); the
  -- prefix carries the adopted series (callee logs included, wholesale — logs
  -- are substate on the Yul side, not caller-local). Same split-point pattern
  -- for the selfdestruct set.
  adoptedLogPrefix : List SolidCore.Solidity.Shared.Log.Entry := []
  adoptedEventCount : Nat := 0
  adoptedSelfdestructCount : Nat := 0
  deriving Repr

def State.empty : State :=
  { storage := {}, transient := {}, immutables := {}, events := [] }

def State.logEntries (state : State) (self : Word) :
    List SolidCore.Solidity.Shared.Log.Entry :=
  state.events.map (Event.toLogEntry self)

def State.loadSlot (state : State) (slot : Word) : Word :=
  match StorageMap.lookup? state.storage slot with
  | some value => value
  | none => 0

def State.storeSlot (state : State) (slot value : Word) : State :=
  { state with
    storage := StorageMap.insertLoop state.storage slot value
    worldMutatedSinceAdoption := true }

def State.loadTransientSlot (state : State) (slot : Word) : Word :=
  match StorageMap.lookup? state.transient slot with
  | some value => value
  | none => 0

def State.storeTransientSlot (state : State) (slot value : Word) : State :=
  { state with
    transient := StorageMap.insertLoop state.transient slot value
    worldMutatedSinceAdoption := true }

def State.clearTransient (state : State) : State :=
  { state with transient := {}, worldMutatedSinceAdoption := true }

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
    selfdestructEffects := state.selfdestructEffects ++ [record]
    worldMutatedSinceAdoption := true }

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
  memory : MemoryMap := {}
  nextMemory : Nat := 0
  deriving Repr

def Runtime.ofState (state : State) : Runtime :=
  { state, locals := [[]] }

/-- A2: the amount a recorded external effect debits from `self`'s balance. Only
    a **successful** value-transferring effect debits — a low-level `call`/
    `callcode` (staticcall/delegatecall/precompiles transfer nothing) or a
    contract creation carrying value. A failed effect debits nothing (the EVM
    refunds value to the caller on callee failure / a reverted create). -/
def ExternalInteraction.selfBalanceDebit : ExternalInteraction → Word
  | ExternalInteraction.lowLevelCall result =>
      if result.success &&
          (result.kind == SolidCore.Solidity.Shared.Call.ExternalCallKind.call ||
            result.kind ==
              SolidCore.Solidity.Shared.Call.ExternalCallKind.callcode) then
        result.value
      else
        0
  | ExternalInteraction.contractCreation result =>
      if result.success then result.value else 0

def Runtime.recordExternalInteraction
    (runtime : Runtime) (interaction : ExternalInteraction) : Runtime :=
  -- openworld/postworld Stage 3: the A2 value-transfer debit no longer lives
  -- here — it is folded into the responder's echo answer
  -- (`ScriptedResponder.answerCall?`/`answerCreate?` debit the sent world's
  -- self account by `interaction.selfBalanceDebit`), and the debited balance
  -- arrives through `adoptWorld`. Balance flows ONLY through adoption; this
  -- helper only records the interaction transcript (not world-observable, so
  -- it does not touch `worldMutatedSinceAdoption`).
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

/- Runtime-aware recursive zeroing for a memory `delete`. solc's `delete` on a
    memory lvalue allocates a brand-new, fully-zeroed object graph at the free
    memory pointer, so nested references become FRESH empty/zeroed cells — never
    aliases of the old ones. `Value.defaultLike` cannot do this: it has no
    `Runtime`, so it preserves inner `memoryRef`s (leaving e.g. a struct's
    dynamic-array member pointing at the old, non-empty array). This walks the
    value graph: value fields become the zero word/empty bytes, a dynamic array
    becomes a fresh length-0 array, a fixed array keeps its length with each
    element recursively zeroed, a struct (tuple) zeroes each field, and every
    inner `memoryRef` is dereferenced, zeroed, and re-allocated as a NEW cell so
    the deleted variable's fresh graph is fully detached from the pre-delete
    cells (which any surviving alias keeps observing). -/
mutual

def Runtime.deleteZeroValue (runtime : Runtime) :
    Nat -> Value -> Except RevertData (Runtime × Value)
  | 0, _ => Except.error RevertData.typeMismatch
  | fuel + 1, value =>
      match value with
      | Value.word _ => Except.ok (runtime, Value.word 0)
      | Value.fixedBytes size _ =>
          Except.ok (runtime, Value.fixedBytes size 0)
      | Value.int _ => Except.ok (runtime, Value.int 0)
      | Value.bytes _ => Except.ok (runtime, Value.bytes [])
      | Value.externalFunction _ _ =>
          Except.ok (runtime, Value.externalFunction 0 0)
      | Value.internalFunction _ =>
          Except.ok (runtime, Value.internalFunction 0)
      | Value.fixedArray values => do
          let (runtime', zeroed) ← runtime.deleteZeroValues (fuel + 1) values
          Except.ok (runtime', Value.fixedArray zeroed)
      | Value.dynamicArray _ => Except.ok (runtime, Value.dynamicArray [])
      | Value.tuple values => do
          let (runtime', zeroed) ← runtime.deleteZeroValues (fuel + 1) values
          Except.ok (runtime', Value.tuple zeroed)
      | Value.memoryRef id =>
          match runtime.loadMemory? id with
          | some stored => do
              let (runtime', zeroed) ← runtime.deleteZeroValue fuel stored
              Except.ok (runtime'.allocMemory zeroed)
          | none => Except.error RevertData.typeMismatch
      | Value.abiLazy cleanup value => do
          let forced ← cleanup.forceValue value
          runtime.deleteZeroValue fuel forced
      | Value.storageRef _ => Except.ok (runtime, value)
      | Value.storageSlotRef _ _ => Except.ok (runtime, value)

def Runtime.deleteZeroValues (runtime : Runtime) (fuel : Nat) :
    List Value -> Except RevertData (Runtime × List Value)
  | [] => Except.ok (runtime, [])
  | value :: rest => do
      let (runtime', zeroed) ← runtime.deleteZeroValue fuel value
      let (runtime'', zeroedRest) ← runtime'.deleteZeroValues fuel rest
      Except.ok (runtime'', zeroed :: zeroedRest)

end

def Runtime.deleteZeroValueDeep (runtime : Runtime) (value : Value) :
    Except RevertData (Runtime × Value) :=
  runtime.deleteZeroValue (runtime.nextMemory + 1) value

def Runtime.lookupMemoryRef? (runtime : Runtime) (name : String) :
    Option Nat :=
  match runtime.lookupLocal? name with
  | some (Value.memoryRef id) => some id
  | _ => none

/-- WS2: the `StorageBase` a local storage POINTER is bound to (whole
    variable → `.field`, early-bound path → captured `.slot`). Replaces the
    late-binding `lookupStoragePathRef?` (root + index path). -/
def Runtime.lookupStorageBase? (runtime : Runtime) (name : String) :
    Option StorageBase :=
  match runtime.lookupLocal? name with
  | some (Value.storageRef target) => some (StorageBase.field target)
  | some (Value.storageSlotRef slot layout) =>
      some (StorageBase.slot slot layout)
  | _ => none

/-- Re-point a local that currently holds a storage POINTER to a new
    (already early-bound) storage-ref value. -/
def Runtime.assignStorageRefValue?
    (runtime : Runtime) (name : String) (ref : Value) : Option Runtime :=
  match runtime.lookupLocal? name with
  | some (Value.storageRef _) | some (Value.storageSlotRef _ _) =>
      match LocalEnv.assign? runtime.locals name ref with
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

/-- Reference-aware local assignment for internal-call return capture
    (function-boundary refactor, reference-signature extension). A returned
    storage pointer must re-point the caller's storage-alias target (through
    `assignStorageRefValue?`), not be `coerceLike?`'d as an ordinary value
    (which has no storage/memory-ref case). Memory-ref returns and
    plain values fall through to `assignLocal?` (which already aliases a memory
    target and coerces a value target). -/
def Runtime.assignLocalRefAware?
    (runtime : Runtime) (name : String) (value : Value) : Option Runtime :=
  match value with
  | Value.storageRef _ | Value.storageSlotRef _ _ =>
      runtime.assignStorageRefValue? name value
  | _ => runtime.assignLocal? name value

def Runtime.assignNamedValuesRef? (runtime : Runtime) :
    List String -> List Value -> Option Runtime
  | [], [] => some runtime
  | name :: names, value :: values =>
      match runtime.assignLocalRefAware? name value with
      | some updated => Runtime.assignNamedValuesRef? updated names values
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
      -- Item #1: solc NEVER splits a value element across a slot boundary. A
      -- narrow element occupies `floor(32 / widthBytes)` per slot (with padding
      -- waste at the slot tail), so the array spans `ceil(size / perSlot)` slots
      -- — NOT `ceil(size * widthBytes / 32)` (tight bit-packing, which would let
      -- an element straddle a slot boundary and undercount slots, e.g.
      -- `uint72[7]` is 3 slots, not 2).
      natCeilDiv size (max 1 (wordBytes / widthBytes))
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
      -- Item #1: elements-per-slot = floor(32 / widthBytes); no element straddles
      -- a slot boundary (see `StorageLayout.slotSpan`).
      let span := natCeilDiv size (max 1 (wordBytes / widthBytes))
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
        -- Item #1: elements-per-slot = floor(32 / widthBytes); an element that
        -- would not fit in the remaining bytes of a slot starts a fresh slot
        -- (solc never splits a value element across slots). The previous tight
        -- bit-packing (`byteOffset := index * widthBytes`, `slot = byteOffset/32`,
        -- `offset = byteOffset%32`) let an element straddle a slot boundary,
        -- landing at the wrong slot/offset (e.g. `uint72` element 3 at slot 0
        -- offset 27 instead of slot 1 offset 0).
        let perSlot := max 1 (wordBytes / widthBytes)
        some
          ( index / perSlot
          , StorageLayout.packedScalar
              ((index % perSlot) * widthBytes) widthBytes signed ty )
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

/-- #186 closed-world self-dispatch hook. An external call to `address(this)` is
    NOT open-world: the model has the contract's own code, so instead of emitting
    a `Query.external` to a responder it must route the call through the
    contract's own external dispatcher against the LIVE caller state. This hook
    carries exactly that capability, installed on the entry `Context` by the
    closed-world call entries (defined downstream in `ABI.lean`, where the
    dispatcher is in scope) and consulted at the external-call emit sites when the
    target equals `context.self`. Arguments: the sub-frame `msg.sender` (the
    contract's own address), `msg.value`, the ABI `calldata`, and the live caller
    `State`. Result: `(success, returndata, post-call state)`, or `none` when the
    self-dispatch cannot resolve (fail-closed). It is `none` by default, so the
    open-world responder path (all other-contract calls, and the existing
    responder-scripted self-call witnesses) is entirely unaffected.

    NOTE the hook takes NO runtime fuel: its dispatch budget and nesting-depth
    bound are baked in at installation time (a fixed `Nat`), so the emit-site
    value is independent of the caller's remaining statement fuel — this is what
    keeps `Stmt.eval` fuel-monotone across the self-dispatch site. -/
abbrev SelfDispatchFn :=
  Word → Word → List Byte → State → Option (Bool × List Byte × State)

/-- A self-dispatch hook is an opaque capability; its `Repr` is a placeholder so
    `Context`'s derived `Repr` keeps working (the field is never displayed). -/
instance : Repr SelfDispatchFn := ⟨fun _ _ => Std.Format.text "<selfDispatch>"⟩

structure Context where
  storageFields : List StorageField
  immutableFields : List ImmutableField := []
  -- #186: closed-world self-dispatch capability for calls to `address(this)`;
  -- `none` on every open-world path (default), set only by the closed-world
  -- entry points. See `SelfDispatchFn`.
  selfDispatch? : Option SelfDispatchFn := none
  eventDecls : List EventDecl
  checked : Bool
  construction : Bool := false
  calldata : List Byte
  sender : Word
  value : Word
  self : Word
  -- openworld/postworld: the four fields below are entry-time SEEDS. After
  -- the first `postWorld` adoption, `State.envWorld?` is authoritative for
  -- other-account balance/code/codehash and the created-accounts set; route
  -- reads through `State.envAccountBalance`/`envAccountCode`/
  -- `envAccountCodehash`/`envCreatedAccounts`, never these maps directly.
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
    memoryAllocationLimit? := none }

def Context.checkMemoryAllocation (context : Context) (length : Word) :
    Except RevertData Nat :=
  let size := SolidCore.Solidity.Shared.norm length
  -- solc `arrayAllocationSizeFunction` opens every `new bytes(n)` / `new T[](n)`
  -- allocation with `if gt(length, 0xffffffffffffffff) { panic 0x41 }`
  -- (YulUtilFunctions.cpp:2370), checked on the raw element count before it is
  -- scaled by the element stride. This is the production-path allocation bound;
  -- enforce it unconditionally so an oversized allocation raises Panic(0x41)
  -- rather than materializing an unbounded object.
  if size > 0xffffffffffffffff then
    Except.error RevertData.memoryAllocationTooLarge
  else
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
  | Ty.fixedBytes n => do
      -- AGG1: solc hashes a `bytesN` mapping key LEFT-aligned — the value slot
      -- is `keccak256(h(key) . slot)` where `h(key)` is the cleaned stack form
      -- stored at memory 0, and bytesN stack values are left-aligned
      -- (`FixedBytesType::leftAligned = true`, Types.h:701-702). Our internal
      -- bytesN convention is right-aligned (meaningful bytes in the LOW n bytes;
      -- :468-475), so shift the low 8n bits into the high bytes of the preimage
      -- word before hashing. (n = 32 → shift 0, identical to a bytes32 key.)
      let word ← coerceMappingKeyWordAs keyTy key
      let low := SolidCore.Solidity.Shared.norm word % (2 ^ (8 * n))
      let preimage := normWord (low * 2 ^ (8 * (wordBytes - n)))
      Except.ok (mappingStorageSlot slot preimage)
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

/-! ### openworld/postworld — outgoing `OpenWorld` snapshots

`snapshotWorld` materializes the real `OpenWorld` carried by every
`Query.external` (mirror of the Yul side's `ofYulShared`): the self account
verbatim from `State` (storage, transient, A2 `selfBalance`, `selfNonce`, code
from `Context`), other accounts from the environment-fact seed maps, the
substate (log series, selfdestruct set; access sets/refund are `default` — a
declared fidelity gap, same code-erasure spirit as the Yul side's gas
exclusion), and `createdAccounts`. Nothing restructures state: the snapshot is
a projection, and responder matchers never inspect it (corpus-neutral). -/

def wordMapToStorage (m : StorageMap) : EvmYul.Storage :=
  -- Keys in a `StorageMap` are unique (insert dedups), so fold order is
  -- irrelevant — every entry maps to a distinct `EvmYul.Storage` slot.
  Std.HashMap.fold
    (fun acc k v => acc.insert (wordToU256 k) (wordToU256 v)) default m

def storageToWordMap (s : EvmYul.Storage) : StorageMap :=
  s.toList.foldl
    (fun acc kv => StorageMap.insertLoop acc (u256ToWord kv.1) (u256ToWord kv.2))
    {}

def logEntryToEvm (e : SolidCore.Solidity.Shared.Log.Entry) :
    EvmYul.LogEntry :=
  { address := wordToAddress e.address
    topics := (e.topics.map wordToU256).toArray
    data := bytesToByteArray e.data }

def evmLogEntryToShared (e : EvmYul.LogEntry) :
    SolidCore.Solidity.Shared.Log.Entry :=
  { address := addressToWord e.address
    topics := e.topics.toList.map u256ToWord
    data := byteArrayToBytes e.data }

def addressSetOfWords (words : List Word) :
    Batteries.RBSet EvmCompiler.Simulation.OpenAddress compare :=
  words.foldl (fun acc w => acc.insert (wordToAddress w)) default

/-- Canonical log series: the adopted prefix (whatever the last answered
    `postWorld` carried — callee logs included) followed by the projection of
    the events emitted since that adoption. `events` itself stays cumulative
    (risk R1's split-point variant: no fixture-visible change). -/
def State.canonicalLogEntries (state : State) (self : Word) :
    List SolidCore.Solidity.Shared.Log.Entry :=
  state.adoptedLogPrefix ++
    (state.events.drop state.adoptedEventCount).map (Event.toLogEntry self)

/-- Selfdestruct records added since the last adoption (split-point pattern,
    like the log series). -/
def State.selfdestructsSinceAdoption (state : State) : List (Word × Word) :=
  state.selfdestructs.drop state.adoptedSelfdestructCount

/-- The self account as an `OpenAccount` (see table in
    `docs/openworld-postworld-plan.md` §2.1). The code seed comes from
    `Context.accountCodes`; after an adoption the answered world owns the self
    code (`snapshotWorld`'s overlay branch reads it from `envWorld?`). -/
def snapshotSelfAccount (context : Context) (state : State) :
    EvmCompiler.Simulation.OpenAccount :=
  { nonce := wordToU256 state.selfNonce
    balance := wordToU256 state.selfBalance
    storage := wordMapToStorage state.storage
    transientStorage := wordMapToStorage state.transient
    codeBytes :=
      match state.envWorld? with
      | some w =>
          match w.accounts.find? (wordToAddress context.self) with
          | some account => account.codeBytes
          | none => ByteArray.empty
      | none =>
          bytesToByteArray
            (SolidCore.Solidity.Shared.Account.codeAt
              context.accountCodes context.self) }

/-- Environment-fact accounts (every address seeded in the Context maps,
    excluding self): balance/code from the maps, storage/transient empty
    (we assert nothing about other accounts' storage), nonce 0. -/
def snapshotOtherAccounts (context : Context) : List (Word × EvmCompiler.Simulation.OpenAccount) :=
  let addrs :=
    (context.accountBalances.map Prod.fst ++
      context.accountCodes.map Prod.fst ++
      context.accountCodehashes.map Prod.fst).map
        SolidCore.Solidity.Shared.norm
  let dedup := addrs.foldl (fun acc a =>
    if acc.contains a then acc else acc ++ [a]) []
  (dedup.filter (fun a => !(wordEq a context.self))).map (fun a =>
    ( a
    , { nonce := wordToU256 0
        balance :=
          wordToU256
            (SolidCore.Solidity.Shared.Account.balanceAt
              context.accountBalances a)
        storage := default
        transientStorage := default
        codeBytes :=
          bytesToByteArray
            (SolidCore.Solidity.Shared.Account.codeAt
              context.accountCodes a) } ))

/-- The outgoing world snapshot before any adoption: self from `State`,
    other accounts + created set from the Context seed maps, substate from the
    canonical series (mirror of Yul's `ofYulShared` at seed fidelity). -/
def snapshotWorldSeed (context : Context) (state : State) :
    SolidCore.Solidity.Shared.OpenWorld :=
  let accounts : EvmYul.AddrMap EvmCompiler.Simulation.OpenAccount :=
    ((snapshotOtherAccounts context).foldl
      (fun (acc : EvmYul.AddrMap EvmCompiler.Simulation.OpenAccount) entry =>
        acc.insert (wordToAddress entry.1) entry.2)
      default).insert
        (wordToAddress context.self) (snapshotSelfAccount context state)
  let substate : EvmYul.Substate :=
    { (default : EvmYul.Substate) with
      selfDestructSet :=
        addressSetOfWords (state.selfdestructs.map Prod.fst)
      logSeries :=
        ((state.canonicalLogEntries context.self).map logEntryToEvm).toArray }
  { accounts := accounts
    substate := substate
    createdAccounts :=
      addressSetOfWords context.createdInTransactionAccounts }

/-- The outgoing world snapshot (mirror of Yul's `ofYulShared`).

    After an adoption, the answered world is authoritative for everything the
    interpreter does not own: if nothing mutated since adoption the adopted
    world is returned VERBATIM (exactly `ofYulShared ∘ installYulShared = id`,
    the round-trip law `snapshot_adoptWorld`); otherwise the adopted world is
    overlaid with the live self account, the canonical log series, and the
    selfdestruct records added since adoption. Before any adoption, the
    Context seed maps supply the environment facts (`snapshotWorldSeed`). -/
def snapshotWorld (context : Context) (state : State) :
    SolidCore.Solidity.Shared.OpenWorld :=
  match state.envWorld? with
  | some w =>
      if state.worldMutatedSinceAdoption then
        { accounts :=
            w.accounts.insert (wordToAddress context.self)
              (snapshotSelfAccount context state)
          substate :=
            { w.substate with
              selfDestructSet :=
                (state.selfdestructsSinceAdoption.map Prod.fst).foldl
                  (fun acc a => acc.insert (wordToAddress a))
                  w.substate.selfDestructSet
              logSeries :=
                ((state.canonicalLogEntries context.self).map
                  logEntryToEvm).toArray }
          createdAccounts := w.createdAccounts }
      else
        w
  | none => snapshotWorldSeed context state

/-- Wholesale adoption of an answered `postWorld` (mirror of Yul's
    `installYulShared`): the self-account fields land on the existing `State`
    fields (ordinary slot-keyed writes into the same `WordMap`s — wholesale
    replacement, not merge), the world itself is retained verbatim as the live
    environment view (`envWorld?` owns other accounts, self code, substate
    extras, `createdAccounts`), and the canonical log series becomes the
    answered `logSeries` (split-point pattern: `events` stays cumulative).
    Self absent from the answered accounts ⇒ the empty account — total, no
    error, same as `installYulAccounts`. -/
def adoptWorld (postWorld : SolidCore.Solidity.Shared.OpenWorld)
    (context : Context) (state : State) : State :=
  let selfAccount :=
    (postWorld.accounts.find? (wordToAddress context.self)).getD default
  { state with
    storage := storageToWordMap selfAccount.storage
    transient := storageToWordMap selfAccount.transientStorage
    selfBalance := u256ToWord selfAccount.balance
    selfNonce := u256ToWord selfAccount.nonce
    envWorld? := some postWorld
    worldMutatedSinceAdoption := false
    adoptedLogPrefix :=
      postWorld.substate.logSeries.toList.map evmLogEntryToShared
    adoptedEventCount := state.events.length
    adoptedSelfdestructCount := state.selfdestructs.length }

/-! ### Adopted environment facts (plan §2.3)

After the first adoption the Context maps (`accountBalances`, `accountCodes`,
`accountCodehashes`, `createdInTransactionAccounts`) are SEED-ONLY: reads of
other-account facts consult the adopted world first and fall back to the seeds
only pre-adoption (`envWorld? = none`), so pre-first-call behavior is
unchanged. The adopted world is authoritative including absence: an account
missing from the answered world reads as nonexistent (balance 0, no code). -/

def State.envAccount? (state : State) (addr : Word) :
    Option EvmCompiler.Simulation.OpenAccount :=
  state.envWorld?.bind (fun w => w.accounts.find? (wordToAddress addr))

def State.envAccountBalance (state : State) (context : Context)
    (addr : Word) : Word :=
  match state.envWorld? with
  | some _ =>
      match state.envAccount? addr with
      | some account => u256ToWord account.balance
      | none => 0
  | none =>
      SolidCore.Solidity.Shared.Account.balanceAt
        context.accountBalances addr

def State.envAccountCode (state : State) (context : Context)
    (addr : Word) : List Byte :=
  match state.envWorld? with
  | some _ =>
      match state.envAccount? addr with
      | some account => byteArrayToBytes account.codeBytes
      | none => []
  | none =>
      SolidCore.Solidity.Shared.Account.codeAt context.accountCodes addr

def State.envAccountHasCode (state : State) (context : Context)
    (addr : Word) : Bool :=
  !(state.envAccountCode context addr).isEmpty

def State.envCreatedAccounts (state : State) (context : Context) :
    List Word :=
  match state.envWorld? with
  | some w => w.createdAccounts.toList.map addressToWord
  | none => context.createdInTransactionAccounts

/-- `extcodehash` from the adopted world: nonexistent account → 0 (EIP-1052);
    existing account → keccak of its adopted code bytes. Pre-adoption the
    Context seed map is authoritative (it may carry oracle codehashes that are
    not keccak(seed code) — a recorded environment-fact liberty). -/
def State.envAccountCodehash (state : State) (context : Context)
    (addr : Word) : Word :=
  match state.envWorld? with
  | some _ =>
      match state.envAccount? addr with
      | some account => keccakWord (byteArrayToBytes account.codeBytes)
      | none => 0
  | none =>
      SolidCore.Solidity.Shared.Account.codehashAt
        context.accountCodehashes addr

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

/-- In-semantics precompile answering: a STATICCALL request with zero value
    whose code address is a mainnet precompile is answered deterministically
    from `Precompile.execute?` (pure — sha256/ripemd160/ecrecover/identity/
    modexp/bnAdd/bnMul/blake2f; `none` for the unimplemented bnPairing and
    pointEvaluation, which stay fail-closed open-world). Consulted by every
    answering fold ONLY after responder-row lookup misses (row-first
    precedence — scripted precompile rows keep answering byte-identically),
    and NEVER at the emit site: the `Query.external` node still appears in the
    transcript, keeping the query alphabet aligned with evm-compiler. The
    answered `postWorld` is the echoed sent world (a staticcall transfers no
    value, so the A2 debit is 0) and `returnedGas` echoes the request, exactly
    `ScriptedResponder.answerCall?`'s row shape. -/
def precompileAnswerCall? (world : SolidCore.Solidity.Shared.OpenWorld)
    (request : EvmCompiler.Simulation.CallRequest) :
    Option EvmCompiler.Simulation.CallResponse :=
  match request.kind with
  | EvmCompiler.Simulation.CallKind.staticcall =>
      if u256ToWord request.transferValue == 0 then
        match SolidCore.Solidity.Shared.Precompile.kindOfAddress?
            (addressToWord request.codeAddress) with
        | some kind =>
            match SolidCore.Solidity.Shared.Precompile.execute? kind
                (byteArrayToBytes request.calldata) with
            | some (success, output) =>
                some
                  { success := success
                    returnData := bytesToByteArray output
                    postWorld := world
                    returnedGas := request.requestedGas }
            | none => none
        | none => none
      else
        none
  | _ => none

/-- Emit an external low-level call as a `Query.external` node and resume on the
    `CallResponse`. The query carries the real `snapshotWorld` of the caller's
    state at emit (mirror of Yul's `callEval` → `ofYulShared`); responder
    matchers never inspect it (corpus-neutral). On resume the answered
    `postWorld` is adopted WHOLESALE into the state (mirror of Yul's
    `withWorldAndMachine` → `installYulShared`); under the echo convention
    (`postWorld := sent world`, `Query.defaultAnswer`'s shape) adoption is the
    identity on every carried field. -/
def emitLowLevelCall (context : Context) (state : State)
    (kind : LowLevelCallKind)
    (target : Word) (calldata : List Byte) (value : Word) (gas? : Option Word) :
    SolI (LowLevelCallResult × State) :=
  let request := buildCallRequest context kind target calldata value gas?
  .request
    (EvmCompiler.Simulation.Query.external (snapshotWorld context state)
      (EvmCompiler.Simulation.ExternalRequest.call request))
    (fun response =>
      .done (.ok
        ( decodeCallResponse response kind target calldata value gas?
        , adoptWorld response.postWorld context state )))

/-- #186: obtain the `(LowLevelCallResult × State)` pair for an external call
    whose target is `address(this)`. When a closed-world self-dispatch hook is
    installed (`context.selfDispatch?`), route the call through the contract's own
    dispatcher against the LIVE state — a real re-entrant sub-frame with
    `msg.sender := context.self` — mirroring `emitLowLevelCall`'s result shape but
    emitting NO `Query.external`. When no hook is installed (every open-world
    entry, incl. responder-scripted self-call witnesses), fall back to the
    ordinary open-world emit so behaviour there is byte-identical. A hook that
    fails to resolve (`none`) yields a failed call (`success := false`, empty
    returndata), fail-closed.

    Only CALL and STATICCALL self-dispatch (STATICCALL reaches the statement-level
    site solely from the high-level `this.f()` lowering, which picks it
    exclusively for typechecked view/pure targets, so the dispatched frame cannot
    write; the expression-level low-level site additionally restricts itself to
    plain CALL). A DELEGATECALL/CALLCODE whose target word happens to equal
    `context.self` must NOT self-dispatch: it preserves the OUTER
    `msg.sender`/`msg.value`, and under the closed-world entries an
    external-library delegatecall's unresolved address defaults to word 0 ==
    self — hijacking it would silently run the wrong code with the wrong frame.
    Those kinds keep the open-world emit (fail-closed). -/
def selfDispatchKindOk (kind : LowLevelCallKind) : Bool :=
  match kind with
  | SolidCore.Solidity.Shared.Call.ExternalCallKind.call => true
  | SolidCore.Solidity.Shared.Call.ExternalCallKind.staticcall => true
  | _ => false

def selfDispatchCall (context : Context) (state : State)
    (kind : LowLevelCallKind) (target : Word) (calldata : List Byte)
    (value : Word) (gas? : Option Word) : SolI (LowLevelCallResult × State) :=
  match (if selfDispatchKindOk kind && wordEq target context.self then
      context.selfDispatch?
    else none) with
  | some dispatch =>
      match dispatch context.self value calldata state with
      | some (success, output, state') =>
          pure
            ( { kind := kind, target := target, calldata := calldata,
                value := value, gas? := gas?, success := success, output := output }
            , state' )
      | none =>
          pure
            ( { kind := kind, target := target, calldata := calldata,
                value := value, gas? := gas?, success := false, output := [] }
            , state )
  | none => emitLowLevelCall context state kind target calldata value gas?

/-- Emit a precompile builtin (ecrecover/sha256/ripemd160) as a `STATICCALL` to
    address 1/2/3 and decode its 32-byte output word. In the EVM these builtins
    ARE ordinary external calls (a staticcall to the precompile address), so they
    emit `Query.external` like any call; the deterministic result is computed in
    the responder (`answerCall` → `lookupLowLevelCall?`, which reads the same
    oracle rows `Precompile.lookup?` keyed). Mirrors `Precompile.outputWord?`: a
    failed call or short output yields `none`. `keccak256` is the KECCAK256
    opcode, computed in-EVM, so it stays local — no query. -/
def emitPrecompileWord (context : Context) (state : State)
    (kind : SolidCore.Solidity.Shared.Precompile.Kind) (input : List Byte) :
    SolI (Option Word × State) := do
  let (result, state') ← emitLowLevelCall context state
    LowLevelCallKind.staticcall
    (SolidCore.Solidity.Shared.Precompile.address kind) input 0 none
  pure (SolidCore.Solidity.Shared.Precompile.outputWord? result, state')

/-- Emit `gasleft()` as a `Query.resource .gas` observation on the shared
    alphabet's reserved resource arm, resuming on the answered word (A3). Every
    answerer supplies the ambient `context.gasleft` (`contextAnswer`/`SolI.run`,
    `SolI.runFromContext`/`foldExpr`), so the returned value is exactly the
    former ambient constant — the query simply now appears in the transcript.
    Resource queries are answered ambiently, NOT matched against a responder's
    call/create rows (see `SolI.runWith`). -/
def emitGasleft : SolI Word :=
  .request
    (EvmCompiler.Simulation.Query.resource
      EvmCompiler.Simulation.ResourceQuery.gas)
    (fun g => .done (.ok (u256ToWord g)))

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
    `CreateResponse`. The query carries the real `snapshotWorld` (mirror of
    Yul's `createEval` → `ofYulShared`); matchers ignore it. -/
def emitContractCreation (context : Context) (state : State)
    (name : String) (args : List Byte)
    (value : Word) (salt? : Option Word) :
    SolI (ContractCreationResult × State) :=
  let request := buildCreateRequest context name args value salt?
  .request
    (EvmCompiler.Simulation.Query.external (snapshotWorld context state)
      (EvmCompiler.Simulation.ExternalRequest.create request))
    (fun response =>
      .done (.ok
        ( decodeCreateResponse response name args value salt?
        , adoptWorld response.postWorld context state )))

/-- The stage-3 context answerer: external queries get `Query.defaultAnswer` (the
    context no longer carries oracle rows; see `SolI.runFromContext`), and the
    reserved `resource .gas` arm (A3) is answered ambiently with the context's
    `gasleft` word — exactly the constant `EnvWord.gasleft` returned before the
    query existed. Other resource arms (`msize`) keep the canonical default. -/
def contextAnswer (context : Context) :
    (q : EvmCompiler.Simulation.Query) → EvmCompiler.Simulation.Answer q
  | EvmCompiler.Simulation.Query.resource
      EvmCompiler.Simulation.ResourceQuery.gas =>
      wordToU256 context.gasleft
  | EvmCompiler.Simulation.Query.external world
      (EvmCompiler.Simulation.ExternalRequest.call request) =>
      -- Precompile staticcalls are answered in-semantics (deterministic,
      -- `precompileAnswerCall?`); every other external call keeps the
      -- fail-open default answer.
      match precompileAnswerCall? world request with
      | some response => response
      | none =>
          EvmCompiler.Simulation.Query.defaultAnswer
            (EvmCompiler.Simulation.Query.external world
              (EvmCompiler.Simulation.ExternalRequest.call request))
  | q => EvmCompiler.Simulation.Query.defaultAnswer q

/-- Fuel-bounded fold answering every query from `Context` via `contextAnswer`
    (stage 3: the fixture oracle left `Context`; external answers come from
    scripted responders — `SolI.runWith`/`runFailOpen`). `contextAnswer`'s
    external call/create shapes decode to exactly the old fail-open
    `failedRequest` (success = false / address = 0, empty output), so this is
    bit-identical to the retired replay-from-Context fold on the row-less
    contexts that remain; the reserved `resource .gas` arm (A3) returns the
    ambient `context.gasleft`. Kept fuel-bounded for the transcript utilities and
    `foldExpr` (constant-expression evaluation). -/
def SolI.runFromContext {α : Type} (fuel : Nat) (context : Context) :
    SolI α → Except SolidityFailure α
  | .done r => r
  | .request query k =>
      match fuel with
      | 0 => .error .outOfFuel
      | Nat.succ fuel' =>
          SolI.runFromContext fuel' context
            (k (contextAnswer context query))

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
snapshot in the query never participates in row MATCHING; it participates in
the ANSWER: rows without a world delta answer `postWorld := sent world` — the
echo convention, exactly `Query.defaultAnswer`'s shape — so echo adoption is
the identity on every carried field (openworld/postworld Stage 2). -/

/-- Per-account world delta for responder rows: overrides of environment-fact
    fields of OTHER accounts (we never model their storage — risk R6). -/
structure OpenAccountDelta where
  balance? : Option Word := none
  code? : Option (List Byte) := none
  deriving Repr

/-- Optional `postWorld` delta on a responder row (openworld/postworld
    Stage 3). Deltas are MODEL-LEVEL: ordinary slot-keyed writes into the same
    maps the interpreter uses (ruling #1 — no new representation). A row
    without a delta answers the echo world with the A2 value-transfer debit
    folded in (§3.1); `selfBalance?` is absolute and REPLACES the debit
    entirely (no double-count). Deltas are derived from what Forge's real
    reentering callee actually does (Forge is ground truth). -/
structure PostDelta where
  selfStorageWrites : List (Word × Word) := []
  selfTransientWrites : List (Word × Word) := []
  selfBalance? : Option Word := none
  selfNonce? : Option Word := none
  otherAccounts : List (Word × OpenAccountDelta) := []
  appendLogs : List SolidCore.Solidity.Shared.Log.Entry := []
  createdAccounts : List Word := []
  deriving Repr

def PostDelta.isEmpty (delta : PostDelta) : Bool :=
  delta.selfStorageWrites.isEmpty && delta.selfTransientWrites.isEmpty &&
    delta.selfBalance?.isNone && delta.selfNonce?.isNone &&
    delta.otherAccounts.isEmpty && delta.appendLogs.isEmpty &&
    delta.createdAccounts.isEmpty

/-- The A2 value-transfer debit applied to the echoed world's self (caller)
    account — same success/kind table as `ExternalInteraction.selfBalanceDebit`,
    floored at 0 like the retired record-side debit was. -/
def debitWorldSelf (world : SolidCore.Solidity.Shared.OpenWorld)
    (self : Word) (debit : Word) :
    SolidCore.Solidity.Shared.OpenWorld :=
  if debit == 0 then
    world
  else
    let addr := wordToAddress self
    let account := (world.accounts.find? addr).getD default
    let balance := u256ToWord account.balance
    let balance' :=
      if balance >= debit then
        SolidCore.Solidity.Shared.subWord balance debit
      else
        0
    { world with
      accounts :=
        world.accounts.insert addr
          { account with balance := wordToU256 balance' } }

/-- Credit `addr`'s balance by `amount` in the open world (used by the
    selfdestruct balance transfer, gap CS1). -/
def creditWorldAccount (world : SolidCore.Solidity.Shared.OpenWorld)
    (addr : Word) (amount : Word) :
    SolidCore.Solidity.Shared.OpenWorld :=
  if amount == 0 then
    world
  else
    let a := wordToAddress addr
    let account := (world.accounts.find? a).getD default
    { world with
      accounts :=
        world.accounts.insert a
          { account with
            balance :=
              wordToU256
                (SolidCore.Solidity.Shared.addWord
                  (u256ToWord account.balance) amount) } }

/-- Set `addr`'s balance to `amount` in the open world (used to zero the
    self-destructing contract, gap CS1). -/
def setWorldAccountBalance (world : SolidCore.Solidity.Shared.OpenWorld)
    (addr : Word) (amount : Word) :
    SolidCore.Solidity.Shared.OpenWorld :=
  let a := wordToAddress addr
  let account := (world.accounts.find? a).getD default
  { world with
    accounts :=
      world.accounts.insert a
        { account with balance := wordToU256 amount } }

/-- `selfdestruct(recipient)` moves the contract's ENTIRE balance to `recipient`
    (unconditionally — this is independent of EIP-6780, which only governs
    whether the account is DELETED, tracked separately by the selfdestruct
    record). Model it in the open/post world: credit the recipient by the self
    balance, THEN zero self. Crediting before zeroing makes the
    self-destruct-to-self edge net to 0 (matching the EVM, where a same-tx
    account is deleted), and a distinct recipient is credited by the full self
    balance. The old model recorded the (from, recipient, delete) facts but
    moved no balance (gap CS1). -/
def State.selfdestructTransfer (context : Context) (state : State)
    (recipient : Word) : State :=
  let amount := state.selfBalance
  let world := snapshotWorld context state
  let world := creditWorldAccount world recipient amount
  let world := setWorldAccountBalance world context.self 0
  { state with
    selfBalance := 0
    envWorld? := some world
    worldMutatedSinceAdoption := true }

/-- Apply a responder row's delta to the (possibly debit-folded) echo world:
    slot-keyed self storage/transient writes, absolute balance/nonce
    overrides, other-account fact overrides, appended callee logs, and
    created-accounts additions. -/
def PostDelta.apply (delta : PostDelta) (self : Word)
    (world : SolidCore.Solidity.Shared.OpenWorld) :
    SolidCore.Solidity.Shared.OpenWorld :=
  let selfAddr := wordToAddress self
  let selfAccount := (world.accounts.find? selfAddr).getD default
  let selfAccount :=
    { selfAccount with
      storage :=
        delta.selfStorageWrites.foldl
          (fun acc kv => acc.insert (wordToU256 kv.1) (wordToU256 kv.2))
          selfAccount.storage
      transientStorage :=
        delta.selfTransientWrites.foldl
          (fun acc kv => acc.insert (wordToU256 kv.1) (wordToU256 kv.2))
          selfAccount.transientStorage
      balance :=
        match delta.selfBalance? with
        | some b => wordToU256 b
        | none => selfAccount.balance
      nonce :=
        match delta.selfNonce? with
        | some n => wordToU256 n
        | none => selfAccount.nonce }
  let accounts :=
    delta.otherAccounts.foldl
      (fun (acc : EvmYul.AddrMap EvmCompiler.Simulation.OpenAccount) entry =>
        let addr := wordToAddress entry.1
        let account := (acc.find? addr).getD default
        acc.insert addr
          { account with
            balance :=
              match entry.2.balance? with
              | some b => wordToU256 b
              | none => account.balance
            codeBytes :=
              match entry.2.code? with
              | some code => bytesToByteArray code
              | none => account.codeBytes })
      (world.accounts.insert selfAddr selfAccount)
  { accounts := accounts
    substate :=
      { world.substate with
        logSeries :=
          world.substate.logSeries ++
            (delta.appendLogs.map logEntryToEvm).toArray }
    createdAccounts :=
      delta.createdAccounts.foldl
        (fun acc a => acc.insert (wordToAddress a))
        world.createdAccounts }

inductive OracleRow where
  | call : LowLevelCallResult → OracleRow
  | callWithPost : LowLevelCallResult → PostDelta → OracleRow
  | create : ContractCreationResult → OracleRow
  | createWithPost : ContractCreationResult → PostDelta → OracleRow
  deriving Repr

abbrev ScriptedResponder := List OracleRow

def ScriptedResponder.callRows (responder : ScriptedResponder) :
    List (LowLevelCallResult × Option PostDelta) :=
  responder.filterMap (fun row =>
    match row with
    | OracleRow.call c => some (c, none)
    | OracleRow.callWithPost c post => some (c, some post)
    | _ => none)

def ScriptedResponder.createRows (responder : ScriptedResponder) :
    List (ContractCreationResult × Option PostDelta) :=
  responder.filterMap (fun row =>
    match row with
    | OracleRow.create c => some (c, none)
    | OracleRow.createWithPost c post => some (c, some post)
    | _ => none)

/-- Answer a call request from the responder's call rows; `none` on a total
    miss. Keying + gas fallback mirror `answerCall` exactly; the sent world
    NEVER participates in matching. The answered `postWorld` is the echo world
    with the A2 debit folded in (`selfBalance?` on the row replaces the debit
    entirely), then the row's delta applied. -/
def ScriptedResponder.answerCall? (responder : ScriptedResponder)
    (world : SolidCore.Solidity.Shared.OpenWorld)
    (request : EvmCompiler.Simulation.CallRequest) :
    Option EvmCompiler.Simulation.CallResponse :=
  let kind := callKindToLowLevel request.kind
  let target := addressToWord request.codeAddress
  let calldata := byteArrayToBytes request.calldata
  let value := u256ToWord request.transferValue
  let rows := responder.callRows
  let rowMatches := fun (row : LowLevelCallResult × Option PostDelta) gas? =>
    row.1.matchesRequest kind target calldata value gas?
  let row? :=
    match rows.find? (fun row =>
        rowMatches row (some (u256ToWord request.requestedGas))) with
    | some r => some r
    | none => rows.find? (fun row => rowMatches row none)
  row?.map (fun (result, post?) =>
    let self := addressToWord request.caller
    let debit :=
      ExternalInteraction.selfBalanceDebit
        (ExternalInteraction.lowLevelCall result)
    let base :=
      -- An absolute `selfBalance?` replaces the debit entirely (§3.1).
      if (post?.map (fun p => p.selfBalance?.isSome)).getD false then
        world
      else
        debitWorldSelf world self debit
    { success := result.success
      returnData := bytesToByteArray result.output
      postWorld :=
        match post? with
        | some post => post.apply self base
        | none => base
      returnedGas := request.requestedGas })

/-- Answer a create request from the responder's create rows; `none` on a total
    miss OR a malformed name-encoded initCode (fail-closed) OR an ill-formed
    row combining `address = 0` (failed create) with a nonempty delta
    (risk R7: a failed create's postWorld is the echo world by revert
    semantics; a delta on it is a fixture bug, rejected fail-closed). -/
def ScriptedResponder.answerCreate? (responder : ScriptedResponder)
    (world : SolidCore.Solidity.Shared.OpenWorld)
    (request : EvmCompiler.Simulation.CreateRequest) :
    Option EvmCompiler.Simulation.CreateResponse := do
  let (name, args) ← decodeCreationInitCode? request.initCode
  let value := u256ToWord request.value
  let salt? := request.salt.map u256ToWord
  let (result, post?) ←
    responder.createRows.find? (fun row =>
      row.1.toCreationRequest.matchesRequest name args value salt?)
  let failed := !result.success || result.address == 0
  if failed && !((post?.map PostDelta.isEmpty).getD true) then
    none
  else
    let self := addressToWord request.creator
    let debit :=
      ExternalInteraction.selfBalanceDebit
        (ExternalInteraction.contractCreation result)
    let base :=
      if (post?.map (fun p => p.selfBalance?.isSome)).getD false then
        world
      else
        debitWorldSelf world self debit
    some
      { address := wordToU256 (if result.success then result.address else 0)
        returnData := bytesToByteArray result.output
        postWorld :=
          match post? with
          | some post => post.apply self base
          | none => base
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
      (EvmCompiler.Simulation.Query.external world
        (EvmCompiler.Simulation.ExternalRequest.call request)) k =>
      -- Row-first precedence: the precompile answer is consulted only on a
      -- responder-row miss, so scripted precompile rows answer unchanged.
      match responder.answerCall? world request with
      | some response => SolI.runWith responder (k response)
      | none =>
          match precompileAnswerCall? world request with
          | some response => SolI.runWith responder (k response)
          | none =>
              .error (ResponderFailure.unmatched
                (EvmCompiler.Simulation.ExternalRequest.call request))
  | .request
      (EvmCompiler.Simulation.Query.external world
        (EvmCompiler.Simulation.ExternalRequest.create request)) k =>
      match responder.answerCreate? world request with
      | some response => SolI.runWith responder (k response)
      | none =>
          .error (ResponderFailure.unmatched
            (EvmCompiler.Simulation.ExternalRequest.create request))
  | .request (EvmCompiler.Simulation.Query.resource r) k =>
      -- Resource queries (`gas`/`msize`, A3) are a DIFFERENT query arm from the
      -- external call/create requests matched above: they are answered ambiently,
      -- never treated as an unmatched-external miss. This context-free responder
      -- fold carries no ambient gas word, so `gas` takes the canonical default
      -- (`0`); no corpus fixture emits a `gasleft` query through this path
      -- (verified: 0 corpus `gasleft` users), so every corpus value is unchanged.
      -- A context-bearing fold (`contextAnswer`/`SolI.run`, `SolI.runFromContext`)
      -- answers `gas` with the ambient `context.gasleft`.
      SolI.runWith responder
        (k (EvmCompiler.Simulation.Query.defaultAnswer
          (EvmCompiler.Simulation.Query.resource r)))

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
      match responder.answerCall? world request with
      | some response => response
      | none =>
          -- Row-first precedence (see `SolI.runWith`): precompile staticcalls
          -- with no scripted row are answered in-semantics before the
          -- fail-open default.
          match precompileAnswerCall? world request with
          | some response => response
          | none =>
              EvmCompiler.Simulation.Query.defaultAnswer
                (EvmCompiler.Simulation.Query.external world
                  (EvmCompiler.Simulation.ExternalRequest.call request))
  | EvmCompiler.Simulation.Query.external world
      (EvmCompiler.Simulation.ExternalRequest.create request) =>
      match responder.answerCreate? world request with
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
  -- A storage write is a use site: force any deferred cleanup first (a
  -- storage-loaded out-of-range enum panics 0x21 here, matching solc's
  -- `update_storage_value` → `cleanup_t_enum`).
  let value ← value.forceAbiLazy
  let coerced ←
    match ty.coerceValue? value with
    | some coerced => Except.ok coerced
    | none => Except.error RevertData.typeMismatch
  match ty, coerced with
  | Ty.externalFunction, Value.externalFunction addr selector =>
      match externalFunctionStorageWord? addr selector with
      | some word => Except.ok word
      | none => Except.error RevertData.typeMismatch
  | Ty.internalFunction, Value.internalFunction id =>
      Except.ok (SolidCore.Solidity.Shared.norm id % internalFunctionIdModulus)
  | _, _ =>
      match coerced.asStorageWord? with
      | some word => Except.ok word
      | none => Except.error RevertData.typeMismatch

-- R2: pad a source fixed-array VALUE to a fixed destination's length by
-- appending the element default (`defaultLike` of an existing element, which is
-- the zero of that element's shape). Applied at the non-mutual store entry so
-- the value handed to the structural-recursive `storeStorageLayoutAt` already
-- has the exact length (padding elements would otherwise break its structural
-- recursion). solc widens `T[N] = S[M]` (N ≥ M, guaranteed by the typecheck)
-- and zero-fills the M..N tail.
def Value.padFixedArrayTo (size : Nat) : Value -> Value
  | Value.fixedArray values =>
      if values.length < size then
        match values with
        | v :: _ =>
            Value.fixedArray
              (values ++ List.replicate (size - values.length) v.defaultLike)
        | [] => Value.fixedArray values
      else
        Value.fixedArray values
  | value => value

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
    let length := (raw - 1) / 2
    -- solc `extract_byte_array_length` (YulUtilFunctions.cpp:1359) panics with
    -- StorageEncodingError (0x22) when `eq(outOfPlaceEncoding, lt(length, 32))`.
    -- Here the low bit is set (long / out-of-place form), so an encoded length
    -- below 32 is a malformed word and must revert Panic(0x22).
    if length < 32 then
      Except.error RevertData.invalidStorageByteArray
    else
      Except.ok { length := length, long := true }

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
      | some layout@(StorageLayout.fixedArray _ _) =>
          -- R2: a whole-fixed-storage-array READ (e.g. the RHS of a storage
          -- array copy `dstFixed = srcFixed`) materialises every element.
          State.loadStorageLayoutAt runtime.state field.slot layout
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
  | some layout@(StorageLayout.fixedArray size _) => do
      -- R2: pad a shorter source fixed-array to the dest length before storing.
      let state ←
        State.storeStorageLayoutAt runtime.state field.slot layout
          (value.padFixedArrayTo size)
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

/-- ITEM-4 (`contents` vs `load []`): ONE reader. On a `bytes`/`string`
    layout the `contents` read (`Runtime.loadStorageByteStringField`) and the
    whole-value materializing `load []` (`Runtime.loadStoragePath name []` →
    `State.loadStorageLayoutAt slot layout` → `State.loadStorageBytesAt`)
    are PROVABLY the same read: `resolveStoragePathSlot slot layout [] =
    (slot, layout)` and `loadStorageLayoutAt` on `bytes`/`string` is exactly
    `loadStorageBytesAt`. This def therefore delegates to the shared
    layout reader — the read semantics can never diverge again.

    The MODES nevertheless stay distinct, because they differ in a property
    that is not the read value: `Expr.hasStorageRoot` is `false` for
    `contents` (a `bytes(state)`/`string(state)` CAST is a materialized
    VALUE) and `true` for `load` (a storage lvalue root), and `.length`/
    `[i]` evaluation routes on that bit (value-indexing a loaded
    `Value.bytes` vs a storage element read). On non-bytes layouts the two
    also differ: `contents` fail-closes (`typeMismatch`) while `load`
    materializes — unreachable from the lowering (which gates `contents` on
    `bytes`/`string` targets) but load-bearing for hand-built core. Those
    two corners are the precise residue that blocks deleting the mode. -/
def Runtime.loadStorageByteStringField (context : Context)
    (runtime : Runtime) (name : String) : Except RevertData Value := do
  let field ←
    match context.storageField? name with
    | some field => Except.ok field
    | none => Except.error RevertData.typeMismatch
  match field.layout? with
  | some StorageLayout.bytes =>
      runtime.state.loadStorageLayoutAt field.slot StorageLayout.bytes
  | some StorageLayout.string =>
      runtime.state.loadStorageLayoutAt field.slot StorageLayout.string
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
          -- R2: fixed-dest copy `T[N] = S[M]`, N > M — pad the tail with the
          -- element default (typecheck guarantees N ≥ M).
          let values :=
            if values.length < size then
              match values with
              | v :: _ =>
                  values ++ List.replicate (size - values.length) v.defaultLike
              | [] => values
            else
              values
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
  | some layout@(StorageLayout.struct _), Value.tuple _ => do
      -- STORE-TAIL-CLEAR: a whole-struct assignment must recurse so that any
      -- dynamic-array member shrinking below its stored length gets its tail
      -- element slots zeroed (solc `copy_struct_to_storage` →
      -- `cleanup_storage_array_end`). The deep-store recursion already does
      -- this at every level; the plain `storeStorageField` path did not.
      let state ←
        State.storeStorageLayoutAtWithDeepClear runtime.state
          field.slot layout value
      Except.ok { runtime with state }
  | some layout@(StorageLayout.fixedArray size _), Value.fixedArray _ => do
      -- STORE-TAIL-CLEAR: same for a whole fixed-array assignment whose
      -- elements are structs / dynamic arrays. Pad a shorter source first
      -- (R2), matching the plain path, then recurse to tail-zero shrunk
      -- dynamic-array members at every level.
      let state ←
        State.storeStorageLayoutAtWithDeepClear runtime.state
          field.slot layout (value.padFixedArrayTo size)
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
  -- `bytes(s)[i] = v` reinterprets a storage `string` as `bytes` (identical
  -- length-prefixed layout), so the byte write is valid and must hit the same
  -- path as a `bytes` field. Direct `s[i] = v` on a `string` is rejected by the
  -- typechecker, so `string` reaches here only via that reinterpret peel.
  | some StorageLayout.bytes
  | some StorageLayout.string => do
      let key ← index.expectWord
      let word ← coerceStorageWordAs (Ty.fixedBytes 1) value
      let state ←
        State.storeStorageByteAt runtime.state field.slot key word
      Except.ok { runtime with state }
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

/-- WS2: the anchor slot + layout of a `StorageBase`. For a `.field` base
    this is the state variable's static slot and declared layout (with the
    legacy scalar fallback and the transient-with-indexes rejection exactly
    as the old name-rooted helpers had); for a `.slot` base it is the
    captured slot + layout — nothing is re-resolved. -/
def Runtime.storageBaseAnchor (context : Context)
    (_runtime : Runtime) (base : StorageBase) (indexes : List Value) :
    Except RevertData (Word × StorageLayout) :=
  match base with
  | StorageBase.slot slot layout => Except.ok (slot, layout)
  | StorageBase.field name => do
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
      -- A top-level PACKED scalar state variable carries its sub-slot
      -- offset/width on the `StorageField` record (`packedOffset`/`packedBytes`/
      -- `packedSigned`), while its `layout?` is a whole-word `scalar` (the
      -- packing lives on the field, mirroring solc's per-slot placement). The
      -- `loadStorageField`/`storeFieldWord` accessors honour `field.isPacked`,
      -- but the `resolveStorageBasePath` reader/writer used by `storagePath`
      -- (e.g. the reference-preserving tuple-assignment RHS) drives off this
      -- anchor layout alone. Reconstitute the `packedScalar` layout here so a
      -- bare packed-variable read extracts just its bits — matching the packed
      -- member layout `Ty.toCoreStorageMemberLayout?` builds — instead of the
      -- whole slot (which, coerced back on store, clobbers the neighbour).
      let layout :=
        match layout with
        | StorageLayout.scalar ty =>
            if field.isPacked then
              StorageLayout.packedScalar field.packedOffset field.packedBytes
                field.packedSigned ty
            else layout
        | _ => layout
      Except.ok (field.slot, layout)

/-- Resolve `indexes` LIVE from a base anchor (bounds checks run here — at
    the access, as the EVM does). For a bound pointer (`.slot` base) the
    already-bound prefix is NOT re-resolved. -/
def Runtime.resolveStorageBasePath (context : Context)
    (runtime : Runtime) (base : StorageBase) (indexes : List Value) :
    Except RevertData (Word × StorageLayout) := do
  let (slot, layout) ← runtime.storageBaseAnchor context base indexes
  State.resolveStoragePathSlot runtime.state slot layout indexes

/-- WS2 BIND-SITE resolution: build the storage-ref VALUE for a pointer
    bound at `base` through `indexes`, resolving the concrete slot ONCE (an
    out-of-bounds index Panics 0x32 HERE, at the bind, as solc does). A
    whole-variable bind keeps the name form. -/
def Runtime.bindStorageRef (context : Context)
    (runtime : Runtime) (base : StorageBase) (indexes : List Value) :
    Except RevertData Value :=
  match base, indexes with
  | StorageBase.field name, [] => Except.ok (Value.storageRef name)
  | _, _ => do
      let (slot, layout) ←
        runtime.resolveStorageBasePath context base indexes
      Except.ok (Value.storageSlotRef slot layout)

def Runtime.loadStorageBasePath (context : Context)
    (runtime : Runtime) (base : StorageBase) (indexes : List Value) :
    Except RevertData Value := do
  let (slot, valueLayout) ←
    runtime.resolveStorageBasePath context base indexes
  runtime.state.loadStorageLayoutAt slot valueLayout

def Runtime.loadStoragePath (context : Context)
    (runtime : Runtime) (name : String) (indexes : List Value) :
    Except RevertData Value :=
  runtime.loadStorageBasePath context (StorageBase.field name) indexes

/- R3 (#192): materialize a value for a VALUE-USE boundary (a builtin that
   needs the value's BYTES/elements — `keccak256`/`sha256`/`ripemd160`/
   `erc7201`, `abi.encode*`, `bytes.concat`/`string.concat`). solc implicitly
   copies a storage `bytes`/`string`/array/struct to memory at that boundary;
   structurally, a storage REF value is loaded in full via the same
   `loadStoragePath` reader every storage-value read uses, and memory refs are
   deep-dereferenced exactly as before. Plain values pass through. -/
mutual

/-- Structurally recursive value-use materialization: unlike the memory-only
    deep deref, this also LOADS storage references NESTED inside aggregates
    (`abi.encode([p1, p2])` with `bytes storage p1/p2` locals produces a
    `Value.fixedArray [storageRef, storageRef]`), which previously survived
    to the consumer unloaded and always failed `asBytes?`/
    `abiEncodeValues?` (`typeMismatch` = Panic(0)). Top-level behavior and
    the memory/lazy handling mirror `derefMemoryValueWithFuel` exactly;
    loaded storage values contain no refs, so no re-recursion after a load. -/
def Runtime.materializeForValueUseFuel (context : Context)
    (runtime : Runtime) : Nat -> Value -> Except RevertData Value
  | 0, _ => Except.error RevertData.typeMismatch
  | _fuel + 1, Value.storageRef name =>
      runtime.loadStoragePath context name []
  | _fuel + 1, Value.storageSlotRef slot layout =>
      runtime.state.loadStorageLayoutAt slot layout
  | fuel + 1, Value.memoryRef id =>
      match runtime.loadMemory? id with
      | some stored =>
          Runtime.materializeForValueUseFuel context runtime fuel stored
      | none => Except.error RevertData.typeMismatch
  | fuel + 1, Value.abiLazy cleanup value => do
      let value ← cleanup.forceValue value
      Runtime.materializeForValueUseFuel context runtime fuel value
  | fuel + 1, Value.fixedArray values => do
      let values ←
        Runtime.materializeForValueUseListFuel context runtime (fuel + 1) values
      Except.ok (Value.fixedArray values)
  | fuel + 1, Value.dynamicArray values => do
      let values ←
        Runtime.materializeForValueUseListFuel context runtime (fuel + 1) values
      Except.ok (Value.dynamicArray values)
  | fuel + 1, Value.tuple values => do
      let values ←
        Runtime.materializeForValueUseListFuel context runtime (fuel + 1) values
      Except.ok (Value.tuple values)
  | _fuel + 1, value => Except.ok value

def Runtime.materializeForValueUseListFuel (context : Context)
    (runtime : Runtime) (fuel : Nat) :
    List Value -> Except RevertData (List Value)
  | [] => Except.ok []
  | value :: rest => do
      let value ←
        Runtime.materializeForValueUseFuel context runtime fuel value
      let rest ←
        Runtime.materializeForValueUseListFuel context runtime fuel rest
      Except.ok (value :: rest)

end

def Runtime.materializeForValueUse (context : Context)
    (runtime : Runtime) (value : Value) : Except RevertData Value :=
  Runtime.materializeForValueUseFuel context runtime
    (runtime.nextMemory + 1) value

def Runtime.materializeForValueUseList (context : Context)
    (runtime : Runtime) : List Value -> Except RevertData (List Value)
  | [] => Except.ok []
  | value :: rest => do
      let head ← runtime.materializeForValueUse context value
      let tail ← runtime.materializeForValueUseList context rest
      Except.ok (head :: tail)

/-- The storage SLOT (as a `Word`) of the storage lvalue rooted at state
    variable `name` and reached through `indexes` — the same slot the value
    forms load from, obtained via `State.resolveStoragePathSlot`, but returned
    rather than dereferenced. Used to ABI-encode a storage pointer by slot on
    the public-library `delegatecall` boundary. -/
def Runtime.storageBasePathSlotValue (context : Context)
    (runtime : Runtime) (base : StorageBase) (indexes : List Value) :
    Except RevertData Word := do
  let (slot, _) ← runtime.resolveStorageBasePath context base indexes
  Except.ok slot

def Runtime.storagePathSlotValue (context : Context)
    (runtime : Runtime) (name : String) (indexes : List Value) :
    Except RevertData Word :=
  runtime.storageBasePathSlotValue context (StorageBase.field name) indexes

def Runtime.storeStorageBasePathWithDeepClear (context : Context)
    (runtime : Runtime) (base : StorageBase) (indexes : List Value)
    (value : Value) : Except RevertData Runtime := do
  let value ← runtime.storageMaterializedValue value
  let (slot, valueLayout) ←
    runtime.resolveStorageBasePath context base indexes
  let state ←
    State.storeStorageLayoutAtWithDeepClear
      runtime.state slot valueLayout value
  Except.ok { runtime with state }

def Runtime.storeStoragePathWithDeepClear (context : Context)
    (runtime : Runtime) (name : String) (indexes : List Value)
    (value : Value) : Except RevertData Runtime :=
  runtime.storeStorageBasePathWithDeepClear context
    (StorageBase.field name) indexes value

def Runtime.deleteStorageBasePath (context : Context)
    (runtime : Runtime) (base : StorageBase) (indexes : List Value) :
    Except RevertData Runtime := do
  let (slot, valueLayout) ←
    runtime.resolveStorageBasePath context base indexes
  let state ←
    State.clearStorageLayoutAtDeep runtime.state slot valueLayout
  Except.ok { runtime with state }

def Runtime.deleteStoragePath (context : Context)
    (runtime : Runtime) (name : String) (indexes : List Value) :
    Except RevertData Runtime :=
  runtime.deleteStorageBasePath context (StorageBase.field name) indexes

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
  -- `bytes(s)[i] = v` reinterprets a storage `string` as `bytes` (identical
  -- length-prefixed layout), so the byte write is valid and must hit the same
  -- path as a `bytes` field. Direct `s[i] = v` on a `string` is rejected by the
  -- typechecker, so `string` reaches here only via that reinterpret peel.
  | some StorageLayout.bytes
  | some StorageLayout.string => do
      let key ← index.expectWord
      let word ← coerceStorageWordAs (Ty.fixedBytes 1) value
      let state ←
        State.storeStorageByteAt runtime.state field.slot key word
      Except.ok { runtime with state }
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
              -- No-arg `push()`: solc/EVM only bumps the length word and relies
              -- on the storage zero-invariant (slots past the length are zero,
              -- maintained by pop/delete). It does NOT re-zero the regrown
              -- element, so a stale write into a freed slot (via a dangling
              -- storage pointer) survives the regrow. Do NOT deep-clear here.
              Except.ok runtime.state
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
        let state ←
          match value? with
          | some value =>
              let word ← coerceStorageWordAs Ty.uint256 value
              Except.ok
                (runtime.state.storeSlot
                  (legacyIndexedStorageSlot field.slot length) word)
          | none =>
              -- No-arg `push()`: length-bump only, no re-zero of the regrown
              -- element (see the layout branch above).
              Except.ok runtime.state
        Except.ok
          { runtime with
            state := state.storeSlot field.slot (normWord rawLength) }
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

/-- Push onto the dynamic array / bytes whose length word lives at `slot`
    with layout `valueLayout` (the shared core of the name-rooted and
    early-bound push forms). -/
def Runtime.storageArrayPushAt
    (runtime : Runtime) (slot : Word) (valueLayout : StorageLayout)
    (value? : Option Value) :
    Except RevertData Runtime := do
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
                  -- No-arg `push()`: length-bump only, no re-zero of the
                  -- regrown element (see `storageArrayPush`).
                  Except.ok runtime.state
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

/-- WS2: base-rooted push. A whole-variable base with no extra indexes keeps
    the field-level `storageArrayPush` (legacy no-layout handling); everything
    else resolves the extra indexes LIVE from the base and pushes at the
    resolved slot. The `.field`-with-indexes case rejects `transient` and
    layoutless fields exactly as the old name-rooted path form did (the
    anchor's scalar fallback dead-ends in `resolveStoragePathSlot`/the
    layout match with the same `typeMismatch`). -/
def Runtime.storageArrayPushBasePath (context : Context)
    (runtime : Runtime) (base : StorageBase) (indexes : List Value)
    (value? : Option Value) :
    Except RevertData Runtime := do
  match base, indexes with
  | StorageBase.field name, [] => runtime.storageArrayPush context name value?
  | _, _ =>
      let (slot, valueLayout) ←
        runtime.resolveStorageBasePath context base indexes
      runtime.storageArrayPushAt slot valueLayout value?

def Runtime.storageArrayPushPath (context : Context)
    (runtime : Runtime) (name : String) (indexes : List Value)
    (value? : Option Value) :
    Except RevertData Runtime :=
  runtime.storageArrayPushBasePath context (StorageBase.field name)
    indexes value?

/-- Pop from the dynamic array / bytes whose length word lives at `slot`. -/
def Runtime.storageArrayPopAt
    (runtime : Runtime) (slot : Word) (valueLayout : StorageLayout) :
    Except RevertData Runtime := do
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

/-- WS2: base-rooted pop (see `storageArrayPushBasePath`). -/
def Runtime.storageArrayPopBasePath (context : Context)
    (runtime : Runtime) (base : StorageBase) (indexes : List Value) :
    Except RevertData Runtime := do
  match base, indexes with
  | StorageBase.field name, [] => runtime.storageArrayPop context name
  | _, _ =>
      let (slot, valueLayout) ←
        runtime.resolveStorageBasePath context base indexes
      runtime.storageArrayPopAt slot valueLayout

def Runtime.storageArrayPopPath (context : Context)
    (runtime : Runtime) (name : String) (indexes : List Value) :
    Except RevertData Runtime :=
  runtime.storageArrayPopBasePath context (StorageBase.field name) indexes

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
  -- SIGNED-CONSTANT-FOLD (S, signed-constant-shift-in-abiencode-arg): a
  -- constant-folded signed expression that the env-less arg path folds to a
  -- plain `Expr.word` (e.g. `abi.encode(int256(5) >> 1)` — the fold in
  -- `Expr.toCore?` discards the operand signedness the surrounding `int256(...)`
  -- cast established) reaches a signed `int256` slot as a `Value.word`, never a
  -- `Value.int`, so the strict `Value.int`-only arm above rejected it with a
  -- SPURIOUS Panic(0) (`typeMismatch`) where solc+EVM encode the value. A value
  -- that reaches an `int256` slot as a `Value.word` is a folded constant that
  -- fits `int256` (typecheck bounds it to < 2^255, so its high bit is clear),
  -- hence its word bits ARE the correct 2's-complement and the boundary bytes
  -- are byte-identical to the `Value.int` encoding above.
  | Ty.int256, Value.word value => some (wordToBytesBE wordBytes value)
  | Ty.fixedBytes size, Value.word value =>
      if abiFixedBytesFits size value then
        some
          (wordToBytesBE size value ++
            List.replicate (wordBytes - size) 0)
      else
        none
  -- R3: width-tagged bytesN — identical left-aligned boundary encoding.
  | Ty.fixedBytes size, Value.fixedBytes _ value =>
      if abiFixedBytesFits size value then
        some
          (wordToBytesBE size value ++
            List.replicate (wordBytes - size) 0)
      else
        none
  -- LIT-COERCION (#141 emit event data + indexed `bytesN` topic): a
  -- hex/string/bytes LITERAL argument to a `bytesN` event field is lowered
  -- target-blind to a dynamic-`bytes` `Value.bytes`. solc coerces it to the
  -- fixed target — ONE left-aligned 32-byte word (the ≤ n meaningful bytes at
  -- the top, zero-padded); a `bytesN` indexed topic is that same word UNHASHED
  -- (value type). This routes both the non-indexed data (`abiEncodeValues?`) and
  -- the indexed topic (`abiEventTopic?`, non-hashed branch → `bytesToWordBE`).
  | Ty.fixedBytes size, Value.bytes bytes =>
      if bytes.length ≤ size then
        some
          (bytes.map normByte ++
            List.replicate (wordBytes - bytes.length) 0)
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

/-- Lift a structural (data-presence / validator) decode failure into the
`abi.decode` failure monad. solc surfaces every such failure as the empty
`revert(0, 0)`, so a `none` here maps to `RevertData.empty`. -/
def abiDecodeOpt {α} : Option α -> Except RevertData α
  | some a => Except.ok a
  | none => Except.error RevertData.empty

/-- solc allocates a dynamic array / `bytes` / `string` decode target BEFORE the
data-presence check, so an oversized runtime length raises Panic(0x41) rather
than the empty revert. Mirror the FULL production allocation path:

* `arrayAllocationSizeFunction` (`YulUtilFunctions.cpp:2362`) opens with
  `if gt(length, 0xffffffffffffffff) { panic_error_0x41() }` on the raw element
  count, then computes the byte size:
    - byte arrays / `string`: `size := roundUp(length)` — the *byte* length
      rounded UP to a multiple of 32 (`round_up_to_mul_of_32`, i.e.
      `and(add(length, 31), not(31))`), NOT `length * 1`, and
    - value arrays `T[]`:     `size := mul(length, 0x20)` — one word (a value or
      a pointer) per element,
  then adds the `0x20` length slot for the dynamic case (`size := add(size, 0x20)`).
* `finalize_allocation` (`YulUtilFunctions.cpp:3256`) then sets
  `newFreePtr := add(memPtr, roundUp(size))` and fires `panic_error_0x41()` when
  `gt(newFreePtr, 0xffffffffffffffff)` (or `lt(newFreePtr, memPtr)`, a
  wraparound). `memPtr` is the CURRENT free-memory pointer — the term the earlier
  guard omitted. Because `memPtr ≥ 0x80`, solc's panic threshold is strictly
  LOWER than the `elementSize * n + 0x20` bound alone.

The model abstracts memory (the decoder is a pure function of the argument
bytes; there is no running free pointer). On the reachable path solc allocates
the decode target at the INITIAL free-memory pointer `0x80`: the external
dispatcher decodes the first/only dynamic reference parameter with the free
pointer still at its `0x80` reset, and a fresh `abi.decode` target is likewise
the first allocation. So `memPtr = 0x80` reproduces solc's threshold exactly on
that path, and — since `memPtr ≥ 0x80` for ANY decode — it is a sound lower
bound that never over-panics on a length solc would accept (a decode preceded by
further allocation has an even lower solc threshold; the residual band above
`0x80` is a memory-layout abstraction limit, not an over-reject).

`size` is already 32-aligned, so the outer `roundUp(size)` is the identity; the
first gate caps `length ≤ 2^64-1`, so `newFreePtr` stays far below `2^256` and
the wraparound arm is unreachable (Nat arithmetic has no wraparound anyway). -/
def abiCheckAllocation? (byteArray : Bool) (length : Word) :
    Except RevertData Unit :=
  let n := SolidCore.Solidity.Shared.norm length
  if n > 0xffffffffffffffff then
    Except.error RevertData.memoryAllocationTooLarge
  else
    -- `arrayAllocationSizeFunction`: byte length rounds UP to a word; value
    -- arrays take one word per element; both add the `0x20` length slot.
    let dataSize := if byteArray then (n + 31) / 32 * 32 else n * wordBytes
    let size := dataSize + wordBytes
    -- `finalize_allocation`: `newFreePtr = memPtr + roundUp(size)`, panic if it
    -- exceeds `2^64-1`. `memPtr = 0x80` = the initial free-memory pointer.
    if 0x80 + size > 0xffffffffffffffff then
      Except.error RevertData.memoryAllocationTooLarge
    else
      Except.ok ()

def abiDecodeValueAtWithFuel? :
    Nat -> List Byte -> Nat -> Ty -> Except RevertData Value
  | 0, _, _, _ => Except.error RevertData.empty
  | _fuel + 1, argData, headIndex, Ty.bool => do
      let value ← abiDecodeOpt (readWord? argData (wordBytes * headIndex))
      if wordEq value 0 || wordEq value 1 then
        Except.ok (Value.word value)
      else
        Except.error RevertData.empty
  | _fuel + 1, argData, headIndex, Ty.address => do
      let value ← abiDecodeOpt (readWord? argData (wordBytes * headIndex))
      if abiAddressFits value then
        Except.ok (Value.word value)
      else
        Except.error RevertData.empty
  | _fuel + 1, argData, headIndex, Ty.uint256 => do
      let value ← abiDecodeOpt (readWord? argData (wordBytes * headIndex))
      Except.ok (Value.word value)
  | _fuel + 1, argData, headIndex, Ty.int256 => do
      let value ← abiDecodeOpt (readWord? argData (wordBytes * headIndex))
      Except.ok (Value.int value)
  | _fuel + 1, argData, headIndex, Ty.fixedBytes size =>
      if 0 < size && size <= wordBytes then
        do
        let slot ← abiDecodeOpt (readBytes? argData (wordBytes * headIndex) wordBytes)
        let bytes ← abiDecodeOpt (readBytes? slot 0 size)
        let padding ← abiDecodeOpt (readBytes? slot size (wordBytes - size))
        if abiAllZeroBytes padding then
          Except.ok (Value.word (bytesToWordBE bytes))
        else
          Except.error RevertData.empty
      else
        Except.error RevertData.empty
  | _fuel + 1, _argData, _headIndex, Ty.internalFunction =>
      -- Internal function pointers have no ABI representation (they cannot
      -- cross the external boundary); decoding one is a type error.
      Except.error RevertData.empty
  | _fuel + 1, argData, headIndex, Ty.externalFunction => do
      let slot ← abiDecodeOpt (readBytes? argData (wordBytes * headIndex) wordBytes)
      let addressBytes ← abiDecodeOpt (readBytes? slot 0 20)
      let selectorPart ← abiDecodeOpt (readBytes? slot 20 selectorBytes)
      let padding ←
        abiDecodeOpt (readBytes? slot (20 + selectorBytes)
          (wordBytes - 20 - selectorBytes))
      if abiAllZeroBytes padding then
        Except.ok
          (Value.externalFunction
            (bytesToWordBE addressBytes) (bytesToWordBE selectorPart))
      else
        Except.error RevertData.empty
  | _fuel + 1, argData, headIndex, Ty.bytesCalldata => do
      let offset ← abiDecodeOpt (readWord? argData (wordBytes * headIndex))
      let length ← abiDecodeOpt (readWord? argData offset)
      -- solc allocates the `bytes`/`string` (element size 1) before the
      -- data-presence check, so an oversized length raises Panic(0x41).
      abiCheckAllocation? true length
      let bytes ← abiDecodeOpt (readBytes? argData (offset + wordBytes) length)
      Except.ok (Value.bytes bytes)
  | fuel + 1, argData, headIndex, Ty.dynamicArray elementTy => do
      let offset ← abiDecodeOpt (readWord? argData (wordBytes * headIndex))
      let length ← abiDecodeOpt (readWord? argData offset)
      -- solc allocates the array (element size 0x20) before reading elements,
      -- so an oversized length raises Panic(0x41) ahead of data presence.
      abiCheckAllocation? false length
      -- Head-area presence check (solc `abi_decode_available_length_*_array`:
      -- `srcEnd := add(arrayPos, mul(length, headStride)); if gt(srcEnd, end)`):
      -- run AFTER the outer allocation guard but BEFORE any element decode, so a
      -- truncated element-head area reverts EMPTY here instead of reaching an
      -- inner dynamic element's Panic(0x41). Stride = element calldata head size
      -- (`step * 0x20`), matching solc's `mul(length, calldata_head)`. `gt` is
      -- strict, so a well-formed head with `srcEnd == end` PASSES.
      let step ← abiDecodeOpt (Ty.abiHeadWords? elementTy)
      if (readBytes? (argData.drop (offset + wordBytes)) 0
            (length * step * wordBytes)).isNone then
        Except.error RevertData.empty
      let rec decodeDynamicValues? : Nat -> Nat -> Except RevertData (List Value)
        | 0, _ => Except.ok []
        | remaining + 1, index => do
            let value ←
              abiDecodeValueAtWithFuel? fuel
                (argData.drop (offset + wordBytes)) index elementTy
            let step ← abiDecodeOpt (Ty.abiHeadWords? elementTy)
            let rest ← decodeDynamicValues? remaining (index + step)
            Except.ok (value :: rest)
      let values ← decodeDynamicValues? length 0
      Except.ok (Value.dynamicArray values)
  | fuel + 1, argData, headIndex, Ty.fixedArray size elementTy =>
      let rec decodeFixedValues? (arrayData : List Byte) :
          Nat -> Nat -> Except RevertData (List Value)
        | 0, _ => Except.ok []
        | remaining + 1, index => do
            let value ←
              abiDecodeValueAtWithFuel? fuel arrayData index elementTy
            let step ← abiDecodeOpt (Ty.abiHeadWords? elementTy)
            let rest ← decodeFixedValues? arrayData remaining (index + step)
            Except.ok (value :: rest)
      if Ty.isDynamicAbi elementTy then
        do
        let offset ← abiDecodeOpt (readWord? argData (wordBytes * headIndex))
        -- Upfront head-area presence check when FOLLOWING the tail offset
        -- (solc `abi_decode_available_length_*`, fixed length `size`): the
        -- `size` element head words must be present BEFORE any element decode,
        -- so a truncated head reverts EMPTY here instead of a later inner
        -- Panic(0x41). Keep in sync with the boundary decoder's fixed-array
        -- frame (`ABI.lean`, `decodeValueAtWithFuel?`).
        let step ← abiDecodeOpt (Ty.abiHeadWords? elementTy)
        if (readBytes? (argData.drop offset) 0
              (size * step * wordBytes)).isNone then
          Except.error RevertData.empty
        let values ← decodeFixedValues? (argData.drop offset) size 0
        Except.ok (Value.fixedArray values)
      else
        do
        -- Static-element fixed array decoded inline in the head: covered by
        -- the ENCLOSING frame's upfront head-size check (it counts the full
        -- static width), so no separate check is needed here.
        let values ← decodeFixedValues? argData size headIndex
        Except.ok (Value.fixedArray values)
  | fuel + 1, argData, headIndex, Ty.tuple elementTys =>
      let rec decodeTupleValues? (tupleData : List Byte) :
          List Ty -> Nat -> Except RevertData (List Value)
        | [], _ => Except.ok []
        | ty :: tys, index => do
            let value ← abiDecodeValueAtWithFuel? fuel tupleData index ty
            let step ← abiDecodeOpt (Ty.abiHeadWords? ty)
            let rest ← decodeTupleValues? tupleData tys (index + step)
            Except.ok (value :: rest)
      if Ty.listHasDynamicAbi elementTys then
        do
        let offset ← abiDecodeOpt (readWord? argData (wordBytes * headIndex))
        -- solc `abi_decode_t_struct`: `if slt(sub(end, offset), <headSize>)
        -- { revert(0,0) }` BEFORE any member decode — a truncated member-head
        -- area reverts EMPTY here instead of a later inner Panic(0x41). Keep
        -- in sync with the boundary decoder's tuple frame (`ABI.lean`,
        -- `decodeValueAtWithFuel?`).
        let headWords ← abiDecodeOpt (Ty.listAbiHeadWords? elementTys)
        if (readBytes? (argData.drop offset) 0
              (headWords * wordBytes)).isNone then
          Except.error RevertData.empty
        let values ← decodeTupleValues? (argData.drop offset) elementTys 0
        Except.ok (Value.tuple values)
      else
        do
        -- Fully-static tuple decoded inline in the head: covered by the
        -- ENCLOSING frame's upfront head-size check (it counts the full
        -- static width), so no separate check is needed here.
        let values ← decodeTupleValues? argData elementTys headIndex
        Except.ok (Value.tuple values)
  -- `enumStorage` is a storage-layout-only type; it never appears in an ABI
  -- position (params/returns lower enums to `uint256` + `AbiCleanup.enum`).
  | _fuel + 1, _, _, Ty.enumStorage _ => Except.error RevertData.empty

def abiDecodeValueAt? (argData : List Byte) (headIndex : Nat)
    (ty : Ty) : Except RevertData Value :=
  abiDecodeValueAtWithFuel? (Ty.abiDecodeFuel ty) argData headIndex ty

def abiDecodeValuesAux? (argData : List Byte) :
    List Ty -> Nat -> Except RevertData (List Value)
  | [], _ => Except.ok []
  | ty :: tys, index => do
      let value ← abiDecodeValueAt? argData index ty
      let headWords ← abiDecodeOpt (Ty.abiHeadWords? ty)
      let values ← abiDecodeValuesAux? argData tys (index + headWords)
      Except.ok (value :: values)

/-- `abi.decode` decoder distinguishing Panic(0x41) (oversized allocation of a
dynamic decode target) from the empty revert (data-presence / validator
failures). -/
def abiDecodeValuesExcept? (tys : List Ty) (argData : List Byte) :
    Except RevertData (List Value) := do
  -- solc's decoder OPENS with `if slt(sub(dataEnd, headStart), <totalHeadSize>)
  -- { revert(0,0) }`: the WHOLE static head of the decoded tuple must be
  -- present BEFORE any component decode. Head size: 1 word per dynamic
  -- component (its tail offset), full static width per static component
  -- (recursively for nested static tuples / fixed arrays) — exactly
  -- `Ty.listAbiHeadWords?`. Without this, short data (e.g. 63 bytes for a
  -- `(uint256[], uint256)` head of 64) follows a garbage offset and dies later
  -- with Panic(0x41) instead of solc's upfront EMPTY revert. Keep in sync with
  -- the boundary decoder's identical check (`ABI.lean`, `decodeArgsWith?`).
  let headWords ← abiDecodeOpt (Ty.listAbiHeadWords? tys)
  if argData.length < wordBytes * headWords then
    Except.error RevertData.empty
  abiDecodeValuesAux? argData tys 0

/-- Option view of the decoder, for callers that only need success/failure and
not the failure mode (e.g. external-return decoding and witness checks). -/
def abiDecodeValues? (tys : List Ty) (argData : List Byte) :
    Option (List Value) :=
  match abiDecodeValuesExcept? tys argData with
  | Except.ok values => some values
  | Except.error _ => none

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
  -- SIGNED-CONSTANT-FOLD (S): mirror the `abiStaticBytes?` int256 arm — a
  -- constant-folded signed shift `abi.encodePacked(int256(5) >> 1)` reaches the
  -- signed slot as a (correctly 2's-complement-represented) `Value.word`; encode
  -- it byte-identically to the `Value.int` case instead of Panic(0)'ing.
  | Ty.int256, Value.word value => some (wordToBytesBE wordBytes value)
  | Ty.fixedBytes size, Value.word value =>
      if 0 < size && size <= wordBytes then
        some (wordToBytesBE size value)
      else
        none
  | Ty.fixedBytes size, Value.fixedBytes _ value =>
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
  match ty, value with
  -- A nested STATIC array element (e.g. the `uint[2]` inside `uint[2][3]`) is
  -- packed by recursing element-wise; solc pads array elements to 32 bytes but
  -- keeps them in-place, so the inner elements route back through the padded
  -- element path. Dynamic-array elements are rejected upstream by the packed
  -- type-shape check, so they stay unencodable here.
  | Ty.fixedArray size elementTy, Value.fixedArray values =>
      if values.length == size then
        abiEncodePackedArrayValues? elementTy values
      else
        none
  | Ty.fixedArray _ _, _ => none
  | Ty.dynamicArray _, _ => none
  | Ty.tuple _, _ => none
  | _, _ => abiEventIndexedBytes? true ty value

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

/-- How a storage READ rooted at a top-level state variable produces its
    value. The old representation enumerated these as four SEPARATE
    constructors (`storage`/`storageBytes`/`storageIndex`/`storagePath`),
    which meant "bare header read" and "full content load" were different
    CONSTRUCTORS rather than one location with a read-mode — so every
    value-use boundary (abi.encode*/keccak256/emit/…) had to individually
    rewrite the header form to the loading form (the ~40-site
    `materializeStorageValueUseCore` whack-a-mole, #192 + #4–#10). With an
    explicit mode, "materialize" is a MODE FLIP (`header` → `load`) on one
    constructor.

    - `header`: the state variable's HEADER word (the `.length` convention
      for `bytes`, the slot word for dynamic arrays) or its whole value for
      scalar/packed/struct/fixed-array layouts; transient- and packed-aware
      (`Runtime.loadStorageField`). Old `Expr.storage`.
    - `contents`: the full `bytes`/`string` CONTENTS (`Value.bytes`), the
      `bytes(x)`/`string(x)` cast of a bytes/string state variable
      (`Runtime.loadStorageByteStringField`). Old `Expr.storageBytes`.
    - `element`: a single-step indexed read (mapping value / array element /
      struct field / bytes byte) with the exact one-step semantics of
      `Runtime.loadStorageIndex` (byte reads return the right-aligned byte
      word; the legacy no-layout slot fallback applies). Expects exactly one
      index expression. Old `Expr.storageIndex`.
    - `load`: the fully MATERIALIZING read through an index path
      (`Runtime.loadStoragePath`); `load name []` loads the whole value
      (bytes/string → `Value.bytes`, arrays → elements, structs → tuples).
      Old `Expr.storagePath`. -/
inductive StorageReadMode where
  | header : StorageReadMode
  /-- A BARE state-variable IDENTIFIER in expression position: the value is a
      REFERENCE to the variable that a value-use boundary must materialize
      (`normalizeStorageValueUses` flips `ref` → `load` there). Evaluates
      exactly like `header` (the header-word convention) when it survives to
      pointer positions. This mode exists because the bare header word is
      AMBIGUOUS in the legacy representation: `stateBytes.length` and the
      synthesized `push()`-last-index reads deliberately lower to the header
      WORD (mode `header`, never rewritten), while a bare `stateBytes`
      argument is an unmaterialized reference (mode `ref`, rewritten at
      value-use boundaries). Conflating them is what made the per-boundary
      materializer rewrite `.length` reads too. -/
  | ref : StorageReadMode
  | contents : StorageReadMode
  | element : StorageReadMode
  | load : StorageReadMode
  deriving Repr

/-- ITEM-3 (cosmetic constructor families): which value the projection of an
    external-function VALUE produces. `value selector` builds the packed
    external-function value from an address expression (the legacy
    `externalFunctionValue`); `selector`/`address` project the stored
    selector/address word back out. -/
inductive ExtFnPart where
  | value : Word -> ExtFnPart
  | selector : ExtFnPart
  | address : ExtFnPart
  deriving Repr

/-- ITEM-3: the parameterized cast/cleanup family. Each kind carries the
    non-target payload it needs (`fixedBytes` its SOURCE word size); the
    target width/size is the `Nat` argument of `Expr.castOp`. Legacy
    spellings (`uintCast`/`intCast`/`uintCleanup`/`intCleanup`/
    `fixedBytesCast`/`fixedBytesFromBytes`) remain as `@[match_pattern]`
    smart constructors. -/
inductive CastKind where
  | uintCast : CastKind
  | intCast : CastKind
  | uintCleanup : CastKind
  | intCleanup : CastKind
  | fixedBytes : Nat -> CastKind
  | fixedBytesFromBytes : CastKind
  deriving Repr

/-- ITEM-3: the `abi.encode*` family selector. `plain` = `abi.encode`,
    `withSelector` = `abi.encodeWithSelector`/`encodeWithSignature`/
    `encodeCall` (the selector expression rides in the `Option Expr` slot of
    `Expr.encode`), `packed` = `abi.encodePacked` (the packed top widths ride
    in the `List Nat` slot). -/
inductive EncodeKind where
  | plain : EncodeKind
  | withSelector : EncodeKind
  | packed : EncodeKind
  deriving Repr

inductive Expr where
  | word : Word -> Expr
  | intWord : Word -> Expr
  /-- Internal-function-pointer literal: a function identifier used in value
      position compiles to its per-contract dispatch ID
      (`docs/refs-completion-solc-research.md` §2). Evaluates to
      `Value.internalFunction id`. -/
  | internalFunction : Word -> Expr
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
  /-- The storage SLOT (as a `uint256` word) of a top-level storage state
      variable. Used to ABI-encode a `T storage` pointer argument on the
      external (public/external) library `delegatecall` boundary: solc passes
      the callee's storage `self` as its slot number in the delegatecall
      calldata (see `Ty.abiCanonical` `... storage` signatures). Evaluates to
      `context.storageSlot? name` — a compile-time-constant slot for a
      top-level state variable. -/
  | storageSlot : String -> Expr
  /-- The storage SLOT (as a `uint256` word) of a storage LVALUE rooted at a
      top-level state variable and reached through mapping keys / array indices /
      struct-field ordinals (`indexes`). Generalises `storageSlot` to
      `mapping`-value, array-element and struct-member storage pointers passed on
      the external/public-library `delegatecall` boundary (LIB-STORAGE-PUBLIC-2).
      Evaluates by resolving the same slot path the value forms
      (`storageIndex`/`storagePath`) use — `State.resolveStoragePathSlot` from the
      field's base slot and layout — and returning that slot number, without
      loading the value. -/
  | storagePathSlot : String -> List Expr -> Expr
  /-- The storage SLOT (as a `uint256` word) of a `T storage` local pointer
      (`Foo storage p = …`) reached through further `indexes`. The pointer is a
      `Value.storageSlotRef` (or whole-variable `Value.storageRef`) in the
      runtime; the slot is the resolution of `indexes` from the pointer's
      captured base. Used to encode such a local as its slot on the
      public-library `delegatecall` boundary. -/
  | storageRefSlot : String -> List Expr -> Expr
  /-- The unified storage-value READ: one location (state-variable `name` +
      `indexes` path) with an explicit `StorageReadMode` saying WHICH value the
      read produces (header word vs bytes contents vs one-step element vs full
      materializing load). `header`/`contents` ignore `indexes` (always `[]`
      from lowering); `element` expects exactly one index. See
      `StorageReadMode`'s doc comment for the exact per-mode semantics and the
      legacy constructor each mode replaces. The legacy names
      (`Expr.storage`/`storageBytes`/`storageIndex`/`storagePath`) remain as
      `@[match_pattern]` smart constructors below. -/
  | storageRead : StorageReadMode -> String -> List Expr -> Expr
  /-- ITEM-3 (e): the unified external-function-value projection family
      (`ExtFnPart`). Legacy spellings `externalFunctionValue`/
      `externalFunctionSelector`/`externalFunctionAddress` remain as
      `@[match_pattern]` smart constructors. -/
  | extFnPart : ExtFnPart -> Expr -> Expr
  | unary : UnaryOp -> Expr -> Expr
  /-- ITEM-3 (a): the unified inc/dec family — `incDec op returnOld cleanup?
      target`. `op` is `add` (increment) or `sub` (decrement); `returnOld`
      is the fixity (`true` = postfix, return the OLD value); `cleanup?`
      carries the narrow-width cleanup when present. Legacy spellings
      (`preIncrement`/`preDecrement`/`postIncrement`/`postDecrement`/
      `incDecCleanup`) remain as `@[match_pattern]` smart constructors. -/
  | incDec : BinaryOp -> Bool -> Option ValueCleanup -> Expr -> Expr
  /-- ITEM-3 (b): the unified assignment-expression family — `assignment op?
      cleanup? target rhs`. `op? = none` is plain `=` (RHS value written and
      returned, no LHS read); `some op` is compound read-modify-write;
      `cleanup?` the optional narrow-width result cleanup. Legacy spellings
      (`assignExpr`/`assignOpExpr`/`assignOpCleanupExpr`) remain as
      `@[match_pattern]` smart constructors. -/
  | assignment : Option BinaryOp -> Option ValueCleanup -> Expr -> Expr -> Expr
  | binary : BinaryOp -> Expr -> Expr -> Expr
  | addMod : Expr -> Expr -> Expr -> Expr
  | mulMod : Expr -> Expr -> Expr -> Expr
  | concatBytes : List Expr -> Expr
  | fixedBytesIndex : Nat -> Expr -> Expr -> Expr
  /-- ITEM-3 (c): the unified cast/cleanup family — `castOp kind target
      operand` (see `CastKind`; `target` is the bit width for int/uint kinds
      and the byte size for the fixed-bytes kinds). Legacy spellings remain
      as `@[match_pattern]` smart constructors. -/
  | castOp : CastKind -> Nat -> Expr -> Expr
  | keccak256 : Expr -> Expr
  | erc7201 : Expr -> Expr
  | tuple : List Expr -> Expr
  /-- ITEM-3 (d): the unified `abi.encode*` family — `encode kind selector?
      packedWidths tys args` (see `EncodeKind`; `selector?` is `some` exactly
      for `withSelector`, `packedWidths` non-degenerate exactly for
      `packed`). Legacy spellings (`abiEncode`/`abiEncodeWithSelector`/
      `abiEncodePacked`) remain as `@[match_pattern]` smart constructors. -/
  | encode :
      EncodeKind -> Option Expr -> List Nat -> List Ty -> List Expr -> Expr
  | abiDecode : List Ty -> List AbiCleanup -> Expr -> Expr
  | lowLevelCall :
      LowLevelCallKind -> Expr -> Expr -> Expr -> Option Expr -> Bool -> Expr
  -- `contractCreate contractName args value salt? valueBeforeSalt`: the final
  -- `Bool` records whether the `{value, salt}` options were written value-before-
  -- salt in source (solc evaluates the options in source order — DIV-CREATE-2).
  | contractCreate : String -> Expr -> Expr -> Option Expr -> Bool -> Expr
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

/-- Legacy spellings of the unified `Expr.storageRead` (see `StorageReadMode`).
    `@[match_pattern]` lets existing construction sites AND patterns keep the
    old names; they unfold to the single parameterized constructor, so any
    semantic dispatch over the family happens in ONE place (on the mode). -/
@[match_pattern] def Expr.storage (name : String) : Expr :=
  Expr.storageRead StorageReadMode.header name []

/-- A bare state-variable identifier in expression position (see
    `StorageReadMode.ref`). -/
@[match_pattern] def Expr.storageIdent (name : String) : Expr :=
  Expr.storageRead StorageReadMode.ref name []

@[match_pattern] def Expr.storageBytes (name : String) : Expr :=
  Expr.storageRead StorageReadMode.contents name []

@[match_pattern] def Expr.storageIndex (name : String) (idx : Expr) : Expr :=
  Expr.storageRead StorageReadMode.element name [idx]

@[match_pattern] def Expr.storagePath (name : String)
    (indexes : List Expr) : Expr :=
  Expr.storageRead StorageReadMode.load name indexes

/-! ITEM-3 legacy spellings. Exactly like the `storageRead` family above:
    `@[match_pattern]` smart constructors keep every construction site AND
    pattern compiling under the old names, while the semantic dispatch for
    each family happens in ONE eval arm (on the kind parameter). -/

@[match_pattern] def Expr.externalFunctionValue (addressExpr : Expr)
    (selector : Word) : Expr :=
  Expr.extFnPart (ExtFnPart.value selector) addressExpr

@[match_pattern] def Expr.externalFunctionSelector (expr : Expr) : Expr :=
  Expr.extFnPart ExtFnPart.selector expr

@[match_pattern] def Expr.externalFunctionAddress (expr : Expr) : Expr :=
  Expr.extFnPart ExtFnPart.address expr

@[match_pattern] def Expr.preIncrement (target : Expr) : Expr :=
  Expr.incDec BinaryOp.add false none target

@[match_pattern] def Expr.preDecrement (target : Expr) : Expr :=
  Expr.incDec BinaryOp.sub false none target

@[match_pattern] def Expr.postIncrement (target : Expr) : Expr :=
  Expr.incDec BinaryOp.add true none target

@[match_pattern] def Expr.postDecrement (target : Expr) : Expr :=
  Expr.incDec BinaryOp.sub true none target

@[match_pattern] def Expr.incDecCleanup (target : Expr) (op : BinaryOp)
    (post : Bool) (cleanup : ValueCleanup) : Expr :=
  Expr.incDec op post (some cleanup) target

@[match_pattern] def Expr.assignExpr (target rhs : Expr) : Expr :=
  Expr.assignment none none target rhs

@[match_pattern] def Expr.assignOpExpr (target : Expr) (op : BinaryOp)
    (rhs : Expr) : Expr :=
  Expr.assignment (some op) none target rhs

@[match_pattern] def Expr.assignOpCleanupExpr (target : Expr) (op : BinaryOp)
    (rhs : Expr) (cleanup : ValueCleanup) : Expr :=
  Expr.assignment (some op) (some cleanup) target rhs

@[match_pattern] def Expr.uintCast (bits : Nat) (expr : Expr) : Expr :=
  Expr.castOp CastKind.uintCast bits expr

@[match_pattern] def Expr.intCast (bits : Nat) (expr : Expr) : Expr :=
  Expr.castOp CastKind.intCast bits expr

@[match_pattern] def Expr.uintCleanup (bits : Nat) (expr : Expr) : Expr :=
  Expr.castOp CastKind.uintCleanup bits expr

@[match_pattern] def Expr.intCleanup (bits : Nat) (expr : Expr) : Expr :=
  Expr.castOp CastKind.intCleanup bits expr

@[match_pattern] def Expr.fixedBytesCast (targetSize sourceSize : Nat)
    (expr : Expr) : Expr :=
  Expr.castOp (CastKind.fixedBytes sourceSize) targetSize expr

@[match_pattern] def Expr.fixedBytesFromBytes (targetSize : Nat)
    (expr : Expr) : Expr :=
  Expr.castOp CastKind.fixedBytesFromBytes targetSize expr

@[match_pattern] def Expr.abiEncode (tys : List Ty)
    (exprs : List Expr) : Expr :=
  Expr.encode EncodeKind.plain none [] tys exprs

@[match_pattern] def Expr.abiEncodeWithSelector (selectorExpr : Expr)
    (tys : List Ty) (exprs : List Expr) : Expr :=
  Expr.encode EncodeKind.withSelector (some selectorExpr) [] tys exprs

@[match_pattern] def Expr.abiEncodePacked (widths : List Nat)
    (tys : List Ty) (exprs : List Expr) : Expr :=
  Expr.encode EncodeKind.packed none widths tys exprs

def Expr.hasStorageRoot : Expr -> Bool
  -- `contents` (old `storageBytes`) was NOT a storage root in the legacy
  -- enumeration; the other three modes were. Preserved exactly.
  | Expr.storageRead StorageReadMode.contents _ _ => false
  | Expr.storageRead _ _ _ => true
  | Expr.index base _ => Expr.hasStorageRoot base
  | _ => false

def Expr.hasStorageRefRoot (runtime : Runtime) : Expr -> Bool
  | Expr.var name => runtime.lookupStorageBase? name |>.isSome
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
  | Expr.storageIdent name => some (LValue.storage name)
  | Expr.storageIndex name idx => some (LValue.storageIndex name idx)
  | Expr.index base idx => do
      let baseTarget ← Expr.toLValue? base
      some (LValue.index baseTarget idx)
  | _ => none

/-- Should this assignment target receive its RHS reference-preservingly (as a
    `Value.memoryRef` pointer, aliasing) rather than as a dereferenced/copied
    value? True exactly when the target denotes a MEMORY location: a memory-ref
    local, or a memory aggregate element/field (an `index` whose base is neither
    a storage variable nor a storage-alias local). Storage / immutable targets
    return false so storage stores keep deep-copy semantics; value-type locals
    return false (their RHS is never a memory pointer anyway). -/
def LValue.wantsMemoryRefRhs (target : LValue) (runtime : Runtime) : Bool :=
  match target with
  | LValue.var name => (runtime.lookupMemoryRef? name).isSome
  | LValue.index base _ =>
      let baseExpr := base.toExpr
      ! (Expr.hasStorageRoot baseExpr || Expr.hasStorageRefRoot runtime baseExpr)
  | _ => false

/-- Should this assignment target receive its RHS as a storage-ref POINTER
    (RE-POINTING the local, like the scalar `p = q` → `storageAliasAssignFrom`)
    rather than as a dereferenced/copied value? True exactly when the target is a
    bare storage-pointer local (`T storage p`). A `p.a`/`p[i]` member/index target
    is a THROUGH-write and returns false (its store deep-copies as before). This
    is what makes a tuple assignment `(p, q) = (q, p)` swap the POINTERS instead
    of swapping the pointed-to contents. -/
def LValue.wantsStorageRefRhs (target : LValue) (runtime : Runtime) : Bool :=
  match target with
  | LValue.var name => (runtime.lookupStorageBase? name).isSome
  | _ => false

/-- A component of a NESTED tuple-assignment LHS (`((a, b), c) = …`). `hole` is
    an omitted component (its RHS value is still produced, then discarded);
    `leaf` is an ordinary assignable target; `nested` is a parenthesized
    sub-tuple destructured against a `Value.tuple` sub-value in lockstep. The
    flat `Stmt.assignTuple` (`List (Option LValue)`) is unchanged and still used
    for non-nested LHSs; only genuinely nested LHSs elaborate to `nested`. -/
inductive TupleTarget where
  | hole : TupleTarget
  | leaf : LValue -> TupleTarget
  | nested : List TupleTarget -> TupleTarget
  deriving Repr

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

/-- Exponentiation by squaring, O(log e). `combine` reduces each partial product
    to keep the intermediates bounded: modular reduction (`natPowMod`) for the
    two's-complement wrapped result, saturation (`natPowCapped`) for overflow
    detection. `fuel` bounds the number of halvings of `e`; a 256-bit exponent
    needs at most 256, so `expFuel = 257` never runs out.

    Item #2 (soundness of termination + value): the previous `checkedExpLoop`
    multiplied the accumulator `e` times, so a large runtime exponent (e.g.
    `2 ** (2**200)`) looped 2^200 times and hung, whereas solc/EVM produce the
    wrapped result in O(log e). This computes both observables in O(log e) while
    preserving the checked overflow-Panic-0x11 point exactly (see the overflow
    predicate below). -/
def expBySquaring (combine : Nat -> Nat -> Nat) :
    Nat -> Nat -> Nat -> Nat -> Nat
  | 0, acc, _, _ => acc
  | fuel + 1, acc, b, e =>
      if e = 0 then acc
      else
        let acc := if e % 2 = 1 then combine acc b else acc
        let e' := e / 2
        let b := if e' = 0 then b else combine b b
        expBySquaring combine fuel acc b e'

def expFuel : Nat := 257

/-- `base ^ exp mod modulus`, O(log exp). Every intermediate stays `< modulus`. -/
def natPowMod (base exp modulus : Nat) : Nat :=
  expBySquaring (fun x y => x * y % modulus) expFuel (1 % modulus)
    (base % modulus) exp

/-- `min (base ^ exp) cap`, O(log exp). Saturates at `cap`: because every
    intermediate power in exponentiation by squaring is `<= base ^ exp`, the
    result equals the true power exactly when it is `< cap`, and equals `cap`
    (i.e. `>= cap`) exactly when the true power is `>= cap`. This lets checked
    exp detect overflow at the same point as the naive repeated-multiply loop. -/
def natPowCapped (base exp cap : Nat) : Nat :=
  expBySquaring (fun x y => min (x * y) cap) expFuel 1 base exp

def checkedExp (checked : Bool) (base exponent : Word) :
    Except RevertData Word :=
  let b := SolidCore.Solidity.Shared.norm base
  let e := SolidCore.Solidity.Shared.norm exponent
  if checked && wordModulus <= natPowCapped b e wordModulus then
    Except.error RevertData.overflow
  else
    Except.ok (normWord (natPowMod b e wordModulus))

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

-- Signed exponentiation with two's-complement wrapping, O(log e) (items #2/#6).
-- The exponent is a non-negative magnitude (Solidity rejects negative
-- exponents). The two's-complement wrapped word is `(base_word) ^ e mod 2^256`,
-- computed modularly. Checked int256 overflow is decided from the magnitude
-- `|base| ^ e` and the result sign (`base < 0 && e` odd): a positive result
-- overflows at `|r| >= 2^255` (max int256 = 2^255 - 1), a negative one at
-- `|r| > 2^255` (min int256 = -2^255). This detects overflow at exactly the
-- same point as the old repeated-multiply loop. Narrow-type (`intN`) result
-- overflow is still enforced by the enclosing `intCleanup` the importer inserts.
def checkedSignedExp (checked : Bool) (base exponent : Word) :
    Except RevertData Word :=
  let e := SolidCore.Solidity.Shared.norm exponent
  let wrapped := normWord (natPowMod (SolidCore.Solidity.Shared.norm base) e wordModulus)
  if checked then
    let bInt := SolidCore.Solidity.Shared.signedValue base
    let mag := natPowCapped bInt.natAbs e wordModulus
    let negative := decide (bInt < 0) && (e % 2 = 1)
    let overflow :=
      if negative then
        SolidCore.Solidity.Shared.halfWordModulus < mag
      else
        SolidCore.Solidity.Shared.halfWordModulus <= mag
    if overflow then
      Except.error RevertData.overflow
    else
      Except.ok wrapped
  else
    Except.ok wrapped

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

/-- R3: does a binary op on bytesN operands PRESERVE the bytesN width on its
    result? Bitwise/shift ops do (`a & b`, `a << k` are bytesN-typed); the
    comparisons produce a bool word. The word bits are computed exactly as
    before in both cases — only the width tag is added. -/
def BinaryOp.preservesFixedBytesWidth : BinaryOp -> Bool
  | BinaryOp.bitAnd => true
  | BinaryOp.bitOr => true
  | BinaryOp.bitXor => true
  | BinaryOp.shl => true
  | BinaryOp.shr => true
  | BinaryOp.sar => true
  | _ => false

def BinaryOp.apply
    (checked : Bool) (op : BinaryOp) (lhs rhs : Value) :
    Except RevertData Value := do
  -- Operators are use sites: force deferred cleanups first (a storage-loaded
  -- out-of-range enum operand panics 0x21 here, matching solc routing both
  -- comparison operands through `cleanup_t_enum`).
  let lhs ← lhs.forceAbiLazy
  let rhs ← rhs.forceAbiLazy
  -- R3: bytesN operands compute on the RAW word exactly as before (the
  -- lowering already emits the width cleanups); the tag is peeled here and
  -- re-attached on width-preserving results below.
  let (lhs, lhsSize?) :=
    match lhs with
    | Value.fixedBytes size word => (Value.word word, some size)
    | value => (value, none)
  let (rhs, rhsSize?) :=
    match rhs with
    | Value.fixedBytes size word => (Value.word word, some size)
    | value => (value, none)
  let retag : Value -> Value := fun result =>
    match result, (if op.preservesFixedBytesWidth then lhsSize?.orElse (fun _ => rhsSize?) else none) with
    | Value.word word, some size => Value.fixedBytes size word
    | value, _ => value
  (fun result => retag result) <$> (do
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
      | Value.internalFunction lhsId, Value.internalFunction rhsId =>
          -- Internal function pointers are dispatch IDs; two pointers are
          -- equal iff they refer to the same function (same dispatch identity).
          -- solc 0.8.35 legacy (optimizer=false) compiles `fp == g` to an
          -- id/code-pointer comparison returning a bool.
          Except.ok (Value.word (boolWord (wordEq lhsId rhsId)))
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
      | Value.internalFunction lhsId, Value.internalFunction rhsId =>
          Except.ok (Value.word (boolWord (!(wordEq lhsId rhsId))))
      | _, _ => Except.error RevertData.typeMismatch
  | _ =>
      match lhs, rhs with
      | Value.word lhsWord, Value.word rhsWord => do
          let value ← op.applyWord checked lhsWord rhsWord
          Except.ok (Value.word value)
      | Value.int lhsWord, Value.int rhsWord =>
          op.applySignedWord checked lhsWord rhsWord
      -- MIXED SIGNED/WORD (packed-signed unpack #11): a SIGNED operand
      -- (`Value.int`, e.g. an `intCast` of a packed `intN` storage/array element)
      -- meeting a `Value.word` operand — the shape the env-less `Expr.toCore?`
      -- emits for a signed binary whose other operand is a literal (`word 1000`),
      -- e.g. inside `uint256(int8Elem + 1000)`. By Solidity's typing rules a
      -- `Value.int` operand forces the WHOLE operation signed (int/uint never
      -- mix), so the raw word is the 2's-complement of a signed value: dispatch
      -- to the signed path. This matters because signed and unsigned differ in
      -- the overflow check (`-1 + 1000` overflows as unsigned but not signed).
      -- `applySignedWord` reproduces the previous `shl`/`shr`/`sar`/`exp`
      -- handling here exactly, and additionally handles `add`/`sub`/`mul`/`div`/
      -- `mod`/bitwise/comparisons that previously Panic(0)'d as `typeMismatch`.
      | Value.int lhsWord, Value.word rhsWord =>
          op.applySignedWord checked lhsWord rhsWord
      | Value.word lhsWord, Value.int rhsWord =>
          op.applySignedWord checked lhsWord rhsWord
      | _, _ => Except.error RevertData.typeMismatch)

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
      -- R3: same raw complement as the untagged word (the lowering's width
      -- cleanup masks it), with the width preserved on the result.
      | Value.fixedBytes size word =>
          Except.ok
            (Value.fixedBytes size (SolidCore.Solidity.Shared.notWord word))
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

def enumFromUIntValue (maxValue : Word) (value : Value) :
    Except RevertData Value := do
  -- Conversion is a use site: force deferred cleanups first (a storage-loaded
  -- out-of-range enum re-validated through `E(x)` panics 0x21 here).
  let value ← value.forceAbiLazy
  match value with
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
  /-- WS2: a storage lvalue rooted at an EARLY-BOUND pointer: captured base
      slot + layout, plus the extra indexes accumulated at THIS use (resolved
      live against the captured base — never from the root). -/
  | storageSlotPath : Word -> StorageLayout -> List Value -> ResolvedLValue
  | valueIndex : ResolvedLValue -> Word -> ResolvedLValue
  deriving Repr

def ResolvedLValue.asStoragePath? :
    ResolvedLValue -> Option (StorageBase × List Value)
  | ResolvedLValue.storageField name => some (StorageBase.field name, [])
  | ResolvedLValue.storageIndex name index =>
      some (StorageBase.field name, [index])
  | ResolvedLValue.storagePath name indexes =>
      some (StorageBase.field name, indexes)
  | ResolvedLValue.storageSlotPath slot layout indexes =>
      some (StorageBase.slot slot layout, indexes)
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
  | ResolvedLValue.storageSlotPath slot layout indexes =>
      runtime.loadStorageBasePath context (StorageBase.slot slot layout)
        indexes
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
  | ResolvedLValue.storageSlotPath slot layout indexes =>
      runtime.storeStorageBasePathWithDeepClear context
        (StorageBase.slot slot layout) indexes value
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
  | ResolvedLValue.storageSlotPath slot layout indexes =>
      runtime.storeStorageBasePathWithDeepClear context
        (StorageBase.slot slot layout) indexes value
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
          -- `delete input` on a whole memory-reference LOCAL repoints the local
          -- to a fresh zeroed graph (solc allocates a brand-new object at the
          -- free pointer). It must NOT mutate the pointed-to cell in place: any
          -- surviving alias (`T x = input; delete input;`) keeps observing the
          -- OLD cell. Build the fresh zeroed value graph (runtime-aware, so
          -- nested memoryRefs become fresh empty/zeroed cells — the #168 fix),
          -- store it as a NEW cell, and rebind the local to it.
          let (runtime', zeroed) ← runtime.deleteZeroValueDeep value
          let (runtime'', freshRef) := runtime'.memoryStoreValue zeroed
          match runtime''.assignLocal? name freshRef with
          | some updated => Except.ok updated
          | none => Except.error RevertData.typeMismatch
      | some value =>
          match runtime.assignLocal? name value.defaultLike with
          | some updated => Except.ok updated
          | none => Except.error RevertData.typeMismatch
      | none => Except.error RevertData.typeMismatch
  | ResolvedLValue.memoryCell id =>
      match runtime.loadMemory? id with
      | some value => do
          let (runtime', zeroed) ← runtime.deleteZeroValueDeep value
          match runtime'.storeMemory? id zeroed with
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
  | ResolvedLValue.storageSlotPath slot layout indexes =>
      runtime.deleteStorageBasePath context (StorageBase.slot slot layout)
        indexes
  | ResolvedLValue.valueIndex base index => do
      let baseValue ← base.read context runtime
      let baseValue ← runtime.derefMemoryValue baseValue
      let oldValue ← baseValue.index? index
      let (runtime', zeroed) ← runtime.deleteZeroValueDeep oldValue
      let updatedBase ← baseValue.setIndex? index zeroed
      base.writeContainer context runtime' updatedBase

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
  | Expr.internalFunction _ => 1
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
  | Expr.storageSlot _ => 1
  | Expr.storagePathSlot _ indexes => Expr.listEvalFuel indexes + 1
  | Expr.storageRefSlot _ indexes => Expr.listEvalFuel indexes + 1
  -- Uniform bound for every read mode: `listEvalFuel indexes + 1` dominates
  -- each mode's actual consumption (`header`/`contents` evaluate no indexes;
  -- `element` evaluates its single index directly; `load` evaluates the list).
  -- Only sufficiency matters (fuel results are stable above the need).
  | Expr.storageRead _ _ indexes => Expr.listEvalFuel indexes + 1
  | Expr.extFnPart _ expr => Expr.orderFuel expr + 1
  | Expr.unary _ expr => Expr.orderFuel expr + 1
  | Expr.incDec _ _ _ target => Expr.orderFuel target + 1
  | Expr.assignment _ _ target rhs =>
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
  | Expr.castOp _ _ expr => Expr.orderFuel expr + 1
  | Expr.keccak256 expr => Expr.orderFuel expr + 1
  | Expr.erc7201 expr => Expr.orderFuel expr + 1
  | Expr.tuple exprs => Expr.listEvalFuel exprs + 1
  | Expr.encode _ selector? _ _ exprs =>
      (match selector? with
      | some selectorExpr => Expr.orderFuel selectorExpr
      | none => 0) + Expr.listEvalFuel exprs + 1
  | Expr.abiDecode _ _ expr => Expr.orderFuel expr + 1
  | Expr.lowLevelCall _ targetExpr calldataExpr valueExpr gas? _ =>
      Expr.orderFuel targetExpr + Expr.orderFuel calldataExpr +
        Expr.orderFuel valueExpr +
          (match gas? with
          | some gas => Expr.orderFuel gas
          | none => 0) + 1
  | Expr.contractCreate _ args value salt? _ =>
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

def Expr.evalFuel (fuel : Nat)
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
          | Expr.internalFunction id =>
              pure (Value.internalFunction (normWord id), runtime)
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
              match which with
              | EnvWord.gasleft => do
                  -- A3: `gasleft` is a resource query, not an ambient read.
                  let gas ← emitGasleft
                  pure (Value.word gas, runtime)
              | _ => pure (Value.word (which.eval context), runtime)
          | Expr.envLookup which keyExpr => do
              let (keyValue, runtime') ←
                Expr.evalFuel fuel context runtime keyExpr
              let key ← keyValue.expectWord
              -- A2: `address(this).balance` / `selfbalance` (an accountBalance
              -- lookup keyed on `self`) read the dynamic self balance.
              -- openworld/postworld Stage 2: other-address facts come from the
              -- ADOPTED world when one exists (`State.env*`), falling back to
              -- the Context seed maps pre-adoption.
              let result :=
                match which with
                | EnvLookup.accountBalance =>
                    if wordEq key context.self then
                      runtime'.state.selfBalance
                    else
                      runtime'.state.envAccountBalance context key
                | EnvLookup.accountCodehash =>
                    if context.evmVersion.constantinopleOrLater then
                      runtime'.state.envAccountCodehash context key
                    else
                      0
                | _ => which.eval context key
              pure (Value.word result, runtime')
          | Expr.envBytesLookup which keyExpr => do
              let (keyValue, runtime') ←
                Expr.evalFuel fuel context runtime keyExpr
              let key ← keyValue.expectWord
              let result :=
                match which with
                | EnvBytesLookup.accountCode =>
                    runtime'.state.envAccountCode context key
              pure (Value.bytes result, runtime')
          | Expr.var name =>
              match runtime.lookupStorageBase? name with
              | some base => do
                  let value ←
                    runtime.loadStorageBasePath context base []
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
          | Expr.storageRead mode name indexes =>
              (match mode with
              | StorageReadMode.header
              | StorageReadMode.ref => do
                  -- Header word / whole-scalar read; transient- and
                  -- packed-aware. Indexes are always `[]` from lowering and
                  -- are ignored (exactly the old `Expr.storage` semantics).
                  let value ← runtime.loadStorageField context name
                  pure (value, runtime)
              | StorageReadMode.contents => do
                  let value ←
                    runtime.loadStorageByteStringField context name
                  pure (value, runtime)
              | StorageReadMode.element =>
                  match indexes with
                  | [idx] => do
                      let (indexValue, runtime') ←
                        Expr.evalFuel fuel context runtime idx
                      let value ←
                        runtime'.loadStorageIndex context name indexValue
                      pure (value, runtime')
                  | _ =>
                      throw <| SolidityFailure.revert RevertData.typeMismatch
              | StorageReadMode.load => do
                  let (indexValues, runtime') ←
                    Expr.evalListFuel fuel context runtime
                      indexes
                  -- SCALAR COINCIDENCE: for a scalar-layout state variable the
                  -- header/load distinction does not exist — there is nothing
                  -- to "materialize". Route the whole-variable load through
                  -- the same transient- and packed-aware reader `.header`
                  -- uses, so the normalizer's `header → load` flip is
                  -- semantically a NO-OP on scalars (including TRANSIENT
                  -- scalars, which `loadStoragePath []` would misread from
                  -- the persistent slot — the pre-existing
                  -- `abi.encode(transientScalar)` divergence). Aggregate
                  -- layouts (bytes/string/arrays/structs) keep the exact
                  -- `loadStoragePath` materializing semantics.
                  let scalarWhole :=
                    indexValues.isEmpty &&
                      (match context.storageField? name with
                      | some field =>
                          match field.layout? with
                          | some (StorageLayout.scalar _) => true
                          | some (StorageLayout.packedScalar _ _ _ _) => true
                          | some _ => false
                          | none => true
                      | none => false)
                  if scalarWhole then
                    let value ← runtime'.loadStorageField context name
                    pure (value, runtime')
                  else
                    let value ←
                      runtime'.loadStoragePath context name indexValues
                    pure (value, runtime'))
          | Expr.storageSlot name =>
              match context.storageSlot? name with
              | some slot => pure (Value.word slot, runtime)
              | none =>
                  throw <| SolidityFailure.revert RevertData.typeMismatch
          | Expr.storagePathSlot name indexes => do
              let (indexValues, runtime') ←
                Expr.evalListFuel fuel context runtime
                  indexes
              let slot ←
                runtime'.storagePathSlotValue context name indexValues
              pure (Value.word slot, runtime')
          | Expr.storageRefSlot name indexes => do
              let (indexValues, runtime') ←
                Expr.evalListFuel fuel context runtime
                  indexes
              match runtime'.lookupStorageBase? name with
              | some base => do
                  let slot ←
                    runtime'.storageBasePathSlotValue context base
                      indexValues
                  pure (Value.word slot, runtime')
              | none =>
                  throw <| SolidityFailure.revert RevertData.typeMismatch
          | Expr.extFnPart part expr => do
              let (value, runtime') ←
                Expr.evalFuel fuel context runtime expr
              match part with
              | ExtFnPart.value selector => do
                  let address ← value.expectWord
                  pure (Value.externalFunction address selector, runtime')
              | ExtFnPart.selector =>
                  match value with
                  | Value.externalFunction _ selector =>
                      pure (Value.word selector, runtime')
                  | _ => throw <| SolidityFailure.revert RevertData.typeMismatch
              | ExtFnPart.address =>
                  match value with
                  | Value.externalFunction addr _ =>
                      pure (Value.word addr, runtime')
                  | _ => throw <| SolidityFailure.revert RevertData.typeMismatch
          | Expr.unary op expr => do
              let (value, runtime') ←
                Expr.evalFuel fuel context runtime expr
              let result ← op.apply context.checked value
              pure (result, runtime')
          | Expr.incDec op returnOld cleanup? target => do
              -- ITEM-3 (a): ONE dispatch for the inc/dec family; the legacy
              -- five constructors are (op, returnOld, cleanup?) points.
              let (resolved, runtime') ←
                Expr.resolveLValueFuel fuel context
                  runtime target
              match cleanup? with
              | none => resolved.applyIncDec context runtime' op returnOld
              | some cleanup =>
                  resolved.applyIncDecCleanup context runtime' op returnOld
                    cleanup
          | Expr.assignment op? cleanup? target rhs => do
              -- ITEM-3 (b): ONE dispatch for the assignment-expression family.
              -- Intrinsic order (solc ExpressionCompiler.cpp:319,331,336-370):
              -- the RHS is evaluated fully BEFORE the LHS reference (and, for
              -- compound ops, the LHS read).
              let (rhsValue, runtime') ←
                Expr.evalFuel fuel context
                  runtime rhs
              let (resolved, runtime'') ←
                Expr.resolveLValueFuel fuel
                  context runtime' target
              match op? with
              | none => do
                  -- Plain `=`: write the RHS value through; no LHS read and
                  -- no cleanup (the lowering never emits one for plain `=`).
                  let updated ← resolved.write context runtime'' rhsValue
                  pure (rhsValue, updated)
              | some op => do
                  let lhsValue ← resolved.read context runtime''
                  let value ←
                    BinaryOp.apply context.checked op lhsValue rhsValue
                  match cleanup? with
                  | none => do
                      let updated ← resolved.write context runtime'' value
                      pure (value, updated)
                  | some cleanup => do
                      -- Left shifts truncate to the operand width with no
                      -- overflow check, even inside a checked block, so the
                      -- compound-assign cleanup for `<<=` must be applied
                      -- unchecked.
                      let cleanupChecked :=
                        match op with
                        | BinaryOp.shl => false
                        | _ => context.checked
                      let cleaned ← cleanup.apply cleanupChecked value
                      let updated ← resolved.write context runtime'' cleaned
                      pure (cleaned, updated)
          | Expr.binary BinaryOp.boolAnd lhs rhs => do
              let (lhsValue, runtime') ←
                Expr.evalFuel fuel context runtime lhs
              let lhsWord ← lhsValue.expectWord
              if wordTruthy lhsWord then
                let (rhsValue, runtime'') ←
                  Expr.evalFuel fuel context runtime' rhs
                let rhsWord ← rhsValue.expectWord
                pure
                  (Value.word (boolWord (wordTruthy rhsWord)), runtime'')
              else
                pure (Value.word 0, runtime')
          | Expr.binary BinaryOp.boolOr lhs rhs => do
              let (lhsValue, runtime') ←
                Expr.evalFuel fuel context runtime lhs
              let lhsWord ← lhsValue.expectWord
              if wordTruthy lhsWord then
                pure (Value.word 1, runtime')
              else
                let (rhsValue, runtime'') ←
                  Expr.evalFuel fuel context runtime' rhs
                let rhsWord ← rhsValue.expectWord
                pure
                  (Value.word (boolWord (wordTruthy rhsWord)), runtime'')
          | Expr.binary op lhs rhs => do
              -- Intrinsic order (solc ExpressionCompiler.cpp:614-615): binary
              -- operands are evaluated RIGHT first, then LEFT.
              let ((lhsValue, rhsValue), runtime'') ← do
                    let (rhsValue, runtime') ←
                      Expr.evalFuel fuel context runtime
                        rhs
                    let (lhsValue, runtime'') ←
                      Expr.evalFuel fuel context runtime'
                        lhs
                    pure ((lhsValue, rhsValue), runtime'')
              let value ← BinaryOp.apply context.checked op lhsValue rhsValue
              pure (value, runtime'')
          | Expr.addMod lhs rhs modulus => do
              let (values, runtime') ←
                Expr.evalListFuel fuel context runtime
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
                Expr.evalListFuel fuel context runtime
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
                Expr.evalListFuel fuel context runtime
                  exprs
              -- R3 (#192): storage refs/memory refs materialize uniformly at
              -- this value-use boundary.
              let values ← runtime'.materializeForValueUseList context values
              match Value.concatBytes? values with
              | some bs => pure (Value.bytes bs, runtime')
              | none => throw <| SolidityFailure.revert RevertData.typeMismatch
          | Expr.fixedBytesIndex size base idx => do
              let (values, runtime') ←
                Expr.evalListFuel fuel context runtime
                  [base, idx]
              match values with
              | [baseValue, indexValue] => do
                  let word ← baseValue.expectWord
                  let indexWord ← indexValue.expectWord
                  let value ← fixedBytesIndex? size word indexWord
                  pure (value, runtime')
              | _ => throw <| SolidityFailure.revert RevertData.typeMismatch
          | Expr.castOp kind target expr => do
              -- ITEM-3 (c): ONE dispatch for the cast/cleanup family; each
              -- kind applies its own conversion to the single evaluated
              -- operand.
              let (value, runtime') ←
                Expr.evalFuel fuel context runtime expr
              match kind with
              | CastKind.uintCast => do
                  let casted ← uintCast? target value
                  pure (casted, runtime')
              | CastKind.intCast => do
                  let casted ← intCast? target value
                  pure (casted, runtime')
              | CastKind.uintCleanup => do
                  let casted ← uintCleanup? context.checked target value
                  pure (casted, runtime')
              | CastKind.intCleanup => do
                  let casted ← intCleanup? context.checked target value
                  pure (casted, runtime')
              | CastKind.fixedBytes sourceSize => do
                  let word ← value.expectWord
                  let casted ← fixedBytesCast? target sourceSize word
                  pure (casted, runtime')
              | CastKind.fixedBytesFromBytes =>
                  match value.asBytes? with
                  | some bytes => do
                      let casted ← fixedBytesFromBytes? target bytes
                      pure (casted, runtime')
                  | none =>
                      throw <| SolidityFailure.revert RevertData.typeMismatch
          | Expr.keccak256 expr => do
              let (value, runtime') ←
                Expr.evalFuel fuel context runtime expr
              -- M4/R3 (#192): fully materialize memory refs AND storage refs
              -- at this value-use boundary; an unmaterialized ref has no
              -- `asBytes?`.
              let value ← runtime'.materializeForValueUse context value
              match value.asBytes? with
              | some bytes =>
                  pure (Value.fixedBytes wordBytes (keccakWord bytes), runtime')
              | none => throw <| SolidityFailure.revert RevertData.typeMismatch
          | Expr.erc7201 expr => do
              let (value, runtime') ←
                Expr.evalFuel fuel context runtime expr
              let value ← runtime'.materializeForValueUse context value
              match value.asBytes? with
              | some bytes =>
                  pure (Value.word (erc7201Slot bytes), runtime')
              | none => throw <| SolidityFailure.revert RevertData.typeMismatch
          | Expr.externalHash kind expr => do
              let (value, runtime') ←
                Expr.evalFuel fuel context runtime expr
              let value ← runtime'.materializeForValueUse context value
              match value.asBytes? with
              | some bytes =>
                  match ← emitPrecompileWord context runtime'.state
                      kind.precompileKind bytes with
                  | (some hash, adoptedState) =>
                      pure (Value.word hash,
                        { runtime' with state := adoptedState })
                  | (none, _) => throw <| SolidityFailure.revert RevertData.typeMismatch
              | none => throw <| SolidityFailure.revert RevertData.typeMismatch
          | Expr.ecrecover digestExpr vExpr rExpr sExpr => do
              let (values, runtime') ←
                Expr.evalListFuel fuel context runtime
                  [digestExpr, vExpr, rExpr, sExpr]
              match values with
              | [digestValue, vValue, rValue, sValue] => do
                  let digest ← digestValue.expectWord
                  let v ← vValue.expectWord
                  let r ← rValue.expectWord
                  let s ← sValue.expectWord
                  let (address, adoptedState) ←
                    emitPrecompileWord context runtime'.state
                      SolidCore.Solidity.Shared.Precompile.Kind.ecrecover
                      (SolidCore.Solidity.Shared.Precompile.ecrecoverInput digest v r s)
                  pure (Value.word (address.getD 0),
                    { runtime' with state := adoptedState })
              | _ => throw <| SolidityFailure.revert RevertData.typeMismatch
          | Expr.tuple exprs => do
              let (values, runtime') ←
                Expr.evalListFuel fuel context runtime
                  exprs
              pure (Value.tuple values, runtime')
          | Expr.fixedArray exprs => do
              let (values, runtime') ←
                Expr.evalListFuel fuel context runtime
                  exprs
              pure (Value.fixedArray values, runtime')
          | Expr.encode kind selector? widths tys exprs => do
              -- ITEM-3 (d): ONE dispatch for the `abi.encode*` family. The
              -- optional selector expression rides at the head of the SAME
              -- evaluation list the legacy `abiEncodeWithSelector` arm used
              -- (`selectorExpr :: exprs`) — argument order and fuel
              -- consumption are byte-identical to the legacy three arms.
              -- Ref-nested memory values deep-materialize (M4) before the
              -- value-structural encoder runs.
              let (values, runtime') ←
                Expr.evalListFuel fuel context runtime
                  (match selector? with
                  | some selectorExpr => selectorExpr :: exprs
                  | none => exprs)
              let (selector?, argValues) ←
                match selector?, values with
                | some _, selectorValue :: argValues => do
                    let selector ← selectorValue.expectWord
                    pure (some selector, argValues)
                | some _, [] =>
                    throw <| SolidityFailure.revert RevertData.typeMismatch
                | none, argValues => pure ((none : Option Word), argValues)
              let argValues ←
                runtime'.materializeForValueUseList context argValues
              let encoded? :=
                match kind with
                | EncodeKind.packed =>
                    abiEncodePackedValues? widths tys argValues
                | _ => abiEncodeValues? tys argValues
              match encoded? with
              | some bytes =>
                  match selector? with
                  | some selector =>
                      pure
                        ( Value.bytes
                            (wordToBytesBE selectorBytes selector ++ bytes)
                        , runtime' )
                  | none => pure (Value.bytes bytes, runtime')
              | none => throw <| SolidityFailure.revert RevertData.typeMismatch
          | Expr.abiDecode tys cleanups expr => do
              let (value, runtime') ←
                Expr.evalFuel fuel context runtime expr
              match value.asBytes? with
              | some bytes =>
                  match abiDecodeValuesExcept? tys bytes with
                  | Except.ok decoded =>
                      if AbiCleanups.acceptOrUnspecified cleanups decoded then
                        match decoded with
                        | [value] => pure (value, runtime')
                        | values =>
                            pure (Value.tuple values, runtime')
                      else
                        throw <| SolidityFailure.revert RevertData.empty
                  | Except.error revertData =>
                      throw <| SolidityFailure.revert revertData
              | none => throw <| SolidityFailure.revert RevertData.typeMismatch
          | Expr.lowLevelCall kind targetExpr calldataExpr valueExpr
              gasExpr? gasFirst => do
              -- solc (v0.8.35) evaluates a low-level call as: the base/target
              -- expression, then the FunctionCallOptions in their WRITTEN order
              -- (gas/value ordered by `gasFirst`), then the calldata argument.
              -- This top-level order is FIXED, so evaluate the components
              -- sequentially in that order; each component's own inner children
              -- use their construct-intrinsic order.
              -- The old code evaluated calldata before the options and
              -- ignored `gasFirst` entirely (gap EO1).
              let (targetValue, runtimeTarget) ←
                Expr.evalFuel fuel context runtime targetExpr
              let target ← targetValue.expectWord
              let (value, gas?, runtimeOpts) ←
                (match gasExpr? with
                | none => do
                    let (valueValue, runtimeValue) ←
                      Expr.evalFuel fuel context
                        runtimeTarget valueExpr
                    let value ← valueValue.expectWord
                    pure (value, none, runtimeValue)
                | some gasExpr => do
                    if gasFirst then
                      let (gasValue, runtimeGas) ←
                        Expr.evalFuel fuel context
                          runtimeTarget gasExpr
                      let gas ← gasValue.expectWord
                      let (valueValue, runtimeValue) ←
                        Expr.evalFuel fuel context
                          runtimeGas valueExpr
                      let value ← valueValue.expectWord
                      pure (value, some gas, runtimeValue)
                    else
                      let (valueValue, runtimeValue) ←
                        Expr.evalFuel fuel context
                          runtimeTarget valueExpr
                      let value ← valueValue.expectWord
                      let (gasValue, runtimeGas) ←
                        Expr.evalFuel fuel context
                          runtimeValue gasExpr
                      let gas ← gasValue.expectWord
                      pure (value, some gas, runtimeGas) :
                  SolI (Word × Option Word × Runtime))
              let (calldataValue, runtime') ←
                Expr.evalFuel fuel context
                  runtimeOpts calldataExpr
              let cdata ←
                match calldataValue.asBytes? with
                | some bytes => pure bytes
                | none => throw <| SolidityFailure.revert RevertData.typeMismatch
              -- #186: `address(this).call(data)` on the executing contract
              -- self-dispatches (closed-world) when the hook is installed;
              -- `selfDispatchCall` is inert (falls back to the open-world emit)
              -- for every non-self target and every open-world entry. ONLY plain
              -- CALL self-dispatches here: a low-level self-STATICCALL would need
              -- static-context write enforcement (a mutating selector must fail,
              -- not mutate-and-succeed) and a self-DELEGATECALL preserves the
              -- OUTER `msg.sender`/`msg.value` — both stay fail-closed
              -- (open-world emit) rather than dispatch with wrong frame
              -- semantics. During construction (`extcodesize(this) == 0`) a
              -- low-level self-call hits a code-less account, so keep the
              -- open-world emit there too.
              let (result, adoptedState) ←
                (if context.construction ||
                    !(kind ==
                      SolidCore.Solidity.Shared.Call.ExternalCallKind.call) then
                  emitLowLevelCall context runtime'.state
                    kind target cdata value gas?
                else
                  selfDispatchCall context runtime'.state
                    kind target cdata value gas?)
              pure
                ( Value.tuple
                    [ Value.word (boolWord result.success)
                    , Value.bytes result.output ]
                , { runtime' with
                    state := adoptedState }.recordExternalInteraction
                    (ExternalInteraction.lowLevelCall result) )
          | Expr.contractCreate contractName constructorArgsExpr valueExpr
              saltExpr? valueBeforeSalt => do
              -- solc (v0.8.35) evaluates `new C{opts}(args)` as: the
              -- FunctionCallOptions in their WRITTEN order (value/salt ordered by
              -- `valueBeforeSalt`), THEN the constructor arguments LAST.  This
              -- top-level order is FIXED; each component's own inner children
              -- use their construct-intrinsic order.
              -- The old code evaluated `[args, value, salt]`
              -- right-to-left (salt→value→args), which ignored the option source
              -- order (gap DIV-CREATE-2).
              let (value, salt?, runtimeOpts) ←
                (match saltExpr? with
                | none => do
                    let (valueValue, runtimeValue) ←
                      Expr.evalFuel fuel context
                        runtime valueExpr
                    let value ← valueValue.expectWord
                    pure (value, none, runtimeValue)
                | some saltExpr => do
                    if valueBeforeSalt then
                      let (valueValue, runtimeValue) ←
                        Expr.evalFuel fuel context
                          runtime valueExpr
                      let value ← valueValue.expectWord
                      let (saltValue, runtimeSalt) ←
                        Expr.evalFuel fuel context
                          runtimeValue saltExpr
                      let salt ← saltValue.expectWord
                      pure (value, some salt, runtimeSalt)
                    else
                      let (saltValue, runtimeSalt) ←
                        Expr.evalFuel fuel context
                          runtime saltExpr
                      let salt ← saltValue.expectWord
                      let (valueValue, runtimeValue) ←
                        Expr.evalFuel fuel context
                          runtimeSalt valueExpr
                      let value ← valueValue.expectWord
                      pure (value, some salt, runtimeValue) :
                  SolI (Word × Option Word × Runtime))
              let (argsValue, runtime') ←
                Expr.evalFuel fuel context
                  runtimeOpts constructorArgsExpr
              let constructorArgs ←
                match argsValue.asBytes? with
                | some bytes => pure bytes
                | none => throw <| SolidityFailure.revert RevertData.typeMismatch
              let (result, adoptedState) ←
                emitContractCreation context runtime'.state
                  contractName constructorArgs value salt?
              if result.success then
                pure
                  ( Value.word result.address
                  , { runtime' with
                      state := adoptedState }.recordExternalInteraction
                      (ExternalInteraction.contractCreation result) )
              else
                throw <| SolidityFailure.revert (RevertData.fromRawBytes result.output)
          | Expr.newBytes lengthExpr => do
              let (lengthValue, runtime') ←
                Expr.evalFuel fuel context runtime
                  lengthExpr
              let length ← lengthValue.expectWord
              let size ← context.checkMemoryAllocation length
              pure (Value.bytes (List.replicate size 0), runtime')
          | Expr.newDynamicArray elementTy lengthExpr => do
              let (lengthValue, runtime') ←
                Expr.evalFuel fuel context runtime
                  lengthExpr
              let length ← lengthValue.expectWord
              let size ← context.checkMemoryAllocation length
              pure
                ( Value.dynamicArray
                    (List.replicate size elementTy.defaultValue)
                , runtime' )
          | Expr.enumFromUInt maxValue expr => do
              let (value, runtime') ←
                Expr.evalFuel fuel context runtime expr
              let coerced ← enumFromUIntValue maxValue value
              pure (coerced, runtime')
          | Expr.ternary cond thenExpr elseExpr => do
              let (condValue, runtime') ←
                Expr.evalFuel fuel context runtime cond
              let condWord ← condValue.expectWord
              if wordTruthy condWord then
                Expr.evalFuel fuel context runtime'
                  thenExpr
              else
                Expr.evalFuel fuel context runtime'
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
                  match runtime.lookupStorageBase? name with
                  | some base => do
                      let value ←
                        runtime.loadStorageBasePath context base []
                      let len ← lengthValue value
                      pure (len, runtime)
                  | none =>
                      let (value, runtime') ←
                        Expr.evalFuel fuel context
                          runtime expr
                      let len ← lengthValue value
                      pure (len, runtime')
              | _ =>
                  if expr.hasStorageRoot || expr.hasStorageRefRoot runtime then
                    let (target, runtime') ←
                      Expr.resolveLValueFuel fuel
                        context runtime expr
                    match target.asStoragePath? with
                    | some (base, indexes) => do
                        let value ←
                          runtime'.loadStorageBasePath context base indexes
                        let len ← lengthValue value
                        pure (len, runtime')
                    | none => throw <| SolidityFailure.revert RevertData.typeMismatch
                  else
                    let (value, runtime') ←
                      Expr.evalFuel fuel context runtime
                        expr
                    let len ← lengthValue value
                    pure (len, runtime')
          | Expr.index base idx => do
              if base.hasStorageRoot then
                let (baseTarget, runtime') ←
                  Expr.resolveLValueFuel fuel
                    context runtime base
                match baseTarget.asStoragePath? with
                | some (base, indexes) =>
                    let (indexValue, runtime'') ←
                      Expr.evalFuel fuel context
                        runtime' idx
                    let value ←
                      runtime''.loadStorageBasePath context base
                        (indexes ++ [indexValue])
                    pure (value, runtime'')
                | none => throw <| SolidityFailure.revert RevertData.typeMismatch
              else if base.hasStorageRefRoot runtime then
                let (resolved, runtime') ←
                  Expr.resolveLValueFuel fuel context
                    runtime (Expr.index base idx)
                let value ← resolved.read context runtime'
                pure (value, runtime')
              else
                match base with
                | Expr.var name =>
                    match runtime.lookupStorageBase? name with
                    | some base =>
                        let (indexValue, runtime') ←
                          Expr.evalFuel fuel context
                            runtime idx
                        let value ←
                          runtime'.loadStorageBasePath context base
                            [indexValue]
                        pure (value, runtime')
                    | none =>
                        let (values, runtime') ←
                          Expr.evalListFuel fuel
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
                      Expr.evalListFuel fuel context
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
                    Expr.evalFuel fuel context
                      runtime base
                  readSlice baseValue none none runtime'
              | some startExpr, none => do
                  let (values, runtime') ←
                    Expr.evalListFuel fuel context
                      runtime [base, startExpr]
                  match values with
                  | [baseValue, startValue] =>
                      readSlice baseValue (some startValue) none runtime'
                  | _ => throw <| SolidityFailure.revert RevertData.typeMismatch
              | none, some stopExpr => do
                  let (values, runtime') ←
                    Expr.evalListFuel fuel context
                      runtime [base, stopExpr]
                  match values with
                  | [baseValue, stopValue] =>
                      readSlice baseValue none (some stopValue) runtime'
                  | _ => throw <| SolidityFailure.revert RevertData.typeMismatch
              | some startExpr, some stopExpr => do
                  let (values, runtime') ←
                    Expr.evalListFuel fuel context
                      runtime [base, startExpr, stopExpr]
                  match values with
                  | [baseValue, startValue, stopValue] =>
                      readSlice baseValue (some startValue) (some stopValue)
                        runtime'
                  | _ => throw <| SolidityFailure.revert RevertData.typeMismatch

def Expr.evalListFuel (fuel : Nat)
    (context : Context) : Runtime -> List Expr ->
    SolI (List Value × Runtime)
  | runtime, exprs =>
      match fuel with
      | 0 => throw <| SolidityFailure.revert RevertData.typeMismatch
      | fuel + 1 =>
          match exprs with
          | [] => pure ([], runtime)
          | expr :: rest => do
              -- Intrinsic order: sibling lists (call arguments, tuple/array
              -- components, abi.encode args, [base, key] pairs) evaluate LEFT
              -- to RIGHT (solc ExpressionCompiler.cpp:710-711,682-684,1031,
              -- 400,388).
              let (value, runtime') ←
                Expr.evalFuel fuel context runtime
                  expr
              let (values, runtime'') ←
                Expr.evalListFuel fuel context
                  runtime' rest
              pure (value :: values, runtime'')

def Expr.memoryRefOrValueFuel
    (fuel : Nat) (context : Context) :
    Runtime -> Expr -> SolI (Option Nat × Option Value × Runtime)
  | runtime, expr =>
      match fuel with
      | 0 => throw <| SolidityFailure.revert RevertData.typeMismatch
      | fuel + 1 =>
          match expr with
          | Expr.var name =>
              match runtime.lookupMemoryRef? name with
              | some id => pure (some id, none, runtime)
              | none => do
                  -- Value-type / storage-alias var: evaluate normally (a value
                  -- copy or storage read), so this stays TOTAL (never `none,
                  -- none`) and callers never need a re-evaluating fallback.
                  let (value, runtime') ←
                    Expr.evalFuel fuel context runtime expr
                  pure (none, some value, runtime')
          | Expr.ternary cond thenExpr elseExpr => do
              -- M1: a memory reference-type ternary aliases the chosen branch
              -- (solc pointer-copies it). Evaluate the condition, then recurse
              -- on the taken branch so a memory-ref branch flows as its ref id.
              let (condValue, runtime') ←
                Expr.evalFuel fuel context runtime cond
              let condWord ← condValue.expectWord
              Expr.memoryRefOrValueFuel fuel context
                runtime' (if wordTruthy condWord then thenExpr else elseExpr)
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
              -- Intrinsic order (solc IndexAccess visitor): base BEFORE key.
              let (baseValue, runtime') ←
                Expr.evalFuel fuel context
                  runtime base
              let (indexValue, runtime'') ←
                Expr.evalFuel fuel context
                  runtime' idx
              finish baseValue indexValue runtime''
          | _ => do
              -- Any other RHS shape: evaluate normally. Keeping this arm TOTAL
              -- (returning the evaluated value rather than `none, none`) lets
              -- the ref-preserving wrapper avoid a double-evaluation fallback.
              let (value, runtime') ←
                Expr.evalFuel fuel context runtime expr
              pure (none, some value, runtime')

def Expr.resolveLValueFuel
    (fuel : Nat) (context : Context) :
    Runtime -> Expr -> SolI (ResolvedLValue × Runtime)
  | runtime, expr =>
      match fuel with
      | 0 => throw <| SolidityFailure.revert RevertData.typeMismatch
      | fuel + 1 =>
          match expr with
          | Expr.var name =>
              match runtime.lookupStorageBase? name with
              | some (StorageBase.field target) =>
                  pure (ResolvedLValue.storageField target, runtime)
              | some (StorageBase.slot slot layout) =>
                  pure (ResolvedLValue.storageSlotPath slot layout [],
                    runtime)
              | none =>
                  match runtime.lookupLocal? name with
                  | some _ => pure (ResolvedLValue.local name, runtime)
                  | none => throw <| SolidityFailure.revert RevertData.typeMismatch
          | Expr.immutable name =>
              pure (ResolvedLValue.immutable name, runtime)
          | Expr.storage name =>
              pure (ResolvedLValue.storageField name, runtime)
          | Expr.storageIdent name =>
              pure (ResolvedLValue.storageField name, runtime)
          | Expr.storageIndex name idx => do
              let (indexValue, runtime') ←
                Expr.evalFuel fuel context runtime idx
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
                | ResolvedLValue.storageSlotPath slot layout indexes =>
                    pure
                      (ResolvedLValue.storageSlotPath slot layout
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
              -- Intrinsic order (solc IndexAccess visitor): base BEFORE key.
              let (baseTarget, runtime') ←
                Expr.resolveLValueFuel fuel
                  context runtime base
              let (indexValue, runtime'') ←
                Expr.evalFuel fuel context
                  runtime' idx
              finish baseTarget indexValue runtime''
          | _ => throw <| SolidityFailure.revert RevertData.typeMismatch

end

def Expr.eval (context : Context) (runtime : Runtime)
    (expr : Expr) : SolI (Value × Runtime) :=
  Expr.evalFuel (Expr.orderFuel expr + 1)
    context runtime expr

def Expr.evalList (context : Context) (runtime : Runtime)
    (exprs : List Expr) : SolI (List Value × Runtime) :=
  Expr.evalListFuel (Expr.listEvalFuel exprs)
    context runtime exprs

def Expr.memoryRefOrValue (context : Context) (runtime : Runtime)
    (expr : Expr) : SolI (Option Nat × Option Value × Runtime) :=
  -- Budget `orderFuel expr + 2` (one more than the plain `eval`
  -- entry, `orderFuel expr + 1`). The non-ref fallback arms of
  -- `memoryRefOrValueFuel` re-evaluate the FULL `expr` inline via
  -- `evalFuel` using the already-decremented `fuel`; a correct
  -- from-scratch eval needs `orderFuel expr + 1`, so after the one-step decrement
  -- inside the recursor the entry budget must be `orderFuel expr + 2`. With only
  -- `+ 1` a multi-child RHS at its exact fuel bound (e.g. a calldata slice
  -- `input[i:j]` copied into a `memory` local) exhausts fuel and spuriously
  -- reverts `Panic(0)` (`RevertData.typeMismatch`).
  Expr.memoryRefOrValueFuel (Expr.orderFuel expr + 2)
    context runtime expr

/-- Reference-preserving expression evaluation for memory-ref-valued assignment
    RHSs (M1/M2/M3). When `expr` denotes a memory reference type (a memory local,
    a memory aggregate element/field, or a ternary over such), it yields the
    `Value.memoryRef` *pointer* rather than the dereferenced object, so the store
    paths (`assignLocal?`, `memoryStoreValue`, `storeMemory?`) ALIAS it (they
    already pass a bare `memoryRef` through unchanged) instead of allocating a
    fresh copy. Everything else evaluates exactly as ordinary eval — value types
    still copy, storage/calldata reads still deep-copy — because
    `memoryRefOrValue` only produces a ref id for genuine memory pointers. -/
def Expr.evalMemoryRefPreserving (context : Context) (runtime : Runtime)
    (expr : Expr) : SolI (Value × Runtime) := do
  let (idOpt, valueOpt, runtime') ←
    Expr.memoryRefOrValue context runtime expr
  match idOpt, valueOpt with
  | some id, _ => pure (Value.memoryRef id, runtime')
  | none, some value => pure (value, runtime')
  | none, none =>
      -- `memoryRefOrValue` is total (never `none, none`); this arm is a
      -- defensive fallback and does not re-run side effects in practice.
      Expr.eval context runtime' expr

def Expr.resolveLValue (context : Context) (runtime : Runtime)
    (expr : Expr) : SolI (ResolvedLValue × Runtime) :=
  Expr.resolveLValueFuel (Expr.orderFuel expr + 1)
    context runtime expr

/-- Evaluate the components of a tuple-assignment RHS reference-preservingly
    (M2). Each component paired with a memory-ref target flows as its
    `Value.memoryRef` pointer so tuple destructuring aliases (matching solc's
    per-component pointer store); components paired with value/storage targets
    (or holes) evaluate normally. All components are evaluated BEFORE any write
    (the caller writes afterwards), so `(a, b) = (b, a)` performs a genuine
    pointer swap. Components evaluate LEFT to RIGHT (intrinsic order). -/
def Expr.evalTupleComponentsRefPreservingFuel
    (fuel : Nat) (context : Context) :
    Runtime -> List (Option LValue) -> List Expr ->
    SolI (List Value × Runtime)
  | runtime, targets, components =>
    match fuel with
    | 0 => throw <| SolidityFailure.revert RevertData.typeMismatch
    | fuel + 1 =>
      match targets, components with
      | [], [] => pure ([], runtime)
      | target? :: targetsRest, comp :: compsRest =>
          let evalOne (rt : Runtime) : SolI (Value × Runtime) :=
            match target? with
            | some target =>
                if target.wantsMemoryRefRhs rt then
                  Expr.evalMemoryRefPreserving context rt
                    comp
                else if target.wantsStorageRefRhs rt then
                  -- Storage-pointer tuple target: yield the storage-ref POINTER
                  -- (the same value the scalar `p = q` re-point captures) so the
                  -- write RE-POINTS the local rather than deep-copying the
                  -- pointed-to contents — this is what makes `(p, q) = (q, p)`
                  -- swap the pointers. A non-bare-var RHS shape falls back to
                  -- ordinary (dereferencing) eval, unchanged.
                  match comp with
                  | Expr.var source =>
                      match rt.lookupStorageBase? source with
                      | some base => pure (base.toRefValue, rt)
                      | none => Expr.eval context rt comp
                  | Expr.storageRead _ source [] =>
                      -- A whole bare STATE-VARIABLE RHS (`y`) paired with a
                      -- storage-pointer target RE-POINTS the local to that state
                      -- variable's storage lvalue — the same pointer the scalar
                      -- `p = y` re-point captures (`Stmt.storageAliasAssign` →
                      -- `Value.storageRef`) — instead of DEREFERENCING y's
                      -- struct CONTENTS into a value the write then deep-copies
                      -- THROUGH the pointer. The storage value-use normalizer
                      -- flips this whole-variable read `ref` → `load` (tuple-RHS
                      -- components are value-use), so match ANY mode with empty
                      -- indexes; since the target is a storage pointer, solc's
                      -- typing guarantees the component is a storage reference.
                      -- This makes `(p, v) = (y, 7)` rebind p to y rather than
                      -- copying y's contents into x.
                      pure (Value.storageRef source, rt)
                  | _ => Expr.eval context rt comp
                else
                  Expr.eval context rt comp
            | none => Expr.eval context rt comp
          -- Intrinsic order (solc ExpressionCompiler.cpp:400): tuple
          -- components evaluate LEFT to RIGHT.
          do
            let (value, runtime') ← evalOne runtime
            let (values, runtime'') ←
              Expr.evalTupleComponentsRefPreservingFuel fuel context
                runtime' targetsRest compsRest
            pure (value :: values, runtime'')
      | _, _ => throw <| SolidityFailure.revert RevertData.typeMismatch

def Expr.evalTupleComponentsRefPreserving (context : Context) (runtime : Runtime)
    (targets : List (Option LValue)) (components : List Expr) :
    SolI (List Value × Runtime) :=
  Expr.evalTupleComponentsRefPreservingFuel (Expr.listEvalFuel components)
    context runtime targets components

def Expr.evalBinary (context : Context) (runtime : Runtime)
    (op : BinaryOp) (lhs rhs : Expr) :
    SolI (Value × Runtime) :=
  Expr.eval context runtime (Expr.binary op lhs rhs)

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
    (Expr.eval context runtime expr)

def Expr.evalListWithRuntimeByContext
    (context : Context) (runtime : Runtime) (exprs : List Expr) :
    Except RevertData (List Value × Runtime) :=
  SolI.foldExpr (Expr.listEvalFuel exprs + 1) context
    (Expr.evalList context runtime exprs)

inductive TernaryBranch where
  | thenBranch
  | elseBranch
  deriving Repr, BEq

def Expr.memoryRefOrValueWithRuntimeByContext
    (expr : Expr) (context : Context) (runtime : Runtime) :
    Except RevertData (Option Nat × Option Value × Runtime) :=
  SolI.foldExpr (Expr.orderFuel expr + 1) context
    (Expr.memoryRefOrValue
      context runtime expr)

def Expr.resolveLValueWithRuntimeByContext
    (expr : Expr) (context : Context) (runtime : Runtime) :
    Except RevertData (ResolvedLValue × Runtime) :=
  SolI.foldExpr (Expr.orderFuel expr + 1) context
    (Expr.resolveLValue
      context runtime expr)

def Expr.evalReturnValue (context : Context) (runtime : Runtime)
    (expr : Expr) : SolI (Value × Runtime) :=
  match expr with
  | Expr.var name =>
      match runtime.lookupMemoryRef? name with
      | some id => pure (Value.memoryRef id, runtime)
      | none => Expr.eval context runtime expr
  | _ => Expr.eval context runtime expr

def Expr.evalReturnListFuel
    (fuel : Nat) (context : Context) :
    Runtime -> List Expr -> SolI (List Value × Runtime)
  | runtime, exprs =>
      match fuel with
      | 0 => throw <| SolidityFailure.revert RevertData.typeMismatch
      | fuel + 1 =>
          match exprs with
          | [] => pure ([], runtime)
          | expr :: rest => do
              -- Intrinsic order: return-tuple components evaluate LEFT to
              -- RIGHT (solc TupleExpression visitor).
              let (value, runtime') ←
                Expr.evalReturnValue context
                  runtime expr
              let (values, runtime'') ←
                Expr.evalReturnListFuel fuel
                  context runtime' rest
              pure (value :: values, runtime'')

def Expr.evalReturnList (context : Context) (runtime : Runtime)
    (exprs : List Expr) : SolI (List Value × Runtime) :=
  Expr.evalReturnListFuel (Expr.listEvalFuel exprs)
    context runtime exprs

def Expr.evalReturnListWithRuntimeByContext
    (context : Context) (runtime : Runtime) (exprs : List Expr) :
    Except RevertData (List Value × Runtime) :=
  SolI.foldExpr (Expr.listEvalFuel exprs + 1) context
    (Expr.evalReturnList
      context runtime exprs)

/-- Reference-preserving argument evaluation for the `internalCall` arm
    (function-boundary refactor, reference-signature extension). Unlike ordinary
    `Expr.var` evaluation — which *dereferences* a variable bound to a storage
    pointer (loading the pointed-to storage value) or a memory pointer (loading
    the memory object) — this yields the pointer VALUE itself when the argument
    is a variable holding a storage/memory reference. That is how reference-typed
    parameters flow across an internal-function boundary: `T memory` passes the
    memory pointer (callee mutations alias back), `T storage` passes the storage
    pointer as a plain runtime argument (solc's model). Non-reference arguments
    (the elaboration's `_ic_arg_*` value temps, and any expression not bound to a
    reference) fall through to ordinary evaluation, so value calls are
    unaffected. -/
def Expr.evalRefArg (context : Context) (runtime : Runtime)
    (expr : Expr) : SolI (Value × Runtime) :=
  match expr with
  | Expr.var name =>
      match runtime.lookupStorageBase? name with
      | some base =>
          pure (base.toRefValue, runtime)
      | none =>
          match runtime.lookupMemoryRef? name with
          | some id => pure (Value.memoryRef id, runtime)
          | none => Expr.eval context runtime expr
  | _ => Expr.eval context runtime expr

def Expr.evalRefArgListFuel
    (fuel : Nat) (context : Context) :
    Runtime -> List Expr -> SolI (List Value × Runtime)
  | runtime, exprs =>
      match fuel with
      | 0 => throw <| SolidityFailure.revert RevertData.typeMismatch
      | fuel + 1 =>
          match exprs with
          | [] => pure ([], runtime)
          | expr :: rest => do
              -- Intrinsic order: internal-call arguments evaluate LEFT to
              -- RIGHT (solc ExpressionCompiler.cpp:710-711).
              let (value, runtime') ←
                Expr.evalRefArg context runtime expr
              let (values, runtime'') ←
                Expr.evalRefArgListFuel fuel
                  context runtime' rest
              pure (value :: values, runtime'')

def Expr.evalRefArgList (context : Context) (runtime : Runtime)
    (exprs : List Expr) : SolI (List Value × Runtime) :=
  Expr.evalRefArgListFuel (Expr.listEvalFuel exprs)
    context runtime exprs

def LValue.resolveWithRuntime (target : LValue) (context : Context)
    (runtime : Runtime) : SolI (ResolvedLValue × Runtime) :=
  Expr.resolveLValue context
    runtime target.toExpr

/-- PHASE 1 of a flat tuple write: resolve every present LHS component's lvalue
    reference LEFT-TO-RIGHT into a `ResolvedLValue` "place", WITHOUT performing
    any store. Index/key/member sub-expressions are evaluated here, so every
    component observes PRE-STORE state, and a storage/memory index is FROZEN
    into the resolved place (`ResolvedLValue.storageIndex`/`storagePath` capture
    the concrete index value, `valueIndex` the concrete `Word`). Holes
    contribute no place. Mirrors solc visiting the LHS TupleExpression to
    compute every component's lvalue ref before any store
    (`ExpressionCompiler.cpp:396-415`). -/
def LValues.resolveTupleWithRuntime (context : Context) :
    Runtime -> List (Option LValue) -> List Value ->
    SolI (List (ResolvedLValue × Value) × Runtime)
  | runtime, [], [] => pure ([], runtime)
  | runtime, some target :: targets, value :: values => do
      -- A storage-pointer local target paired with a storage-ref POINTER value
      -- (produced by `evalTupleComponentsRefPreserving`) RE-POINTS the local:
      -- resolve it to the `local` place so the write goes through
      -- `assignLocal?`/`coerceLike?` (a storage-ref template adopts the incoming
      -- ref) instead of the write-through `storageField` place, which would
      -- deep-copy the pointed-to contents. Mirrors how a memory-ref local target
      -- already resolves to `local`.
      let (resolved, runtime') ←
        match target, value with
        | LValue.var name, Value.storageRef _
        | LValue.var name, Value.storageSlotRef _ _ =>
            if (runtime.lookupStorageBase? name).isSome then
              pure (ResolvedLValue.local name, runtime)
            else
              target.resolveWithRuntime context runtime
        | _, _ => target.resolveWithRuntime context runtime
      let (rest, runtime'') ←
        LValues.resolveTupleWithRuntime context runtime' targets values
      pure ((resolved, value) :: rest, runtime'')
  | runtime, none :: targets, _ :: values =>
      LValues.resolveTupleWithRuntime context runtime targets values
  | _, _, _ => throw (SolidityFailure.revert RevertData.typeMismatch)

/-- PHASE 2: store the already-resolved places RIGHT-TO-LEFT (rightmost first,
    leftmost last). Recursing into the tail before writing the head realises the
    right-to-left order, matching solc's `TupleObject::storeValue` ("We will
    assign from right to left to optimize stack layout", `LValue.cpp:589-615`).
    When two components alias the same place the LEFTMOST wins because it is
    stored last. -/
def LValues.writeResolvedRightToLeft (context : Context) :
    Runtime -> List (ResolvedLValue × Value) -> SolI Runtime
  | runtime, [] => pure runtime
  | runtime, (resolved, value) :: rest => do
      let runtime' ← LValues.writeResolvedRightToLeft context runtime rest
      resolved.write context runtime' value

/-- Two-phase flat tuple write matching solc (#132 TUPLE-WRITE-ORDER): resolve
    ALL LHS lvalue references left-to-right (pre-store state, indices frozen),
    then store the resolved places right-to-left. -/
def LValues.writeTupleWithRuntime (context : Context) (runtime : Runtime)
    (targets : List (Option LValue)) (values : List Value) : SolI Runtime := do
  let (resolved, runtime') ←
    LValues.resolveTupleWithRuntime context runtime targets values
  LValues.writeResolvedRightToLeft context runtime' resolved

mutual

/-- PHASE 1 for NESTED tuple targets: solc FLATTENS a nested tuple LHS, so we
    resolve every leaf's lvalue place LEFT-TO-RIGHT (depth-first) into a single
    flat list, without storing. Same pre-store/frozen-index guarantees as the
    flat case. -/
def TupleTargets.resolveNested (context : Context) :
    Runtime -> List TupleTarget -> List Value ->
    SolI (List (ResolvedLValue × Value) × Runtime)
  | runtime, [], [] => pure ([], runtime)
  | runtime, target :: targets, value :: values => do
      let (head, runtime') ←
        TupleTarget.resolveNested context runtime target value
      let (rest, runtime'') ←
        TupleTargets.resolveNested context runtime' targets values
      pure (head ++ rest, runtime'')
  | _, _, _ => throw (SolidityFailure.revert RevertData.typeMismatch)

def TupleTarget.resolveNested (context : Context) (runtime : Runtime) :
    TupleTarget -> Value -> SolI (List (ResolvedLValue × Value) × Runtime)
  | TupleTarget.hole, _ => pure ([], runtime)
  | TupleTarget.leaf target, value => do
      let (resolved, runtime') ← target.resolveWithRuntime context runtime
      pure ([(resolved, value)], runtime')
  | TupleTarget.nested targets, Value.tuple values =>
      TupleTargets.resolveNested context runtime targets values
  | TupleTarget.nested _, _ =>
      throw (SolidityFailure.revert RevertData.typeMismatch)

end

/-- Write a (possibly nested) tuple-target tree against the matching RHS values.
    The RHS was fully evaluated before any write (so `(a, b) = (b, a)` swaps and
    a hole's value is already produced). Matching solc, all leaves are resolved
    left-to-right (flattened), then stored right-to-left (#132). -/
def TupleTargets.writeNested (context : Context) (runtime : Runtime)
    (targets : List TupleTarget) (values : List Value) : SolI Runtime := do
  let (resolved, runtime') ←
    TupleTargets.resolveNested context runtime targets values
  LValues.writeResolvedRightToLeft context runtime' resolved

/-- Reserved storage-alias target for a not-yet-assigned `T storage` named
    return (reference-signature extension, stage A). It names no real storage
    field, so reading through it fails — unreachable in accepted programs (solc's
    frontend enforces definite assignment of storage-pointer returns; see
    `docs/refs-completion-solc-research.md` §1). Shared with elaboration
    (`Interface.lean` aliases this constant). -/
def uninitializedStorageReturnTarget : String :=
  "__solidcore_uninitialized_storage_return"

structure BindingDecl where
  name : String
  ty : Ty
  /-- `true` for a `T storage` reference parameter/return: `defaultBinding`
      binds the name to a storage POINTER (initially the reserved
      `uninitializedStorageReturnTarget`) instead of `ty.defaultValue`, so a
      callee body's re-points (`storageAliasAssign*` — which require an existing
      storage-ref binding and assign through all scopes into the frame) and the
      reference-preserving return collection find a storage reference. Defaulted
      `false` so every existing construction site is unchanged. -/
  isStorageRef : Bool := false
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
  /-- Nested tuple-assignment LHS (`((a, b), c) = …`): the RHS is evaluated once
      to a (possibly nested) `Value.tuple`, then destructured against the target
      tree in lockstep, left-to-right (`docs/DECISIONS.md` 2026-07-08 G13). -/
  | assignTupleNested : List TupleTarget -> Expr -> Stmt
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
  /-- Call through an internal function POINTER (boundary-completion arc,
      stage C): `targets`, the function-pointer expression (evaluated first,
      then the arguments — matching via-IR's sequencing), and the argument
      expressions. The pointer's dispatch ID is resolved against the
      `FunctionTable` at call time; a miss — including the uninitialized ID 0 —
      panics `0x51`, exactly solc's per-arity dispatch default
      (`docs/refs-completion-solc-research.md` §2). -/
  | internalCallPtr : List String -> Expr -> List Expr -> Stmt
  | ifElse : Expr -> Stmt -> Stmt -> Stmt
  | switch : Expr -> List (Word × Stmt) -> Option Stmt -> Stmt
  | whileLoop : Expr -> Stmt -> Stmt
  | doWhile : Stmt -> Expr -> Stmt
  | forLoop : Stmt -> Expr -> Stmt -> Stmt -> Stmt
  | tryExternalCall :
      LowLevelCallKind -> Expr -> Expr -> Expr -> Option Expr -> Bool ->
      Bool -> List BindingDecl -> List AbiCleanup -> Stmt ->
      List TryCatchClause -> Stmt
  -- `tryContractCreate contractName args value salt? valueBeforeSalt …`: the
  -- `Bool` records value-before-salt source order of the options (DIV-CREATE-1/2).
  | tryContractCreate :
      String -> Expr -> Expr -> Option Expr -> Bool -> List BindingDecl -> Stmt ->
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

/-! ## Storage value-use normalization (R3 #192 endgame)

The single, fully-recursive, position-aware pass that replaces the ~40
hand-placed `materializeStorageValueUseCore` call sites in the lowering.

THE BUG CLASS: a bare state `bytes`/`string`/dynamic-array variable lowers to
`Expr.storageRead .header name []`, whose eval is the HEADER word (the
`.length` convention) — useless to any consumer of the CONTENTS. solc
implicitly copies storage to memory at every value-use boundary
(`abi.encode*`, `keccak256`/`sha256`/`ripemd160`/`erc7201`, event args,
custom-error args, mapping-key derivation, require/revert reasons, tuple
RHSs, `abi.decode` data, `bytes.concat`, array literals, …). Fixing each
boundary individually (commits #4–#10) left every FUTURE boundary a
pre-loaded copy of the same bug, and the shallow materializer missed storage
reads NESTED inside array literals / tuples / concats / struct-constructor
args.

THE FIX: one total pass over the whole core `Expr`/`Stmt` syntax that threads
the POSITION (value-use vs pointer-use) downward explicitly (Reader-by-hand;
no monad — the position parameter keeps the recursion structurally obvious
and the definitions kernel-friendly for the witness `#guard`s):

- `valueUse`: the surrounding consumer needs the CONTENTS. A bare header
  read (`.header`) is flipped to the materializing read (`.load`) — a
  ONE-LINE mode flip on the unified `Expr.storageRead`.
- `pointerUse`: the surrounding consumer wants the reference/header form
  (`.length`, lvalue targets, slot encodings, storage-pointer arguments).
  Bare header reads pass through untouched. This is the safe, byte-identical
  default for every scalar/unknown child position.

Scalar reads are unaffected by design: `.load name []` on a scalar-layout
field routes through the same whole-field reader as `.header` (see the
scalar-coincidence arm in `Expr.evalFuel`), so flipping a scalar's mode is
semantically a no-op — including for transient and packed scalars.
-/

/-- The position a core sub-expression occupies relative to its consumer:
    `valueUse` when the consumer reads the CONTENTS of the value (so a bare
    storage-header read must materialize), `pointerUse` when the consumer
    wants the reference/header form itself. -/
inductive StoragePosition where
  | valueUse : StoragePosition
  | pointerUse : StoragePosition
  deriving Repr

mutual

/-- Normalize storage value-use reads in `expr`, which itself sits at
    position `pos`. Total over every `Expr` constructor; each child position
    is classified explicitly (see the module doc comment). -/
def Expr.normalizeStorageValueUses (pos : StoragePosition) : Expr -> Expr
  -- ── The storage-read family ────────────────────────────────────────────
  | Expr.storageRead mode name indexes =>
      -- THE mode flip: a bare state-variable REFERENCE (`ref`) in value
      -- position materializes. `header` is a DELIBERATE header-word read
      -- (`.length`, synthesized push-index arithmetic) and never flips;
      -- `contents`/`element`/`load` already materialize and pass through.
      -- Index children are VALUE-USE regardless of `pos`: a mapping key's
      -- CONTENTS feed the value-slot hash (`mappingStorageSlotForKey`).
      let mode :=
        match pos, mode with
        | StoragePosition.valueUse, StorageReadMode.ref =>
            StorageReadMode.load
        | _, mode => mode
      Expr.storageRead mode name
        (Expr.normalizeStorageValueUsesList StoragePosition.valueUse indexes)
  | Expr.storageSlot name => Expr.storageSlot name
  | Expr.storagePathSlot name indexes =>
      -- Slot-only forms: the RESULT is a pointer encoding (never flipped),
      -- but the path keys are value-use exactly like the value forms'.
      Expr.storagePathSlot name
        (Expr.normalizeStorageValueUsesList StoragePosition.valueUse indexes)
  | Expr.storageRefSlot name indexes =>
      Expr.storageRefSlot name
        (Expr.normalizeStorageValueUsesList StoragePosition.valueUse indexes)
  -- ── Leaves ─────────────────────────────────────────────────────────────
  | Expr.word value => Expr.word value
  | Expr.intWord value => Expr.intWord value
  | Expr.internalFunction id => Expr.internalFunction id
  | Expr.byteArray bytes => Expr.byteArray bytes
  | Expr.contractAddress name => Expr.contractAddress name
  | Expr.contractCreationCode name => Expr.contractCreationCode name
  | Expr.contractRuntimeCode name => Expr.contractRuntimeCode name
  | Expr.calldata => Expr.calldata
  | Expr.msgSig => Expr.msgSig
  | Expr.caller => Expr.caller
  | Expr.callValue => Expr.callValue
  | Expr.self => Expr.self
  | Expr.env envWord => Expr.env envWord
  | Expr.var name => Expr.var name
  | Expr.immutable name => Expr.immutable name
  -- ── Scalar-childed nodes: children default to POINTER-use ─────────────
  | Expr.envLookup lookup expr =>
      Expr.envLookup lookup
        (Expr.normalizeStorageValueUses StoragePosition.pointerUse expr)
  | Expr.envBytesLookup lookup expr =>
      Expr.envBytesLookup lookup
        (Expr.normalizeStorageValueUses StoragePosition.pointerUse expr)
  | Expr.extFnPart part expr =>
      Expr.extFnPart part
        (Expr.normalizeStorageValueUses StoragePosition.pointerUse expr)
  | Expr.unary op expr =>
      Expr.unary op
        (Expr.normalizeStorageValueUses StoragePosition.pointerUse expr)
  -- Inc/dec and assignment-expression targets are LVALUES: pointer-use.
  | Expr.incDec op post cleanup? target =>
      Expr.incDec op post cleanup?
        (Expr.normalizeStorageValueUses StoragePosition.pointerUse target)
  | Expr.assignment op? cleanup? target rhs =>
      Expr.assignment op? cleanup?
        (Expr.normalizeStorageValueUses StoragePosition.pointerUse target)
        (Expr.normalizeStorageValueUses StoragePosition.pointerUse rhs)
  -- Binary operands are WORD consumers: pointer-use. Aggregates cannot be
  -- binary operands in accepted Solidity, and the lowering deliberately
  -- reads storage headers as lengths here (the synthesized
  -- `storageLastPushedIndexExpr` emits `header - 1`), so propagating the
  -- parent's value-use classification into operands would corrupt those
  -- deliberate word reads.
  | Expr.binary op lhs rhs =>
      Expr.binary op
        (Expr.normalizeStorageValueUses StoragePosition.pointerUse lhs)
        (Expr.normalizeStorageValueUses StoragePosition.pointerUse rhs)
  | Expr.addMod lhs rhs modulus =>
      Expr.addMod
        (Expr.normalizeStorageValueUses StoragePosition.pointerUse lhs)
        (Expr.normalizeStorageValueUses StoragePosition.pointerUse rhs)
        (Expr.normalizeStorageValueUses StoragePosition.pointerUse modulus)
  | Expr.mulMod lhs rhs modulus =>
      Expr.mulMod
        (Expr.normalizeStorageValueUses StoragePosition.pointerUse lhs)
        (Expr.normalizeStorageValueUses StoragePosition.pointerUse rhs)
        (Expr.normalizeStorageValueUses StoragePosition.pointerUse modulus)
  -- ── VALUE-USE boundaries: children consume CONTENTS ────────────────────
  | Expr.concatBytes exprs =>
      Expr.concatBytes
        (Expr.normalizeStorageValueUsesList StoragePosition.valueUse exprs)
  | Expr.fixedBytesIndex size base idx =>
      Expr.fixedBytesIndex size
        (Expr.normalizeStorageValueUses StoragePosition.pointerUse base)
        (Expr.normalizeStorageValueUses StoragePosition.pointerUse idx)
  | Expr.castOp kind target expr =>
      -- `bytesN(someBytes)` (`fixedBytesFromBytes`) consumes the byte
      -- CONTENTS; every other cast/cleanup kind is a scalar word consumer.
      Expr.castOp kind target
        (Expr.normalizeStorageValueUses
          (match kind with
          | CastKind.fixedBytesFromBytes => StoragePosition.valueUse
          | _ => StoragePosition.pointerUse)
          expr)
  | Expr.keccak256 expr =>
      Expr.keccak256
        (Expr.normalizeStorageValueUses StoragePosition.valueUse expr)
  | Expr.erc7201 expr =>
      Expr.erc7201
        (Expr.normalizeStorageValueUses StoragePosition.valueUse expr)
  | Expr.tuple exprs =>
      -- Tuple-RHS components are read BY VALUE (TUPLE-RHS fix, #6).
      Expr.tuple
        (Expr.normalizeStorageValueUsesList StoragePosition.valueUse exprs)
  | Expr.encode kind selector? widths tys exprs =>
      -- Encoded arguments consume CONTENTS; the optional selector is a
      -- scalar word.
      Expr.encode kind
        (Expr.normalizeStorageValueUsesOpt StoragePosition.pointerUse
          selector?)
        widths tys
        (Expr.normalizeStorageValueUsesList StoragePosition.valueUse exprs)
  | Expr.abiDecode tys cleanups expr =>
      -- `abi.decode`'s DATA argument consumes byte contents (#4).
      Expr.abiDecode tys cleanups
        (Expr.normalizeStorageValueUses StoragePosition.valueUse expr)
  | Expr.lowLevelCall kind target calldataExpr value gas? bubble =>
      -- The CALLDATA argument is consumed as bytes contents; target/value/
      -- gas are scalar words.
      Expr.lowLevelCall kind
        (Expr.normalizeStorageValueUses StoragePosition.pointerUse target)
        (Expr.normalizeStorageValueUses StoragePosition.valueUse calldataExpr)
        (Expr.normalizeStorageValueUses StoragePosition.pointerUse value)
        (Expr.normalizeStorageValueUsesOpt StoragePosition.pointerUse gas?)
        bubble
  | Expr.contractCreate name args value salt? valueBeforeSalt =>
      -- The encoded constructor-args expression is consumed as bytes.
      Expr.contractCreate name
        (Expr.normalizeStorageValueUses StoragePosition.valueUse args)
        (Expr.normalizeStorageValueUses StoragePosition.pointerUse value)
        (Expr.normalizeStorageValueUsesOpt StoragePosition.pointerUse salt?)
        valueBeforeSalt
  | Expr.newBytes expr =>
      -- The length operand is a scalar word; value-use per the boundary
      -- family it belongs to (inert for scalars).
      Expr.newBytes
        (Expr.normalizeStorageValueUses StoragePosition.valueUse expr)
  | Expr.newDynamicArray ty expr =>
      Expr.newDynamicArray ty
        (Expr.normalizeStorageValueUses StoragePosition.valueUse expr)
  | Expr.externalHash kind expr =>
      Expr.externalHash kind
        (Expr.normalizeStorageValueUses StoragePosition.valueUse expr)
  | Expr.ecrecover digest v r s =>
      Expr.ecrecover
        (Expr.normalizeStorageValueUses StoragePosition.pointerUse digest)
        (Expr.normalizeStorageValueUses StoragePosition.pointerUse v)
        (Expr.normalizeStorageValueUses StoragePosition.pointerUse r)
        (Expr.normalizeStorageValueUses StoragePosition.pointerUse s)
  | Expr.enumFromUInt size expr =>
      Expr.enumFromUInt size
        (Expr.normalizeStorageValueUses StoragePosition.pointerUse expr)
  | Expr.ternary cond thenExpr elseExpr =>
      -- The chosen branch flows to the parent's consumer: propagate `pos`
      -- into the VALUE branches; the boolean condition is never a value use.
      Expr.ternary
        (Expr.normalizeStorageValueUses StoragePosition.pointerUse cond)
        (Expr.normalizeStorageValueUses pos thenExpr)
        (Expr.normalizeStorageValueUses pos elseExpr)
  | Expr.fixedArray exprs =>
      -- Array-literal elements are COPIED into the literal (value-use) —
      -- the nested case the shallow materializer missed.
      Expr.fixedArray
        (Expr.normalizeStorageValueUsesList StoragePosition.valueUse exprs)
  | Expr.length expr =>
      -- `.length` wants the HEADER: pointer-use by definition.
      Expr.length
        (Expr.normalizeStorageValueUses StoragePosition.pointerUse expr)
  | Expr.index base idx =>
      -- Indexing reads the aggregate IN PLACE (base: pointer-use); the key
      -- is value-use (mapping-key contents feed the slot hash, #5).
      Expr.index
        (Expr.normalizeStorageValueUses StoragePosition.pointerUse base)
        (Expr.normalizeStorageValueUses StoragePosition.valueUse idx)
  | Expr.slice base start? stop? =>
      Expr.slice
        (Expr.normalizeStorageValueUses StoragePosition.pointerUse base)
        (Expr.normalizeStorageValueUsesOpt StoragePosition.pointerUse start?)
        (Expr.normalizeStorageValueUsesOpt StoragePosition.pointerUse stop?)

def Expr.normalizeStorageValueUsesList (pos : StoragePosition) :
    List Expr -> List Expr
  | [] => []
  | expr :: rest =>
      Expr.normalizeStorageValueUses pos expr ::
        Expr.normalizeStorageValueUsesList pos rest

def Expr.normalizeStorageValueUsesOpt (pos : StoragePosition) :
    Option Expr -> Option Expr
  | none => none
  | some expr => some (Expr.normalizeStorageValueUses pos expr)

end

/-- Normalize an LVALUE's embedded index expressions. The lvalue SPINE is a
    pointer use by definition (it names a location); index KEYS are value
    uses (mapping-key contents feed the slot hash — the WRITE twin of the
    read-side rule, #5). -/
def LValue.normalizeStorageValueUses : LValue -> LValue
  | LValue.var name => LValue.var name
  | LValue.immutable name => LValue.immutable name
  | LValue.storage name => LValue.storage name
  | LValue.storageIndex name idx =>
      LValue.storageIndex name
        (Expr.normalizeStorageValueUses StoragePosition.valueUse idx)
  | LValue.index base idx =>
      LValue.index base.normalizeStorageValueUses
        (Expr.normalizeStorageValueUses StoragePosition.valueUse idx)

def LValue.normalizeStorageValueUsesOptList :
    List (Option LValue) -> List (Option LValue)
  | [] => []
  | none :: rest => none :: LValue.normalizeStorageValueUsesOptList rest
  | some target :: rest =>
      some target.normalizeStorageValueUses ::
        LValue.normalizeStorageValueUsesOptList rest

mutual

def TupleTarget.normalizeStorageValueUses : TupleTarget -> TupleTarget
  | TupleTarget.hole => TupleTarget.hole
  | TupleTarget.leaf target =>
      TupleTarget.leaf target.normalizeStorageValueUses
  | TupleTarget.nested targets =>
      TupleTarget.nested (TupleTarget.normalizeStorageValueUsesList targets)

def TupleTarget.normalizeStorageValueUsesList :
    List TupleTarget -> List TupleTarget
  | [] => []
  | target :: rest =>
      target.normalizeStorageValueUses ::
        TupleTarget.normalizeStorageValueUsesList rest

end

mutual

/-- The statement-level walk: recurse into every child statement and thread
    the ROOT position of each embedded expression. Value-use roots are
    exactly the statement boundaries that ABI-encode / hash / copy their
    argument CONTENTS: `emitEvent`/`revert` args (#7/#8), require/revert
    string reasons (#10), custom-error `require` args, `revertErrorExpr`,
    storage-alias/push/pop index paths and pushed values, external-call
    calldata. Everything else (conditions, lvalue spines, internal-call
    args — which may pass storage POINTERS — return positions, scalar
    operands) is pointer-use. -/
def Stmt.normalizeStorageValueUses : Stmt -> Stmt
  | Stmt.skip => Stmt.skip
  | Stmt.block stmts =>
      Stmt.block (Stmt.normalizeStorageValueUsesList stmts)
  | Stmt.varDecl ty name init? =>
      Stmt.varDecl ty name
        (Expr.normalizeStorageValueUsesOpt StoragePosition.pointerUse init?)
  | Stmt.memoryVarDecl ty name init? =>
      Stmt.memoryVarDecl ty name
        (Expr.normalizeStorageValueUsesOpt StoragePosition.pointerUse init?)
  | Stmt.memoryLocalize ty name => Stmt.memoryLocalize ty name
  | Stmt.storageAlias aliasName target => Stmt.storageAlias aliasName target
  | Stmt.storageAliasPath aliasName target indexes =>
      Stmt.storageAliasPath aliasName target
        (Expr.normalizeStorageValueUsesList StoragePosition.valueUse indexes)
  | Stmt.storageAliasFrom aliasName source => Stmt.storageAliasFrom aliasName source
  | Stmt.storageAliasFromPath aliasName source indexes =>
      Stmt.storageAliasFromPath aliasName source
        (Expr.normalizeStorageValueUsesList StoragePosition.valueUse indexes)
  | Stmt.storageAliasAssign aliasName target => Stmt.storageAliasAssign aliasName target
  | Stmt.storageAliasAssignPath aliasName target indexes =>
      Stmt.storageAliasAssignPath aliasName target
        (Expr.normalizeStorageValueUsesList StoragePosition.valueUse indexes)
  | Stmt.storageAliasAssignFrom aliasName source =>
      Stmt.storageAliasAssignFrom aliasName source
  | Stmt.storageAliasAssignFromPath aliasName source indexes =>
      Stmt.storageAliasAssignFromPath aliasName source
        (Expr.normalizeStorageValueUsesList StoragePosition.valueUse indexes)
  | Stmt.exprStmt expr =>
      Stmt.exprStmt
        (Expr.normalizeStorageValueUses StoragePosition.pointerUse expr)
  | Stmt.assign target rhs =>
      Stmt.assign target.normalizeStorageValueUses
        (Expr.normalizeStorageValueUses StoragePosition.pointerUse rhs)
  | Stmt.assignTuple targets rhs =>
      Stmt.assignTuple
        (LValue.normalizeStorageValueUsesOptList targets)
        (Expr.normalizeStorageValueUses StoragePosition.pointerUse rhs)
  | Stmt.assignTupleNested targets rhs =>
      Stmt.assignTupleNested
        (TupleTarget.normalizeStorageValueUsesList targets)
        (Expr.normalizeStorageValueUses StoragePosition.pointerUse rhs)
  | Stmt.assignOp target op rhs =>
      Stmt.assignOp target.normalizeStorageValueUses op
        (Expr.normalizeStorageValueUses StoragePosition.pointerUse rhs)
  | Stmt.assignOpCleanup target op rhs cleanup =>
      Stmt.assignOpCleanup target.normalizeStorageValueUses op
        (Expr.normalizeStorageValueUses StoragePosition.pointerUse rhs)
        cleanup
  | Stmt.deleteValue target =>
      Stmt.deleteValue target.normalizeStorageValueUses
  | Stmt.storageArrayPush name arg? =>
      Stmt.storageArrayPush name
        (Expr.normalizeStorageValueUsesOpt StoragePosition.valueUse arg?)
  | Stmt.storageArrayPushRef name arg? =>
      Stmt.storageArrayPushRef name
        (Expr.normalizeStorageValueUsesOpt StoragePosition.valueUse arg?)
  | Stmt.storageArrayPushRefPath name indexes arg? =>
      Stmt.storageArrayPushRefPath name
        (Expr.normalizeStorageValueUsesList StoragePosition.valueUse indexes)
        (Expr.normalizeStorageValueUsesOpt StoragePosition.valueUse arg?)
  | Stmt.storageArrayPushPath name indexes arg? =>
      Stmt.storageArrayPushPath name
        (Expr.normalizeStorageValueUsesList StoragePosition.valueUse indexes)
        (Expr.normalizeStorageValueUsesOpt StoragePosition.valueUse arg?)
  | Stmt.storageArrayPushPathAssign name indexes rhs =>
      Stmt.storageArrayPushPathAssign name
        (Expr.normalizeStorageValueUsesList StoragePosition.valueUse indexes)
        (Expr.normalizeStorageValueUses StoragePosition.valueUse rhs)
  | Stmt.storageArrayPushRefPathAssign name indexes rhs =>
      Stmt.storageArrayPushRefPathAssign name
        (Expr.normalizeStorageValueUsesList StoragePosition.valueUse indexes)
        (Expr.normalizeStorageValueUses StoragePosition.valueUse rhs)
  | Stmt.storageArrayPop name => Stmt.storageArrayPop name
  | Stmt.storageArrayPopRef name => Stmt.storageArrayPopRef name
  | Stmt.storageArrayPopRefPath name indexes =>
      Stmt.storageArrayPopRefPath name
        (Expr.normalizeStorageValueUsesList StoragePosition.valueUse indexes)
  | Stmt.storageArrayPopPath name indexes =>
      Stmt.storageArrayPopPath name
        (Expr.normalizeStorageValueUsesList StoragePosition.valueUse indexes)
  | Stmt.panic code => Stmt.panic code
  | Stmt.assertStmt cond =>
      Stmt.assertStmt
        (Expr.normalizeStorageValueUses StoragePosition.pointerUse cond)
  | Stmt.requireStmt cond reason? =>
      Stmt.requireStmt
        (Expr.normalizeStorageValueUses StoragePosition.pointerUse cond)
        reason?
  | Stmt.requireErrorExpr cond reason =>
      -- The reason is ABI-encoded into `Error(string)`: value-use (#10).
      Stmt.requireErrorExpr
        (Expr.normalizeStorageValueUses StoragePosition.pointerUse cond)
        (Expr.normalizeStorageValueUses StoragePosition.valueUse reason)
  | Stmt.requireCustom cond name args =>
      -- Custom-error args are ABI-encoded into the revert data: value-use
      -- (the previously-unpatched sibling of `Stmt.revert`).
      Stmt.requireCustom
        (Expr.normalizeStorageValueUses StoragePosition.pointerUse cond)
        name
        (Expr.normalizeStorageValueUsesList StoragePosition.valueUse args)
  | Stmt.captureReturn names stmt =>
      Stmt.captureReturn names stmt.normalizeStorageValueUses
  | Stmt.internalCall targets name args =>
      -- Internal-call arguments may pass storage POINTERS: pointer-use.
      Stmt.internalCall targets name
        (Expr.normalizeStorageValueUsesList StoragePosition.pointerUse args)
  | Stmt.internalCallPtr targets fnExpr args =>
      Stmt.internalCallPtr targets
        (Expr.normalizeStorageValueUses StoragePosition.pointerUse fnExpr)
        (Expr.normalizeStorageValueUsesList StoragePosition.pointerUse args)
  | Stmt.ifElse cond thenStmt elseStmt =>
      Stmt.ifElse
        (Expr.normalizeStorageValueUses StoragePosition.pointerUse cond)
        thenStmt.normalizeStorageValueUses
        elseStmt.normalizeStorageValueUses
  | Stmt.switch cond cases default? =>
      Stmt.switch
        (Expr.normalizeStorageValueUses StoragePosition.pointerUse cond)
        (Stmt.normalizeStorageValueUsesCases cases)
        (Stmt.normalizeStorageValueUsesOpt default?)
  | Stmt.whileLoop cond body =>
      Stmt.whileLoop
        (Expr.normalizeStorageValueUses StoragePosition.pointerUse cond)
        body.normalizeStorageValueUses
  | Stmt.doWhile body cond =>
      Stmt.doWhile body.normalizeStorageValueUses
        (Expr.normalizeStorageValueUses StoragePosition.pointerUse cond)
  | Stmt.forLoop init cond step body =>
      Stmt.forLoop init.normalizeStorageValueUses
        (Expr.normalizeStorageValueUses StoragePosition.pointerUse cond)
        step.normalizeStorageValueUses
        body.normalizeStorageValueUses
  | Stmt.tryExternalCall kind target calldataExpr value gas? bubble
      returnsDeclared bindings cleanups success clauses =>
      Stmt.tryExternalCall kind
        (Expr.normalizeStorageValueUses StoragePosition.pointerUse target)
        (Expr.normalizeStorageValueUses StoragePosition.valueUse calldataExpr)
        (Expr.normalizeStorageValueUses StoragePosition.pointerUse value)
        (Expr.normalizeStorageValueUsesOpt StoragePosition.pointerUse gas?)
        bubble returnsDeclared bindings cleanups
        success.normalizeStorageValueUses
        (Stmt.normalizeStorageValueUsesClauses clauses)
  | Stmt.tryContractCreate name args value salt? valueBeforeSalt bindings
      success clauses =>
      Stmt.tryContractCreate name
        (Expr.normalizeStorageValueUses StoragePosition.valueUse args)
        (Expr.normalizeStorageValueUses StoragePosition.pointerUse value)
        (Expr.normalizeStorageValueUsesOpt StoragePosition.pointerUse salt?)
        valueBeforeSalt bindings
        success.normalizeStorageValueUses
        (Stmt.normalizeStorageValueUsesClauses clauses)
  | Stmt.break => Stmt.break
  | Stmt.continue => Stmt.continue
  | Stmt.returnValues exprs =>
      -- Returns may be storage POINTERS (storage-ref returns): pointer-use.
      -- Nested value-use boundaries inside a returned expression are handled
      -- by the expression walk.
      Stmt.returnValues
        (Expr.normalizeStorageValueUsesList StoragePosition.pointerUse exprs)
  | Stmt.revertError reason? => Stmt.revertError reason?
  | Stmt.revertErrorExpr expr =>
      -- `revert(bytesExpr)`-shaped reason: value-use (the previously
      -- unpatched sibling of the `requireErrorExpr` reason).
      Stmt.revertErrorExpr
        (Expr.normalizeStorageValueUses StoragePosition.valueUse expr)
  | Stmt.revert name args =>
      -- Custom-error revert args are ABI-encoded: value-use (#8).
      Stmt.revert name
        (Expr.normalizeStorageValueUsesList StoragePosition.valueUse args)
  | Stmt.emitEvent name args =>
      -- Event args are ABI-encoded: value-use (#7).
      Stmt.emitEvent name
        (Expr.normalizeStorageValueUsesList StoragePosition.valueUse args)
  | Stmt.selfdestruct expr =>
      Stmt.selfdestruct
        (Expr.normalizeStorageValueUses StoragePosition.pointerUse expr)
  | Stmt.checked stmt => Stmt.checked stmt.normalizeStorageValueUses
  | Stmt.unchecked stmt => Stmt.unchecked stmt.normalizeStorageValueUses

def Stmt.normalizeStorageValueUsesList : List Stmt -> List Stmt
  | [] => []
  | stmt :: rest =>
      stmt.normalizeStorageValueUses ::
        Stmt.normalizeStorageValueUsesList rest

def Stmt.normalizeStorageValueUsesOpt : Option Stmt -> Option Stmt
  | none => none
  | some stmt => some stmt.normalizeStorageValueUses

def Stmt.normalizeStorageValueUsesCases :
    List (Word × Stmt) -> List (Word × Stmt)
  | [] => []
  | (caseWord, stmt) :: rest =>
      (caseWord, stmt.normalizeStorageValueUses) ::
        Stmt.normalizeStorageValueUsesCases rest

def Stmt.normalizeStorageValueUsesClauses :
    List TryCatchClause -> List TryCatchClause
  | [] => []
  | TryCatchClause.clause name? bindings stmt :: rest =>
      TryCatchClause.clause name? bindings stmt.normalizeStorageValueUses ::
        Stmt.normalizeStorageValueUsesClauses rest

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
  if decl.isStorageRef then
    (decl.name, Value.storageRef uninitializedStorageReturnTarget)
  else
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
  -- R3: emitted event values are externally observable — strip bytesN width
  -- tags (topics/dataBytes are computed by typed encoders either way; the
  -- stored `indexed`/`data` Value lists match the pre-R3 shapes exactly).
  let values := values.map Value.untagFixedBytes
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
                  runtime.state.events event
                worldMutatedSinceAdoption := true } }
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

/-- The kind of an external-call revert, as solc classifies it before choosing a
    catch clause. An `Error(string)` classification requires — matching solc's
    `tryDecodeErrorMessage` (YulUtilFunctions.cpp:4676-4713,
    IRGeneratorForStatements.cpp:3460-3521) — that the revert data be at least
    0x44 (68) bytes (selector + head-offset word + length word) AND decode as a
    standard ABI string; a shorter/undecodable `Error`-selector payload (e.g. a
    36-byte `selector‖32 zero bytes`) is NOT an `Error(string)` and routes to the
    byte / catch-all clause (gap CB1). `Panic(uint256)` likewise needs >= 0x24
    (36) bytes. -/
inductive RevertKind where
  | errorString
  | panic
  | lowLevel
  deriving Repr, BEq

def revertClassify (raw : List Byte) : RevertKind :=
  match revertBytesSelector? raw with
  | some selector =>
      if wordEq selector externalErrorSelector
          && raw.length ≥ 68
          && (abiDecodeValues? [Ty.bytesCalldata]
                (raw.drop selectorBytes)).isSome then
        RevertKind.errorString
      else if wordEq selector externalPanicSelector
          && raw.length ≥ 36
          && (abiDecodeValues? [Ty.uint256]
                (raw.drop selectorBytes)).isSome then
        RevertKind.panic
      else
        RevertKind.lowLevel
  | none => RevertKind.lowLevel

def TryCatchClause.errorClause? :
    List TryCatchClause -> Option (List BindingDecl × Stmt)
  | [] => none
  | TryCatchClause.clause (some "Error") params body :: _ => some (params, body)
  | _ :: rest => TryCatchClause.errorClause? rest

def TryCatchClause.panicClause? :
    List TryCatchClause -> Option (List BindingDecl × Stmt)
  | [] => none
  | TryCatchClause.clause (some "Panic") params body :: _ => some (params, body)
  | _ :: rest => TryCatchClause.panicClause? rest

def TryCatchClause.catchAllClause? :
    List TryCatchClause -> Option (List BindingDecl × Stmt)
  | [] => none
  | TryCatchClause.clause none params body :: _ => some (params, body)
  | _ :: rest => TryCatchClause.catchAllClause? rest

/-- Dispatch a reverted external call to a catch clause BY the revert KIND
    (not source-order first-match, gap A2): classify the revert data, run the
    matching typed clause if one is present, otherwise fall through to the
    byte / catch-all (`catch (bytes …)` / `catch { }`) clause; `none` means no
    clause matched and the revert propagates (re-reverts). This routing is
    independent of the clauses' written order and matches solc's per-kind
    guarded branches. -/
def TryCatchClause.findMatch? (raw : List Byte)
    (clauses : List TryCatchClause) : Option (Frame × Stmt) :=
  let typed? : Option (Frame × Stmt) :=
    match revertClassify raw with
    | RevertKind.errorString => do
        let (params, body) ← TryCatchClause.errorClause? clauses
        let values ← abiDecodeValues? [Ty.bytesCalldata] (raw.drop selectorBytes)
        let frame ← BindingDecl.bindArgs? params values
        some (frame, body)
    | RevertKind.panic => do
        let (params, body) ← TryCatchClause.panicClause? clauses
        let values ← abiDecodeValues? [Ty.uint256] (raw.drop selectorBytes)
        let frame ← BindingDecl.bindArgs? params values
        some (frame, body)
    | RevertKind.lowLevel => none
  match typed? with
  | some matched => some matched
  | none => do
      let (params, body) ← TryCatchClause.catchAllClause? clauses
      let frame ← TryCatchClause.matchLowLevel? raw params
      some (frame, body)

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
  /-- Per-contract dispatch ID for functions reachable through internal
      function POINTERS (stage C): `some id` (1..n) iff the function is used as
      a value somewhere in the contract, mirroring solc via-IR's internal
      dispatch numbering. `none` for functions never used as values (calling
      such an ID panics 0x51, like solc's dispatch default). Defaulted so all
      existing construction sites are unchanged. -/
  id? : Option Word := none
  deriving Repr

/-- The evaluator-visible table of internal-linkage functions, looked up by
    name. Threaded as an explicit parameter of the `Stmt.eval` mutual block: it
    cannot live in `Context` (defined long before `Stmt`/`FunctionDef`, and
    `InternalFunction.body : Stmt`). -/
abbrev FunctionTable := List InternalFunction

def FunctionTable.lookup? (table : FunctionTable) (name : String) :
    Option InternalFunction :=
  List.find? (fun fn => fn.name == name) table

/-- Resolve a function-pointer dispatch ID. ID 0 never matches (`id?` is `some`
    of 1..n only), so the uninitialized pointer misses — the caller maps a miss
    to `Panic(0x51)`. -/
def FunctionTable.lookupById? (table : FunctionTable) (id : Word) :
    Option InternalFunction :=
  List.find?
    (fun fn =>
      match fn.id? with
      | some fnId => wordEq fnId id
      | none => false)
    table

def InternalFunction.returnDefaultBindings (fn : InternalFunction) : Frame :=
  fn.returns.map BindingDecl.defaultBinding

/-- Reference-preserving parameter binding (function-boundary refactor,
    reference-signature extension). A memory/storage-reference argument value is
    a pointer and must be bound to the (reference-typed) parameter unchanged:
    `Ty.coerceValue?` has no case for `memoryRef`/`storageRef`/`storageSlotRef`,
    so ordinary binding would reject it. Non-reference values coerce exactly as
    the entry path's `BindingDecl.bindArg?`. -/
def BindingDecl.bindArgRef? (decl : BindingDecl) (value : Value) :
    Option (String × Value) :=
  match value with
  | Value.memoryRef _ | Value.storageRef _ | Value.storageSlotRef _ _ =>
      some (decl.name, value)
  | _ => decl.bindArg? value

def BindingDecl.bindArgsRef? :
    List BindingDecl -> List Value -> Option Frame
  | [], [] => some []
  | decl :: decls, value :: values => do
      let head ← decl.bindArgRef? value
      let tail ← BindingDecl.bindArgsRef? decls values
      some (head :: tail)
  | _, _ => none

/-- Build the isolated callee frame: parameters bound to (coerced, or
    reference-preserved) argument values, followed by named/return locals
    defaulted. Mirrors `FunctionDef.initialFrame?` (the entry-frame builder),
    but binds reference-typed parameters by preserving the pointer value
    (`bindArgsRef?`) so `T memory`/`T storage` parameters flow by reference. -/
def InternalFunction.initialFrame? (fn : InternalFunction)
    (args : List Value) : Option Frame :=
  match BindingDecl.bindArgsRef? fn.params args with
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

/-- Reference-preserving analogues of `collectReturnBindings`/
    `coerceReturnBindings` for the `internalCall` arm (reference-signature
    extension). A `T memory` return keeps its memory pointer (so the caller
    aliases the same object, not a deep copy) and a `T storage` return keeps its
    storage pointer (`coerceValue?` has no reference case). Non-reference returns
    are dereferenced-and-coerced exactly as the shared collectors, so the entry
    path (which must abi-value its memory returns and never returns storage
    pointers) is untouched — the divergence is confined to the reference kinds
    the entry path never produces. -/
def collectReturnBindingsRef (returns : List BindingDecl)
    (runtime : Runtime) : Except RevertData (List Value) :=
  let rec collect : List BindingDecl -> Except RevertData (List Value)
    | [] => Except.ok []
    | decl :: rest => do
        let value ←
          match runtime.lookupLocal? decl.name with
          | some value => Except.ok value
          | none => Except.error RevertData.typeMismatch
        let value ←
          match value with
          | Value.memoryRef _ | Value.storageRef _ | Value.storageSlotRef _ _ =>
              Except.ok value
          | _ => do
              let value ← runtime.derefMemoryValueDeep value
              match decl.ty.coerceValue? value with
              | some coerced => Except.ok coerced
              | none => Except.error RevertData.typeMismatch
        let values ← collect rest
        Except.ok (value :: values)
  collect returns

def coerceReturnBindingsRef (returns : List BindingDecl)
    (runtime : Runtime) (values : List Value) :
    Except RevertData (List Value) :=
  let rec coerce :
      List BindingDecl -> List Value -> Except RevertData (List Value)
    | [], [] => Except.ok []
    | decl :: decls, value :: rest => do
        let head ←
          match value with
          | Value.memoryRef _ | Value.storageRef _ | Value.storageSlotRef _ _ =>
              Except.ok value
          | _ => do
              let value ← runtime.derefMemoryValueDeep value
              match decl.ty.coerceValue? value with
              | some coerced => Except.ok coerced
              | none => Except.error RevertData.typeMismatch
        let tail ← coerce decls rest
        Except.ok (head :: tail)
    | _, _ => Except.error RevertData.typeMismatch
  coerce returns values

/-- Write an internal call's coerced return values into the caller's target
    locals (already declared by elaboration). Empty targets discard the values
    (statement-position call). Mirrors `Stmt.captureReturn`'s assignment. A
    returned storage/memory pointer is written reference-aware
    (`assignNamedValuesRef?`) so a storage-pointer return re-points the caller's
    alias target. -/
def internalCallAssign (runtime : Runtime) (targets : List String)
    (values : List Value) : SolI Result :=
  if targets.isEmpty then
    pure (Result.normal runtime)
  else
    match runtime.assignNamedValuesRef? targets values with
    | some updated => pure (Result.normal updated)
    | none => pure (Result.reverted runtime RevertData.typeMismatch)

/-- Frame prologue of a framed internal call, shared by the `internalCall` and
    `internalCallPtr` arms: build the callee frame (reference-preserving
    binding) and REPLACE the caller's locals (state — storage/memory/events/
    transient — is shared). Factored OUT of the `Stmt.eval` mutual block to keep
    that function's compiled stack frame small: the eval block recurses once per
    statement, so its frame size bounds the usable program depth (an oversized
    frame segfaults deep-but-legal programs). -/
def internalCallEnter? (fn : InternalFunction) (argValues : List Value)
    (runtime : Runtime) : Option (Runtime × LocalEnv) :=
  match fn.initialFrame? argValues with
  | none => none
  | some frame => some ({ runtime with locals := [frame] }, runtime.locals)

/-- Result epilogue of a framed internal call (the internal-call analog of
    `FunctionDef.callBodyResult`), shared by the `internalCall` and
    `internalCallPtr` arms and factored out of the eval block (see
    `internalCallEnter?`): collect/coerce returns reference-preservingly,
    restore the caller's locals (keeping the callee's state), assign targets;
    propagate reverts/selfdestructs; a callee cannot break the caller's loop. -/
def internalCallFinish (fn : InternalFunction) (targets : List String)
    (savedLocals : LocalEnv) : Result -> SolI Result
  | Result.returned r values =>
      match
        (if values.isEmpty then
            collectReturnBindingsRef fn.returns r
          else
            coerceReturnBindingsRef fn.returns r values)
      with
      | Except.ok values =>
          internalCallAssign { r with locals := savedLocals } targets values
      | Except.error err => pure (Result.reverted r err)
  | Result.normal r =>
      match collectReturnBindingsRef fn.returns r with
      | Except.ok values =>
          internalCallAssign { r with locals := savedLocals } targets values
      | Except.error err => pure (Result.reverted r err)
  | Result.selfdestructed r =>
      -- Halts the whole external frame; propagate until the entry
      -- `callBodyResult` maps it to `returned []`.
      pure (Result.selfdestructed r)
  | Result.reverted r err =>
      -- Propagate; rollback happens at the entry snapshot.
      pure (Result.reverted r err)
  | Result.broke r =>
      -- A callee cannot break the caller's loop; fixes the latent
      -- `captureReturn` passthrough (function-boundary plan §1.2 / R3).
      pure (Result.reverted r RevertData.typeMismatch)
  | Result.continued r =>
      pure (Result.reverted r RevertData.typeMismatch)

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
              match ← (Expr.eval
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
                (Expr.memoryRefOrValue
                  context runtime expr).caught
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
                  match ← (Expr.eval
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
          match ← (Expr.evalList
              context runtime indexes).caught with
          | Except.ok (indexValues, runtime') =>
              -- WS2: resolve the concrete slot ONCE, at the bind (an
              -- out-of-bounds index Panics 0x32 HERE, as solc does).
              match
                runtime'.bindStorageRef context (StorageBase.field target)
                  indexValues
              with
              | Except.ok ref =>
                  pure (Result.normal (runtime'.declareLocal name ref))
              | Except.error err => pure (Result.reverted runtime err)
          | Except.error err => pure (Result.reverted runtime err)
      | Stmt.storageAliasFrom name source =>
          match runtime.lookupStorageBase? source with
          | some base =>
              pure
                (Result.normal
                  (runtime.declareLocal name base.toRefValue))
          | none => pure (Result.reverted runtime RevertData.typeMismatch)
      | Stmt.storageAliasFromPath name source extraIndexes =>
          match runtime.lookupStorageBase? source with
          | some base => do
              match ←
                (Expr.evalList
                  context runtime extraIndexes).caught
              with
              | Except.ok (extraIndexValues, runtime') =>
                  match
                    runtime'.bindStorageRef context base extraIndexValues
                  with
                  | Except.ok ref =>
                      pure (Result.normal (runtime'.declareLocal name ref))
                  | Except.error err => pure (Result.reverted runtime err)
              | Except.error err => pure (Result.reverted runtime err)
          | none => pure (Result.reverted runtime RevertData.typeMismatch)
      | Stmt.storageAliasAssign name target =>
          match
            runtime.assignStorageRefValue? name (Value.storageRef target)
          with
          | some updated => pure (Result.normal updated)
          | none => pure (Result.reverted runtime RevertData.typeMismatch)
      | Stmt.storageAliasAssignPath name target indexes => do
          match ← (Expr.evalList
              context runtime indexes).caught with
          | Except.ok (indexValues, runtime') =>
              match
                runtime'.bindStorageRef context (StorageBase.field target)
                  indexValues
              with
              | Except.ok ref =>
                  match runtime'.assignStorageRefValue? name ref with
                  | some updated => pure (Result.normal updated)
                  | none =>
                      pure (Result.reverted runtime RevertData.typeMismatch)
              | Except.error err => pure (Result.reverted runtime err)
          | Except.error err => pure (Result.reverted runtime err)
      | Stmt.storageAliasAssignFrom name source =>
          match runtime.lookupStorageBase? source with
          | some base =>
              match runtime.assignStorageRefValue? name base.toRefValue with
              | some updated => pure (Result.normal updated)
              | none => pure (Result.reverted runtime RevertData.typeMismatch)
          | none => pure (Result.reverted runtime RevertData.typeMismatch)
      | Stmt.storageAliasAssignFromPath name source extraIndexes =>
          match runtime.lookupStorageBase? source with
          | some base => do
              match ←
                (Expr.evalList
                  context runtime extraIndexes).caught
              with
              | Except.ok (extraIndexValues, runtime') =>
                  match
                    runtime'.bindStorageRef context base extraIndexValues
                  with
                  | Except.ok ref =>
                      match runtime'.assignStorageRefValue? name ref with
                      | some updated => pure (Result.normal updated)
                      | none =>
                          pure
                            (Result.reverted runtime RevertData.typeMismatch)
                  | Except.error err => pure (Result.reverted runtime err)
              | Except.error err => pure (Result.reverted runtime err)
          | none => pure (Result.reverted runtime RevertData.typeMismatch)
      | Stmt.exprStmt expr => do
          match ← (Expr.eval
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
          -- M1/M3: a memory target aliases a memory-ref RHS (ternary, index/
          -- member, plain var) instead of deep-copying. The target's storage-
          -- vs-memory nature is stable across RHS evaluation, so it is computed
          -- once from the entry runtime.
          let refPreserve := target.wantsMemoryRefRhs runtime
          let evalRhs (rt : Runtime) : SolI (Value × Runtime) :=
            if refPreserve then
              Expr.evalMemoryRefPreserving
                context rt expr
            else
              Expr.eval
                context rt expr
          let evalRhsThenTarget : SolI Result := do
            match ← (evalRhs runtime).caught with
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
                  -- Intrinsic order (solc ExpressionCompiler.cpp:319,331):
                  -- RHS fully, then the LHS reference.
                  evalRhsThenTarget
          | _, _ =>
              evalRhsThenTarget
      | Stmt.assignTuple targets expr => do
          match expr with
          | Expr.tuple components =>
              -- M2: destructure component-by-component reference-preservingly, so
              -- each memory-ref component aliases its target (and `(a,b)=(b,a)`
              -- swaps pointers). All RHS components are evaluated before any
              -- write.
              match ← (Expr.evalTupleComponentsRefPreserving
                  context runtime targets
                  components).caught with
              | Except.ok (values, runtime') =>
                  match ← (LValues.writeTupleWithRuntime context runtime' targets
                      values).caught with
                  | Except.ok updated => pure (Result.normal updated)
                  | Except.error err => pure (Result.reverted runtime err)
              | Except.error err => pure (Result.reverted runtime err)
          | _ =>
              match ← (Expr.eval
                  context runtime expr).caught with
              | Except.ok (Value.tuple values, runtime') =>
                  match ← (LValues.writeTupleWithRuntime context runtime' targets
                      values).caught with
                  | Except.ok updated => pure (Result.normal updated)
                  | Except.error err => pure (Result.reverted runtime err)
              | Except.ok _ => pure (Result.reverted runtime RevertData.typeMismatch)
              | Except.error err => pure (Result.reverted runtime err)
      | Stmt.assignTupleNested targets expr => do
          match ← (Expr.eval
              context runtime expr).caught with
          | Except.ok (Value.tuple values, runtime') =>
              match ← (TupleTargets.writeNested context runtime' targets
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
          let evalRhsThenTarget : SolI Result := do
            match ← (Expr.eval
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
          -- Intrinsic order (solc ExpressionCompiler.cpp:336-370): RHS fully,
          -- then the LHS reference/read.
          evalRhsThenTarget
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
          let evalRhsThenTarget : SolI Result := do
            match ← (Expr.eval
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
          -- Intrinsic order (solc ExpressionCompiler.cpp:336-370): RHS fully,
          -- then the LHS reference/read.
          evalRhsThenTarget
      | Stmt.deleteValue target =>
          match target with
          | LValue.storage name =>
              match runtime.deleteStorageField context name with
              | Except.ok updated => pure (Result.normal updated)
              | Except.error err => pure (Result.reverted runtime err)
          | LValue.var name =>
              match runtime.lookupStorageBase? name with
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
              match ← (Expr.eval
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
          match runtime.lookupStorageBase? name, value? with
          | some base, some expr => do
              match ← (Expr.eval
                  context runtime expr).caught with
              | Except.ok (value, runtime') =>
                  match
                    runtime'.storageArrayPushBasePath context base []
                      (some value)
                  with
                  | Except.ok updated => pure (Result.normal updated)
                  | Except.error err => pure (Result.reverted runtime err)
              | Except.error err => pure (Result.reverted runtime err)
          | some base, none =>
              match runtime.storageArrayPushBasePath context base [] none with
              | Except.ok updated => pure (Result.normal updated)
              | Except.error err => pure (Result.reverted runtime err)
          | none, _ => pure (Result.reverted runtime RevertData.typeMismatch)
      | Stmt.storageArrayPushRefPath name extraIndexes value? =>
          match runtime.lookupStorageBase? name with
          | some base => do
              match ←
                (Expr.evalList
                  context runtime extraIndexes).caught
              with
              | Except.ok (extraIndexValues, runtime') =>
                  match value? with
                  | some expr =>
                      match ← (Expr.eval
                          context runtime'
                          expr).caught with
                      | Except.ok (value, runtime'') =>
                          match
                            runtime''.storageArrayPushBasePath context base
                              extraIndexValues (some value)
                          with
                          | Except.ok updated => pure (Result.normal updated)
                          | Except.error err =>
                              pure (Result.reverted runtime err)
                      | Except.error err => pure (Result.reverted runtime' err)
                  | none =>
                      match
                        runtime'.storageArrayPushBasePath context base
                          extraIndexValues none
                      with
                      | Except.ok updated => pure (Result.normal updated)
                      | Except.error err => pure (Result.reverted runtime err)
              | Except.error err => pure (Result.reverted runtime err)
          | none => pure (Result.reverted runtime RevertData.typeMismatch)
      | Stmt.storageArrayPushPath name indexes value? => do
          match ← (Expr.evalList
              context runtime indexes).caught with
          | Except.ok (indexValues, runtime') =>
              match value? with
              | some expr =>
                  match ← (Expr.eval
                      context runtime'
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
          match ← (Expr.evalList
              context runtime indexes).caught with
          | Except.ok (indexValues, runtime') =>
              match runtime'.storageArrayPushPath context name indexValues none with
              | Except.ok pushed => do
                  match ← (Expr.eval
                      context pushed rhs).caught with
                  | Except.ok (value, runtime'') =>
                      match
                        runtime''.loadStoragePath
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
          match runtime.lookupStorageBase? name with
          | some base => do
              match ←
                (Expr.evalList
                  context runtime extraIndexes).caught
              with
              | Except.ok (extraIndexValues, runtime') =>
                  match
                    runtime'.storageArrayPushBasePath context base
                      extraIndexValues none
                  with
                  | Except.ok pushed => do
                      match ← (Expr.eval
                          context pushed
                          rhs).caught with
                      | Except.ok (value, runtime'') =>
                          match
                            runtime''.loadStorageBasePath
                              context base extraIndexValues
                          with
                          | Except.ok container =>
                              match container.storageArrayLength? with
                              | some length =>
                                  let last := length - 1
                                  match
                                    runtime''.storeStorageBasePathWithDeepClear
                                      context base
                                      (extraIndexValues ++ [Value.word last])
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
          match runtime.lookupStorageBase? name with
          | some base =>
              match runtime.storageArrayPopBasePath context base [] with
              | Except.ok updated => pure (Result.normal updated)
              | Except.error err => pure (Result.reverted runtime err)
          | none => pure (Result.reverted runtime RevertData.typeMismatch)
      | Stmt.storageArrayPopRefPath name extraIndexes =>
          match runtime.lookupStorageBase? name with
          | some base => do
              match ←
                (Expr.evalList
                  context runtime extraIndexes).caught
              with
              | Except.ok (extraIndexValues, runtime') =>
                  match
                    runtime'.storageArrayPopBasePath context base
                      extraIndexValues
                  with
                  | Except.ok updated => pure (Result.normal updated)
                  | Except.error err => pure (Result.reverted runtime err)
              | Except.error err => pure (Result.reverted runtime err)
          | none => pure (Result.reverted runtime RevertData.typeMismatch)
      | Stmt.storageArrayPopPath name indexes => do
          match ← (Expr.evalList
              context runtime indexes).caught with
          | Except.ok (indexValues, runtime') =>
              match runtime'.storageArrayPopPath context name indexValues with
              | Except.ok updated => pure (Result.normal updated)
              | Except.error err => pure (Result.reverted runtime err)
          | Except.error err => pure (Result.reverted runtime err)
      | Stmt.panic code =>
          pure (Result.reverted runtime (RevertData.panic code))
      | Stmt.assertStmt cond => do
          match ← (Expr.eval
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
          match ← (Expr.eval
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
          match ← (Expr.eval
              context runtime cond).caught with
          | Except.ok (value, runtime') =>
              match ← (Expr.eval
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
          match ← (Expr.eval
              context runtime cond).caught with
          | Except.ok (value, runtime') =>
              match ← (Expr.evalList
                  context runtime' exprs).caught with
              | Except.ok (args, runtime'') =>
                  match value.expectWord with
                  | Except.ok word =>
                      if wordTruthy word then
                        pure (Result.normal runtime'')
                      else
                        -- Same value-use materialization as `Stmt.revert`:
                        -- the payload is encoded Runtime-free downstream.
                        match runtime''.materializeForValueUseList
                            context args with
                        | Except.ok args =>
                            pure
                              (Result.reverted runtime''
                                (RevertData.custom name args))
                        | Except.error err =>
                            pure (Result.reverted runtime'' err)
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
          -- Checked-ness is lexical per function: the callee body starts
          -- CHECKED regardless of the caller's enclosing checked/unchecked
          -- block. Frame build + result mapping live OUTSIDE the mutual block
          -- (`internalCallEnter?`/`internalCallFinish`) to keep this
          -- function's stack frame small.
          match ← (Expr.evalRefArgList
              context runtime args).caught with
          | Except.error err => pure (Result.reverted runtime err)
          | Except.ok (argValues, runtime') =>
              match table.lookup? callee with
              | none => pure (Result.reverted runtime' RevertData.typeMismatch)
              | some fn =>
                  match internalCallEnter? fn argValues runtime' with
                  | none => pure (Result.reverted runtime' RevertData.typeMismatch)
                  | some (calleeRuntime, savedLocals) => do
                      let result ← Stmt.eval fuel table
                        { context with checked := true } calleeRuntime fn.body
                      internalCallFinish fn targets savedLocals result
      | Stmt.internalCallPtr targets fnExpr args => do
          -- Call through an internal function pointer (stage C). The pointer
          -- expression evaluates FIRST, then the arguments (via-IR
          -- sequencing); the ID resolves against the table at call time; a
          -- miss — including the uninitialized/deleted ID 0 and
          -- adoption-planted dirty IDs with no dispatch entry — panics 0x51
          -- (solc's dispatch-switch default). Once resolved, the call is the
          -- ordinary framed internal call.
          match ← (Expr.eval
              context runtime fnExpr).caught with
          | Except.error err => pure (Result.reverted runtime err)
          | Except.ok (Value.internalFunction id, runtimeFn) => do
              match ← (Expr.evalRefArgList
                  context runtimeFn args).caught with
              | Except.error err => pure (Result.reverted runtimeFn err)
              | Except.ok (argValues, runtime') =>
                  match table.lookupById? id with
                  | none =>
                      pure (Result.reverted runtime' (RevertData.panic 0x51))
                  | some fn =>
                      match internalCallEnter? fn argValues runtime' with
                      | none =>
                          pure
                            (Result.reverted runtime' RevertData.typeMismatch)
                      | some (calleeRuntime, savedLocals) => do
                          let result ← Stmt.eval fuel table
                            { context with checked := true }
                            calleeRuntime fn.body
                          internalCallFinish fn targets savedLocals result
          | Except.ok (_, runtimeFn) =>
              pure (Result.reverted runtimeFn RevertData.typeMismatch)
      | Stmt.ifElse cond thenBranch elseBranch => do
          match ← (Expr.eval
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
          match ← (Expr.eval
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
                    -- solc (v0.8.35) evaluates a try-call as: the target, then
                    -- the call options in written order (gas/value ordered by
                    -- `gasFirst`), then the calldata argument.  The old code
                    -- evaluated calldata before the options (gap EO1).
                    let valueGasResult? :
                        Except (Runtime × RevertData)
                          (Word × Option Word × Runtime) :=
                      match gasExpr? with
                      | none =>
                          match valueExpr.evalWithRuntimeByContext context runtime' with
                          | Except.ok (valueValue, runtimeValue) =>
                              match valueValue.expectWord with
                              | Except.ok value =>
                                  Except.ok (value, none, runtimeValue)
                              | Except.error err =>
                                  Except.error (runtimeValue, err)
                          | Except.error err =>
                              Except.error (runtime', err)
                      | some gasExpr =>
                          if gasFirst then
                            match gasExpr.evalWithRuntimeByContext context runtime' with
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
                                Except.error (runtime', err)
                          else
                            match valueExpr.evalWithRuntimeByContext
                                context runtime' with
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
                                Except.error (runtime', err)
                    match valueGasResult? with
                    | Except.ok (value, gas?, runtimeOpts) =>
                        match calldataExpr.evalWithRuntimeByContext context runtimeOpts with
                        | Except.ok (calldataValue, runtime''') =>
                            match calldataValue.asBytes? with
                            | some calldata => do
                                    -- #186: a call to `address(this)` is
                                    -- closed-world — self-dispatch through the
                                    -- contract's own code — whenever the hook is
                                    -- installed. Two pre-CALL `extcodesize`
                                    -- existence guards emit the SAME uncatchable
                                    -- empty revert (kept a single `if` branch so
                                    -- the fuel-monotonicity proof's structure is
                                    -- unchanged):
                                    --   * A1: a self-call while the contract is
                                    --     under construction (`extcodesize(this)
                                    --     == 0`) — `this.f()` in a constructor
                                    --     reverts;
                                    --   * A1/A3: a NON-self missing-code target
                                    --     (the guard solc emits before the CALL;
                                    --     try/catch cannot intercept it).
                                    let selfDispatching :=
                                      selfDispatchKindOk kind &&
                                        wordEq target context.self &&
                                        context.selfDispatch?.isSome
                                    if (selfDispatching && context.construction) ||
                                        (!selfDispatching && checkTargetCode &&
                                          !(runtime'''.state.envAccountHasCode
                                            context target)) then
                                      pure
                                        (Result.reverted runtime''' RevertData.empty)
                                    else do
                                      let (callResult, adoptedState) ←
                                        selfDispatchCall context runtime'''.state
                                          kind target calldata value gas?
                                      let runtimeWithInteraction :=
                                        { runtime''' with
                                          state :=
                                            adoptedState }.recordExternalInteraction
                                          (ExternalInteraction.lowLevelCall
                                            callResult)
                                      let success := callResult.success
                                      let output := callResult.output.map normByte
                                      if success then
                                        -- Decode the typed return with the
                                        -- Except view so an oversized dynamic
                                        -- length (L > 0xffffffffffffffff) raises
                                        -- Panic(0x41) — solc decodes the SUCCESS
                                        -- return via `array_allocation_size`, and
                                        -- that panic is NOT catchable (it is a
                                        -- fresh revert of the CALLER, not the
                                        -- callee's returndata), so it propagates
                                        -- uncaught (TC-OOM1). Genuinely-empty
                                        -- decode failures (short data / bad
                                        -- offset / dirty-bit / validator) stay
                                        -- `RevertData.empty`, exactly matching the
                                        -- explicit `abi.decode` path above.
                                        match abiDecodeValuesExcept?
                                            (returns.map BindingDecl.ty) output with
                                          | Except.ok decoded =>
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
                                          | Except.error revertData =>
                                              pure
                                                (Result.reverted
                                                  runtimeWithInteraction
                                                  revertData)
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
                            | none =>
                                pure (Result.reverted runtime''' RevertData.typeMismatch)
                        | Except.error err => pure (Result.reverted runtimeOpts err)
                    | Except.error (runtimeFailed, err) =>
                        pure (Result.reverted runtimeFailed err)
                | Except.error err => pure (Result.reverted runtime' err)
            | Except.error err => pure (Result.reverted runtime err)
        | Stmt.tryContractCreate contractName constructorArgsExpr valueExpr
            saltExpr? valueBeforeSalt returns successBody catchClauses =>
            -- solc (v0.8.35) evaluates `new C{opts}(args)` as: the
            -- FunctionCallOptions in their WRITTEN order (value/salt ordered by
            -- `valueBeforeSalt`), THEN the constructor arguments LAST.  The old
            -- code forced args→value→salt (gap DIV-CREATE-1); now it is
            -- options-first, args-last — matching the plain-create handler above
            -- and solc.  The option eval carries its threaded runtime in the
            -- error so a mid-option revert reports the right post-effect runtime.
            let optionsResult? :
                Except (Runtime × RevertData)
                  (Word × Option Word × Runtime) :=
              match saltExpr? with
              | none =>
                  match valueExpr.evalWithRuntimeByContext context runtime with
                  | Except.ok (valueValue, runtimeValue) =>
                      match valueValue.expectWord with
                      | Except.ok value => Except.ok (value, none, runtimeValue)
                      | Except.error err => Except.error (runtimeValue, err)
                  | Except.error err => Except.error (runtime, err)
              | some saltExpr =>
                  if valueBeforeSalt then
                    match valueExpr.evalWithRuntimeByContext context runtime with
                    | Except.ok (valueValue, runtimeValue) =>
                        match valueValue.expectWord with
                        | Except.ok value =>
                            match saltExpr.evalWithRuntimeByContext
                                context runtimeValue with
                            | Except.ok (saltValue, runtimeSalt) =>
                                match saltValue.expectWord with
                                | Except.ok salt =>
                                    Except.ok (value, some salt, runtimeSalt)
                                | Except.error err =>
                                    Except.error (runtimeSalt, err)
                            | Except.error err => Except.error (runtimeValue, err)
                        | Except.error err => Except.error (runtimeValue, err)
                    | Except.error err => Except.error (runtime, err)
                  else
                    match saltExpr.evalWithRuntimeByContext context runtime with
                    | Except.ok (saltValue, runtimeSalt) =>
                        match saltValue.expectWord with
                        | Except.ok salt =>
                            match valueExpr.evalWithRuntimeByContext
                                context runtimeSalt with
                            | Except.ok (valueValue, runtimeValue) =>
                                match valueValue.expectWord with
                                | Except.ok value =>
                                    Except.ok (value, some salt, runtimeValue)
                                | Except.error err =>
                                    Except.error (runtimeValue, err)
                            | Except.error err => Except.error (runtimeSalt, err)
                        | Except.error err => Except.error (runtimeSalt, err)
                    | Except.error err => Except.error (runtime, err)
            match optionsResult? with
            | Except.ok (value, salt?, runtimeOpts) =>
                match constructorArgsExpr.evalWithRuntimeByContext
                    context runtimeOpts with
                | Except.ok (argsValue, runtime''') =>
                    match argsValue.asBytes? with
                    | some constructorArgs =>
                        emitContractCreation context runtime'''.state
                            contractName constructorArgs value salt? >>=
                          fun (createResult, adoptedState) =>
                      let runtimeWithInteraction :=
                        { runtime''' with
                          state :=
                            adoptedState }.recordExternalInteraction
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
                    | none =>
                        pure (Result.reverted runtime''' RevertData.typeMismatch)
                | Except.error err => pure (Result.reverted runtimeOpts err)
            | Except.error (runtimeErr, err) =>
                pure (Result.reverted runtimeErr err)
      | Stmt.break => pure (Result.broke runtime)
      | Stmt.continue => pure (Result.continued runtime)
      | Stmt.returnValues exprs => do
          match ← (Expr.evalReturnList
              context runtime exprs).caught with
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
          match ← (Expr.eval
              context runtime reasonExpr).caught with
          | Except.ok (reasonValue, runtime') =>
              match errorStringBytesRevert? reasonValue with
              | some payload =>
                  pure (Result.reverted runtime' payload)
              | none =>
                  pure (Result.reverted runtime' RevertData.typeMismatch)
          | Except.error err => pure (Result.reverted runtime err)
      | Stmt.revert name exprs => do
          match ← (Expr.evalList
              context runtime exprs).caught with
          | Except.ok (values, runtime') =>
              -- Deep value-use materialization (same class as emitEvent /
              -- abi.encode): the custom-error payload is ABI-encoded OUTSIDE
              -- the runtime (`Contract.encodeRevertData?` is Runtime-free),
              -- so nested memory/storage ref leaves must be loaded here.
              match runtime'.materializeForValueUseList context values with
              | Except.ok values =>
                  pure (Result.reverted runtime' (RevertData.custom name values))
              | Except.error err => pure (Result.reverted runtime' err)
          | Except.error err => pure (Result.reverted runtime err)
      | Stmt.emitEvent name exprs => do
          -- TWO-PHASE emit order (solc ExpressionCompiler.cpp Kind::Event,
          -- 976-1043): the INDEXED (topic) arguments are evaluated in REVERSE
          -- source order first, then the NON-INDEXED (data) arguments in
          -- FORWARD source order. Evaluate in that schedule, then restore
          -- positional order for encoding (`Runtime.emitEvent` is positional).
          let flags : List Bool :=
            match context.eventDecl? name with
            | some decl =>
                if decl.fields.length == exprs.length then
                  decl.fields.map (fun field => field.indexed)
                else if decl.fields.isEmpty then
                  -- Legacy field-less decls: the first `indexedCount`
                  -- positional arguments are the indexed ones
                  -- (`Runtime.emitEvent` takes/drops at `indexedCount`).
                  (List.range exprs.length).map
                    (fun i => decide (i < decl.indexedCount))
                else
                  List.replicate exprs.length false
            | none => List.replicate exprs.length false
          let positions := (List.range exprs.length).zip flags
          let scheduleIdx :=
            ((positions.filter (fun p => p.2)).reverse ++
              positions.filter (fun p => !p.2)).map Prod.fst
          let scheduleExprs := scheduleIdx.filterMap (fun i => exprs[i]?)
          match ← (Expr.evalList context runtime scheduleExprs).caught with
          | Except.ok (scheduled, runtime') =>
              let paired := scheduleIdx.zip scheduled
              let values :=
                (List.range exprs.length).filterMap
                  (fun i => (paired.find? (fun p => p.1 == i)).map Prod.snd)
              -- Deep value-use materialization (same family as abi.encode /
              -- keccak / concat): an event argument NESTING a memory or
              -- storage reference (e.g. a `uint256[][]` argument whose
              -- element rows are `Value.memoryRef`s) must be fully loaded
              -- before the Runtime-free event encoder runs — a bare ref
              -- leaf has no structural encoding and would spuriously revert
              -- where solc+EVM emits the event.
              match runtime'.materializeForValueUseList context values with
              | Except.ok values =>
                  match runtime'.emitEvent context name values with
                  | Except.ok updated => pure (Result.normal updated)
                  | Except.error err => pure (Result.reverted runtime err)
              | Except.error err => pure (Result.reverted runtime err)
          | Except.error err => pure (Result.reverted runtime err)
      | Stmt.selfdestruct recipientExpr => do
          match ← (Expr.eval
              context runtime recipientExpr).caught with
          | Except.ok (recipientValue, runtime') =>
              match recipientValue.expectWord with
              | Except.ok recipient =>
                  -- CS1: compute the 6780 delete flag from the PRE-transfer
                  -- created-accounts set, then move the full self balance to the
                  -- recipient, then record the (from, recipient, delete) facts.
                  let created := runtime'.state.envCreatedAccounts context
                  let transferred :=
                    runtime'.state.selfdestructTransfer context recipient
                  pure
                    (Result.selfdestructed
                      { runtime' with
                        state :=
                          transferred.recordSelfdestruct
                            context.evmVersion
                            created
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
      match ← (Expr.eval
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
          match ← (Expr.eval
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
          match ← (Expr.eval
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
      match ← (Expr.eval
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
  /-- Internal-function-pointer dispatch ID (stage C), copied onto the
      table projection (`toInternal` -> `InternalFunction.id?`). -/
  dispatchId? : Option Word := none
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
    body := function.body
    id? := function.dispatchId? }

def FunctionDef.callBodyResult (function : FunctionDef)
    (state : State) : Result -> CallResult
  | Result.normal runtime' =>
      match function.collectReturns runtime' with
      | Except.ok values =>
          CallResult.returned runtime'.state
            (values.map Value.untagFixedBytes)
      | Except.error err =>
          CallResult.reverted state err.untagFixedBytes
  | Result.returned runtime' values =>
      if values.isEmpty then
        match function.collectReturns runtime' with
        | Except.ok namedValues =>
            CallResult.returned runtime'.state
              (namedValues.map Value.untagFixedBytes)
        | Except.error err =>
            CallResult.reverted state err.untagFixedBytes
      else
        match function.coerceReturnValues runtime' values with
        | Except.ok coerced =>
            CallResult.returned runtime'.state
              (coerced.map Value.untagFixedBytes)
        | Except.error err =>
            CallResult.reverted state err.untagFixedBytes
  | Result.selfdestructed runtime' =>
      CallResult.returned runtime'.state []
  | Result.reverted runtime' revert =>
      let _ := runtime'
      CallResult.reverted state revert.untagFixedBytes
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
        -- A2: this is the external message-call / constructor entry (internal
        -- calls are spliced in `Stmt.eval` and never reach here). Before the
        -- body runs, re-base `self`'s dynamic balance to the environment fact
        -- for `self` and credit `msg.value`, as the EVM credits value before
        -- body execution. Re-basing from the oracle each entry (rather than
        -- threading a persistent balance) honours the environment injecting ETH
        -- between top-level calls; the intra-frame credit/debit is what A2 adds.
        let state :=
          { state with
            selfBalance :=
              SolidCore.Solidity.Shared.addWord
                (SolidCore.Solidity.Shared.Account.balanceAt
                  context.accountBalances context.self)
                context.value
            worldMutatedSinceAdoption := true }
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

theorem FunctionDef.call?_reverted_rolls_back
    {fuel : Nat} {table : FunctionTable} {context : Context}
    {function : FunctionDef}
    {state : State} {args : List Value} {frame : Frame}
    {runtime : Runtime} {revert : RevertData}
    (hAccepts : function.acceptsValue context.value = true)
    (hFrame : function.initialFrame? args = some frame)
  (hEval :
      Stmt.eval fuel table context
          { state :=
              { state with
                selfBalance :=
                  SolidCore.Solidity.Shared.addWord
                    (SolidCore.Solidity.Shared.Account.balanceAt
                      context.accountBalances context.self)
                    context.value
                worldMutatedSinceAdoption := true }
            locals := [frame] }
          function.body =
        pure (Result.reverted runtime revert)) :
    function.call? fuel table context state args =
      some (CallResult.reverted state revert.untagFixedBytes) := by
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

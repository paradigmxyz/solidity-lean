import SolidCore.Solidity.Shared.Word
import SolidCore.Solidity.Interpreter
import SolidCore.Solidity.Keccak

namespace SolidCore
namespace Solidity
namespace Source
namespace ABI

abbrev Bytes := List Byte

def selectorBytes : Nat := 4
def wordBytes : Nat := 32

def normalizeBytes (bytes : Bytes) : Bytes :=
  SolidCore.Solidity.Shared.External.normalizeBytes bytes

def readBytes? (bytes : Bytes) (offset size : Nat) : Option Bytes :=
  let rest := bytes.drop offset
  if size <= rest.length then
    some (normalizeBytes (rest.take size))
  else
    none

def bytesToWordBE (bytes : Bytes) : Word :=
  SolidCore.Solidity.Shared.norm
    (bytes.foldl (fun acc byte => acc * 256 + normByte byte) 0)

def wordToBytesBE : Nat -> Word -> Bytes
  | 0, _ => []
  | n + 1, value =>
      wordToBytesBE n (value / 256) ++ [normByte value]

def encodeWord (value : Word) : Bytes :=
  wordToBytesBE wordBytes (SolidCore.Solidity.Shared.norm value)

def addressFits (value : Word) : Bool :=
  SolidCore.Solidity.Shared.norm value < 2 ^ 160

def selectorFits (value : Word) : Bool :=
  SolidCore.Solidity.Shared.norm value < 2 ^ (8 * selectorBytes)

def fixedBytesFits (size : Nat) (value : Word) : Bool :=
  0 < size && size <= wordBytes &&
    SolidCore.Solidity.Shared.norm value < 2 ^ (8 * size)

def allZeroBytes : Bytes -> Bool
  | [] => true
  | byte :: rest => normByte byte == 0 && allZeroBytes rest

def encodeSelector (selector : Word) : Bytes :=
  wordToBytesBE selectorBytes (SolidCore.Solidity.Shared.norm selector)

def structuralSelectorFromBytes (bytes : Bytes) : Word :=
  bytesToWordBE ((normalizeBytes bytes).take selectorBytes)

def selectorFromSignature (signature : String) : Word :=
  SolidCore.Solidity.Shared.norm (Keccak.selector4 signature)

def structuralSelectorFromSignature (signature : String) : Word :=
  selectorFromSignature signature

def readWord? (bytes : Bytes) (offset : Nat) : Option Word :=
  match readBytes? bytes offset wordBytes with
  | some chunk => some (bytesToWordBE chunk)
  | none => none

def readSelector? (calldata : Bytes) : Option Word :=
  match readBytes? calldata 0 selectorBytes with
  | some selector => some (bytesToWordBE selector)
  | none => none

def paddingLength (length : Nat) : Nat :=
  (wordBytes - length % wordBytes) % wordBytes

def padRightWord (bytes : Bytes) : Bytes :=
  normalizeBytes bytes ++ List.replicate (paddingLength bytes.length) 0

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

def Ty.abiDecodeFuel : Ty -> Nat
  | Ty.fixedArray _ elementTy => abiDecodeFuel elementTy + 1
  | Ty.dynamicArray elementTy => abiDecodeFuel elementTy + 1
  | Ty.tuple elements => listAbiDecodeFuel elements + 1
  | _ => 1

def Ty.listAbiDecodeFuel : List Ty -> Nat
  | [] => 0
  | ty :: rest => abiDecodeFuel ty + listAbiDecodeFuel rest

end

def encodeStaticValue? : Ty -> Value -> Option Bytes
  | Ty.bool, Value.word value =>
      if wordEq value 0 || wordEq value 1 then
        some (encodeWord value)
      else
        none
  | Ty.address, Value.word value =>
      if addressFits value then
        some (encodeWord value)
      else
        none
  | Ty.uint256, Value.word value => some (encodeWord value)
  | Ty.int256, Value.int value => some (encodeWord value)
  | Ty.fixedBytes size, Value.word value =>
      if fixedBytesFits size value then
        some (wordToBytesBE size value ++
          List.replicate (wordBytes - size) 0)
      else
        none
  -- R3: width-tagged bytesN — identical left-aligned boundary encoding.
  | Ty.fixedBytes size, Value.fixedBytes _ value =>
      if fixedBytesFits size value then
        some (wordToBytesBE size value ++
          List.replicate (wordBytes - size) 0)
      else
        none
  -- LIT-COERCION (#141 revert/require custom-error data): a hex/string/bytes
  -- LITERAL argument to a `bytesN` error parameter is lowered target-blind to a
  -- dynamic-`bytes` `Value.bytes` (its type derived from the literal, not the
  -- declared parameter). solc coerces such a literal to the fixed target: ONE
  -- left-aligned 32-byte word (the ≤ n meaningful bytes at the top, zero-padded).
  -- Encode it as that word here — the ONLY way a `Value.bytes` reaches a
  -- `fixedBytes` slot is this literal path (solc rejects any implicit
  -- `bytes`→`bytesN` value conversion at compile time).
  | Ty.fixedBytes size, Value.bytes bytes =>
      if bytes.length ≤ size then
        some (padRightWord bytes)
      else
        none
  | Ty.externalFunction, Value.externalFunction addr selector =>
      if addressFits addr && selectorFits selector then
        some
          (wordToBytesBE 20 addr ++
            wordToBytesBE selectorBytes selector ++
            List.replicate (wordBytes - 20 - selectorBytes) 0)
      else
        none
  | Ty.fixedArray size elementTy, Value.fixedArray values =>
      if values.length == size && !Ty.isDynamicAbi elementTy then
        let rec encodeArrayValues? : List Value -> Option Bytes
          | [] => some []
          | value :: rest => do
              let head ← encodeStaticValue? elementTy value
              let tail ← encodeArrayValues? rest
              some (head ++ tail)
        encodeArrayValues? values
      else
        none
  | Ty.tuple elementTys, Value.tuple values =>
      if values.length == elementTys.length &&
          !Ty.listHasDynamicAbi elementTys then
        let rec encodeTupleValues? :
            List Ty -> List Value -> Option Bytes
          | [], [] => some []
          | ty :: tys, value :: rest => do
              let head ← encodeStaticValue? ty value
              let tail ← encodeTupleValues? tys rest
              some (head ++ tail)
          | _, _ => none
        encodeTupleValues? elementTys values
      else
        none
  | _, _ => none

def encodeDynamicPayload? : Ty -> Value -> Option Bytes
  | Ty.bytesCalldata, Value.bytes bytes =>
      some (encodeWord bytes.length ++ padRightWord bytes)
  | Ty.dynamicArray elementTy, Value.dynamicArray values =>
      let rec encodeDynamicArrayValues? :
          List Value -> Nat -> Option (Bytes × Bytes × Nat)
        | [], offset => some ([], [], offset)
        | value :: rest, offset =>
            if Ty.isDynamicAbi elementTy then
              match encodeDynamicPayload? elementTy value with
              | some payload =>
                  match encodeDynamicArrayValues? rest
                      (offset + payload.length) with
                  | some (heads, tails, finalOffset) =>
                      some (encodeWord offset ++ heads,
                        payload ++ tails, finalOffset)
                  | none => none
              | none => none
            else
              match encodeStaticValue? elementTy value,
                  encodeDynamicArrayValues? rest offset with
              | some head, some (heads, tails, finalOffset) =>
                  some (head ++ heads, tails, finalOffset)
              | _, _ => none
      match Ty.abiHeadWords? elementTy with
      | some elementWords =>
          let initialOffset := wordBytes * values.length * elementWords
          match encodeDynamicArrayValues? values initialOffset with
          | some (heads, tails, _) =>
              some (encodeWord values.length ++ heads ++ tails)
          | none => none
      | none => none
  | Ty.fixedArray size elementTy, Value.fixedArray values =>
      if values.length == size && Ty.isDynamicAbi elementTy then
        let rec encodeArrayValues? :
            List Value -> Nat -> Option (Bytes × Bytes × Nat)
          | [], offset => some ([], [], offset)
          | value :: rest, offset => do
              let payload ← encodeDynamicPayload? elementTy value
              let encodedRest ←
                encodeArrayValues? rest (offset + payload.length)
              match encodedRest with
              | (heads, tails, finalOffset) =>
                  some (encodeWord offset ++ heads,
                    payload ++ tails, finalOffset)
        match encodeArrayValues? values (wordBytes * size) with
        | some (heads, tails, _) => some (heads ++ tails)
        | none => none
      else
        none
  | Ty.tuple elementTys, Value.tuple values =>
      if values.length == elementTys.length &&
          Ty.listHasDynamicAbi elementTys then
        let rec encodeTupleValues? :
            List Ty -> List Value -> Nat -> Option (Bytes × Bytes × Nat)
          | [], [], offset => some ([], [], offset)
          | ty :: tys, value :: rest, offset =>
              if Ty.isDynamicAbi ty then
                match encodeDynamicPayload? ty value with
                | some payload =>
                    match encodeTupleValues? tys rest
                        (offset + payload.length) with
                    | some (heads, tails, finalOffset) =>
                        some (encodeWord offset ++ heads,
                          payload ++ tails, finalOffset)
                    | none => none
                | none => none
              else
                match encodeStaticValue? ty value,
                    encodeTupleValues? tys rest offset with
                | some head, some (heads, tails, finalOffset) =>
                    some (head ++ heads, tails, finalOffset)
                | _, _ => none
          | _, _, _ => none
        match Ty.listAbiHeadWords? elementTys with
        | some headWords =>
            match encodeTupleValues? elementTys values
                (wordBytes * headWords) with
            | some (heads, tails, _) => some (heads ++ tails)
            | none => none
        | none => none
      else
        none
  | _, _ => none

def encodeValuesAux? :
    List Ty -> List Value -> Nat -> Option (Bytes × Bytes × Nat)
  | [], [], offset => some ([], [], offset)
  | ty :: tys, value :: values, offset =>
      if Ty.isDynamicAbi ty then
        match encodeDynamicPayload? ty value with
        | some payload =>
            match encodeValuesAux? tys values (offset + payload.length) with
            | some (heads, tails, finalOffset) =>
                some (encodeWord offset ++ heads, payload ++ tails,
                  finalOffset)
            | none => none
        | none => none
      else
        match encodeStaticValue? ty value,
            encodeValuesAux? tys values offset with
        | some head, some (heads, tails, finalOffset) =>
            some (head ++ heads, tails, finalOffset)
        | _, _ => none
  | _, _, _ => none

def encodeValues? (tys : List Ty) (values : List Value) : Option Bytes := do
  let headWords ← Ty.listAbiHeadWords? tys
  match encodeValuesAux? tys values (wordBytes * headWords) with
  | some (heads, tails, _) => some (heads ++ tails)
  | none => none

-- The `lazy` flag marks a *calldata* parameter (vs a `memory`-location one,
-- which solc validates eagerly). When set, structurally-malformed inner
-- *dynamic* elements of a calldata aggregate are not rejected at the boundary;
-- instead a `Value.calldataDeferredInvalid` marker is placed in the decoded
-- spine and validated on access, mirroring solc's calldata-pointer model. The
-- immediate structure (length bound, head-area presence) is still validated
-- eagerly. `lazy` is threaded unchanged into nested calldata elements; the
-- top-level per-parameter decode never substitutes markers (a malformed
-- top-level offset reverts eagerly, exactly as solc validates immediate
-- structure), because marker substitution happens only inside the aggregate
-- element loops below.
-- Lift an `Option`-returning primitive (calldata word/byte read, head-word
-- count) into the `Except RevertData` decode monad: a `none` — a data-presence
-- / bounds failure — is solc's empty `revert(0, 0)`.
def abiArgOpt {α} : Option α -> Except RevertData α
  | some a => Except.ok a
  | none => Except.error RevertData.empty

-- Returns `Except RevertData Value`: `Except.error RevertData.empty` is solc's
-- empty `revert(0, 0)` (bounds / dirty-value / enum-range failure), while
-- `Except.error RevertData.memoryAllocationTooLarge` is Panic(0x41), raised only
-- for an *eager* (`memory`-location, `lazy = false`) dynamic reference param
-- whose length exceeds the allocation bound — mirroring DEC-OOM #62's
-- `abi.decode` decoder (`abiCheckAllocation?`). A `calldata`-location param
-- (`lazy = true`) returns a pointer and never allocates, so it keeps the empty
-- revert on an oversized length.
def decodeValueAtWithFuel? : Nat -> Bool -> Bytes -> Nat -> Ty -> Except RevertData Value
  | 0, _, _, _, _ => Except.error RevertData.empty
  | _fuel + 1, _lazy, argData, headIndex, Ty.bool => do
      let value ← abiArgOpt (readWord? argData (wordBytes * headIndex))
      if wordEq value 0 || wordEq value 1 then
        Except.ok (Value.word value)
      else
        Except.error RevertData.empty
  | _fuel + 1, _lazy, argData, headIndex, Ty.address => do
      let value ← abiArgOpt (readWord? argData (wordBytes * headIndex))
      if addressFits value then
        Except.ok (Value.word value)
      else
        Except.error RevertData.empty
  | _fuel + 1, _lazy, argData, headIndex, Ty.uint256 => do
      let value ← abiArgOpt (readWord? argData (wordBytes * headIndex))
      Except.ok (Value.word value)
  | _fuel + 1, _lazy, argData, headIndex, Ty.int256 => do
      let value ← abiArgOpt (readWord? argData (wordBytes * headIndex))
      Except.ok (Value.int value)
  | _fuel + 1, _lazy, argData, headIndex, Ty.fixedBytes size =>
      if 0 < size && size <= wordBytes then
        do
        let slot ← abiArgOpt (readBytes? argData (wordBytes * headIndex) wordBytes)
        let bytes ← abiArgOpt (readBytes? slot 0 size)
        let padding ← abiArgOpt (readBytes? slot size (wordBytes - size))
        if allZeroBytes padding then
          -- R3: carry the width on the decoded bytesN value (raw word is the
          -- right-aligned internal form, exactly as before).
          Except.ok (Value.fixedBytes size (bytesToWordBE bytes))
        else
          Except.error RevertData.empty
      else
        Except.error RevertData.empty
  | _fuel + 1, _lazy, _argData, _headIndex, Ty.internalFunction =>
      -- Internal function pointers have no ABI representation (they cannot
      -- cross the external boundary); decoding one is a type error.
      Except.error RevertData.empty
  | _fuel + 1, _lazy, argData, headIndex, Ty.externalFunction => do
      let slot ← abiArgOpt (readBytes? argData (wordBytes * headIndex) wordBytes)
      let addressBytes ← abiArgOpt (readBytes? slot 0 20)
      let selectorPart ← abiArgOpt (readBytes? slot 20 selectorBytes)
      let padding ←
        abiArgOpt (readBytes? slot (20 + selectorBytes)
          (wordBytes - 20 - selectorBytes))
      if allZeroBytes padding then
        Except.ok
          (Value.externalFunction
            (bytesToWordBE addressBytes) (bytesToWordBE selectorPart))
      else
        Except.error RevertData.empty
  | _fuel + 1, lazy, argData, headIndex, Ty.bytesCalldata => do
      let offset ← abiArgOpt (readWord? argData (wordBytes * headIndex))
      let length ← abiArgOpt (readWord? argData offset)
      -- A `memory`-location `bytes`/`string` (eager) is allocated (byte length
      -- rounded up to a word + memPtr) BEFORE the calldata data-presence check,
      -- so an oversized length raises Panic(0x41). A `calldata` param never
      -- allocates → empty revert.
      if !lazy then abiCheckAllocation? true length
      let bytes ← abiArgOpt (readBytes? argData (offset + wordBytes) length)
      Except.ok (Value.bytes bytes)
  | fuel + 1, lazy, argData, headIndex, Ty.dynamicArray elementTy => do
      let offset ← abiArgOpt (readWord? argData (wordBytes * headIndex))
      let length ← abiArgOpt (readWord? argData offset)
      -- A `memory` array (eager) is allocated (memory stride 0x20 per element)
      -- BEFORE elements are read, so an oversized length raises Panic(0x41); a
      -- `calldata` array (lazy) returns a pointer and never allocates.
      if !lazy then abiCheckAllocation? false length
      -- Inner-element validation is deferred only for a *calldata* array of
      -- *dynamic* elements (solc returns a calldata pointer and validates each
      -- element's inner offset/length lazily on access); a structurally
      -- malformed such element becomes a deferred marker instead of a boundary
      -- revert. The recursor's shape matches the eager decoder so the automatic
      -- termination measure is preserved. `lazy` is threaded unchanged into the
      -- element decode, so an eager array of eager reference elements fires each
      -- element's own Panic(0x41) guard.
      let rec decodeDynamicArrayValues? :
          Nat -> Nat -> Except RevertData (List Value)
        | 0, _ => Except.ok []
        | remaining + 1, index => do
            let value ←
              match
                decodeValueAtWithFuel? fuel lazy
                  (argData.drop (offset + wordBytes)) index elementTy
              with
              | Except.ok v => Except.ok v
              | Except.error e =>
                  -- On the calldata (lazy) path, the eager head-area presence
                  -- check below already guaranteed every element's head words
                  -- are present, so a decode failure here is a *value*
                  -- validation failure (dirty bool/address/bytesN, or a nested
                  -- dynamic element's malformed inner offset/length), never a
                  -- bounds failure. solc validates such elements only on
                  -- ACCESS, so substitute the deferred-invalid marker instead
                  -- of reverting at the boundary. This now covers value-type
                  -- (non-`isDynamicAbi`) elements too, not just dynamic ones.
                  if lazy then
                    Except.ok (Value.calldataDeferredInvalid elementTy)
                  else
                    Except.error e
            let step ← abiArgOpt (Ty.abiHeadWords? elementTy)
            let rest ← decodeDynamicArrayValues? remaining (index + step)
            Except.ok (value :: rest)
      let step ← abiArgOpt (Ty.abiHeadWords? elementTy)
      -- Head-area presence check (solc `abi_decode_available_length_*_array`:
      -- `srcEnd := add(arrayPos, mul(length, headStride)); if gt(srcEnd, end)`):
      -- the `length` element head words must be within `argData`. This runs on
      -- BOTH the calldata (lazy) and memory (eager) paths, and — crucially —
      -- AFTER the outer allocation guard (`abiCheckAllocation?` above) but BEFORE
      -- any element decode, so on the eager path a truncated element-head area
      -- reverts EMPTY here instead of reaching an inner dynamic element's
      -- Panic(0x41). It applies to value-type elements (stride 0x20) as well as
      -- dynamic ones (offset stride 0x20; static-element stride = element head
      -- size, i.e. `step * 0x20`, matching solc's `mul(length, calldata_head)`).
      -- Only the value validation / offset-following read INSIDE a present head
      -- is deferred to access time (calldata/lazy path). `gt` is strict, so a
      -- well-formed head with `srcEnd == end` PASSES (readBytes? returns some).
      if (readBytes? (argData.drop (offset + wordBytes)) 0
            (length * step * wordBytes)).isNone then
        Except.error RevertData.empty
      else do
        let values ← decodeDynamicArrayValues? length 0
        Except.ok (Value.dynamicArray values)
  | fuel + 1, lazy, argData, headIndex, Ty.fixedArray size elementTy =>
      -- A fixed-size memory array `T[N]` allocates, but `N` is a compile-time
      -- constant (`size`), never attacker-controlled, so no length-panic arises
      -- here; an oversized inner *dynamic* element fires its own guard via the
      -- threaded (`lazy = false`) element decode below.
      let rec decodeArrayValues? (arrayData : Bytes) :
          Nat -> Nat -> Except RevertData (List Value)
        | 0, _ => Except.ok []
        | remaining + 1, index => do
            let value ←
              match decodeValueAtWithFuel? fuel lazy arrayData index elementTy with
              | Except.ok v => Except.ok v
              | Except.error e =>
                  -- calldata (lazy) path: the enclosing branch's eager
                  -- head-area presence check guarantees bounds, so a failure
                  -- here is a value/inner validation failure that solc defers
                  -- to access time — substitute the deferred-invalid marker.
                  if lazy then
                    Except.ok (Value.calldataDeferredInvalid elementTy)
                  else
                    Except.error e
            let step ← abiArgOpt (Ty.abiHeadWords? elementTy)
            let rest ← decodeArrayValues? arrayData remaining (index + step)
            Except.ok (value :: rest)
      if Ty.isDynamicAbi elementTy then
        do
        let offset ← abiArgOpt (readWord? argData (wordBytes * headIndex))
        let step ← abiArgOpt (Ty.abiHeadWords? elementTy)
        if lazy && (readBytes? (argData.drop offset) 0
            (size * step * wordBytes)).isNone then
          Except.error RevertData.empty
        else do
          let values ← decodeArrayValues? (argData.drop offset) size 0
          Except.ok (Value.fixedArray values)
      else
        do
        -- Static-element fixed array `T[N] calldata`: the `N` element words are
        -- inline in the head. Eager presence check (solc `slt(sub(end,pos),N*32)`)
        -- so a truncated head still reverts eagerly; only a present-but-dirty
        -- element value is deferred to access time via the marker above.
        let step ← abiArgOpt (Ty.abiHeadWords? elementTy)
        if lazy && (readBytes? argData (wordBytes * headIndex)
            (size * step * wordBytes)).isNone then
          Except.error RevertData.empty
        else do
          let values ← decodeArrayValues? argData size headIndex
          Except.ok (Value.fixedArray values)
  | fuel + 1, lazy, argData, headIndex, Ty.tuple elementTys =>
      let rec decodeTupleValues? (tupleData : Bytes) :
          List Ty -> Nat -> Except RevertData (List Value)
        | [], _ => Except.ok []
        | ty :: tys, index => do
            let value ←
              match decodeValueAtWithFuel? fuel lazy tupleData index ty with
              | Except.ok v => Except.ok v
              | Except.error e =>
                  -- calldata (lazy) path: the eager head-area presence check
                  -- (either branch below) guarantees every member's head words
                  -- are present, so a failure here is a value/inner validation
                  -- failure that solc defers to access — substitute the marker.
                  -- Covers static value members (dirty bool/address/bytesN) of
                  -- a calldata struct, not just dynamic members.
                  if lazy then
                    Except.ok (Value.calldataDeferredInvalid ty)
                  else
                    Except.error e
            let step ← abiArgOpt (Ty.abiHeadWords? ty)
            let rest ← decodeTupleValues? tupleData tys (index + step)
            Except.ok (value :: rest)
      if Ty.listHasDynamicAbi elementTys then
        do
        let offset ← abiArgOpt (readWord? argData (wordBytes * headIndex))
        let headWords ← abiArgOpt (Ty.listAbiHeadWords? elementTys)
        -- Eager head-area presence (solc `slt(sub(end,offset), N*32)`); inner
        -- dynamic-member offsets are validated lazily on access for calldata.
        if lazy && (readBytes? (argData.drop offset) 0
            (headWords * wordBytes)).isNone then
          Except.error RevertData.empty
        else do
          let values ← decodeTupleValues? (argData.drop offset) elementTys 0
          Except.ok (Value.tuple values)
      else
        do
        -- Fully-static struct `S calldata` decoded inline in the head. Eager
        -- presence check so a truncated head still reverts eagerly; a
        -- present-but-dirty value member is deferred to access via the marker.
        let headWords ← abiArgOpt (Ty.listAbiHeadWords? elementTys)
        if lazy && (readBytes? argData (wordBytes * headIndex)
            (headWords * wordBytes)).isNone then
          Except.error RevertData.empty
        else do
          let values ← decodeTupleValues? argData elementTys headIndex
          Except.ok (Value.tuple values)
  -- `enumStorage` is a storage-layout-only type; it never appears in an ABI
  -- position (params/returns lower enums to `uint256` + `AbiCleanup.enum`).
  | _fuel + 1, _lazy, _, _, Ty.enumStorage _ => Except.error RevertData.empty

def decodeValueAt? (lazy : Bool) (argData : Bytes) (headIndex : Nat)
    (ty : Ty) : Except RevertData Value :=
  decodeValueAtWithFuel? (Ty.abiDecodeFuel ty) lazy argData headIndex ty

-- Each parameter carries its own `lazy` flag (calldata vs memory), threaded
-- from `decodeFunctionArgs?` via the param ABI cleanups.
def decodeArgsAux? (argData : Bytes) :
    List (Bool × Ty) -> Nat -> Except RevertData (List Value)
  | [], _ => Except.ok []
  | (lazy, ty) :: tys, index => do
      let value ← decodeValueAt? lazy argData index ty
      let headWords ← abiArgOpt (Ty.abiHeadWords? ty)
      let values ← decodeArgsAux? argData tys (index + headWords)
      Except.ok (value :: values)

def decodeArgsWith? (params : List (Bool × Ty)) (argData : Bytes) :
    Except RevertData (List Value) :=
  decodeArgsAux? argData params 0

-- Eager decode (all params non-lazy). Used for well-formed witness vectors and
-- any caller that is not the external calldata boundary. Collapses any decode
-- revert (empty or Panic 0x41) to `none`, preserving the historical `Option`
-- surface for witnesses.
def decodeArgs? (tys : List Ty) (argData : Bytes) :
    Option (List Value) :=
  match decodeArgsWith? (tys.map (fun ty => (false, ty))) argData with
  | Except.ok vs => some vs
  | Except.error _ => none

-- A calldata parameter (anything but a `memory`-location aggregate) defers
-- inner dynamic-element validation to access time; a `memoryEager` param is
-- validated eagerly, matching solc.
def AbiCleanup.decodeLazy : AbiCleanup -> Bool
  | AbiCleanup.memoryEager _ => false
  | _ => true

def decodeFunctionArgs? (function : FunctionDef)
    (argData : Bytes) : Except RevertData (List Value) := do
  let tys := function.params.map BindingDecl.ty
  let lazyFlags :=
    if function.paramAbiCleanups.length == tys.length then
      function.paramAbiCleanups.map AbiCleanup.decodeLazy
    else
      tys.map (fun _ => true)
  let values ← decodeArgsWith? (lazyFlags.zip tys) argData
  if function.paramAbiCleanups.isEmpty then
    Except.ok values
  else
    abiArgOpt (AbiCleanups.lazyParamValues function.paramAbiCleanups values)

def decodeFunctionArgsStrict? (function : FunctionDef)
    (argData : Bytes) : Option (List Value) := do
  let values ← decodeArgs? (function.params.map BindingDecl.ty) argData
  if AbiCleanups.acceptOrUnspecified function.paramAbiCleanups values then
    some values
  else
    none

def encodeArgs? (tys : List Ty) (values : List Value) : Option Bytes :=
  encodeValues? tys values

def calldataFor? (function : FunctionDef) (args : List Value) :
    Option Bytes := do
  let selector ← function.selector?
  let encodedArgs ← encodeArgs? (function.params.map BindingDecl.ty) args
  some (encodeSelector selector ++ encodedArgs)

def panicSelector : Word := 0x4e487b71

def errorSelector : Word := 0x08c379a0

def stringBytes (text : String) : Bytes :=
  text.toUTF8.toList.map UInt8.toNat

def Contract.findErrorDecl? (contract : Contract)
    (name : String) : Option ErrorDecl :=
  contract.errorDecls.find? (fun error => error.name == name)

def Contract.encodeRevertData? (contract : Contract)
    (revert : RevertData) : Option Bytes :=
  match revert with
  | RevertData.empty => some []
  | RevertData.panic code =>
      match encodeValues? [Ty.uint256] [Value.word code] with
      | some payload => some (encodeSelector panicSelector ++ payload)
      | none => none
  | RevertData.error reason =>
      match encodeValues? [Ty.bytesCalldata] [Value.bytes (stringBytes reason)] with
      | some payload => some (encodeSelector errorSelector ++ payload)
      | none => none
  | RevertData.custom name values => do
      let decl ← Contract.findErrorDecl? contract name
      let payload ← encodeValues? decl.fields values
      some (encodeSelector decl.selector ++ payload)
  | RevertData.raw bytes => some (normalizeBytes bytes)

structure AbiCallResult where
  success : Bool
  output : Bytes
  state : State
  deriving Repr

inductive AbiResultEncodingMode where
  | returned
  | reverted
  deriving Repr, BEq

inductive AbiEntryKind where
  | messageCall
  | transaction
  deriving Repr, BEq

inductive AbiDispatchKind where
  | functionSelector
  | receive
  | fallback
  | missing
  deriving Repr, BEq

def encodeReturnOutputForDispatch? (dispatchKind : AbiDispatchKind)
    (returns : List BindingDecl) (values : List Value) :
    Option Bytes :=
  match dispatchKind, returns, values with
  | AbiDispatchKind.fallback, [], [] => some []
  | AbiDispatchKind.fallback,
      [{ ty := Ty.bytesCalldata, name := _ }], [Value.bytes bytes] =>
      some (normalizeBytes bytes)
  | _, _, _ => encodeValues? (returns.map BindingDecl.ty) values

def AbiCallResult.clearTransient (result : AbiCallResult) : AbiCallResult :=
  { result with state := result.state.clearTransient }

def Contract.revertedCall? (contract : Contract) (state : State)
    (revert : RevertData) : Option AbiCallResult := do
  let output ← Contract.encodeRevertData? contract revert
  some { success := false, output, state := state }

def Contract.revertedEmptyCall? (contract : Contract)
    (state : State) : Option AbiCallResult :=
  Contract.revertedCall? contract state RevertData.empty

def Contract.rejectedValueCall? (contract : Contract)
    (state : State) : Option AbiCallResult :=
  Contract.revertedEmptyCall? contract state

def Contract.missingFallbackCall? (contract : Contract)
    (state : State) : Option AbiCallResult :=
  Contract.revertedEmptyCall? contract state

def Contract.findReceive? (contract : Contract) : Option FunctionDef :=
  contract.findFunctionByName? "__receive"

def Contract.findFallback? (contract : Contract) : Option FunctionDef :=
  contract.findFunctionByName? "__fallback"

def FunctionDef.fallbackArgs? (function : FunctionDef)
    (calldata : Bytes) : Option (List Value) :=
  match function.params with
  | [] => some []
  | [param] =>
      match param.ty with
      | Ty.bytesCalldata => some [Value.bytes calldata]
      | _ => none
  | _ => none

def FunctionDef.encodeFallbackOutput? (function : FunctionDef)
    (values : List Value) : Option Bytes :=
  match function.returns, values with
  | [], [] => some []
  | [{ ty := Ty.bytesCalldata, name := _ }], [Value.bytes bytes] =>
      some (normalizeBytes bytes)
  | _, _ => encodeValues? (function.returns.map BindingDecl.ty) values

def Contract.callContextAtWithBase (contract : Contract)
    (base : Context) (self sender value : Word) (calldata : Bytes) :
    Context :=
  { base with
    storageFields := contract.storageFields
    immutableFields := contract.immutableFields
    eventDecls := contract.eventDecls
    checked := true
    construction := false
    calldata := normalizeBytes calldata
    self := SolidCore.Solidity.Shared.norm self
    sender := SolidCore.Solidity.Shared.norm sender
    value := SolidCore.Solidity.Shared.norm value }

def Contract.callContextAt (contract : Contract)
    (self sender value : Word) (calldata : Bytes) : Context :=
  Contract.callContextAtWithBase contract contract.context self sender value
    calldata

def Contract.callContext (contract : Contract)
    (sender value : Word) (calldata : Bytes) : Context :=
  Contract.callContextAt contract 0 sender value calldata

def Contract.callFallbackAtFromWithContext? (fuel : Nat)
    (contract : Contract) (base : Context) (state : State)
    (self sender value : Word) (calldata : Bytes) : Option AbiCallResult :=
  match Contract.findFallback? contract with
  | some function => do
      let args ← FunctionDef.fallbackArgs? function calldata
      let context :=
        Contract.callContextAtWithBase contract base self sender value calldata
      if function.acceptsValue value then
        match FunctionDef.call? fuel contract.table context function state args with
        | some (CallResult.returned state' values) => do
            let output ← FunctionDef.encodeFallbackOutput? function values
            some { success := true, output, state := state' }
        | some (CallResult.reverted state' revert) => do
            let output ← Contract.encodeRevertData? contract revert
            some { success := false, output, state := state' }
        | none => none
      else
        Contract.rejectedValueCall? contract state
  | none =>
      Contract.missingFallbackCall? contract state

def Contract.callFallbackAtFrom? (fuel : Nat) (contract : Contract)
    (state : State) (self sender value : Word) (calldata : Bytes) :
    Option AbiCallResult :=
  Contract.callFallbackAtFromWithContext?
    fuel contract contract.context state self sender value calldata

def Contract.callFallbackFrom? (fuel : Nat) (contract : Contract)
    (state : State) (sender value : Word) (calldata : Bytes) :
    Option AbiCallResult :=
  Contract.callFallbackAtFrom? fuel contract state 0 sender value calldata

def Contract.callFallback? (fuel : Nat) (contract : Contract)
    (state : State) (calldata : Bytes) : Option AbiCallResult :=
  Contract.callFallbackFrom? fuel contract state 0 0 calldata

def Contract.callReceiveOrFallbackAtFromWithContext? (fuel : Nat)
    (contract : Contract) (base : Context) (state : State)
    (self sender value : Word) (calldata : Bytes) : Option AbiCallResult :=
  if calldata.isEmpty then
    match Contract.findReceive? contract with
    | some function =>
        let context :=
          Contract.callContextAtWithBase contract base self sender value []
        if function.acceptsValue value then
          match FunctionDef.call? fuel contract.table context function state [] with
          | some (CallResult.returned state' values) => do
              let output ← encodeValues?
                (function.returns.map BindingDecl.ty) values
              some { success := true, output, state := state' }
          | some (CallResult.reverted state' revert) => do
              let output ← Contract.encodeRevertData? contract revert
              some { success := false, output, state := state' }
          | none => none
        else
          Contract.rejectedValueCall? contract state
    | none =>
        Contract.callFallbackAtFromWithContext? fuel contract base state
          self sender value calldata
  else
    Contract.callFallbackAtFromWithContext? fuel contract base state
      self sender value calldata

def Contract.callReceiveOrFallbackAtFrom? (fuel : Nat) (contract : Contract)
    (state : State) (self sender value : Word) (calldata : Bytes) :
    Option AbiCallResult :=
  Contract.callReceiveOrFallbackAtFromWithContext?
    fuel contract contract.context state self sender value calldata

def Contract.callReceiveOrFallbackFrom? (fuel : Nat) (contract : Contract)
    (state : State) (sender value : Word) (calldata : Bytes) :
    Option AbiCallResult :=
  Contract.callReceiveOrFallbackAtFrom? fuel contract state 0 sender value
    calldata

def Contract.callReceiveOrFallback? (fuel : Nat) (contract : Contract)
    (state : State) (calldata : Bytes) : Option AbiCallResult :=
  Contract.callReceiveOrFallbackFrom? fuel contract state 0 0 calldata

def Contract.callCalldataAtFromWithContext? (fuel : Nat)
    (contract : Contract) (base : Context) (state : State)
    (self sender value : Word) (calldata : Bytes) : Option AbiCallResult := do
  match readSelector? calldata with
  | some selector =>
      match contract.findFunctionBySelector? selector with
      | some function =>
          match
            decodeFunctionArgs? function (calldata.drop selectorBytes)
          with
          | Except.ok args =>
              let context :=
                Contract.callContextAtWithBase contract base self sender value
                  calldata
              if function.acceptsValue value then
                match function.call? fuel contract.table context state args with
                | some (CallResult.returned state' values) => do
                    let output ← encodeValues?
                      (function.returns.map BindingDecl.ty) values
                    some { success := true, output, state := state' }
                | some (CallResult.reverted state' revert) => do
                    let output ← Contract.encodeRevertData? contract revert
                    some { success := false, output, state := state' }
                | none => none
              else
                Contract.rejectedValueCall? contract state
          -- A decode revert: `RevertData.empty` (bounds/dirty) is the empty
          -- `revert(0,0)`; `RevertData.memoryAllocationTooLarge` is Panic(0x41)
          -- for an eager `memory` reference param with an oversized length.
          | Except.error revert => Contract.revertedCall? contract state revert
      | none =>
          Contract.callFallbackAtFromWithContext? fuel contract base state
            self sender value calldata
  | none =>
      Contract.callReceiveOrFallbackAtFromWithContext? fuel contract base state
        self sender value calldata

def Contract.callCalldataAtFrom? (fuel : Nat) (contract : Contract)
    (state : State) (self sender value : Word) (calldata : Bytes) :
    Option AbiCallResult :=
  Contract.callCalldataAtFromWithContext?
    fuel contract contract.context state self sender value calldata

def Contract.callCalldataFromWithContext? (fuel : Nat) (contract : Contract)
    (base : Context) (state : State) (sender value : Word)
    (calldata : Bytes) : Option AbiCallResult :=
  Contract.callCalldataAtFromWithContext?
    fuel contract base state 0 sender value calldata

def Contract.callCalldataFrom? (fuel : Nat) (contract : Contract)
    (state : State) (sender value : Word) (calldata : Bytes) :
    Option AbiCallResult :=
  Contract.callCalldataAtFrom? fuel contract state 0 sender value calldata

def Contract.callCalldataAtWithContext? (fuel : Nat) (contract : Contract)
    (base : Context) (state : State) (self : Word) (calldata : Bytes) :
    Option AbiCallResult :=
  Contract.callCalldataAtFromWithContext?
    fuel contract base state self 0 0 calldata

def Contract.callCalldataAt? (fuel : Nat) (contract : Contract)
    (state : State) (self : Word) (calldata : Bytes) :
    Option AbiCallResult :=
  Contract.callCalldataAtFrom? fuel contract state self 0 0 calldata

def Contract.callCalldataWithContext? (fuel : Nat) (contract : Contract)
    (base : Context) (state : State) (calldata : Bytes) :
    Option AbiCallResult :=
  Contract.callCalldataFromWithContext? fuel contract base state 0 0 calldata

def Contract.callCalldata? (fuel : Nat) (contract : Contract)
    (state : State) (calldata : Bytes) : Option AbiCallResult :=
  Contract.callCalldataFrom? fuel contract state 0 0 calldata

/-! ### #186 closed-world self-dispatch (`address(this).f()`).

A call whose target is the executing contract's own address is closed-world: the
model has the contract's code, so it routes through the contract's OWN external
dispatcher (`Contract.callCalldataAtFromWithContext?`) against the LIVE caller
state in a proper sub-frame, rather than emitting an open-world `Query.external`.
The capability is packaged as a `SelfDispatchFn` and installed on the entry
`Context` by the closed-world call entries below; the interpreter consults it at
its external-call emit sites when `target == context.self`. -/

/-- The self-dispatch hook (see `SelfDispatchFn`). The `Nat` argument is BOTH the
    nesting-depth bound (structural recursion — each nested self-call decrements
    it, so mutual self-recursion terminates) AND the dispatch fuel budget threaded
    into `Contract.callCalldataAtFromWithContext?`. It is baked in at installation
    time, so the hook value does NOT depend on the caller's remaining statement
    fuel (keeping `Stmt.eval` fuel-monotone). `msg.sender` in the sub-frame is the
    contract's own address (`selfAddr`), matching a real CALL to `address(this)`. -/
def selfDispatchHook : Nat → Contract → Word → SelfDispatchFn
  | 0, _, _ => fun _ _ _ _ => none
  | Nat.succ depth, contract, selfAddr => fun sender value calldata state =>
      let base : Context :=
        { contract.context with
          selfDispatch? := some (selfDispatchHook depth contract selfAddr) }
      (Contract.callCalldataAtFromWithContext? (Nat.succ depth) contract base state
        selfAddr sender value calldata).map
        (fun result => (result.success, result.output, result.state))

/-- Closed-world own-call resolution with the self-dispatch hook installed on the
    entry context (own-call self address `0`). Mirrors `Contract.call` but routes
    `address(this)` calls through `selfDispatchHook` instead of the open-world
    responder. -/
def Contract.callWithSelfDispatch (fuel : Nat) (contract : Contract)
    (target : CallTarget) (state : State) (args : List Value) :
    Option (SolI CallResult) :=
  match contract.resolveCallFunction? target args with
  | some function =>
      function.call fuel contract.table
        { contract.context with
          selfDispatch? := some (selfDispatchHook fuel contract 0) }
        state args
  | none => none

/-- Fail-closed fold of `Contract.callWithSelfDispatch` (empty responder: only
    self-targeted external calls are answered, in-model; any OTHER external call
    still fails closed). -/
def Contract.callSelfDispatch? (fuel : Nat) (contract : Contract)
    (target : CallTarget) (state : State) (args : List Value) : Option CallResult :=
  (Contract.callWithSelfDispatch fuel contract target state args).bind fun tree =>
    match SolI.runWith [] tree with
    | .ok result => some result
    | .error _ => none

/-- Transaction-scoped twin of `Contract.callWithSelfDispatch` (clears transient
    state before, maps `clearTransient` over the result). -/
def Contract.callTransactionWithSelfDispatch (fuel : Nat) (contract : Contract)
    (target : CallTarget) (state : State) (args : List Value) :
    Option (SolI CallResult) :=
  (Contract.callWithSelfDispatch fuel contract target state.clearTransient args).map
    (Functor.map CallResult.clearTransient)

def Contract.callTransactionSelfDispatch? (fuel : Nat) (contract : Contract)
    (target : CallTarget) (state : State) (args : List Value) : Option CallResult :=
  (Contract.callTransactionWithSelfDispatch fuel contract target state args).bind
    fun tree =>
      match SolI.runWith [] tree with
      | .ok result => some result
      | .error _ => none

def Contract.callCalldataTransactionAtFromWithContext? (fuel : Nat)
    (contract : Contract) (base : Context) (state : State)
    (self sender value : Word) (calldata : Bytes) :
    Option AbiCallResult := do
  let result ←
    Contract.callCalldataAtFromWithContext?
      fuel contract base state.clearTransient self sender value calldata
  some result.clearTransient

def Contract.callCalldataTransactionAtFrom? (fuel : Nat)
    (contract : Contract) (state : State) (self sender value : Word)
    (calldata : Bytes) :
    Option AbiCallResult := do
  Contract.callCalldataTransactionAtFromWithContext?
    fuel contract contract.context state self sender value calldata

def Contract.callCalldataTransactionFromWithContext? (fuel : Nat)
    (contract : Contract) (base : Context) (state : State)
    (sender value : Word) (calldata : Bytes) : Option AbiCallResult :=
  Contract.callCalldataTransactionAtFromWithContext?
    fuel contract base state 0 sender value calldata

def Contract.callCalldataTransactionFrom? (fuel : Nat) (contract : Contract)
    (state : State) (sender value : Word) (calldata : Bytes) :
    Option AbiCallResult :=
  Contract.callCalldataTransactionAtFrom? fuel contract state 0 sender value
    calldata

def Contract.callCalldataTransactionAtWithContext? (fuel : Nat)
    (contract : Contract) (base : Context) (state : State)
    (self : Word) (calldata : Bytes) : Option AbiCallResult :=
  Contract.callCalldataTransactionAtFromWithContext?
    fuel contract base state self 0 0 calldata

def Contract.callCalldataTransactionAt? (fuel : Nat) (contract : Contract)
    (state : State) (self : Word) (calldata : Bytes) :
    Option AbiCallResult :=
  Contract.callCalldataTransactionAtFrom? fuel contract state self 0 0
    calldata

def Contract.callCalldataTransactionWithContext? (fuel : Nat)
    (contract : Contract) (base : Context) (state : State)
    (calldata : Bytes) : Option AbiCallResult :=
  Contract.callCalldataTransactionFromWithContext?
    fuel contract base state 0 0 calldata

def Contract.callCalldataTransaction? (fuel : Nat) (contract : Contract)
    (state : State) (calldata : Bytes) : Option AbiCallResult :=
  Contract.callCalldataTransactionFrom? fuel contract state 0 0 calldata

def AbiEntryKind.executionState (kind : AbiEntryKind) (state : State) :
    State :=
  match kind with
  | AbiEntryKind.messageCall => state
  | AbiEntryKind.transaction => state.clearTransient

def Contract.callCalldataEntryAtFromWithContext? (kind : AbiEntryKind)
    (fuel : Nat) (contract : Contract) (base : Context) (state : State)
    (self sender value : Word) (calldata : Bytes) :
    Option AbiCallResult :=
  match kind with
  | AbiEntryKind.messageCall =>
      Contract.callCalldataAtFromWithContext?
        fuel contract base state self sender value calldata
  | AbiEntryKind.transaction =>
      Contract.callCalldataTransactionAtFromWithContext?
        fuel contract base state self sender value calldata

/-! ## Stage 1e — `SolI`-tree-returning twins of the ABI dispatch.

These mirror the `?`/`Option`-returning entry points above, but return the
execution as an interaction tree (`Option (SolI AbiCallResult)`).  The static
decode of the *entry* calldata stays outside the tree (the outer `Option`
encodes static absence); the result-encode is applied inside the tree via
`bind`.  A post-execution *output-encode* failure (which the `?` versions turn
into `none`) is lifted into the tree as a throw — folding the tree through
`SolI.run` in the frozen `?` adapters reproduces `none` exactly, so behavior is
preserved.  The `?` entry points above are left untouched (they already fold at
`FunctionDef.call?`); these twins are what the manifest consumes at stage 3. -/

/-- Wrap a static `Option AbiCallResult` result as a degenerate `pure` tree. -/
def pureAbi (r : AbiCallResult) : SolI AbiCallResult := pure r

/-- Lift an output-encode `Option AbiCallResult` into the tree: `none` (encode
    failure) becomes a throw so the frozen `?` adapter folds it back to `none`. -/
def liftAbiEncode : Option AbiCallResult → SolI AbiCallResult
  | some r => pure r
  | none => .done (.error SolidityFailure.outOfFuel)

def Contract.encodeCalldataResult? (contract : Contract) (function : FunctionDef) :
    CallResult → Option AbiCallResult
  | CallResult.returned state' values => do
      let output ← encodeValues? (function.returns.map BindingDecl.ty) values
      some { success := true, output, state := state' }
  | CallResult.reverted state' revert => do
      let output ← Contract.encodeRevertData? contract revert
      some { success := false, output, state := state' }

def Contract.encodeFallbackResult? (contract : Contract) (function : FunctionDef) :
    CallResult → Option AbiCallResult
  | CallResult.returned state' values => do
      let output ← FunctionDef.encodeFallbackOutput? function values
      some { success := true, output, state := state' }
  | CallResult.reverted state' revert => do
      let output ← Contract.encodeRevertData? contract revert
      some { success := false, output, state := state' }

def Contract.callFallbackAtFromWithContext (fuel : Nat)
    (contract : Contract) (base : Context) (state : State)
    (self sender value : Word) (calldata : Bytes) :
    Option (SolI AbiCallResult) :=
  match Contract.findFallback? contract with
  | some function => do
      let args ← FunctionDef.fallbackArgs? function calldata
      let context :=
        Contract.callContextAtWithBase contract base self sender value calldata
      if function.acceptsValue value then
        (FunctionDef.call fuel contract.table context function state args).map fun tree =>
          tree.bind fun cr =>
            liftAbiEncode (Contract.encodeFallbackResult? contract function cr)
      else
        (Contract.rejectedValueCall? contract state).map pureAbi
  | none =>
      (Contract.missingFallbackCall? contract state).map pureAbi

def Contract.callReceiveOrFallbackAtFromWithContext (fuel : Nat)
    (contract : Contract) (base : Context) (state : State)
    (self sender value : Word) (calldata : Bytes) : Option (SolI AbiCallResult) :=
  if calldata.isEmpty then
    match Contract.findReceive? contract with
    | some function =>
        let context :=
          Contract.callContextAtWithBase contract base self sender value []
        if function.acceptsValue value then
          (FunctionDef.call fuel contract.table context function state []).map fun tree =>
            tree.bind fun cr =>
              liftAbiEncode (Contract.encodeCalldataResult? contract function cr)
        else
          (Contract.rejectedValueCall? contract state).map pureAbi
    | none =>
        Contract.callFallbackAtFromWithContext fuel contract base state
          self sender value calldata
  else
    Contract.callFallbackAtFromWithContext fuel contract base state
      self sender value calldata

def Contract.callCalldataAtFromWithContext (fuel : Nat)
    (contract : Contract) (base : Context) (state : State)
    (self sender value : Word) (calldata : Bytes) :
    Option (SolI AbiCallResult) := do
  match readSelector? calldata with
  | some selector =>
      match contract.findFunctionBySelector? selector with
      | some function =>
          match
            decodeFunctionArgs? function (calldata.drop selectorBytes)
          with
          | Except.ok args =>
              let context :=
                Contract.callContextAtWithBase contract base self sender value
                  calldata
              if function.acceptsValue value then
                (function.call fuel contract.table context state args).map fun tree =>
                  tree.bind fun cr =>
                    liftAbiEncode
                      (Contract.encodeCalldataResult? contract function cr)
              else
                (Contract.rejectedValueCall? contract state).map pureAbi
          -- Panic(0x41) for an eager oversized-length ref param, else empty.
          | Except.error revert =>
              (Contract.revertedCall? contract state revert).map pureAbi
      | none =>
          Contract.callFallbackAtFromWithContext fuel contract base state
            self sender value calldata
  | none =>
      Contract.callReceiveOrFallbackAtFromWithContext fuel contract base state
        self sender value calldata

def Contract.callCalldataAtFrom (fuel : Nat) (contract : Contract)
    (state : State) (self sender value : Word) (calldata : Bytes) :
    Option (SolI AbiCallResult) :=
  Contract.callCalldataAtFromWithContext
    fuel contract contract.context state self sender value calldata

def Contract.callCalldataFromWithContext (fuel : Nat) (contract : Contract)
    (base : Context) (state : State) (sender value : Word)
    (calldata : Bytes) : Option (SolI AbiCallResult) :=
  Contract.callCalldataAtFromWithContext
    fuel contract base state 0 sender value calldata

def Contract.callCalldataFrom (fuel : Nat) (contract : Contract)
    (state : State) (sender value : Word) (calldata : Bytes) :
    Option (SolI AbiCallResult) :=
  Contract.callCalldataAtFrom fuel contract state 0 sender value calldata

def Contract.callCalldataAtWithContext (fuel : Nat) (contract : Contract)
    (base : Context) (state : State) (self : Word) (calldata : Bytes) :
    Option (SolI AbiCallResult) :=
  Contract.callCalldataAtFromWithContext
    fuel contract base state self 0 0 calldata

def Contract.callCalldataAt (fuel : Nat) (contract : Contract)
    (state : State) (self : Word) (calldata : Bytes) :
    Option (SolI AbiCallResult) :=
  Contract.callCalldataAtFrom fuel contract state self 0 0 calldata

def Contract.callCalldataWithContext (fuel : Nat) (contract : Contract)
    (base : Context) (state : State) (calldata : Bytes) :
    Option (SolI AbiCallResult) :=
  Contract.callCalldataFromWithContext fuel contract base state 0 0 calldata

def Contract.callCalldata (fuel : Nat) (contract : Contract)
    (state : State) (calldata : Bytes) : Option (SolI AbiCallResult) :=
  Contract.callCalldataFrom fuel contract state 0 0 calldata

/-- Transaction-scoped calldata dispatch as a tree: clear transient state
    before, and `.clearTransient` mapped over the result inside the tree. -/
def Contract.callCalldataTransactionAtFromWithContext (fuel : Nat)
    (contract : Contract) (base : Context) (state : State)
    (self sender value : Word) (calldata : Bytes) :
    Option (SolI AbiCallResult) :=
  (Contract.callCalldataAtFromWithContext
      fuel contract base state.clearTransient self sender value calldata).map
    (Functor.map AbiCallResult.clearTransient)

def Contract.callCalldataTransactionAtFrom (fuel : Nat)
    (contract : Contract) (state : State) (self sender value : Word)
    (calldata : Bytes) : Option (SolI AbiCallResult) :=
  Contract.callCalldataTransactionAtFromWithContext
    fuel contract contract.context state self sender value calldata

def Contract.callCalldataTransactionFromWithContext (fuel : Nat)
    (contract : Contract) (base : Context) (state : State)
    (sender value : Word) (calldata : Bytes) : Option (SolI AbiCallResult) :=
  Contract.callCalldataTransactionAtFromWithContext
    fuel contract base state 0 sender value calldata

def Contract.callCalldataTransactionFrom (fuel : Nat) (contract : Contract)
    (state : State) (sender value : Word) (calldata : Bytes) :
    Option (SolI AbiCallResult) :=
  Contract.callCalldataTransactionAtFrom fuel contract state 0 sender value
    calldata

def Contract.callCalldataTransactionAtWithContext (fuel : Nat)
    (contract : Contract) (base : Context) (state : State)
    (self : Word) (calldata : Bytes) : Option (SolI AbiCallResult) :=
  Contract.callCalldataTransactionAtFromWithContext
    fuel contract base state self 0 0 calldata

def Contract.callCalldataTransactionAt (fuel : Nat) (contract : Contract)
    (state : State) (self : Word) (calldata : Bytes) :
    Option (SolI AbiCallResult) :=
  Contract.callCalldataTransactionAtFrom fuel contract state self 0 0
    calldata

def Contract.callCalldataTransactionWithContext (fuel : Nat)
    (contract : Contract) (base : Context) (state : State)
    (calldata : Bytes) : Option (SolI AbiCallResult) :=
  Contract.callCalldataTransactionFromWithContext
    fuel contract base state 0 0 calldata

def Contract.callCalldataTransaction (fuel : Nat) (contract : Contract)
    (state : State) (calldata : Bytes) : Option (SolI AbiCallResult) :=
  Contract.callCalldataTransactionFrom fuel contract state 0 0 calldata

def Contract.callCalldataEntryAtFromWithContext (kind : AbiEntryKind)
    (fuel : Nat) (contract : Contract) (base : Context) (state : State)
    (self sender value : Word) (calldata : Bytes) :
    Option (SolI AbiCallResult) :=
  match kind with
  | AbiEntryKind.messageCall =>
      Contract.callCalldataAtFromWithContext
        fuel contract base state self sender value calldata
  | AbiEntryKind.transaction =>
      Contract.callCalldataTransactionAtFromWithContext
        fuel contract base state self sender value calldata

end ABI
end Source
end Solidity
end SolidCore

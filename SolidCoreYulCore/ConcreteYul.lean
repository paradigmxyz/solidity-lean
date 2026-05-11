import SolidCoreYulCore.FullYul

namespace SolidCoreYulCore
namespace ConcreteYul

abbrev Byte := Nat
abbrev Bytes := List Byte

def byteModulus : Nat := 256

def normByte (byte : Nat) : Byte :=
  byte % byteModulus

theorem normByte_normByte (byte : Nat) :
    normByte (normByte byte) = normByte byte := by
  simp [normByte, byteModulus]

theorem norm_norm (value : Word) :
    norm (norm value) = norm value := by
  simp [norm, wordModulus]

def zeroBytes : Nat -> Bytes
  | 0 => []
  | n + 1 => 0 :: zeroBytes n

def byteAt : Bytes -> Nat -> Byte
  | [], _ => 0
  | byte :: _, 0 => normByte byte
  | _ :: rest, ix + 1 => byteAt rest ix

theorem byteAt_eq_getElem?_getD (bytes : Bytes) (offset : Nat) :
    byteAt bytes offset = normByte ((bytes[offset]?).getD 0) := by
  induction bytes generalizing offset with
  | nil =>
      simp [byteAt, normByte, byteModulus]
  | cons byte rest ih =>
      cases offset with
      | zero =>
          simp [byteAt]
      | succ offset =>
          simpa [byteAt] using ih offset

theorem byteAt_map_range (f : Nat -> Byte) {size offset : Nat}
    (hOffset : offset < size) :
    byteAt ((List.range size).map f) offset = normByte (f offset) := by
  rw [byteAt_eq_getElem?_getD]
  have hGet :
      ((List.range size).map f)[offset]? = some (f offset) := by
    rw [List.getElem?_map, List.getElem?_range hOffset]
    rfl
  simp [hGet]

theorem normByte_byteAt (bytes : Bytes) (offset : Nat) :
    normByte (byteAt bytes offset) = byteAt bytes offset := by
  induction bytes generalizing offset with
  | nil =>
      simp [byteAt, normByte, byteModulus]
  | cons byte rest ih =>
      cases offset with
      | zero =>
          simp [byteAt, normByte_normByte]
      | succ offset =>
          simpa [byteAt] using ih offset

def readBytes (bytes : Bytes) (offset size : Nat) : Bytes :=
  (List.range size).map (fun ix => byteAt bytes (offset + ix))

theorem readBytes_length (bytes : Bytes) (offset size : Nat) :
    (readBytes bytes offset size).length = size := by
  simp [readBytes]

theorem readBytes_map_normByte (bytes : Bytes) (offset size : Nat) :
    (readBytes bytes offset size).map normByte =
      readBytes bytes offset size := by
  simp [readBytes, List.map_map, normByte_byteAt]

def writeByte : Bytes -> Nat -> Byte -> Bytes
  | [], 0, byte => [normByte byte]
  | [], ix + 1, byte => 0 :: writeByte [] ix byte
  | _ :: rest, 0, byte => normByte byte :: rest
  | head :: rest, ix + 1, byte => normByte head :: writeByte rest ix byte

theorem byteAt_writeByte_same
    (bytes : Bytes) (offset byte : Nat) :
    byteAt (writeByte bytes offset byte) offset = normByte byte := by
  induction offset generalizing bytes with
  | zero =>
      cases bytes <;> simp [writeByte, byteAt, normByte_normByte]
  | succ offset ih =>
      cases bytes <;> simp [writeByte, byteAt, ih]

theorem byteAt_writeByte_before
    (bytes : Bytes) (writeOffset byte readOffset : Nat)
    (hBefore : readOffset < writeOffset) :
    byteAt (writeByte bytes writeOffset byte) readOffset =
      byteAt bytes readOffset := by
  induction writeOffset generalizing bytes readOffset with
  | zero =>
      omega
  | succ writeOffset ih =>
      cases readOffset with
      | zero =>
          cases bytes <;>
            simp [writeByte, byteAt, normByte, byteModulus]
      | succ readOffset =>
          cases bytes with
          | nil =>
              simpa [writeByte, byteAt] using
                ih [] readOffset (by omega)
          | cons head rest =>
              simpa [writeByte, byteAt] using
                ih rest readOffset (by omega)

def writeBytes (bytes : Bytes) (offset : Nat) : Bytes -> Bytes
  | [] => bytes
  | byte :: rest => writeBytes (writeByte bytes offset byte) (offset + 1) rest

theorem byteAt_writeBytes_before
    (bytes : Bytes) (writeOffset : Nat) (newBytes : Bytes)
    (readOffset : Nat) (hBefore : readOffset < writeOffset) :
    byteAt (writeBytes bytes writeOffset newBytes) readOffset =
      byteAt bytes readOffset := by
  induction newBytes generalizing bytes writeOffset with
  | nil =>
      rfl
  | cons byte rest ih =>
      calc
        byteAt (writeBytes (writeByte bytes writeOffset byte)
            (writeOffset + 1) rest) readOffset
            = byteAt (writeByte bytes writeOffset byte) readOffset := by
              exact ih (writeByte bytes writeOffset byte)
                (writeOffset + 1) (by omega)
        _ = byteAt bytes readOffset :=
              byteAt_writeByte_before bytes writeOffset byte readOffset
                hBefore

theorem byteAt_writeBytes_start
    (bytes : Bytes) (offset byte : Nat) (rest : Bytes) :
    byteAt (writeBytes bytes offset (byte :: rest)) offset =
      normByte byte := by
  calc
    byteAt (writeBytes (writeByte bytes offset byte) (offset + 1) rest)
        offset
        = byteAt (writeByte bytes offset byte) offset := by
          exact byteAt_writeBytes_before (writeByte bytes offset byte)
            (offset + 1) rest offset (by omega)
    _ = normByte byte := byteAt_writeByte_same bytes offset byte

theorem readBytes_writeBytes_one
    (bytes : Bytes) (offset byte : Nat) (rest : Bytes) :
    readBytes (writeBytes bytes offset (byte :: rest)) offset 1 =
      [normByte byte] := by
  simp [readBytes, byteAt_writeBytes_start]

theorem readBytes_writeByte_one
    (bytes : Bytes) (offset byte : Nat) :
    readBytes (writeByte bytes offset byte) offset 1 =
      [normByte byte] := by
  simp [readBytes, byteAt_writeByte_same]

theorem readBytes_succ
    (bytes : Bytes) (offset size : Nat) :
    readBytes bytes offset (size + 1) =
      byteAt bytes offset :: readBytes bytes (offset + 1) size := by
  unfold readBytes
  rw [show size + 1 = 1 + size by omega, List.range_add]
  simp [Nat.add_comm, Nat.add_left_comm]

theorem readBytes_writeBytes_same
    (bytes : Bytes) (offset : Nat) (newBytes : Bytes) :
    readBytes (writeBytes bytes offset newBytes) offset newBytes.length =
      newBytes.map normByte := by
  induction newBytes generalizing bytes offset with
  | nil =>
      simp [readBytes, writeBytes]
  | cons byte rest ih =>
      change
        readBytes (writeBytes bytes offset (byte :: rest)) offset
            (rest.length + 1) =
          normByte byte :: rest.map normByte
      rw [readBytes_succ]
      change
        byteAt (writeBytes (writeByte bytes offset byte) (offset + 1)
            rest) offset ::
          readBytes (writeBytes (writeByte bytes offset byte)
            (offset + 1) rest) (offset + 1) rest.length =
            normByte byte :: rest.map normByte
      congr
      · rw [byteAt_writeBytes_before (writeByte bytes offset byte)
          (offset + 1) rest offset (by omega)]
        rw [byteAt_writeByte_same]
      · exact ih (writeByte bytes offset byte) (offset + 1)

def wordByteBE (word ix : Word) : Byte :=
  normByte (norm word / (byteModulus ^ (31 - ix)))

theorem normByte_wordByteBE (word ix : Word) :
    normByte (wordByteBE word ix) = wordByteBE word ix := by
  simp [wordByteBE, normByte_normByte]

def wordToBytes32 (word : Word) : Bytes :=
  (List.range 32).map (fun ix => wordByteBE word ix)

theorem wordToBytes32_length (word : Word) :
    (wordToBytes32 word).length = 32 := by
  simp [wordToBytes32]

theorem wordToBytes32_map_normByte (word : Word) :
    (wordToBytes32 word).map normByte = wordToBytes32 word := by
  simp [wordToBytes32, normByte_wordByteBE]

theorem readBytes_wordToBytes32_zero (word : Word) :
    readBytes (wordToBytes32 word) 0 32 = wordToBytes32 word := by
  simp [readBytes, wordToBytes32]
  intro ix hIx
  exact
    (byteAt_map_range (fun ix => wordByteBE word ix)
      (size := 32) (offset := ix) hIx).trans
        (normByte_wordByteBE word ix)

def bytesToNat (bytes : Bytes) : Nat :=
  bytes.foldl (fun acc byte => acc * byteModulus + normByte byte) 0

theorem norm_decode_step (acc byte : Nat) :
    norm (norm acc * byteModulus + normByte byte) =
      norm (acc * byteModulus + normByte byte) := by
  simp [norm, normByte, Nat.add_mod, Nat.mul_mod]

theorem foldWord_eq_norm_foldNat (bytes : Bytes) (acc : Nat) :
    bytes.foldl (fun acc byte => norm (acc * byteModulus + normByte byte))
        (norm acc) =
      norm (bytes.foldl
        (fun acc byte => acc * byteModulus + normByte byte) acc) := by
  induction bytes generalizing acc with
  | nil =>
      simp
  | cons byte rest ih =>
      simp [List.foldl]
      rw [norm_decode_step]
      exact ih (acc * byteModulus + normByte byte)

theorem foldWord_zero_eq_norm_bytesToNat (bytes : Bytes) :
    bytes.foldl (fun acc byte => norm (acc * byteModulus + normByte byte))
        0 =
      norm (bytesToNat bytes) := by
  simpa [bytesToNat] using foldWord_eq_norm_foldNat bytes 0

def bigEndianBytes (value byteCount : Nat) : Bytes :=
  (List.range byteCount).map
    (fun ix => normByte (value / byteModulus ^ (byteCount - 1 - ix)))

theorem bigEndianBytes_succ (value byteCount : Nat) :
    bigEndianBytes value (byteCount + 1) =
      bigEndianBytes (value / byteModulus) byteCount ++
        [normByte value] := by
  unfold bigEndianBytes
  rw [show byteCount + 1 = byteCount.succ by omega]
  rw [List.range_succ, List.map_append]
  simp only [List.map_cons, List.map_nil]
  have hMap :
      List.map
          (fun ix =>
            normByte
              (value / byteModulus ^ (byteCount.succ - 1 - ix)))
          (List.range byteCount) =
        List.map
          (fun ix =>
            normByte
              (value / byteModulus /
                byteModulus ^ (byteCount - 1 - ix)))
          (List.range byteCount) := by
    apply List.map_congr_left
    intro ix hMem
    have hIx : ix < byteCount := List.mem_range.mp hMem
    have hPow : byteModulus ^ (byteCount - ix) =
        byteModulus * byteModulus ^ (byteCount - 1 - ix) := by
      rw [show byteCount - ix =
          (byteCount - 1 - ix).succ by omega]
      simp [Nat.pow_succ, Nat.mul_comm]
    congr 1
    rw [show byteCount.succ - 1 - ix = byteCount - ix by omega]
    rw [hPow]
    rw [Nat.div_div_eq_div_mul]
  rw [hMap]
  simp [byteModulus]

theorem decodeNat_step (value byteCount : Nat) :
    ((value / byteModulus) % byteModulus ^ byteCount) *
        byteModulus + normByte value =
      value % byteModulus ^ (byteCount + 1) := by
  simp [byteModulus, normByte]
  let p := 256 ^ byteCount
  let q := value / 256
  let r := value % 256
  have hp : 0 < p := by
    exact Nat.pow_pos (by decide : 0 < 256)
  have hr : r < 256 := Nat.mod_lt value (by decide : 0 < 256)
  have hq : q % p < p := Nat.mod_lt q hp
  have hRemLt : (q % p) * 256 + r < p * 256 := by
    omega
  have hValue :
      value = (p * 256) * (q / p) + ((q % p) * 256 + r) := by
    calc
      value = 256 * q + r := by
        exact (Nat.div_add_mod value 256).symm
      _ = 256 * (p * (q / p) + q % p) + r := by
        rw [Nat.div_add_mod q p]
      _ = (p * 256) * (q / p) + ((q % p) * 256 + r) := by
        rw [Nat.left_distrib]
        ac_rfl
  calc
    ((value / 256) % 256 ^ byteCount) * 256 + value % 256 =
        (q % p) * 256 + r := by
      rfl
    _ = ((p * 256) * (q / p) + ((q % p) * 256 + r)) %
          (p * 256) := by
      rw [Nat.mul_add_mod_self_left]
      rw [Nat.mod_eq_of_lt hRemLt]
    _ = value % (p * 256) := by
      rw [hValue]
    _ = value % 256 ^ (byteCount + 1) := by
      rw [Nat.pow_succ]

theorem bytesToNat_bigEndianBytes (value byteCount : Nat) :
    bytesToNat (bigEndianBytes value byteCount) =
      value % byteModulus ^ byteCount := by
  induction byteCount generalizing value with
  | zero =>
      simp [bytesToNat, bigEndianBytes, byteModulus]
      omega
  | succ byteCount ih =>
      rw [bigEndianBytes_succ]
      unfold bytesToNat
      rw [List.foldl_append]
      simp [normByte_normByte]
      rw [show
        List.foldl
          (fun acc byte => acc * byteModulus + normByte byte) 0
          (bigEndianBytes (value / byteModulus) byteCount) =
        bytesToNat (bigEndianBytes (value / byteModulus) byteCount) by
        rfl]
      rw [ih]
      exact decodeNat_step value byteCount

theorem byteModulus_pow_32_eq_wordModulus :
    byteModulus ^ 32 = wordModulus := by
  native_decide

theorem wordToBytes32_eq_bigEndianBytes (word : Word) :
    wordToBytes32 word = bigEndianBytes (norm word) 32 := by
  rfl

def bytesToWord (bytes : Bytes) : Word :=
  (readBytes bytes 0 32).foldl
    (fun acc byte => norm (acc * byteModulus + normByte byte)) 0

theorem bytesToWord_wordToBytes32 (word : Word) :
    bytesToWord (wordToBytes32 word) = norm word := by
  unfold bytesToWord
  rw [readBytes_wordToBytes32_zero]
  rw [foldWord_zero_eq_norm_bytesToNat]
  rw [wordToBytes32_eq_bigEndianBytes]
  rw [bytesToNat_bigEndianBytes]
  rw [byteModulus_pow_32_eq_wordModulus]
  rw [show norm word % wordModulus = norm word by exact norm_norm word]
  exact norm_norm word

theorem norm_bytesToWord_wordToBytes32 (word : Word) :
    norm (bytesToWord (wordToBytes32 word)) = norm word := by
  rw [bytesToWord_wordToBytes32]
  exact norm_norm word

def writeWord (memory : Bytes) (offset word : Word) : Bytes :=
  writeBytes memory offset (wordToBytes32 word)

theorem readBytes_writeWord_same
    (memory : Bytes) (offset word : Word) :
    readBytes (writeWord memory offset word) offset 32 =
      wordToBytes32 word := by
  simpa [writeWord, wordToBytes32_map_normByte] using
    readBytes_writeBytes_same memory offset (wordToBytes32 word)

def readWord (memory : Bytes) (offset : Word) : Word :=
  bytesToWord (readBytes memory offset 32)

theorem readWord_writeWord_same
    (memory : Bytes) (offset word : Word) :
    readWord (writeWord memory offset word) offset =
      bytesToWord (wordToBytes32 word) := by
  simp [readWord, readBytes_writeWord_same]

def writeByteWord (memory : Bytes) (offset byte : Word) : Bytes :=
  writeByte memory offset byte

theorem readBytes_writeByteWord_one
    (memory : Bytes) (offset byte : Word) :
    readBytes (writeByteWord memory offset byte) offset 1 =
      [normByte byte] :=
  readBytes_writeByte_one memory offset byte

def copyBytes (memory : Bytes) (dest : Word) (source : Bytes)
    (sourceOffset size : Word) : Bytes :=
  writeBytes memory dest (readBytes source sourceOffset size)

theorem copyBytes_zero_size
    (memory source : Bytes) (dest sourceOffset : Word) :
    copyBytes memory dest source sourceOffset 0 = memory := by
  rfl

theorem readBytes_copyBytes_same
    (memory source : Bytes) (dest sourceOffset size : Word) :
    readBytes (copyBytes memory dest source sourceOffset size) dest size =
      readBytes source sourceOffset size := by
  simpa [copyBytes, readBytes_length, readBytes_map_normByte] using
    readBytes_writeBytes_same memory dest
      (readBytes source sourceOffset size)

theorem readWord_copyBytes_word_same
    (memory source : Bytes) (dest sourceOffset : Word) :
    readWord (copyBytes memory dest source sourceOffset 32) dest =
      readWord source sourceOffset := by
  simp [readWord, readBytes_copyBytes_same]

def lookupWordMap? : List (Word × Word) -> Word -> Option Word
  | [], _ => none
  | (candidate, value) :: rest, key =>
      if norm candidate = norm key then some value else lookupWordMap? rest key

def lookupWordListMap? : List (Word × List Word) -> Word -> Option (List Word)
  | [], _ => none
  | (candidate, value) :: rest, key =>
      if norm candidate = norm key then some value else lookupWordListMap? rest key

def writeWordMap (entries : List (Word × Word)) (key value : Word) :
    List (Word × Word) :=
  (norm key, norm value) :: entries

theorem lookupWordMap_writeWordMap_same
    (entries : List (Word × Word)) (key value : Word) :
    lookupWordMap? (writeWordMap entries key value) key =
      some (norm value) := by
  simp [lookupWordMap?, writeWordMap, norm_norm]

theorem lookupWordMap_writeWordMap_other
    (entries : List (Word × Word)) {key query value : Word}
    (hKey : norm key ≠ norm query) :
    lookupWordMap? (writeWordMap entries key value) query =
      lookupWordMap? entries query := by
  simp [lookupWordMap?, writeWordMap, norm_norm, hKey]

abbrev AccountWordMap := List (Word × List (Word × Word))

def lookupAccountWordEntries? : AccountWordMap -> Word ->
    Option (List (Word × Word))
  | [], _ => none
  | (candidate, entries) :: rest, address =>
      if norm candidate = norm address then
        some entries
      else
        lookupAccountWordEntries? rest address

def lookupAccountWordMap?
    (accounts : AccountWordMap) (address key : Word) : Option Word :=
  match lookupAccountWordEntries? accounts address with
  | some entries => lookupWordMap? entries key
  | none => none

def writeAccountWordMap
    (accounts : AccountWordMap) (address key value : Word) :
    AccountWordMap :=
  let entries :=
    match lookupAccountWordEntries? accounts address with
    | some entries => entries
    | none => []
  (norm address, writeWordMap entries key value) :: accounts

theorem lookupAccountWordEntries_write_other_address
    (accounts : AccountWordMap) {address other key value : Word}
    (hOther : norm other ≠ norm address) :
    lookupAccountWordEntries?
        (writeAccountWordMap accounts address key value) other =
      lookupAccountWordEntries? accounts other := by
  simp [writeAccountWordMap, lookupAccountWordEntries?, norm_norm,
    Ne.symm hOther]

theorem lookupAccountWordMap_write_same
    (accounts : AccountWordMap) (address key value : Word) :
    lookupAccountWordMap?
        (writeAccountWordMap accounts address key value) address key =
      some (norm value) := by
  simp [lookupAccountWordMap?, writeAccountWordMap,
    lookupAccountWordEntries?, lookupWordMap_writeWordMap_same, norm_norm]

theorem lookupAccountWordMap_write_other_address
    (accounts : AccountWordMap) {address other key value query : Word}
    (hOther : norm other ≠ norm address) :
    lookupAccountWordMap?
        (writeAccountWordMap accounts address key value) other query =
      lookupAccountWordMap? accounts other query := by
  simp [lookupAccountWordMap?,
    lookupAccountWordEntries_write_other_address accounts hOther]

theorem lookupAccountWordMap_write_same_address_other_key
    (accounts : AccountWordMap) (address : Word) {key query value : Word}
    (hKey : norm key ≠ norm query) :
    lookupAccountWordMap?
        (writeAccountWordMap accounts address key value) address query =
      lookupAccountWordMap? accounts address query := by
  cases hEntries : lookupAccountWordEntries? accounts address with
  | none =>
      simp [lookupAccountWordMap?, writeAccountWordMap,
        lookupAccountWordEntries?, hEntries, lookupWordMap_writeWordMap_other,
        hKey, norm_norm, lookupWordMap?]
  | some entries =>
      simp [lookupAccountWordMap?, writeAccountWordMap,
        lookupAccountWordEntries?, hEntries, lookupWordMap_writeWordMap_other,
        hKey, norm_norm]

def lookupBytesMap? : List (Word × Bytes) -> Word -> Option Bytes
  | [], _ => none
  | (candidate, value) :: rest, key =>
      if norm candidate = norm key then some value else lookupBytesMap? rest key

def normalizedWords (words : List Word) : List Word :=
  words.map norm

structure ExternalAction where
  builtin : Evm.Builtin
  args : List Word
  deriving DecidableEq, Repr

structure ExternalCallResponse where
  result : Word := 1
  returndata : Bytes := []
  deriving DecidableEq, Repr

structure CreateResponse where
  address : Word := 0
  returndata : Bytes := []
  deriving DecidableEq, Repr

structure HaltState where
  kind : Evm.HaltKind
  returndata : Bytes
  deriving DecidableEq, Repr

structure State where
  storage : AccountWordMap := []
  transientStorage : AccountWordMap := []
  immutables : List (Word × Word) := []
  immutablePositions : List (Word × List Word) := []
  linkerSymbols : List (Word × Word) := []
  memory : Bytes := []
  memorySize : Word := 0
  calldata : Bytes := []
  returndata : Bytes := []
  code : Bytes := []
  address : Word := 0
  origin : Word := 0
  caller : Word := 0
  callvalue : Word := 0
  gasprice : Word := 0
  coinbase : Word := 0
  timestamp : Word := 0
  number : Word := 0
  difficulty : Word := 0
  prevrandao : Word := 0
  gaslimit : Word := 0
  chainid : Word := 0
  selfbalance : Word := 0
  basefee : Word := 0
  gas : Word := 0
  pc : Word := 0
  blobbasefee : Word := 0
  blockhash0 : Word := 0
  blockhashes : List (Word × Word) := []
  balance0 : Word := 0
  balances : List (Word × Word) := []
  extcode0 : Bytes := []
  extcodes : List (Word × Bytes) := []
  blobhash0 : Word := 0
  blobhashes : List (Word × Word) := []
  callResult : Word := 1
  callResponses : List (Evm.Builtin × List Word × ExternalCallResponse) := []
  createdAddress : Word := 0
  createResponses : List (Evm.Builtin × List Word × CreateResponse) := []
  logs : List (Nat × List Word × Bytes) := []
  externalActions : List ExternalAction := []
  halt? : Option HaltState := none
  deriving DecidableEq, Repr

def State.empty : State := {}

def lookupExternalCallResponse? :
    List (Evm.Builtin × List Word × ExternalCallResponse) ->
      Evm.Builtin -> List Word -> Option ExternalCallResponse
  | [], _, _ => none
  | (candidate, candidateArgs, response) :: rest, builtin, args =>
      if candidate = builtin ∧ normalizedWords candidateArgs = normalizedWords args then
        some response
      else
        lookupExternalCallResponse? rest builtin args

def lookupCreateResponse? :
    List (Evm.Builtin × List Word × CreateResponse) ->
      Evm.Builtin -> List Word -> Option CreateResponse
  | [], _, _ => none
  | (candidate, candidateArgs, response) :: rest, builtin, args =>
      if candidate = builtin ∧ normalizedWords candidateArgs = normalizedWords args then
        some response
      else
        lookupCreateResponse? rest builtin args

def State.blockhash (state : State) (blockNumber : Word) : Word :=
  match lookupWordMap? state.blockhashes blockNumber with
  | some value => value
  | none => if norm blockNumber = 0 then state.blockhash0 else 0

def State.balance (state : State) (address : Word) : Word :=
  match lookupWordMap? state.balances address with
  | some value => value
  | none => if norm address = 0 then state.balance0 else 0

def State.extcode (state : State) (address : Word) : Bytes :=
  match lookupBytesMap? state.extcodes address with
  | some bytes => bytes
  | none => if norm address = 0 then state.extcode0 else []

def State.blobhash (state : State) (ix : Word) : Word :=
  match lookupWordMap? state.blobhashes ix with
  | some value => value
  | none => if norm ix = 0 then state.blobhash0 else 0

def State.callResponse (state : State) (builtin : Evm.Builtin)
    (args : List Word) : ExternalCallResponse :=
  match lookupExternalCallResponse? state.callResponses builtin args with
  | some response => response
  | none => { result := state.callResult, returndata := state.returndata }

def State.createResponse (state : State) (builtin : Evm.Builtin)
    (args : List Word) : CreateResponse :=
  match lookupCreateResponse? state.createResponses builtin args with
  | some response => response
  | none => { address := state.createdAddress, returndata := state.returndata }

structure HashOracle where
  keccak256 : Bytes -> Word
  verbatim : Evm.Builtin -> List Word -> Word := fun _ _ => 0
  verbatimValues : Evm.Builtin -> List Word -> List Word := fun builtin _ =>
    match builtin with
    | Evm.Builtin.verbatimOp _ outputs => List.replicate outputs 0
    | _ => []

def returnWord (value : Word) (state : State) : Option (Word × State) :=
  some (norm value, state)

theorem result_eq_of_returnWord_some
    {value result : Word} {state state' : State}
    (hEval : returnWord value state = some (result, state')) :
    result = norm value := by
  unfold returnWord at hEval
  injection hEval with hPair
  cases hPair
  rfl

theorem state_eq_of_returnWord_some
    {value result : Word} {state state' : State}
    (hEval : returnWord value state = some (result, state')) :
    state' = state := by
  unfold returnWord at hEval
  injection hEval with hPair
  cases hPair
  rfl

theorem memory_eq_of_returnWord_some
    {value result : Word} {state state' : State}
    (hEval : returnWord value state = some (result, state')) :
    state'.memory = state.memory := by
  rw [state_eq_of_returnWord_some hEval]

def returnUnit (state : State) : Option (Word × State) :=
  returnWord 0 state

theorem state_eq_of_returnUnit_some
    {state state' : State} {result : Word}
    (hEval : returnUnit state = some (result, state')) :
    state' = state := by
  unfold returnUnit returnWord at hEval
  injection hEval with hPair
  cases hPair
  rfl

theorem memory_eq_of_returnUnit_some
    {state state' : State} {result : Word}
    (hEval : returnUnit state = some (result, state')) :
    state'.memory = state.memory := by
  rw [state_eq_of_returnUnit_some hEval]

def expandMemory (state : State) (offset size : Word) : State :=
  { state with memorySize := memorySizeAfter state.memorySize offset size }

def setMemoryAfterAccess (state : State) (memory : Bytes)
    (offset size : Word) : State :=
  { state with
    memory := memory
    memorySize := memorySizeAfter state.memorySize offset size }

theorem memory_eq_of_returnUnit_setMemoryAfterAccess
    {state state' : State} {memory : Bytes} {offset size result : Word}
    (hEval :
      returnUnit (setMemoryAfterAccess state memory offset size) =
        some (result, state')) :
    state'.memory = memory := by
  rw [memory_eq_of_returnUnit_some hEval]
  rfl

theorem readBytes_of_returnUnit_setMemoryAfterAccess_writeWord
    {state state' : State} {memory : Bytes} {offset value result : Word}
    (hEval :
      returnUnit
          (setMemoryAfterAccess state (writeWord memory offset value)
            offset 32) =
        some (result, state')) :
    readBytes state'.memory offset 32 = wordToBytes32 value := by
  rw [memory_eq_of_returnUnit_setMemoryAfterAccess hEval]
  exact readBytes_writeWord_same memory offset value

theorem readBytes_of_returnUnit_setMemoryAfterAccess_writeByteWord
    {state state' : State} {memory : Bytes} {offset value result : Word}
    (hEval :
      returnUnit
          (setMemoryAfterAccess state (writeByteWord memory offset value)
            offset 1) =
        some (result, state')) :
    readBytes state'.memory offset 1 = [normByte value] := by
  rw [memory_eq_of_returnUnit_setMemoryAfterAccess hEval]
  exact readBytes_writeByteWord_one memory offset value

theorem readBytes_of_returnUnit_setMemoryAfterAccess_copyBytes
    {state state' : State} {memory source : Bytes}
    {dest sourceOffset size result : Word}
    (hEval :
      returnUnit
          (setMemoryAfterAccess state
            (copyBytes memory dest source sourceOffset size) dest size) =
        some (result, state')) :
    readBytes state'.memory dest size =
      readBytes source sourceOffset size := by
  rw [memory_eq_of_returnUnit_setMemoryAfterAccess hEval]
  exact readBytes_copyBytes_same memory source dest sourceOffset size

theorem readBytes_of_returnUnit_state_copyBytes
    {finalState state' : State} {memory source : Bytes}
    {dest sourceOffset size result : Word}
    (hMemory :
      finalState.memory = copyBytes memory dest source sourceOffset size)
    (hEval : returnUnit finalState = some (result, state')) :
    readBytes state'.memory dest size =
      readBytes source sourceOffset size := by
  rw [memory_eq_of_returnUnit_some hEval, hMemory]
  exact readBytes_copyBytes_same memory source dest sourceOffset size

def writeImmutableMemory (state : State) (offset : Word)
    (positions : List Word) (value : Word) : State :=
  positions.foldl
    (fun state' relativeOffset =>
      let absoluteOffset := addWord offset relativeOffset
      setMemoryAfterAccess state'
        (writeWord state'.memory absoluteOffset value) absoluteOffset 32)
    state

def recordExternalAction (builtin : Evm.Builtin) (args : List Word)
    (state : State) : State :=
  { state with externalActions := { builtin := builtin, args := args } :: state.externalActions }

def applyReturnedBytes (state : State) (offset size : Word)
    (returndata : Bytes) : State :=
  setMemoryAfterAccess { state with returndata := returndata }
    (copyBytes state.memory offset returndata 0 size) offset size

theorem applyReturnedBytes_returndata
    (state : State) (offset size : Word) (returndata : Bytes) :
    (applyReturnedBytes state offset size returndata).returndata =
      returndata := by
  rfl

theorem applyReturnedBytes_readBytes_same
    (state : State) (offset size : Word) (returndata : Bytes) :
    readBytes (applyReturnedBytes state offset size returndata).memory
        offset size =
      readBytes returndata 0 size := by
  simpa [applyReturnedBytes, setMemoryAfterAccess] using
    readBytes_copyBytes_same state.memory returndata offset 0 size

def finishExternalCall (builtin : Evm.Builtin) (args : List Word)
    (argsOffset argsSize retOffset retSize : Word) (state : State) :
    Word × State :=
  let response := state.callResponse builtin args
  let state' := expandMemory state argsOffset argsSize
  let state'' := recordExternalAction builtin args state'
  (norm response.result, applyReturnedBytes state'' retOffset retSize response.returndata)

theorem finishExternalCall_returndata
    (builtin : Evm.Builtin) (args : List Word)
    (argsOffset argsSize retOffset retSize : Word) (state : State) :
    (finishExternalCall builtin args argsOffset argsSize retOffset retSize
      state).2.returndata =
      (state.callResponse builtin args).returndata := by
  simp [finishExternalCall, applyReturnedBytes_returndata]

theorem finishExternalCall_result
    (builtin : Evm.Builtin) (args : List Word)
    (argsOffset argsSize retOffset retSize : Word) (state : State) :
    (finishExternalCall builtin args argsOffset argsSize retOffset retSize
      state).1 =
      norm (state.callResponse builtin args).result := by
  simp [finishExternalCall]

theorem finishExternalCall_readBytes_same
    (builtin : Evm.Builtin) (args : List Word)
    (argsOffset argsSize retOffset retSize : Word) (state : State) :
    readBytes
        (finishExternalCall builtin args argsOffset argsSize retOffset
          retSize state).2.memory retOffset retSize =
      readBytes (state.callResponse builtin args).returndata 0 retSize := by
  simp [finishExternalCall, applyReturnedBytes_readBytes_same]

theorem finishExternalCall_records_action
    (builtin : Evm.Builtin) (args : List Word)
    (argsOffset argsSize retOffset retSize : Word) (state : State) :
    (finishExternalCall builtin args argsOffset argsSize retOffset retSize
      state).2.externalActions =
      { builtin := builtin, args := args } :: state.externalActions := by
  simp [finishExternalCall, applyReturnedBytes, setMemoryAfterAccess,
    recordExternalAction, expandMemory]

theorem result_of_returnWord_finishExternalCall
    {builtin : Evm.Builtin} {args : List Word}
    {argsOffset argsSize retOffset retSize : Word} {state : State}
    {result : Word} {state' : State}
    (hEval :
      returnWord
          (finishExternalCall builtin args argsOffset argsSize retOffset
            retSize state).1
          (finishExternalCall builtin args argsOffset argsSize retOffset
            retSize state).2 =
        some (result, state')) :
    result = norm (state.callResponse builtin args).result := by
  simpa [finishExternalCall_result, norm_norm] using
    result_eq_of_returnWord_some hEval

theorem returndata_of_returnWord_finishExternalCall
    {builtin : Evm.Builtin} {args : List Word}
    {argsOffset argsSize retOffset retSize : Word} {state : State}
    {result : Word} {state' : State}
    (hEval :
      returnWord
          (finishExternalCall builtin args argsOffset argsSize retOffset
            retSize state).1
          (finishExternalCall builtin args argsOffset argsSize retOffset
            retSize state).2 =
        some (result, state')) :
    state'.returndata =
      (state.callResponse builtin args).returndata := by
  rw [state_eq_of_returnWord_some hEval]
  exact finishExternalCall_returndata builtin args argsOffset argsSize
    retOffset retSize state

theorem readBytes_of_returnWord_finishExternalCall
    {builtin : Evm.Builtin} {args : List Word}
    {argsOffset argsSize retOffset retSize : Word} {state : State}
    {result : Word} {state' : State}
    (hEval :
      returnWord
          (finishExternalCall builtin args argsOffset argsSize retOffset
            retSize state).1
          (finishExternalCall builtin args argsOffset argsSize retOffset
            retSize state).2 =
        some (result, state')) :
    readBytes state'.memory retOffset retSize =
      readBytes (state.callResponse builtin args).returndata 0 retSize := by
  rw [state_eq_of_returnWord_some hEval]
  exact finishExternalCall_readBytes_same builtin args argsOffset argsSize
    retOffset retSize state

theorem externalActions_of_returnWord_finishExternalCall
    {builtin : Evm.Builtin} {args : List Word}
    {argsOffset argsSize retOffset retSize : Word} {state : State}
    {result : Word} {state' : State}
    (hEval :
      returnWord
          (finishExternalCall builtin args argsOffset argsSize retOffset
            retSize state).1
          (finishExternalCall builtin args argsOffset argsSize retOffset
            retSize state).2 =
        some (result, state')) :
    state'.externalActions =
      { builtin := builtin, args := args } :: state.externalActions := by
  rw [state_eq_of_returnWord_some hEval]
  exact finishExternalCall_records_action builtin args argsOffset argsSize
    retOffset retSize state

def finishCreate (builtin : Evm.Builtin) (args : List Word)
    (offset size : Word) (state : State) : Word × State :=
  let response := state.createResponse builtin args
  let state' := expandMemory state offset size
  let state'' := recordExternalAction builtin args state'
  (norm response.address, { state'' with returndata := response.returndata })

theorem finishCreate_result
    (builtin : Evm.Builtin) (args : List Word)
    (offset size : Word) (state : State) :
    (finishCreate builtin args offset size state).1 =
      norm (state.createResponse builtin args).address := by
  simp [finishCreate]

theorem finishCreate_returndata
    (builtin : Evm.Builtin) (args : List Word)
    (offset size : Word) (state : State) :
    (finishCreate builtin args offset size state).2.returndata =
      (state.createResponse builtin args).returndata := by
  simp [finishCreate, recordExternalAction, expandMemory]

theorem finishCreate_records_action
    (builtin : Evm.Builtin) (args : List Word)
    (offset size : Word) (state : State) :
    (finishCreate builtin args offset size state).2.externalActions =
      { builtin := builtin, args := args } :: state.externalActions := by
  simp [finishCreate, recordExternalAction, expandMemory]

theorem result_of_returnWord_finishCreate
    {builtin : Evm.Builtin} {args : List Word}
    {offset size : Word} {state : State}
    {result : Word} {state' : State}
    (hEval :
      returnWord (finishCreate builtin args offset size state).1
          (finishCreate builtin args offset size state).2 =
        some (result, state')) :
    result = norm (state.createResponse builtin args).address := by
  simpa [finishCreate_result, norm_norm] using
    result_eq_of_returnWord_some hEval

theorem returndata_of_returnWord_finishCreate
    {builtin : Evm.Builtin} {args : List Word}
    {offset size : Word} {state : State}
    {result : Word} {state' : State}
    (hEval :
      returnWord (finishCreate builtin args offset size state).1
          (finishCreate builtin args offset size state).2 =
        some (result, state')) :
    state'.returndata =
      (state.createResponse builtin args).returndata := by
  rw [state_eq_of_returnWord_some hEval]
  exact finishCreate_returndata builtin args offset size state

theorem externalActions_of_returnWord_finishCreate
    {builtin : Evm.Builtin} {args : List Word}
    {offset size : Word} {state : State}
    {result : Word} {state' : State}
    (hEval :
      returnWord (finishCreate builtin args offset size state).1
          (finishCreate builtin args offset size state).2 =
        some (result, state')) :
    state'.externalActions =
      { builtin := builtin, args := args } :: state.externalActions := by
  rw [state_eq_of_returnWord_some hEval]
  exact finishCreate_records_action builtin args offset size state

def haltWith (kind : Evm.HaltKind) (returndata : Bytes)
    (state : State) : State :=
  { state with halt? := some { kind := kind, returndata := returndata } }

theorem halt?_of_returnUnit_haltWith
    {state state' : State} {kind : Evm.HaltKind}
    {returndata : Bytes} {result : Word}
    (hEval :
      returnUnit (haltWith kind returndata state) = some (result, state')) :
    state'.halt? = some { kind := kind, returndata := returndata } := by
  rw [state_eq_of_returnUnit_some hEval]
  rfl

def evalBuiltin (hash : HashOracle) (builtin : Evm.Builtin)
    (args : List Word) (state : State) : Option (Word × State) :=
  match builtin, args with
  | Evm.Builtin.stopOp, [] =>
      returnUnit (haltWith Evm.HaltKind.stop [] state)
  | Evm.Builtin.add, [lhs, rhs] => returnWord (addWord lhs rhs) state
  | Evm.Builtin.mul, [lhs, rhs] => returnWord (mulWord lhs rhs) state
  | Evm.Builtin.divOp, [lhs, rhs] => returnWord (divWord lhs rhs) state
  | Evm.Builtin.sdivOp, [lhs, rhs] => returnWord (sdivWord lhs rhs) state
  | Evm.Builtin.modOp, [lhs, rhs] => returnWord (modWord lhs rhs) state
  | Evm.Builtin.smodOp, [lhs, rhs] => returnWord (smodWord lhs rhs) state
  | Evm.Builtin.addmodOp, [lhs, rhs, modulus] =>
      returnWord (addmodWord lhs rhs modulus) state
  | Evm.Builtin.mulmodOp, [lhs, rhs, modulus] =>
      returnWord (mulmodWord lhs rhs modulus) state
  | Evm.Builtin.expOp, [base, exponent] =>
      returnWord (expWord base exponent) state
  | Evm.Builtin.sub, [lhs, rhs] => returnWord (subWord lhs rhs) state
  | Evm.Builtin.iszero, [value] => returnWord (iszeroWord value) state
  | Evm.Builtin.eqOp, [lhs, rhs] => returnWord (eqWord lhs rhs) state
  | Evm.Builtin.ltOp, [lhs, rhs] => returnWord (ltWord lhs rhs) state
  | Evm.Builtin.gtOp, [lhs, rhs] => returnWord (gtWord lhs rhs) state
  | Evm.Builtin.sltOp, [lhs, rhs] => returnWord (sltWord lhs rhs) state
  | Evm.Builtin.sgtOp, [lhs, rhs] => returnWord (sgtWord lhs rhs) state
  | Evm.Builtin.andOp, [lhs, rhs] => returnWord (andWord lhs rhs) state
  | Evm.Builtin.orOp, [lhs, rhs] => returnWord (orWord lhs rhs) state
  | Evm.Builtin.xorOp, [lhs, rhs] => returnWord (xorWord lhs rhs) state
  | Evm.Builtin.notOp, [value] => returnWord (notWord value) state
  | Evm.Builtin.shlOp, [shift, value] => returnWord (shlWord shift value) state
  | Evm.Builtin.shrOp, [shift, value] => returnWord (shrWord shift value) state
  | Evm.Builtin.sarOp, [shift, value] => returnWord (sarWord shift value) state
  | Evm.Builtin.signextendOp, [ix, value] =>
      returnWord (signextendWord ix value) state
  | Evm.Builtin.byteOp, [ix, value] => returnWord (byteWord ix value) state
  | Evm.Builtin.clzOp, [value] => returnWord (clzWord value) state
  | Evm.Builtin.popOp, [_] => returnUnit state
  | Evm.Builtin.addressOp, [] => returnWord state.address state
  | Evm.Builtin.originOp, [] => returnWord state.origin state
  | Evm.Builtin.callerOp, [] => returnWord state.caller state
  | Evm.Builtin.callvalueOp, [] => returnWord state.callvalue state
  | Evm.Builtin.gaspriceOp, [] => returnWord state.gasprice state
  | Evm.Builtin.coinbaseOp, [] => returnWord state.coinbase state
  | Evm.Builtin.timestampOp, [] => returnWord state.timestamp state
  | Evm.Builtin.numberOp, [] => returnWord state.number state
  | Evm.Builtin.difficultyOp, [] => returnWord state.difficulty state
  | Evm.Builtin.prevrandaoOp, [] => returnWord state.prevrandao state
  | Evm.Builtin.gaslimitOp, [] => returnWord state.gaslimit state
  | Evm.Builtin.chainidOp, [] => returnWord state.chainid state
  | Evm.Builtin.selfbalanceOp, [] => returnWord state.selfbalance state
  | Evm.Builtin.basefeeOp, [] => returnWord state.basefee state
  | Evm.Builtin.gasOp, [] => returnWord state.gas state
  | Evm.Builtin.pcOp, [] => returnWord state.pc state
  | Evm.Builtin.msizeOp, [] => returnWord state.memorySize state
  | Evm.Builtin.blobbasefeeOp, [] => returnWord state.blobbasefee state
  | Evm.Builtin.calldataloadOp, [offset] =>
      returnWord (readWord state.calldata offset) state
  | Evm.Builtin.calldatasizeOp, [] =>
      returnWord state.calldata.length state
  | Evm.Builtin.calldatacopyOp, [dest, offset, size] =>
      returnUnit
        (setMemoryAfterAccess state
          (copyBytes state.memory dest state.calldata offset size) dest size)
  | Evm.Builtin.returndataloadOp, [offset] =>
      returnWord (readWord state.returndata offset) state
  | Evm.Builtin.returndatasizeOp, [] =>
      returnWord state.returndata.length state
  | Evm.Builtin.returndatacopyOp, [dest, offset, size] =>
      returnUnit
        (setMemoryAfterAccess state
          (copyBytes state.memory dest state.returndata offset size) dest size)
  | Evm.Builtin.codecopyOp, [dest, offset, size] =>
      returnUnit
        (setMemoryAfterAccess state
          (copyBytes state.memory dest state.code offset size) dest size)
  | Evm.Builtin.datacopyOp, [dest, offset, size] =>
      returnUnit
        (setMemoryAfterAccess state
          (copyBytes state.memory dest state.code offset size) dest size)
  | Evm.Builtin.extcodecopyOp, [address, dest, offset, size] =>
      returnUnit
        (setMemoryAfterAccess state
          (copyBytes state.memory dest (state.extcode address) offset size) dest size)
  | Evm.Builtin.keccak256Op, [offset, size] =>
      returnWord (hash.keccak256 (readBytes state.memory offset size))
        (expandMemory state offset size)
  | Evm.Builtin.mload, [offset] =>
      returnWord (readWord state.memory offset) (expandMemory state offset 32)
  | Evm.Builtin.mstore, [offset, value] =>
      returnUnit
        (setMemoryAfterAccess state (writeWord state.memory offset value) offset 32)
  | Evm.Builtin.mstore8, [offset, value] =>
      returnUnit
        (setMemoryAfterAccess state (writeByteWord state.memory offset value) offset 1)
  | Evm.Builtin.mcopyOp, [dest, source, size] =>
      returnUnit
        { expandMemory (setMemoryAfterAccess state
            (copyBytes state.memory dest state.memory source size) dest size) source size with
          memory := copyBytes state.memory dest state.memory source size }
  | Evm.Builtin.sload, [key] =>
      match lookupAccountWordMap? state.storage state.address key with
      | some value => returnWord value state
      | none => returnWord 0 state
  | Evm.Builtin.sstore, [key, value] =>
      returnUnit
        { state with
          storage := writeAccountWordMap state.storage state.address key value }
  | Evm.Builtin.tloadOp, [key] =>
      match lookupAccountWordMap? state.transientStorage state.address key with
      | some value => returnWord value state
      | none => returnWord 0 state
  | Evm.Builtin.tstoreOp, [key, value] =>
      returnUnit
        { state with
          transientStorage :=
            writeAccountWordMap state.transientStorage state.address key value }
  | Evm.Builtin.log0Op, [offset, size] =>
      let state := expandMemory state offset size
      returnUnit
        { state with logs := (0, [], readBytes state.memory offset size) :: state.logs }
  | Evm.Builtin.log1Op, [offset, size, topic0] =>
      let state := expandMemory state offset size
      returnUnit
        { state with logs := (1, [topic0], readBytes state.memory offset size) :: state.logs }
  | Evm.Builtin.log2Op, [offset, size, topic0, topic1] =>
      let state := expandMemory state offset size
      returnUnit
        { state with logs :=
          (2, [topic0, topic1], readBytes state.memory offset size) :: state.logs }
  | Evm.Builtin.log3Op, [offset, size, topic0, topic1, topic2] =>
      let state := expandMemory state offset size
      returnUnit
        { state with logs :=
          (3, [topic0, topic1, topic2], readBytes state.memory offset size) :: state.logs }
  | Evm.Builtin.log4Op, [offset, size, topic0, topic1, topic2, topic3] =>
      let state := expandMemory state offset size
      returnUnit
        { state with logs :=
          (4, [topic0, topic1, topic2, topic3], readBytes state.memory offset size) ::
            state.logs }
  | Evm.Builtin.blockhashOp, [blockNumber] =>
      returnWord (state.blockhash blockNumber) state
  | Evm.Builtin.balanceOp, [address] =>
      returnWord (state.balance address) state
  | Evm.Builtin.extcodesizeOp, [address] =>
      returnWord (state.extcode address).length state
  | Evm.Builtin.extcodehashOp, [address] =>
      returnWord (hash.keccak256 (state.extcode address)) state
  | Evm.Builtin.codesizeOp, [] => returnWord state.code.length state
  | Evm.Builtin.blobhashOp, [ix] =>
      returnWord (state.blobhash ix) state
  | Evm.Builtin.callOp, [gas, address, value, argsOffset, argsSize, retOffset, retSize] =>
      let args := [gas, address, value, argsOffset, argsSize, retOffset, retSize]
      let (result, state') :=
        finishExternalCall Evm.Builtin.callOp args argsOffset argsSize retOffset retSize state
      returnWord result state'
  | Evm.Builtin.callcodeOp, [gas, address, value, argsOffset, argsSize, retOffset, retSize] =>
      let args := [gas, address, value, argsOffset, argsSize, retOffset, retSize]
      let (result, state') :=
        finishExternalCall Evm.Builtin.callcodeOp args argsOffset argsSize retOffset retSize state
      returnWord result state'
  | Evm.Builtin.delegatecallOp, [gas, address, argsOffset, argsSize, retOffset, retSize] =>
      let args := [gas, address, argsOffset, argsSize, retOffset, retSize]
      let (result, state') :=
        finishExternalCall Evm.Builtin.delegatecallOp args argsOffset argsSize retOffset retSize state
      returnWord result state'
  | Evm.Builtin.staticcallOp, [gas, address, argsOffset, argsSize, retOffset, retSize] =>
      let args := [gas, address, argsOffset, argsSize, retOffset, retSize]
      let (result, state') :=
        finishExternalCall Evm.Builtin.staticcallOp args argsOffset argsSize retOffset retSize state
      returnWord result state'
  | Evm.Builtin.returnOp, [offset, size] =>
      let state' := expandMemory state offset size
      returnUnit
        (haltWith Evm.HaltKind.returned (readBytes state.memory offset size) state')
  | Evm.Builtin.revertOp, [offset, size] =>
      let state' := expandMemory state offset size
      returnUnit
        (haltWith Evm.HaltKind.reverted (readBytes state.memory offset size) state')
  | Evm.Builtin.invalidOp, [] =>
      returnUnit (haltWith Evm.HaltKind.invalid [] state)
  | Evm.Builtin.createOp, [value, offset, size] =>
      let args := [value, offset, size]
      let (address, state') := finishCreate Evm.Builtin.createOp args offset size state
      returnWord address state'
  | Evm.Builtin.create2Op, [value, offset, size, salt] =>
      let args := [value, offset, size, salt]
      let (address, state') := finishCreate Evm.Builtin.create2Op args offset size state
      returnWord address state'
  | Evm.Builtin.selfdestructOp, [target] =>
      returnUnit
        (haltWith Evm.HaltKind.stop []
          (recordExternalAction Evm.Builtin.selfdestructOp [target] state))
  | Evm.Builtin.setimmutableOp, [offset, key, value] =>
      let state' :=
        { state with immutables := writeWordMap state.immutables key value }
      match lookupWordListMap? state.immutablePositions key with
      | some positions => returnUnit (writeImmutableMemory state' offset positions value)
      | none => returnUnit state'
  | Evm.Builtin.loadimmutableOp, [key] =>
      match lookupWordMap? state.immutables key with
      | some value => returnWord value state
      | none => returnWord 0 state
  | Evm.Builtin.linkersymbolOp, [key] =>
      match lookupWordMap? state.linkerSymbols key with
      | some value => returnWord value state
      | none => returnWord 0 state
  | Evm.Builtin.memoryguardOp, [size] => returnWord size state
  | Evm.Builtin.verbatimOp inputs 0, args =>
      if args.length = inputs then
        returnUnit (recordExternalAction (Evm.Builtin.verbatimOp inputs 0) args state)
      else
        none
  | Evm.Builtin.verbatimOp inputs 1, args =>
      if args.length = inputs then
        returnWord (hash.verbatim (Evm.Builtin.verbatimOp inputs 1) args)
          (recordExternalAction (Evm.Builtin.verbatimOp inputs 1) args state)
      else
        none
  | Evm.Builtin.verbatimOp _ _, _ => none
  | Evm.Builtin.opaque _, _ => none
  | _, _ => none

theorem evalBuiltin_opaque_none
    (hash : HashOracle) (id : Nat) (args : List Word) (state : State) :
    evalBuiltin hash (Evm.Builtin.opaque id) args state = none := by
  rfl

theorem evalBuiltin_sload_present
    (hash : HashOracle) (state : State) (key value : Word)
    (hLookup :
      lookupAccountWordMap? state.storage state.address key = some value) :
    evalBuiltin hash Evm.Builtin.sload [key] state =
      returnWord value state := by
  change
    (match lookupAccountWordMap? state.storage state.address key with
    | some value => returnWord value state
    | none => returnWord 0 state) =
      returnWord value state
  rw [hLookup]

theorem evalBuiltin_sload_missing
    (hash : HashOracle) (state : State) (key : Word)
    (hLookup :
      lookupAccountWordMap? state.storage state.address key = none) :
    evalBuiltin hash Evm.Builtin.sload [key] state =
      returnWord 0 state := by
  change
    (match lookupAccountWordMap? state.storage state.address key with
    | some value => returnWord value state
    | none => returnWord 0 state) =
      returnWord 0 state
  rw [hLookup]

theorem evalBuiltin_tload_present
    (hash : HashOracle) (state : State) (key value : Word)
    (hLookup :
      lookupAccountWordMap? state.transientStorage state.address key =
        some value) :
    evalBuiltin hash Evm.Builtin.tloadOp [key] state =
      returnWord value state := by
  change
    (match lookupAccountWordMap? state.transientStorage state.address key with
    | some value => returnWord value state
    | none => returnWord 0 state) =
      returnWord value state
  rw [hLookup]

theorem evalBuiltin_tload_missing
    (hash : HashOracle) (state : State) (key : Word)
    (hLookup :
      lookupAccountWordMap? state.transientStorage state.address key = none) :
    evalBuiltin hash Evm.Builtin.tloadOp [key] state =
      returnWord 0 state := by
  change
    (match lookupAccountWordMap? state.transientStorage state.address key with
    | some value => returnWord value state
    | none => returnWord 0 state) =
      returnWord 0 state
  rw [hLookup]

theorem evalBuiltin_sstore_words
    (hash : HashOracle) (state : State) (key value : Word) :
    evalBuiltin hash Evm.Builtin.sstore [key, value] state =
      returnUnit
        { state with
          storage := writeAccountWordMap state.storage state.address key value } := by
  rfl

theorem storage_lookup_of_returnUnit_sstore
    {state state' : State} {key value result : Word}
    (hEval :
      returnUnit
          { state with
            storage := writeAccountWordMap state.storage state.address key value } =
        some (result, state')) :
    lookupAccountWordMap? state'.storage state'.address key = some (norm value) := by
  rw [state_eq_of_returnUnit_some hEval]
  exact lookupAccountWordMap_write_same state.storage state.address key value

theorem evalBuiltin_sstore_lookup_same
    (hash : HashOracle) (state : State) (key value result : Word)
    (state' : State)
    (hEval :
      evalBuiltin hash Evm.Builtin.sstore [key, value] state =
        some (result, state')) :
    lookupAccountWordMap? state'.storage state'.address key =
      some (norm value) := by
  rw [evalBuiltin_sstore_words] at hEval
  exact storage_lookup_of_returnUnit_sstore hEval

theorem evalBuiltin_sload_after_sstore_same
    (hash : HashOracle) (state : State) (key value result : Word)
    (state' : State)
    (hStore :
      evalBuiltin hash Evm.Builtin.sstore [key, value] state =
        some (result, state')) :
    evalBuiltin hash Evm.Builtin.sload [key] state' =
      returnWord (norm value) state' :=
  evalBuiltin_sload_present hash state' key (norm value)
    (evalBuiltin_sstore_lookup_same hash state key value result state'
      hStore)

theorem evalBuiltin_tstore_words
    (hash : HashOracle) (state : State) (key value : Word) :
    evalBuiltin hash Evm.Builtin.tstoreOp [key, value] state =
      returnUnit
        { state with
          transientStorage :=
            writeAccountWordMap state.transientStorage state.address key value } := by
  rfl

theorem transientStorage_lookup_of_returnUnit_tstore
    {state state' : State} {key value result : Word}
    (hEval :
      returnUnit
          { state with
            transientStorage :=
              writeAccountWordMap state.transientStorage state.address key value } =
        some (result, state')) :
    lookupAccountWordMap? state'.transientStorage state'.address key =
      some (norm value) := by
  rw [state_eq_of_returnUnit_some hEval]
  exact lookupAccountWordMap_write_same state.transientStorage state.address key value

theorem evalBuiltin_tstore_lookup_same
    (hash : HashOracle) (state : State) (key value result : Word)
    (state' : State)
    (hEval :
      evalBuiltin hash Evm.Builtin.tstoreOp [key, value] state =
        some (result, state')) :
    lookupAccountWordMap? state'.transientStorage state'.address key =
      some (norm value) := by
  rw [evalBuiltin_tstore_words] at hEval
  exact transientStorage_lookup_of_returnUnit_tstore hEval

theorem evalBuiltin_tload_after_tstore_same
    (hash : HashOracle) (state : State) (key value result : Word)
    (state' : State)
    (hStore :
      evalBuiltin hash Evm.Builtin.tstoreOp [key, value] state =
        some (result, state')) :
    evalBuiltin hash Evm.Builtin.tloadOp [key] state' =
      returnWord (norm value) state' :=
  evalBuiltin_tload_present hash state' key (norm value)
    (evalBuiltin_tstore_lookup_same hash state key value result state'
      hStore)

theorem evalBuiltin_stop
    (hash : HashOracle) (state : State) :
    evalBuiltin hash Evm.Builtin.stopOp [] state =
      returnUnit (haltWith Evm.HaltKind.stop [] state) := by
  rfl

theorem evalBuiltin_stop_halt?
    (hash : HashOracle) (state : State) (result : Word) (state' : State)
    (hEval :
      evalBuiltin hash Evm.Builtin.stopOp [] state =
        some (result, state')) :
    state'.halt? =
      some { kind := Evm.HaltKind.stop, returndata := [] } := by
  rw [evalBuiltin_stop] at hEval
  exact halt?_of_returnUnit_haltWith hEval

theorem evalBuiltin_pop_word
    (hash : HashOracle) (state : State) (value : Word) :
    evalBuiltin hash Evm.Builtin.popOp [value] state =
      returnUnit state := by
  rfl

theorem evalBuiltin_invalid
    (hash : HashOracle) (state : State) :
    evalBuiltin hash Evm.Builtin.invalidOp [] state =
      returnUnit (haltWith Evm.HaltKind.invalid [] state) := by
  rfl

theorem evalBuiltin_invalid_halt?
    (hash : HashOracle) (state : State) (result : Word) (state' : State)
    (hEval :
      evalBuiltin hash Evm.Builtin.invalidOp [] state =
        some (result, state')) :
    state'.halt? =
      some { kind := Evm.HaltKind.invalid, returndata := [] } := by
  rw [evalBuiltin_invalid] at hEval
  exact halt?_of_returnUnit_haltWith hEval

theorem evalBuiltin_selfdestruct_word
    (hash : HashOracle) (state : State) (target : Word) :
    evalBuiltin hash Evm.Builtin.selfdestructOp [target] state =
      returnUnit
        (haltWith Evm.HaltKind.stop []
          (recordExternalAction Evm.Builtin.selfdestructOp [target] state)) := by
  rfl

theorem evalBuiltin_selfdestruct_halt?
    {hash : HashOracle} {state state' : State} {target result : Word}
    (hEval :
      evalBuiltin hash Evm.Builtin.selfdestructOp [target] state =
        some (result, state')) :
    state'.halt? =
      some { kind := Evm.HaltKind.stop, returndata := [] } := by
  rw [evalBuiltin_selfdestruct_word] at hEval
  exact halt?_of_returnUnit_haltWith hEval

theorem evalBuiltin_call_finishExternalCall
    (hash : HashOracle) (state : State)
    (gas address value argsOffset argsSize retOffset retSize : Word) :
    evalBuiltin hash Evm.Builtin.callOp
        [gas, address, value, argsOffset, argsSize, retOffset, retSize]
        state =
      let args :=
        [gas, address, value, argsOffset, argsSize, retOffset, retSize]
      let outcome :=
        finishExternalCall Evm.Builtin.callOp args argsOffset argsSize
          retOffset retSize state
      returnWord outcome.1 outcome.2 := by
  rfl

theorem evalBuiltin_callcode_finishExternalCall
    (hash : HashOracle) (state : State)
    (gas address value argsOffset argsSize retOffset retSize : Word) :
    evalBuiltin hash Evm.Builtin.callcodeOp
        [gas, address, value, argsOffset, argsSize, retOffset, retSize]
        state =
      let args :=
        [gas, address, value, argsOffset, argsSize, retOffset, retSize]
      let outcome :=
        finishExternalCall Evm.Builtin.callcodeOp args argsOffset argsSize
          retOffset retSize state
      returnWord outcome.1 outcome.2 := by
  rfl

theorem evalBuiltin_delegatecall_finishExternalCall
    (hash : HashOracle) (state : State)
    (gas address argsOffset argsSize retOffset retSize : Word) :
    evalBuiltin hash Evm.Builtin.delegatecallOp
        [gas, address, argsOffset, argsSize, retOffset, retSize] state =
      let args := [gas, address, argsOffset, argsSize, retOffset, retSize]
      let outcome :=
        finishExternalCall Evm.Builtin.delegatecallOp args argsOffset
          argsSize retOffset retSize state
      returnWord outcome.1 outcome.2 := by
  rfl

theorem evalBuiltin_staticcall_finishExternalCall
    (hash : HashOracle) (state : State)
    (gas address argsOffset argsSize retOffset retSize : Word) :
    evalBuiltin hash Evm.Builtin.staticcallOp
        [gas, address, argsOffset, argsSize, retOffset, retSize] state =
      let args := [gas, address, argsOffset, argsSize, retOffset, retSize]
      let outcome :=
        finishExternalCall Evm.Builtin.staticcallOp args argsOffset
          argsSize retOffset retSize state
      returnWord outcome.1 outcome.2 := by
  rfl

theorem evalBuiltin_create_finishCreate
    (hash : HashOracle) (state : State) (value offset size : Word) :
    evalBuiltin hash Evm.Builtin.createOp [value, offset, size] state =
      let args := [value, offset, size]
      let outcome := finishCreate Evm.Builtin.createOp args offset size state
      returnWord outcome.1 outcome.2 := by
  rfl

theorem evalBuiltin_create2_finishCreate
    (hash : HashOracle) (state : State) (value offset size salt : Word) :
    evalBuiltin hash Evm.Builtin.create2Op [value, offset, size, salt] state =
      let args := [value, offset, size, salt]
      let outcome := finishCreate Evm.Builtin.create2Op args offset size state
      returnWord outcome.1 outcome.2 := by
  rfl

theorem evalBuiltin_call_words
    (hash : HashOracle) (state : State)
    (gas address value argsOffset argsSize retOffset retSize : Word) :
    evalBuiltin hash Evm.Builtin.callOp
        [gas, address, value, argsOffset, argsSize, retOffset, retSize]
        state =
      let args :=
        [gas, address, value, argsOffset, argsSize, retOffset, retSize]
      let response := state.callResponse Evm.Builtin.callOp args
      returnWord (norm response.result)
        (applyReturnedBytes
          (recordExternalAction Evm.Builtin.callOp args
            (expandMemory state argsOffset argsSize))
          retOffset retSize response.returndata) := by
  rfl

theorem evalBuiltin_callcode_words
    (hash : HashOracle) (state : State)
    (gas address value argsOffset argsSize retOffset retSize : Word) :
    evalBuiltin hash Evm.Builtin.callcodeOp
        [gas, address, value, argsOffset, argsSize, retOffset, retSize]
        state =
      let args :=
        [gas, address, value, argsOffset, argsSize, retOffset, retSize]
      let response := state.callResponse Evm.Builtin.callcodeOp args
      returnWord (norm response.result)
        (applyReturnedBytes
          (recordExternalAction Evm.Builtin.callcodeOp args
            (expandMemory state argsOffset argsSize))
          retOffset retSize response.returndata) := by
  rfl

theorem evalBuiltin_delegatecall_words
    (hash : HashOracle) (state : State)
    (gas address argsOffset argsSize retOffset retSize : Word) :
    evalBuiltin hash Evm.Builtin.delegatecallOp
        [gas, address, argsOffset, argsSize, retOffset, retSize] state =
      let args := [gas, address, argsOffset, argsSize, retOffset, retSize]
      let response := state.callResponse Evm.Builtin.delegatecallOp args
      returnWord (norm response.result)
        (applyReturnedBytes
          (recordExternalAction Evm.Builtin.delegatecallOp args
            (expandMemory state argsOffset argsSize))
          retOffset retSize response.returndata) := by
  rfl

theorem evalBuiltin_staticcall_words
    (hash : HashOracle) (state : State)
    (gas address argsOffset argsSize retOffset retSize : Word) :
    evalBuiltin hash Evm.Builtin.staticcallOp
        [gas, address, argsOffset, argsSize, retOffset, retSize] state =
      let args := [gas, address, argsOffset, argsSize, retOffset, retSize]
      let response := state.callResponse Evm.Builtin.staticcallOp args
      returnWord (norm response.result)
        (applyReturnedBytes
          (recordExternalAction Evm.Builtin.staticcallOp args
            (expandMemory state argsOffset argsSize))
          retOffset retSize response.returndata) := by
  rfl

theorem evalBuiltin_create_words
    (hash : HashOracle) (state : State) (value offset size : Word) :
    evalBuiltin hash Evm.Builtin.createOp [value, offset, size] state =
      let args := [value, offset, size]
      let response := state.createResponse Evm.Builtin.createOp args
      returnWord (norm response.address)
        { recordExternalAction Evm.Builtin.createOp args
            (expandMemory state offset size) with
          returndata := response.returndata } := by
  rfl

theorem evalBuiltin_create2_words
    (hash : HashOracle) (state : State) (value offset size salt : Word) :
    evalBuiltin hash Evm.Builtin.create2Op [value, offset, size, salt] state =
      let args := [value, offset, size, salt]
      let response := state.createResponse Evm.Builtin.create2Op args
      returnWord (norm response.address)
        { recordExternalAction Evm.Builtin.create2Op args
            (expandMemory state offset size) with
          returndata := response.returndata } := by
  rfl

theorem evalBuiltin_verbatim_zero_args
    (hash : HashOracle) (state : State) (inputs : Nat) (args : List Word)
    (hArgs : args.length = inputs) :
    evalBuiltin hash (Evm.Builtin.verbatimOp inputs 0) args state =
      returnUnit
        (recordExternalAction (Evm.Builtin.verbatimOp inputs 0) args
          state) := by
  change
    (if args.length = inputs then
      returnUnit
        (recordExternalAction (Evm.Builtin.verbatimOp inputs 0) args state)
    else none) =
      returnUnit
        (recordExternalAction (Evm.Builtin.verbatimOp inputs 0) args state)
  simp [hArgs]

theorem evalBuiltin_verbatim_one_args
    (hash : HashOracle) (state : State) (inputs : Nat) (args : List Word)
    (hArgs : args.length = inputs) :
    evalBuiltin hash (Evm.Builtin.verbatimOp inputs 1) args state =
      returnWord (hash.verbatim (Evm.Builtin.verbatimOp inputs 1) args)
        (recordExternalAction (Evm.Builtin.verbatimOp inputs 1) args
          state) := by
  change
    (if args.length = inputs then
      returnWord (hash.verbatim (Evm.Builtin.verbatimOp inputs 1) args)
        (recordExternalAction (Evm.Builtin.verbatimOp inputs 1) args state)
    else none) =
      returnWord (hash.verbatim (Evm.Builtin.verbatimOp inputs 1) args)
        (recordExternalAction (Evm.Builtin.verbatimOp inputs 1) args state)
  simp [hArgs]

theorem evalBuiltin_log0_words
    (hash : HashOracle) (state : State) (offset size : Word) :
    evalBuiltin hash Evm.Builtin.log0Op [offset, size] state =
      returnUnit
        { expandMemory state offset size with
          logs := (0, [], readBytes state.memory offset size) :: state.logs } := by
  rfl

theorem evalBuiltin_log1_words
    (hash : HashOracle) (state : State) (offset size topic0 : Word) :
    evalBuiltin hash Evm.Builtin.log1Op [offset, size, topic0] state =
      returnUnit
        { expandMemory state offset size with
          logs :=
            (1, [topic0], readBytes state.memory offset size) ::
              state.logs } := by
  rfl

theorem evalBuiltin_log2_words
    (hash : HashOracle) (state : State)
    (offset size topic0 topic1 : Word) :
    evalBuiltin hash Evm.Builtin.log2Op
        [offset, size, topic0, topic1] state =
      returnUnit
        { expandMemory state offset size with
          logs :=
            (2, [topic0, topic1],
              readBytes state.memory offset size) ::
              state.logs } := by
  rfl

theorem evalBuiltin_log3_words
    (hash : HashOracle) (state : State)
    (offset size topic0 topic1 topic2 : Word) :
    evalBuiltin hash Evm.Builtin.log3Op
        [offset, size, topic0, topic1, topic2] state =
      returnUnit
        { expandMemory state offset size with
          logs :=
            (3, [topic0, topic1, topic2],
              readBytes state.memory offset size) ::
              state.logs } := by
  rfl

theorem evalBuiltin_log4_words
    (hash : HashOracle) (state : State)
    (offset size topic0 topic1 topic2 topic3 : Word) :
    evalBuiltin hash Evm.Builtin.log4Op
        [offset, size, topic0, topic1, topic2, topic3] state =
      returnUnit
        { expandMemory state offset size with
          logs :=
            (4, [topic0, topic1, topic2, topic3],
              readBytes state.memory offset size) ::
              state.logs } := by
  rfl

theorem evalBuiltin_memoryguard_word
    (hash : HashOracle) (state : State) (size : Word) :
    evalBuiltin hash Evm.Builtin.memoryguardOp [size] state =
      returnWord size state := by
  rfl

theorem evalBuiltin_contextWord_returns_word
    (hash : HashOracle) (state : State) {builtin : Evm.Builtin}
    (hBuiltin : FullYul.CompilerProfile.ContextWordBuiltin builtin) :
    ∃ value,
      evalBuiltin hash builtin [] state = returnWord value state := by
  cases hBuiltin
  · exact ⟨state.address, rfl⟩
  · exact ⟨state.origin, rfl⟩
  · exact ⟨state.caller, rfl⟩
  · exact ⟨state.callvalue, rfl⟩
  · exact ⟨state.gasprice, rfl⟩
  · exact ⟨state.coinbase, rfl⟩
  · exact ⟨state.timestamp, rfl⟩
  · exact ⟨state.number, rfl⟩
  · exact ⟨state.difficulty, rfl⟩
  · exact ⟨state.prevrandao, rfl⟩
  · exact ⟨state.gaslimit, rfl⟩
  · exact ⟨state.chainid, rfl⟩
  · exact ⟨state.selfbalance, rfl⟩
  · exact ⟨state.basefee, rfl⟩
  · exact ⟨state.memorySize, rfl⟩
  · exact ⟨state.blobbasefee, rfl⟩

theorem evalBuiltin_contextWord_preserves_state
    {hash : HashOracle} {state state' : State} {value : Word}
    {builtin : Evm.Builtin}
    (hBuiltin : FullYul.CompilerProfile.ContextWordBuiltin builtin)
    (hEval : evalBuiltin hash builtin [] state = some (value, state')) :
    state' = state := by
  cases hBuiltin
  · exact state_eq_of_returnWord_some hEval
  · exact state_eq_of_returnWord_some hEval
  · exact state_eq_of_returnWord_some hEval
  · exact state_eq_of_returnWord_some hEval
  · exact state_eq_of_returnWord_some hEval
  · exact state_eq_of_returnWord_some hEval
  · exact state_eq_of_returnWord_some hEval
  · exact state_eq_of_returnWord_some hEval
  · exact state_eq_of_returnWord_some hEval
  · exact state_eq_of_returnWord_some hEval
  · exact state_eq_of_returnWord_some hEval
  · exact state_eq_of_returnWord_some hEval
  · exact state_eq_of_returnWord_some hEval
  · exact state_eq_of_returnWord_some hEval
  · exact state_eq_of_returnWord_some hEval
  · exact state_eq_of_returnWord_some hEval

theorem evalBuiltin_calldatasize
    (hash : HashOracle) (state : State) :
    evalBuiltin hash Evm.Builtin.calldatasizeOp [] state =
      returnWord state.calldata.length state := by
  rfl

theorem evalBuiltin_calldataload_word
    (hash : HashOracle) (state : State) (offset : Word) :
    evalBuiltin hash Evm.Builtin.calldataloadOp [offset] state =
      returnWord (readWord state.calldata offset) state := by
  rfl

theorem evalBuiltin_returndataload_word
    (hash : HashOracle) (state : State) (offset : Word) :
    evalBuiltin hash Evm.Builtin.returndataloadOp [offset] state =
      returnWord (readWord state.returndata offset) state := by
  rfl

theorem evalBuiltin_returndatasize
    (hash : HashOracle) (state : State) :
    evalBuiltin hash Evm.Builtin.returndatasizeOp [] state =
      returnWord state.returndata.length state := by
  rfl

theorem evalBuiltin_codesize
    (hash : HashOracle) (state : State) :
    evalBuiltin hash Evm.Builtin.codesizeOp [] state =
      returnWord state.code.length state := by
  rfl

theorem evalBuiltin_blockhash_word
    (hash : HashOracle) (state : State) (blockNumber : Word) :
    evalBuiltin hash Evm.Builtin.blockhashOp [blockNumber] state =
      returnWord (state.blockhash blockNumber) state := by
  rfl

theorem evalBuiltin_balance_word
    (hash : HashOracle) (state : State) (address : Word) :
    evalBuiltin hash Evm.Builtin.balanceOp [address] state =
      returnWord (state.balance address) state := by
  rfl

theorem evalBuiltin_extcodesize_word
    (hash : HashOracle) (state : State) (address : Word) :
    evalBuiltin hash Evm.Builtin.extcodesizeOp [address] state =
      returnWord (state.extcode address).length state := by
  rfl

theorem evalBuiltin_extcodehash_word
    (hash : HashOracle) (state : State) (address : Word) :
    evalBuiltin hash Evm.Builtin.extcodehashOp [address] state =
      returnWord (hash.keccak256 (state.extcode address)) state := by
  rfl

theorem evalBuiltin_blobhash_word
    (hash : HashOracle) (state : State) (index : Word) :
    evalBuiltin hash Evm.Builtin.blobhashOp [index] state =
      returnWord (state.blobhash index) state := by
  rfl

theorem evalBuiltin_mload_word
    (hash : HashOracle) (state : State) (offset : Word) :
    evalBuiltin hash Evm.Builtin.mload [offset] state =
      returnWord (readWord state.memory offset) (expandMemory state offset 32) := by
  rfl

theorem evalBuiltin_mstore_words
    (hash : HashOracle) (state : State) (offset value : Word) :
    evalBuiltin hash Evm.Builtin.mstore [offset, value] state =
      returnUnit
        (setMemoryAfterAccess state (writeWord state.memory offset value)
          offset 32) := by
  rfl

theorem evalBuiltin_mstore_readBytes_same
    (hash : HashOracle) (state : State) (offset value result : Word)
    (state' : State)
    (hEval :
      evalBuiltin hash Evm.Builtin.mstore [offset, value] state =
        some (result, state')) :
    readBytes state'.memory offset 32 = wordToBytes32 value := by
  rw [evalBuiltin_mstore_words] at hEval
  exact readBytes_of_returnUnit_setMemoryAfterAccess_writeWord hEval

theorem evalBuiltin_mstore8_words
    (hash : HashOracle) (state : State) (offset value : Word) :
    evalBuiltin hash Evm.Builtin.mstore8 [offset, value] state =
      returnUnit
        (setMemoryAfterAccess state (writeByteWord state.memory offset value)
          offset 1) := by
  rfl

theorem evalBuiltin_mstore8_readBytes_same
    (hash : HashOracle) (state : State) (offset value result : Word)
    (state' : State)
    (hEval :
      evalBuiltin hash Evm.Builtin.mstore8 [offset, value] state =
        some (result, state')) :
    readBytes state'.memory offset 1 = [normByte value] := by
  rw [evalBuiltin_mstore8_words] at hEval
  exact readBytes_of_returnUnit_setMemoryAfterAccess_writeByteWord hEval

theorem evalBuiltin_keccak256_words
    (hash : HashOracle) (state : State) (offset size : Word) :
    evalBuiltin hash Evm.Builtin.keccak256Op [offset, size] state =
      returnWord (hash.keccak256 (readBytes state.memory offset size))
        (expandMemory state offset size) := by
  rfl

theorem evalBuiltin_return_words
    (hash : HashOracle) (state : State) (offset size : Word) :
    evalBuiltin hash Evm.Builtin.returnOp [offset, size] state =
      returnUnit
        (haltWith Evm.HaltKind.returned
          (readBytes state.memory offset size)
          (expandMemory state offset size)) := by
  rfl

theorem evalBuiltin_return_halt?
    (hash : HashOracle) (state : State) (offset size result : Word)
    (state' : State)
    (hEval :
      evalBuiltin hash Evm.Builtin.returnOp [offset, size] state =
        some (result, state')) :
    state'.halt? =
      some
        { kind := Evm.HaltKind.returned
          returndata := readBytes state.memory offset size } := by
  rw [evalBuiltin_return_words] at hEval
  exact halt?_of_returnUnit_haltWith hEval

theorem evalBuiltin_revert_words
    (hash : HashOracle) (state : State) (offset size : Word) :
    evalBuiltin hash Evm.Builtin.revertOp [offset, size] state =
      returnUnit
        (haltWith Evm.HaltKind.reverted
          (readBytes state.memory offset size)
          (expandMemory state offset size)) := by
  rfl

theorem evalBuiltin_revert_halt?
    (hash : HashOracle) (state : State) (offset size result : Word)
    (state' : State)
    (hEval :
      evalBuiltin hash Evm.Builtin.revertOp [offset, size] state =
        some (result, state')) :
    state'.halt? =
      some
        { kind := Evm.HaltKind.reverted
          returndata := readBytes state.memory offset size } := by
  rw [evalBuiltin_revert_words] at hEval
  exact halt?_of_returnUnit_haltWith hEval

theorem evalBuiltin_calldatacopy_words
    (hash : HashOracle) (state : State) (dest offset size : Word) :
    evalBuiltin hash Evm.Builtin.calldatacopyOp [dest, offset, size] state =
      returnUnit
        (setMemoryAfterAccess state
          (copyBytes state.memory dest state.calldata offset size) dest size) := by
  rfl

theorem evalBuiltin_calldatacopy_readBytes_same
    (hash : HashOracle) (state : State)
    (dest offset size result : Word) (state' : State)
    (hEval :
      evalBuiltin hash Evm.Builtin.calldatacopyOp [dest, offset, size] state =
        some (result, state')) :
    readBytes state'.memory dest size =
      readBytes state.calldata offset size := by
  rw [evalBuiltin_calldatacopy_words] at hEval
  exact readBytes_of_returnUnit_setMemoryAfterAccess_copyBytes hEval

theorem evalBuiltin_returndatacopy_words
    (hash : HashOracle) (state : State) (dest offset size : Word) :
    evalBuiltin hash Evm.Builtin.returndatacopyOp [dest, offset, size] state =
      returnUnit
        (setMemoryAfterAccess state
          (copyBytes state.memory dest state.returndata offset size) dest size) := by
  rfl

theorem evalBuiltin_returndatacopy_readBytes_same
    (hash : HashOracle) (state : State)
    (dest offset size result : Word) (state' : State)
    (hEval :
      evalBuiltin hash Evm.Builtin.returndatacopyOp [dest, offset, size]
          state =
        some (result, state')) :
    readBytes state'.memory dest size =
      readBytes state.returndata offset size := by
  rw [evalBuiltin_returndatacopy_words] at hEval
  exact readBytes_of_returnUnit_setMemoryAfterAccess_copyBytes hEval

theorem evalBuiltin_codecopy_words
    (hash : HashOracle) (state : State) (dest offset size : Word) :
    evalBuiltin hash Evm.Builtin.codecopyOp [dest, offset, size] state =
      returnUnit
        (setMemoryAfterAccess state
          (copyBytes state.memory dest state.code offset size) dest size) := by
  rfl

theorem evalBuiltin_codecopy_readBytes_same
    (hash : HashOracle) (state : State)
    (dest offset size result : Word) (state' : State)
    (hEval :
      evalBuiltin hash Evm.Builtin.codecopyOp [dest, offset, size] state =
        some (result, state')) :
    readBytes state'.memory dest size =
      readBytes state.code offset size := by
  rw [evalBuiltin_codecopy_words] at hEval
  exact readBytes_of_returnUnit_setMemoryAfterAccess_copyBytes hEval

theorem evalBuiltin_datacopy_words
    (hash : HashOracle) (state : State) (dest offset size : Word) :
    evalBuiltin hash Evm.Builtin.datacopyOp [dest, offset, size] state =
      returnUnit
        (setMemoryAfterAccess state
          (copyBytes state.memory dest state.code offset size) dest size) := by
  rfl

theorem evalBuiltin_datacopy_readBytes_same
    (hash : HashOracle) (state : State)
    (dest offset size result : Word) (state' : State)
    (hEval :
      evalBuiltin hash Evm.Builtin.datacopyOp [dest, offset, size] state =
        some (result, state')) :
    readBytes state'.memory dest size =
      readBytes state.code offset size := by
  rw [evalBuiltin_datacopy_words] at hEval
  exact readBytes_of_returnUnit_setMemoryAfterAccess_copyBytes hEval

theorem evalBuiltin_extcodecopy_words
    (hash : HashOracle) (state : State)
    (address dest offset size : Word) :
    evalBuiltin hash Evm.Builtin.extcodecopyOp
        [address, dest, offset, size] state =
      returnUnit
        (setMemoryAfterAccess state
          (copyBytes state.memory dest (state.extcode address) offset size)
          dest size) := by
  rfl

theorem evalBuiltin_extcodecopy_readBytes_same
    (hash : HashOracle) (state : State)
    (address dest offset size result : Word) (state' : State)
    (hEval :
      evalBuiltin hash Evm.Builtin.extcodecopyOp
          [address, dest, offset, size] state =
        some (result, state')) :
    readBytes state'.memory dest size =
      readBytes (state.extcode address) offset size := by
  rw [evalBuiltin_extcodecopy_words] at hEval
  exact readBytes_of_returnUnit_setMemoryAfterAccess_copyBytes hEval

theorem evalBuiltin_mcopy_words
    (hash : HashOracle) (state : State) (dest source size : Word) :
    evalBuiltin hash Evm.Builtin.mcopyOp [dest, source, size] state =
      returnUnit
        { expandMemory
            (setMemoryAfterAccess state
              (copyBytes state.memory dest state.memory source size) dest size)
            source size with
          memory := copyBytes state.memory dest state.memory source size } := by
  rfl

theorem evalBuiltin_mcopy_readBytes_same
    (hash : HashOracle) (state : State)
    (dest source size result : Word) (state' : State)
    (hEval :
      evalBuiltin hash Evm.Builtin.mcopyOp [dest, source, size] state =
        some (result, state')) :
    readBytes state'.memory dest size =
      readBytes state.memory source size := by
  rw [evalBuiltin_mcopy_words] at hEval
  exact
    readBytes_of_returnUnit_state_copyBytes
      (memory := state.memory) (source := state.memory)
      (dest := dest) (sourceOffset := source) (size := size)
      (by rfl) hEval

theorem evalBuiltin_mcopy_zero_size_of_normalized_memorySize
    (hash : HashOracle) (state : State) (dest source : Word)
    (hMemorySize : norm state.memorySize = state.memorySize) :
    evalBuiltin hash Evm.Builtin.mcopyOp [dest, source, 0] state =
      returnUnit state := by
  have hZero : norm 0 = 0 := rfl
  simp [evalBuiltin_mcopy_words, returnUnit, returnWord,
    setMemoryAfterAccess, expandMemory, memorySizeAfter,
    copyBytes_zero_size, hMemorySize, hZero]

theorem evalBuiltin_loadimmutable_present
    (hash : HashOracle) (state : State) (key value : Word)
    (hLookup : lookupWordMap? state.immutables key = some value) :
    evalBuiltin hash Evm.Builtin.loadimmutableOp [key] state =
      returnWord value state := by
  change
    (match lookupWordMap? state.immutables key with
    | some value => returnWord value state
    | none => returnWord 0 state) =
      returnWord value state
  rw [hLookup]

theorem evalBuiltin_loadimmutable_missing
    (hash : HashOracle) (state : State) (key : Word)
    (hLookup : lookupWordMap? state.immutables key = none) :
    evalBuiltin hash Evm.Builtin.loadimmutableOp [key] state =
      returnWord 0 state := by
  change
    (match lookupWordMap? state.immutables key with
    | some value => returnWord value state
    | none => returnWord 0 state) =
      returnWord 0 state
  rw [hLookup]

theorem evalBuiltin_linkersymbol_present
    (hash : HashOracle) (state : State) (key value : Word)
    (hLookup : lookupWordMap? state.linkerSymbols key = some value) :
    evalBuiltin hash Evm.Builtin.linkersymbolOp [key] state =
      returnWord value state := by
  change
    (match lookupWordMap? state.linkerSymbols key with
    | some value => returnWord value state
    | none => returnWord 0 state) =
      returnWord value state
  rw [hLookup]

theorem evalBuiltin_linkersymbol_missing
    (hash : HashOracle) (state : State) (key : Word)
    (hLookup : lookupWordMap? state.linkerSymbols key = none) :
    evalBuiltin hash Evm.Builtin.linkersymbolOp [key] state =
      returnWord 0 state := by
  change
    (match lookupWordMap? state.linkerSymbols key with
    | some value => returnWord value state
    | none => returnWord 0 state) =
      returnWord 0 state
  rw [hLookup]

theorem evalBuiltin_setimmutable_no_positions
    (hash : HashOracle) (state : State) (offset key value : Word)
    (hPositions : lookupWordListMap? state.immutablePositions key = none) :
    evalBuiltin hash Evm.Builtin.setimmutableOp [offset, key, value] state =
      returnUnit { state with immutables := writeWordMap state.immutables key value } := by
  change
    (let state' :=
      { state with immutables := writeWordMap state.immutables key value }
    match lookupWordListMap? state.immutablePositions key with
    | some positions => returnUnit (writeImmutableMemory state' offset positions value)
    | none => returnUnit state') =
      returnUnit { state with immutables := writeWordMap state.immutables key value }
  simp [hPositions]

theorem evalBuiltin_setimmutable_positions
    (hash : HashOracle) (state : State) (offset key value : Word)
    (positions : List Word)
    (hPositions : lookupWordListMap? state.immutablePositions key =
      some positions) :
    evalBuiltin hash Evm.Builtin.setimmutableOp [offset, key, value] state =
      returnUnit
        (writeImmutableMemory
          { state with immutables := writeWordMap state.immutables key value }
          offset positions value) := by
  change
    (let state' :=
      { state with immutables := writeWordMap state.immutables key value }
    match lookupWordListMap? state.immutablePositions key with
    | some positions => returnUnit (writeImmutableMemory state' offset positions value)
    | none => returnUnit state') =
      returnUnit
        (writeImmutableMemory
          { state with immutables := writeWordMap state.immutables key value }
          offset positions value)
  simp [hPositions]

def evalBuiltinValues (hash : HashOracle) (builtin : Evm.Builtin)
    (args : List Word) (state : State) : Option (List Word × State) :=
  match builtin with
  | Evm.Builtin.verbatimOp inputs outputs =>
      if args.length = inputs then
        let values := (hash.verbatimValues (Evm.Builtin.verbatimOp inputs outputs) args).map norm
        if values.length = outputs then
          some
            ( values
            , recordExternalAction (Evm.Builtin.verbatimOp inputs outputs) args state )
        else
          none
      else
        none
  | _ =>
      match builtin.signature? with
      | some sig =>
          if sig.resultCount = 0 then
            match evalBuiltin hash builtin args state with
            | some (_, state') => some ([], state')
            | none => none
          else if sig.resultCount = 1 then
            match evalBuiltin hash builtin args state with
            | some (value, state') => some ([value], state')
            | none => none
          else
            none
      | none => none

theorem evalBuiltinValues_opaque_none
    (hash : HashOracle) (id : Nat) (args : List Word) (state : State) :
    evalBuiltinValues hash (Evm.Builtin.opaque id) args state = none := by
  simp [evalBuiltinValues, Evm.Builtin.signature?]

theorem evalBuiltinValues_zero_match_length
    {hash : HashOracle} {builtin : Evm.Builtin} {args : List Word}
    {state state' : State} {values : List Word}
    (hEval :
      (match evalBuiltin hash builtin args state with
      | some (_, nextState) => some ([], nextState)
      | none => none) = some (values, state')) :
    values.length = 0 := by
  cases hBuiltin : evalBuiltin hash builtin args state with
  | none =>
      simp [hBuiltin] at hEval
  | some pair =>
      cases pair with
      | mk _ nextState =>
          simp [hBuiltin] at hEval
          cases hEval.1
          rfl

theorem evalBuiltinValues_one_match_length
    {hash : HashOracle} {builtin : Evm.Builtin} {args : List Word}
    {state state' : State} {values : List Word}
    (hEval :
      (match evalBuiltin hash builtin args state with
      | some (value, nextState) => some ([value], nextState)
      | none => none) = some (values, state')) :
    values.length = 1 := by
  cases hBuiltin : evalBuiltin hash builtin args state with
  | none =>
      simp [hBuiltin] at hEval
  | some pair =>
      cases pair with
      | mk value nextState =>
          simp [hBuiltin] at hEval
          cases hEval.1
          rfl

theorem evalBuiltinValues_length_of_signature
    {hash : HashOracle} {builtin : Evm.Builtin} {args : List Word}
    {state state' : State} {values : List Word}
    {sig : Evm.BuiltinSignature}
    (hSig : builtin.signature? = some sig)
    (hEval : evalBuiltinValues hash builtin args state = some (values, state')) :
    values.length = sig.resultCount := by
  cases builtin <;>
    simp [evalBuiltinValues, Evm.Builtin.signature?] at hSig hEval ⊢
  case verbatimOp inputs outputs =>
    subst sig
    rcases hEval with ⟨_, hLen, hEval⟩
    cases hEval.1
    simpa using hLen
  all_goals
    subst sig
    first
    | exact evalBuiltinValues_zero_match_length hEval
    | exact evalBuiltinValues_one_match_length hEval

abbrev Name := FullYul.Name
abbrev DataLabel := FullYul.DataLabel
abbrev Env := List (Name × Word)

def lookup? : Env -> Name -> Option Word
  | [], _ => none
  | (candidate, value) :: rest, name =>
      if candidate = name then some value else lookup? rest name

def declare? (env : Env) (name : Name) (value : Word) : Option Env :=
  match lookup? env name with
  | some _ => none
  | none => some ((name, norm value) :: env)

def assign? : Env -> Name -> Word -> Option Env
  | [], _, _ => none
  | (candidate, current) :: rest, name, value =>
      if candidate = name then
        some ((candidate, norm value) :: rest)
      else
        match assign? rest name value with
        | some rest' => some ((candidate, current) :: rest')
        | none => none

def declareMany? : Env -> List Name -> List Word -> Option Env
  | env, [], [] => some env
  | env, name :: names, value :: values =>
      match declare? env name value with
      | some env' => declareMany? env' names values
      | none => none
  | _, _, _ => none

def assignMany? : Env -> List Name -> List Word -> Option Env
  | env, [], [] => some env
  | env, name :: names, value :: values =>
      match assign? env name value with
      | some env' => assignMany? env' names values
      | none => none
  | _, _, _ => none

def restoreOuter : Env -> Env -> Option Env
  | [], _ => some []
  | (name, _) :: rest, inner =>
      match lookup? inner name, restoreOuter rest inner with
      | some value, some rest' => some ((name, value) :: rest')
      | _, _ => none

structure Object where
  data : List (DataLabel × Bytes) := []
  objects : List (DataLabel × Bytes) := []
  code : Bytes := []
  deriving DecidableEq, Repr

def lookupData? : List (DataLabel × Bytes) -> DataLabel -> Option Bytes
  | [], _ => none
  | (candidate, bytes) :: rest, label =>
      if candidate = label then some bytes else lookupData? rest label

def Object.data? (object : Object) (label : DataLabel) : Option Bytes :=
  match lookupData? object.data label with
  | some bytes => some bytes
  | none => lookupData? object.objects label

structure Config where
  env : Env := []
  state : State := State.empty
  object : Object := {}
  deriving DecidableEq, Repr

def Config.empty : Config := {}

inductive Expr where
  | word : Word -> Expr
  | var : Name -> Expr
  | builtin : Evm.Builtin -> List Expr -> Expr
  | dataSize : DataLabel -> Expr
  | dataOffset : DataLabel -> Expr
  deriving Repr

mutual
  def evalExpr (hash : HashOracle) : Expr -> Config -> Option (Word × Config)
    | Expr.word value, config => some (norm value, config)
    | Expr.var name, config =>
        match lookup? config.env name with
        | some value => some (value, config)
        | none => none
    | Expr.builtin Evm.Builtin.datacopyOp
        [destExpr, Expr.dataOffset label, sizeExpr], config =>
        match evalExpr hash sizeExpr config with
        | some (size, config') =>
            match evalExpr hash (Expr.dataOffset label) config' with
            | some (_, config'') =>
                match evalExpr hash destExpr config'' with
                | some (dest, config''') =>
                    match config'''.object.data? label with
                    | some bytes =>
                        some
                          (0,
                            { config''' with
                              state :=
                                setMemoryAfterAccess config'''.state
                                  (copyBytes config'''.state.memory dest bytes 0 size)
                                  dest size })
                    | none => none
                | none => none
            | none => none
        | none => none
    | Expr.builtin builtin args, config =>
        match evalExprs hash args config with
        | some (values, config') =>
            match evalBuiltin hash builtin values config'.state with
            | some (value, state') => some (value, { config' with state := state' })
            | none => none
        | none => none
    | Expr.dataSize label, config =>
        match config.object.data? label with
        | some bytes => some (norm bytes.length, config)
        | none => none
    | Expr.dataOffset label, config =>
        match config.object.data? label with
        | some _ => some (label, config)
        | none => none

  def evalExprs (hash : HashOracle) : List Expr -> Config ->
      Option (List Word × Config)
    | [], config => some ([], config)
    | expr :: rest, config =>
        match evalExprs hash rest config with
        | some (values, config') =>
            match evalExpr hash expr config' with
            | some (value, config'') => some (value :: values, config'')
            | none => none
        | none => none
end

def evalExprsAsYulValues (hash : HashOracle) (exprs : List Expr)
    (config : Config) : Option (List Word × Config) :=
  match exprs with
  | [Expr.builtin builtin args] =>
      match builtin.signature? with
      | some sig =>
          if sig.resultCount = 1 then
            evalExprs hash exprs config
          else
            match evalExprs hash args config with
            | some (argValues, config') =>
                match evalBuiltinValues hash builtin argValues config'.state with
                | some (values, state') =>
                    some (values, { config' with state := state' })
                | none => none
            | none => none
      | none => evalExprs hash exprs config
  | _ => evalExprs hash exprs config

inductive Flow where
  | normal
  | broke
  | continued
  | left
  | halted
  deriving DecidableEq, Repr

structure Result where
  flow : Flow
  config : Config
  deriving DecidableEq, Repr

def normalResult (config : Config) : Result :=
  { flow := Flow.normal, config := config }

def resultAfterExpr (config : Config) : Result :=
  match config.state.halt? with
  | some _ => { flow := Flow.halted, config := config }
  | none => normalResult config

def restoreBlockConfig (outer : Config) (inner : Config) :
    Option Config :=
  match restoreOuter outer.env inner.env with
  | some env' => some { inner with env := env' }
  | none => none

theorem restoreBlockConfig_preserves_state {outer inner restored : Config}
    (h : restoreBlockConfig outer inner = some restored) :
    restored.state = inner.state := by
  unfold restoreBlockConfig at h
  cases hRestore : restoreOuter outer.env inner.env with
  | none =>
      simp [hRestore] at h
  | some env' =>
      simp [hRestore] at h
      cases h
      rfl

theorem restoreBlockConfig_preserves_object {outer inner restored : Config}
    (h : restoreBlockConfig outer inner = some restored) :
    restored.object = inner.object := by
  unfold restoreBlockConfig at h
  cases hRestore : restoreOuter outer.env inner.env with
  | none =>
      simp [hRestore] at h
  | some env' =>
      simp [hRestore] at h
      cases h
      rfl

def withRestoredConfig (outer : Config) (result : Result) :
    Option Result :=
  match restoreBlockConfig outer result.config with
  | some config' => some { flow := result.flow, config := config' }
  | none => none

theorem withRestoredConfig_preserves_state {outer : Config}
    {result restored : Result}
    (h : withRestoredConfig outer result = some restored) :
    restored.config.state = result.config.state := by
  unfold withRestoredConfig at h
  cases hRestore : restoreBlockConfig outer result.config with
  | none =>
      simp [hRestore] at h
  | some config' =>
      simp [hRestore] at h
      cases h
      exact restoreBlockConfig_preserves_state hRestore

inductive Stmt where
  | skip
  | expr : Expr -> Stmt
  | let1 : Name -> Option Expr -> Stmt
  | letMany : List Name -> Option (List Expr) -> Stmt
  | funDef : Name -> List Name -> List Name -> Stmt -> Stmt
  | assign : Name -> Expr -> Stmt
  | assignMany : List Name -> List Expr -> Stmt
  | letCall : List Name -> Name -> List Expr -> Stmt
  | assignCall : List Name -> Name -> List Expr -> Stmt
  | seq : Stmt -> Stmt -> Stmt
  | block : List Stmt -> Stmt
  | ifThen : Expr -> Stmt -> Stmt
  | switch : Expr -> List (Word × Stmt) -> Option Stmt -> Stmt
  | forLoop : Stmt -> Expr -> Stmt -> Stmt -> Stmt
  | break
  | continue
  | leave
  deriving Repr

def switchTarget? (value : Word) : List (Word × Stmt) -> Option Stmt ->
    Option Stmt
  | [], defaultBranch => defaultBranch
  | (label, branch) :: rest, defaultBranch =>
      if norm label = norm value then some branch else switchTarget? value rest defaultBranch

mutual
  def evalStmtFuel (hash : HashOracle) : Nat -> Config -> Stmt -> Option Result
    | 0, _, _ => none
    | _fuel + 1, config, Stmt.skip => some (normalResult config)
    | _fuel + 1, config, Stmt.expr expr =>
        match evalExpr hash expr config with
        | some (_, config') => some (resultAfterExpr config')
        | none => none
    | _fuel + 1, config, Stmt.let1 name init =>
        match init with
        | some expr =>
            match evalExpr hash expr config with
            | some (value, config') =>
                match declare? config'.env name value with
                | some env' => some (normalResult { config' with env := env' })
                | none => none
            | none => none
        | none =>
            match declare? config.env name 0 with
            | some env' => some (normalResult { config with env := env' })
            | none => none
    | _fuel + 1, config, Stmt.letMany names init =>
        match init with
        | some exprs =>
            match evalExprsAsYulValues hash exprs config with
            | some (values, config') =>
                match declareMany? config'.env names values with
                | some env' => some (normalResult { config' with env := env' })
                | none => none
            | none => none
        | none =>
            match declareMany? config.env names (names.map (fun _ => 0)) with
            | some env' => some (normalResult { config with env := env' })
            | none => none
    | _fuel + 1, config, Stmt.funDef _ _ _ _ =>
        some (normalResult config)
    | _fuel + 1, config, Stmt.assign name expr =>
        match evalExpr hash expr config with
        | some (value, config') =>
            match assign? config'.env name value with
            | some env' => some (normalResult { config' with env := env' })
            | none => none
        | none => none
    | _fuel + 1, config, Stmt.assignMany names exprs =>
        match evalExprsAsYulValues hash exprs config with
        | some (values, config') =>
            match assignMany? config'.env names values with
            | some env' => some (normalResult { config' with env := env' })
            | none => none
        | none => none
    | _fuel + 1, _, Stmt.letCall _ _ _ => none
    | _fuel + 1, _, Stmt.assignCall _ _ _ => none
    | fuel + 1, config, Stmt.seq first second =>
        match evalStmtFuel hash fuel config first with
        | some { flow := Flow.normal, config := config' } =>
            evalStmtFuel hash fuel config' second
        | some result => some result
        | none => none
    | fuel + 1, config, Stmt.block stmts =>
        match evalBlockFuel hash fuel config stmts with
        | some result => withRestoredConfig config result
        | none => none
    | fuel + 1, config, Stmt.ifThen cond body =>
        match evalExpr hash cond config with
        | some (value, config') =>
            if norm value = 0 then some (normalResult config')
            else evalStmtFuel hash fuel config' body
        | none => none
    | fuel + 1, config, Stmt.switch discr cases defaultBranch =>
        match evalExpr hash discr config with
        | some (value, config') =>
            match switchTarget? value cases defaultBranch with
            | some branch => evalStmtFuel hash fuel config' branch
            | none => some (normalResult config')
        | none => none
    | fuel + 1, config, Stmt.forLoop pre cond post body =>
        match evalStmtFuel hash fuel config pre with
        | some { flow := Flow.normal, config := loopConfig } =>
            evalForFuel hash fuel config loopConfig cond post body
        | some result => withRestoredConfig config result
        | none => none
    | _fuel + 1, config, Stmt.break =>
        some { flow := Flow.broke, config := config }
    | _fuel + 1, config, Stmt.continue =>
        some { flow := Flow.continued, config := config }
    | _fuel + 1, config, Stmt.leave =>
        some { flow := Flow.left, config := config }

  def evalBlockFuel (hash : HashOracle) : Nat -> Config -> List Stmt ->
      Option Result
    | 0, _, _ => none
    | _fuel + 1, config, [] => some (normalResult config)
    | fuel + 1, config, stmt :: rest =>
        match evalStmtFuel hash fuel config stmt with
        | some { flow := Flow.normal, config := config' } =>
            evalBlockFuel hash fuel config' rest
        | some result => some result
        | none => none

  def evalForFuel (hash : HashOracle) : Nat -> Config -> Config -> Expr ->
      Stmt -> Stmt -> Option Result
    | 0, _, _, _, _, _ => none
    | fuel + 1, outer, loopConfig, cond, post, body =>
        match evalExpr hash cond loopConfig with
        | some (value, condConfig) =>
            if norm value = 0 then
              match restoreBlockConfig outer condConfig with
              | some config' => some (normalResult config')
              | none => none
            else
              match evalStmtFuel hash fuel condConfig body with
              | some { flow := Flow.normal, config := bodyConfig } =>
                  match evalStmtFuel hash fuel bodyConfig post with
                  | some { flow := Flow.normal, config := postConfig } =>
                      evalForFuel hash fuel outer postConfig cond post body
                  | some { flow := Flow.continued, config := postConfig } =>
                      evalForFuel hash fuel outer postConfig cond post body
                  | some { flow := Flow.broke, config := postConfig } =>
                      match restoreBlockConfig outer postConfig with
                      | some config' => some (normalResult config')
                      | none => none
                  | some { flow := Flow.left, config := postConfig } =>
                      match restoreBlockConfig outer postConfig with
                      | some config' => some { flow := Flow.left, config := config' }
                      | none => none
                  | some { flow := Flow.halted, config := postConfig } =>
                      match restoreBlockConfig outer postConfig with
                      | some config' => some { flow := Flow.halted, config := config' }
                      | none => none
                  | none => none
              | some { flow := Flow.continued, config := bodyConfig } =>
                  match evalStmtFuel hash fuel bodyConfig post with
                  | some { flow := Flow.normal, config := postConfig } =>
                      evalForFuel hash fuel outer postConfig cond post body
                  | some { flow := Flow.continued, config := postConfig } =>
                      evalForFuel hash fuel outer postConfig cond post body
                  | some { flow := Flow.broke, config := postConfig } =>
                      match restoreBlockConfig outer postConfig with
                      | some config' => some (normalResult config')
                      | none => none
                  | some { flow := Flow.left, config := postConfig } =>
                      match restoreBlockConfig outer postConfig with
                      | some config' => some { flow := Flow.left, config := config' }
                      | none => none
                  | some { flow := Flow.halted, config := postConfig } =>
                      match restoreBlockConfig outer postConfig with
                      | some config' => some { flow := Flow.halted, config := config' }
                      | none => none
                  | none => none
              | some { flow := Flow.broke, config := bodyConfig } =>
                  match restoreBlockConfig outer bodyConfig with
                  | some config' => some (normalResult config')
                  | none => none
              | some { flow := Flow.left, config := bodyConfig } =>
                  match restoreBlockConfig outer bodyConfig with
                  | some config' => some { flow := Flow.left, config := config' }
                  | none => none
              | some { flow := Flow.halted, config := bodyConfig } =>
                  match restoreBlockConfig outer bodyConfig with
                  | some config' => some { flow := Flow.halted, config := config' }
                  | none => none
              | none => none
        | none => none
end

structure FunctionDef where
  params : List Name
  returns : List Name
  body : Stmt
  deriving Repr

abbrev FunctionEnv := List (Name × FunctionDef)

def lookupFunction? : FunctionEnv -> Name -> Option FunctionDef
  | [], _ => none
  | (candidate, fn) :: rest, name =>
      if candidate = name then some fn else lookupFunction? rest name

def declareFunction (funcs : FunctionEnv) (name : Name)
    (fn : FunctionDef) : FunctionEnv :=
  match lookupFunction? funcs name with
  | some _ => funcs
  | none => (name, fn) :: funcs

def collectStmtFunctionDefs : Stmt -> FunctionEnv -> FunctionEnv
  | Stmt.funDef name params returns body, funcs =>
      declareFunction funcs name { params := params, returns := returns, body := body }
  | Stmt.seq first second, funcs =>
      collectStmtFunctionDefs second (collectStmtFunctionDefs first funcs)
  | _, funcs => funcs

def collectBlockFunctionDefs : List Stmt -> FunctionEnv -> FunctionEnv
  | [], funcs => funcs
  | stmt :: rest, funcs =>
      collectBlockFunctionDefs rest (collectStmtFunctionDefs stmt funcs)

def valuesForNames? (env : Env) : List Name -> Option (List Word)
  | [] => some []
  | name :: rest =>
      match lookup? env name, valuesForNames? env rest with
      | some value, some values => some (value :: values)
      | _, _ => none

def initFunctionEnv (params : List Name) (args : List Word)
    (returns : List Name) : Option Env :=
  match declareMany? [] params args with
  | some paramEnv => declareMany? paramEnv returns (returns.map (fun _ => 0))
  | none => none

mutual
  def evalProgramStmtFuel (hash : HashOracle) (funcs : FunctionEnv) :
      Nat -> Config -> Stmt -> Option Result
    | 0, _, _ => none
    | _fuel + 1, config, Stmt.skip => some (normalResult config)
    | _fuel + 1, config, Stmt.expr expr =>
        match evalExpr hash expr config with
        | some (_, config') => some (resultAfterExpr config')
        | none => none
    | _fuel + 1, config, Stmt.let1 name init =>
        match init with
        | some expr =>
            match evalExpr hash expr config with
            | some (value, config') =>
                match declare? config'.env name value with
                | some env' => some (normalResult { config' with env := env' })
                | none => none
            | none => none
        | none =>
            match declare? config.env name 0 with
            | some env' => some (normalResult { config with env := env' })
            | none => none
    | _fuel + 1, config, Stmt.letMany names init =>
        match init with
        | some exprs =>
            match evalExprsAsYulValues hash exprs config with
            | some (values, config') =>
                match declareMany? config'.env names values with
                | some env' => some (normalResult { config' with env := env' })
                | none => none
            | none => none
        | none =>
            match declareMany? config.env names (names.map (fun _ => 0)) with
            | some env' => some (normalResult { config with env := env' })
            | none => none
    | _fuel + 1, config, Stmt.funDef _ _ _ _ =>
        some (normalResult config)
    | _fuel + 1, config, Stmt.assign name expr =>
        match evalExpr hash expr config with
        | some (value, config') =>
            match assign? config'.env name value with
            | some env' => some (normalResult { config' with env := env' })
            | none => none
        | none => none
    | _fuel + 1, config, Stmt.assignMany names exprs =>
        match evalExprsAsYulValues hash exprs config with
        | some (values, config') =>
            match assignMany? config'.env names values with
            | some env' => some (normalResult { config' with env := env' })
            | none => none
        | none => none
    | fuel + 1, config, Stmt.letCall names fnName args =>
        match evalExprs hash args config with
        | some (argValues, config') =>
            match evalFunctionFuel hash funcs fuel fnName argValues config' with
            | some (returnValues, config'') =>
                match declareMany? config''.env names returnValues with
                | some env' => some (normalResult { config'' with env := env' })
                | none => none
            | none => none
        | none => none
    | fuel + 1, config, Stmt.assignCall names fnName args =>
        match evalExprs hash args config with
        | some (argValues, config') =>
            match evalFunctionFuel hash funcs fuel fnName argValues config' with
            | some (returnValues, config'') =>
                match assignMany? config''.env names returnValues with
                | some env' => some (normalResult { config'' with env := env' })
                | none => none
            | none => none
        | none => none
    | fuel + 1, config, Stmt.seq first second =>
        match evalProgramStmtFuel hash funcs fuel config first with
        | some { flow := Flow.normal, config := config' } =>
            evalProgramStmtFuel hash funcs fuel config' second
        | some result => some result
        | none => none
    | fuel + 1, config, Stmt.block stmts =>
        match evalProgramBlockFuel hash funcs fuel config stmts with
        | some result => withRestoredConfig config result
        | none => none
    | fuel + 1, config, Stmt.ifThen cond body =>
        match evalExpr hash cond config with
        | some (value, config') =>
            if norm value = 0 then some (normalResult config')
            else evalProgramStmtFuel hash funcs fuel config' body
        | none => none
    | fuel + 1, config, Stmt.switch discr cases defaultBranch =>
        match evalExpr hash discr config with
        | some (value, config') =>
            match switchTarget? value cases defaultBranch with
            | some branch => evalProgramStmtFuel hash funcs fuel config' branch
            | none => some (normalResult config')
        | none => none
    | fuel + 1, config, Stmt.forLoop pre cond post body =>
        match evalProgramStmtFuel hash funcs fuel config pre with
        | some { flow := Flow.normal, config := loopConfig } =>
            evalProgramForFuel hash funcs fuel config loopConfig cond post body
        | some result => withRestoredConfig config result
        | none => none
    | _fuel + 1, config, Stmt.break =>
        some { flow := Flow.broke, config := config }
    | _fuel + 1, config, Stmt.continue =>
        some { flow := Flow.continued, config := config }
    | _fuel + 1, config, Stmt.leave =>
        some { flow := Flow.left, config := config }

  def evalProgramBlockFuel (hash : HashOracle) (funcs : FunctionEnv) :
      Nat -> Config -> List Stmt -> Option Result
    | 0, _, _ => none
    | _fuel + 1, config, [] => some (normalResult config)
    | fuel + 1, config, stmt :: rest =>
        match evalProgramStmtFuel hash funcs fuel config stmt with
        | some { flow := Flow.normal, config := config' } =>
            evalProgramBlockFuel hash funcs fuel config' rest
        | some result => some result
        | none => none

  def evalProgramForFuel (hash : HashOracle) (funcs : FunctionEnv) :
      Nat -> Config -> Config -> Expr -> Stmt -> Stmt -> Option Result
    | 0, _, _, _, _, _ => none
    | fuel + 1, outer, loopConfig, cond, post, body =>
        match evalExpr hash cond loopConfig with
        | some (value, condConfig) =>
            if norm value = 0 then
              match restoreBlockConfig outer condConfig with
              | some config' => some (normalResult config')
              | none => none
            else
              match evalProgramStmtFuel hash funcs fuel condConfig body with
              | some { flow := Flow.normal, config := bodyConfig } =>
                  match evalProgramStmtFuel hash funcs fuel bodyConfig post with
                  | some { flow := Flow.normal, config := postConfig } =>
                      evalProgramForFuel hash funcs fuel outer postConfig cond post body
                  | some { flow := Flow.continued, config := postConfig } =>
                      evalProgramForFuel hash funcs fuel outer postConfig cond post body
                  | some { flow := Flow.broke, config := postConfig } =>
                      match restoreBlockConfig outer postConfig with
                      | some config' => some (normalResult config')
                      | none => none
                  | some { flow := Flow.left, config := postConfig } =>
                      match restoreBlockConfig outer postConfig with
                      | some config' => some { flow := Flow.left, config := config' }
                      | none => none
                  | some { flow := Flow.halted, config := postConfig } =>
                      match restoreBlockConfig outer postConfig with
                      | some config' => some { flow := Flow.halted, config := config' }
                      | none => none
                  | none => none
              | some { flow := Flow.continued, config := bodyConfig } =>
                  match evalProgramStmtFuel hash funcs fuel bodyConfig post with
                  | some { flow := Flow.normal, config := postConfig } =>
                      evalProgramForFuel hash funcs fuel outer postConfig cond post body
                  | some { flow := Flow.continued, config := postConfig } =>
                      evalProgramForFuel hash funcs fuel outer postConfig cond post body
                  | some { flow := Flow.broke, config := postConfig } =>
                      match restoreBlockConfig outer postConfig with
                      | some config' => some (normalResult config')
                      | none => none
                  | some { flow := Flow.left, config := postConfig } =>
                      match restoreBlockConfig outer postConfig with
                      | some config' => some { flow := Flow.left, config := config' }
                      | none => none
                  | some { flow := Flow.halted, config := postConfig } =>
                      match restoreBlockConfig outer postConfig with
                      | some config' => some { flow := Flow.halted, config := config' }
                      | none => none
                  | none => none
              | some { flow := Flow.broke, config := bodyConfig } =>
                  match restoreBlockConfig outer bodyConfig with
                  | some config' => some (normalResult config')
                  | none => none
              | some { flow := Flow.left, config := bodyConfig } =>
                  match restoreBlockConfig outer bodyConfig with
                  | some config' => some { flow := Flow.left, config := config' }
                  | none => none
              | some { flow := Flow.halted, config := bodyConfig } =>
                  match restoreBlockConfig outer bodyConfig with
                  | some config' => some { flow := Flow.halted, config := config' }
                  | none => none
              | none => none
        | none => none

  def evalFunctionFuel (hash : HashOracle) (funcs : FunctionEnv) :
      Nat -> Name -> List Word -> Config -> Option (List Word × Config)
    | 0, _, _, _ => none
    | fuel + 1, fnName, args, callerConfig =>
        match lookupFunction? funcs fnName with
        | some fn =>
            match initFunctionEnv fn.params args fn.returns with
            | some callEnv =>
                let callConfig := { callerConfig with env := callEnv }
                match evalProgramStmtFuel hash funcs fuel callConfig fn.body with
                | some { flow := Flow.normal, config := resultConfig } =>
                    match valuesForNames? resultConfig.env fn.returns with
                    | some values => some (values, { resultConfig with env := callerConfig.env })
                    | none => none
                | some { flow := Flow.left, config := resultConfig } =>
                    match valuesForNames? resultConfig.env fn.returns with
                    | some values => some (values, { resultConfig with env := callerConfig.env })
                    | none => none
                | some _ => none
                | none => none
            | none => none
        | none => none
end

structure RuntimeConfig where
  env : Env := []
  state : State := State.empty
  object : Object := {}
  funcs : FunctionEnv := []
  deriving Repr

def RuntimeConfig.empty : RuntimeConfig := {}

def RuntimeConfig.toConfig (config : RuntimeConfig) : Config :=
  { env := config.env, state := config.state, object := config.object }

def RuntimeConfig.withConfig (runtime : RuntimeConfig) (config : Config) :
    RuntimeConfig :=
  { runtime with env := config.env, state := config.state, object := config.object }

structure Program where
  object : Object := {}
  body : Stmt
  deriving Repr

def RuntimeConfig.forProgram (program : Program) : RuntimeConfig :=
  { RuntimeConfig.empty with
    object := program.object
    state := { State.empty with code := program.object.code } }

inductive CompleteFlow where
  | normal
  | broke
  | continued
  | left
  | halted
  deriving DecidableEq, Repr

def CompleteFlow.toFlow : CompleteFlow -> Flow
  | CompleteFlow.normal => Flow.normal
  | CompleteFlow.broke => Flow.broke
  | CompleteFlow.continued => Flow.continued
  | CompleteFlow.left => Flow.left
  | CompleteFlow.halted => Flow.halted

structure RuntimeResult where
  flow : CompleteFlow
  config : RuntimeConfig
  deriving Repr

def runtimeNormalResult (config : RuntimeConfig) : RuntimeResult :=
  { flow := CompleteFlow.normal, config := config }

def runtimeResultAfterExpr (config : RuntimeConfig) : RuntimeResult :=
  match config.state.halt? with
  | some _ => { flow := CompleteFlow.halted, config := config }
  | none => runtimeNormalResult config

def evalRuntimeExpr (hash : HashOracle) (expr : Expr)
    (config : RuntimeConfig) : Option (Word × RuntimeConfig) :=
  match evalExpr hash expr config.toConfig with
  | some (value, config') => some (value, config.withConfig config')
  | none => none

def evalRuntimeExprs (hash : HashOracle) :
    List Expr -> RuntimeConfig -> Option (List Word × RuntimeConfig)
  | [], config => some ([], config)
  | expr :: rest, config =>
      match evalRuntimeExprs hash rest config with
      | some (values, config') =>
          match evalRuntimeExpr hash expr config' with
          | some (value, config'') => some (value :: values, config'')
          | none => none
      | none => none

def evalRuntimeExprsAsYulValues (hash : HashOracle) (exprs : List Expr)
    (config : RuntimeConfig) : Option (List Word × RuntimeConfig) :=
  match evalExprsAsYulValues hash exprs config.toConfig with
  | some (values, config') => some (values, config.withConfig config')
  | none => none

def restoreRuntimeBlockConfig (outer : RuntimeConfig)
    (inner : RuntimeConfig) : Option RuntimeConfig :=
  match restoreOuter outer.env inner.env with
  | some env' => some { inner with env := env', funcs := outer.funcs }
  | none => none

def withRestoredRuntimeConfig (outer : RuntimeConfig)
    (result : RuntimeResult) : Option RuntimeResult :=
  match restoreRuntimeBlockConfig outer result.config with
  | some config' => some { flow := result.flow, config := config' }
  | none => none

mutual
  def evalRuntimeStmtFuel (hash : HashOracle) :
      Nat -> RuntimeConfig -> Stmt -> Option RuntimeResult
    | 0, _, _ => none
    | _fuel + 1, config, Stmt.skip => some (runtimeNormalResult config)
    | _fuel + 1, config, Stmt.expr expr =>
        match evalRuntimeExpr hash expr config with
        | some (_, config') => some (runtimeResultAfterExpr config')
        | none => none
    | _fuel + 1, config, Stmt.let1 name init =>
        match init with
        | some expr =>
            match evalRuntimeExpr hash expr config with
            | some (value, config') =>
                match declare? config'.env name value with
                | some env' =>
                    some (runtimeNormalResult { config' with env := env' })
                | none => none
            | none => none
        | none =>
            match declare? config.env name 0 with
            | some env' => some (runtimeNormalResult { config with env := env' })
            | none => none
    | _fuel + 1, config, Stmt.letMany names init =>
        match init with
        | some exprs =>
            match evalRuntimeExprsAsYulValues hash exprs config with
            | some (values, config') =>
                match declareMany? config'.env names values with
                | some env' =>
                    some (runtimeNormalResult { config' with env := env' })
                | none => none
            | none => none
        | none =>
            match declareMany? config.env names (names.map (fun _ => 0)) with
            | some env' => some (runtimeNormalResult { config with env := env' })
            | none => none
    | _fuel + 1, config, Stmt.funDef fnName params returns body =>
        let fn : FunctionDef := { params := params, returns := returns, body := body }
        some
          (runtimeNormalResult
            { config with funcs := declareFunction config.funcs fnName fn })
    | _fuel + 1, config, Stmt.assign name expr =>
        match evalRuntimeExpr hash expr config with
        | some (value, config') =>
            match assign? config'.env name value with
            | some env' => some (runtimeNormalResult { config' with env := env' })
            | none => none
        | none => none
    | _fuel + 1, config, Stmt.assignMany names exprs =>
        match evalRuntimeExprsAsYulValues hash exprs config with
        | some (values, config') =>
            match assignMany? config'.env names values with
            | some env' => some (runtimeNormalResult { config' with env := env' })
            | none => none
        | none => none
    | fuel + 1, config, Stmt.letCall names fnName args =>
        match evalRuntimeExprs hash args config with
        | some (argValues, config') =>
            match evalRuntimeFunctionFuel hash fuel fnName argValues config' with
            | some (returnValues, config'') =>
                match declareMany? config''.env names returnValues with
                | some env' =>
                    some (runtimeNormalResult { config'' with env := env' })
                | none => none
            | none => none
        | none => none
    | fuel + 1, config, Stmt.assignCall names fnName args =>
        match evalRuntimeExprs hash args config with
        | some (argValues, config') =>
            match evalRuntimeFunctionFuel hash fuel fnName argValues config' with
            | some (returnValues, config'') =>
                match assignMany? config''.env names returnValues with
                | some env' =>
                    some (runtimeNormalResult { config'' with env := env' })
                | none => none
            | none => none
        | none => none
    | fuel + 1, config, Stmt.seq first second =>
        let config :=
          { config with
            funcs := collectStmtFunctionDefs (Stmt.seq first second) config.funcs }
        match evalRuntimeStmtFuel hash fuel config first with
        | some { flow := CompleteFlow.normal, config := config' } =>
            evalRuntimeStmtFuel hash fuel config' second
        | some result => some result
        | none => none
    | fuel + 1, config, Stmt.block stmts =>
        let blockConfig :=
          { config with funcs := collectBlockFunctionDefs stmts config.funcs }
        match evalRuntimeBlockFuel hash fuel blockConfig stmts with
        | some result => withRestoredRuntimeConfig config result
        | none => none
    | fuel + 1, config, Stmt.ifThen cond body =>
        match evalRuntimeExpr hash cond config with
        | some (value, config') =>
            if norm value = 0 then some (runtimeNormalResult config')
            else evalRuntimeStmtFuel hash fuel config' body
        | none => none
    | fuel + 1, config, Stmt.switch discr cases defaultBranch =>
        match evalRuntimeExpr hash discr config with
        | some (value, config') =>
            match switchTarget? value cases defaultBranch with
            | some branch => evalRuntimeStmtFuel hash fuel config' branch
            | none => some (runtimeNormalResult config')
        | none => none
    | fuel + 1, config, Stmt.forLoop pre cond post body =>
        match evalRuntimeStmtFuel hash fuel config pre with
        | some { flow := CompleteFlow.normal, config := loopConfig } =>
            evalRuntimeForFuel hash fuel config loopConfig cond post body
        | some result => withRestoredRuntimeConfig config result
        | none => none
    | _fuel + 1, config, Stmt.break =>
        some { flow := CompleteFlow.broke, config := config }
    | _fuel + 1, config, Stmt.continue =>
        some { flow := CompleteFlow.continued, config := config }
    | _fuel + 1, config, Stmt.leave =>
        some { flow := CompleteFlow.left, config := config }

  def evalRuntimeBlockFuel (hash : HashOracle) :
      Nat -> RuntimeConfig -> List Stmt -> Option RuntimeResult
    | 0, _, _ => none
    | _fuel + 1, config, [] => some (runtimeNormalResult config)
    | fuel + 1, config, stmt :: rest =>
        match evalRuntimeStmtFuel hash fuel config stmt with
        | some { flow := CompleteFlow.normal, config := config' } =>
            evalRuntimeBlockFuel hash fuel config' rest
        | some result => some result
        | none => none

  def evalRuntimeForFuel (hash : HashOracle) :
      Nat -> RuntimeConfig -> RuntimeConfig -> Expr -> Stmt -> Stmt ->
        Option RuntimeResult
    | 0, _, _, _, _, _ => none
    | fuel + 1, outer, loopConfig, cond, post, body =>
        match evalRuntimeExpr hash cond loopConfig with
        | some (value, condConfig) =>
            if norm value = 0 then
              match restoreRuntimeBlockConfig outer condConfig with
              | some config' => some (runtimeNormalResult config')
              | none => none
            else
              match evalRuntimeStmtFuel hash fuel condConfig body with
              | some { flow := CompleteFlow.normal, config := bodyConfig } =>
                  match evalRuntimeStmtFuel hash fuel bodyConfig post with
                  | some { flow := CompleteFlow.normal, config := postConfig } =>
                      evalRuntimeForFuel hash fuel outer postConfig cond post body
                  | some { flow := CompleteFlow.continued, config := postConfig } =>
                      evalRuntimeForFuel hash fuel outer postConfig cond post body
                  | some { flow := CompleteFlow.broke, config := postConfig } =>
                      match restoreRuntimeBlockConfig outer postConfig with
                      | some config' => some (runtimeNormalResult config')
                      | none => none
                  | some { flow := CompleteFlow.left, config := postConfig } =>
                      match restoreRuntimeBlockConfig outer postConfig with
                      | some config' => some { flow := CompleteFlow.left, config := config' }
                      | none => none
                  | some { flow := CompleteFlow.halted, config := postConfig } =>
                      match restoreRuntimeBlockConfig outer postConfig with
                      | some config' => some { flow := CompleteFlow.halted, config := config' }
                      | none => none
                  | none => none
              | some { flow := CompleteFlow.continued, config := bodyConfig } =>
                  match evalRuntimeStmtFuel hash fuel bodyConfig post with
                  | some { flow := CompleteFlow.normal, config := postConfig } =>
                      evalRuntimeForFuel hash fuel outer postConfig cond post body
                  | some { flow := CompleteFlow.continued, config := postConfig } =>
                      evalRuntimeForFuel hash fuel outer postConfig cond post body
                  | some { flow := CompleteFlow.broke, config := postConfig } =>
                      match restoreRuntimeBlockConfig outer postConfig with
                      | some config' => some (runtimeNormalResult config')
                      | none => none
                  | some { flow := CompleteFlow.left, config := postConfig } =>
                      match restoreRuntimeBlockConfig outer postConfig with
                      | some config' => some { flow := CompleteFlow.left, config := config' }
                      | none => none
                  | some { flow := CompleteFlow.halted, config := postConfig } =>
                      match restoreRuntimeBlockConfig outer postConfig with
                      | some config' => some { flow := CompleteFlow.halted, config := config' }
                      | none => none
                  | none => none
              | some { flow := CompleteFlow.broke, config := bodyConfig } =>
                  match restoreRuntimeBlockConfig outer bodyConfig with
                  | some config' => some (runtimeNormalResult config')
                  | none => none
              | some { flow := CompleteFlow.left, config := bodyConfig } =>
                  match restoreRuntimeBlockConfig outer bodyConfig with
                  | some config' => some { flow := CompleteFlow.left, config := config' }
                  | none => none
              | some { flow := CompleteFlow.halted, config := bodyConfig } =>
                  match restoreRuntimeBlockConfig outer bodyConfig with
                  | some config' => some { flow := CompleteFlow.halted, config := config' }
                  | none => none
              | none => none
        | none => none

  def evalRuntimeFunctionFuel (hash : HashOracle) :
      Nat -> Name -> List Word -> RuntimeConfig ->
        Option (List Word × RuntimeConfig)
    | 0, _, _, _ => none
    | fuel + 1, fnName, args, callerConfig =>
        match lookupFunction? callerConfig.funcs fnName with
        | some fn =>
            match initFunctionEnv fn.params args fn.returns with
            | some callEnv =>
                let callConfig :=
                  { callerConfig with
                    env := callEnv
                    funcs := collectStmtFunctionDefs fn.body callerConfig.funcs }
                match evalRuntimeStmtFuel hash fuel callConfig fn.body with
                | some { flow := CompleteFlow.normal, config := resultConfig } =>
                    match valuesForNames? resultConfig.env fn.returns with
                    | some values =>
                        some
                          ( values
                          , { resultConfig with
                              env := callerConfig.env
                              funcs := callerConfig.funcs } )
                    | none => none
                | some { flow := CompleteFlow.left, config := resultConfig } =>
                    match valuesForNames? resultConfig.env fn.returns with
                    | some values =>
                        some
                          ( values
                          , { resultConfig with
                              env := callerConfig.env
                              funcs := callerConfig.funcs } )
                    | none => none
                | some _ => none
                | none => none
            | none => none
        | none => none
end

def runStmtFuel (hash : HashOracle) (fuel : Nat) (stmt : Stmt) :
    Option RuntimeResult :=
  evalRuntimeStmtFuel hash fuel RuntimeConfig.empty stmt

def runProgramFuel (hash : HashOracle) (fuel : Nat)
    (program : Program) : Option RuntimeResult :=
  evalRuntimeStmtFuel hash fuel (RuntimeConfig.forProgram program) program.body

theorem evalRuntimeFunctionFuel_restores_caller_frame
    {hash : HashOracle} {fuel : Nat}
    {fnName : Name} {args values : List Word}
    {callerConfig afterConfig : RuntimeConfig}
    (h : evalRuntimeFunctionFuel hash fuel fnName args callerConfig =
      some (values, afterConfig)) :
    afterConfig.env = callerConfig.env ∧
      afterConfig.funcs = callerConfig.funcs := by
  cases fuel with
  | zero =>
      simp [evalRuntimeFunctionFuel] at h
  | succ fuel =>
      simp [evalRuntimeFunctionFuel] at h
      repeat
        first
        | split at h
        | contradiction
        | cases h; constructor <;> rfl

theorem evalFunctionFuel_restores_caller_env
    {hash : HashOracle} {funcs : FunctionEnv} {fuel : Nat}
    {fnName : Name} {args values : List Word} {callerConfig afterConfig : Config}
    (h : evalFunctionFuel hash funcs fuel fnName args callerConfig =
      some (values, afterConfig)) :
    afterConfig.env = callerConfig.env := by
  cases fuel with
  | zero =>
      simp [evalFunctionFuel] at h
  | succ fuel =>
      simp [evalFunctionFuel] at h
      repeat
        first
        | split at h
        | contradiction
        | cases h; rfl

theorem readBytes_pads_past_end :
    readBytes [1, 2] 1 4 = [2, 0, 0, 0] := by
  rfl

theorem evalStmtFuel_zero
    (hash : HashOracle) (config : Config) (stmt : Stmt) :
    evalStmtFuel hash 0 config stmt = none := by
  rfl

theorem evalBlockFuel_zero
    (hash : HashOracle) (config : Config) (stmts : List Stmt) :
    evalBlockFuel hash 0 config stmts = none := by
  rfl

theorem evalForFuel_zero
    (hash : HashOracle) (outer loopConfig : Config) (cond : Expr)
    (post body : Stmt) :
    evalForFuel hash 0 outer loopConfig cond post body = none := by
  rfl

theorem evalProgramStmtFuel_zero
    (hash : HashOracle) (funcs : FunctionEnv) (config : Config) (stmt : Stmt) :
    evalProgramStmtFuel hash funcs 0 config stmt = none := by
  rfl

theorem evalProgramBlockFuel_zero
    (hash : HashOracle) (funcs : FunctionEnv) (config : Config)
    (stmts : List Stmt) :
    evalProgramBlockFuel hash funcs 0 config stmts = none := by
  rfl

theorem evalProgramForFuel_zero
    (hash : HashOracle) (funcs : FunctionEnv) (outer loopConfig : Config)
    (cond : Expr) (post body : Stmt) :
    evalProgramForFuel hash funcs 0 outer loopConfig cond post body = none := by
  rfl

theorem evalFunctionFuel_zero
    (hash : HashOracle) (funcs : FunctionEnv) (name : Name)
    (args : List Word) (callerConfig : Config) :
    evalFunctionFuel hash funcs 0 name args callerConfig = none := by
  rfl

theorem evalRuntimeStmtFuel_zero
    (hash : HashOracle) (config : RuntimeConfig) (stmt : Stmt) :
    evalRuntimeStmtFuel hash 0 config stmt = none := by
  rfl

theorem evalRuntimeBlockFuel_zero
    (hash : HashOracle) (config : RuntimeConfig) (stmts : List Stmt) :
    evalRuntimeBlockFuel hash 0 config stmts = none := by
  rfl

theorem evalRuntimeForFuel_zero
    (hash : HashOracle) (outer loopConfig : RuntimeConfig) (cond : Expr)
    (post body : Stmt) :
    evalRuntimeForFuel hash 0 outer loopConfig cond post body = none := by
  rfl

theorem evalRuntimeFunctionFuel_zero
    (hash : HashOracle) (name : Name) (args : List Word)
    (callerConfig : RuntimeConfig) :
    evalRuntimeFunctionFuel hash 0 name args callerConfig = none := by
  rfl

theorem writeByte_extends_with_zeroes :
    writeByte [] 2 9 = [0, 0, 9] := by
  rfl

theorem bytesToWord_single_low_byte :
    bytesToWord (zeroBytes 31 ++ [7]) = 7 := by
  rfl

theorem mstore_writes_word_bytes (hash : HashOracle) :
    evalBuiltin hash Evm.Builtin.mstore [0, 7] State.empty =
      some (0, { State.empty with memory := writeWord [] 0 7, memorySize := 32 }) := by
  rfl

theorem mload_reads_concrete_word (hash : HashOracle) :
    evalBuiltin hash Evm.Builtin.mload [0]
        { State.empty with memory := zeroBytes 31 ++ [7] } =
      some (7, { State.empty with memory := zeroBytes 31 ++ [7], memorySize := 32 }) := by
  rfl

theorem mstore8_writes_low_byte_and_expands (hash : HashOracle) :
    evalBuiltin hash Evm.Builtin.mstore8 [31, 263] State.empty =
      some (0, { State.empty with memory := zeroBytes 31 ++ [7], memorySize := 32 }) := by
  rfl

theorem msize_tracks_active_memory_not_backing_length (hash : HashOracle) :
    evalBuiltin hash Evm.Builtin.msizeOp []
        { State.empty with memory := zeroBytes 64, memorySize := 32 } =
      some (32, { State.empty with memory := zeroBytes 64, memorySize := 32 }) := by
  rfl

theorem calldatacopy_writes_concrete_bytes (hash : HashOracle) :
    evalBuiltin hash Evm.Builtin.calldatacopyOp [2, 1, 3]
        { State.empty with calldata := [10, 11, 12, 13] } =
      some
        ( 0
        , { State.empty with
            calldata := [10, 11, 12, 13]
            memorySize := 32
            memory := [0, 0, 11, 12, 13] } ) := by
  rfl

theorem zero_length_copy_does_not_expand_memory (hash : HashOracle) :
    evalBuiltin hash Evm.Builtin.calldatacopyOp [100, 0, 0] State.empty =
      some (0, State.empty) := by
  rfl

theorem mcopy_overlap_reads_original_bytes (hash : HashOracle) :
    evalBuiltin hash Evm.Builtin.mcopyOp [1, 0, 3]
        { State.empty with memory := [1, 2, 3, 4] } =
      some
        ( 0
        , { State.empty with memory := [1, 1, 2, 3], memorySize := 32 } ) := by
  rfl

theorem datacopy_writes_concrete_code_bytes (hash : HashOracle) :
    evalBuiltin hash Evm.Builtin.datacopyOp [2, 1, 3]
        { State.empty with code := [10, 11, 12, 13] } =
      some
        ( 0
        , { State.empty with
            code := [10, 11, 12, 13]
            memorySize := 32
            memory := [0, 0, 11, 12, 13] } ) := by
  rfl

theorem keccak_reads_concrete_memory_slice (hash : HashOracle) :
    evalBuiltin hash Evm.Builtin.keccak256Op [1, 3]
        { State.empty with memory := [10, 11, 12, 13, 14] } =
      some
        ( norm (hash.keccak256 [11, 12, 13])
        , { State.empty with memory := [10, 11, 12, 13, 14], memorySize := 32 } ) := by
  rfl

theorem return_halts_with_memory_slice (hash : HashOracle) :
    evalBuiltin hash Evm.Builtin.returnOp [1, 3]
        { State.empty with memory := [10, 11, 12, 13, 14] } =
      some
        ( 0
        , { State.empty with
            memory := [10, 11, 12, 13, 14]
            memorySize := 32
            halt? := some
              { kind := Evm.HaltKind.returned
                returndata := [11, 12, 13] } } ) := by
  rfl

theorem concrete_extra_builtin_ops (hash : HashOracle) :
    evalBuiltin hash Evm.Builtin.signextendOp [0, 128] State.empty =
      some (norm (signextendWord 0 128), State.empty) ∧
    evalBuiltin hash Evm.Builtin.clzOp [0] State.empty =
      some (norm (clzWord 0), State.empty) ∧
    evalBuiltin hash Evm.Builtin.memoryguardOp [64] State.empty =
      some (64, State.empty) := by
  constructor
  · rfl
  constructor <;> rfl

theorem setimmutable_loadimmutable_concrete_roundtrip (hash : HashOracle) :
    evalBuiltin hash Evm.Builtin.loadimmutableOp [1]
        { State.empty with immutables := [(1, 9)] } =
      some (9, { State.empty with immutables := [(1, 9)] }) := by
  rfl

theorem setimmutable_writes_known_memory_positions (hash : HashOracle) :
    evalBuiltin hash Evm.Builtin.setimmutableOp [4, 1, 7]
        { State.empty with immutablePositions := [(1, [0, 32])] } =
      some
        ( 0
        , { State.empty with
            immutables := [(1, 7)]
            immutablePositions := [(1, [0, 32])]
            memory := writeWord (writeWord [] 4 7) 36 7
            memorySize := 96 } ) := by
  rfl

def sampleHash : HashOracle :=
  { keccak256 := fun bytes => bytes.length }

def sampleVerbatimHash : HashOracle :=
  { sampleHash with verbatimValues := fun _ _ => [7, 9] }

def sampleObjectData : Object :=
  { data := [(1, [10, 11, 12])] }

def sampleObjectSections : Object :=
  { objects := [(2, [6, 7, 8])], code := [1, 2, 3, 4] }

theorem evalStmt_datacopy_object_bytes :
    evalStmtFuel sampleHash 4 { Config.empty with object := sampleObjectData }
        (Stmt.expr
          (Expr.builtin Evm.Builtin.datacopyOp
            [Expr.word 0, Expr.dataOffset 1, Expr.dataSize 1])) =
      some
        { flow := Flow.normal
          config :=
            { Config.empty with
              object := sampleObjectData
              state := { State.empty with memory := [10, 11, 12], memorySize := 32 } } } := by
  rfl

theorem evalRuntime_datacopy_object_section_bytes :
    evalRuntimeStmtFuel sampleHash 4
        { RuntimeConfig.empty with object := sampleObjectSections }
        (Stmt.expr
          (Expr.builtin Evm.Builtin.datacopyOp
            [Expr.word 0, Expr.dataOffset 2, Expr.dataSize 2])) =
      some
        { flow := CompleteFlow.normal
          config :=
            { RuntimeConfig.empty with
              object := sampleObjectSections
              state := { State.empty with memory := [6, 7, 8], memorySize := 32 } } } := by
  rfl

theorem runProgram_sets_code_context :
    runProgramFuel sampleHash 3
        { object := sampleObjectSections, body := Stmt.expr (Expr.builtin Evm.Builtin.codesizeOp []) } =
      some
        { flow := CompleteFlow.normal
          config :=
            { RuntimeConfig.empty with
              object := sampleObjectSections
              state := { State.empty with code := [1, 2, 3, 4] } } } := by
  rfl

theorem evalRuntime_multi_output_verbatim_letMany :
    evalRuntimeStmtFuel sampleVerbatimHash 4 RuntimeConfig.empty
        (Stmt.letMany [0, 1]
          (some [Expr.builtin (Evm.Builtin.verbatimOp 1 2) [Expr.word 5]])) =
      some
        { flow := CompleteFlow.normal
          config :=
            { RuntimeConfig.empty with
              env := [(1, 9), (0, 7)]
              state :=
                { State.empty with
                  externalActions :=
                    [{ builtin := Evm.Builtin.verbatimOp 1 2, args := [5] }] } } } := by
  rfl

theorem evalBuiltin_environment_maps (hash : HashOracle) :
    evalBuiltin hash Evm.Builtin.blockhashOp [5]
        { State.empty with blockhashes := [(5, 99)] } =
      some (99, { State.empty with blockhashes := [(5, 99)] }) ∧
    evalBuiltin hash Evm.Builtin.balanceOp [7]
        { State.empty with balances := [(7, 11)] } =
      some (11, { State.empty with balances := [(7, 11)] }) ∧
    evalBuiltin hash Evm.Builtin.extcodesizeOp [8]
        { State.empty with extcodes := [(8, [1, 2, 3])] } =
      some (3, { State.empty with extcodes := [(8, [1, 2, 3])] }) := by
  constructor
  · rfl
  constructor <;> rfl

theorem evalBuiltin_call_uses_host_response_and_copies_returndata :
    evalBuiltin sampleHash Evm.Builtin.callOp [100, 1, 0, 0, 0, 0, 2]
        { State.empty with
          callResponses :=
            [ ( Evm.Builtin.callOp
              , [100, 1, 0, 0, 0, 0, 2]
              , { result := 1, returndata := [9, 8, 7] } ) ] } =
      some
        ( 1
        , { State.empty with
            memory := [9, 8]
            memorySize := 32
            returndata := [9, 8, 7]
            callResponses :=
              [ ( Evm.Builtin.callOp
                , [100, 1, 0, 0, 0, 0, 2]
                , { result := 1, returndata := [9, 8, 7] } ) ]
            externalActions :=
              [{ builtin := Evm.Builtin.callOp
                 args := [100, 1, 0, 0, 0, 0, 2] }] } ) := by
  rfl

theorem evalExprs_right_to_left_args_observable :
    evalExprs sampleHash
        [ Expr.builtin Evm.Builtin.mstore [Expr.word 0, Expr.word 7]
        , Expr.builtin Evm.Builtin.mload [Expr.word 0] ]
        Config.empty =
      some
        ( [0, 0]
        , { Config.empty with
            state := { State.empty with memory := writeWord [] 0 7, memorySize := 32 } } ) := by
  rfl

set_option maxRecDepth 2000 in
theorem evalStmt_mstore_then_mload_to_local :
    evalStmtFuel sampleHash 8 Config.empty
        (Stmt.seq
          (Stmt.expr
            (Expr.builtin Evm.Builtin.mstore [Expr.word 0, Expr.word 7]))
          (Stmt.let1 0
            (some (Expr.builtin Evm.Builtin.mload [Expr.word 0])))) =
      some
        { flow := Flow.normal
          config :=
            { Config.empty with
              env := [(0, 7)]
              state := { State.empty with memory := writeWord [] 0 7, memorySize := 32 } } } := by
  rfl

theorem evalStmt_if_records_storage_effect :
    evalStmtFuel sampleHash 5 Config.empty
        (Stmt.ifThen (Expr.word 1)
          (Stmt.expr
            (Expr.builtin Evm.Builtin.sstore
              [Expr.word 0, Expr.word 7]))) =
      some
        { flow := Flow.normal
          config :=
            { Config.empty with
              state := { State.empty with storage := [(0, [(0, 7)])] } } } := by
  rfl

theorem evalStmt_block_drops_local_keeps_storage :
    evalStmtFuel sampleHash 5 Config.empty
        (Stmt.block
          [ Stmt.let1 0 none
          , Stmt.expr
              (Expr.builtin Evm.Builtin.sstore
                [Expr.word 0, Expr.word 7]) ]) =
      some
        { flow := Flow.normal
          config :=
            { Config.empty with
              state := { State.empty with storage := [(0, [(0, 7)])] } } } := by
  rfl

theorem evalStmt_return_stops_sequence :
    evalStmtFuel sampleHash 5 Config.empty
        (Stmt.seq
          (Stmt.expr
            (Expr.builtin Evm.Builtin.returnOp [Expr.word 0, Expr.word 0]))
          (Stmt.expr
            (Expr.builtin Evm.Builtin.sstore [Expr.word 0, Expr.word 7]))) =
      some
        { flow := Flow.halted
          config :=
            { Config.empty with
              state :=
                { State.empty with
                  halt? := some
                    { kind := Evm.HaltKind.returned
                      returndata := [] } } } } := by
  rfl

theorem sload_reads_latest_storage_write (hash : HashOracle) :
    evalBuiltin hash Evm.Builtin.sload [0]
        { State.empty with storage := [(0, [(0, 9), (0, 7)])] } =
      some (9, { State.empty with storage := [(0, [(0, 9), (0, 7)])] }) := by
  rfl

theorem tload_reads_latest_transient_write (hash : HashOracle) :
    evalBuiltin hash Evm.Builtin.tloadOp [0]
        { State.empty with transientStorage := [(0, [(0, 9), (0, 7)])] } =
      some
        ( 9
        , { State.empty with transientStorage := [(0, [(0, 9), (0, 7)])] } ) := by
  rfl

def addReturnFunction : FunctionDef :=
  { params := [0, 1]
    returns := [2]
    body :=
      Stmt.seq
        (Stmt.assign 2
          (Expr.builtin Evm.Builtin.add [Expr.var 0, Expr.var 1]))
        Stmt.leave }

theorem evalFunction_add_returns_value :
    evalFunctionFuel sampleHash [(10, addReturnFunction)] 8 10 [2, 3]
        Config.empty =
      some ([5], Config.empty) := by
  rfl

theorem evalProgram_assignCall_updates_caller_local :
    evalProgramStmtFuel sampleHash [(10, addReturnFunction)] 10
        { Config.empty with env := [(5, 0)] }
        (Stmt.assignCall [5] 10 [Expr.word 2, Expr.word 3]) =
      some { flow := Flow.normal, config := { Config.empty with env := [(5, 5)] } } := by
  rfl

def inlineReturnFunctionBody : Stmt :=
  Stmt.assign 1 (Expr.var 0)

def inlineReturnFunction : FunctionDef :=
  { params := [0], returns := [1], body := inlineReturnFunctionBody }

theorem evalRuntime_funDef_then_assignCall_updates_caller :
    evalRuntimeStmtFuel sampleHash 8
        { RuntimeConfig.empty with env := [(2, 0)] }
        (Stmt.seq
          (Stmt.funDef 10 [0] [1] inlineReturnFunctionBody)
          (Stmt.assignCall [2] 10 [Expr.word 7])) =
      some
        { flow := CompleteFlow.normal
          config :=
            { RuntimeConfig.empty with
              env := [(2, 7)]
              funcs := [(10, inlineReturnFunction)] } } := by
  rfl

theorem evalRuntime_forward_function_visible_before_declaration :
    evalRuntimeStmtFuel sampleHash 8
        { RuntimeConfig.empty with env := [(2, 0)] }
        (Stmt.seq
          (Stmt.assignCall [2] 10 [Expr.word 7])
          (Stmt.funDef 10 [0] [1] inlineReturnFunctionBody)) =
      some
        { flow := CompleteFlow.normal
          config :=
            { RuntimeConfig.empty with
              env := [(2, 7)]
              funcs := [(10, inlineReturnFunction)] } } := by
  rfl

theorem evalRuntime_block_function_does_not_escape :
    evalRuntimeStmtFuel sampleHash 8 RuntimeConfig.empty
        (Stmt.seq
          (Stmt.block [Stmt.funDef 10 [] [] Stmt.skip])
          (Stmt.letCall [] 10 [])) = none := by
  rfl

def memoryReturnFunction : FunctionDef :=
  { params := []
    returns := [0]
    body :=
      Stmt.seq
        (Stmt.expr
          (Expr.builtin Evm.Builtin.mstore [Expr.word 0, Expr.word 7]))
        (Stmt.seq
          (Stmt.assign 0
            (Expr.builtin Evm.Builtin.mload [Expr.word 0]))
          Stmt.leave) }

set_option maxRecDepth 2000 in
theorem evalFunction_threads_memory_effects :
    evalFunctionFuel sampleHash [(20, memoryReturnFunction)] 10 20 []
        Config.empty =
      some
        ( [7]
        , { Config.empty with
            state := { State.empty with memory := writeWord [] 0 7, memorySize := 32 } } ) := by
  rfl

end ConcreteYul
end SolidCoreYulCore

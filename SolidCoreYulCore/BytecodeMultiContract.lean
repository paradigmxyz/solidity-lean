import SolidCoreYulCore.BytecodeGas

namespace SolidCoreYulCore
namespace BytecodeMultiContract

open BytecodeEvm
open BytecodeGas

def callSuccess (state : MeteredState) : Bool :=
  state.gasError?.isNone &&
    match state.evm.halt? with
    | some HaltKind.stopped => true
    | some HaltKind.returned => true
    | some HaltKind.selfdestructed => true
    | _ => false

def callReturndata (state : MeteredState) : Bytes :=
  match state.evm.halt? with
  | some HaltKind.returned => state.evm.output
  | some HaltKind.reverted => state.evm.output
  | _ => []

def createSuccess (state : MeteredState) : Bool :=
  state.gasError?.isNone &&
    match state.evm.halt? with
    | some HaltKind.stopped => true
    | some HaltKind.returned => true
    | _ => false

def createRuntimeCode (state : MeteredState) : Bytes :=
  match state.evm.halt? with
  | some HaltKind.returned => state.evm.output
  | _ => []

def createReturndata (state : MeteredState) : Bytes :=
  match state.evm.halt? with
  | some HaltKind.returned => state.evm.output
  | some HaltKind.reverted => state.evm.output
  | _ => []

def subBalance? (balance value : Word) : Option Word :=
  if norm value <= norm balance then some (norm balance - norm value) else none

def incrementNonce (account : Account) : Account :=
  { account with nonce := addWord account.nonce 1, destroyed := false }

def accountCollision (account : Account) : Bool :=
  norm account.nonce ≠ 0 || account.code ≠ []

def transferValue? (accounts : AccountMap) (fromAddr toAddr value : Word) :
    Option AccountMap :=
  if norm value = 0 || norm fromAddr = norm toAddr then
    some accounts
  else
    let fromAccount :=
      match lookupAccount? accounts fromAddr with
      | some account => account
      | none => {}
    match subBalance? fromAccount.balance value with
    | none => none
    | some fromBalance =>
        let toAccount :=
          match lookupAccount? accounts toAddr with
          | some account => account
          | none => {}
        let accountsAfterDebit :=
          writeAccount accounts fromAddr
            { fromAccount with balance := fromBalance, destroyed := false }
        some
          (writeAccount accountsAfterDebit toAddr
            { toAccount with
              balance := addWord toAccount.balance value,
              destroyed := false })

def accountsBeforeCall? (parent : State) (call : ExternalCall) :
    Option AccountMap :=
  match call.kind with
  | ExternalCallKind.call =>
      transferValue? parent.accounts call.caller call.to call.value
  | ExternalCallKind.callcode => some parent.accounts
  | ExternalCallKind.delegatecall => some parent.accounts
  | ExternalCallKind.staticcall => some parent.accounts

def addressBytes20 (address : Word) : Bytes :=
  (wordToBytes32 address).drop 12

def low160 (value : Word) : Word :=
  norm value % (2 ^ 160)

def dropLeadingZeroBytes : Bytes → Bytes
  | [] => []
  | value :: rest =>
      if byte value = 0 then dropLeadingZeroBytes rest else value :: rest

def wordToMinimalBytes (value : Word) : Bytes :=
  dropLeadingZeroBytes (wordToBytes32 value)

def rlpWord (value : Word) : Bytes :=
  if norm value = 0 then
    [0x80]
  else if norm value < 128 then
    [byte value]
  else
    let bytes := wordToMinimalBytes value
    byte (0x80 + bytes.length) :: bytes

def createAddressPreimage (creator nonce : Word) : Bytes :=
  let payload := [0x94] ++ addressBytes20 creator ++ rlpWord nonce
  byte (0xc0 + payload.length) :: payload

def create2AddressPreimage
    (creator salt initCodeHash : Word) : Bytes :=
  [0xff] ++ addressBytes20 creator ++ wordToBytes32 salt ++ wordToBytes32 initCodeHash

inductive AddressDerivation where
  | ok (address : Word)
  | missingHash (data : Bytes)
deriving DecidableEq, Repr

def createdAddressFromState (state : State) (create : ExternalCreate) :
    AddressDerivation :=
  match create.kind with
  | ExternalCreateKind.create =>
      let nonce := (rawAccount state create.creator).nonce
      let preimage := createAddressPreimage create.creator nonce
      match lookupHash? state.keccakHashes preimage with
      | some hash => AddressDerivation.ok (low160 hash)
      | none => AddressDerivation.missingHash preimage
  | ExternalCreateKind.create2 =>
      match lookupHash? state.keccakHashes create.initCode with
      | none => AddressDerivation.missingHash create.initCode
      | some initCodeHash =>
          let preimage := create2AddressPreimage create.creator
            ((create.salt?).getD 0) initCodeHash
          match lookupHash? state.keccakHashes preimage with
          | some hash => AddressDerivation.ok (low160 hash)
          | none => AddressDerivation.missingHash preimage

def createFailureAccounts (accounts : AccountMap) (creator : Word) :
    AccountMap :=
  let creatorAccount :=
    match lookupAccount? accounts creator with
    | some account => account
    | none => {}
  writeAccount accounts creator (incrementNonce creatorAccount)

def accountsBeforeCreate? (parent : State) (create : ExternalCreate)
    (address : Word) : Option AccountMap :=
  let creatorAccount := rawAccount parent create.creator
  match subBalance? creatorAccount.balance create.value with
  | none => none
  | some creatorBalance =>
      let destination := rawAccount parent address
      if accountCollision destination then
        none
      else
        let creatorFinal :=
          { incrementNonce creatorAccount with balance := creatorBalance }
        let createdAccount : Account :=
          { balance := create.value,
            nonce := 1,
            code := [],
            storage := [],
            transientStorage := [],
            createdInTransaction := true,
            destroyed := false }
        some
          (writeAccount
            (writeAccount parent.accounts create.creator creatorFinal)
            address createdAccount)

def childCode (parent : State) (accounts : AccountMap) (call : ExternalCall) :
    Bytes :=
  accountCode { parent with accounts := accounts } call.to

def childState (parent : State) (accounts : AccountMap) (call : ExternalCall) :
    State :=
  { State.empty with
    code := childCode parent accounts call,
    keccakHashes := parent.keccakHashes,
    cheatcodeAddresses := parent.cheatcodeAddresses,
    cheatcodeSignatures := parent.cheatcodeSignatures,
    accounts := accounts,
    tx := parent.tx,
    block := parent.block,
    cheatcodes := parent.cheatcodes,
    call :=
      { address := call.address,
        caller := call.caller,
        callvalue := call.value,
        calldata := call.input,
        returndata := [],
        isStatic := call.isStatic },
    logs := parent.logs }

def createChildState
    (parent : State) (accounts : AccountMap) (create : ExternalCreate)
    (address : Word) : State :=
  { State.empty with
    code := create.initCode,
    keccakHashes := parent.keccakHashes,
    cheatcodeAddresses := parent.cheatcodeAddresses,
    cheatcodeSignatures := parent.cheatcodeSignatures,
    accounts := accounts,
    tx := parent.tx,
    block := parent.block,
    cheatcodes := parent.cheatcodes,
    call :=
      { address := address,
        caller := create.creator,
        callvalue := create.value,
        calldata := [],
        returndata := [],
        isStatic := false },
    logs := parent.logs }

def externalCallWithValue? (state : State)
    (kind : ExternalCallKind) : Option ExternalCall :=
  match state.stack with
  | gas :: to :: value :: argsOffset :: argsSize :: retOffset :: retSize :: _ =>
      if state.call.isStatic = true ∧ norm value ≠ 0 then
        none
      else
        let input := readMemoryBytes state.memory argsOffset argsSize
        some
          { kind := kind,
            gas := gas,
            to := to,
            value := value,
            input := input,
            retOffset := retOffset,
            retSize := retSize,
            caller := state.call.address,
            address :=
              if kind = ExternalCallKind.call then to else state.call.address,
            isStatic := state.call.isStatic }
  | _ => none

def externalCallNoValue? (state : State)
    (kind : ExternalCallKind) : Option ExternalCall :=
  match state.stack with
  | gas :: to :: argsOffset :: argsSize :: retOffset :: retSize :: _ =>
      let input := readMemoryBytes state.memory argsOffset argsSize
      let actionCaller :=
        if kind = ExternalCallKind.delegatecall then
          state.call.caller
        else
          state.call.address
      let actionAddress :=
        if kind = ExternalCallKind.delegatecall then
          state.call.address
        else
          to
      let actionStatic :=
        if kind = ExternalCallKind.staticcall then true else state.call.isStatic
      let actionValue :=
        if kind = ExternalCallKind.delegatecall then state.call.callvalue else 0
      some
        { kind := kind,
          gas := gas,
          to := to,
          value := actionValue,
          input := input,
          retOffset := retOffset,
          retSize := retSize,
          caller := actionCaller,
          address := actionAddress,
          isStatic := actionStatic }
  | _ => none

def externalCallForOpcode? (opcode : Opcode) (state : State) :
    Option ExternalCall :=
  match opcode with
  | Opcode.call => externalCallWithValue? state ExternalCallKind.call
  | Opcode.callcode => externalCallWithValue? state ExternalCallKind.callcode
  | Opcode.delegatecall =>
      externalCallNoValue? state ExternalCallKind.delegatecall
  | Opcode.staticcall =>
      externalCallNoValue? state ExternalCallKind.staticcall
  | _ => none

def externalCreateForOpcode? (opcode : Opcode) (state : State) :
    Option ExternalCreate :=
  match opcode with
  | Opcode.create =>
      match state.stack with
      | value :: offset :: size :: _ =>
          if state.call.isStatic then
            none
          else
            some
              { kind := ExternalCreateKind.create,
                value := value,
                initCode := readMemoryBytes state.memory offset size,
                creator := state.call.address }
      | _ => none
  | Opcode.create2 =>
      match state.stack with
      | value :: offset :: size :: salt :: _ =>
          if state.call.isStatic then
            none
          else
            some
              { kind := ExternalCreateKind.create2,
                value := value,
                initCode := readMemoryBytes state.memory offset size,
                salt? := some salt,
                creator := state.call.address }
      | _ => none
  | _ => none

def childInitialMeteredState
    (parent : MeteredState) (effects : MeterEffects) (call : ExternalCall)
    (childGas : Gas) (accounts : AccountMap) : MeteredState :=
  let afterCallAccess := applyMeterEffects effects parent
  { MeteredState.ofStateOsaka (childState parent.evm accounts call) childGas with
    originalAccounts := parent.originalAccounts,
    accessedAddresses := afterCallAccess.accessedAddresses,
    accessedStorageKeys := afterCallAccess.accessedStorageKeys,
    refund := afterCallAccess.refund }

def createChildInitialMeteredState
    (parent : MeteredState) (effects : MeterEffects) (create : ExternalCreate)
    (createdAddress : Word) (childGas : Gas) (accounts : AccountMap) :
    MeteredState :=
  let afterCreateAccess := applyMeterEffects effects parent
  { MeteredState.ofStateOsaka
      (createChildState parent.evm accounts create createdAddress) childGas with
    originalAccounts := parent.originalAccounts,
    accessedAddresses :=
      insertWordSet createdAddress afterCreateAccess.accessedAddresses,
    accessedStorageKeys := afterCreateAccess.accessedStorageKeys,
    refund := afterCreateAccess.refund }

def failedCallResult (accounts : AccountMap) (gasRemaining : Gas) :
    ExternalResult :=
  { success := false,
    returndata := [],
    accounts? := some accounts,
    gasRemaining := gasRemaining }

def failedCreateResult (accounts : AccountMap) (gasRemaining : Gas) :
    ExternalResult :=
  { success := false,
    returndata := [],
    accounts? := some accounts,
    gasRemaining := gasRemaining }

def setCreatedCode (accounts : AccountMap) (address : Word) (code : Bytes) :
    AccountMap :=
  let account :=
    match lookupAccount? accounts address with
    | some account => account
    | none => {}
  writeAccount accounts address
    { account with code := code, destroyed := false, createdInTransaction := true }

def codeDepositCost (code : Bytes) : Gas :=
  GasConst.codeDepositPerByte * code.length

def precompileEcrecoverResult?
    (parent : State) (call : ExternalCall) (childGas : Gas)
    (accounts : AccountMap) : Option ExternalResult :=
  if norm call.to = 1 then
    let cost := GasConst.precompileEcrecover
    if cost <= childGas then
      let digest := readWordFromBytes call.input 0
      let signature : CheatcodeSignature :=
        { v := readWordFromBytes call.input 32
          r := readWordFromBytes call.input 64
          s := readWordFromBytes call.input 96 }
      let returndata :=
        match lookupCheatcodeSignatureSigner?
            parent.cheatcodeSignatures digest signature with
        | none => []
        | some privateKey =>
            match lookupWord? parent.cheatcodeAddresses privateKey with
            | none => []
            | some address => wordToBytes32 (low160 address)
      some
        { success := true,
          returndata := returndata,
          accounts? := some accounts,
          gasRemaining := childGas - cost }
    else
      some
        { success := false,
          returndata := [],
          accounts? := some accounts,
          gasRemaining := 0 }
  else
    none

def precompileIdentityResult?
    (call : ExternalCall) (childGas : Gas) (accounts : AccountMap) :
    Option ExternalResult :=
  if norm call.to = 4 then
    let cost :=
      GasConst.precompileIdentityBase +
        GasConst.precompileIdentityPerWord * wordsForBytes call.input.length
    if cost <= childGas then
      some
        { success := true,
          returndata := call.input,
          accounts? := some accounts,
          gasRemaining := childGas - cost }
    else
      some
        { success := false,
          returndata := [],
          accounts? := some accounts,
          gasRemaining := 0 }
  else
    none

def precompileResult?
    (parent : State) (call : ExternalCall) (childGas : Gas) (accounts : AccountMap) :
    Option ExternalResult :=
  match precompileEcrecoverResult? parent call childGas accounts with
  | some result => some result
  | none => precompileIdentityResult? call childGas accounts

structure CallOutcome where
  result : ExternalResult
  parentEvm : State
  logs : List LogEntry
  accessState : MeteredState
deriving DecidableEq, Repr

def missingHashError? (state : MeteredState) : Option Bytes :=
  match state.evm.error? with
  | some (StepError.missingHash data) => some data
  | _ => none

def finishExternalCall
    (opcode : Opcode) (state : MeteredState) (outcome : CallOutcome) :
    MeteredState :=
  let stateWithResult :=
    { state with
      evm :=
        { outcome.parentEvm with
          externalResults := outcome.result :: outcome.parentEvm.externalResults } }
  let parentAfter := meteredStepOpcode osakaCostModel opcode stateWithResult
  { parentAfter with
    accessedAddresses := outcome.accessState.accessedAddresses,
    accessedStorageKeys := outcome.accessState.accessedStorageKeys,
    refund := outcome.accessState.refund,
    evm := { parentAfter.evm with logs := outcome.logs } }

def hevmAddress : Word :=
  0x7109709ECfa91a80626fF3989D68f67F5b1DD12D

def selectorBytes (a b c d : Nat) : Bytes :=
  [byte a, byte b, byte c, byte d]

def isSelector (input selector : Bytes) : Bool :=
  normalizeBytes (input.take 4) = normalizeBytes selector

def successfulCheatcodeResult (childGas : Gas) (accounts : AccountMap) :
    ExternalResult :=
  { success := true,
    returndata := [],
    accounts? := some accounts,
    gasRemaining := childGas }

def successfulCheatcodeResultWithData
    (childGas : Gas) (accounts : AccountMap) (returndata : Bytes) :
    ExternalResult :=
  { success := true,
    returndata := returndata,
    accounts? := some accounts,
    gasRemaining := childGas }

def prankSelector : Bytes := selectorBytes 0xca 0x66 0x9f 0xa7
def prankOriginSelector : Bytes := selectorBytes 0x47 0xe5 0x0c 0xce
def startPrankSelector : Bytes := selectorBytes 0x06 0x44 0x7d 0x56
def startPrankOriginSelector : Bytes := selectorBytes 0x45 0xb5 0x60 0x78
def stopPrankSelector : Bytes := selectorBytes 0x90 0xc5 0x01 0x3b
def loadSelector : Bytes := selectorBytes 0x66 0x7f 0x9d 0x70
def storeSelector : Bytes := selectorBytes 0x70 0xca 0x10 0xbb
def etchSelector : Bytes := selectorBytes 0xb4 0xd6 0xc7 0x82
def getNonceSelector : Bytes := selectorBytes 0x2d 0x03 0x35 0xab
def setNonceSelector : Bytes := selectorBytes 0xf8 0xe1 0x8b 0x57
def expectRevertSelector : Bytes := selectorBytes 0xf2 0x8d 0xce 0xb3
def expectRevertBytes4Selector : Bytes := selectorBytes 0xc3 0x1e 0xb0 0xe0
def expectRevertNoArgsSelector : Bytes := selectorBytes 0xf4 0x84 0x48 0x14
def expectRevertStringSelector : Bytes := selectorBytes 0xba 0xf6 0x4c 0x1b
def expectRevertBytesSelector : Bytes := selectorBytes 0xf2 0x8d 0xce 0xb3
def expectRevertAddressSelector : Bytes := selectorBytes 0xd8 0x14 0xf3 0x8a
def expectRevertBytesAddressSelector : Bytes := selectorBytes 0x61 0xeb 0xcf 0x12
def expectRevertBytes4AddressSelector : Bytes := selectorBytes 0x26 0x0b 0xc5 0xde
def expectEmitSelector : Bytes := selectorBytes 0x44 0x0e 0xd1 0x0d
def expectEmitChecksSelector : Bytes := selectorBytes 0x49 0x1c 0xc7 0xc2
def expectEmitAddressSelector : Bytes := selectorBytes 0x81 0xba 0xd6 0xf3
def expectCallSelector : Bytes := selectorBytes 0xbd 0x6a 0xf4 0x34
def addrSelector : Bytes := selectorBytes 0xff 0xa1 0x86 0x49
def signSelector : Bytes := selectorBytes 0xe3 0x41 0xea 0xa4
def assumeSelector : Bytes := selectorBytes 0x4c 0x63 0xe5 0x62
def warpSelector : Bytes := selectorBytes 0xe5 0xd6 0xbf 0x02
def rollSelector : Bytes := selectorBytes 0x1f 0x7b 0x4f 0x30
def feeSelector : Bytes := selectorBytes 0x39 0xb3 0x7a 0xb0
def chainIdSelector : Bytes := selectorBytes 0x40 0x49 0xdd 0xd2
def txGasPriceSelector : Bytes := selectorBytes 0x48 0xf5 0x0c 0x0f
def coinbaseSelector : Bytes := selectorBytes 0xff 0x48 0x3c 0x54
def prevrandaoSelector : Bytes := selectorBytes 0x3b 0x92 0x55 0x49
def blobbasefeeSelector : Bytes := selectorBytes 0xd7 0xc7 0x42 0x85
def skipSelector : Bytes := selectorBytes 0xb9 0xc0 0x71 0xb4
def rewindSelector : Bytes := selectorBytes 0x2d 0x6c 0x17 0xa3
def dealSelector : Bytes := selectorBytes 0xc8 0x8a 0x5e 0x6d
def dealAdjustSelector : Bytes := selectorBytes 0xe9 0x88 0x36 0x8a
def labelSelector : Bytes := selectorBytes 0xc6 0x57 0xc7 0x18
def recordLogsSelector : Bytes := selectorBytes 0x41 0xaf 0x2f 0x52
def getRecordedLogsSelector : Bytes := selectorBytes 0x19 0x15 0x53 0xa4
def snapshotStateSelector : Bytes := selectorBytes 0x9c 0xd2 0x38 0x35
def revertToStateSelector : Bytes := selectorBytes 0xc2 0x52 0x74 0x05
def warmSlotSelector : Bytes := selectorBytes 0xb2 0x31 0x84 0xcf
def coolSlotSelector : Bytes := selectorBytes 0x8c 0x78 0xe6 0x54
def coolAddressSelector : Bytes := selectorBytes 0x40 0xff 0x9f 0x21

def padRight32 (values : Bytes) : Bytes :=
  values ++ zeroBytes ((32 - values.length % 32) % 32)

def abiEncodeBytes (values : Bytes) : Bytes :=
  wordToBytes32 values.length ++ padRight32 values

def abiEncodeWordArray (values : List Word) : Bytes :=
  wordToBytes32 values.length ++ values.flatMap wordToBytes32

def readAbiBytesArg (input : Bytes) (slotOffset : Word) : Bytes :=
  let dataOffset := readWordFromBytes input slotOffset
  let lengthOffset := 4 + norm dataOffset
  let length := readWordFromBytes input lengthOffset
  readBytes input (lengthOffset + 32) (norm length)

def abiLogStruct (log : LogEntry) : Bytes :=
  let topics := abiEncodeWordArray log.topics
  let data := abiEncodeBytes log.data
  let headSize := 96
  wordToBytes32 headSize ++
    wordToBytes32 (headSize + topics.length) ++
    wordToBytes32 log.address ++
    topics ++
    data

def abiLogArrayDataAux : List Bytes → Nat → Bytes × Bytes
  | [], _ => ([], [])
  | value :: rest, offset =>
      let tailOffset := offset + value.length
      let (heads, tails) := abiLogArrayDataAux rest tailOffset
      (wordToBytes32 offset ++ heads, value ++ tails)

def abiEncodeLogArray (logs : List LogEntry) : Bytes :=
  let encodedLogs := logs.map abiLogStruct
  let firstOffset := encodedLogs.length * 32
  let (heads, tails) := abiLogArrayDataAux encodedLogs firstOffset
  wordToBytes32 logs.length ++ heads ++ tails

def abiEncodeReturnedLogArray (logs : List LogEntry) : Bytes :=
  wordToBytes32 32 ++ abiEncodeLogArray logs

def storeAccountStorage
    (accounts : AccountMap) (address key value : Word) : AccountMap :=
  let account :=
    match lookupAccount? accounts address with
    | some account => account
    | none => {}
  writeAccount accounts address
    { account with storage := writeWord account.storage key value }

def storeAccountCode (accounts : AccountMap) (address : Word) (code : Bytes) :
    AccountMap :=
  let account :=
    match lookupAccount? accounts address with
    | some account => account
    | none => {}
  writeAccount accounts address { account with code := code, destroyed := false }

def storeAccountNonce (accounts : AccountMap) (address nonce : Word) :
    AccountMap :=
  let account :=
    match lookupAccount? accounts address with
    | some account => account
    | none => {}
  writeAccount accounts address { account with nonce := nonce, destroyed := false }

def removeWordSet (value : Word) : List Word → List Word
  | [] => []
  | candidate :: rest =>
      if norm candidate = norm value then
        removeWordSet value rest
      else
        candidate :: removeWordSet value rest

def removeStorageKeySet
    (key : StorageAccessKey) : List StorageAccessKey → List StorageAccessKey
  | [] => []
  | candidate :: rest =>
      if norm candidate.1 = norm key.1 ∧ norm candidate.2 = norm key.2 then
        removeStorageKeySet key rest
      else
        candidate :: removeStorageKeySet key rest

def lookupSnapshot? : List (Word × CheatcodeSnapshot) → Word →
    Option CheatcodeSnapshot
  | [], _ => none
  | (candidate, snapshot) :: rest, key =>
      if norm candidate = norm key then some snapshot else lookupSnapshot? rest key

inductive CheatcodeDecision where
  | notCheatcode
  | handled (outcome : CallOutcome)
  | unsupported (selector : Bytes)
  | error (error : StepError)
deriving DecidableEq, Repr

def handledCheatcode
    (state : MeteredState) (effects : MeterEffects) (childGas : Gas)
    (accounts : AccountMap) (parentEvm : State) (returndata : Bytes) :
    CheatcodeDecision :=
  CheatcodeDecision.handled
    { result :=
        successfulCheatcodeResultWithData childGas accounts returndata,
      parentEvm := parentEvm,
      logs := parentEvm.logs,
      accessState := applyMeterEffects effects { state with evm := parentEvm } }

def handledCheatcodeNoData
    (state : MeteredState) (effects : MeterEffects) (childGas : Gas)
    (accounts : AccountMap) (parentEvm : State) : CheatcodeDecision :=
  handledCheatcode state effects childGas accounts parentEvm []

def cheatcodeDecision
    (state : MeteredState) (effects : MeterEffects) (call : ExternalCall)
    (childGas : Gas) (accounts : AccountMap) : CheatcodeDecision :=
  if norm call.to = norm hevmAddress then
    if isSelector call.input prankSelector then
      let prankCaller := low160 (readWordFromBytes call.input 4)
      let parentEvm :=
        { state.evm with
          cheatcodes := { state.evm.cheatcodes with prankCaller? := some prankCaller } }
      handledCheatcodeNoData state effects childGas accounts parentEvm
    else if isSelector call.input prankOriginSelector then
      let prankCaller := low160 (readWordFromBytes call.input 4)
      let parentEvm :=
        { state.evm with
          cheatcodes := { state.evm.cheatcodes with prankCaller? := some prankCaller } }
      handledCheatcodeNoData state effects childGas accounts parentEvm
    else if isSelector call.input startPrankSelector then
      let prankCaller := low160 (readWordFromBytes call.input 4)
      let parentEvm :=
        { state.evm with
          cheatcodes :=
            { state.evm.cheatcodes with persistentPrankCaller? := some prankCaller } }
      handledCheatcodeNoData state effects childGas accounts parentEvm
    else if isSelector call.input startPrankOriginSelector then
      let prankCaller := low160 (readWordFromBytes call.input 4)
      let parentEvm :=
        { state.evm with
          cheatcodes :=
            { state.evm.cheatcodes with persistentPrankCaller? := some prankCaller } }
      handledCheatcodeNoData state effects childGas accounts parentEvm
    else if isSelector call.input stopPrankSelector then
      let parentEvm :=
        { state.evm with
          cheatcodes :=
            { state.evm.cheatcodes with
              prankCaller? := none,
              persistentPrankCaller? := none } }
      handledCheatcodeNoData state effects childGas accounts parentEvm
    else if isSelector call.input loadSelector then
      let target := low160 (readWordFromBytes call.input 4)
      let key := readWordFromBytes call.input 36
      let value := (lookupWord? (rawAccount state.evm target).storage key).getD 0
      handledCheatcode state effects childGas accounts state.evm
        (wordToBytes32 value)
    else if isSelector call.input storeSelector then
      let target := low160 (readWordFromBytes call.input 4)
      let key := readWordFromBytes call.input 36
      let value := readWordFromBytes call.input 68
      let accounts' := storeAccountStorage accounts target key value
      let parentEvm := { state.evm with accounts := accounts' }
      handledCheatcodeNoData state effects childGas accounts' parentEvm
    else if isSelector call.input etchSelector then
      let target := low160 (readWordFromBytes call.input 4)
      let code := readAbiBytesArg call.input 36
      let accounts' := storeAccountCode accounts target code
      let parentEvm := { state.evm with accounts := accounts' }
      handledCheatcodeNoData state effects childGas accounts' parentEvm
    else if isSelector call.input getNonceSelector then
      let target := low160 (readWordFromBytes call.input 4)
      let nonce := (rawAccount state.evm target).nonce
      handledCheatcode state effects childGas accounts state.evm
        (wordToBytes32 nonce)
    else if isSelector call.input setNonceSelector then
      let target := low160 (readWordFromBytes call.input 4)
      let nonce := readWordFromBytes call.input 36
      let accounts' := storeAccountNonce accounts target nonce
      let parentEvm := { state.evm with accounts := accounts' }
      handledCheatcodeNoData state effects childGas accounts' parentEvm
    else if isSelector call.input expectRevertSelector ||
        isSelector call.input expectRevertBytes4Selector ||
        isSelector call.input expectRevertNoArgsSelector ||
        isSelector call.input expectRevertStringSelector ||
        isSelector call.input expectRevertAddressSelector ||
        isSelector call.input expectRevertBytesAddressSelector ||
        isSelector call.input expectRevertBytes4AddressSelector then
      let parentEvm :=
        { state.evm with
          cheatcodes := { state.evm.cheatcodes with expectRevert := true } }
      handledCheatcodeNoData state effects childGas accounts parentEvm
    else if isSelector call.input expectEmitSelector ||
        isSelector call.input expectEmitChecksSelector ||
        isSelector call.input expectEmitAddressSelector ||
        isSelector call.input expectCallSelector ||
        isSelector call.input labelSelector then
      handledCheatcodeNoData state effects childGas accounts state.evm
    else if isSelector call.input addrSelector then
      let privateKey := readWordFromBytes call.input 4
      match lookupWord? state.evm.cheatcodeAddresses privateKey with
      | some address =>
          handledCheatcode state effects childGas accounts state.evm
            (wordToBytes32 (low160 address))
      | none =>
          CheatcodeDecision.error (StepError.missingCheatcodeAddress privateKey)
    else if isSelector call.input signSelector then
      let privateKey := readWordFromBytes call.input 4
      let digest := readWordFromBytes call.input 36
      match lookupCheatcodeSignature? state.evm.cheatcodeSignatures privateKey digest with
      | some signature =>
          handledCheatcode state effects childGas accounts state.evm
            (wordToBytes32 signature.v ++ wordToBytes32 signature.r ++ wordToBytes32 signature.s)
      | none =>
          CheatcodeDecision.error
            (StepError.missingCheatcodeSignature privateKey digest)
    else if isSelector call.input assumeSelector then
      let condition := readWordFromBytes call.input 4
      if norm condition = 0 then
        CheatcodeDecision.unsupported (call.input.take 4)
      else
        handledCheatcodeNoData state effects childGas accounts state.evm
    else if isSelector call.input warpSelector then
      let timestamp := readWordFromBytes call.input 4
      let parentEvm := { state.evm with block := { state.evm.block with timestamp := timestamp } }
      handledCheatcodeNoData state effects childGas accounts parentEvm
    else if isSelector call.input rollSelector then
      let number := readWordFromBytes call.input 4
      let parentEvm := { state.evm with block := { state.evm.block with number := number } }
      handledCheatcodeNoData state effects childGas accounts parentEvm
    else if isSelector call.input feeSelector then
      let basefee := readWordFromBytes call.input 4
      let parentEvm := { state.evm with block := { state.evm.block with basefee := basefee } }
      handledCheatcodeNoData state effects childGas accounts parentEvm
    else if isSelector call.input chainIdSelector then
      let chainid := readWordFromBytes call.input 4
      let parentEvm := { state.evm with block := { state.evm.block with chainid := chainid } }
      handledCheatcodeNoData state effects childGas accounts parentEvm
    else if isSelector call.input txGasPriceSelector then
      let gasprice := readWordFromBytes call.input 4
      let parentEvm := { state.evm with tx := { state.evm.tx with gasprice := gasprice } }
      handledCheatcodeNoData state effects childGas accounts parentEvm
    else if isSelector call.input coinbaseSelector then
      let coinbase := low160 (readWordFromBytes call.input 4)
      let parentEvm := { state.evm with block := { state.evm.block with coinbase := coinbase } }
      handledCheatcodeNoData state effects childGas accounts parentEvm
    else if isSelector call.input prevrandaoSelector then
      let prevrandao := readWordFromBytes call.input 4
      let parentEvm := { state.evm with block := { state.evm.block with prevrandao := prevrandao } }
      handledCheatcodeNoData state effects childGas accounts parentEvm
    else if isSelector call.input blobbasefeeSelector then
      let blobbasefee := readWordFromBytes call.input 4
      let parentEvm := { state.evm with block := { state.evm.block with blobbasefee := blobbasefee } }
      handledCheatcodeNoData state effects childGas accounts parentEvm
    else if isSelector call.input skipSelector then
      let seconds := readWordFromBytes call.input 4
      let timestamp := addWord state.evm.block.timestamp seconds
      let parentEvm := { state.evm with block := { state.evm.block with timestamp := timestamp } }
      handledCheatcodeNoData state effects childGas accounts parentEvm
    else if isSelector call.input rewindSelector then
      let seconds := readWordFromBytes call.input 4
      let timestamp :=
        if norm seconds <= norm state.evm.block.timestamp then
          norm state.evm.block.timestamp - norm seconds
        else
          0
      let parentEvm := { state.evm with block := { state.evm.block with timestamp := timestamp } }
      handledCheatcodeNoData state effects childGas accounts parentEvm
    else if isSelector call.input dealSelector then
      let target := low160 (readWordFromBytes call.input 4)
      let balance := readWordFromBytes call.input 36
      let account :=
        match lookupAccount? accounts target with
        | some account => account
        | none => {}
      let accounts' :=
        writeAccount accounts target
          { account with balance := balance, destroyed := false }
      let parentEvm := { state.evm with accounts := accounts' }
      handledCheatcodeNoData state effects childGas accounts' parentEvm
    else if isSelector call.input dealAdjustSelector then
      let target := low160 (readWordFromBytes call.input 4)
      let balance := readWordFromBytes call.input 36
      let account :=
        match lookupAccount? accounts target with
        | some account => account
        | none => {}
      let accounts' :=
        writeAccount accounts target
          { account with balance := balance, destroyed := false }
      let parentEvm := { state.evm with accounts := accounts' }
      handledCheatcodeNoData state effects childGas accounts' parentEvm
    else if isSelector call.input recordLogsSelector then
      let parentEvm :=
        { state.evm with
          cheatcodes :=
            { state.evm.cheatcodes with
              recordingLogs := true,
              recordedLogs := [] } }
      handledCheatcodeNoData state effects childGas accounts parentEvm
    else if isSelector call.input getRecordedLogsSelector then
      handledCheatcode state effects childGas accounts state.evm
        (abiEncodeReturnedLogArray state.evm.cheatcodes.recordedLogs.reverse)
    else if isSelector call.input snapshotStateSelector then
      let snapshotId := state.evm.cheatcodes.nextSnapshotId
      let snapshot : CheatcodeSnapshot :=
        { accounts := accounts,
          tx := state.evm.tx,
          block := state.evm.block,
          logs := state.evm.logs }
      let parentEvm :=
        { state.evm with
          cheatcodes :=
            { state.evm.cheatcodes with
              nextSnapshotId := addWord snapshotId 1,
              snapshots := (snapshotId, snapshot) :: state.evm.cheatcodes.snapshots } }
      handledCheatcode state effects childGas accounts parentEvm
        (wordToBytes32 snapshotId)
    else if isSelector call.input revertToStateSelector then
      let snapshotId := readWordFromBytes call.input 4
      match lookupSnapshot? state.evm.cheatcodes.snapshots snapshotId with
      | none =>
          handledCheatcode state effects childGas accounts state.evm
            (wordToBytes32 0)
      | some snapshot =>
          let parentEvm :=
            { state.evm with
              accounts := snapshot.accounts,
              tx := snapshot.tx,
              block := snapshot.block,
              logs := snapshot.logs }
          handledCheatcode state effects childGas snapshot.accounts parentEvm
            (wordToBytes32 1)
    else if isSelector call.input warmSlotSelector then
      let target := low160 (readWordFromBytes call.input 4)
      let key := readWordFromBytes call.input 36
      CheatcodeDecision.handled
        { result := successfulCheatcodeResult childGas accounts,
          parentEvm := state.evm,
          logs := state.evm.logs,
          accessState :=
            applyMeterEffects effects
              { state with
                accessedStorageKeys :=
                  insertStorageKeySet (target, key) state.accessedStorageKeys } }
    else if isSelector call.input coolSlotSelector then
      let target := low160 (readWordFromBytes call.input 4)
      let key := readWordFromBytes call.input 36
      CheatcodeDecision.handled
        { result := successfulCheatcodeResult childGas accounts,
          parentEvm := state.evm,
          logs := state.evm.logs,
          accessState :=
            applyMeterEffects effects
              { state with
                accessedStorageKeys :=
                  removeStorageKeySet (target, key) state.accessedStorageKeys } }
    else if isSelector call.input coolAddressSelector then
      let target := low160 (readWordFromBytes call.input 4)
      CheatcodeDecision.handled
        { result := successfulCheatcodeResult childGas accounts,
          parentEvm := state.evm,
          logs := state.evm.logs,
          accessState :=
            applyMeterEffects effects
              { state with
                accessedAddresses := removeWordSet target state.accessedAddresses } }
    else
      CheatcodeDecision.unsupported (call.input.take 4)
  else
    CheatcodeDecision.notCheatcode

def applyPrankToCall (state : State) (call : ExternalCall) :
    ExternalCall × State :=
  match state.cheatcodes.prankCaller? with
  | none =>
      match state.cheatcodes.persistentPrankCaller? with
      | none => (call, state)
      | some caller => ({ call with caller := caller }, state)
  | some caller =>
      ( { call with caller := caller },
        { state with
          cheatcodes := { state.cheatcodes with prankCaller? := none } } )

mutual

partial def runFuel : Nat → Nat → Nat → MeteredState → MeteredState
  | _, _, 0, state => state
  | callFuel, stepFuel, fuel + 1, state =>
      if state.stopped then
        state
      else
        runFuel callFuel stepFuel fuel (step callFuel stepFuel state)

partial def step (callFuel stepFuel : Nat) (state : MeteredState) : MeteredState :=
  if state.stopped then
    state
  else
    match state.evm.code[state.evm.pc]? with
    | none => { state with evm := BytecodeEvm.step state.evm }
    | some op =>
        match decodeOpcode op with
        | none => meteredStepInvalidOpcode osakaCostModel op state
        | some opcode =>
            match externalCreateForOpcode? opcode state.evm with
            | some create =>
                stepExternalCreate callFuel stepFuel opcode create state
            | none =>
                match externalCallForOpcode? opcode state.evm with
                | none => meteredStepOpcode osakaCostModel opcode state
                | some call =>
                    stepExternalCall callFuel stepFuel opcode call state

partial def stepExternalCall
    (callFuel stepFuel : Nat) (opcode : Opcode) (call : ExternalCall)
    (state : MeteredState) : MeteredState :=
  let effects := osakaCostModel.opcodeCost opcode state
  match effects.childGas? with
  | none => meteredStepOpcode osakaCostModel opcode state
  | some childGas =>
      match chargeGas effects.cost state with
      | none => setOutOfGas effects.cost state
      | some _ =>
          match cheatcodeDecision state effects call childGas state.evm.accounts with
          | CheatcodeDecision.handled outcome =>
              finishExternalCall opcode state outcome
          | CheatcodeDecision.unsupported selector =>
              { state with
                evm := setError state.evm (StepError.unsupportedCheatcode selector) }
          | CheatcodeDecision.error error =>
              { state with evm := setError state.evm error }
          | CheatcodeDecision.notCheatcode =>
              let (callForChild, parentEvmAfterPrank) := applyPrankToCall state.evm call
              let parentState := { state with evm := parentEvmAfterPrank }
              match accountsBeforeCall? parentState.evm callForChild with
              | none =>
                  let result := failedCallResult parentState.evm.accounts childGas
                  let stateWithResult :=
                    { parentState with
                      evm :=
                        { parentState.evm with
                          externalResults := result :: parentState.evm.externalResults } }
                  meteredStepOpcode osakaCostModel opcode stateWithResult
              | some accountsForChild =>
                  match precompileResult? parentState.evm callForChild childGas accountsForChild with
                  | some result =>
                      finishExternalCall opcode parentState
                        { result := result,
                          parentEvm := parentState.evm,
                          logs := parentState.evm.logs,
                          accessState := applyMeterEffects effects parentState }
                  | none =>
                      let childStart :=
                        childInitialMeteredState parentState effects callForChild childGas accountsForChild
                      let childFinal :=
                        match callFuel with
                        | 0 => childStart
                        | depth + 1 => runFuel depth stepFuel stepFuel childStart
                      match missingHashError? childFinal with
                      | some data =>
                          { parentState with
                            evm := setError parentState.evm (StepError.missingHash data) }
                      | none =>
                          let success := callSuccess childFinal
                          if parentState.evm.cheatcodes.expectRevert then
                            let parentEvm :=
                              { parentState.evm with
                                cheatcodes :=
                                  { parentState.evm.cheatcodes with expectRevert := false } }
                            finishExternalCall opcode parentState
                              { result :=
                                  { success := !success,
                                    returndata := [],
                                    accounts? := some parentState.evm.accounts,
                                    gasRemaining := childFinal.gasRemaining },
                                parentEvm := parentEvm,
                                logs := parentState.evm.logs,
                                accessState := applyMeterEffects effects { parentState with evm := parentEvm } }
                          else
                            let committedAccounts :=
                              if success then childFinal.evm.accounts else parentState.evm.accounts
                            let parentEvm :=
                              if success then
                                { parentState.evm with cheatcodes := childFinal.evm.cheatcodes }
                              else
                                parentState.evm
                            finishExternalCall opcode parentState
                              { result :=
                                  { success := success,
                                    returndata := callReturndata childFinal,
                                    accounts? := some committedAccounts,
                                    gasRemaining := childFinal.gasRemaining },
                                parentEvm := parentEvm,
                                logs :=
                                  if success then childFinal.evm.logs else parentState.evm.logs,
                                accessState :=
                                  if success then childFinal else applyMeterEffects effects parentState }

partial def stepExternalCreate
    (callFuel stepFuel : Nat) (opcode : Opcode) (create : ExternalCreate)
    (state : MeteredState) : MeteredState :=
  let effects := osakaCostModel.opcodeCost opcode state
  match effects.childGas? with
  | none => meteredStepOpcode osakaCostModel opcode state
  | some childGas =>
      match chargeGas effects.cost state with
      | none => setOutOfGas effects.cost state
      | some _ =>
          match createdAddressFromState state.evm create with
          | AddressDerivation.missingHash data =>
              { state with
                evm := setError state.evm (StepError.missingHash data) }
          | AddressDerivation.ok createdAddress =>
              let failureAccounts :=
                createFailureAccounts state.evm.accounts create.creator
              match accountsBeforeCreate? state.evm create createdAddress with
              | none =>
                  let result := failedCreateResult failureAccounts childGas
                  let stateWithResult :=
                    { state with
                      evm :=
                        { state.evm with
                          externalResults := result :: state.evm.externalResults } }
                  meteredStepOpcode osakaCostModel opcode stateWithResult
              | some accountsForChild =>
                  let childStart :=
                    createChildInitialMeteredState state effects create
                      createdAddress childGas accountsForChild
                  let childFinal :=
                    match callFuel with
                    | 0 => childStart
                    | depth + 1 => runFuel depth stepFuel stepFuel childStart
                  match missingHashError? childFinal with
                  | some data =>
                      { state with
                        evm := setError state.evm (StepError.missingHash data) }
                  | none =>
                      let runtime := createRuntimeCode childFinal
                      let depositCost := codeDepositCost runtime
                      let initSuccess := createSuccess childFinal
                      let depositSuccess := depositCost <= childFinal.gasRemaining
                      let success := initSuccess && depositSuccess
                      let resultGasRemaining :=
                        if success then
                          childFinal.gasRemaining - depositCost
                        else if initSuccess then
                          0
                        else
                          childFinal.gasRemaining
                      let committedAccounts :=
                        if success then
                          setCreatedCode childFinal.evm.accounts createdAddress runtime
                        else
                          failureAccounts
                      let committedLogs :=
                        if success then childFinal.evm.logs else state.evm.logs
                      let committedAccessState :=
                        if success then
                          { childFinal with gasRemaining := resultGasRemaining }
                        else
                          applyMeterEffects effects state
                      let result : ExternalResult :=
                        { success := success,
                          returndata := createReturndata childFinal,
                          createdAddress := createdAddress,
                          accounts? := some committedAccounts,
                          gasRemaining := resultGasRemaining }
                      let stateWithResult :=
                        { state with
                          evm :=
                            { state.evm with
                              externalResults := result :: state.evm.externalResults } }
                      let parentAfter :=
                        meteredStepOpcode osakaCostModel opcode stateWithResult
                      { parentAfter with
                        accessedAddresses := committedAccessState.accessedAddresses,
                        accessedStorageKeys := committedAccessState.accessedStorageKeys,
                        refund := committedAccessState.refund,
                        evm := { parentAfter.evm with logs := committedLogs } }

end

end BytecodeMultiContract
end SolidCoreYulCore

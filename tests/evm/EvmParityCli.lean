import SolidCoreYulCore.BytecodeMultiContract

open SolidCoreYulCore
open SolidCoreYulCore.BytecodeEvm
open SolidCoreYulCore.BytecodeGas

namespace SolidCore.Tests.EvmParityCli

structure Config where
  code : Bytes := []
  calldata : Bytes := []
  gas : Nat := 1000000
  fuel : Nat := 200000
  callDepth : Nat := 16
  address : Word := 1
  caller : Word := 0x1000
  origin : Word := 0x1000
  coinbase : Word := 0
  timestamp : Word := GasConst.osakaMainnetTimestamp
  number : Word := 0
  gaslimit : Word := GasConst.defaultBlockGasLimit
  basefee : Word := 0
  chainid : Word := 1
  callvalue : Word := 0
  balance : Word := 0
  nonce : Word := 0
  storage : WordMap := []
  originalStorage : WordMap := []
  originalStorageSpecified : Bool := false
  accounts : AccountMap := []
  originalAccounts : AccountMap := []
  keccakHashes : HashMap := []
  cheatcodeAddresses : WordMap := []
  cheatcodeSignatures : CheatcodeSignatureMap := []
  warmAddresses : List Word := []
  warmStorageKeys : List StorageAccessKey := []
deriving Repr

def stripHexPrefix (s : String) : String :=
  if s.startsWith "0x" || s.startsWith "0X" then (s.drop 2).toString else s

def hexValue? (c : Char) : Option Nat :=
  if '0' <= c && c <= '9' then
    some (c.toNat - '0'.toNat)
  else if 'a' <= c && c <= 'f' then
    some (10 + c.toNat - 'a'.toNat)
  else if 'A' <= c && c <= 'F' then
    some (10 + c.toNat - 'A'.toNat)
  else
    none

def parseHexNat (raw : String) : Except String Nat :=
  let chars := (stripHexPrefix raw).toList
  chars.foldlM
    (fun acc c =>
      match hexValue? c with
      | some value => Except.ok (acc * 16 + value)
      | none => Except.error s!"invalid hex digit '{c}' in {raw}")
    0

def parseHexBytePair (hi lo : Char) : Except String Byte := do
  let hiValue ←
    match hexValue? hi with
    | some value => Except.ok value
    | none => Except.error s!"invalid hex digit '{hi}'"
  let loValue ←
    match hexValue? lo with
    | some value => Except.ok value
    | none => Except.error s!"invalid hex digit '{lo}'"
  Except.ok (byte (hiValue * 16 + loValue))

def parseHexBytesAux : List Char → Except String Bytes
  | [] => Except.ok []
  | hi :: lo :: rest => do
      let value ← parseHexBytePair hi lo
      let values ← parseHexBytesAux rest
      Except.ok (value :: values)
  | [_] => Except.error "hex byte strings must have an even number of digits"

def parseHexBytes (raw : String) : Except String Bytes :=
  parseHexBytesAux (stripHexPrefix raw).toList

def parseWord (raw : String) : Except String Word :=
  if raw.startsWith "0x" || raw.startsWith "0X" then
    norm <$> parseHexNat raw
  else
    match raw.toNat? with
    | some value => Except.ok (norm value)
    | none => Except.error s!"invalid decimal word {raw}"

def parseNatArg (raw : String) : Except String Nat :=
  match raw.toNat? with
  | some value => Except.ok value
  | none => Except.error s!"invalid natural number {raw}"

def splitAssignment (raw : String) : Except String (String × String) :=
  match raw.splitOn "=" with
  | [lhs, rhs] => Except.ok (lhs, rhs)
  | _ => Except.error s!"expected key=value assignment, got {raw}"

def parseStorageAssignment (raw : String) : Except String (Word × Word) := do
  let (key, value) ← splitAssignment raw
  return (← parseWord key, ← parseWord value)

def parseAccountBytesAssignment (raw : String) : Except String (Word × Bytes) := do
  let (address, value) ← splitAssignment raw
  return (← parseWord address, ← parseHexBytes value)

def parseAccountWordAssignment (raw : String) : Except String (Word × Word) := do
  let (address, value) ← splitAssignment raw
  return (← parseWord address, ← parseWord value)

def splitAccountStorageAssignment
    (raw : String) : Except String (String × String × String) := do
  let (addressAndKey, value) ← splitAssignment raw
  match addressAndKey.splitOn ":" with
  | [address, key] => Except.ok (address, key, value)
  | _ => Except.error s!"expected address:key=value assignment, got {raw}"

def parseAccountStorageAssignment
    (raw : String) : Except String (Word × Word × Word) := do
  let (address, key, value) ← splitAccountStorageAssignment raw
  return (← parseWord address, ← parseWord key, ← parseWord value)

def parseKeccakAssignment (raw : String) : Except String (Bytes × Word) := do
  let (data, hash) ← splitAssignment raw
  return (← parseHexBytes data, ← parseWord hash)

def parseCheatcodeAddressAssignment (raw : String) : Except String (Word × Word) :=
  parseStorageAssignment raw

def splitCheatcodeSignatureAssignment
    (raw : String) : Except String (String × String × String × String × String) := do
  let (keyAndDigest, value) ← splitAssignment raw
  let keyDigestParts := keyAndDigest.splitOn ":"
  let valueParts := value.splitOn ":"
  match keyDigestParts, valueParts with
  | [privateKey, digest], [v, r, s] => Except.ok (privateKey, digest, v, r, s)
  | _, _ =>
      Except.error
        s!"expected privateKey:digest=v:r:s signature assignment, got {raw}"

def parseCheatcodeSignatureAssignment
    (raw : String) : Except String (Word × Word × CheatcodeSignature) := do
  let (privateKey, digest, v, r, s) ← splitCheatcodeSignatureAssignment raw
  let privateKey ← parseWord privateKey
  let digest ← parseWord digest
  let v ← parseWord v
  let r ← parseWord r
  let s ← parseWord s
  return (privateKey, digest, { v := v, r := r, s := s })

def upsertAccount (accounts : AccountMap) (address : Word)
    (f : Account → Account) : AccountMap :=
  let account :=
    match lookupAccount? accounts address with
    | some account => account
    | none => {}
  writeAccount accounts address (f account)

def upsertAccountCode (accounts : AccountMap) (address : Word) (code : Bytes) :
    AccountMap :=
  upsertAccount accounts address (fun account => { account with code := code })

def upsertAccountBalance
    (accounts : AccountMap) (address balance : Word) : AccountMap :=
  upsertAccount accounts address
    (fun account => { account with balance := balance })

def upsertAccountNonce
    (accounts : AccountMap) (address nonce : Word) : AccountMap :=
  upsertAccount accounts address
    (fun account => { account with nonce := nonce })

def upsertAccountStorage
    (accounts : AccountMap) (address key value : Word) : AccountMap :=
  upsertAccount accounts address
    (fun account =>
      { account with storage := writeWord account.storage key value })

partial def parseArgs : List String → Config → Except String Config
  | [], cfg => Except.ok cfg
  | "--code" :: value :: rest, cfg => do
      parseArgs rest { cfg with code := ← parseHexBytes value }
  | "--calldata" :: value :: rest, cfg => do
      parseArgs rest { cfg with calldata := ← parseHexBytes value }
  | "--gas" :: value :: rest, cfg => do
      parseArgs rest { cfg with gas := ← parseNatArg value }
  | "--fuel" :: value :: rest, cfg => do
      parseArgs rest { cfg with fuel := ← parseNatArg value }
  | "--call-depth" :: value :: rest, cfg => do
      parseArgs rest { cfg with callDepth := ← parseNatArg value }
  | "--address" :: value :: rest, cfg => do
      parseArgs rest { cfg with address := ← parseWord value }
  | "--caller" :: value :: rest, cfg => do
      parseArgs rest { cfg with caller := ← parseWord value }
  | "--origin" :: value :: rest, cfg => do
      parseArgs rest { cfg with origin := ← parseWord value }
  | "--coinbase" :: value :: rest, cfg => do
      parseArgs rest { cfg with coinbase := ← parseWord value }
  | "--timestamp" :: value :: rest, cfg => do
      parseArgs rest { cfg with timestamp := ← parseWord value }
  | "--number" :: value :: rest, cfg => do
      parseArgs rest { cfg with number := ← parseWord value }
  | "--gaslimit" :: value :: rest, cfg => do
      parseArgs rest { cfg with gaslimit := ← parseWord value }
  | "--basefee" :: value :: rest, cfg => do
      parseArgs rest { cfg with basefee := ← parseWord value }
  | "--chainid" :: value :: rest, cfg => do
      parseArgs rest { cfg with chainid := ← parseWord value }
  | "--callvalue" :: value :: rest, cfg => do
      parseArgs rest { cfg with callvalue := ← parseWord value }
  | "--balance" :: value :: rest, cfg => do
      parseArgs rest { cfg with balance := ← parseWord value }
  | "--nonce" :: value :: rest, cfg => do
      parseArgs rest { cfg with nonce := ← parseWord value }
  | "--storage" :: value :: rest, cfg => do
      parseArgs rest { cfg with storage := (← parseStorageAssignment value) :: cfg.storage }
  | "--original-storage" :: value :: rest, cfg => do
      parseArgs rest
        { cfg with
          originalStorage := (← parseStorageAssignment value) :: cfg.originalStorage,
          originalStorageSpecified := true }
  | "--account" :: value :: rest, cfg => do
      let (address, code) ← parseAccountBytesAssignment value
      parseArgs rest
        { cfg with accounts := upsertAccountCode cfg.accounts address code }
  | "--account-balance" :: value :: rest, cfg => do
      let (address, balance) ← parseAccountWordAssignment value
      parseArgs rest
        { cfg with
          accounts := upsertAccountBalance cfg.accounts address balance }
  | "--account-nonce" :: value :: rest, cfg => do
      let (address, nonce) ← parseAccountWordAssignment value
      parseArgs rest
        { cfg with
          accounts := upsertAccountNonce cfg.accounts address nonce }
  | "--account-storage" :: value :: rest, cfg => do
      let (address, key, storageValue) ← parseAccountStorageAssignment value
      parseArgs rest
        { cfg with
          accounts :=
            upsertAccountStorage cfg.accounts address key storageValue }
  | "--account-original-storage" :: value :: rest, cfg => do
      let (address, key, storageValue) ← parseAccountStorageAssignment value
      parseArgs rest
        { cfg with
          originalAccounts :=
            upsertAccountStorage cfg.originalAccounts address key storageValue }
  | "--keccak" :: value :: rest, cfg => do
      parseArgs rest { cfg with keccakHashes := (← parseKeccakAssignment value) :: cfg.keccakHashes }
  | "--cheat-addr" :: value :: rest, cfg => do
      parseArgs rest
        { cfg with
          cheatcodeAddresses :=
            (← parseCheatcodeAddressAssignment value) :: cfg.cheatcodeAddresses }
  | "--cheat-sign" :: value :: rest, cfg => do
      parseArgs rest
        { cfg with
          cheatcodeSignatures :=
            (← parseCheatcodeSignatureAssignment value) :: cfg.cheatcodeSignatures }
  | "--warm-address" :: value :: rest, cfg => do
      parseArgs rest { cfg with warmAddresses := (← parseWord value) :: cfg.warmAddresses }
  | "--warm-storage" :: value :: rest, cfg => do
      parseArgs rest { cfg with warmStorageKeys := (cfg.address, ← parseWord value) :: cfg.warmStorageKeys }
  | flag :: _, _ => Except.error s!"unknown or incomplete argument {flag}"

def initialState (cfg : Config) : State :=
  let account : Account :=
    { balance := cfg.balance,
      nonce := cfg.nonce,
      code := cfg.code,
      storage := cfg.storage }
  let accounts :=
    cfg.accounts.foldl
      (fun acc entry => writeAccount acc entry.1 entry.2)
      [(cfg.address, account)]
  { State.empty with
    code := cfg.code,
    keccakHashes := cfg.keccakHashes,
    cheatcodeAddresses := cfg.cheatcodeAddresses,
    cheatcodeSignatures := cfg.cheatcodeSignatures,
    accounts := accounts,
    tx := { origin := cfg.origin },
    block :=
      { coinbase := cfg.coinbase,
        timestamp := cfg.timestamp,
        number := cfg.number,
        gaslimit := cfg.gaslimit,
        chainid := cfg.chainid,
        basefee := cfg.basefee },
    call :=
      { address := cfg.address,
        caller := cfg.caller,
        callvalue := cfg.callvalue,
        calldata := cfg.calldata } }

def initialMeteredState (cfg : Config) : MeteredState :=
  let base := MeteredState.ofStateOsaka (initialState cfg) cfg.gas
  let originalStorage :=
    if cfg.originalStorageSpecified then cfg.originalStorage else cfg.storage
  let originalAccount : Account :=
    { balance := cfg.balance,
      nonce := cfg.nonce,
      code := cfg.code,
      storage := originalStorage }
  let originalAccounts :=
    base.evm.accounts.foldl
      (fun acc entry =>
        let address := entry.1
        let current := entry.2
        let original :=
          match lookupAccount? cfg.originalAccounts address with
          | some account => { current with storage := account.storage }
          | none =>
              if norm address = norm cfg.address then
                originalAccount
              else
                current
        writeAccount acc address original)
      []
  { base with
    originalAccounts := originalAccounts,
    accessedAddresses :=
      cfg.warmAddresses.foldl
        (fun acc address => insertWordSet address acc)
        base.accessedAddresses,
    accessedStorageKeys :=
      cfg.warmStorageKeys.foldl
        (fun acc key => insertStorageKeySet key acc)
        base.accessedStorageKeys }

def haltStatus (state : MeteredState) : String :=
  match state.gasError? with
  | some _ => "out_of_gas"
  | none =>
      match state.evm.halt? with
      | some HaltKind.stopped => "stopped"
      | some HaltKind.returned => "returned"
      | some HaltKind.reverted => "reverted"
      | some HaltKind.selfdestructed => "selfdestructed"
      | some HaltKind.exceptional => "exceptional"
      | none => "running"

def callSuccess (state : MeteredState) : Bool :=
  state.gasError?.isNone &&
    match state.evm.halt? with
    | some HaltKind.stopped => true
    | some HaltKind.returned => true
    | some HaltKind.selfdestructed => true
    | _ => false

def hexDigit (n : Nat) : Char :=
  match n with
  | 0 => '0'
  | 1 => '1'
  | 2 => '2'
  | 3 => '3'
  | 4 => '4'
  | 5 => '5'
  | 6 => '6'
  | 7 => '7'
  | 8 => '8'
  | 9 => '9'
  | 10 => 'a'
  | 11 => 'b'
  | 12 => 'c'
  | 13 => 'd'
  | 14 => 'e'
  | _ => 'f'

def byteHexChars (value : Byte) : List Char :=
  [hexDigit (byte value / 16), hexDigit (byte value % 16)]

def bytesHex (values : Bytes) : String :=
  "0x" ++ String.ofList (values.flatMap byteHexChars)

def wordHex32 (value : Word) : String :=
  bytesHex (wordToBytes32 value)

def joinStrings (separator : String) : List String → String
  | [] => ""
  | value :: rest =>
      rest.foldl (fun acc next => acc ++ separator ++ next) value

def optionReprLine {α : Type} [Repr α] (name : String) (value : Option α) :
    String :=
  match value with
  | none => s!"{name} none"
  | some x => s!"{name} {repr x}"

def externalCallKindName : ExternalCallKind → String
  | ExternalCallKind.call => "call"
  | ExternalCallKind.callcode => "callcode"
  | ExternalCallKind.delegatecall => "delegatecall"
  | ExternalCallKind.staticcall => "staticcall"

def printResult (cfg : Config) (result : MeteredState) : IO Unit := do
  IO.println s!"status {haltStatus result}"
  IO.println s!"success {if callSuccess result then "1" else "0"}"
  IO.println s!"output {bytesHex result.evm.output}"
  IO.println s!"gas_used {result.gasUsed}"
  IO.println s!"gas_remaining {result.gasRemaining}"
  IO.println s!"refund {result.refund}"
  IO.println (optionReprLine "gas_error" result.gasError?)
  IO.println (optionReprLine "evm_error" result.evm.error?)
  IO.println (optionReprLine "cheat_prank" result.evm.cheatcodes.prankCaller?)
  let account := rawAccount result.evm cfg.address
  IO.println s!"nonce {wordHex32 account.nonce}"
  IO.println s!"balance {wordHex32 account.balance}"
  IO.println s!"destroyed {if account.destroyed then "1" else "0"}"
  for (key, value) in account.storage do
    IO.println s!"storage {wordHex32 key} {wordHex32 value}"
  for (address, account) in result.evm.accounts do
    IO.println s!"account_nonce {wordHex32 address} {wordHex32 account.nonce}"
    IO.println s!"account_balance {wordHex32 address} {wordHex32 account.balance}"
    IO.println s!"account_destroyed {wordHex32 address} {if account.destroyed then "1" else "0"}"
    IO.println s!"account_code {wordHex32 address} {bytesHex account.code}"
    for (key, value) in account.storage do
      IO.println s!"account_storage {wordHex32 address} {wordHex32 key} {wordHex32 value}"
  for log in result.evm.logs.reverse do
    IO.println
      s!"log {wordHex32 log.address} {joinStrings "," (log.topics.map wordHex32)} {bytesHex log.data}"
  for action in result.evm.externalActions.reverse do
    match action with
    | ExternalAction.call call =>
        IO.println
          s!"external_call {externalCallKindName call.kind} {wordHex32 call.to} {wordHex32 call.caller} {wordHex32 call.gas} {bytesHex call.input}"
    | ExternalAction.create create =>
        IO.println
          s!"external_create {repr create.kind} {wordHex32 create.creator} {bytesHex create.initCode}"
  for entry in result.evm.externalTrace.reverse do
    match entry.1 with
    | ExternalAction.call call =>
        IO.println
          s!"external_result call {externalCallKindName call.kind} {wordHex32 call.to} {if entry.2.success then "1" else "0"} {wordHex32 entry.2.gasRemaining} {bytesHex entry.2.returndata}"
    | ExternalAction.create create =>
        IO.println
          s!"external_result create {repr create.kind} {wordHex32 create.creator} {if entry.2.success then "1" else "0"} {wordHex32 entry.2.gasRemaining} {bytesHex entry.2.returndata}"

end SolidCore.Tests.EvmParityCli

def main (args : List String) : IO UInt32 := do
  match SolidCore.Tests.EvmParityCli.parseArgs args {} with
  | Except.error error =>
      IO.eprintln s!"evm_parity: {error}"
      return 2
  | Except.ok cfg =>
      let result :=
        SolidCoreYulCore.BytecodeMultiContract.runFuel
          cfg.callDepth cfg.fuel cfg.fuel
          (SolidCore.Tests.EvmParityCli.initialMeteredState cfg)
      SolidCore.Tests.EvmParityCli.printResult cfg result
      return 0

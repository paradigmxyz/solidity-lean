import SolidCore.Solidity.Shared.Block

namespace SolidCore.Solidity.Shared
namespace External

abbrev Byte := Nat
abbrev Bytes := List Byte
abbrev WordMap := List (Word × Word)
abbrev HashMap := List (Bytes × Word)
abbrev BytesMap := List (Bytes × Bytes)
abbrev BytesSet := List Bytes
abbrev NamedBytesMap := List (String × Bytes)

def byte (value : Nat) : Byte :=
  value % 256

def normalizeBytes (bytes : Bytes) : Bytes :=
  bytes.map byte

def bytesEq (lhs rhs : Bytes) : Bool :=
  normalizeBytes lhs == normalizeBytes rhs

def wordEq (lhs rhs : Word) : Bool :=
  norm lhs == norm rhs

def addressModulus : Nat := 2 ^ 160

def addressWord (address : Word) : Word :=
  norm address % addressModulus

def optionWordEq (lhs rhs : Option Word) : Bool :=
  match lhs, rhs with
  | some lhs, some rhs => wordEq lhs rhs
  | none, none => true
  | _, _ => false

def lookupWord? : WordMap → Word → Option Word
  | [], _ => none
  | (candidate, value) :: rest, key =>
      if wordEq candidate key then
        some (norm value)
      else
        lookupWord? rest key

def wordListAt (values : List Word) (index : Word) : Word :=
  SolidCore.Solidity.Shared.Block.wordListAt values index

def blobHashAt (hashes : List Word) (index : Word) : Word :=
  SolidCore.Solidity.Shared.Block.blobHashAt hashes index

def blockhashNumberInRange (current requested : Word) : Bool :=
  SolidCore.Solidity.Shared.Block.blockhashNumberInRange current requested

def blockHashAt (current : Word) (hashes : WordMap)
    (requested : Word) : Word :=
  SolidCore.Solidity.Shared.Block.blockHashAt current hashes requested

def lookupHash? : HashMap → Bytes → Option Word
  | [], _ => none
  | (candidate, value) :: rest, bytes =>
      if bytesEq candidate bytes then
        some (norm value)
      else
        lookupHash? rest bytes

def lookupBytes? : BytesMap → Bytes → Option Bytes
  | [], _ => none
  | (candidate, value) :: rest, bytes =>
      if bytesEq candidate bytes then
        some (normalizeBytes value)
      else
        lookupBytes? rest bytes

def lookupNamedBytes? : NamedBytesMap → String → Option Bytes
  | [], _ => none
  | (candidate, value) :: rest, name =>
      if candidate == name then
        some (normalizeBytes value)
      else
        lookupNamedBytes? rest name

def namedBytesAt (values : NamedBytesMap) (name : String) : Bytes :=
  (lookupNamedBytes? values name).getD []

def containsBytes : BytesSet → Bytes → Bool
  | [], _ => false
  | candidate :: rest, bytes =>
      bytesEq candidate bytes || containsBytes rest bytes

structure EcrecoverSignature where
  v : Word := 0
  r : Word := 0
  s : Word := 0
  deriving DecidableEq, Repr

namespace EcrecoverSignature

def matches? (lhs rhs : EcrecoverSignature) : Bool :=
  wordEq lhs.v rhs.v && wordEq lhs.r rhs.r && wordEq lhs.s rhs.s

end EcrecoverSignature

abbrev EcrecoverMap := List (Word × EcrecoverSignature × Word)

def lookupEcrecover? : EcrecoverMap → Word → EcrecoverSignature → Option Word
  | [], _, _ => none
  | (candidateDigest, candidateSignature, address) :: rest, digest, signature =>
      if wordEq candidateDigest digest &&
          EcrecoverSignature.matches? candidateSignature signature then
        some (addressWord address)
      else
        lookupEcrecover? rest digest signature

structure CallRequest (Kind : Type) where
  kind : Kind
  target : Word
  calldata : Bytes
  value : Word := 0
  deriving Repr

namespace CallRequest

def matchesRequest [BEq Kind] (request : CallRequest Kind)
    (kind : Kind) (target : Word) (calldata : Bytes) (value : Word) : Bool :=
  request.kind == kind &&
    wordEq request.target target &&
    bytesEq request.calldata calldata &&
    wordEq request.value value

end CallRequest

structure CallResult (Kind : Type) extends CallRequest Kind where
  success : Bool
  output : Bytes := []
  deriving Repr

namespace CallResult

def matchesRequest [BEq Kind] (result : CallResult Kind)
    (kind : Kind) (target : Word) (calldata : Bytes) (value : Word) : Bool :=
  result.toCallRequest.matchesRequest kind target calldata value

def lookup? [BEq Kind] (results : List (CallResult Kind))
    (kind : Kind) (target : Word) (calldata : Bytes)
    (value : Word) : Option (CallResult Kind) :=
  results.find? (fun result => result.matchesRequest kind target calldata value)

end CallResult

structure ContractCreationRequest where
  contractName : String
  constructorArgs : Bytes
  value : Word := 0
  salt? : Option Word := none
  deriving Repr

namespace ContractCreationRequest

def matchesRequest (request : ContractCreationRequest)
    (contractName : String) (constructorArgs : Bytes)
    (value : Word) (salt? : Option Word) : Bool :=
  request.contractName == contractName &&
    bytesEq request.constructorArgs constructorArgs &&
    wordEq request.value value &&
    optionWordEq request.salt? salt?

end ContractCreationRequest

structure ContractCreationResult extends ContractCreationRequest where
  success : Bool
  address : Word := 0
  output : Bytes := []
  deriving Repr

namespace ContractCreationResult

def matchesRequest (result : ContractCreationResult)
    (contractName : String) (constructorArgs : Bytes)
    (value : Word) (salt? : Option Word) : Bool :=
  result.toContractCreationRequest.matchesRequest contractName constructorArgs value salt?

def lookup? (results : List ContractCreationResult)
    (contractName : String) (constructorArgs : Bytes)
    (value : Word) (salt? : Option Word) : Option ContractCreationResult :=
  results.find?
    (fun result => result.matchesRequest contractName constructorArgs value salt?)

end ContractCreationResult

inductive ExternalCallKind where
  | call
  | callcode
  | delegatecall
  | staticcall
  deriving DecidableEq, Repr, BEq

inductive ExternalCreateKind where
  | create
  | create2
  deriving DecidableEq, Repr, BEq

structure EvmCallRequest where
  kind : ExternalCallKind
  gas : Word
  target : Word
  calldata : Bytes
  value : Word := 0
  retOffset : Word := 0
  retSize : Word := 0
  caller : Word := 0
  address : Word := 0
  isStatic : Bool := false
  deriving DecidableEq, Repr

namespace EvmCallRequest

def toCallRequest (request : EvmCallRequest) :
    CallRequest ExternalCallKind :=
  { kind := request.kind
    target := request.target
    calldata := request.calldata
    value := request.value }

end EvmCallRequest

structure EvmCreateRequest where
  kind : ExternalCreateKind
  value : Word
  initCode : Bytes
  salt? : Option Word := none
  creator : Word := 0
  deriving DecidableEq, Repr

inductive EvmAction where
  | call : EvmCallRequest → EvmAction
  | create : EvmCreateRequest → EvmAction
  deriving DecidableEq, Repr

structure EvmResult where
  success : Bool := false
  output : Bytes := []
  createdAddress : Word := 0
  gasRemaining : Word := 0
  deriving DecidableEq, Repr

namespace EvmResult

def toCallResult (request : EvmCallRequest) (result : EvmResult) :
    CallResult ExternalCallKind :=
  { request.toCallRequest with
    success := result.success
    output := result.output }

end EvmResult

abbrev EvmTrace := List (EvmAction × EvmResult)

structure EvmExternal where
  call : EvmCallRequest → EvmResult := fun _ => {}
  create : EvmCreateRequest → EvmResult := fun _ => {}

namespace EvmExternal

def empty : EvmExternal := {}

def callExternal (external : EvmExternal) (request : EvmCallRequest) :
    EvmResult :=
  external.call request

def createExternal (external : EvmExternal) (request : EvmCreateRequest) :
    EvmResult :=
  external.create request

theorem callExternal_eq_call (external : EvmExternal)
    (request : EvmCallRequest) :
    external.callExternal request = external.call request := by
  rfl

theorem createExternal_eq_create (external : EvmExternal)
    (request : EvmCreateRequest) :
    external.createExternal request = external.create request := by
  rfl

end EvmExternal

end External
end SolidCore.Solidity.Shared

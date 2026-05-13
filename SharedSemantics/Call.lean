import SharedSemantics.Account

namespace SharedSemantics
namespace Call

abbrev Byte := Account.Byte
abbrev Bytes := Account.Bytes
abbrev NamedBytesMap := List (String × Bytes)

def normalizeBytes : Bytes → Bytes :=
  Account.normalizeBytes

def bytesEq : Bytes → Bytes → Bool :=
  Account.bytesEq

def wordEq : Word → Word → Bool :=
  Account.wordEq

def optionWordEq (lhs rhs : Option Word) : Bool :=
  match lhs, rhs with
  | some lhs, some rhs => wordEq lhs rhs
  | none, none => true
  | _, _ => false

def lookupNamedBytes? : NamedBytesMap → String → Option Bytes
  | [], _ => none
  | (candidate, value) :: rest, name =>
      if candidate == name then
        some (normalizeBytes value)
      else
        lookupNamedBytes? rest name

def namedBytesAt (values : NamedBytesMap) (name : String) : Bytes :=
  (lookupNamedBytes? values name).getD []

structure Request (Kind : Type) where
  kind : Kind
  target : Word
  calldata : Bytes
  value : Word := 0
  gas? : Option Word := none
  deriving Repr

namespace Request

def matchesRequest [BEq Kind] (request : Request Kind)
    (kind : Kind) (target : Word) (calldata : Bytes) (value : Word)
    (gas? : Option Word) : Bool :=
  request.kind == kind &&
    wordEq request.target target &&
    bytesEq request.calldata calldata &&
    wordEq request.value value &&
    optionWordEq request.gas? gas?

end Request

structure Result (Kind : Type) extends Request Kind where
  success : Bool
  output : Bytes := []
  deriving Repr

namespace Result

def matchesRequest [BEq Kind] (result : Result Kind)
    (kind : Kind) (target : Word) (calldata : Bytes) (value : Word)
    (gas? : Option Word) : Bool :=
  result.toRequest.matchesRequest kind target calldata value gas?

def lookup? [BEq Kind] (results : List (Result Kind))
    (kind : Kind) (target : Word) (calldata : Bytes)
    (value : Word) (gas? : Option Word) : Option (Result Kind) :=
  results.find?
    (fun result => result.matchesRequest kind target calldata value gas?)

end Result

structure CreationRequest where
  contractName : String
  constructorArgs : Bytes
  value : Word := 0
  salt? : Option Word := none
  deriving Repr

namespace CreationRequest

def matchesRequest (request : CreationRequest)
    (contractName : String) (constructorArgs : Bytes)
    (value : Word) (salt? : Option Word) : Bool :=
  request.contractName == contractName &&
    bytesEq request.constructorArgs constructorArgs &&
    wordEq request.value value &&
    optionWordEq request.salt? salt?

end CreationRequest

structure CreationResult extends CreationRequest where
  success : Bool
  address : Word := 0
  output : Bytes := []
  deriving Repr

namespace CreationResult

def matchesRequest (result : CreationResult)
    (contractName : String) (constructorArgs : Bytes)
    (value : Word) (salt? : Option Word) : Bool :=
  result.toCreationRequest.matchesRequest contractName constructorArgs value salt?

def lookup? (results : List CreationResult)
    (contractName : String) (constructorArgs : Bytes)
    (value : Word) (salt? : Option Word) : Option CreationResult :=
  results.find?
    (fun result => result.matchesRequest contractName constructorArgs value salt?)

end CreationResult

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

def toRequest (request : EvmCallRequest) : Request ExternalCallKind :=
  { kind := request.kind
    target := request.target
    calldata := request.calldata
    value := request.value
    gas? := some request.gas }

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
    Result ExternalCallKind :=
  { request.toRequest with
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

end Call
end SharedSemantics

import SolidCore.Solidity.Interpreter

namespace SolidCore
namespace Solidity
namespace Source
namespace ABI

abbrev Bytes := List Byte

def selectorBytes : Nat := 4
def wordBytes : Nat := 32

def normalizeBytes (bytes : Bytes) : Bytes :=
  bytes.map normByte

def readBytes? (bytes : Bytes) (offset size : Nat) : Option Bytes :=
  let rest := bytes.drop offset
  if size <= rest.length then
    some (normalizeBytes (rest.take size))
  else
    none

def bytesToWordBE (bytes : Bytes) : Word :=
  SolidCoreYulCore.norm
    (bytes.foldl (fun acc byte => acc * 256 + normByte byte) 0)

def wordToBytesBE : Nat -> Word -> Bytes
  | 0, _ => []
  | n + 1, value =>
      wordToBytesBE n (value / 256) ++ [normByte value]

def encodeWord (value : Word) : Bytes :=
  wordToBytesBE wordBytes (SolidCoreYulCore.norm value)

def encodeSelector (selector : Word) : Bytes :=
  wordToBytesBE selectorBytes (SolidCoreYulCore.norm selector)

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

def Ty.isDynamicAbi : Ty -> Bool
  | Ty.bytesCalldata => true
  | _ => false

def encodeStaticValue? : Ty -> Value -> Option Bytes
  | Ty.uint256, Value.word value => some (encodeWord value)
  | _, _ => none

def encodeDynamicPayload? : Ty -> Value -> Option Bytes
  | Ty.bytesCalldata, Value.bytes bytes =>
      some (encodeWord bytes.length ++ padRightWord bytes)
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

def encodeValues? (tys : List Ty) (values : List Value) : Option Bytes :=
  match encodeValuesAux? tys values (wordBytes * tys.length) with
  | some (heads, tails, _) => some (heads ++ tails)
  | none => none

def decodeValueAt? (argData : Bytes) (headIndex : Nat) :
    Ty -> Option Value
  | Ty.uint256 => do
      let value ← readWord? argData (wordBytes * headIndex)
      some (Value.word value)
  | Ty.bytesCalldata => do
      let offset ← readWord? argData (wordBytes * headIndex)
      let length ← readWord? argData offset
      let bytes ← readBytes? argData (offset + wordBytes) length
      some (Value.bytes bytes)
  | _ => none

def decodeArgsAux? (argData : Bytes) :
    List Ty -> Nat -> Option (List Value)
  | [], _ => some []
  | ty :: tys, index => do
      let value ← decodeValueAt? argData index ty
      let values ← decodeArgsAux? argData tys (index + 1)
      some (value :: values)

def decodeArgs? (tys : List Ty) (argData : Bytes) :
    Option (List Value) :=
  decodeArgsAux? argData tys 0

def encodeArgs? (tys : List Ty) (values : List Value) : Option Bytes :=
  encodeValues? tys values

def calldataFor? (function : FunctionDef) (args : List Value) :
    Option Bytes := do
  let selector ← function.selector?
  let encodedArgs ← encodeArgs? (function.params.map BindingDecl.ty) args
  some (encodeSelector selector ++ encodedArgs)

def panicSelector : Word := 0x4e487b71

def Contract.findErrorDecl? (contract : Contract)
    (name : String) : Option ErrorDecl :=
  contract.errorDecls.find? (fun error => error.name == name)

def Contract.encodeRevertData? (contract : Contract)
    (revert : RevertData) : Option Bytes :=
  match revert with
  | RevertData.panic code =>
      match encodeValues? [Ty.uint256] [Value.word code] with
      | some payload => some (encodeSelector panicSelector ++ payload)
      | none => none
  | RevertData.custom name values => do
      let decl ← Contract.findErrorDecl? contract name
      let payload ← encodeValues? decl.fields values
      some (encodeSelector decl.selector ++ payload)

structure AbiCallResult where
  success : Bool
  output : Bytes
  state : State
  deriving Repr

def Contract.callCalldata? (fuel : Nat) (contract : Contract)
    (state : State) (calldata : Bytes) : Option AbiCallResult := do
  let selector ← readSelector? calldata
  let function ← contract.findFunctionBySelector? selector
  let args ←
    decodeArgs? (function.params.map BindingDecl.ty)
      (calldata.drop selectorBytes)
  match function.call? fuel contract.context state args with
  | some (CallResult.returned state' values) => do
      let output ← encodeValues? (function.returns.map BindingDecl.ty) values
      some { success := true, output, state := state' }
  | some (CallResult.reverted state' revert) => do
      let output ← Contract.encodeRevertData? contract revert
      some { success := false, output, state := state' }
  | none => none

end ABI
end Source
end Solidity
end SolidCore

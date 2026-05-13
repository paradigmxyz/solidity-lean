import SharedSemantics.Word
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
  SharedSemantics.External.normalizeBytes bytes

def readBytes? (bytes : Bytes) (offset size : Nat) : Option Bytes :=
  let rest := bytes.drop offset
  if size <= rest.length then
    some (normalizeBytes (rest.take size))
  else
    none

def bytesToWordBE (bytes : Bytes) : Word :=
  SharedSemantics.norm
    (bytes.foldl (fun acc byte => acc * 256 + normByte byte) 0)

def wordToBytesBE : Nat -> Word -> Bytes
  | 0, _ => []
  | n + 1, value =>
      wordToBytesBE n (value / 256) ++ [normByte value]

def encodeWord (value : Word) : Bytes :=
  wordToBytesBE wordBytes (SharedSemantics.norm value)

def addressFits (value : Word) : Bool :=
  SharedSemantics.norm value < 2 ^ 160

def selectorFits (value : Word) : Bool :=
  SharedSemantics.norm value < 2 ^ (8 * selectorBytes)

def fixedBytesFits (size : Nat) (value : Word) : Bool :=
  0 < size && size <= wordBytes &&
    SharedSemantics.norm value < 2 ^ (8 * size)

def allZeroBytes : Bytes -> Bool
  | [] => true
  | byte :: rest => normByte byte == 0 && allZeroBytes rest

def encodeSelector (selector : Word) : Bytes :=
  wordToBytesBE selectorBytes (SharedSemantics.norm selector)

def structuralSelectorFromBytes (bytes : Bytes) : Word :=
  bytesToWordBE ((normalizeBytes bytes).take selectorBytes)

def selectorFromSignature (signature : String) : Word :=
  SharedSemantics.norm (Keccak.selector4 signature)

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

def decodeValueAtWithFuel? : Nat -> Bytes -> Nat -> Ty -> Option Value
  | 0, _, _, _ => none
  | _fuel + 1, argData, headIndex, Ty.bool => do
      let value ← readWord? argData (wordBytes * headIndex)
      if wordEq value 0 || wordEq value 1 then
        some (Value.word value)
      else
        none
  | _fuel + 1, argData, headIndex, Ty.address => do
      let value ← readWord? argData (wordBytes * headIndex)
      if addressFits value then
        some (Value.word value)
      else
        none
  | _fuel + 1, argData, headIndex, Ty.uint256 => do
      let value ← readWord? argData (wordBytes * headIndex)
      some (Value.word value)
  | _fuel + 1, argData, headIndex, Ty.int256 => do
      let value ← readWord? argData (wordBytes * headIndex)
      some (Value.int value)
  | _fuel + 1, argData, headIndex, Ty.fixedBytes size =>
      if 0 < size && size <= wordBytes then
        do
        let slot ← readBytes? argData (wordBytes * headIndex) wordBytes
        let bytes ← readBytes? slot 0 size
        let padding ← readBytes? slot size (wordBytes - size)
        if allZeroBytes padding then
          some (Value.word (bytesToWordBE bytes))
        else
          none
      else
        none
  | _fuel + 1, argData, headIndex, Ty.externalFunction => do
      let slot ← readBytes? argData (wordBytes * headIndex) wordBytes
      let addressBytes ← readBytes? slot 0 20
      let selectorPart ← readBytes? slot 20 selectorBytes
      let padding ←
        readBytes? slot (20 + selectorBytes)
          (wordBytes - 20 - selectorBytes)
      if allZeroBytes padding then
        some
          (Value.externalFunction
            (bytesToWordBE addressBytes) (bytesToWordBE selectorPart))
      else
        none
  | _fuel + 1, argData, headIndex, Ty.bytesCalldata => do
      let offset ← readWord? argData (wordBytes * headIndex)
      let length ← readWord? argData offset
      let bytes ← readBytes? argData (offset + wordBytes) length
      some (Value.bytes bytes)
  | fuel + 1, argData, headIndex, Ty.dynamicArray elementTy => do
      let offset ← readWord? argData (wordBytes * headIndex)
      let length ← readWord? argData offset
      let rec decodeDynamicArrayValues? :
          Nat -> Nat -> Option (List Value)
        | 0, _ => some []
        | remaining + 1, index => do
            let value ←
              decodeValueAtWithFuel? fuel
                (argData.drop (offset + wordBytes))
                index elementTy
            let step ← Ty.abiHeadWords? elementTy
            let rest ← decodeDynamicArrayValues? remaining (index + step)
            some (value :: rest)
      let values ← decodeDynamicArrayValues? length 0
      some (Value.dynamicArray values)
  | fuel + 1, argData, headIndex, Ty.fixedArray size elementTy =>
      let rec decodeArrayValues? (arrayData : Bytes) :
          Nat -> Nat -> Option (List Value)
        | 0, _ => some []
        | remaining + 1, index => do
            let value ← decodeValueAtWithFuel? fuel arrayData index elementTy
            let step ← Ty.abiHeadWords? elementTy
            let rest ← decodeArrayValues? arrayData remaining (index + step)
            some (value :: rest)
      if Ty.isDynamicAbi elementTy then
        do
        let offset ← readWord? argData (wordBytes * headIndex)
        let values ← decodeArrayValues? (argData.drop offset) size 0
        some (Value.fixedArray values)
      else
        do
        let values ← decodeArrayValues? argData size headIndex
        some (Value.fixedArray values)
  | fuel + 1, argData, headIndex, Ty.tuple elementTys =>
      let rec decodeTupleValues? (tupleData : Bytes) :
          List Ty -> Nat -> Option (List Value)
        | [], _ => some []
        | ty :: tys, index => do
            let value ← decodeValueAtWithFuel? fuel tupleData index ty
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

def decodeValueAt? (argData : Bytes) (headIndex : Nat)
    (ty : Ty) : Option Value :=
  decodeValueAtWithFuel? (Ty.abiDecodeFuel ty) argData headIndex ty

def decodeArgsAux? (argData : Bytes) :
    List Ty -> Nat -> Option (List Value)
  | [], _ => some []
  | ty :: tys, index => do
      let value ← decodeValueAt? argData index ty
      let headWords ← Ty.abiHeadWords? ty
      let values ← decodeArgsAux? argData tys (index + headWords)
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

def errorSelector : Word := 0x08c379a0

def stringBytes (text : String) : Bytes :=
  text.toList.map Char.toNat

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

def AbiCallResult.clearTransient (result : AbiCallResult) : AbiCallResult :=
  { result with state := result.state.clearTransient }

def Contract.rejectedValueCall? (contract : Contract)
    (state : State) : Option AbiCallResult := do
  let output ← Contract.encodeRevertData? contract RevertData.empty
  some { success := false, output, state := state }

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

def Contract.callContextAt (contract : Contract)
    (self sender value : Word) (calldata : Bytes) : Context :=
  { contract.context with
    calldata := normalizeBytes calldata
    self := SharedSemantics.norm self
    sender := SharedSemantics.norm sender
    value := SharedSemantics.norm value }

def Contract.callContext (contract : Contract)
    (sender value : Word) (calldata : Bytes) : Context :=
  Contract.callContextAt contract 0 sender value calldata

def Contract.callFallbackAtFrom? (fuel : Nat) (contract : Contract)
    (state : State) (self sender value : Word) (calldata : Bytes) :
    Option AbiCallResult := do
  let function ← Contract.findFallback? contract
  let args ← FunctionDef.fallbackArgs? function calldata
  let context := Contract.callContextAt contract self sender value calldata
  if function.acceptsValue value then
    match FunctionDef.call? fuel context function state args with
    | some (CallResult.returned state' values) => do
        let output ← FunctionDef.encodeFallbackOutput? function values
        some { success := true, output, state := state' }
    | some (CallResult.reverted state' revert) => do
        let output ← Contract.encodeRevertData? contract revert
        some { success := false, output, state := state' }
    | none => none
  else
    Contract.rejectedValueCall? contract state

def Contract.callFallbackFrom? (fuel : Nat) (contract : Contract)
    (state : State) (sender value : Word) (calldata : Bytes) :
    Option AbiCallResult :=
  Contract.callFallbackAtFrom? fuel contract state 0 sender value calldata

def Contract.callFallback? (fuel : Nat) (contract : Contract)
    (state : State) (calldata : Bytes) : Option AbiCallResult :=
  Contract.callFallbackFrom? fuel contract state 0 0 calldata

def Contract.callReceiveOrFallbackAtFrom? (fuel : Nat) (contract : Contract)
    (state : State) (self sender value : Word) (calldata : Bytes) :
    Option AbiCallResult :=
  if calldata.isEmpty then
    match Contract.findReceive? contract with
    | some function =>
        let context := Contract.callContextAt contract self sender value []
        if function.acceptsValue value then
          match FunctionDef.call? fuel context function state [] with
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
    | none => Contract.callFallbackAtFrom? fuel contract state
        self sender value calldata
  else
    Contract.callFallbackAtFrom? fuel contract state self sender value calldata

def Contract.callReceiveOrFallbackFrom? (fuel : Nat) (contract : Contract)
    (state : State) (sender value : Word) (calldata : Bytes) :
    Option AbiCallResult :=
  Contract.callReceiveOrFallbackAtFrom? fuel contract state 0 sender value
    calldata

def Contract.callReceiveOrFallback? (fuel : Nat) (contract : Contract)
    (state : State) (calldata : Bytes) : Option AbiCallResult :=
  Contract.callReceiveOrFallbackFrom? fuel contract state 0 0 calldata

def Contract.callCalldataAtFrom? (fuel : Nat) (contract : Contract)
    (state : State) (self sender value : Word) (calldata : Bytes) :
    Option AbiCallResult := do
  match readSelector? calldata with
  | some selector =>
      match contract.findFunctionBySelector? selector with
      | some function => do
          let args ←
            decodeArgs? (function.params.map BindingDecl.ty)
              (calldata.drop selectorBytes)
          let context :=
            Contract.callContextAt contract self sender value calldata
          if function.acceptsValue value then
            match function.call? fuel context state args with
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
          Contract.callFallbackAtFrom? fuel contract state
            self sender value calldata
  | none =>
      Contract.callReceiveOrFallbackAtFrom? fuel contract state
        self sender value calldata

def Contract.callCalldataFrom? (fuel : Nat) (contract : Contract)
    (state : State) (sender value : Word) (calldata : Bytes) :
    Option AbiCallResult :=
  Contract.callCalldataAtFrom? fuel contract state 0 sender value calldata

def Contract.callCalldataAt? (fuel : Nat) (contract : Contract)
    (state : State) (self : Word) (calldata : Bytes) :
    Option AbiCallResult :=
  Contract.callCalldataAtFrom? fuel contract state self 0 0 calldata

def Contract.callCalldata? (fuel : Nat) (contract : Contract)
    (state : State) (calldata : Bytes) : Option AbiCallResult :=
  Contract.callCalldataFrom? fuel contract state 0 0 calldata

def Contract.callCalldataTransactionAtFrom? (fuel : Nat)
    (contract : Contract) (state : State) (self sender value : Word)
    (calldata : Bytes) :
    Option AbiCallResult := do
  let result ←
    Contract.callCalldataAtFrom?
      fuel contract state.clearTransient self sender value calldata
  some result.clearTransient

def Contract.callCalldataTransactionFrom? (fuel : Nat) (contract : Contract)
    (state : State) (sender value : Word) (calldata : Bytes) :
    Option AbiCallResult :=
  Contract.callCalldataTransactionAtFrom? fuel contract state 0 sender value
    calldata

def Contract.callCalldataTransactionAt? (fuel : Nat) (contract : Contract)
    (state : State) (self : Word) (calldata : Bytes) :
    Option AbiCallResult :=
  Contract.callCalldataTransactionAtFrom? fuel contract state self 0 0
    calldata

def Contract.callCalldataTransaction? (fuel : Nat) (contract : Contract)
    (state : State) (calldata : Bytes) : Option AbiCallResult :=
  Contract.callCalldataTransactionFrom? fuel contract state 0 0 calldata

end ABI
end Source
end Solidity
end SolidCore

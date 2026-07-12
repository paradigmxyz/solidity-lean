/-
Witness corpus extracted verbatim from Checked.lean (Phase 3, sub-step a).

Hand-written example/witness definitions moved out of the semantics module.
Declaration names and namespaces are unchanged so the harness manifest's
`SolidCore.Solidity.TypeCheck.Examples` eval expressions still resolve; only the manifest `lean.imports` target
gains this module.
-/
import SolidCore.Solidity.Checked
import SolidCore.Witness.TypeCheck

namespace SolidCore
namespace Solidity
namespace TypeCheck

namespace Examples

def checkedSourceFunctionCallWithContext (fuel : Nat)
    (source : Solidity.SourceUnit) (contractName functionName : Name)
    (context : SolidCore.Solidity.Source.Context)
    (state : CoreState) (args : List CoreValue) :
    Except TypeError CoreCallResult :=
  SourceUnit.checkedCallFunctionWithContext
    fuel source contractName functionName context state args

/-- Witness fail-open twin (responder after fuel; see `foldFailOpen`). -/
def checkedSourceFunctionCallWithContextFailOpen (fuel : Nat)
    (responder : SolidCore.Solidity.Source.ScriptedResponder)
    (source : Solidity.SourceUnit) (contractName functionName : Name)
    (context : SolidCore.Solidity.Source.Context)
    (state : CoreState) (args : List CoreValue) :
    Except TypeError CoreCallResult :=
  SourceUnit.checkedCallFunctionWithContextFailOpen
    fuel responder source contractName functionName context state args

def checkedStorageReturnConditionalMatches : Except TypeError Bool := do
  let result ←
    ContractDecl.checkedCall 128
      Executable.Examples.storageReturnAliasContract
      (SolidCore.Solidity.Source.CallTarget.name
        "bindConditionalReturnedStorage")
      SolidCore.Solidity.Source.State.empty []
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _
      [SolidCore.Solidity.Source.Value.word value] =>
      Except.ok (value == 127)
  | _ => Except.ok false

def missingVisibilityExecutableContract : Solidity.ContractDecl :=
  { name := "MissingVisibilityExecutable"
    items :=
      [ Solidity.ContractItem.function
          { name := some "run"
            returns := [{ name := some "out", ty := Ty.uint 256 }]
            body :=
              some
                (Solidity.Stmt.returnValues
                  (some
                    (Solidity.Expr.literal
                      (Solidity.Literal.number "7")))) } ] }

def rawMissingVisibilityStillExecutes : Option Bool := do
  let result ←
    Executable.ContractDecl.call? 16 missingVisibilityExecutableContract
      (SolidCore.Solidity.Source.CallTarget.name "run")
      SolidCore.Solidity.Source.State.empty []
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _
      [SolidCore.Solidity.Source.Value.word value] =>
      some (value == 7)
  | _ => some false

def checkedMissingVisibilityRejected : Bool :=
  Result.isError
    (ContractDecl.checkedCall 16 missingVisibilityExecutableContract
      (SolidCore.Solidity.Source.CallTarget.name "run")
      SolidCore.Solidity.Source.State.empty [])

def checkedPreValidityBoundarySemanticsMatch : Bool :=
  rawMissingVisibilityStillExecutes == some true &&
    checkedMissingVisibilityRejected

def checkedFallbackReceiveContract : Solidity.ContractDecl :=
  { name := "CheckedFallbackReceive"
    items :=
      [ Solidity.ContractItem.stateVar
          { name := "x", ty := Ty.uint 256 }
      , Solidity.ContractItem.function
          { kind := FunctionKind.fallback
            visibility := some Visibility.external_
            body :=
              some
                (Solidity.Stmt.expr
                  (Solidity.Expr.assign
                    (Solidity.Expr.ident "x")
                    AssignOp.assign
                    (Solidity.Expr.literal
                      (Solidity.Literal.number "1")))) }
      , Solidity.ContractItem.function
          { kind := FunctionKind.receive
            visibility := some Visibility.external_
            mutability := StateMutability.payable
            body :=
              some
                (Solidity.Stmt.expr
                  (Solidity.Expr.assign
                    (Solidity.Expr.ident "x")
                    AssignOp.assign
                    (Solidity.Expr.literal
                      (Solidity.Literal.number "2")))) } ] }

def checkedFallbackDispatchMatches : Except TypeError Bool := do
  let result ←
    ContractDecl.checkedCallCalldata 16 checkedFallbackReceiveContract
      SolidCore.Solidity.Source.State.empty [0xde, 0xad, 0xbe, 0xef]
  Except.ok
    (result.success &&
      SolidCore.Solidity.Source.wordEq (result.state.loadSlot 0) 1 &&
      result.output == [])

def checkedReceiveDispatchMatches : Except TypeError Bool := do
  let result ←
    ContractDecl.checkedCallCalldata 16 checkedFallbackReceiveContract
      SolidCore.Solidity.Source.State.empty []
  Except.ok
    (result.success &&
      SolidCore.Solidity.Source.wordEq (result.state.loadSlot 0) 2 &&
      result.output == [])

def checkedPayableFallbackValueContract :
    Solidity.ContractDecl :=
  { name := "CheckedFallbackValue"
    items :=
      [ Solidity.ContractItem.stateVar
          { name := "last", ty := Ty.uint 256 }
      , Solidity.ContractItem.function
          { kind := FunctionKind.fallback
            visibility := some Visibility.external_
            mutability := StateMutability.payable
            body :=
              some
                (Solidity.Stmt.expr
                  (Solidity.Expr.assign
                    (Solidity.Expr.ident "last")
                    AssignOp.assign
                    (Solidity.Expr.member
                      (Solidity.Expr.ident "msg") "value"))) } ] }

def checkedPayableFallbackValueDispatchMatches :
    Except TypeError Bool := do
  let result ←
    ContractDecl.checkedCallCalldataFrom 16
      checkedPayableFallbackValueContract
      SolidCore.Solidity.Source.State.empty
      0xabc 33 [0xff, 0xff, 0xff, 0xff]
  Except.ok
    (result.success &&
      SolidCore.Solidity.Source.wordEq (result.state.loadSlot 0) 33 &&
      result.output == [])

def checkedPayableFallbackPlainEtherMatches :
    Except TypeError Bool := do
  let result ←
    ContractDecl.checkedCallCalldataFrom 16
      checkedPayableFallbackValueContract
      SolidCore.Solidity.Source.State.empty
      0xabc 44 []
  Except.ok
    (result.success &&
      SolidCore.Solidity.Source.wordEq (result.state.loadSlot 0) 44 &&
      result.output == [])

def checkedNonpayableFallbackRejectsValueMatches :
    Except TypeError Bool := do
  let result ←
    ContractDecl.checkedCallCalldataFrom 16 checkedFallbackReceiveContract
      SolidCore.Solidity.Source.State.empty
      0xabc 1 [0xff, 0xff, 0xff, 0xff]
  Except.ok
    (!result.success &&
      SolidCore.Solidity.Source.wordEq (result.state.loadSlot 0) 0 &&
      result.output == [])

def checkedMissingFallbackContract : Solidity.ContractDecl :=
  { name := "CheckedMissingFallback"
    items :=
      [ Solidity.ContractItem.stateVar
          { name := "x", ty := Ty.uint 256 }
      , Solidity.ContractItem.function
          { name := some "touch"
            visibility := some Visibility.public_
            body :=
              some
                (Solidity.Stmt.expr
                  (Solidity.Expr.assign
                    (Solidity.Expr.ident "x")
                    AssignOp.assign
                    (Solidity.Expr.literal
                      (Solidity.Literal.number "9")))) } ] }

def checkedMissingFallbackSelectorRejectsMatches :
    Except TypeError Bool := do
  let result ←
    ContractDecl.checkedCallCalldataFrom 16 checkedMissingFallbackContract
      SolidCore.Solidity.Source.State.empty
      0xabc 0 [0xde, 0xad, 0xbe, 0xef]
  Except.ok
    (!result.success &&
      SolidCore.Solidity.Source.wordEq (result.state.loadSlot 0) 0 &&
      result.output == [])

def checkedMissingReceiveFallbackPlainEtherRejectsMatches :
    Except TypeError Bool := do
  let result ←
    ContractDecl.checkedCallCalldataFrom 16 checkedMissingFallbackContract
      SolidCore.Solidity.Source.State.empty
      0xabc 1 []
  Except.ok
    (!result.success &&
      SolidCore.Solidity.Source.wordEq (result.state.loadSlot 0) 0 &&
      result.output == [])

def checkedCanonicalFallbackValueDispatchContractsAccepted : Bool :=
  Result.isOk
    (TypecheckedInput.checkedSourceUnit
      Executable.Examples.fallbackReceiveContract) &&
  Result.isOk
    (TypecheckedInput.checkedSourceUnit
      Executable.Examples.inheritedReceiveFallbackUnit) &&
  Result.isOk
    (TypecheckedInput.checkedSourceUnit
      Executable.Examples.fallbackBytesContract) &&
  Result.isOk
    (TypecheckedInput.checkedSourceUnit
      Executable.Examples.fallbackMsgDataContract) &&
  Result.isOk
    (TypecheckedInput.checkedSourceUnit
      Executable.Examples.receiveMsgValueContract) &&
  Result.isOk
    (TypecheckedInput.checkedSourceUnit
      Executable.Examples.fallbackMsgSenderContract) &&
  Result.isOk
    (TypecheckedInput.checkedSourceUnit
      Executable.Examples.payableFallbackValueContract) &&
  Result.isOk
    (TypecheckedInput.checkedSourceUnit
      Executable.Examples.missingFallbackContract) &&
  Result.isOk
    (TypecheckedInput.checkedSourceUnit
      Executable.Examples.payableFunctionValueContract) &&
  Result.isOk
    (TypecheckedInput.checkedSourceUnit
      Executable.Examples.nonpayableRejectsValueContract)

def checkedCanonicalFallbackDispatchMatches : Except TypeError Bool := do
  let result ←
    ContractDecl.checkedCallCalldata 16
      Executable.Examples.fallbackReceiveContract
      SolidCore.Solidity.Source.State.empty
      [0xde, 0xad, 0xbe, 0xef]
  Except.ok
    (result.success &&
      SolidCore.Solidity.Source.wordEq (result.state.loadSlot 0) 1 &&
      result.output == [])

def checkedCanonicalReceiveDispatchMatches : Except TypeError Bool := do
  let result ←
    ContractDecl.checkedCallCalldata 16
      Executable.Examples.fallbackReceiveContract
      SolidCore.Solidity.Source.State.empty []
  Except.ok
    (result.success &&
      SolidCore.Solidity.Source.wordEq (result.state.loadSlot 0) 2 &&
      result.output == [])

def checkedInheritedReceiveDispatchMatches : Except TypeError Bool := do
  let result ←
    CheckedInput.callCalldata 16
      Executable.Examples.inheritedReceiveFallbackUnit
      "InheritedReceiveFallbackChild"
      SolidCore.Solidity.Source.State.empty []
  Except.ok
    (result.success &&
      SolidCore.Solidity.Source.wordEq (result.state.loadSlot 0) 1 &&
      result.output == [])

def checkedOverriddenReceiveDispatchMatches : Except TypeError Bool := do
  let result ←
    CheckedInput.callCalldata 16
      Executable.Examples.inheritedReceiveFallbackUnit
      "InheritedReceiveFallbackOverride"
      SolidCore.Solidity.Source.State.empty []
  Except.ok
    (result.success &&
      SolidCore.Solidity.Source.wordEq (result.state.loadSlot 0) 2 &&
      result.output == [])

def checkedInheritedFallbackDispatchMatches : Except TypeError Bool := do
  let result ←
    CheckedInput.callCalldata 16
      Executable.Examples.inheritedReceiveFallbackUnit
      "InheritedReceiveFallbackChild"
      SolidCore.Solidity.Source.State.empty
      [0xde, 0xad, 0xbe, 0xef]
  Except.ok
    (result.success &&
      SolidCore.Solidity.Source.wordEq (result.state.loadSlot 0) 3 &&
      result.output == [])

def checkedOverriddenFallbackDispatchMatches : Except TypeError Bool := do
  let result ←
    CheckedInput.callCalldata 16
      Executable.Examples.inheritedReceiveFallbackUnit
      "InheritedReceiveFallbackOverride"
      SolidCore.Solidity.Source.State.empty
      [0xde, 0xad, 0xbe, 0xef]
  Except.ok
    (result.success &&
      SolidCore.Solidity.Source.wordEq (result.state.loadSlot 0) 4 &&
      result.output == [])

def checkedFallbackBytesDispatchMatches : Except TypeError Bool := do
  let result ←
    ContractDecl.checkedCallCalldata 16
      Executable.Examples.fallbackBytesContract
      SolidCore.Solidity.Source.State.empty [1, 2, 3]
  Except.ok (result.success && result.output == [1, 2, 3])

def checkedFallbackMsgDataDispatchMatches : Except TypeError Bool := do
  let result ←
    ContractDecl.checkedCallCalldata 16
      Executable.Examples.fallbackMsgDataContract
      SolidCore.Solidity.Source.State.empty [4, 5, 6]
  Except.ok (result.success && result.output == [4, 5, 6])

def checkedReceiveMsgValueDispatchMatches : Except TypeError Bool := do
  let result ←
    ContractDecl.checkedCallCalldataFrom 16
      Executable.Examples.receiveMsgValueContract
      SolidCore.Solidity.Source.State.empty 0xabc 77 []
  Except.ok
    (result.success &&
      SolidCore.Solidity.Source.wordEq (result.state.loadSlot 0) 77 &&
      result.output == [])

def checkedFallbackMsgSenderDispatchMatches : Except TypeError Bool := do
  let result ←
    ContractDecl.checkedCallCalldataFrom 16
      Executable.Examples.fallbackMsgSenderContract
      SolidCore.Solidity.Source.State.empty
      0xabc 0 [0xff, 0xff, 0xff, 0xff]
  Except.ok
    (result.success &&
      SolidCore.Solidity.Source.wordEq (result.state.loadSlot 0) 0xabc &&
      result.output == [])

def checkedCanonicalPayableFallbackValueDispatchMatches :
    Except TypeError Bool := do
  let result ←
    ContractDecl.checkedCallCalldataFrom 16
      Executable.Examples.payableFallbackValueContract
      SolidCore.Solidity.Source.State.empty
      0xabc 33 [0xff, 0xff, 0xff, 0xff]
  Except.ok
    (result.success &&
      SolidCore.Solidity.Source.wordEq (result.state.loadSlot 0) 33 &&
      result.output == [])

def checkedCanonicalPayableFallbackPlainEtherDispatchMatches :
    Except TypeError Bool := do
  let result ←
    ContractDecl.checkedCallCalldataFrom 16
      Executable.Examples.payableFallbackValueContract
      SolidCore.Solidity.Source.State.empty
      0xabc 44 []
  Except.ok
    (result.success &&
      SolidCore.Solidity.Source.wordEq (result.state.loadSlot 0) 44 &&
      result.output == [])

def checkedCanonicalNonpayableFallbackRejectsValueDispatchMatches :
    Except TypeError Bool := do
  let result ←
    ContractDecl.checkedCallCalldataFrom 16
      Executable.Examples.fallbackReceiveContract
      SolidCore.Solidity.Source.State.empty
      0xabc 1 [0xff, 0xff, 0xff, 0xff]
  Except.ok
    (!result.success &&
      SolidCore.Solidity.Source.wordEq (result.state.loadSlot 0) 0 &&
      result.output == [])

def checkedCanonicalMissingFallbackSelectorDispatchMatches :
    Except TypeError Bool := do
  let result ←
    ContractDecl.checkedCallCalldataFrom 16
      Executable.Examples.missingFallbackContract
      SolidCore.Solidity.Source.State.empty
      0xabc 0 [0xde, 0xad, 0xbe, 0xef]
  Except.ok
    (!result.success &&
      SolidCore.Solidity.Source.wordEq (result.state.loadSlot 0) 0 &&
      result.output == [])

def checkedCanonicalMissingReceiveFallbackPlainEtherDispatchMatches :
    Except TypeError Bool := do
  let result ←
    ContractDecl.checkedCallCalldataFrom 16
      Executable.Examples.missingFallbackContract
      SolidCore.Solidity.Source.State.empty
      0xabc 1 []
  Except.ok
    (!result.success &&
      SolidCore.Solidity.Source.wordEq (result.state.loadSlot 0) 0 &&
      result.output == [])

def checkedPayableFunctionValueDispatchMatches :
    Except TypeError Bool := do
  let calldata ←
    ContractDecl.checkedFunctionCalldata
      Executable.Examples.payableFunctionValueContract "deposit" []
  let result ←
    ContractDecl.checkedCallCalldataFrom 16
      Executable.Examples.payableFunctionValueContract
      SolidCore.Solidity.Source.State.empty 0xabc 55 calldata
  Except.ok
    (result.success &&
      SolidCore.Solidity.Source.wordEq (result.state.loadSlot 0) 55 &&
      result.output == [])

def checkedPayableFunctionDirectCallMatches :
    Except TypeError Bool := do
  let contract ←
    ContractDecl.checkedContract
      Executable.Examples.payableFunctionValueContract
  let result ←
    CheckedContract.callFunctionWithContext 16 contract "deposit"
      { contract.core.context with sender := 0xabc, value := 55 }
      SolidCore.Solidity.Source.State.empty []
  match result with
  | SolidCore.Solidity.Source.CallResult.returned state [] =>
      Except.ok (SolidCore.Solidity.Source.wordEq (state.loadSlot 0) 55)
  | _ => Except.ok false

def checkedNonpayableRejectsValueDispatchMatches :
    Except TypeError Bool := do
  let calldata ←
    ContractDecl.checkedFunctionCalldata
      Executable.Examples.nonpayableRejectsValueContract "touch" []
  let result ←
    ContractDecl.checkedCallCalldataFrom 16
      Executable.Examples.nonpayableRejectsValueContract
      SolidCore.Solidity.Source.State.empty 0xabc 1 calldata
  Except.ok
    (!result.success &&
      SolidCore.Solidity.Source.wordEq (result.state.loadSlot 0) 0 &&
      result.output == [])

def checkedNonpayableDirectCallRejectsValueMatches :
    Except TypeError Bool := do
  let contract ←
    ContractDecl.checkedContract
      Executable.Examples.nonpayableRejectsValueContract
  let result ←
    CheckedContract.callFunctionWithContext 16 contract "touch"
      { contract.core.context with sender := 0xabc, value := 1 }
      SolidCore.Solidity.Source.State.empty []
  match result with
  | SolidCore.Solidity.Source.CallResult.reverted state
      SolidCore.Solidity.Source.RevertData.empty =>
      Except.ok (SolidCore.Solidity.Source.wordEq (state.loadSlot 0) 0)
  | _ => Except.ok false

def checkedFallbackReceivePayableSemanticsMatch :
    Except TypeError Bool := do
  let fallback ← checkedFallbackDispatchMatches
  let receive ← checkedReceiveDispatchMatches
  let payableFallback ← checkedPayableFallbackValueDispatchMatches
  let payableEther ← checkedPayableFallbackPlainEtherMatches
  let nonpayableFallback ← checkedNonpayableFallbackRejectsValueMatches
  let missingFallback ← checkedMissingFallbackSelectorRejectsMatches
  let missingReceive ← checkedMissingReceiveFallbackPlainEtherRejectsMatches
  let canonicalFallback ← checkedCanonicalFallbackDispatchMatches
  let canonicalReceive ← checkedCanonicalReceiveDispatchMatches
  let inheritedReceive ← checkedInheritedReceiveDispatchMatches
  let overriddenReceive ← checkedOverriddenReceiveDispatchMatches
  let inheritedFallback ← checkedInheritedFallbackDispatchMatches
  let overriddenFallback ← checkedOverriddenFallbackDispatchMatches
  let fallbackBytes ← checkedFallbackBytesDispatchMatches
  let fallbackMsgData ← checkedFallbackMsgDataDispatchMatches
  let receiveMsgValue ← checkedReceiveMsgValueDispatchMatches
  let fallbackSender ← checkedFallbackMsgSenderDispatchMatches
  let canonicalPayableFallback ←
    checkedCanonicalPayableFallbackValueDispatchMatches
  let canonicalPayableEther ←
    checkedCanonicalPayableFallbackPlainEtherDispatchMatches
  let canonicalNonpayableFallback ←
    checkedCanonicalNonpayableFallbackRejectsValueDispatchMatches
  let canonicalMissingFallback ←
    checkedCanonicalMissingFallbackSelectorDispatchMatches
  let canonicalMissingReceive ←
    checkedCanonicalMissingReceiveFallbackPlainEtherDispatchMatches
  let payableFunctionDispatch ← checkedPayableFunctionValueDispatchMatches
  let payableFunctionDirect ← checkedPayableFunctionDirectCallMatches
  let nonpayableDispatch ← checkedNonpayableRejectsValueDispatchMatches
  let nonpayableDirect ← checkedNonpayableDirectCallRejectsValueMatches
  Except.ok
    (checkedCanonicalFallbackValueDispatchContractsAccepted &&
      fallback && receive && payableFallback && payableEther &&
      nonpayableFallback && missingFallback && missingReceive &&
      canonicalFallback && canonicalReceive && inheritedReceive &&
      overriddenReceive && inheritedFallback && overriddenFallback &&
      fallbackBytes && fallbackMsgData && receiveMsgValue &&
      fallbackSender && canonicalPayableFallback &&
      canonicalPayableEther && canonicalNonpayableFallback &&
      canonicalMissingFallback && canonicalMissingReceive &&
      payableFunctionDispatch && payableFunctionDirect &&
      nonpayableDispatch && nonpayableDirect)

def checkedFunctionCalldata (decl : Solidity.ContractDecl)
    (functionName : Name) (args : List CoreValue) :
    Except TypeError (List Byte) :=
  ContractDecl.checkedFunctionCalldata decl functionName args

def checkedDecodeUint256 (bytes : List Byte) : Except TypeError Word := do
  let values ←
    optionToExcept "ABI uint256 decode"
      (SolidCore.Solidity.Source.abiDecodeValues?
        [SolidCore.Solidity.Source.Ty.uint256] bytes)
  match values with
  | [SolidCore.Solidity.Source.Value.word value] => Except.ok value
  | _ => Except.error (executableFailure "ABI uint256 decode")

def checkedDecodeLowLevelReturn (value : CoreValue) :
    Except TypeError (Word × List Byte) :=
  optionToExcept "low-level return decode"
    (Executable.CoreValue.asLowLevelReturn? value)

def checkedDecodeWordPair (value : CoreValue) :
    Except TypeError (Word × Word) :=
  optionToExcept "word pair decode"
    (Executable.CoreValue.asWordPair? value)

def checkedAbiEncodeValues
    (tys : List SolidCore.Solidity.Source.Ty)
    (values : List CoreValue) : Except TypeError (List Byte) :=
  optionToExcept "ABI encode values"
    (SolidCore.Solidity.Source.ABI.encodeValues? tys values)

def checkedCallWordMatches (fuel : Nat) (source : SourceUnitAst)
    (contractName functionName : Name) (state : CoreState)
    (args : List CoreValue) (expected : Word) :
    Except TypeError Bool := do
  let result ←
    CheckedInput.callContract fuel source contractName
      (SolidCore.Solidity.Source.CallTarget.name functionName)
      state args
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _
      [SolidCore.Solidity.Source.Value.word value] =>
      Except.ok (SolidCore.Solidity.Source.wordEq value expected)
  | _ => Except.ok false

mutual

def checkedCoreValueEq : CoreValue -> CoreValue -> Bool
  | SolidCore.Solidity.Source.Value.word left,
      SolidCore.Solidity.Source.Value.word right =>
      SolidCore.Solidity.Source.wordEq left right
  | SolidCore.Solidity.Source.Value.int left,
      SolidCore.Solidity.Source.Value.int right =>
      SolidCore.Solidity.Source.wordEq left right
  | SolidCore.Solidity.Source.Value.bytes left,
      SolidCore.Solidity.Source.Value.bytes right => left == right
  | SolidCore.Solidity.Source.Value.externalFunction leftAddress leftSelector,
      SolidCore.Solidity.Source.Value.externalFunction rightAddress rightSelector =>
      SolidCore.Solidity.Source.wordEq leftAddress rightAddress &&
        SolidCore.Solidity.Source.wordEq leftSelector rightSelector
  | SolidCore.Solidity.Source.Value.fixedArray left,
      SolidCore.Solidity.Source.Value.fixedArray right =>
      checkedCoreValuesEq left right
  | SolidCore.Solidity.Source.Value.dynamicArray left,
      SolidCore.Solidity.Source.Value.dynamicArray right =>
      checkedCoreValuesEq left right
  | SolidCore.Solidity.Source.Value.tuple left,
      SolidCore.Solidity.Source.Value.tuple right =>
      checkedCoreValuesEq left right
  | SolidCore.Solidity.Source.Value.storageRef left,
      SolidCore.Solidity.Source.Value.storageRef right => left == right
  | SolidCore.Solidity.Source.Value.storagePathRef leftName leftPath,
      SolidCore.Solidity.Source.Value.storagePathRef rightName rightPath =>
      leftName == rightName && checkedCoreValuesEq leftPath rightPath
  | SolidCore.Solidity.Source.Value.memoryRef left,
      SolidCore.Solidity.Source.Value.memoryRef right => left == right
  | _, _ => false

def checkedCoreValuesEq : List CoreValue -> List CoreValue -> Bool
  | [], [] => true
  | left :: leftRest, right :: rightRest =>
      checkedCoreValueEq left right &&
        checkedCoreValuesEq leftRest rightRest
  | _, _ => false

end

def checkedCallValuesMatch (fuel : Nat) (source : SourceUnitAst)
    (contractName functionName : Name) (state : CoreState)
    (args expected : List CoreValue) : Except TypeError Bool := do
  let result ←
    CheckedInput.callContract fuel source contractName
      (SolidCore.Solidity.Source.CallTarget.name functionName)
      state args
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _ values =>
      Except.ok (checkedCoreValuesEq values expected)
  | _ => Except.ok false

def checkedCallSlotMatches (fuel : Nat) (source : SourceUnitAst)
    (contractName functionName : Name) (state : CoreState)
    (args : List CoreValue) (slot expected : Word) :
    Except TypeError Bool := do
  let result ←
    CheckedInput.callContract fuel source contractName
      (SolidCore.Solidity.Source.CallTarget.name functionName)
      state args
  match result with
  | SolidCore.Solidity.Source.CallResult.returned nextState _ =>
      Except.ok
        (SolidCore.Solidity.Source.wordEq
          (nextState.loadSlot slot) expected)
  | _ => Except.ok false

def checkedCallWordPairMatches (fuel : Nat) (source : SourceUnitAst)
    (contractName functionName : Name) (state : CoreState)
    (args : List CoreValue) (expectedX expectedY : Word) :
    Except TypeError Bool := do
  let result ←
    CheckedInput.callContract fuel source contractName
      (SolidCore.Solidity.Source.CallTarget.name functionName)
      state args
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _
      [ SolidCore.Solidity.Source.Value.word x
      , SolidCore.Solidity.Source.Value.word y ] =>
      Except.ok
        (SolidCore.Solidity.Source.wordEq x expectedX &&
          SolidCore.Solidity.Source.wordEq y expectedY)
  | SolidCore.Solidity.Source.CallResult.returned _ [value] =>
      let (x, y) ← checkedDecodeWordPair value
      Except.ok
        (SolidCore.Solidity.Source.wordEq x expectedX &&
          SolidCore.Solidity.Source.wordEq y expectedY)
  | _ => Except.ok false

def checkedConstructSlotMatches (fuel : Nat) (source : SourceUnitAst)
    (contractName : Name) (state : CoreState)
    (args : List CoreValue) (slot expected : Word) :
    Except TypeError Bool := do
  let result ←
    CheckedInput.constructContract fuel source contractName state args
  match result with
  | SolidCore.Solidity.Source.CallResult.returned nextState _ =>
      Except.ok
        (SolidCore.Solidity.Source.wordEq
          (nextState.loadSlot slot) expected)
  | _ => Except.ok false

def checkedProgramCommonLayerMatches : Except TypeError Bool := do
  let program ← CheckedInput.program simpleSource
  let checked ← CheckedInput.checkedSourceUnit simpleSource
  let decl ←
    optionToExcept "simple contract declaration"
      (Solidity.Executable.SourceUnit.findContract?
        simpleSource "C")
  let rawChecked ← TypecheckedInput.checkedSourceUnit simpleSource
  let rawCheckedViaNamespace ← SourceUnit.typechecked simpleSource
  let declChecked ← TypecheckedInput.checkedSourceUnit decl
  let declCheckedViaNamespace ← ContractDecl.typechecked decl
  let declSource ← TypecheckedInput.source decl
  let defaultName ← TypecheckedInput.defaultContractName decl
  let sourceDefaultName ← TypecheckedInput.defaultContractName simpleSource
  let checkedDefaultName ← TypecheckedInput.defaultContractName checked
  let checkedInputDefaultName ← CheckedInput.defaultContractName simpleSource
  let checkedSourceDefaultName ← CheckedInput.defaultContractName checked
  let _core ← CheckedInput.toCoreContract program "C"
  let function ← CheckedInput.coreFunction checked "C" "f"
  let directResult ←
    CheckedInput.callContract 16 simpleSource "C"
      (SolidCore.Solidity.Source.CallTarget.name "f")
      SolidCore.Solidity.Source.State.empty []
  let contract ← CheckedInput.contract checked "C"
  let contractResult ←
    CheckedContract.call 16 contract
      (SolidCore.Solidity.Source.CallTarget.name "f")
      SolidCore.Solidity.Source.State.empty []
  let functionResult ←
    CheckedInput.callFunctionWithContext 16 program "C" "f"
      contract.core.context
      SolidCore.Solidity.Source.State.empty []
  let calldata ←
    CheckedInput.functionCalldata simpleSource "C" "f" []
  let abiResult ←
    CheckedInput.callCalldata 16 checked "C"
      SolidCore.Solidity.Source.State.empty calldata
  let declResult ←
    CheckedInput.ownCall 16 decl
      (SolidCore.Solidity.Source.CallTarget.name "f")
      SolidCore.Solidity.Source.State.empty []
  let sourceOwnResult ←
    CheckedInput.ownCall 16 simpleSource
      (SolidCore.Solidity.Source.CallTarget.name "f")
      SolidCore.Solidity.Source.State.empty []
  let checkedOwnResult ←
    CheckedInput.ownCall 16 checked
      (SolidCore.Solidity.Source.CallTarget.name "f")
      SolidCore.Solidity.Source.State.empty []
  let abiValue ← checkedDecodeUint256 abiResult.output
  match directResult, contractResult, functionResult, declResult,
      sourceOwnResult, checkedOwnResult with
  | SolidCore.Solidity.Source.CallResult.returned _
      [SolidCore.Solidity.Source.Value.word direct],
    SolidCore.Solidity.Source.CallResult.returned _
      [SolidCore.Solidity.Source.Value.word viaContract],
    SolidCore.Solidity.Source.CallResult.returned _
      [SolidCore.Solidity.Source.Value.word viaFunction],
    SolidCore.Solidity.Source.CallResult.returned _
      [SolidCore.Solidity.Source.Value.word viaDecl],
    SolidCore.Solidity.Source.CallResult.returned _
      [SolidCore.Solidity.Source.Value.word viaSource],
    SolidCore.Solidity.Source.CallResult.returned _
      [SolidCore.Solidity.Source.Value.word viaChecked] =>
      Except.ok
        (direct == 7 &&
          viaContract == 7 &&
          viaFunction == 7 &&
          viaDecl == 7 &&
          viaSource == 7 &&
          viaChecked == 7 &&
          abiResult.success &&
          abiValue == 7 &&
          function.name == some "f" &&
          rawChecked.source.items.length == simpleSource.items.length &&
          rawCheckedViaNamespace.source.items.length ==
            simpleSource.items.length &&
          declChecked.source.items.length == 1 &&
          declCheckedViaNamespace.source.items.length == 1 &&
          declSource.items.length == 1 &&
          defaultName == "C" &&
          sourceDefaultName == "C" &&
          checkedDefaultName == "C" &&
          checkedInputDefaultName == "C" &&
          checkedSourceDefaultName == "C")
  | _, _, _, _, _, _ => Except.ok false

def checkedMultiContractDefaultNameRejected : Bool :=
  Result.isError
      (TypecheckedInput.defaultContractName internalAbiTwinSource) &&
    Result.isError
      (CheckedInput.defaultContractName internalAbiTwinSource)

def rawImportPathStillExecutes : Option Bool := do
  let result ←
    Executable.SourceUnit.callContract? 16 unresolvedImportSource "ImportC"
      (SolidCore.Solidity.Source.CallTarget.name "f")
      SolidCore.Solidity.Source.State.empty []
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _
      [SolidCore.Solidity.Source.Value.word value] =>
      some (value == 7)
  | _ => some false

def checkedPragmaMetadataAccepted : Except TypeError Bool :=
  checkedCallWordMatches 16 pragmaSimpleSource
    "PragmaC" "f" SolidCore.Solidity.Source.State.empty [] 7

def checkedPragmaVersionSyntaxAccepted : Bool :=
  pragmaVersionSyntaxAccepted

def checkedPragmaVersionSyntaxRejected : Bool :=
  pragmaVersionSyntaxRejected

def checkedPragmaDirectiveSyntaxRejected : Bool :=
  pragmaDirectiveSyntaxRejected

def checkedPragmaAbiCoderV1Accepted : Bool :=
  pragmaAbiCoderV1DisciplineAccepted

def checkedPragmaAbiCoderV1Rejected : Bool :=
  pragmaAbiCoderV1DisciplineRejected

def checkedUnresolvedImportRejected : Bool :=
  Result.isError (TypecheckedInput.checkedSourceUnit unresolvedImportSource)

def checkedSourceUnitDirectiveBoundarySemanticsMatch :
    Except TypeError Bool := do
  let pragma ← checkedPragmaMetadataAccepted
  Except.ok
    (rawImportPathStillExecutes == some true &&
      checkedUnresolvedImportRejected &&
      checkedPragmaVersionSyntaxAccepted &&
      checkedPragmaVersionSyntaxRejected &&
      checkedPragmaDirectiveSyntaxRejected &&
      checkedPragmaAbiCoderV1Accepted &&
      checkedPragmaAbiCoderV1Rejected &&
      pragma)

def checkedAbiCallUintMatches (fuel : Nat) (source : SourceUnitAst)
    (contractName functionName : Name) (state : CoreState)
    (args : List CoreValue) (expected : Word) :
    Except TypeError Bool := do
  let calldata ←
    CheckedInput.functionCalldata source contractName functionName args
  let result ←
    CheckedInput.callCalldata fuel source contractName state calldata
  let value ← checkedDecodeUint256 result.output
  Except.ok
    (result.success && SolidCore.Solidity.Source.wordEq value expected)

def checkedPrimitiveAbiContract : Solidity.ContractDecl :=
  { name := "CheckedPrimitiveAbi"
    items :=
      [ ContractItem.function
          { Executable.Examples.boolIdentityFunction with
            visibility := some Visibility.public_
            mutability := StateMutability.pure }
      , ContractItem.function
          { Executable.Examples.addressIdentityFunction with
            visibility := some Visibility.public_
            mutability := StateMutability.pure }
      , ContractItem.function
          { Executable.Examples.fixedBytesEchoFunction with
            visibility := some Visibility.public_
            mutability := StateMutability.pure } ] }

def checkedPrimitiveAbiContractAccepted : Bool :=
  Result.isOk (CheckedInput.program checkedPrimitiveAbiContract)

def checkedPrimitiveAbiOwnCallWordMatches (functionName : Name)
    (args : List CoreValue) (expected : Word) : Except TypeError Bool := do
  let result ←
    CheckedInput.ownCall 8 checkedPrimitiveAbiContract
      (SolidCore.Solidity.Source.CallTarget.name functionName)
      SolidCore.Solidity.Source.State.empty args
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _
      [SolidCore.Solidity.Source.Value.word value] =>
      Except.ok (SolidCore.Solidity.Source.wordEq value expected)
  | _ => Except.ok false

def checkedBoolIdentityCallMatches : Except TypeError Bool :=
  checkedPrimitiveAbiOwnCallWordMatches "idBool"
    [SolidCore.Solidity.Source.Value.word 1] 1

def checkedAddressIdentityCallMatches : Except TypeError Bool :=
  checkedPrimitiveAbiOwnCallWordMatches "idAddress"
    [SolidCore.Solidity.Source.Value.word 0x1234] 0x1234

def checkedAddressAbiCalldataMatches : Except TypeError Bool := do
  let calldata ←
    ContractDecl.checkedFunctionCalldata
      checkedPrimitiveAbiContract "idAddress"
      [SolidCore.Solidity.Source.Value.word 0x1234]
  let result ←
    ContractDecl.checkedCallCalldata 8 checkedPrimitiveAbiContract
      SolidCore.Solidity.Source.State.empty calldata
  let expected ←
    checkedAbiEncodeValues
      [SolidCore.Solidity.Source.Ty.address]
      [SolidCore.Solidity.Source.Value.word 0x1234]
  Except.ok (result.success && result.output == expected)

def checkedAddressAbiRejectsWideEncode : Bool :=
  Result.isError
    (checkedAbiEncodeValues
      [SolidCore.Solidity.Source.Ty.address]
      [SolidCore.Solidity.Source.Value.word (2 ^ 160)])

def checkedAddressAbiRejectsWideCalldata : Bool :=
  let selector :=
    SolidCore.Solidity.Source.ABI.encodeSelector
      (SolidCore.Solidity.Source.ABI.selectorFromSignature
        "idAddress(address)")
  let calldata :=
    selector ++
      SolidCore.Solidity.Source.ABI.encodeWord (2 ^ 160)
  Result.isError
    (ContractDecl.checkedCallCalldata 8 checkedPrimitiveAbiContract
      SolidCore.Solidity.Source.State.empty calldata)

def checkedFixedBytesAbiCalldataMatches : Except TypeError Bool := do
  let calldata ←
    ContractDecl.checkedFunctionCalldata
      checkedPrimitiveAbiContract "echo4"
      [SolidCore.Solidity.Source.Value.word 0xaabbccdd]
  let result ←
    ContractDecl.checkedCallCalldata 16 checkedPrimitiveAbiContract
      SolidCore.Solidity.Source.State.empty calldata
  let expected ←
    checkedAbiEncodeValues
      [SolidCore.Solidity.Source.Ty.fixedBytes 4]
      [SolidCore.Solidity.Source.Value.word 0xaabbccdd]
  Except.ok (result.success && result.output == expected)

def checkedFixedBytesAbiRejectsWideEncode : Bool :=
  Result.isError
    (checkedAbiEncodeValues
      [SolidCore.Solidity.Source.Ty.fixedBytes 4]
      [SolidCore.Solidity.Source.Value.word (2 ^ 32)])

def checkedFixedBytesAbiRejectsDirtyPadding : Bool :=
  let selector :=
    SolidCore.Solidity.Source.ABI.encodeSelector
      (SolidCore.Solidity.Source.ABI.selectorFromSignature
        "echo4(bytes4)")
  let calldata :=
    selector ++ [0xaa, 0xbb, 0xcc, 0xdd, 1] ++
      List.replicate 27 0
  Result.isError
    (ContractDecl.checkedCallCalldata 16 checkedPrimitiveAbiContract
      SolidCore.Solidity.Source.State.empty calldata)

def checkedDataTypeSourceUnitsAccepted : Bool :=
  Result.isOk
      (TypecheckedInput.checkedSourceUnit
        Executable.Examples.udvtSourceUnit) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit
        Executable.Examples.enumSourceUnit) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit
        Executable.Examples.structSourceUnit)

def checkedUdvtSetState : Except TypeError CoreState := do
  let result ←
    CheckedInput.callContract 32 Executable.Examples.udvtSourceUnit "UDVT"
      (SolidCore.Solidity.Source.CallTarget.name "set")
      SolidCore.Solidity.Source.State.empty
      [SolidCore.Solidity.Source.Value.word 42]
  match result with
  | SolidCore.Solidity.Source.CallResult.returned state _ =>
      Except.ok state
  | _ => Except.error (executableFailure "UDVT set")

def checkedUdvtReadMatches : Except TypeError Bool := do
  let state ← checkedUdvtSetState
  checkedCallWordMatches 32 Executable.Examples.udvtSourceUnit
    "UDVT" "read" state [] 42

def checkedUdvtPublicGetterMatches : Except TypeError Bool := do
  let state ← checkedUdvtSetState
  checkedCallWordMatches 32 Executable.Examples.udvtSourceUnit
    "UDVT" "last" state [] 42

def checkedUdvtRoundtripMatches : Except TypeError Bool :=
  checkedCallWordMatches 32 Executable.Examples.udvtSourceUnit
    "UDVT" "roundtrip" SolidCore.Solidity.Source.State.empty
    [SolidCore.Solidity.Source.Value.word 77] 77

def checkedUserValueWrapUnwrapMatches : Except TypeError Bool :=
  checkedCallWordMatches 16 userValueWrapUnwrapSource
    "UserValueWrap" "unwrap" SolidCore.Solidity.Source.State.empty [] 1

def checkedBadUserValueUnwrapRejected : Bool :=
  Result.isError (TypecheckedInput.checkedSourceUnit badUserValueUnwrapSource)

def checkedUdvtAbiSetState : Except TypeError CoreState := do
  let calldata ←
    CheckedInput.functionCalldata
      Executable.Examples.udvtSourceUnit "UDVT" "set"
      [SolidCore.Solidity.Source.Value.word 42]
  let result ←
    CheckedInput.callCalldata 32 Executable.Examples.udvtSourceUnit
      "UDVT" SolidCore.Solidity.Source.State.empty calldata
  if result.success then
    Except.ok result.state
  else
    Except.error (executableFailure "UDVT ABI set")

def checkedUdvtAbiGetterMatches : Except TypeError Bool := do
  let state ← checkedUdvtAbiSetState
  checkedAbiCallUintMatches 32 Executable.Examples.udvtSourceUnit
    "UDVT" "last" state [] 42

def checkedUdvtAbiEchoMatches : Except TypeError Bool :=
  checkedAbiCallUintMatches 32 Executable.Examples.udvtSourceUnit
    "UDVT" "echo" SolidCore.Solidity.Source.State.empty
    [SolidCore.Solidity.Source.Value.word 55] 55

def checkedUdvtEventTopicMatches : Except TypeError Bool := do
  let contract ←
    CheckedInput.toCoreContract
      Executable.Examples.udvtSourceUnit "UDVT"
  let event ←
    optionToExcept "UDVT Seen event"
      (contract.eventDecls.find? (fun event => event.name == "Seen"))
  let field ←
    optionToExcept "UDVT Seen field" event.fields.head?
  let fieldIsUint256 :=
    match field.ty with
    | SolidCore.Solidity.Source.Ty.uint256 => true
    | _ => false
  Except.ok
    (event.topic? ==
      some (SolidCore.Solidity.Source.Keccak.digestWord
        "Seen(uint256)") &&
      fieldIsUint256 && field.indexed)

def checkedUdvtErrorSelectorMatches : Except TypeError Bool := do
  let contract ←
    CheckedInput.toCoreContract
      Executable.Examples.udvtSourceUnit "UDVT"
  let err ←
    optionToExcept "UDVT Bad error"
      (contract.errorDecls.find? (fun err => err.name == "Bad"))
  let field ←
    optionToExcept "UDVT Bad field" err.fields.head?
  let fieldIsUint256 :=
    match field with
    | SolidCore.Solidity.Source.Ty.uint256 => true
    | _ => false
  Except.ok
    (err.selector ==
      SolidCore.Solidity.Source.ABI.selectorFromSignature
        "Bad(uint256)" &&
      fieldIsUint256)

def checkedEnumSetState : Except TypeError CoreState := do
  let result ←
    CheckedInput.callContract 32 Executable.Examples.enumSourceUnit
      "EnumDemo"
      (SolidCore.Solidity.Source.CallTarget.name "setGoStraight")
      SolidCore.Solidity.Source.State.empty []
  match result with
  | SolidCore.Solidity.Source.CallResult.returned state _ =>
      Except.ok state
  | _ => Except.error (executableFailure "enum set")

def checkedEnumPublicGetterMatches : Except TypeError Bool := do
  let state ← checkedEnumSetState
  checkedCallWordMatches 32 Executable.Examples.enumSourceUnit
    "EnumDemo" "choice" state [] 2

def checkedEnumReadAsUintMatches : Except TypeError Bool := do
  let state ← checkedEnumSetState
  checkedCallWordMatches 32 Executable.Examples.enumSourceUnit
    "EnumDemo" "readAsUint" state [] 2

def checkedEnumTypeMinMaxMatches : Except TypeError Bool := do
  let largest ←
    checkedCallWordMatches 32 Executable.Examples.enumSourceUnit
      "EnumDemo" "largest" SolidCore.Solidity.Source.State.empty [] 3
  let smallest ←
    checkedCallWordMatches 32 Executable.Examples.enumSourceUnit
      "EnumDemo" "smallest" SolidCore.Solidity.Source.State.empty [] 0
  Except.ok (largest && smallest)

def checkedEnumConversionInRangeMatches : Except TypeError Bool := do
  let result ←
    CheckedInput.callContract 32 Executable.Examples.enumSourceUnit
      "EnumDemo"
      (SolidCore.Solidity.Source.CallTarget.name "setFromUint")
      SolidCore.Solidity.Source.State.empty
      [SolidCore.Solidity.Source.Value.word 1]
  match result with
  | SolidCore.Solidity.Source.CallResult.returned state _ =>
      checkedCallWordMatches 32 Executable.Examples.enumSourceUnit
        "EnumDemo" "choice" state [] 1
  | _ => Except.ok false

def checkedEnumConversionOutOfRangePanics :
    Except TypeError Bool := do
  let result ←
    CheckedInput.callContract 32 Executable.Examples.enumSourceUnit
      "EnumDemo"
      (SolidCore.Solidity.Source.CallTarget.name "setFromUint")
      SolidCore.Solidity.Source.State.empty
      [SolidCore.Solidity.Source.Value.word 9]
  match result with
  | SolidCore.Solidity.Source.CallResult.reverted _
      (SolidCore.Solidity.Source.RevertData.panic code) =>
      Except.ok (code == 0x21)
  | _ => Except.ok false

def checkedEnumLiteralConversionSource : SourceUnitAst :=
  enumConversionSource "EnumLiteralConversion"
    (enumConversionFunction "fromLiteral" (numberExpr "1"))

def checkedEnumTypedOutOfRangeConversionSource : SourceUnitAst :=
  enumConversionSource "EnumTypedOutOfRangeConversion"
    (enumConversionFunction "fromTyped"
      (Expr.call (Expr.typeName uint256)
        [Arg.positional (numberExpr "2")]))

def checkedEnumToUintSource : SourceUnitAst :=
  enumConversionSource "EnumToUint" enumToUintFunction

def checkedEnumOutOfRangeLiteralConversionSource : SourceUnitAst :=
  enumConversionSource "BadEnumOutOfRangeLiteral"
    (enumConversionFunction "fromLiteral" (numberExpr "2"))

def checkedEnumNegativeLiteralConversionSource : SourceUnitAst :=
  enumConversionSource "BadEnumNegativeLiteral"
    (enumConversionFunction "fromLiteral"
      (Expr.unary UnaryOp.neg (numberExpr "1")))

def checkedEnumSourceDisciplineAccepted : Bool :=
  Result.isOk (TypecheckedInput.checkedSourceUnit enumMemberSource) &&
    Result.isOk (TypecheckedInput.checkedSourceUnit enumMinMaxSource) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit
        checkedEnumLiteralConversionSource) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit
        checkedEnumTypedOutOfRangeConversionSource) &&
    Result.isOk (TypecheckedInput.checkedSourceUnit checkedEnumToUintSource)

def checkedEnumSourceDisciplineRejected : Bool :=
  Result.isError (TypecheckedInput.checkedSourceUnit emptyEnumSource) &&
    Result.isError (TypecheckedInput.checkedSourceUnit badEnumMemberSource) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit
        checkedEnumOutOfRangeLiteralConversionSource) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit
        checkedEnumNegativeLiteralConversionSource) &&
    Result.isError (TypecheckedInput.checkedSourceUnit enumToIntSource)

def checkedEnumMemberFixtureMatches :
    Except TypeError Bool :=
  checkedCallWordMatches 16 enumMemberSource
    "EnumUser" "red" SolidCore.Solidity.Source.State.empty [] 0

def checkedEnumMinMaxFixtureMatches :
    Except TypeError Bool := do
  let minimum ←
    checkedCallWordMatches 16 enumMinMaxSource
      "EnumMinMax" "minimum"
      SolidCore.Solidity.Source.State.empty [] 0
  let maximum ←
    checkedCallWordMatches 16 enumMinMaxSource
      "EnumMinMax" "maximum"
      SolidCore.Solidity.Source.State.empty [] 1
  Except.ok (minimum && maximum)

def checkedEnumLiteralConversionFixtureMatches :
    Except TypeError Bool :=
  checkedCallWordMatches 16 checkedEnumLiteralConversionSource
    "EnumLiteralConversion" "fromLiteral"
    SolidCore.Solidity.Source.State.empty [] 1

def checkedEnumTypedOutOfRangeConversionFixturePanics :
    Except TypeError Bool := do
  let result ←
    CheckedInput.callContract 16
      checkedEnumTypedOutOfRangeConversionSource
      "EnumTypedOutOfRangeConversion"
      (SolidCore.Solidity.Source.CallTarget.name "fromTyped")
      SolidCore.Solidity.Source.State.empty []
  match result with
  | SolidCore.Solidity.Source.CallResult.reverted _
      (SolidCore.Solidity.Source.RevertData.panic code) =>
      Except.ok (code == 0x21)
  | _ => Except.ok false

def checkedEnumToUintConversionFixtureMatches :
    Except TypeError Bool :=
  checkedCallWordMatches 16 checkedEnumToUintSource
    "EnumToUint" "asUint" SolidCore.Solidity.Source.State.empty
    [SolidCore.Solidity.Source.Value.word 1] 1

def checkedEnumAbiEchoUsesUint8Selector :
    Except TypeError Bool :=
  checkedAbiCallUintMatches 32 Executable.Examples.enumSourceUnit
    "EnumDemo" "echo" SolidCore.Solidity.Source.State.empty
    [SolidCore.Solidity.Source.Value.word 3] 3

def checkedEnumEventTopicMatches : Except TypeError Bool := do
  let contract ←
    CheckedInput.toCoreContract
      Executable.Examples.enumSourceUnit "EnumDemo"
  let event ←
    optionToExcept "enum Seen event"
      (contract.eventDecls.find? (fun event => event.name == "Seen"))
  let field ←
    optionToExcept "enum Seen field" event.fields.head?
  let fieldIsUint :=
    match field.ty with
    | SolidCore.Solidity.Source.Ty.uint256 => true
    | _ => false
  Except.ok
    (event.topic? ==
      some (SolidCore.Solidity.Source.Keccak.digestWord
        "Seen(uint8)") &&
      fieldIsUint && field.indexed)

def checkedEnumErrorSelectorMatches : Except TypeError Bool := do
  let contract ←
    CheckedInput.toCoreContract
      Executable.Examples.enumSourceUnit "EnumDemo"
  let err ←
    optionToExcept "enum Bad error"
      (contract.errorDecls.find? (fun err => err.name == "Bad"))
  let field ←
    optionToExcept "enum Bad field" err.fields.head?
  let fieldIsUint :=
    match field with
    | SolidCore.Solidity.Source.Ty.uint256 => true
    | _ => false
  Except.ok
    (err.selector ==
      SolidCore.Solidity.Source.ABI.selectorFromSignature
        "Bad(uint8)" &&
      fieldIsUint)

def checkedStructNamedConstructorFieldSumMatches :
    Except TypeError Bool :=
  checkedCallWordMatches 48 Executable.Examples.structSourceUnit
    "StructDemo" "sum" SolidCore.Solidity.Source.State.empty
    [ SolidCore.Solidity.Source.Value.word 7
    , SolidCore.Solidity.Source.Value.word 8 ] 15

def checkedStructConstructorFieldAccessMatches :
    Except TypeError Bool :=
  checkedCallWordMatches 16 pairConstructorFieldSource
    "StructCtor" "pairX" SolidCore.Solidity.Source.State.empty [] 1

def checkedStructConstructorInvalidSourcesRejected : Bool :=
  Result.isError
      (TypecheckedInput.checkedSourceUnit
        badPairConstructorMissingFieldSource) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit
        badPairConstructorMixedArgsSource) &&
    Result.isError (TypecheckedInput.checkedSourceUnit badStructFieldSource)

def checkedRecursiveStructTypeDisciplineAccepted : Bool :=
  Result.isOk
      (TypecheckedInput.checkedSourceUnit dynamicRecursiveStructSource) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit
        functionPointerRecursiveStructSource)

def checkedRecursiveStructTypeDisciplineRejected : Bool :=
  Result.isError
    (TypecheckedInput.checkedSourceUnit mutualRecursiveStructSource)

def checkedStructFieldAssignmentMatches : Except TypeError Bool :=
  checkedCallWordMatches 48 Executable.Examples.structSourceUnit
    "StructDemo" "replaceY" SolidCore.Solidity.Source.State.empty [] 9

def checkedStructStorageFieldAssignmentMatches :
    Except TypeError Bool := do
  let returned ←
    checkedCallWordMatches 16 structFieldAssignSource
      "StructStorage" "writeField"
      SolidCore.Solidity.Source.State.empty [] 1
  let slot ←
    checkedCallSlotMatches 16 structFieldAssignSource
      "StructStorage" "writeField"
      SolidCore.Solidity.Source.State.empty [] 0 3
  Except.ok (returned && slot)

def checkedStructStorageFieldAssignmentViewRejected : Bool :=
  Result.isError
    (TypecheckedInput.checkedSourceUnit structFieldAssignViewSource)

def checkedStructAbiEchoMatches : Except TypeError Bool := do
  let tupleTy :=
    SolidCore.Solidity.Source.Ty.tuple
      [ SolidCore.Solidity.Source.Ty.uint256
      , SolidCore.Solidity.Source.Ty.uint256 ]
  let tupleValue :=
    SolidCore.Solidity.Source.Value.tuple
      [ SolidCore.Solidity.Source.Value.word 3
      , SolidCore.Solidity.Source.Value.word 4 ]
  let calldata ←
    CheckedInput.functionCalldata
      Executable.Examples.structSourceUnit "StructDemo" "echo"
      [tupleValue]
  let result ←
    CheckedInput.callCalldata 48 Executable.Examples.structSourceUnit
      "StructDemo" SolidCore.Solidity.Source.State.empty calldata
  let expected ← checkedAbiEncodeValues [tupleTy] [tupleValue]
  Except.ok (result.success && result.output == expected)

def checkedStructEventTopicMatches : Except TypeError Bool := do
  let contract ←
    CheckedInput.toCoreContract
      Executable.Examples.structSourceUnit "StructDemo"
  let event ←
    optionToExcept "struct Seen event"
      (contract.eventDecls.find? (fun event => event.name == "Seen"))
  let field ←
    optionToExcept "struct Seen field" event.fields.head?
  let fieldIsTuple :=
    match field.ty with
    | SolidCore.Solidity.Source.Ty.tuple
        [ SolidCore.Solidity.Source.Ty.uint256
        , SolidCore.Solidity.Source.Ty.uint256 ] => true
    | _ => false
  Except.ok
    (event.topic? ==
      some
        (SolidCore.Solidity.Source.Keccak.digestWord
          "Seen((uint256,uint256))") &&
      fieldIsTuple && !field.indexed)

def checkedStructErrorSelectorMatches : Except TypeError Bool := do
  let contract ←
    CheckedInput.toCoreContract
      Executable.Examples.structSourceUnit "StructDemo"
  let err ←
    optionToExcept "struct Bad error"
      (contract.errorDecls.find? (fun err => err.name == "Bad"))
  let field ←
    optionToExcept "struct Bad field" err.fields.head?
  let fieldIsTuple :=
    match field with
    | SolidCore.Solidity.Source.Ty.tuple
        [ SolidCore.Solidity.Source.Ty.uint256
        , SolidCore.Solidity.Source.Ty.uint256 ] => true
    | _ => false
  Except.ok
    (err.selector ==
      SolidCore.Solidity.Source.ABI.selectorFromSignature
        "Bad((uint256,uint256))" &&
      fieldIsTuple)

def checkedStorageStructSourceUnitAccepted : Bool :=
  Result.isOk
    (TypecheckedInput.checkedSourceUnit
      Executable.Examples.storageStructSourceUnit)

def checkedStorageStructSetState : Except TypeError CoreState := do
  let result ←
    CheckedInput.callContract 48
      Executable.Examples.storageStructSourceUnit "StorageStructDemo"
      (SolidCore.Solidity.Source.CallTarget.name "set")
      SolidCore.Solidity.Source.State.empty
      [ SolidCore.Solidity.Source.Value.word 11
      , SolidCore.Solidity.Source.Value.word 12 ]
  match result with
  | SolidCore.Solidity.Source.CallResult.returned state _ =>
      Except.ok state
  | _ => Except.error (executableFailure "storage struct set")

def checkedStorageStructSumMatches : Except TypeError Bool := do
  let state ← checkedStorageStructSetState
  checkedCallWordMatches 48
    Executable.Examples.storageStructSourceUnit
    "StorageStructDemo" "sum" state [] 23

def checkedStorageStructFieldWriteState :
    Except TypeError CoreState := do
  let state ← checkedStorageStructSetState
  let result ←
    CheckedInput.callContract 48
      Executable.Examples.storageStructSourceUnit "StorageStructDemo"
      (SolidCore.Solidity.Source.CallTarget.name "setY")
      state [SolidCore.Solidity.Source.Value.word 40]
  match result with
  | SolidCore.Solidity.Source.CallResult.returned state _ =>
      Except.ok state
  | _ => Except.error (executableFailure "storage struct setY")

def checkedStorageStructFieldWriteMatches :
    Except TypeError Bool := do
  let state ← checkedStorageStructFieldWriteState
  checkedCallWordMatches 48
    Executable.Examples.storageStructSourceUnit
    "StorageStructDemo" "sum" state [] 51

def checkedStorageStructAliasFieldWriteState :
    Except TypeError CoreState := do
  let state ← checkedStorageStructSetState
  let result ←
    CheckedInput.callContract 48
      Executable.Examples.storageStructSourceUnit "StorageStructDemo"
      (SolidCore.Solidity.Source.CallTarget.name "aliasSetY")
      state [SolidCore.Solidity.Source.Value.word 70]
  match result with
  | SolidCore.Solidity.Source.CallResult.returned state _ =>
      Except.ok state
  | _ => Except.error (executableFailure "storage struct aliasSetY")

def checkedStorageStructAliasFieldWriteMatches :
    Except TypeError Bool := do
  let state ← checkedStorageStructAliasFieldWriteState
  checkedCallWordMatches 48
    Executable.Examples.storageStructSourceUnit
    "StorageStructDemo" "sum" state [] 81

def checkedStorageStructAliasReadMatches :
    Except TypeError Bool := do
  let state ← checkedStorageStructAliasFieldWriteState
  checkedCallWordMatches 48
    Executable.Examples.storageStructSourceUnit
    "StorageStructDemo" "aliasSum" state [] 81

def checkedStorageStructInternalParamSetState :
    Except TypeError CoreState := do
  let state ← checkedStorageStructSetState
  let result ←
    CheckedInput.callContract 64
      Executable.Examples.storageStructSourceUnit "StorageStructDemo"
      (SolidCore.Solidity.Source.CallTarget.name "internalSetY")
      state [SolidCore.Solidity.Source.Value.word 50]
  match result with
  | SolidCore.Solidity.Source.CallResult.returned state _ =>
      Except.ok state
  | _ => Except.error (executableFailure "storage struct internalSetY")

def checkedStorageStructInternalParamFieldWriteMatches :
    Except TypeError Bool := do
  let state ← checkedStorageStructInternalParamSetState
  checkedCallWordMatches 48
    Executable.Examples.storageStructSourceUnit
    "StorageStructDemo" "sum" state [] 61

def checkedStorageStructInternalParamAliasSetState :
    Except TypeError CoreState := do
  let state ← checkedStorageStructSetState
  let result ←
    CheckedInput.callContract 64
      Executable.Examples.storageStructSourceUnit "StorageStructDemo"
      (SolidCore.Solidity.Source.CallTarget.name "internalAliasSetY")
      state [SolidCore.Solidity.Source.Value.word 60]
  match result with
  | SolidCore.Solidity.Source.CallResult.returned state _ =>
      Except.ok state
  | _ =>
      Except.error
        (executableFailure "storage struct internalAliasSetY")

def checkedStorageStructInternalParamAliasFieldWriteMatches :
    Except TypeError Bool := do
  let state ← checkedStorageStructInternalParamAliasSetState
  checkedCallWordMatches 48
    Executable.Examples.storageStructSourceUnit
    "StorageStructDemo" "sum" state [] 71

def checkedStorageStructInternalParamReadMatches :
    Except TypeError Bool := do
  let state ← checkedStorageStructInternalParamAliasSetState
  checkedCallWordMatches 64
    Executable.Examples.storageStructSourceUnit
    "StorageStructDemo" "internalSum" state [] 71

def checkedStorageStructPublicGetterMatches :
    Except TypeError Bool := do
  let state ← checkedStorageStructFieldWriteState
  checkedCallWordPairMatches 48
    Executable.Examples.storageStructSourceUnit
    "StorageStructDemo" "origin" state [] 11 40

def checkedStorageStructDeleteState :
    Except TypeError CoreState := do
  let state ← checkedStorageStructFieldWriteState
  let result ←
    CheckedInput.callContract 48
      Executable.Examples.storageStructSourceUnit "StorageStructDemo"
      (SolidCore.Solidity.Source.CallTarget.name "clear")
      state []
  match result with
  | SolidCore.Solidity.Source.CallResult.returned state _ =>
      Except.ok state
  | _ => Except.error (executableFailure "storage struct clear")

def checkedStorageStructDeleteClears :
    Except TypeError Bool := do
  let state ← checkedStorageStructDeleteState
  checkedCallWordPairMatches 48
    Executable.Examples.storageStructSourceUnit
    "StorageStructDemo" "origin" state [] 0 0

def checkedStorageStructAbiGetterMatches :
    Except TypeError Bool := do
  let state ← checkedStorageStructFieldWriteState
  let calldata ←
    CheckedInput.functionCalldata
      Executable.Examples.storageStructSourceUnit
      "StorageStructDemo" "origin" []
  let result ←
    CheckedInput.callCalldata 48
      Executable.Examples.storageStructSourceUnit
      "StorageStructDemo" state calldata
  let tupleTy :=
    SolidCore.Solidity.Source.Ty.tuple
      [ SolidCore.Solidity.Source.Ty.uint256
      , SolidCore.Solidity.Source.Ty.uint256 ]
  let expected ←
    checkedAbiEncodeValues
      [tupleTy]
      [SolidCore.Solidity.Source.Value.tuple
        [ SolidCore.Solidity.Source.Value.word 11
        , SolidCore.Solidity.Source.Value.word 40 ]]
  Except.ok (result.success && result.output == expected)

def checkedSourceDataTypeSemanticsMatch :
    Except TypeError Bool := do
  let udvtRead ← checkedUdvtReadMatches
  let udvtGetter ← checkedUdvtPublicGetterMatches
  let udvtRoundtrip ← checkedUdvtRoundtripMatches
  let udvtWrapUnwrap ← checkedUserValueWrapUnwrapMatches
  let udvtAbiGetter ← checkedUdvtAbiGetterMatches
  let udvtAbiEcho ← checkedUdvtAbiEchoMatches
  let udvtEvent ← checkedUdvtEventTopicMatches
  let udvtError ← checkedUdvtErrorSelectorMatches
  let enumGetter ← checkedEnumPublicGetterMatches
  let enumRead ← checkedEnumReadAsUintMatches
  let enumMinMax ← checkedEnumTypeMinMaxMatches
  let enumInRange ← checkedEnumConversionInRangeMatches
  let enumOutOfRange ← checkedEnumConversionOutOfRangePanics
  let enumMemberFixture ← checkedEnumMemberFixtureMatches
  let enumMinMaxFixture ← checkedEnumMinMaxFixtureMatches
  let enumLiteralFixture ← checkedEnumLiteralConversionFixtureMatches
  let enumTypedOutOfRangeFixture ←
    checkedEnumTypedOutOfRangeConversionFixturePanics
  let enumToUintFixture ← checkedEnumToUintConversionFixtureMatches
  let enumAbiEcho ← checkedEnumAbiEchoUsesUint8Selector
  let enumEvent ← checkedEnumEventTopicMatches
  let enumError ← checkedEnumErrorSelectorMatches
  let structConstructor ← checkedStructNamedConstructorFieldSumMatches
  let structFieldAccess ← checkedStructConstructorFieldAccessMatches
  let structAssign ← checkedStructFieldAssignmentMatches
  let structStorageAssign ← checkedStructStorageFieldAssignmentMatches
  let structAbiEcho ← checkedStructAbiEchoMatches
  let structEvent ← checkedStructEventTopicMatches
  let structError ← checkedStructErrorSelectorMatches
  let storageStructSum ← checkedStorageStructSumMatches
  let storageStructWrite ← checkedStorageStructFieldWriteMatches
  let storageStructAliasWrite ← checkedStorageStructAliasFieldWriteMatches
  let storageStructAliasRead ← checkedStorageStructAliasReadMatches
  let storageStructInternalWrite ←
    checkedStorageStructInternalParamFieldWriteMatches
  let storageStructInternalAliasWrite ←
    checkedStorageStructInternalParamAliasFieldWriteMatches
  let storageStructInternalRead ←
    checkedStorageStructInternalParamReadMatches
  let storageStructGetter ← checkedStorageStructPublicGetterMatches
  let storageStructDelete ← checkedStorageStructDeleteClears
  let storageStructAbiGetter ← checkedStorageStructAbiGetterMatches
  Except.ok
    (checkedDataTypeSourceUnitsAccepted &&
      checkedStorageStructSourceUnitAccepted &&
      checkedBadUserValueUnwrapRejected &&
      udvtRead && udvtGetter && udvtRoundtrip && udvtWrapUnwrap &&
      udvtAbiGetter && udvtAbiEcho && udvtEvent && udvtError &&
      checkedEnumSourceDisciplineAccepted &&
      checkedEnumSourceDisciplineRejected &&
      enumGetter && enumRead && enumMinMax && enumInRange &&
      enumMemberFixture && enumMinMaxFixture && enumLiteralFixture &&
      enumTypedOutOfRangeFixture && enumToUintFixture &&
      enumOutOfRange && enumAbiEcho && enumEvent && enumError &&
      checkedStructConstructorInvalidSourcesRejected &&
      checkedRecursiveStructTypeDisciplineAccepted &&
      checkedRecursiveStructTypeDisciplineRejected &&
      checkedStructStorageFieldAssignmentViewRejected &&
      structConstructor && structFieldAccess && structAssign &&
      structStorageAssign && structAbiEcho && structEvent && structError &&
      storageStructSum && storageStructWrite &&
      storageStructAliasWrite && storageStructAliasRead &&
      storageStructInternalWrite && storageStructInternalAliasWrite &&
      storageStructInternalRead && storageStructGetter &&
      storageStructDelete && storageStructAbiGetter)

def checkedStructStoragePathSourceUnitAccepted : Bool :=
  Result.isOk
    (TypecheckedInput.checkedSourceUnit
      Executable.Examples.structStoragePathSourceUnit)

def checkedStructStoragePathWord (value : Word) : CoreValue :=
  SolidCore.Solidity.Source.Value.word value

def checkedStructStoragePathCallState (fuel : Nat)
    (functionName : Name) (args : List CoreValue) :
    Except TypeError CoreState := do
  let result ←
    CheckedInput.callContract fuel
      Executable.Examples.structStoragePathSourceUnit
      "StructStoragePath"
      (SolidCore.Solidity.Source.CallTarget.name functionName)
      Executable.Examples.structStoragePathInitialState args
  match result with
  | SolidCore.Solidity.Source.CallResult.returned state _ =>
      Except.ok state
  | _ =>
      Except.error
        (executableFailure "struct storage path call")

def checkedStructStoragePathCountAddMatches :
    Except TypeError Bool := do
  let state ←
    checkedStructStoragePathCallState 64 "addCount"
      [checkedStructStoragePathWord 7, checkedStructStoragePathWord 5]
  Except.ok
    (SolidCore.Solidity.Source.wordEq
      (state.loadSlot
        Executable.Examples.structStoragePathEntrySlot) 15)

def checkedStructStoragePathValueAddMatches :
    Except TypeError Bool := do
  let state ←
    checkedStructStoragePathCallState 64 "addValue"
      [ checkedStructStoragePathWord 7
      , checkedStructStoragePathWord 1
      , checkedStructStoragePathWord 6 ]
  Except.ok
    (SolidCore.Solidity.Source.wordEq
      (state.loadSlot
        (Executable.Examples.structStoragePathValueSlot 1)) 15 &&
      SolidCore.Solidity.Source.wordEq
        (state.loadSlot
          Executable.Examples.structStoragePathValuesSlot) 2)

def checkedStructStoragePathValueClearMatches :
    Except TypeError Bool := do
  let state ←
    checkedStructStoragePathCallState 64 "clearValue"
      [checkedStructStoragePathWord 7, checkedStructStoragePathWord 1]
  Except.ok
    (SolidCore.Solidity.Source.wordEq
      (state.loadSlot
        (Executable.Examples.structStoragePathValueSlot 1)) 0 &&
      SolidCore.Solidity.Source.wordEq
        (state.loadSlot
          Executable.Examples.structStoragePathValuesSlot) 2)

def checkedStructStoragePathDirectArrayPushMatches :
    Except TypeError Bool := do
  let state ←
    checkedStructStoragePathCallState 80 "directPathArrayPush"
      [checkedStructStoragePathWord 7, checkedStructStoragePathWord 16]
  Except.ok
    (SolidCore.Solidity.Source.wordEq
      (state.loadSlot
        Executable.Examples.structStoragePathValuesSlot) 3 &&
      SolidCore.Solidity.Source.wordEq
        (state.loadSlot
          (Executable.Examples.structStoragePathValueSlot 2)) 16)

def checkedStructStoragePathDirectArrayPushAssignMatches :
    Except TypeError Bool := do
  let state ←
    checkedStructStoragePathCallState 80 "directPathArrayPushAssign"
      [checkedStructStoragePathWord 7, checkedStructStoragePathWord 17]
  Except.ok
    (SolidCore.Solidity.Source.wordEq
      (state.loadSlot
        Executable.Examples.structStoragePathValuesSlot) 3 &&
      SolidCore.Solidity.Source.wordEq
        (state.loadSlot
          (Executable.Examples.structStoragePathValueSlot 2)) 17)

def checkedStructStoragePathDirectArrayPopMatches :
    Except TypeError Bool := do
  let state ←
    checkedStructStoragePathCallState 80 "directPathArrayPop"
      [checkedStructStoragePathWord 7]
  Except.ok
    (SolidCore.Solidity.Source.wordEq
      (state.loadSlot
        Executable.Examples.structStoragePathValuesSlot) 1 &&
      SolidCore.Solidity.Source.wordEq
        (state.loadSlot
          (Executable.Examples.structStoragePathValueSlot 1)) 0)

def checkedStructStoragePathDirectBlobPushMatches :
    Except TypeError Bool := do
  let state ←
    checkedStructStoragePathCallState 80 "directPathBlobPush"
      [checkedStructStoragePathWord 7, checkedStructStoragePathWord 18]
  Except.ok
    (Executable.Examples.structStoragePathBlobBytesMatch
      state [30, 40, 18])

def checkedStructStoragePathDirectBlobPushAssignMatches :
    Except TypeError Bool := do
  let state ←
    checkedStructStoragePathCallState 80 "directPathBlobPushAssign"
      [checkedStructStoragePathWord 7, checkedStructStoragePathWord 19]
  Except.ok
    (Executable.Examples.structStoragePathBlobBytesMatch
      state [30, 40, 19])

def checkedStructStoragePathDirectBlobPopMatches :
    Except TypeError Bool := do
  let state ←
    checkedStructStoragePathCallState 80 "directPathBlobPop"
      [checkedStructStoragePathWord 7]
  Except.ok
    (Executable.Examples.structStoragePathBlobBytesMatch state [30])

def checkedStructStoragePathAliasCountAddMatches :
    Except TypeError Bool := do
  let state ←
    checkedStructStoragePathCallState 64 "aliasCount"
      [checkedStructStoragePathWord 7, checkedStructStoragePathWord 3]
  Except.ok
    (SolidCore.Solidity.Source.wordEq
      (state.loadSlot
        Executable.Examples.structStoragePathEntrySlot) 13)

def checkedStructStoragePathAliasValueAddMatches :
    Except TypeError Bool := do
  let state ←
    checkedStructStoragePathCallState 64 "aliasValue"
      [ checkedStructStoragePathWord 7
      , checkedStructStoragePathWord 1
      , checkedStructStoragePathWord 4 ]
  Except.ok
    (SolidCore.Solidity.Source.wordEq
      (state.loadSlot
        (Executable.Examples.structStoragePathValueSlot 1)) 13)

def checkedStructStoragePathAliasArrayPushMatches :
    Except TypeError Bool := do
  let state ←
    checkedStructStoragePathCallState 80 "aliasArrayPush"
      [checkedStructStoragePathWord 7, checkedStructStoragePathWord 6]
  Except.ok
    (SolidCore.Solidity.Source.wordEq
      (state.loadSlot
        Executable.Examples.structStoragePathValuesSlot) 3 &&
      SolidCore.Solidity.Source.wordEq
        (state.loadSlot
          (Executable.Examples.structStoragePathValueSlot 2)) 6)

def checkedStructStoragePathAliasArrayPushAssignMatches :
    Except TypeError Bool := do
  let state ←
    checkedStructStoragePathCallState 80 "aliasArrayPushAssign"
      [checkedStructStoragePathWord 7, checkedStructStoragePathWord 8]
  Except.ok
    (SolidCore.Solidity.Source.wordEq
      (state.loadSlot
        Executable.Examples.structStoragePathValuesSlot) 3 &&
      SolidCore.Solidity.Source.wordEq
        (state.loadSlot
          (Executable.Examples.structStoragePathValueSlot 2)) 8)

def checkedStructStoragePathAliasArrayPopMatches :
    Except TypeError Bool := do
  let state ←
    checkedStructStoragePathCallState 80 "aliasArrayPop"
      [checkedStructStoragePathWord 7]
  Except.ok
    (SolidCore.Solidity.Source.wordEq
      (state.loadSlot
        Executable.Examples.structStoragePathValuesSlot) 1 &&
      SolidCore.Solidity.Source.wordEq
        (state.loadSlot
          (Executable.Examples.structStoragePathValueSlot 1)) 0)

def checkedStructStoragePathAliasBlobPushMatches :
    Except TypeError Bool := do
  let state ←
    checkedStructStoragePathCallState 80 "aliasBlobPush"
      [checkedStructStoragePathWord 7, checkedStructStoragePathWord 5]
  Except.ok
    (Executable.Examples.structStoragePathBlobBytesMatch state [30, 40, 5])

def checkedStructStoragePathAliasBlobPushAssignMatches :
    Except TypeError Bool := do
  let state ←
    checkedStructStoragePathCallState 80 "aliasBlobPushAssign"
      [checkedStructStoragePathWord 7, checkedStructStoragePathWord 20]
  Except.ok
    (Executable.Examples.structStoragePathBlobBytesMatch
      state [30, 40, 20])

def checkedStructStoragePathAliasBlobPopMatches :
    Except TypeError Bool := do
  let state ←
    checkedStructStoragePathCallState 80 "aliasBlobPop"
      [checkedStructStoragePathWord 7]
  Except.ok
    (Executable.Examples.structStoragePathBlobBytesMatch state [30])

def checkedStructStoragePathAliasScoreSetMatches :
    Except TypeError Bool := do
  let state ←
    checkedStructStoragePathCallState 96 "aliasScoreSet"
      [ checkedStructStoragePathWord 7
      , checkedStructStoragePathWord 21
      , checkedStructStoragePathWord 55 ]
  Except.ok
    (SolidCore.Solidity.Source.wordEq
      (state.loadSlot
        (Executable.Examples.structStoragePathScoreSlot 21)) 55)

def checkedStructStoragePathInternalArrayPushMatches :
    Except TypeError Bool := do
  let state ←
    checkedStructStoragePathCallState 96 "internalPathArrayPush"
      [checkedStructStoragePathWord 7, checkedStructStoragePathWord 12]
  Except.ok
    (SolidCore.Solidity.Source.wordEq
      (state.loadSlot
        Executable.Examples.structStoragePathValuesSlot) 3 &&
      SolidCore.Solidity.Source.wordEq
        (state.loadSlot
          (Executable.Examples.structStoragePathValueSlot 2)) 12)

def checkedStructStoragePathInternalBlobPushMatches :
    Except TypeError Bool := do
  let state ←
    checkedStructStoragePathCallState 96 "internalPathBlobPush"
      [checkedStructStoragePathWord 7, checkedStructStoragePathWord 13]
  Except.ok
    (Executable.Examples.structStoragePathBlobBytesMatch
      state [30, 40, 13])

def checkedStructStoragePathInternalScoreSetMatches :
    Except TypeError Bool := do
  let state ←
    checkedStructStoragePathCallState 96 "internalPathScoreSet"
      [ checkedStructStoragePathWord 7
      , checkedStructStoragePathWord 22
      , checkedStructStoragePathWord 66 ]
  Except.ok
    (SolidCore.Solidity.Source.wordEq
      (state.loadSlot
        (Executable.Examples.structStoragePathScoreSlot 22)) 66)

def checkedStructStoragePathModifierArrayPushMatches :
    Except TypeError Bool := do
  let state ←
    checkedStructStoragePathCallState 96 "modifierPathArrayPush"
      [checkedStructStoragePathWord 7, checkedStructStoragePathWord 14]
  Except.ok
    (SolidCore.Solidity.Source.wordEq
      (state.loadSlot
        Executable.Examples.structStoragePathValuesSlot) 3 &&
      SolidCore.Solidity.Source.wordEq
        (state.loadSlot
          (Executable.Examples.structStoragePathValueSlot 2)) 14)

def checkedStructStoragePathModifierBlobPushMatches :
    Except TypeError Bool := do
  let state ←
    checkedStructStoragePathCallState 96 "modifierPathBlobPush"
      [checkedStructStoragePathWord 7, checkedStructStoragePathWord 15]
  Except.ok
    (Executable.Examples.structStoragePathBlobBytesMatch
      state [30, 40, 15])

def checkedStructStoragePathModifierScoreSetMatches :
    Except TypeError Bool := do
  let state ←
    checkedStructStoragePathCallState 96 "modifierPathScoreSet"
      [ checkedStructStoragePathWord 7
      , checkedStructStoragePathWord 23
      , checkedStructStoragePathWord 77 ]
  Except.ok
    (SolidCore.Solidity.Source.wordEq
      (state.loadSlot
        (Executable.Examples.structStoragePathScoreSlot 23)) 77)

def checkedOwnCallState (fuel : Nat) (decl : SourceContractDecl)
    (functionName : Name) (state : CoreState)
    (args : List CoreValue) : Except TypeError CoreState := do
  let result ←
    CheckedInput.ownCall fuel decl
      (SolidCore.Solidity.Source.CallTarget.name functionName)
      state args
  match result with
  | SolidCore.Solidity.Source.CallResult.returned state _ =>
      Except.ok state
  | _ =>
      Except.error (executableFailure "own contract call")

def checkedOwnCallWordMatches (fuel : Nat)
    (decl : SourceContractDecl) (functionName : Name)
    (state : CoreState) (args : List CoreValue)
    (expected : Word) : Except TypeError Bool := do
  let result ←
    CheckedInput.ownCall fuel decl
      (SolidCore.Solidity.Source.CallTarget.name functionName)
      state args
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _
      [SolidCore.Solidity.Source.Value.word value] =>
      Except.ok (SolidCore.Solidity.Source.wordEq value expected)
  | _ => Except.ok false

def checkedNestedStoragePathContractsAccepted : Bool :=
  Result.isOk
      (TypecheckedInput.checkedSourceUnit
        Executable.Examples.nestedStoragePathContract) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit
        Executable.Examples.nestedStoragePathCompoundContract) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit
        Executable.Examples.nestedBytesStoragePathContract)

def checkedNestedStoragePathWord (value : Word) : CoreValue :=
  SolidCore.Solidity.Source.Value.word value

def checkedNestedStoragePathInnerSlot : Word :=
  SolidCore.Solidity.Source.dynamicArrayLayoutStorageSlot
    0 0
    (SolidCore.Solidity.Source.StorageLayout.dynamicArray
      (SolidCore.Solidity.Source.StorageLayout.scalar
        SolidCore.Solidity.Source.Ty.uint256))

def checkedNestedStoragePathMatrixSetMatches :
    Except TypeError Bool := do
  let state ←
    checkedOwnCallState 64
      Executable.Examples.nestedStoragePathContract
      "setMatrixCell"
      Executable.Examples.nestedStoragePathMatrixInitialState
      [ checkedNestedStoragePathWord 0
      , checkedNestedStoragePathWord 1
      , checkedNestedStoragePathWord 77 ]
  let read ←
    checkedOwnCallWordMatches 64
      Executable.Examples.nestedStoragePathContract
      "readMatrixCell" state
      [ checkedNestedStoragePathWord 0
      , checkedNestedStoragePathWord 1 ] 77
  Except.ok
    (read &&
      SolidCore.Solidity.Source.wordEq (state.loadSlot 0) 1 &&
      SolidCore.Solidity.Source.wordEq
        (state.loadSlot checkedNestedStoragePathInnerSlot) 2 &&
      SolidCore.Solidity.Source.wordEq
        (state.loadSlot
          (SolidCore.Solidity.Source.dynamicArrayStorageSlot
            checkedNestedStoragePathInnerSlot 1)) 77)

def checkedNestedStoragePathMatrixClearMatches :
    Except TypeError Bool := do
  let state ←
    checkedOwnCallState 64
      Executable.Examples.nestedStoragePathContract
      "clearMatrixCell"
      Executable.Examples.nestedStoragePathMatrixInitialState
      [ checkedNestedStoragePathWord 0
      , checkedNestedStoragePathWord 1 ]
  Except.ok
    (SolidCore.Solidity.Source.wordEq (state.loadSlot 0) 1 &&
      SolidCore.Solidity.Source.wordEq
        (state.loadSlot checkedNestedStoragePathInnerSlot) 2 &&
      SolidCore.Solidity.Source.wordEq
        (state.loadSlot
          (SolidCore.Solidity.Source.dynamicArrayStorageSlot
            checkedNestedStoragePathInnerSlot 0)) 11 &&
      SolidCore.Solidity.Source.wordEq
        (state.loadSlot
          (SolidCore.Solidity.Source.dynamicArrayStorageSlot
            checkedNestedStoragePathInnerSlot 1)) 0)

def checkedNestedStoragePathMappingSetMatches :
    Except TypeError Bool := do
  let state ←
    checkedOwnCallState 64
      Executable.Examples.nestedStoragePathContract
      "setNested"
      SolidCore.Solidity.Source.State.empty
      [ checkedNestedStoragePathWord 3
      , checkedNestedStoragePathWord 4
      , checkedNestedStoragePathWord 55 ]
  let read ←
    checkedOwnCallWordMatches 64
      Executable.Examples.nestedStoragePathContract
      "readNested" state
      [ checkedNestedStoragePathWord 3
      , checkedNestedStoragePathWord 4 ] 55
  Except.ok
    (read &&
      SolidCore.Solidity.Source.wordEq
        (state.loadSlot
          Executable.Examples.nestedStoragePathMappingSlot) 55)

def checkedNestedStoragePathMappingClearMatches :
    Except TypeError Bool := do
  let state ←
    checkedOwnCallState 64
      Executable.Examples.nestedStoragePathContract
      "clearNested"
      Executable.Examples.nestedStoragePathMappingClearInitialState
      [ checkedNestedStoragePathWord 3
      , checkedNestedStoragePathWord 4 ]
  Except.ok
    (SolidCore.Solidity.Source.wordEq
      (state.loadSlot
        Executable.Examples.nestedStoragePathMappingSlot) 0)

def checkedNestedStoragePathCompoundMatrixAddMatches :
    Except TypeError Bool := do
  let state ←
    checkedOwnCallState 64
      Executable.Examples.nestedStoragePathCompoundContract
      "addMatrix"
      Executable.Examples.nestedStoragePathMatrixInitialState
      [ checkedNestedStoragePathWord 0
      , checkedNestedStoragePathWord 1
      , checkedNestedStoragePathWord 5 ]
  Except.ok
    (SolidCore.Solidity.Source.wordEq
      (state.loadSlot
        (SolidCore.Solidity.Source.dynamicArrayStorageSlot
          checkedNestedStoragePathInnerSlot 1)) 27)

def checkedNestedStoragePathCompoundMatrixIncMatches :
    Except TypeError Bool := do
  let result ←
    CheckedInput.ownCall 64
      Executable.Examples.nestedStoragePathCompoundContract
      (SolidCore.Solidity.Source.CallTarget.name "incMatrix")
      Executable.Examples.nestedStoragePathMatrixInitialState
      [ checkedNestedStoragePathWord 0
      , checkedNestedStoragePathWord 1 ]
  match result with
  | SolidCore.Solidity.Source.CallResult.returned state
      [SolidCore.Solidity.Source.Value.word value] =>
      Except.ok
        (SolidCore.Solidity.Source.wordEq value 23 &&
          SolidCore.Solidity.Source.wordEq
            (state.loadSlot
              (SolidCore.Solidity.Source.dynamicArrayStorageSlot
                checkedNestedStoragePathInnerSlot 1)) 23)
  | _ => Except.ok false

def checkedNestedStoragePathCompoundMappingAddMatches :
    Except TypeError Bool := do
  let state ←
    checkedOwnCallState 64
      Executable.Examples.nestedStoragePathCompoundContract
      "addNested"
      Executable.Examples.nestedStoragePathMappingClearInitialState
      [ checkedNestedStoragePathWord 3
      , checkedNestedStoragePathWord 4
      , checkedNestedStoragePathWord 7 ]
  Except.ok
    (SolidCore.Solidity.Source.wordEq
      (state.loadSlot
        Executable.Examples.nestedStoragePathMappingSlot) 62)

def checkedNestedBytesStoragePathElementSlot : Word :=
  SolidCore.Solidity.Source.dynamicArrayStorageSlot 0 0

def checkedNestedBytesStoragePathSetMatches :
    Except TypeError Bool := do
  let state ←
    checkedOwnCallState 64
      Executable.Examples.nestedBytesStoragePathContract
      "setByte"
      Executable.Examples.nestedBytesStoragePathInitialState
      [ checkedNestedStoragePathWord 0
      , checkedNestedStoragePathWord 1
      , checkedNestedStoragePathWord 90 ]
  let read ←
    checkedOwnCallWordMatches 64
      Executable.Examples.nestedBytesStoragePathContract
      "readByte" state
      [ checkedNestedStoragePathWord 0
      , checkedNestedStoragePathWord 1 ] 90
  let bytesMatch :=
    match SolidCore.Solidity.Source.State.loadStorageBytesAt
        state checkedNestedBytesStoragePathElementSlot with
    | Except.ok bytes => bytes == [10, 90]
    | Except.error _ => false
  Except.ok
    (read &&
      SolidCore.Solidity.Source.wordEq (state.loadSlot 0) 1 &&
      bytesMatch)

def checkedNestedBytesStoragePathClearMatches :
    Except TypeError Bool := do
  let state ←
    checkedOwnCallState 64
      Executable.Examples.nestedBytesStoragePathContract
      "clearByte"
      Executable.Examples.nestedBytesStoragePathInitialState
      [ checkedNestedStoragePathWord 0
      , checkedNestedStoragePathWord 1 ]
  let bytesMatch :=
    match SolidCore.Solidity.Source.State.loadStorageBytesAt
        state checkedNestedBytesStoragePathElementSlot with
    | Except.ok bytes => bytes == [10, 0]
    | Except.error _ => false
  Except.ok
    (SolidCore.Solidity.Source.wordEq (state.loadSlot 0) 1 &&
      bytesMatch)

def checkedAggregateStorageSlotSourceUnitAccepted : Bool :=
  Result.isOk
    (TypecheckedInput.checkedSourceUnit
      Executable.Examples.aggregateStorageSlotSourceUnit)

def checkedAggregateStorageSlotFieldsMatch : Except TypeError Bool := do
  let contract ←
    CheckedInput.contract
      Executable.Examples.aggregateStorageSlotSourceUnit
      "AggregateStorageSlots"
  match contract.core.storageFields with
  | [origin, tail, fixeds, afterFixed] =>
      Except.ok
        (origin.name == "origin" &&
          SolidCore.Solidity.Source.wordEq origin.slot 0 &&
          tail.name == "tail" &&
          SolidCore.Solidity.Source.wordEq tail.slot 2 &&
          fixeds.name == "fixeds" &&
          SolidCore.Solidity.Source.wordEq fixeds.slot 3 &&
          afterFixed.name == "afterFixed" &&
          SolidCore.Solidity.Source.wordEq afterFixed.slot 6)
  | _ => Except.ok false

def checkedAggregateStorageSlotWriteMatches :
    Except TypeError Bool := do
  let result ←
    CheckedInput.callContract 96
      Executable.Examples.aggregateStorageSlotSourceUnit
      "AggregateStorageSlots"
      (SolidCore.Solidity.Source.CallTarget.name "writeAll")
      SolidCore.Solidity.Source.State.empty []
  match result with
  | SolidCore.Solidity.Source.CallResult.returned state
      [SolidCore.Solidity.Source.Value.word value] =>
      Except.ok
        (SolidCore.Solidity.Source.wordEq value 5 &&
          SolidCore.Solidity.Source.wordEq (state.loadSlot 0) 1 &&
          SolidCore.Solidity.Source.wordEq (state.loadSlot 1) 2 &&
          SolidCore.Solidity.Source.wordEq (state.loadSlot 2) 3 &&
          SolidCore.Solidity.Source.wordEq (state.loadSlot 5) 4 &&
          SolidCore.Solidity.Source.wordEq (state.loadSlot 6) 5)
  | _ => Except.ok false

def checkedPackedTopLevelStorageSourceUnitAccepted : Bool :=
  Result.isOk
    (TypecheckedInput.checkedSourceUnit
      Executable.Examples.packedTopLevelStorageSourceUnit)

def checkedPackedTopLevelStorageFieldsMatch :
    Except TypeError Bool := do
  let contract ←
    CheckedInput.contract
      Executable.Examples.packedTopLevelStorageSourceUnit
      "PackedTopLevelStorage"
  match contract.core.storageFields with
  | [a, b, c, s, d] =>
      Except.ok
        (a.name == "a" &&
          SolidCore.Solidity.Source.wordEq a.slot 0 &&
          a.packedOffset == 0 && a.packedBytes == 1 &&
          b.name == "b" &&
          SolidCore.Solidity.Source.wordEq b.slot 0 &&
          b.packedOffset == 1 && b.packedBytes == 2 &&
          c.name == "c" &&
          SolidCore.Solidity.Source.wordEq c.slot 0 &&
          c.packedOffset == 3 && c.packedBytes == 1 &&
          s.name == "s" &&
          SolidCore.Solidity.Source.wordEq s.slot 0 &&
          s.packedOffset == 4 && s.packedBytes == 1 &&
          s.packedSigned &&
          d.name == "d" &&
          SolidCore.Solidity.Source.wordEq d.slot 1 &&
          d.packedOffset == 0 &&
          d.packedBytes == SolidCore.Solidity.Source.wordBytes)
  | _ => Except.ok false

def checkedPackedTopLevelStorageState :
    Except TypeError SolidCore.Solidity.Source.State := do
  let result ←
    CheckedInput.callContract 96
      Executable.Examples.packedTopLevelStorageSourceUnit
      "PackedTopLevelStorage"
      (SolidCore.Solidity.Source.CallTarget.name "setAll")
      SolidCore.Solidity.Source.State.empty []
  match result with
  | SolidCore.Solidity.Source.CallResult.returned state
      [SolidCore.Solidity.Source.Value.word value] =>
      if SolidCore.Solidity.Source.wordEq value 9 then
        Except.ok state
      else
        Except.error (TypeError.unsupported "packed storage setAll")
  | _ => Except.error (TypeError.unsupported "packed storage setAll")

def checkedPackedTopLevelStorageSlotMatches :
    Except TypeError Bool := do
  let state ← checkedPackedTopLevelStorageState
  Except.ok
    (SolidCore.Solidity.Source.wordEq
      (state.loadSlot 0) 0xff01345612 &&
      SolidCore.Solidity.Source.wordEq (state.loadSlot 1) 9)

def checkedPackedTopLevelStorageGetterMatches :
    Except TypeError Bool := do
  let state ← checkedPackedTopLevelStorageState
  let aResult ←
    CheckedInput.callContract 32
      Executable.Examples.packedTopLevelStorageSourceUnit
      "PackedTopLevelStorage"
      (SolidCore.Solidity.Source.CallTarget.name "a") state []
  let bResult ←
    CheckedInput.callContract 32
      Executable.Examples.packedTopLevelStorageSourceUnit
      "PackedTopLevelStorage"
      (SolidCore.Solidity.Source.CallTarget.name "b") state []
  let cResult ←
    CheckedInput.callContract 32
      Executable.Examples.packedTopLevelStorageSourceUnit
      "PackedTopLevelStorage"
      (SolidCore.Solidity.Source.CallTarget.name "c") state []
  let sResult ←
    CheckedInput.callContract 32
      Executable.Examples.packedTopLevelStorageSourceUnit
      "PackedTopLevelStorage"
      (SolidCore.Solidity.Source.CallTarget.name "s") state []
  let dResult ←
    CheckedInput.callContract 32
      Executable.Examples.packedTopLevelStorageSourceUnit
      "PackedTopLevelStorage"
      (SolidCore.Solidity.Source.CallTarget.name "d") state []
  match aResult, bResult, cResult, sResult, dResult with
  | SolidCore.Solidity.Source.CallResult.returned _
      [SolidCore.Solidity.Source.Value.word a],
    SolidCore.Solidity.Source.CallResult.returned _
      [SolidCore.Solidity.Source.Value.word b],
    SolidCore.Solidity.Source.CallResult.returned _
      [SolidCore.Solidity.Source.Value.word c],
    SolidCore.Solidity.Source.CallResult.returned _
      [SolidCore.Solidity.Source.Value.int s],
    SolidCore.Solidity.Source.CallResult.returned _
      [SolidCore.Solidity.Source.Value.word d] =>
      Except.ok
        (SolidCore.Solidity.Source.wordEq a 0x12 &&
          SolidCore.Solidity.Source.wordEq b 0x3456 &&
          SolidCore.Solidity.Source.wordEq c 1 &&
          SolidCore.Solidity.Source.wordEq s
            (SolidCore.Solidity.Shared.signedToWord (-1)) &&
          SolidCore.Solidity.Source.wordEq d 9)
  | _, _, _, _, _ => Except.ok false

def checkedPackedStructAndArrayStorageSourceUnitAccepted : Bool :=
  Result.isOk
    (TypecheckedInput.checkedSourceUnit
      Executable.Examples.packedStructAndArrayStorageSourceUnit)

def checkedPackedStructAndArrayStorageFieldsMatch :
    Except TypeError Bool := do
  let contract ←
    CheckedInput.contract
      Executable.Examples.packedStructAndArrayStorageSourceUnit
      "PackedStructAndArrayStorage"
  match contract.core.storageFields with
  | [pair, tail, fixeds, afterFixed] =>
      let pairLayoutMatches :=
        match pair.layout? with
        | some (SolidCore.Solidity.Source.StorageLayout.struct
            [a, b, c, s, d]) =>
            Executable.Examples.packedUintLayoutMatches 0 1 a &&
              Executable.Examples.packedUintLayoutMatches 1 2 b &&
              Executable.Examples.packedBoolLayoutMatches 3 1 c &&
              Executable.Examples.packedIntLayoutMatches 4 1 s &&
              match d with
              | SolidCore.Solidity.Source.StorageLayout.packedScalar
                  0 32 false SolidCore.Solidity.Source.Ty.uint256 =>
                  true
              | _ => false
        | _ => false
      let fixedLayoutMatches :=
        match fixeds.layout? with
        | some
            (SolidCore.Solidity.Source.StorageLayout.fixedArray 4
              elementLayout) =>
            Executable.Examples.packedUintLayoutMatches 0 1 elementLayout
        | _ => false
      Except.ok
        (pair.name == "pair" &&
          SolidCore.Solidity.Source.wordEq pair.slot 0 &&
          pairLayoutMatches &&
          tail.name == "tail" &&
          SolidCore.Solidity.Source.wordEq tail.slot 2 &&
          fixeds.name == "fixeds" &&
          SolidCore.Solidity.Source.wordEq fixeds.slot 3 &&
          fixedLayoutMatches &&
          afterFixed.name == "afterFixed" &&
          SolidCore.Solidity.Source.wordEq afterFixed.slot 4)
  | _ => Except.ok false

def checkedPackedStructAndArrayStorageState :
    Except TypeError SolidCore.Solidity.Source.State := do
  let result ←
    CheckedInput.callContract 128
      Executable.Examples.packedStructAndArrayStorageSourceUnit
      "PackedStructAndArrayStorage"
      (SolidCore.Solidity.Source.CallTarget.name "setAll")
      SolidCore.Solidity.Source.State.empty []
  match result with
  | SolidCore.Solidity.Source.CallResult.returned state
      [SolidCore.Solidity.Source.Value.word value] =>
      if SolidCore.Solidity.Source.wordEq value 11 then
        Except.ok state
      else
        Except.error
          (TypeError.unsupported "packed struct/array storage setAll")
  | _ =>
      Except.error
        (TypeError.unsupported "packed struct/array storage setAll")

def checkedPackedStructAndArrayStorageSlotMatches :
    Except TypeError Bool := do
  let state ← checkedPackedStructAndArrayStorageState
  Except.ok
    (SolidCore.Solidity.Source.wordEq
      (state.loadSlot 0) 0xff01345612 &&
      SolidCore.Solidity.Source.wordEq (state.loadSlot 1) 9 &&
      SolidCore.Solidity.Source.wordEq (state.loadSlot 2) 10 &&
      SolidCore.Solidity.Source.wordEq
        (state.loadSlot 3) 0xddccbbaa &&
      SolidCore.Solidity.Source.wordEq (state.loadSlot 4) 11)

def checkedPackedStructAndArrayStorageReadMatches :
    Except TypeError Bool := do
  let state ← checkedPackedStructAndArrayStorageState
  let aResult ←
    CheckedInput.callContract 32
      Executable.Examples.packedStructAndArrayStorageSourceUnit
      "PackedStructAndArrayStorage"
      (SolidCore.Solidity.Source.CallTarget.name "readA") state []
  let bResult ←
    CheckedInput.callContract 32
      Executable.Examples.packedStructAndArrayStorageSourceUnit
      "PackedStructAndArrayStorage"
      (SolidCore.Solidity.Source.CallTarget.name "readB") state []
  let cResult ←
    CheckedInput.callContract 32
      Executable.Examples.packedStructAndArrayStorageSourceUnit
      "PackedStructAndArrayStorage"
      (SolidCore.Solidity.Source.CallTarget.name "readC") state []
  let sResult ←
    CheckedInput.callContract 32
      Executable.Examples.packedStructAndArrayStorageSourceUnit
      "PackedStructAndArrayStorage"
      (SolidCore.Solidity.Source.CallTarget.name "readS") state []
  let fixedResult ←
    CheckedInput.callContract 32
      Executable.Examples.packedStructAndArrayStorageSourceUnit
      "PackedStructAndArrayStorage"
      (SolidCore.Solidity.Source.CallTarget.name "readFixed2") state []
  match aResult, bResult, cResult, sResult, fixedResult with
  | SolidCore.Solidity.Source.CallResult.returned _
      [SolidCore.Solidity.Source.Value.word a],
    SolidCore.Solidity.Source.CallResult.returned _
      [SolidCore.Solidity.Source.Value.word b],
    SolidCore.Solidity.Source.CallResult.returned _
      [SolidCore.Solidity.Source.Value.word c],
    SolidCore.Solidity.Source.CallResult.returned _
      [SolidCore.Solidity.Source.Value.int s],
    SolidCore.Solidity.Source.CallResult.returned _
      [SolidCore.Solidity.Source.Value.word fixed] =>
      Except.ok
        (SolidCore.Solidity.Source.wordEq a 0x12 &&
          SolidCore.Solidity.Source.wordEq b 0x3456 &&
          SolidCore.Solidity.Source.wordEq c 1 &&
          SolidCore.Solidity.Source.wordEq s
            (SolidCore.Solidity.Shared.signedToWord (-1)) &&
          SolidCore.Solidity.Source.wordEq fixed 0xcc)
  | _, _, _, _, _ => Except.ok false

def checkedInternalFunctionPointerContractsAccepted : Bool :=
  Result.isOk
      (TypecheckedInput.checkedSourceUnit
        Executable.Examples.internalFunctionPointerAliasContract) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit
        Executable.Examples.internalFunctionPointerReassignContract) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit
        Executable.Examples.internalFunctionPointerAssignAfterDeclContract) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit
        Executable.Examples.internalFunctionPointerDeleteThenAssignContract) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit
        Executable.Examples.internalFunctionPointerUninitializedCallContract) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit
        Executable.Examples.internalFunctionPointerDeletedCallContract) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit
        Executable.Examples.internalFunctionPointerCopyContract) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit
        Executable.Examples.internalFunctionPointerParamContract)

def checkedInternalFunctionPointerWord (value : Word) : CoreValue :=
  SolidCore.Solidity.Source.Value.word value

def checkedOwnCallPanicMatches (fuel : Nat)
    (decl : SourceContractDecl) (functionName : Name)
    (state : CoreState) (args : List CoreValue)
    (expected : Word) : Except TypeError Bool := do
  let result ←
    CheckedInput.ownCall fuel decl
      (SolidCore.Solidity.Source.CallTarget.name functionName)
      state args
  match result with
  | SolidCore.Solidity.Source.CallResult.reverted _
      (SolidCore.Solidity.Source.RevertData.panic code) =>
      Except.ok (SolidCore.Solidity.Source.wordEq code expected)
  | _ => Except.ok false

def checkedInternalFunctionPointerAliasMatches :
    Except TypeError Bool :=
  checkedOwnCallWordMatches 48
    Executable.Examples.internalFunctionPointerAliasContract
    "run" SolidCore.Solidity.Source.State.empty
    [checkedInternalFunctionPointerWord 21] 42

def checkedInternalFunctionPointerReassignMatches :
    Except TypeError Bool :=
  checkedOwnCallWordMatches 64
    Executable.Examples.internalFunctionPointerReassignContract
    "run" SolidCore.Solidity.Source.State.empty
    [checkedInternalFunctionPointerWord 21] 63

def checkedInternalFunctionPointerAssignAfterDeclMatches :
    Except TypeError Bool :=
  checkedOwnCallWordMatches 64
    Executable.Examples.internalFunctionPointerAssignAfterDeclContract
    "run" SolidCore.Solidity.Source.State.empty
    [checkedInternalFunctionPointerWord 21] 42

def checkedInternalFunctionPointerDeleteThenAssignMatches :
    Except TypeError Bool :=
  checkedOwnCallWordMatches 64
    Executable.Examples.internalFunctionPointerDeleteThenAssignContract
    "run" SolidCore.Solidity.Source.State.empty
    [checkedInternalFunctionPointerWord 21] 63

def checkedInternalFunctionPointerUninitializedCallPanics :
    Except TypeError Bool :=
  checkedOwnCallPanicMatches 64
    Executable.Examples.internalFunctionPointerUninitializedCallContract
    "run" SolidCore.Solidity.Source.State.empty
    [checkedInternalFunctionPointerWord 21]
    internalFunctionPointerPanicCode

def checkedInternalFunctionPointerDeletedCallPanics :
    Except TypeError Bool :=
  checkedOwnCallPanicMatches 64
    Executable.Examples.internalFunctionPointerDeletedCallContract
    "run" SolidCore.Solidity.Source.State.empty
    [checkedInternalFunctionPointerWord 21]
    internalFunctionPointerPanicCode

def checkedInternalFunctionPointerCopyMatches :
    Except TypeError Bool :=
  checkedOwnCallWordMatches 96
    Executable.Examples.internalFunctionPointerCopyContract
    "run" SolidCore.Solidity.Source.State.empty
    [checkedInternalFunctionPointerWord 21] 105

def checkedInternalFunctionPointerParamMatches :
    Except TypeError Bool :=
  checkedOwnCallWordMatches 128
    Executable.Examples.internalFunctionPointerParamContract
    "run" SolidCore.Solidity.Source.State.empty
    [checkedInternalFunctionPointerWord 21] 42

def checkedInternalFunctionPointerParamDirectMatches :
    Except TypeError Bool :=
  checkedOwnCallWordMatches 128
    Executable.Examples.internalFunctionPointerParamContract
    "runDirect" SolidCore.Solidity.Source.State.empty
    [checkedInternalFunctionPointerWord 21] 42

def checkedInternalFunctionPointerParamUninitializedCallPanics :
    Except TypeError Bool :=
  checkedOwnCallPanicMatches 128
    Executable.Examples.internalFunctionPointerParamContract
    "runUnbound" SolidCore.Solidity.Source.State.empty
    [checkedInternalFunctionPointerWord 21]
    internalFunctionPointerPanicCode

def checkedInternalReturnEvaluationContractsAccepted : Bool :=
  Result.isOk
      (TypecheckedInput.checkedSourceUnit
        Executable.Examples.internalReturnSubexpressionContract) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit
        Executable.Examples.internalReturnRightSubexpressionContract) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit
        Executable.Examples.internalReturnShortCircuitContract)

def checkedInternalReturnSubexpressionMatches :
    Except TypeError Bool :=
  checkedOwnCallWordMatches 32
    Executable.Examples.internalReturnSubexpressionContract
    "run" SolidCore.Solidity.Source.State.empty [] 42

def checkedInternalReturnRightSubexpressionMatches :
    Except TypeError Bool := do
  let result ←
    CheckedInput.ownCall 48
      Executable.Examples.internalReturnRightSubexpressionContract
      (SolidCore.Solidity.Source.CallTarget.name "run")
      SolidCore.Solidity.Source.State.empty []
  match result with
  | SolidCore.Solidity.Source.CallResult.returned state
      [SolidCore.Solidity.Source.Value.word value] =>
      Except.ok
        (SolidCore.Solidity.Source.wordEq value 10 &&
          SolidCore.Solidity.Source.wordEq (state.loadSlot 0) 5)
  | _ => Except.ok false

def checkedInternalReturnShortCircuitMatches :
    Except TypeError Bool := do
  let andSkip ←
    CheckedInput.ownCall 64
      Executable.Examples.internalReturnShortCircuitContract
      (SolidCore.Solidity.Source.CallTarget.name "andSkip")
      SolidCore.Solidity.Source.State.empty []
  let orSkip ←
    CheckedInput.ownCall 64
      Executable.Examples.internalReturnShortCircuitContract
      (SolidCore.Solidity.Source.CallTarget.name "orSkip")
      SolidCore.Solidity.Source.State.empty []
  let andCall ←
    CheckedInput.ownCall 64
      Executable.Examples.internalReturnShortCircuitContract
      (SolidCore.Solidity.Source.CallTarget.name "andCall")
      SolidCore.Solidity.Source.State.empty []
  let orCall ←
    CheckedInput.ownCall 64
      Executable.Examples.internalReturnShortCircuitContract
      (SolidCore.Solidity.Source.CallTarget.name "orCall")
      SolidCore.Solidity.Source.State.empty []
  match andSkip, orSkip, andCall, orCall with
  | SolidCore.Solidity.Source.CallResult.returned andSkipState
      [SolidCore.Solidity.Source.Value.word andSkipValue],
    SolidCore.Solidity.Source.CallResult.returned orSkipState
      [SolidCore.Solidity.Source.Value.word orSkipValue],
    SolidCore.Solidity.Source.CallResult.returned andCallState
      [SolidCore.Solidity.Source.Value.word andCallValue],
    SolidCore.Solidity.Source.CallResult.returned orCallState
      [SolidCore.Solidity.Source.Value.word orCallValue] =>
      Except.ok
        (SolidCore.Solidity.Source.wordEq andSkipValue 0 &&
          SolidCore.Solidity.Source.wordEq
            (andSkipState.loadSlot 0) 0 &&
          SolidCore.Solidity.Source.wordEq orSkipValue 1 &&
          SolidCore.Solidity.Source.wordEq
            (orSkipState.loadSlot 0) 0 &&
          SolidCore.Solidity.Source.wordEq andCallValue 1 &&
          SolidCore.Solidity.Source.wordEq
            (andCallState.loadSlot 0) 1 &&
          SolidCore.Solidity.Source.wordEq orCallValue 1 &&
          SolidCore.Solidity.Source.wordEq
            (orCallState.loadSlot 0) 1)
  | _, _, _, _ => Except.ok false

def checkedControlFlowContractsAccepted : Bool :=
  Result.isOk
      (TypecheckedInput.checkedSourceUnit
        Executable.Examples.internalTernaryBranchCallContract) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit
        Executable.Examples.internalIfConditionCallContract) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit
        Executable.Examples.internalWhileConditionCallContract) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit
        Executable.Examples.internalForPostCallContract) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit
        Executable.Examples.loopBreakContinueContract) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit
        Executable.Examples.namedReturnContract) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit namedBareReturnSource)

def checkedPrimitiveStatementContract :
    Solidity.ContractDecl :=
  { name := "CheckedPrimitiveStatements"
    items :=
      [ ContractItem.function
          { name := some "ternarySkip"
            visibility := some Visibility.public_
            mutability := StateMutability.pure
            returns := [{ ty := Ty.uint 256 }]
            body := some Executable.Examples.ternarySkipsRejectedBranch }
      , ContractItem.function
          { name := some "doWhileOnce"
            visibility := some Visibility.public_
            mutability := StateMutability.pure
            returns := [{ ty := Ty.uint 256 }]
            body := some Executable.Examples.doWhileRunsBeforeCondition }
      , ContractItem.function
          { name := some "deleteLocal"
            visibility := some Visibility.public_
            mutability := StateMutability.pure
            returns := [{ ty := Ty.uint 256 }]
            body := some Executable.Examples.deleteLocalStatement }
      , ContractItem.function
          { name := some "incrementStatement"
            visibility := some Visibility.public_
            mutability := StateMutability.pure
            returns := [{ ty := Ty.uint 256 }]
            body := some Executable.Examples.incrementStatement }
      , ContractItem.function
          { name := some "expressionFailure"
            visibility := some Visibility.public_
            mutability := StateMutability.pure
            body := some Executable.Examples.expressionStatementFailure }
      , ContractItem.function
          { name := some "assertFailure"
            visibility := some Visibility.public_
            mutability := StateMutability.pure
            body := some Executable.Examples.assertFailureStatement }
      , ContractItem.function
          { name := some "requireString"
            visibility := some Visibility.public_
            mutability := StateMutability.pure
            body := some Executable.Examples.requireFailureStatement }
      , ContractItem.function
          { name := some "revertString"
            visibility := some Visibility.public_
            mutability := StateMutability.pure
            body := some Executable.Examples.revertStringStatement } ] }

def checkedPrimitiveStatementContractAccepted : Bool :=
  Result.isOk
    (TypecheckedInput.checkedSourceUnit checkedPrimitiveStatementContract)

def checkedTernarySkipsRejectedBranchMatches :
    Except TypeError Bool :=
  checkedOwnCallWordMatches 16 checkedPrimitiveStatementContract
    "ternarySkip" SolidCore.Solidity.Source.State.empty [] 7

def checkedDoWhileRunsBeforeConditionMatches :
    Except TypeError Bool :=
  checkedOwnCallWordMatches 32 checkedPrimitiveStatementContract
    "doWhileOnce" SolidCore.Solidity.Source.State.empty [] 1

def checkedDeleteLocalStatementMatches :
    Except TypeError Bool :=
  checkedOwnCallWordMatches 16 checkedPrimitiveStatementContract
    "deleteLocal" SolidCore.Solidity.Source.State.empty [] 0

def checkedIncrementStatementMatches :
    Except TypeError Bool :=
  checkedOwnCallWordMatches 16 checkedPrimitiveStatementContract
    "incrementStatement" SolidCore.Solidity.Source.State.empty [] 3

def checkedExpressionStatementFailurePanics :
    Except TypeError Bool :=
  checkedOwnCallPanicMatches 16 checkedPrimitiveStatementContract
    "expressionFailure" SolidCore.Solidity.Source.State.empty [] 0x12

def checkedAssertFailurePanics :
    Except TypeError Bool :=
  checkedOwnCallPanicMatches 16 checkedPrimitiveStatementContract
    "assertFailure" SolidCore.Solidity.Source.State.empty [] 0x01

def checkedRequireFailureStringMatches :
    Except TypeError Bool := do
  let result ←
    CheckedInput.ownCall 16 checkedPrimitiveStatementContract
      (SolidCore.Solidity.Source.CallTarget.name "requireString")
      SolidCore.Solidity.Source.State.empty []
  match result with
  | SolidCore.Solidity.Source.CallResult.reverted _
      (SolidCore.Solidity.Source.RevertData.error reason) =>
      Except.ok (reason == "Nope")
  | _ => Except.ok false

def checkedRevertStringMatches :
    Except TypeError Bool := do
  let result ←
    CheckedInput.ownCall 16 checkedPrimitiveStatementContract
      (SolidCore.Solidity.Source.CallTarget.name "revertString")
      SolidCore.Solidity.Source.State.empty []
  match result with
  | SolidCore.Solidity.Source.CallResult.reverted _
      (SolidCore.Solidity.Source.RevertData.error reason) =>
      Except.ok (reason == "Nope")
  | _ => Except.ok false

def checkedInternalTernaryBranchCallMatches :
    Except TypeError Bool := do
  let runReturnThen ←
    CheckedInput.ownCall 64
      Executable.Examples.internalTernaryBranchCallContract
      (SolidCore.Solidity.Source.CallTarget.name "runReturnThen")
      SolidCore.Solidity.Source.State.empty []
  let runReturnElse ←
    CheckedInput.ownCall 64
      Executable.Examples.internalTernaryBranchCallContract
      (SolidCore.Solidity.Source.CallTarget.name "runReturnElse")
      SolidCore.Solidity.Source.State.empty []
  let runVarBothFalse ←
    CheckedInput.ownCall 64
      Executable.Examples.internalTernaryBranchCallContract
      (SolidCore.Solidity.Source.CallTarget.name "runVarBothFalse")
      SolidCore.Solidity.Source.State.empty []
  let runAssignBothTrue ←
    CheckedInput.ownCall 64
      Executable.Examples.internalTernaryBranchCallContract
      (SolidCore.Solidity.Source.CallTarget.name "runAssignBothTrue")
      SolidCore.Solidity.Source.State.empty []
  match runReturnThen, runReturnElse, runVarBothFalse,
      runAssignBothTrue with
  | SolidCore.Solidity.Source.CallResult.returned runReturnThenState
      [SolidCore.Solidity.Source.Value.word runReturnThenValue],
    SolidCore.Solidity.Source.CallResult.returned runReturnElseState
      [SolidCore.Solidity.Source.Value.word runReturnElseValue],
    SolidCore.Solidity.Source.CallResult.returned runVarBothFalseState
      [SolidCore.Solidity.Source.Value.word runVarBothFalseValue],
    SolidCore.Solidity.Source.CallResult.returned runAssignBothTrueState
      [SolidCore.Solidity.Source.Value.word runAssignBothTrueValue] =>
      Except.ok
        (SolidCore.Solidity.Source.wordEq runReturnThenValue 21 &&
          SolidCore.Solidity.Source.wordEq
            (runReturnThenState.loadSlot 0) 21 &&
          SolidCore.Solidity.Source.wordEq runReturnElseValue 22 &&
          SolidCore.Solidity.Source.wordEq
            (runReturnElseState.loadSlot 0) 22 &&
          SolidCore.Solidity.Source.wordEq runVarBothFalseValue 22 &&
          SolidCore.Solidity.Source.wordEq
            (runVarBothFalseState.loadSlot 0) 22 &&
          SolidCore.Solidity.Source.wordEq runAssignBothTrueValue 21 &&
          SolidCore.Solidity.Source.wordEq
            (runAssignBothTrueState.loadSlot 0) 21)
  | _, _, _, _ => Except.ok false

def checkedInternalIfConditionCallMatches :
    Except TypeError Bool := do
  let runTrue ←
    CheckedInput.ownCall 64
      Executable.Examples.internalIfConditionCallContract
      (SolidCore.Solidity.Source.CallTarget.name "runTrue")
      SolidCore.Solidity.Source.State.empty []
  let runFalse ←
    CheckedInput.ownCall 64
      Executable.Examples.internalIfConditionCallContract
      (SolidCore.Solidity.Source.CallTarget.name "runFalse")
      SolidCore.Solidity.Source.State.empty []
  match runTrue, runFalse with
  | SolidCore.Solidity.Source.CallResult.returned runTrueState
      [SolidCore.Solidity.Source.Value.word runTrueValue],
    SolidCore.Solidity.Source.CallResult.returned runFalseState
      [SolidCore.Solidity.Source.Value.word runFalseValue] =>
      Except.ok
        (SolidCore.Solidity.Source.wordEq runTrueValue 2 &&
          SolidCore.Solidity.Source.wordEq
            (runTrueState.loadSlot 0) 1 &&
          SolidCore.Solidity.Source.wordEq runFalseValue 3 &&
          SolidCore.Solidity.Source.wordEq
            (runFalseState.loadSlot 0) 1)
  | _, _ => Except.ok false

def checkedInternalWhileConditionCallMatches :
    Except TypeError Bool := do
  let result ←
    CheckedInput.ownCall 128
      Executable.Examples.internalWhileConditionCallContract
      (SolidCore.Solidity.Source.CallTarget.name "run")
      SolidCore.Solidity.Source.State.empty []
  match result with
  | SolidCore.Solidity.Source.CallResult.returned state
      [SolidCore.Solidity.Source.Value.word value] =>
      Except.ok
        (SolidCore.Solidity.Source.wordEq value 3 &&
          SolidCore.Solidity.Source.wordEq (state.loadSlot 0) 3)
  | _ => Except.ok false

def checkedInternalForPostCallMatches :
    Except TypeError Bool := do
  let result ←
    CheckedInput.ownCall 128
      Executable.Examples.internalForPostCallContract
      (SolidCore.Solidity.Source.CallTarget.name "run")
      SolidCore.Solidity.Source.State.empty []
  match result with
  | SolidCore.Solidity.Source.CallResult.returned state
      [SolidCore.Solidity.Source.Value.word value] =>
      Except.ok
        (SolidCore.Solidity.Source.wordEq value 3 &&
          SolidCore.Solidity.Source.wordEq (state.loadSlot 0) 3)
  | _ => Except.ok false

def checkedLoopBreakContinueMatches : Except TypeError Bool := do
  let runBreak ←
    CheckedInput.ownCall 128
      Executable.Examples.loopBreakContinueContract
      (SolidCore.Solidity.Source.CallTarget.name "runBreak")
      SolidCore.Solidity.Source.State.empty []
  let runContinue ←
    CheckedInput.ownCall 128
      Executable.Examples.loopBreakContinueContract
      (SolidCore.Solidity.Source.CallTarget.name "runContinue")
      SolidCore.Solidity.Source.State.empty []
  match runBreak, runContinue with
  | SolidCore.Solidity.Source.CallResult.returned runBreakState
      [SolidCore.Solidity.Source.Value.word runBreakValue],
    SolidCore.Solidity.Source.CallResult.returned runContinueState
      [SolidCore.Solidity.Source.Value.word runContinueValue] =>
      Except.ok
        (SolidCore.Solidity.Source.wordEq runBreakValue 3 &&
          SolidCore.Solidity.Source.wordEq
            (runBreakState.loadSlot 0) 3 &&
          SolidCore.Solidity.Source.wordEq runContinueValue 9 &&
          SolidCore.Solidity.Source.wordEq
            (runContinueState.loadSlot 0) 5)
  | _, _ => Except.ok false

def checkedLoopBreakContinueSourceMatches : Except TypeError Bool := do
  let runBreak ←
    checkedCallWordMatches 128 loopBreakContinueSource
      "LoopBreakContinue" "runBreak"
      SolidCore.Solidity.Source.State.empty [] 3
  let runContinue ←
    checkedCallWordMatches 128 loopBreakContinueSource
      "LoopBreakContinue" "runContinue"
      SolidCore.Solidity.Source.State.empty [] 9
  Except.ok (runBreak && runContinue)

def checkedControlFlowSourceDisciplineRejected : Bool :=
  Result.isError (TypecheckedInput.checkedSourceUnit badIfSource) &&
    Result.isError (TypecheckedInput.checkedSourceUnit breakOutsideLoopSource) &&
    Result.isError (TypecheckedInput.checkedSourceUnit continueOutsideLoopSource) &&
    Result.isError (TypecheckedInput.checkedSourceUnit unnamedBareReturnSource)

def checkedNamedReturnMatches : Except TypeError Bool := do
  let stop ←
    CheckedInput.ownCall 32
      Executable.Examples.namedReturnContract
      (SolidCore.Solidity.Source.CallTarget.name "stop")
      SolidCore.Solidity.Source.State.empty []
  let runFallthrough ←
    CheckedInput.ownCall 32
      Executable.Examples.namedReturnContract
      (SolidCore.Solidity.Source.CallTarget.name "runFallthrough")
      SolidCore.Solidity.Source.State.empty []
  let runBare ←
    CheckedInput.ownCall 32
      Executable.Examples.namedReturnContract
      (SolidCore.Solidity.Source.CallTarget.name "runBare")
      SolidCore.Solidity.Source.State.empty []
  let runDefault ←
    CheckedInput.ownCall 32
      Executable.Examples.namedReturnContract
      (SolidCore.Solidity.Source.CallTarget.name "runDefault")
      SolidCore.Solidity.Source.State.empty []
  match stop, runFallthrough, runBare, runDefault with
  | SolidCore.Solidity.Source.CallResult.returned stopState [],
    SolidCore.Solidity.Source.CallResult.returned _
      [SolidCore.Solidity.Source.Value.word runFallthroughValue],
    SolidCore.Solidity.Source.CallResult.returned _
      [SolidCore.Solidity.Source.Value.word runBareValue],
    SolidCore.Solidity.Source.CallResult.returned _
      [SolidCore.Solidity.Source.Value.word runDefaultValue] =>
      Except.ok
        (SolidCore.Solidity.Source.wordEq
          (stopState.loadSlot 0) 1 &&
          SolidCore.Solidity.Source.wordEq runFallthroughValue 9 &&
          SolidCore.Solidity.Source.wordEq runBareValue 11 &&
          SolidCore.Solidity.Source.wordEq runDefaultValue 0)
  | _, _, _, _ => Except.ok false

def checkedNoReturnEffectReturnSourceAccepted : Bool :=
  Result.isOk
    (TypecheckedInput.checkedSourceUnit
      Executable.Examples.noReturnEffectReturnSourceUnit)

def checkedNoReturnEffectReturnMatches : Except TypeError Bool := do
  let requireTrue ←
    CheckedInput.callContract 64
      Executable.Examples.noReturnEffectReturnSourceUnit
      "NoReturnEffectReturn"
      (SolidCore.Solidity.Source.CallTarget.name "returnRequire")
      SolidCore.Solidity.Source.State.empty
      [SolidCore.Solidity.Source.Value.word 1]
  let requireFalse ←
    CheckedInput.callContract 64
      Executable.Examples.noReturnEffectReturnSourceUnit
      "NoReturnEffectReturn"
      (SolidCore.Solidity.Source.CallTarget.name "returnRequire")
      SolidCore.Solidity.Source.State.empty
      [SolidCore.Solidity.Source.Value.word 0]
  let revertResult ←
    CheckedInput.callContract 64
      Executable.Examples.noReturnEffectReturnSourceUnit
      "NoReturnEffectReturn"
      (SolidCore.Solidity.Source.CallTarget.name "returnRevert")
      SolidCore.Solidity.Source.State.empty []
  let deleteResult ←
    CheckedInput.callContract 64
      Executable.Examples.noReturnEffectReturnSourceUnit
      "NoReturnEffectReturn"
      (SolidCore.Solidity.Source.CallTarget.name "returnDelete")
      SolidCore.Solidity.Source.State.empty []
  let popResult ←
    CheckedInput.callContract 96
      Executable.Examples.noReturnEffectReturnSourceUnit
      "NoReturnEffectReturn"
      (SolidCore.Solidity.Source.CallTarget.name "returnPop")
      SolidCore.Solidity.Source.State.empty []
  let pushResult ←
    CheckedInput.callContract 96
      Executable.Examples.noReturnEffectReturnSourceUnit
      "NoReturnEffectReturn"
      (SolidCore.Solidity.Source.CallTarget.name "returnPushValue")
      SolidCore.Solidity.Source.State.empty []
  let internalResult ←
    CheckedInput.callContract 64
      Executable.Examples.noReturnEffectReturnSourceUnit
      "NoReturnEffectReturn"
      (SolidCore.Solidity.Source.CallTarget.name "returnInternal")
      SolidCore.Solidity.Source.State.empty []
  match requireTrue, requireFalse, revertResult, deleteResult,
      popResult, pushResult, internalResult with
  | SolidCore.Solidity.Source.CallResult.returned requireState [],
    SolidCore.Solidity.Source.CallResult.reverted requireFailState
      (SolidCore.Solidity.Source.RevertData.error "bad"),
    SolidCore.Solidity.Source.CallResult.reverted revertState
      (SolidCore.Solidity.Source.RevertData.error "bad"),
    SolidCore.Solidity.Source.CallResult.returned deleteState [],
    SolidCore.Solidity.Source.CallResult.returned popState [],
    SolidCore.Solidity.Source.CallResult.returned pushState [],
    SolidCore.Solidity.Source.CallResult.returned internalState [] =>
      let firstSlot :=
        SolidCore.Solidity.Source.dynamicArrayStorageSlot
          Executable.Examples.noReturnEffectDynamicArraySlot 0
      let secondSlot :=
        SolidCore.Solidity.Source.dynamicArrayStorageSlot
          Executable.Examples.noReturnEffectDynamicArraySlot 1
      Except.ok
        (SolidCore.Solidity.Source.wordEq
          (requireState.loadSlot 0) 1 &&
          SolidCore.Solidity.Source.wordEq
            (requireFailState.loadSlot 0) 0 &&
          SolidCore.Solidity.Source.wordEq
            (revertState.loadSlot 0) 0 &&
          SolidCore.Solidity.Source.wordEq
            (deleteState.loadSlot 0) 0 &&
          SolidCore.Solidity.Source.wordEq
            (popState.loadSlot
              Executable.Examples.noReturnEffectDynamicArraySlot) 1 &&
          SolidCore.Solidity.Source.wordEq
            (popState.loadSlot firstSlot) 11 &&
          SolidCore.Solidity.Source.wordEq
            (popState.loadSlot secondSlot) 0 &&
          SolidCore.Solidity.Source.wordEq
            (pushState.loadSlot
              Executable.Examples.noReturnEffectDynamicArraySlot) 1 &&
          SolidCore.Solidity.Source.wordEq
            (pushState.loadSlot firstSlot) 13 &&
          SolidCore.Solidity.Source.wordEq
            (internalState.loadSlot 0) 9)
  | _, _, _, _, _, _, _ => Except.ok false

def checkedNoReturnEffectReturnTransferMatches :
    Except TypeError Bool := do
  let contract ←
    CheckedInput.contract
      Executable.Examples.noReturnEffectReturnSourceUnit
      "NoReturnEffectReturn"
  let function ←
    optionToExcept "returnTransfer function"
      (contract.core.findFunctionByName? "returnTransfer")
  let result ←
    match
      SolidCore.Solidity.Source.FunctionDef.callFailOpen? 64
      (SolidCore.Solidity.Source.responderOfResults
            [ { kind := SolidCore.Solidity.Source.LowLevelCallKind.call
                target := 0xbeef
                calldata := []
                value := 5
                gas? := some 2300
                success := true
                output := [] } ]
      [])
        (contract.core.context)
        function SolidCore.Solidity.Source.State.empty
        [ SolidCore.Solidity.Source.Value.word 0xbeef
        , SolidCore.Solidity.Source.Value.word 5 ] with
    | some result => Except.ok result
    | none => Except.error (executableFailure "returnTransfer")
  match result with
  | SolidCore.Solidity.Source.CallResult.returned state [] =>
      Except.ok (SolidCore.Solidity.Source.wordEq (state.loadSlot 0) 1)
  | _ => Except.ok false

def checkedTerminalStatementContractsAccepted :
    Except TypeError Bool := do
  let _ ← ContractDecl.checkedContract checkedPrimitiveStatementContract
  let _ ←
    ContractDecl.checkedContract
      Executable.Examples.checkedAddressEnvironmentContract
  Except.ok true

def checkedOwnCallWordAndSlotMatches (fuel : Nat)
    (decl : SourceContractDecl) (functionName : Name)
    (state : CoreState) (args : List CoreValue)
    (expectedValue expectedSlot : Word) : Except TypeError Bool := do
  let result ←
    CheckedInput.ownCall fuel decl
      (SolidCore.Solidity.Source.CallTarget.name functionName)
      state args
  match result with
  | SolidCore.Solidity.Source.CallResult.returned state
      [SolidCore.Solidity.Source.Value.word value] =>
      Except.ok
        (SolidCore.Solidity.Source.wordEq value expectedValue &&
          SolidCore.Solidity.Source.wordEq (state.loadSlot 0) expectedSlot)
  | _ => Except.ok false

def checkedOwnCallIntAndSlotMatches (fuel : Nat)
    (decl : SourceContractDecl) (functionName : Name)
    (state : CoreState) (args : List CoreValue)
    (expectedValue expectedSlot : Word) : Except TypeError Bool := do
  let result ←
    CheckedInput.ownCall fuel decl
      (SolidCore.Solidity.Source.CallTarget.name functionName)
      state args
  match result with
  | SolidCore.Solidity.Source.CallResult.returned state
      [SolidCore.Solidity.Source.Value.int value] =>
      Except.ok
        (SolidCore.Solidity.Source.wordEq value expectedValue &&
          SolidCore.Solidity.Source.wordEq (state.loadSlot 0) expectedSlot)
  | _ => Except.ok false

def checkedExpressionEvaluationContractsAccepted : Bool :=
  Result.isOk
      (TypecheckedInput.checkedSourceUnit
        Executable.Examples.internalBinaryLocalCallContract) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit
        Executable.Examples.internalUnaryLocalCallContract) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit
        Executable.Examples.internalTernaryLocalCallContract)

def checkedInternalBinaryLocalCallMatches :
    Except TypeError Bool := do
  let runVar ←
    checkedOwnCallWordMatches 64
      Executable.Examples.internalBinaryLocalCallContract
      "runVar" SolidCore.Solidity.Source.State.empty [] 42
  let runAssign ←
    checkedOwnCallWordAndSlotMatches 64
      Executable.Examples.internalBinaryLocalCallContract
      "runAssign" SolidCore.Solidity.Source.State.empty [] 10 5
  let runVarBoth ←
    checkedOwnCallWordAndSlotMatches 64
      Executable.Examples.internalBinaryLocalCallContract
      "runVarBoth" SolidCore.Solidity.Source.State.empty [] 10 5
  let runAssignBoth ←
    checkedOwnCallWordAndSlotMatches 64
      Executable.Examples.internalBinaryLocalCallContract
      "runAssignBoth" SolidCore.Solidity.Source.State.empty [] 10 5
  let runVarShort ←
    checkedOwnCallWordAndSlotMatches 64
      Executable.Examples.internalBinaryLocalCallContract
      "runVarShort" SolidCore.Solidity.Source.State.empty [] 0 0
  let runAssignShort ←
    checkedOwnCallWordAndSlotMatches 64
      Executable.Examples.internalBinaryLocalCallContract
      "runAssignShort" SolidCore.Solidity.Source.State.empty [] 0 0
  let runVarShortBoth ←
    checkedOwnCallWordAndSlotMatches 64
      Executable.Examples.internalBinaryLocalCallContract
      "runVarShortBoth" SolidCore.Solidity.Source.State.empty [] 2 2
  let runAssignShortBoth ←
    checkedOwnCallWordAndSlotMatches 64
      Executable.Examples.internalBinaryLocalCallContract
      "runAssignShortBoth" SolidCore.Solidity.Source.State.empty [] 2 2
  let runAssignShortBothCall ←
    checkedOwnCallWordAndSlotMatches 64
      Executable.Examples.internalBinaryLocalCallContract
      "runAssignShortBothCall" SolidCore.Solidity.Source.State.empty [] 1 1
  Except.ok
    (runVar && runAssign && runVarBoth && runAssignBoth &&
      runVarShort && runAssignShort && runVarShortBoth &&
      runAssignShortBoth && runAssignShortBothCall)

def checkedInternalUnaryLocalCallMatches :
    Except TypeError Bool := do
  let runReturnNot ←
    checkedOwnCallWordAndSlotMatches 64
      Executable.Examples.internalUnaryLocalCallContract
      "runReturnNot" SolidCore.Solidity.Source.State.empty [] 1 7
  let runVarNot ←
    checkedOwnCallWordAndSlotMatches 64
      Executable.Examples.internalUnaryLocalCallContract
      "runVarNot" SolidCore.Solidity.Source.State.empty [] 1 7
  let runAssignNot ←
    checkedOwnCallWordAndSlotMatches 64
      Executable.Examples.internalUnaryLocalCallContract
      "runAssignNot" SolidCore.Solidity.Source.State.empty [] 1 7
  let runBitNot ←
    checkedOwnCallWordAndSlotMatches 64
      Executable.Examples.internalUnaryLocalCallContract
      "runBitNot" SolidCore.Solidity.Source.State.empty []
      (SolidCore.Solidity.Shared.notWord 0) 11
  let runNeg ←
    checkedOwnCallIntAndSlotMatches 64
      Executable.Examples.internalUnaryLocalCallContract
      "runNeg" SolidCore.Solidity.Source.State.empty []
      (SolidCore.Solidity.Shared.signedToWord 5) 13
  Except.ok
    (runReturnNot && runVarNot && runAssignNot && runBitNot && runNeg)

def checkedInternalTernaryLocalCallMatches :
    Except TypeError Bool := do
  let runReturnTrue ←
    checkedOwnCallWordAndSlotMatches 64
      Executable.Examples.internalTernaryLocalCallContract
      "runReturnTrue" SolidCore.Solidity.Source.State.empty [] 21 21
  let runReturnFalse ←
    checkedOwnCallWordAndSlotMatches 64
      Executable.Examples.internalTernaryLocalCallContract
      "runReturnFalse" SolidCore.Solidity.Source.State.empty [] 22 22
  let runVarTrue ←
    checkedOwnCallWordAndSlotMatches 64
      Executable.Examples.internalTernaryLocalCallContract
      "runVarTrue" SolidCore.Solidity.Source.State.empty [] 31 31
  let runAssignFalse ←
    checkedOwnCallWordAndSlotMatches 64
      Executable.Examples.internalTernaryLocalCallContract
      "runAssignFalse" SolidCore.Solidity.Source.State.empty [] 42 42
  Except.ok
    (runReturnTrue && runReturnFalse && runVarTrue && runAssignFalse)

def checkedSideEffectArgumentContractsAccepted : Bool :=
  Result.isOk
      (TypecheckedInput.checkedSourceUnit
        Executable.Examples.internalRequireConditionCallContract) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit
        Executable.Examples.internalRequireReasonCallContract) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit
        Executable.Examples.namedRequireCustomErrorArgumentOrderContract) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit
        Executable.Examples.internalEmitArgumentCallContract) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit
        Executable.Examples.internalEmitTwoArgumentCallContract) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit
        Executable.Examples.namedEventArgumentOrderContract) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit
        Executable.Examples.internalRevertArgumentCallContract) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit
        Executable.Examples.internalRevertTwoArgumentCallContract) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit
        Executable.Examples.namedErrorArgumentOrderContract) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit
        Executable.Examples.unspecifiedBinaryOrderContract) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit
        Executable.Examples.unspecifiedTupleOrderContract) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit
        Executable.Examples.unspecifiedLValueIndexOrderContract) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit
        Executable.Examples.unspecifiedStatementAssignOrderContract) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit
        Executable.Examples.unspecifiedMemoryRefOrderContract)

def checkedInternalRequireConditionCallMatches :
    Except TypeError Bool := do
  let runAssert ←
    checkedOwnCallWordAndSlotMatches 64
      Executable.Examples.internalRequireConditionCallContract
      "runAssert" SolidCore.Solidity.Source.State.empty [] 1 1
  let runRequire ←
    checkedOwnCallWordAndSlotMatches 64
      Executable.Examples.internalRequireConditionCallContract
      "runRequire" SolidCore.Solidity.Source.State.empty [] 1 1
  let runRequireFail ←
    CheckedInput.ownCall 64
      Executable.Examples.internalRequireConditionCallContract
      (SolidCore.Solidity.Source.CallTarget.name "runRequireFail")
      SolidCore.Solidity.Source.State.empty []
  let runRequireCustomFail ←
    CheckedInput.ownCall 64
      Executable.Examples.internalRequireConditionCallContract
      (SolidCore.Solidity.Source.CallTarget.name "runRequireCustomFail")
      SolidCore.Solidity.Source.State.empty []
  let failMatches :=
    match runRequireFail with
    | SolidCore.Solidity.Source.CallResult.reverted state
        (SolidCore.Solidity.Source.RevertData.error reason) =>
        reason == "bad" &&
          SolidCore.Solidity.Source.wordEq (state.loadSlot 0) 0
    | _ => false
  let customMatches :=
    match runRequireCustomFail with
    | SolidCore.Solidity.Source.CallResult.reverted state
        (SolidCore.Solidity.Source.RevertData.custom "Bad"
          [SolidCore.Solidity.Source.Value.word value]) =>
        SolidCore.Solidity.Source.wordEq value 7 &&
          SolidCore.Solidity.Source.wordEq (state.loadSlot 0) 0
    | _ => false
  Except.ok
    (runAssert && runRequire && failMatches && customMatches)

def checkedInternalRequireReasonCallMatches :
    Except TypeError Bool := do
  let reasonTrue ←
    checkedOwnCallWordAndSlotMatches 64
      Executable.Examples.internalRequireReasonCallContract
      "runReasonTrue" SolidCore.Solidity.Source.State.empty [] 9 9
  let customFalse ←
    CheckedInput.ownCall 64
      Executable.Examples.internalRequireReasonCallContract
      (SolidCore.Solidity.Source.CallTarget.name "runCustomFalse")
      SolidCore.Solidity.Source.State.empty []
  let bothReasonTrue ←
    checkedOwnCallWordAndSlotMatches 64
      Executable.Examples.internalRequireReasonCallContract
      "runBothReasonTrue" SolidCore.Solidity.Source.State.empty [] 9 9
  let bothCustomFalse ←
    CheckedInput.ownCall 64
      Executable.Examples.internalRequireReasonCallContract
      (SolidCore.Solidity.Source.CallTarget.name "runBothCustomFalse")
      SolidCore.Solidity.Source.State.empty []
  let customMatches :=
    match customFalse with
    | SolidCore.Solidity.Source.CallResult.reverted state
        (SolidCore.Solidity.Source.RevertData.custom "Bad"
          [SolidCore.Solidity.Source.Value.word value]) =>
        SolidCore.Solidity.Source.wordEq value 7 &&
          SolidCore.Solidity.Source.wordEq (state.loadSlot 0) 0
    | _ => false
  let bothCustomMatches :=
    match bothCustomFalse with
    | SolidCore.Solidity.Source.CallResult.reverted state
        (SolidCore.Solidity.Source.RevertData.custom "Bad"
          [SolidCore.Solidity.Source.Value.word value]) =>
        SolidCore.Solidity.Source.wordEq value 7 &&
          SolidCore.Solidity.Source.wordEq (state.loadSlot 0) 0
    | _ => false
  Except.ok
    (reasonTrue && customMatches && bothReasonTrue && bothCustomMatches)

def checkedNamedRequireCustomErrorArgumentOrderMatches :
    Except TypeError Bool := do
  let result ←
    CheckedInput.ownCall 16
      Executable.Examples.namedRequireCustomErrorArgumentOrderContract
      (SolidCore.Solidity.Source.CallTarget.name "run")
      SolidCore.Solidity.Source.State.empty []
  match result with
  | SolidCore.Solidity.Source.CallResult.reverted _
      (SolidCore.Solidity.Source.RevertData.custom "Bad"
        [ SolidCore.Solidity.Source.Value.word first
        , SolidCore.Solidity.Source.Value.word second ]) =>
      Except.ok
        (SolidCore.Solidity.Source.wordEq first 40 &&
          SolidCore.Solidity.Source.wordEq second 2)
  | _ => Except.ok false

def checkedInternalEmitArgumentCallMatches :
    Except TypeError Bool := do
  let result ←
    CheckedInput.ownCall 64
      Executable.Examples.internalEmitArgumentCallContract
      (SolidCore.Solidity.Source.CallTarget.name "run")
      SolidCore.Solidity.Source.State.empty []
  match result with
  | SolidCore.Solidity.Source.CallResult.returned state
      [SolidCore.Solidity.Source.Value.word value] =>
      match state.events with
      | [event] =>
          match event.data with
          | [SolidCore.Solidity.Source.Value.word eventValue] =>
              Except.ok
                (SolidCore.Solidity.Source.wordEq value 7 &&
                  event.name == "Seen" &&
                  SolidCore.Solidity.Source.wordEq eventValue 7 &&
                  SolidCore.Solidity.Source.wordEq
                    (state.loadSlot 0) 7)
          | _ => Except.ok false
      | _ => Except.ok false
  | _ => Except.ok false

def checkedInternalEmitTwoArgumentCallMatches :
    Except TypeError Bool := do
  let left ←
    CheckedInput.ownCall 64
      Executable.Examples.internalEmitTwoArgumentCallContract
      (SolidCore.Solidity.Source.CallTarget.name "runLeft")
      SolidCore.Solidity.Source.State.empty []
  let right ←
    CheckedInput.ownCall 64
      Executable.Examples.internalEmitTwoArgumentCallContract
      (SolidCore.Solidity.Source.CallTarget.name "runRight")
      SolidCore.Solidity.Source.State.empty []
  let both ←
    CheckedInput.ownCall 64
      Executable.Examples.internalEmitTwoArgumentCallContract
      (SolidCore.Solidity.Source.CallTarget.name "runBoth")
      SolidCore.Solidity.Source.State.empty []
  match left, right, both with
  | SolidCore.Solidity.Source.CallResult.returned leftState
      [SolidCore.Solidity.Source.Value.word leftRet],
    SolidCore.Solidity.Source.CallResult.returned rightState
      [SolidCore.Solidity.Source.Value.word rightRet],
    SolidCore.Solidity.Source.CallResult.returned bothState
      [SolidCore.Solidity.Source.Value.word bothRet] =>
      match leftState.events, rightState.events, bothState.events with
      | [leftEvent], [rightEvent], [bothEvent] =>
          match leftEvent.data, rightEvent.data, bothEvent.data with
          | [ SolidCore.Solidity.Source.Value.word left0
            , SolidCore.Solidity.Source.Value.word left1 ],
            [ SolidCore.Solidity.Source.Value.word right0
            , SolidCore.Solidity.Source.Value.word right1 ],
            [ SolidCore.Solidity.Source.Value.word both0
            , SolidCore.Solidity.Source.Value.word both1 ] =>
              Except.ok
                (leftEvent.name == "Seen" &&
                  rightEvent.name == "Seen" &&
                  bothEvent.name == "Seen" &&
                  SolidCore.Solidity.Source.wordEq leftRet 7 &&
                  SolidCore.Solidity.Source.wordEq left0 7 &&
                  SolidCore.Solidity.Source.wordEq left1 8 &&
                  SolidCore.Solidity.Source.wordEq
                    (leftState.loadSlot 0) 7 &&
                  SolidCore.Solidity.Source.wordEq rightRet 5 &&
                  SolidCore.Solidity.Source.wordEq right0 5 &&
                  SolidCore.Solidity.Source.wordEq right1 5 &&
                  SolidCore.Solidity.Source.wordEq
                    (rightState.loadSlot 0) 5 &&
                  SolidCore.Solidity.Source.wordEq bothRet 7 &&
                  SolidCore.Solidity.Source.wordEq both0 7 &&
                  SolidCore.Solidity.Source.wordEq both1 7 &&
                  SolidCore.Solidity.Source.wordEq
                    (bothState.loadSlot 0) 7)
          | _, _, _ => Except.ok false
      | _, _, _ => Except.ok false
  | _, _, _ => Except.ok false

def checkedNamedEventArgumentOrderFixtureMatches :
    Except TypeError Bool := do
  let result ←
    CheckedInput.ownCall 16
      Executable.Examples.namedEventArgumentOrderContract
      (SolidCore.Solidity.Source.CallTarget.name "run")
      SolidCore.Solidity.Source.State.empty []
  match result with
  | SolidCore.Solidity.Source.CallResult.returned state [] =>
      match state.events with
      | [event] =>
          match event.data with
          | [ SolidCore.Solidity.Source.Value.word first
            , SolidCore.Solidity.Source.Value.word second ] =>
              Except.ok
                (event.name == "Seen" &&
                  SolidCore.Solidity.Source.wordEq first 40 &&
                  SolidCore.Solidity.Source.wordEq second 2)
          | _ => Except.ok false
      | _ => Except.ok false
  | _ => Except.ok false

def checkedInternalRevertArgumentCallMatches :
    Except TypeError Bool := do
  let result ←
    CheckedInput.ownCall 64
      Executable.Examples.internalRevertArgumentCallContract
      (SolidCore.Solidity.Source.CallTarget.name "run")
      SolidCore.Solidity.Source.State.empty []
  match result with
  | SolidCore.Solidity.Source.CallResult.reverted state
      (SolidCore.Solidity.Source.RevertData.custom "Bad"
        [SolidCore.Solidity.Source.Value.word value]) =>
      Except.ok
        (SolidCore.Solidity.Source.wordEq value 7 &&
          SolidCore.Solidity.Source.wordEq (state.loadSlot 0) 0)
  | _ => Except.ok false

def checkedInternalRevertTwoArgumentCallMatches :
    Except TypeError Bool := do
  let left ←
    CheckedInput.ownCall 64
      Executable.Examples.internalRevertTwoArgumentCallContract
      (SolidCore.Solidity.Source.CallTarget.name "runLeft")
      SolidCore.Solidity.Source.State.empty []
  let right ←
    CheckedInput.ownCall 64
      Executable.Examples.internalRevertTwoArgumentCallContract
      (SolidCore.Solidity.Source.CallTarget.name "runRight")
      SolidCore.Solidity.Source.State.empty []
  let both ←
    CheckedInput.ownCall 64
      Executable.Examples.internalRevertTwoArgumentCallContract
      (SolidCore.Solidity.Source.CallTarget.name "runBoth")
      SolidCore.Solidity.Source.State.empty []
  match left, right, both with
  | SolidCore.Solidity.Source.CallResult.reverted leftState
      (SolidCore.Solidity.Source.RevertData.custom "Bad"
        [ SolidCore.Solidity.Source.Value.word left0
        , SolidCore.Solidity.Source.Value.word left1 ]),
    SolidCore.Solidity.Source.CallResult.reverted rightState
      (SolidCore.Solidity.Source.RevertData.custom "Bad"
        [ SolidCore.Solidity.Source.Value.word right0
        , SolidCore.Solidity.Source.Value.word right1 ]),
    SolidCore.Solidity.Source.CallResult.reverted bothState
      (SolidCore.Solidity.Source.RevertData.custom "Bad"
        [ SolidCore.Solidity.Source.Value.word both0
        , SolidCore.Solidity.Source.Value.word both1 ]) =>
      Except.ok
        (SolidCore.Solidity.Source.wordEq left0 7 &&
          SolidCore.Solidity.Source.wordEq left1 8 &&
          SolidCore.Solidity.Source.wordEq (leftState.loadSlot 0) 0 &&
          SolidCore.Solidity.Source.wordEq right0 5 &&
          SolidCore.Solidity.Source.wordEq right1 5 &&
          SolidCore.Solidity.Source.wordEq (rightState.loadSlot 0) 0 &&
          SolidCore.Solidity.Source.wordEq both0 7 &&
          SolidCore.Solidity.Source.wordEq both1 7 &&
          SolidCore.Solidity.Source.wordEq (bothState.loadSlot 0) 0)
  | _, _, _ => Except.ok false

def checkedNamedErrorArgumentOrderFixtureMatches :
    Except TypeError Bool := do
  let result ←
    CheckedInput.ownCall 16
      Executable.Examples.namedErrorArgumentOrderContract
      (SolidCore.Solidity.Source.CallTarget.name "run")
      SolidCore.Solidity.Source.State.empty []
  match result with
  | SolidCore.Solidity.Source.CallResult.reverted _
      (SolidCore.Solidity.Source.RevertData.custom "Bad"
        [ SolidCore.Solidity.Source.Value.word first
        , SolidCore.Solidity.Source.Value.word second ]) =>
      Except.ok
        (SolidCore.Solidity.Source.wordEq first 40 &&
          SolidCore.Solidity.Source.wordEq second 2)
  | _ => Except.ok false

def checkedUnspecifiedBinaryOrderDeterministicRunMatches :
    Except TypeError Bool :=
  checkedOwnCallWordAndSlotMatches 32
    Executable.Examples.unspecifiedBinaryOrderContract
    "run" SolidCore.Solidity.Source.State.empty [] 5 5

def checkedUnspecifiedTupleOrderDeterministicRunMatches :
    Except TypeError Bool := do
  -- Tuple components evaluate LEFT to RIGHT (intrinsic order), so both
  -- components observe the assignment: (5, 5).
  let result ←
    CheckedInput.ownCall 32
      Executable.Examples.unspecifiedTupleOrderContract
      (SolidCore.Solidity.Source.CallTarget.name "runTuple")
      SolidCore.Solidity.Source.State.empty []
  match result with
  | SolidCore.Solidity.Source.CallResult.returned state
      [ SolidCore.Solidity.Source.Value.word first
      , SolidCore.Solidity.Source.Value.word second ] =>
      Except.ok
        (SolidCore.Solidity.Source.wordEq first 5 &&
          SolidCore.Solidity.Source.wordEq second 5 &&
          SolidCore.Solidity.Source.wordEq (state.loadSlot 0) 5)
  | SolidCore.Solidity.Source.CallResult.returned state [value] =>
      let (first, second) ← checkedDecodeWordPair value
      Except.ok
        (SolidCore.Solidity.Source.wordEq first 5 &&
          SolidCore.Solidity.Source.wordEq second 5 &&
          SolidCore.Solidity.Source.wordEq (state.loadSlot 0) 5)
  | _ => Except.ok false

def checkedUnspecifiedTupleOrderRunWithContextEval :
    Except TypeError (Option (Word × Word × Word)) := do
  let checkedContract ←
    CheckedInput.ownContract
      Executable.Examples.unspecifiedTupleOrderContract
  let context := checkedContract.core.context
  let result ←
    CheckedContract.callFunctionWithContext 32 checkedContract "runTuple"
      context SolidCore.Solidity.Source.State.empty []
  match result with
  | SolidCore.Solidity.Source.CallResult.returned state
      [ SolidCore.Solidity.Source.Value.word first
      , SolidCore.Solidity.Source.Value.word second ] =>
      Except.ok (some (first, second, state.loadSlot 0))
  | SolidCore.Solidity.Source.CallResult.returned state [value] => do
      let (first, second) ← checkedDecodeWordPair value
      Except.ok (some (first, second, state.loadSlot 0))
  | _ => Except.ok none

def checkedUnspecifiedTupleOrderContextEvaluationMatches :
    Except TypeError Bool := do
  let result ← checkedUnspecifiedTupleOrderRunWithContextEval
  match result with
  | some (first, second, slot) =>
      Except.ok
        (SolidCore.Solidity.Source.wordEq first 5 &&
          SolidCore.Solidity.Source.wordEq second 5 &&
          SolidCore.Solidity.Source.wordEq slot 5)
  | none => Except.ok false

def checkedUnspecifiedTupleOrderAbiRunWithContextEval :
    Except TypeError (Option (Word × Word × Word)) := do
  let checkedContract ←
    CheckedInput.ownContract
      Executable.Examples.unspecifiedTupleOrderContract
  let calldata ←
    CheckedContract.functionCalldata checkedContract "runTuple" []
  let context := checkedContract.core.context
  let result ←
    CheckedContract.callCalldataAtFromWithContext 32 checkedContract context
      SolidCore.Solidity.Source.State.empty 0 0 0 calldata
  if result.success then
    let values ←
      optionToExcept "ABI tuple order decode"
        (SolidCore.Solidity.Source.abiDecodeValues?
          [ SolidCore.Solidity.Source.Ty.uint256
          , SolidCore.Solidity.Source.Ty.uint256 ]
          result.output)
    match values with
    | [ SolidCore.Solidity.Source.Value.word first
      , SolidCore.Solidity.Source.Value.word second ] =>
        Except.ok (some (first, second, result.state.loadSlot 0))
    | _ => Except.ok none
  else
    Except.ok none

def checkedUnspecifiedTupleOrderAbiContextEvaluationMatches :
    Except TypeError Bool := do
  let result ← checkedUnspecifiedTupleOrderAbiRunWithContextEval
  match result with
  | some (first, second, slot) =>
      Except.ok
        (SolidCore.Solidity.Source.wordEq first 5 &&
          SolidCore.Solidity.Source.wordEq second 5 &&
          SolidCore.Solidity.Source.wordEq slot 5)
  | none => Except.ok false

def checkedUnspecifiedLValueIndexOrderRunWithContextEval :
    Except TypeError (Option (Word × Word × Word)) := do
  let checkedContract ←
    CheckedInput.ownContract
      Executable.Examples.unspecifiedLValueIndexOrderContract
  let context := checkedContract.core.context
  let result ←
    CheckedContract.callFunctionWithContext 64 checkedContract
      "runLValueIndex" context
      SolidCore.Solidity.Source.State.empty []
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _
      [ SolidCore.Solidity.Source.Value.word first
      , SolidCore.Solidity.Source.Value.word second
      , SolidCore.Solidity.Source.Value.word seen ] =>
      Except.ok (some (first, second, seen))
  | _ => Except.ok none

def checkedUnspecifiedLValueIndexOrderContextEvaluationMatches :
    Except TypeError Bool := do
  let result ← checkedUnspecifiedLValueIndexOrderRunWithContextEval
  match result with
  | some (first, second, seen) =>
      Except.ok
        (SolidCore.Solidity.Source.wordEq first 0 &&
          SolidCore.Solidity.Source.wordEq second 9 &&
          SolidCore.Solidity.Source.wordEq seen 1)
  | none => Except.ok false

def checkedUnspecifiedStatementAssignOrderRunWithContextEval :
    Except TypeError (Option (Word × Word × Word)) := do
  let checkedContract ←
    CheckedInput.ownContract
      Executable.Examples.unspecifiedStatementAssignOrderContract
  let context := checkedContract.core.context
  let result ←
    CheckedContract.callFunctionWithContext 64 checkedContract
      "runStatementAssign" context
      SolidCore.Solidity.Source.State.empty []
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _
      [ SolidCore.Solidity.Source.Value.word first
      , SolidCore.Solidity.Source.Value.word second
      , SolidCore.Solidity.Source.Value.word seen ] =>
      Except.ok (some (first, second, seen))
  | _ => Except.ok none

def checkedUnspecifiedStatementAssignOrderContextEvaluationMatches :
    Except TypeError Bool := do
  let result ← checkedUnspecifiedStatementAssignOrderRunWithContextEval
  match result with
  | some (first, second, seen) =>
      Except.ok
        (SolidCore.Solidity.Source.wordEq first 0 &&
          SolidCore.Solidity.Source.wordEq second 1 &&
          SolidCore.Solidity.Source.wordEq seen 1)
  | none => Except.ok false

def checkedUnspecifiedMemoryRefOrderRunWithContextEval :
    Except TypeError (Option (Word × Word × Word)) := do
  let checkedContract ←
    CheckedInput.ownContract
      Executable.Examples.unspecifiedMemoryRefOrderContract
  let context := checkedContract.core.context
  let result ←
    CheckedContract.callFunctionWithContext 128 checkedContract
      "runMemoryRefOrder" context
      SolidCore.Solidity.Source.State.empty []
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _
      [ SolidCore.Solidity.Source.Value.word first
      , SolidCore.Solidity.Source.Value.word second
      , SolidCore.Solidity.Source.Value.word seen ] =>
      Except.ok (some (first, second, seen))
  | _ => Except.ok none

def checkedUnspecifiedMemoryRefOrderContextEvaluationMatches :
    Except TypeError Bool := do
  let result ← checkedUnspecifiedMemoryRefOrderRunWithContextEval
  match result with
  | some (first, second, seen) =>
      Except.ok
        (SolidCore.Solidity.Source.wordEq first 0 &&
          SolidCore.Solidity.Source.wordEq second 7 &&
          SolidCore.Solidity.Source.wordEq seen 1)
  | none => Except.ok false

def checkedTupleAndFreeFunctionContractsAccepted : Bool :=
  Result.isOk
      (TypecheckedInput.checkedSourceUnit
        Executable.Examples.internalTupleReturnCallContract) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit
        Executable.Examples.internalTupleRightReturnCallContract) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit
        Executable.Examples.internalTupleBothReturnCallContract) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit
        Executable.Examples.internalNamedArgsContract) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit
        Executable.Examples.tupleVarDeclContract) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit
        Executable.Examples.tupleVarDeclHoleContract) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit
        Executable.Examples.tupleAssignmentSwapContract) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit
        Executable.Examples.tupleAssignmentHoleContract) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit
        Executable.Examples.internalVarDeclCallContract) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit
        Executable.Examples.internalMultiVarDeclCallContract) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit
        Executable.Examples.freeFunctionUnit) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit
        Executable.Examples.freeNamedArgsUnit)

def checkedFreeFunctionStorageIsolationRejected : Bool :=
  match TypecheckedInput.checkedSourceUnit
      Executable.Examples.freeFunctionStorageIsolationUnit with
  | Except.ok _ => false
  | Except.error _ => true

def checkedOwnCallWordPairAndSlotMatches (fuel : Nat)
    (decl : SourceContractDecl) (functionName : Name)
    (state : CoreState) (args : List CoreValue)
    (expectedLeft expectedRight expectedSlot : Word) :
    Except TypeError Bool := do
  let result ←
    CheckedInput.ownCall fuel decl
      (SolidCore.Solidity.Source.CallTarget.name functionName)
      state args
  match result with
  | SolidCore.Solidity.Source.CallResult.returned state
      [ SolidCore.Solidity.Source.Value.word left
      , SolidCore.Solidity.Source.Value.word right ] =>
      Except.ok
        (SolidCore.Solidity.Source.wordEq left expectedLeft &&
          SolidCore.Solidity.Source.wordEq right expectedRight &&
          SolidCore.Solidity.Source.wordEq (state.loadSlot 0) expectedSlot)
  | SolidCore.Solidity.Source.CallResult.returned state [value] =>
      let (left, right) ← checkedDecodeWordPair value
      Except.ok
        (SolidCore.Solidity.Source.wordEq left expectedLeft &&
          SolidCore.Solidity.Source.wordEq right expectedRight &&
          SolidCore.Solidity.Source.wordEq (state.loadSlot 0) expectedSlot)
  | _ => Except.ok false

def checkedInternalTupleReturnCallMatches :
    Except TypeError Bool :=
  checkedOwnCallWordPairAndSlotMatches 64
    Executable.Examples.internalTupleReturnCallContract
    "run" SolidCore.Solidity.Source.State.empty [] 5 6 5

def checkedInternalTupleRightReturnCallMatches :
    Except TypeError Bool :=
  checkedOwnCallWordPairAndSlotMatches 64
    Executable.Examples.internalTupleRightReturnCallContract
    "run" SolidCore.Solidity.Source.State.empty [] 5 5 5

def checkedInternalTupleBothReturnCallMatches :
    Except TypeError Bool :=
  checkedOwnCallWordPairAndSlotMatches 64
    Executable.Examples.internalTupleBothReturnCallContract
    "run" SolidCore.Solidity.Source.State.empty [] 5 5 5

def checkedInternalNamedArgsMatches :
    Except TypeError Bool :=
  checkedOwnCallWordMatches 32
    Executable.Examples.internalNamedArgsContract
    "run" SolidCore.Solidity.Source.State.empty [] 42

def checkedTupleVarDeclMatches :
    Except TypeError Bool :=
  checkedOwnCallWordMatches 32
    Executable.Examples.tupleVarDeclContract
    "run" SolidCore.Solidity.Source.State.empty [] 42

def checkedTupleVarDeclHoleMatches :
    Except TypeError Bool :=
  checkedOwnCallWordMatches 32
    Executable.Examples.tupleVarDeclHoleContract
    "run" SolidCore.Solidity.Source.State.empty [] 42

def checkedTupleAssignmentSwapMatches :
    Except TypeError Bool :=
  checkedOwnCallWordMatches 32
    Executable.Examples.tupleAssignmentSwapContract
    "run" SolidCore.Solidity.Source.State.empty [] 24

def checkedTupleAssignmentHoleMatches :
    Except TypeError Bool :=
  checkedOwnCallWordMatches 32
    Executable.Examples.tupleAssignmentHoleContract
    "run" SolidCore.Solidity.Source.State.empty [] 42

def checkedInternalVarDeclCallMatches :
    Except TypeError Bool :=
  checkedOwnCallWordMatches 32
    Executable.Examples.internalVarDeclCallContract
    "run" SolidCore.Solidity.Source.State.empty [] 10

def checkedInternalMultiVarDeclCallMatches :
    Except TypeError Bool :=
  checkedOwnCallWordMatches 32
    Executable.Examples.internalMultiVarDeclCallContract
    "run" SolidCore.Solidity.Source.State.empty [] 41

def checkedFreeFunctionCallMatches :
    Except TypeError Bool :=
  checkedCallWordMatches 32
    Executable.Examples.freeFunctionUnit "FreeFunctionCaller"
    "run" SolidCore.Solidity.Source.State.empty
    [SolidCore.Solidity.Source.Value.word 21] 42

def checkedFreeNamedArgsMatches :
    Except TypeError Bool :=
  checkedCallWordMatches 32
    Executable.Examples.freeNamedArgsUnit "FreeNamedArgs"
    "run" SolidCore.Solidity.Source.State.empty [] 42

def checkedTargetEffectContractsAccepted : Bool :=
  Result.isOk
      (TypecheckedInput.checkedSourceUnit
        Executable.Examples.expressionTargetEffectsContract) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit
        Executable.Examples.storageIndexedCompoundTargetEffectsContract)

def checkedOwnCallWordTripleMatches (fuel : Nat)
    (decl : SourceContractDecl) (functionName : Name)
    (state : CoreState) (args : List CoreValue)
    (expectedA expectedB expectedC : Word) : Except TypeError Bool := do
  let result ←
    CheckedInput.ownCall fuel decl
      (SolidCore.Solidity.Source.CallTarget.name functionName)
      state args
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _
      [ SolidCore.Solidity.Source.Value.word a
      , SolidCore.Solidity.Source.Value.word b
      , SolidCore.Solidity.Source.Value.word c ] =>
      Except.ok
        (SolidCore.Solidity.Source.wordEq a expectedA &&
          SolidCore.Solidity.Source.wordEq b expectedB &&
          SolidCore.Solidity.Source.wordEq c expectedC)
  | _ => Except.ok false

def checkedOwnCallIntTripleMatches (fuel : Nat)
    (decl : SourceContractDecl) (functionName : Name)
    (state : CoreState) (args : List CoreValue)
    (expectedA expectedB expectedC : Word) : Except TypeError Bool := do
  let result ←
    CheckedInput.ownCall fuel decl
      (SolidCore.Solidity.Source.CallTarget.name functionName)
      state args
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _
      [ SolidCore.Solidity.Source.Value.int a
      , SolidCore.Solidity.Source.Value.int b
      , SolidCore.Solidity.Source.Value.int c ] =>
      Except.ok
        (SolidCore.Solidity.Source.wordEq a expectedA &&
          SolidCore.Solidity.Source.wordEq b expectedB &&
          SolidCore.Solidity.Source.wordEq c expectedC)
  | _ => Except.ok false

def checkedOwnCallWordPairMatches (fuel : Nat)
    (decl : SourceContractDecl) (functionName : Name)
    (state : CoreState) (args : List CoreValue)
    (expectedA expectedB : Word) : Except TypeError Bool := do
  let result ←
    CheckedInput.ownCall fuel decl
      (SolidCore.Solidity.Source.CallTarget.name functionName)
      state args
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _
      [ SolidCore.Solidity.Source.Value.word a
      , SolidCore.Solidity.Source.Value.word b ] =>
      Except.ok
        (SolidCore.Solidity.Source.wordEq a expectedA &&
          SolidCore.Solidity.Source.wordEq b expectedB)
  | SolidCore.Solidity.Source.CallResult.returned _ [value] =>
      let (a, b) ← checkedDecodeWordPair value
      Except.ok
        (SolidCore.Solidity.Source.wordEq a expectedA &&
          SolidCore.Solidity.Source.wordEq b expectedB)
  | _ => Except.ok false

def checkedOwnCallWordQuintMatches (fuel : Nat)
    (decl : SourceContractDecl) (functionName : Name)
    (state : CoreState) (args : List CoreValue)
    (expectedA expectedB expectedC expectedD expectedE : Word) :
    Except TypeError Bool := do
  let result ←
    CheckedInput.ownCall fuel decl
      (SolidCore.Solidity.Source.CallTarget.name functionName)
      state args
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _
      [ SolidCore.Solidity.Source.Value.word a
      , SolidCore.Solidity.Source.Value.word b
      , SolidCore.Solidity.Source.Value.word c
      , SolidCore.Solidity.Source.Value.word d
      , SolidCore.Solidity.Source.Value.word e ] =>
      Except.ok
        (SolidCore.Solidity.Source.wordEq a expectedA &&
          SolidCore.Solidity.Source.wordEq b expectedB &&
          SolidCore.Solidity.Source.wordEq c expectedC &&
          SolidCore.Solidity.Source.wordEq d expectedD &&
          SolidCore.Solidity.Source.wordEq e expectedE)
  | _ => Except.ok false

def checkedOwnCallIntQuintMatches (fuel : Nat)
    (decl : SourceContractDecl) (functionName : Name)
    (state : CoreState) (args : List CoreValue)
    (expectedA expectedB expectedC expectedD expectedE : Word) :
    Except TypeError Bool := do
  let result ←
    CheckedInput.ownCall fuel decl
      (SolidCore.Solidity.Source.CallTarget.name functionName)
      state args
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _
      [ SolidCore.Solidity.Source.Value.int a
      , SolidCore.Solidity.Source.Value.int b
      , SolidCore.Solidity.Source.Value.int c
      , SolidCore.Solidity.Source.Value.int d
      , SolidCore.Solidity.Source.Value.int e ] =>
      Except.ok
        (SolidCore.Solidity.Source.wordEq a expectedA &&
          SolidCore.Solidity.Source.wordEq b expectedB &&
          SolidCore.Solidity.Source.wordEq c expectedC &&
          SolidCore.Solidity.Source.wordEq d expectedD &&
          SolidCore.Solidity.Source.wordEq e expectedE)
  | _ => Except.ok false

def checkedOwnCallWordQuadMatches (fuel : Nat)
    (decl : SourceContractDecl) (functionName : Name)
    (state : CoreState) (args : List CoreValue)
    (expectedA expectedB expectedC expectedD : Word) :
    Except TypeError Bool := do
  let result ←
    CheckedInput.ownCall fuel decl
      (SolidCore.Solidity.Source.CallTarget.name functionName)
      state args
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _
      [ SolidCore.Solidity.Source.Value.word a
      , SolidCore.Solidity.Source.Value.word b
      , SolidCore.Solidity.Source.Value.word c
      , SolidCore.Solidity.Source.Value.word d ] =>
      Except.ok
        (SolidCore.Solidity.Source.wordEq a expectedA &&
          SolidCore.Solidity.Source.wordEq b expectedB &&
          SolidCore.Solidity.Source.wordEq c expectedC &&
          SolidCore.Solidity.Source.wordEq d expectedD)
  | _ => Except.ok false

def checkedOwnCallBytesMatches (fuel : Nat)
    (decl : SourceContractDecl) (functionName : Name)
    (state : CoreState) (args : List CoreValue)
    (expected : List Byte) : Except TypeError Bool := do
  let result ←
    CheckedInput.ownCall fuel decl
      (SolidCore.Solidity.Source.CallTarget.name functionName)
      state args
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _
      [SolidCore.Solidity.Source.Value.bytes bytes] =>
      Except.ok (bytes == expected)
  | _ => Except.ok false

def checkedOwnCallWordAndBytesMatches (fuel : Nat)
    (decl : SourceContractDecl) (functionName : Name)
    (state : CoreState) (args : List CoreValue)
    (expectedWord : Word) (expectedBytes : List Byte) :
    Except TypeError Bool := do
  let result ←
    CheckedInput.ownCall fuel decl
      (SolidCore.Solidity.Source.CallTarget.name functionName)
      state args
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _
      [ SolidCore.Solidity.Source.Value.word value
      , SolidCore.Solidity.Source.Value.bytes bytes ] =>
      Except.ok
        (SolidCore.Solidity.Source.wordEq value expectedWord &&
          bytes == expectedBytes)
  | _ => Except.ok false

def checkedOwnCallBytesAndWordQuadMatches (fuel : Nat)
    (decl : SourceContractDecl) (functionName : Name)
    (state : CoreState) (args : List CoreValue)
    (expectedBytes : List Byte)
    (expectedA expectedB expectedC expectedD : Word) :
    Except TypeError Bool := do
  let result ←
    CheckedInput.ownCall fuel decl
      (SolidCore.Solidity.Source.CallTarget.name functionName)
      state args
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _
      [ SolidCore.Solidity.Source.Value.bytes bytes
      , SolidCore.Solidity.Source.Value.word a
      , SolidCore.Solidity.Source.Value.word b
      , SolidCore.Solidity.Source.Value.word c
      , SolidCore.Solidity.Source.Value.word d ] =>
      Except.ok
        (bytes == expectedBytes &&
          SolidCore.Solidity.Source.wordEq a expectedA &&
          SolidCore.Solidity.Source.wordEq b expectedB &&
          SolidCore.Solidity.Source.wordEq c expectedC &&
          SolidCore.Solidity.Source.wordEq d expectedD)
  | _ => Except.ok false

def checkedWordValues (words : List Word) : List CoreValue :=
  words.map SolidCore.Solidity.Source.Value.word

def checkedWordValuesMatch : List CoreValue -> List Word -> Bool
  | [], [] => true
  | SolidCore.Solidity.Source.Value.word value :: values,
    expected :: expectedValues =>
      SolidCore.Solidity.Source.wordEq value expected &&
        checkedWordValuesMatch values expectedValues
  | _, _ => false

def checkedOwnCallWordAndDynamicWordArrayMatches (fuel : Nat)
    (decl : SourceContractDecl) (functionName : Name)
    (state : CoreState) (args : List CoreValue)
    (expectedHead : Word) (expectedTail : List Word) :
    Except TypeError Bool := do
  let result ←
    CheckedInput.ownCall fuel decl
      (SolidCore.Solidity.Source.CallTarget.name functionName)
      state args
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _
      [ SolidCore.Solidity.Source.Value.word head
      , SolidCore.Solidity.Source.Value.dynamicArray tail ] =>
      Except.ok
        (SolidCore.Solidity.Source.wordEq head expectedHead &&
          checkedWordValuesMatch tail expectedTail)
  | _ => Except.ok false

def checkedContractAbiOutputMatches (fuel : Nat)
    (decl : SourceContractDecl) (functionName : Name)
    (args : List CoreValue) (expected? : Option (List Byte)) :
    Except TypeError Bool := do
  let calldata ←
    ContractDecl.checkedFunctionCalldata decl functionName args
  let result ←
    ContractDecl.checkedCallCalldata fuel decl
      SolidCore.Solidity.Source.State.empty calldata
  let expected ← optionToExcept "expected ABI output" expected?
  Except.ok (result.success && result.output == expected)

def checkedContractAbiOutputFromStateMatches (fuel : Nat)
    (decl : SourceContractDecl) (functionName : Name)
    (state : CoreState) (args : List CoreValue)
    (expected? : Option (List Byte)) :
    Except TypeError Bool := do
  let calldata ←
    ContractDecl.checkedFunctionCalldata decl functionName args
  let result ←
    ContractDecl.checkedCallCalldata fuel decl state calldata
  let expected ← optionToExcept "expected ABI output" expected?
  Except.ok (result.success && result.output == expected)

def checkedGetterAbiWordOutput (expected : Word) :
    Except TypeError (List Byte) :=
  checkedAbiEncodeValues
    [SolidCore.Solidity.Source.Ty.uint256]
    [SolidCore.Solidity.Source.Value.word expected]

def checkedGetterAbiBytesOutput (expected : List Byte) :
    Except TypeError (List Byte) :=
  checkedAbiEncodeValues
    [SolidCore.Solidity.Source.Ty.bytesCalldata]
    [SolidCore.Solidity.Source.Value.bytes expected]

def checkedPublicGetterContractsAccepted : Bool :=
  Result.isOk
      (TypecheckedInput.checkedSourceUnit
        Executable.Examples.publicGetterContract) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit
        Executable.Examples.publicMappingGetterContract) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit
        Executable.Examples.bytesStringMappingKeyContract) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit
        Executable.Examples.publicArrayGetterContract) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit
        Executable.Examples.nestedPublicGetterContract) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit
        Executable.Examples.publicBytesArrayGetterContract) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit
        Executable.Examples.publicStringArrayGetterContract) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit
        Executable.Examples.publicMappingByteStringsGetterContract) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit
        Executable.Examples.publicFixedBytesArrayGetterContract) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit
        Executable.Examples.storageStringGetterContract)

def checkedPublicGetterMatches : Except TypeError Bool :=
  checkedOwnCallWordMatches 16
    Executable.Examples.publicGetterContract
    "x" Executable.Examples.publicGetterState [] 42

def checkedPublicGetterAbiMatches : Except TypeError Bool := do
  let expected ← checkedGetterAbiWordOutput 42
  checkedContractAbiOutputFromStateMatches 16
    Executable.Examples.publicGetterContract
    "x" Executable.Examples.publicGetterState [] (some expected)

def checkedPublicMappingGetterSetState : Except TypeError CoreState := do
  let result ←
    ContractDecl.checkedCall 32
      Executable.Examples.publicMappingGetterContract
      (SolidCore.Solidity.Source.CallTarget.name "set")
      SolidCore.Solidity.Source.State.empty []
  match result with
  | SolidCore.Solidity.Source.CallResult.returned state _ =>
      Except.ok state
  | _ => Except.error (executableFailure "public mapping getter set")

def checkedPublicMappingGetterMatches : Except TypeError Bool := do
  let state ← checkedPublicMappingGetterSetState
  checkedOwnCallWordMatches 32
    Executable.Examples.publicMappingGetterContract
    "m" state [SolidCore.Solidity.Source.Value.word 4] 9

def checkedPublicMappingGetterAbiMatches : Except TypeError Bool := do
  let state ← checkedPublicMappingGetterSetState
  let expected ← checkedGetterAbiWordOutput 9
  checkedContractAbiOutputFromStateMatches 32
    Executable.Examples.publicMappingGetterContract
    "m" state [SolidCore.Solidity.Source.Value.word 4] (some expected)

def checkedDirectMappingContractsAccepted : Bool :=
  Result.isOk
      (TypecheckedInput.checkedSourceUnit
        Executable.Examples.mappingContract) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit
        Executable.Examples.signedMappingKeyContract)

def checkedMappingWriteState : Except TypeError CoreState := do
  let result ←
    ContractDecl.checkedCall 32
      Executable.Examples.mappingContract
      (SolidCore.Solidity.Source.CallTarget.name "set")
      SolidCore.Solidity.Source.State.empty []
  match result with
  | SolidCore.Solidity.Source.CallResult.returned state _ =>
      Except.ok state
  | _ => Except.error (executableFailure "mapping set")

def checkedMappingReadAfterWriteMatches : Except TypeError Bool := do
  let state ← checkedMappingWriteState
  checkedOwnCallWordMatches 32
    Executable.Examples.mappingContract
    "get" state [] 9

def checkedSignedMappingKeySetState : Except TypeError CoreState := do
  let result ←
    ContractDecl.checkedCall 32
      Executable.Examples.signedMappingKeyContract
      (SolidCore.Solidity.Source.CallTarget.name "set")
      SolidCore.Solidity.Source.State.empty
      [ SolidCore.Solidity.Source.Value.int
          Executable.Examples.signedMappingKeyWord
      , SolidCore.Solidity.Source.Value.word 123 ]
  match result with
  | SolidCore.Solidity.Source.CallResult.returned state _ =>
      Except.ok state
  | _ => Except.error (executableFailure "signed mapping key set")

def checkedSignedMappingKeyReadMatches : Except TypeError Bool := do
  let state ← checkedSignedMappingKeySetState
  let slot :=
    SolidCore.Solidity.Source.mappingStorageSlot
      0 Executable.Examples.signedMappingKeyWord
  let result ←
    ContractDecl.checkedCall 32
      Executable.Examples.signedMappingKeyContract
      (SolidCore.Solidity.Source.CallTarget.name "read")
      state
      [SolidCore.Solidity.Source.Value.int
        Executable.Examples.signedMappingKeyWord]
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _
      [SolidCore.Solidity.Source.Value.word value] =>
      Except.ok
        (SolidCore.Solidity.Source.wordEq
          (state.loadSlot slot) 123 &&
          SolidCore.Solidity.Source.wordEq value 123)
  | _ => Except.ok false

def checkedBytesStringMappingSetState : Except TypeError CoreState := do
  let bytesSet ←
    ContractDecl.checkedCall 32
      Executable.Examples.bytesStringMappingKeyContract
      (SolidCore.Solidity.Source.CallTarget.name "setBytes")
      SolidCore.Solidity.Source.State.empty
      [ SolidCore.Solidity.Source.Value.bytes [1, 2, 3]
      , SolidCore.Solidity.Source.Value.word 44 ]
  let state ←
    match bytesSet with
    | SolidCore.Solidity.Source.CallResult.returned state _ =>
        Except.ok state
    | _ => Except.error (executableFailure "bytes mapping key set")
  let stringSet ←
    ContractDecl.checkedCall 32
      Executable.Examples.bytesStringMappingKeyContract
      (SolidCore.Solidity.Source.CallTarget.name "setString")
      state
      [ SolidCore.Solidity.Source.Value.bytes ("hi".toList.map Char.toNat)
      , SolidCore.Solidity.Source.Value.word 55 ]
  match stringSet with
  | SolidCore.Solidity.Source.CallResult.returned state _ =>
      Except.ok state
  | _ => Except.error (executableFailure "string mapping key set")

def checkedPublicBytesMappingGetterMatches : Except TypeError Bool := do
  let state ← checkedBytesStringMappingSetState
  checkedOwnCallWordMatches 32
    Executable.Examples.bytesStringMappingKeyContract
    "mb" state [SolidCore.Solidity.Source.Value.bytes [1, 2, 3]] 44

def checkedBytesMappingKeyReadMatches : Except TypeError Bool := do
  let state ← checkedBytesStringMappingSetState
  checkedOwnCallWordMatches 32
    Executable.Examples.bytesStringMappingKeyContract
    "readBytes" state
    [SolidCore.Solidity.Source.Value.bytes [1, 2, 3]] 44

def checkedBytesMappingDifferentKeyDefaultsToZero :
    Except TypeError Bool := do
  let state ← checkedBytesStringMappingSetState
  checkedOwnCallWordMatches 32
    Executable.Examples.bytesStringMappingKeyContract
    "readBytes" state
    [SolidCore.Solidity.Source.Value.bytes [1, 2, 4]] 0

def checkedStringMappingKeyReadMatches : Except TypeError Bool := do
  let state ← checkedBytesStringMappingSetState
  checkedOwnCallWordMatches 32
    Executable.Examples.bytesStringMappingKeyContract
    "readString" state
    [SolidCore.Solidity.Source.Value.bytes ("hi".toList.map Char.toNat)]
    55

def checkedPublicStringMappingGetterAbiMatches :
    Except TypeError Bool := do
  let state ← checkedBytesStringMappingSetState
  let expected ← checkedGetterAbiWordOutput 55
  checkedContractAbiOutputFromStateMatches 32
    Executable.Examples.bytesStringMappingKeyContract
    "ms" state
    [SolidCore.Solidity.Source.Value.bytes ("hi".toList.map Char.toNat)]
    (some expected)

def checkedPublicArrayGetterSetState : Except TypeError CoreState := do
  let result ←
    ContractDecl.checkedCall 32
      Executable.Examples.publicArrayGetterContract
      (SolidCore.Solidity.Source.CallTarget.name "set")
      SolidCore.Solidity.Source.State.empty []
  match result with
  | SolidCore.Solidity.Source.CallResult.returned state _ =>
      Except.ok state
  | _ => Except.error (executableFailure "public array getter set")

def checkedPublicDynamicArrayGetterMatches :
    Except TypeError Bool := do
  let state ← checkedPublicArrayGetterSetState
  checkedOwnCallWordMatches 32
    Executable.Examples.publicArrayGetterContract
    "items" state [SolidCore.Solidity.Source.Value.word 2] 7

def checkedPublicFixedArrayGetterAbiMatches :
    Except TypeError Bool := do
  let state ← checkedPublicArrayGetterSetState
  let expected ← checkedGetterAbiWordOutput 8
  checkedContractAbiOutputFromStateMatches 32
    Executable.Examples.publicArrayGetterContract
    "fixedItems" state [SolidCore.Solidity.Source.Value.word 1]
    (some expected)

def checkedPublicDynamicArrayGetterOutOfBoundsPanics :
    Except TypeError Bool := do
  let state ← checkedPublicArrayGetterSetState
  checkedOwnCallPanicMatches 32
    Executable.Examples.publicArrayGetterContract
    "items" state [SolidCore.Solidity.Source.Value.word 3] 0x32

def checkedPublicFixedArrayGetterOutOfBoundsPanics :
    Except TypeError Bool := do
  let state ← checkedPublicArrayGetterSetState
  checkedOwnCallPanicMatches 32
    Executable.Examples.publicArrayGetterContract
    "fixedItems" state [SolidCore.Solidity.Source.Value.word 3] 0x32

def checkedNestedMappingPublicGetterMatches :
    Except TypeError Bool :=
  checkedOwnCallWordMatches 32
    Executable.Examples.nestedPublicGetterContract
    "nested" Executable.Examples.nestedPublicGetterState
    [ SolidCore.Solidity.Source.Value.word 4
    , SolidCore.Solidity.Source.Value.word 5 ] 99

def checkedNestedMappingPublicGetterAbiMatches :
    Except TypeError Bool := do
  let expected ← checkedGetterAbiWordOutput 99
  checkedContractAbiOutputFromStateMatches 32
    Executable.Examples.nestedPublicGetterContract
    "nested" Executable.Examples.nestedPublicGetterState
    [ SolidCore.Solidity.Source.Value.word 4
    , SolidCore.Solidity.Source.Value.word 5 ] (some expected)

def checkedMappingArrayPublicGetterMatches :
    Except TypeError Bool :=
  checkedOwnCallWordMatches 32
    Executable.Examples.nestedPublicGetterContract
    "buckets" Executable.Examples.nestedPublicGetterState
    [ SolidCore.Solidity.Source.Value.word 7
    , SolidCore.Solidity.Source.Value.word 1 ] 88

def checkedMappingArrayPublicGetterOutOfBoundsPanics :
    Except TypeError Bool :=
  checkedOwnCallPanicMatches 32
    Executable.Examples.nestedPublicGetterContract
    "buckets" Executable.Examples.nestedPublicGetterState
    [ SolidCore.Solidity.Source.Value.word 7
    , SolidCore.Solidity.Source.Value.word 2 ] 0x32

def checkedPublicBytesArrayGetterMatches :
    Except TypeError Bool :=
  checkedOwnCallBytesMatches 32
    Executable.Examples.publicBytesArrayGetterContract
    "blobs" Executable.Examples.publicBytesArrayGetterState
    [SolidCore.Solidity.Source.Value.word 1] [10, 20, 30]

def checkedPublicBytesArrayGetterAbiMatches :
    Except TypeError Bool := do
  let expected ← checkedGetterAbiBytesOutput [10, 20, 30]
  checkedContractAbiOutputFromStateMatches 32
    Executable.Examples.publicBytesArrayGetterContract
    "blobs" Executable.Examples.publicBytesArrayGetterState
    [SolidCore.Solidity.Source.Value.word 1] (some expected)

def checkedPublicStringArrayGetterMatches :
    Except TypeError Bool :=
  checkedOwnCallBytesMatches 32
    Executable.Examples.publicStringArrayGetterContract
    "names" Executable.Examples.publicStringArrayGetterState
    [SolidCore.Solidity.Source.Value.word 0] [104, 105]

def checkedPublicStringArrayGetterAbiMatches :
    Except TypeError Bool := do
  let expected ← checkedGetterAbiBytesOutput [104, 105]
  checkedContractAbiOutputFromStateMatches 32
    Executable.Examples.publicStringArrayGetterContract
    "names" Executable.Examples.publicStringArrayGetterState
    [SolidCore.Solidity.Source.Value.word 0] (some expected)

def checkedPublicMappingBytesGetterMatches :
    Except TypeError Bool :=
  checkedOwnCallBytesMatches 32
    Executable.Examples.publicMappingByteStringsGetterContract
    "raw" Executable.Examples.publicMappingByteStringsGetterState
    [SolidCore.Solidity.Source.Value.word 4] [1, 2]

def checkedPublicMappingStringGetterAbiMatches :
    Except TypeError Bool := do
  let expected ← checkedGetterAbiBytesOutput [111, 107]
  checkedContractAbiOutputFromStateMatches 32
    Executable.Examples.publicMappingByteStringsGetterContract
    "text" Executable.Examples.publicMappingByteStringsGetterState
    [SolidCore.Solidity.Source.Value.word 5] (some expected)

def checkedPublicFixedBytesArrayGetterMatches :
    Except TypeError Bool :=
  checkedOwnCallBytesMatches 32
    Executable.Examples.publicFixedBytesArrayGetterContract
    "fixedBlobs" Executable.Examples.publicFixedBytesArrayGetterState
    [SolidCore.Solidity.Source.Value.word 1] [7, 8, 9]

def checkedPublicFixedBytesArrayGetterAbiMatches :
    Except TypeError Bool := do
  let expected ← checkedGetterAbiBytesOutput [7, 8, 9]
  checkedContractAbiOutputFromStateMatches 32
    Executable.Examples.publicFixedBytesArrayGetterContract
    "fixedBlobs" Executable.Examples.publicFixedBytesArrayGetterState
    [SolidCore.Solidity.Source.Value.word 1] (some expected)

def checkedPublicFixedBytesArrayGetterOutOfBoundsPanics :
    Except TypeError Bool :=
  checkedOwnCallPanicMatches 32
    Executable.Examples.publicFixedBytesArrayGetterContract
    "fixedBlobs" Executable.Examples.publicFixedBytesArrayGetterState
    [SolidCore.Solidity.Source.Value.word 2] 0x32

def checkedStorageStringSetState : Except TypeError CoreState := do
  let result ←
    ContractDecl.checkedCall 32
      Executable.Examples.storageStringGetterContract
      (SolidCore.Solidity.Source.CallTarget.name "setGreeting")
      SolidCore.Solidity.Source.State.empty
      [ SolidCore.Solidity.Source.Value.bytes
          Executable.Examples.storageStringGreetingBytes ]
  match result with
  | SolidCore.Solidity.Source.CallResult.returned state _ =>
      Except.ok state
  | _ => Except.error (executableFailure "storage string set")

def checkedStorageStringPublicGetterMatches :
    Except TypeError Bool := do
  let state ← checkedStorageStringSetState
  checkedOwnCallBytesMatches 32
    Executable.Examples.storageStringGetterContract
    "greeting" state [] Executable.Examples.storageStringGreetingBytes

def checkedStorageStringPublicGetterAbiMatches :
    Except TypeError Bool := do
  let state ← checkedStorageStringSetState
  let expected ←
    checkedGetterAbiBytesOutput
      Executable.Examples.storageStringGreetingBytes
  checkedContractAbiOutputFromStateMatches 32
    Executable.Examples.storageStringGetterContract
    "greeting" state [] (some expected)

def checkedStorageStringClearState : Except TypeError CoreState := do
  let state ← checkedStorageStringSetState
  let result ←
    ContractDecl.checkedCall 32
      Executable.Examples.storageStringGetterContract
      (SolidCore.Solidity.Source.CallTarget.name "clearGreeting")
      state []
  match result with
  | SolidCore.Solidity.Source.CallResult.returned state _ =>
      Except.ok state
  | _ => Except.error (executableFailure "storage string clear")

def checkedStorageStringClearGetterEmpty :
    Except TypeError Bool := do
  let state ← checkedStorageStringClearState
  checkedOwnCallBytesMatches 32
    Executable.Examples.storageStringGetterContract
    "greeting" state [] []

def checkedStorageBytesSetState : Except TypeError CoreState := do
  let result ←
    ContractDecl.checkedCall 32
      Executable.Examples.storageStringGetterContract
      (SolidCore.Solidity.Source.CallTarget.name "setRaw")
      SolidCore.Solidity.Source.State.empty
      [SolidCore.Solidity.Source.Value.bytes [1, 2, 3]]
  match result with
  | SolidCore.Solidity.Source.CallResult.returned state _ =>
      Except.ok state
  | _ => Except.error (executableFailure "storage bytes set")

def checkedStorageBytesPublicGetterMatches :
    Except TypeError Bool := do
  let state ← checkedStorageBytesSetState
  checkedOwnCallBytesMatches 32
    Executable.Examples.storageStringGetterContract
    "raw" state [] [1, 2, 3]

def checkedOwnCallWordBytesWordMatches (fuel : Nat)
    (decl : SourceContractDecl) (functionName : Name)
    (state : CoreState) (args : List CoreValue)
    (expectedWord : Word) (expectedBytes : List Byte)
    (expectedFlag : Word) : Except TypeError Bool := do
  let result ←
    CheckedInput.ownCall fuel decl
      (SolidCore.Solidity.Source.CallTarget.name functionName)
      state args
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _
      [ SolidCore.Solidity.Source.Value.word value
      , SolidCore.Solidity.Source.Value.bytes bytes
      , SolidCore.Solidity.Source.Value.word flag ] =>
      Except.ok
        (SolidCore.Solidity.Source.wordEq value expectedWord &&
          bytes == expectedBytes &&
          SolidCore.Solidity.Source.wordEq flag expectedFlag)
  | _ => Except.ok false

def checkedGetterAbiWordBytesBoolOutput (expectedWord : Word)
    (expectedBytes : List Byte) (expectedFlag : Word) :
    Except TypeError (List Byte) :=
  checkedAbiEncodeValues
    [ SolidCore.Solidity.Source.Ty.uint256
    , SolidCore.Solidity.Source.Ty.bytesCalldata
    , SolidCore.Solidity.Source.Ty.bool ]
    [ SolidCore.Solidity.Source.Value.word expectedWord
    , SolidCore.Solidity.Source.Value.bytes expectedBytes
    , SolidCore.Solidity.Source.Value.word expectedFlag ]

def checkedPublicStructGetterContractsAccepted : Bool :=
  Result.isOk
      (TypecheckedInput.checkedSourceUnit
        Executable.Examples.publicStructGetterContract) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit
        Executable.Examples.publicNestedStructGetterContract) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit
        Executable.Examples.publicMappingStructGetterContract) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit
        Executable.Examples.publicArrayStructGetterContract) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit
        Executable.Examples.publicFixedArrayStructGetterContract) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit
        Executable.Examples.deleteFixedArrayStructContract)

def checkedPublicStructGetterTypeShapesAccepted : Bool :=
  publicStructGetterShapeReturns &&
    publicNestedStructGetterShapeReturns &&
    publicMappingStructGetterShapeReturns &&
    publicArrayStructGetterShapeReturns &&
    publicFixedArrayStructGetterShapeReturns

def checkedPublicStructGetterLayoutMatches : Bool :=
  Executable.Examples.publicStructGetterCoreLayoutSpanMatches &&
    Executable.Examples.publicArrayStructGetterElementSlotUsesSpan &&
    Executable.Examples.publicFixedArrayStructGetterElementSlotUsesSpan

def checkedPublicStructGetterMatches : Except TypeError Bool :=
  checkedOwnCallWordBytesWordMatches 32
    Executable.Examples.publicStructGetterContract
    "entry" Executable.Examples.publicStructGetterState []
    123 [65, 66] 1

def checkedPublicStructGetterAbiMatches : Except TypeError Bool := do
  let expected ← checkedGetterAbiWordBytesBoolOutput 123 [65, 66] 1
  checkedContractAbiOutputFromStateMatches 32
    Executable.Examples.publicStructGetterContract
    "entry" Executable.Examples.publicStructGetterState []
    (some expected)

def checkedPublicNestedStructGetterMatches : Except TypeError Bool := do
  let result ←
    CheckedInput.ownCall 32
      Executable.Examples.publicNestedStructGetterContract
      (SolidCore.Solidity.Source.CallTarget.name "entry")
      Executable.Examples.publicNestedStructGetterState []
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _
      [ SolidCore.Solidity.Source.Value.word amount
      , SolidCore.Solidity.Source.Value.tuple
          [ SolidCore.Solidity.Source.Value.word inner
          , SolidCore.Solidity.Source.Value.word flag ]
      , SolidCore.Solidity.Source.Value.bytes raw ] =>
      Except.ok
        (SolidCore.Solidity.Source.wordEq amount 33 &&
          SolidCore.Solidity.Source.wordEq inner 44 &&
          SolidCore.Solidity.Source.wordEq flag 1 &&
          raw == [120, 121])
  | _ => Except.ok false

def checkedPublicNestedStructGetterAbiMatches :
    Except TypeError Bool := do
  let expected ←
    checkedAbiEncodeValues
      [ SolidCore.Solidity.Source.Ty.uint256
      , SolidCore.Solidity.Source.Ty.tuple
          [ SolidCore.Solidity.Source.Ty.uint256
          , SolidCore.Solidity.Source.Ty.bool ]
      , SolidCore.Solidity.Source.Ty.bytesCalldata ]
      [ SolidCore.Solidity.Source.Value.word 33
      , SolidCore.Solidity.Source.Value.tuple
          [ SolidCore.Solidity.Source.Value.word 44
          , SolidCore.Solidity.Source.Value.word 1 ]
      , SolidCore.Solidity.Source.Value.bytes [120, 121] ]
  checkedContractAbiOutputFromStateMatches 32
    Executable.Examples.publicNestedStructGetterContract
    "entry" Executable.Examples.publicNestedStructGetterState []
    (some expected)

def checkedPublicMappingStructGetterMatches :
    Except TypeError Bool :=
  checkedOwnCallWordBytesWordMatches 32
    Executable.Examples.publicMappingStructGetterContract
    "entries" Executable.Examples.publicMappingStructGetterState
    [SolidCore.Solidity.Source.Value.word 11] 456 [70, 71, 72] 1

def checkedPublicMappingStructGetterAbiMatches :
    Except TypeError Bool := do
  let expected ← checkedGetterAbiWordBytesBoolOutput 456 [70, 71, 72] 1
  checkedContractAbiOutputFromStateMatches 32
    Executable.Examples.publicMappingStructGetterContract
    "entries" Executable.Examples.publicMappingStructGetterState
    [SolidCore.Solidity.Source.Value.word 11] (some expected)

def checkedPublicArrayStructGetterMatches :
    Except TypeError Bool :=
  checkedOwnCallWordBytesWordMatches 32
    Executable.Examples.publicArrayStructGetterContract
    "records" Executable.Examples.publicArrayStructGetterState
    [SolidCore.Solidity.Source.Value.word 1] 789 [80, 81] 1

def checkedPublicArrayStructGetterAbiMatches :
    Except TypeError Bool := do
  let expected ← checkedGetterAbiWordBytesBoolOutput 789 [80, 81] 1
  checkedContractAbiOutputFromStateMatches 32
    Executable.Examples.publicArrayStructGetterContract
    "records" Executable.Examples.publicArrayStructGetterState
    [SolidCore.Solidity.Source.Value.word 1] (some expected)

def checkedPublicArrayStructGetterOutOfBoundsPanics :
    Except TypeError Bool :=
  checkedOwnCallPanicMatches 32
    Executable.Examples.publicArrayStructGetterContract
    "records" Executable.Examples.publicArrayStructGetterState
    [SolidCore.Solidity.Source.Value.word 2] 0x32

def checkedPublicFixedArrayStructGetterMatches :
    Except TypeError Bool :=
  checkedOwnCallWordBytesWordMatches 32
    Executable.Examples.publicFixedArrayStructGetterContract
    "fixedRecords" Executable.Examples.publicFixedArrayStructGetterState
    [SolidCore.Solidity.Source.Value.word 1] 321 [90, 91, 92, 93] 1

def checkedPublicFixedArrayStructGetterAbiMatches :
    Except TypeError Bool := do
  let expected ←
    checkedGetterAbiWordBytesBoolOutput 321 [90, 91, 92, 93] 1
  checkedContractAbiOutputFromStateMatches 32
    Executable.Examples.publicFixedArrayStructGetterContract
    "fixedRecords" Executable.Examples.publicFixedArrayStructGetterState
    [SolidCore.Solidity.Source.Value.word 1] (some expected)

def checkedPublicFixedArrayStructGetterOutOfBoundsPanics :
    Except TypeError Bool :=
  checkedOwnCallPanicMatches 32
    Executable.Examples.publicFixedArrayStructGetterContract
    "fixedRecords" Executable.Examples.publicFixedArrayStructGetterState
    [SolidCore.Solidity.Source.Value.word 2] 0x32

def checkedDeleteFixedArrayStructState :
    Except TypeError CoreState := do
  let result ←
    ContractDecl.checkedCall 32
      Executable.Examples.deleteFixedArrayStructContract
      (SolidCore.Solidity.Source.CallTarget.name "clear")
      Executable.Examples.publicFixedArrayStructGetterState []
  match result with
  | SolidCore.Solidity.Source.CallResult.returned state _ =>
      Except.ok state
  | _ => Except.error (executableFailure "delete fixed struct array")

def checkedDeleteFixedArrayStructClearsElement :
    Except TypeError Bool := do
  let state ← checkedDeleteFixedArrayStructState
  checkedOwnCallWordBytesWordMatches 32
    Executable.Examples.deleteFixedArrayStructContract
    "fixedRecords" state [SolidCore.Solidity.Source.Value.word 1]
    0 [] 0

def checkedPublicGetterStorageSemanticsMatch :
    Except TypeError Bool := do
  let publicGetter ← checkedPublicGetterMatches
  let publicGetterAbi ← checkedPublicGetterAbiMatches
  let publicMapping ← checkedPublicMappingGetterMatches
  let publicMappingAbi ← checkedPublicMappingGetterAbiMatches
  let mappingRead ← checkedMappingReadAfterWriteMatches
  let signedMapping ← checkedSignedMappingKeyReadMatches
  let bytesMappingGetter ← checkedPublicBytesMappingGetterMatches
  let bytesMappingRead ← checkedBytesMappingKeyReadMatches
  let bytesMappingDefault ← checkedBytesMappingDifferentKeyDefaultsToZero
  let stringMappingRead ← checkedStringMappingKeyReadMatches
  let stringMappingAbi ← checkedPublicStringMappingGetterAbiMatches
  let dynamicArrayGetter ← checkedPublicDynamicArrayGetterMatches
  let fixedArrayGetterAbi ← checkedPublicFixedArrayGetterAbiMatches
  let dynamicArrayOob ← checkedPublicDynamicArrayGetterOutOfBoundsPanics
  let fixedArrayOob ← checkedPublicFixedArrayGetterOutOfBoundsPanics
  let nestedMapping ← checkedNestedMappingPublicGetterMatches
  let nestedMappingAbi ← checkedNestedMappingPublicGetterAbiMatches
  let mappingArray ← checkedMappingArrayPublicGetterMatches
  let mappingArrayOob ← checkedMappingArrayPublicGetterOutOfBoundsPanics
  let bytesArray ← checkedPublicBytesArrayGetterMatches
  let bytesArrayAbi ← checkedPublicBytesArrayGetterAbiMatches
  let stringArray ← checkedPublicStringArrayGetterMatches
  let stringArrayAbi ← checkedPublicStringArrayGetterAbiMatches
  let mappingBytes ← checkedPublicMappingBytesGetterMatches
  let mappingStringAbi ← checkedPublicMappingStringGetterAbiMatches
  let fixedBytesArray ← checkedPublicFixedBytesArrayGetterMatches
  let fixedBytesArrayAbi ← checkedPublicFixedBytesArrayGetterAbiMatches
  let fixedBytesArrayOob ←
    checkedPublicFixedBytesArrayGetterOutOfBoundsPanics
  let storageString ← checkedStorageStringPublicGetterMatches
  let storageStringAbi ← checkedStorageStringPublicGetterAbiMatches
  let storageStringClear ← checkedStorageStringClearGetterEmpty
  let storageBytes ← checkedStorageBytesPublicGetterMatches
  let structGetter ← checkedPublicStructGetterMatches
  let structGetterAbi ← checkedPublicStructGetterAbiMatches
  let nestedStructGetter ← checkedPublicNestedStructGetterMatches
  let nestedStructGetterAbi ← checkedPublicNestedStructGetterAbiMatches
  let mappingStructGetter ← checkedPublicMappingStructGetterMatches
  let mappingStructGetterAbi ← checkedPublicMappingStructGetterAbiMatches
  let arrayStructGetter ← checkedPublicArrayStructGetterMatches
  let arrayStructGetterAbi ← checkedPublicArrayStructGetterAbiMatches
  let arrayStructOob ← checkedPublicArrayStructGetterOutOfBoundsPanics
  let fixedArrayStructGetter ← checkedPublicFixedArrayStructGetterMatches
  let fixedArrayStructGetterAbi ←
    checkedPublicFixedArrayStructGetterAbiMatches
  let fixedArrayStructOob ←
    checkedPublicFixedArrayStructGetterOutOfBoundsPanics
  let fixedArrayStructDelete ← checkedDeleteFixedArrayStructClearsElement
  Except.ok
    (checkedPublicGetterContractsAccepted &&
      checkedDirectMappingContractsAccepted &&
      checkedPublicStructGetterContractsAccepted &&
      checkedPublicStructGetterTypeShapesAccepted &&
      checkedPublicStructGetterLayoutMatches &&
      publicGetter && publicGetterAbi &&
      publicMapping && publicMappingAbi &&
      mappingRead && signedMapping &&
      bytesMappingGetter && bytesMappingRead &&
      bytesMappingDefault && stringMappingRead && stringMappingAbi &&
      dynamicArrayGetter && fixedArrayGetterAbi &&
      dynamicArrayOob && fixedArrayOob &&
      nestedMapping && nestedMappingAbi &&
      mappingArray && mappingArrayOob &&
      bytesArray && bytesArrayAbi &&
      stringArray && stringArrayAbi &&
      mappingBytes && mappingStringAbi &&
      fixedBytesArray && fixedBytesArrayAbi && fixedBytesArrayOob &&
      storageString && storageStringAbi && storageStringClear &&
      storageBytes &&
      structGetter && structGetterAbi &&
      nestedStructGetter && nestedStructGetterAbi &&
      mappingStructGetter && mappingStructGetterAbi &&
      arrayStructGetter && arrayStructGetterAbi && arrayStructOob &&
      fixedArrayStructGetter && fixedArrayStructGetterAbi &&
      fixedArrayStructOob && fixedArrayStructDelete)

def checkedStructArrayStorageContractsAccepted : Bool :=
  Result.isOk
      (TypecheckedInput.checkedSourceUnit
        Executable.Examples.assignFixedStructArrayContract) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit
        Executable.Examples.assignDynamicStructArrayContract) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit
        Executable.Examples.indexAssignFixedStructArrayContract) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit
        Executable.Examples.indexAssignDynamicStructArrayContract) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit
        Executable.Examples.indexAssignMappingStructContract) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit
        Executable.Examples.pushStructArrayContract) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit
        Executable.Examples.deleteNestedStructArrayContract) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit
        Executable.Examples.assignNestedDynamicStructArrayContract) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit
        Executable.Examples.assignNestedStructMappingContract)

def checkedAssignFixedStructArrayState :
    Except TypeError CoreState :=
  checkedOwnCallState 64
    Executable.Examples.assignFixedStructArrayContract
    "set" SolidCore.Solidity.Source.State.empty
    [Executable.Examples.assignFixedStructArrayInput]

def checkedAssignFixedStructArrayGetterMatches :
    Except TypeError Bool := do
  let state ← checkedAssignFixedStructArrayState
  checkedOwnCallWordPairMatches 32
    Executable.Examples.assignFixedStructArrayContract
    "records" state [SolidCore.Solidity.Source.Value.word 1] 20 0

def checkedAssignDynamicStructArrayState :
    Except TypeError CoreState :=
  checkedOwnCallState 64
    Executable.Examples.assignDynamicStructArrayContract
    "set" SolidCore.Solidity.Source.State.empty
    [Executable.Examples.assignDynamicStructArrayInput]

def checkedAssignDynamicStructArrayGetterMatches :
    Except TypeError Bool := do
  let state ← checkedAssignDynamicStructArrayState
  checkedOwnCallWordPairMatches 32
    Executable.Examples.assignDynamicStructArrayContract
    "records" state [SolidCore.Solidity.Source.Value.word 1] 20 0

def checkedIndexAssignFixedStructArrayState :
    Except TypeError CoreState :=
  checkedOwnCallState 64
    Executable.Examples.indexAssignFixedStructArrayContract
    "set" SolidCore.Solidity.Source.State.empty
    [Executable.Examples.indexAssignStructValue]

def checkedIndexAssignFixedStructArrayGetterMatches :
    Except TypeError Bool := do
  let state ← checkedIndexAssignFixedStructArrayState
  checkedOwnCallWordPairMatches 32
    Executable.Examples.indexAssignFixedStructArrayContract
    "records" state [SolidCore.Solidity.Source.Value.word 1] 20 0

def checkedIndexAssignDynamicStructArrayState :
    Except TypeError CoreState :=
  checkedOwnCallState 64
    Executable.Examples.indexAssignDynamicStructArrayContract
    "set" (SolidCore.Solidity.Source.State.empty.storeSlot 0 2)
    [Executable.Examples.indexAssignStructValue]

def checkedIndexAssignDynamicStructArrayGetterMatches :
    Except TypeError Bool := do
  let state ← checkedIndexAssignDynamicStructArrayState
  checkedOwnCallWordPairMatches 32
    Executable.Examples.indexAssignDynamicStructArrayContract
    "records" state [SolidCore.Solidity.Source.Value.word 1] 20 0

def checkedIndexAssignMappingStructState :
    Except TypeError CoreState :=
  checkedOwnCallState 64
    Executable.Examples.indexAssignMappingStructContract
    "set" SolidCore.Solidity.Source.State.empty
    [ SolidCore.Solidity.Source.Value.word 7
    , Executable.Examples.indexAssignStructValue ]

def checkedIndexAssignMappingStructGetterMatches :
    Except TypeError Bool := do
  let state ← checkedIndexAssignMappingStructState
  checkedOwnCallWordPairMatches 32
    Executable.Examples.indexAssignMappingStructContract
    "entries" state [SolidCore.Solidity.Source.Value.word 7] 20 0

def checkedPushStructArrayValueState :
    Except TypeError CoreState :=
  checkedOwnCallState 64
    Executable.Examples.pushStructArrayContract
    "pushValue" SolidCore.Solidity.Source.State.empty
    [Executable.Examples.indexAssignStructValue]

def checkedPushStructArrayValueGetterMatches :
    Except TypeError Bool := do
  let state ← checkedPushStructArrayValueState
  checkedOwnCallWordPairMatches 32
    Executable.Examples.pushStructArrayContract
    "records" state [SolidCore.Solidity.Source.Value.word 0] 20 0

def checkedPushStructArrayDefaultState :
    Except TypeError CoreState :=
  checkedOwnCallState 64
    Executable.Examples.pushStructArrayContract
    "pushDefault" Executable.Examples.pushStructArrayStaleState []

def checkedPushStructArrayDefaultClearsElement :
    Except TypeError Bool := do
  let state ← checkedPushStructArrayDefaultState
  checkedOwnCallWordPairMatches 32
    Executable.Examples.pushStructArrayContract
    "records" state [SolidCore.Solidity.Source.Value.word 0] 0 0

def checkedStructArrayElementSlot : Word :=
  let elementLayout :=
    SolidCore.Solidity.Source.StorageLayout.struct
      [ SolidCore.Solidity.Source.StorageLayout.scalar
          SolidCore.Solidity.Source.Ty.uint256
      , SolidCore.Solidity.Source.StorageLayout.scalar
          SolidCore.Solidity.Source.Ty.bool ]
  SolidCore.Solidity.Source.dynamicArrayLayoutStorageSlot
    0 0 elementLayout

def checkedPopStructArrayState : Except TypeError CoreState :=
  checkedOwnCallState 64
    Executable.Examples.pushStructArrayContract
    "popOne" Executable.Examples.popStructArrayInitialState []

def checkedPopStructArrayClearsElement : Except TypeError Bool := do
  let state ← checkedPopStructArrayState
  Except.ok
    (SolidCore.Solidity.Source.wordEq (state.loadSlot 0) 0 &&
      SolidCore.Solidity.Source.wordEq
        (state.loadSlot checkedStructArrayElementSlot) 0 &&
      SolidCore.Solidity.Source.wordEq
        (state.loadSlot
          (SolidCore.Solidity.Source.fixedArrayStorageSlot
            checkedStructArrayElementSlot 1)) 0)

def checkedDeleteDynamicStructArrayState :
    Except TypeError CoreState :=
  checkedOwnCallState 64
    Executable.Examples.pushStructArrayContract
    "deleteAll" Executable.Examples.popStructArrayInitialState []

def checkedDeleteDynamicStructArrayClearsElement :
    Except TypeError Bool := do
  let state ← checkedDeleteDynamicStructArrayState
  Except.ok
    (SolidCore.Solidity.Source.wordEq (state.loadSlot 0) 0 &&
      SolidCore.Solidity.Source.wordEq
        (state.loadSlot checkedStructArrayElementSlot) 0 &&
      SolidCore.Solidity.Source.wordEq
        (state.loadSlot
          (SolidCore.Solidity.Source.fixedArrayStorageSlot
            checkedStructArrayElementSlot 1)) 0)

def checkedDeleteNestedDynamicStructArrayState :
    Except TypeError CoreState :=
  checkedOwnCallState 96
    Executable.Examples.deleteNestedStructArrayContract
    "clearDynamic"
    Executable.Examples.deleteNestedDynamicStructArrayInitialState []

def checkedDeleteNestedDynamicStructArrayClearsNestedData :
    Except TypeError Bool := do
  let state ← checkedDeleteNestedDynamicStructArrayState
  let recordSlot :=
    SolidCore.Solidity.Source.dynamicArrayLayoutStorageSlot
      0 0 Executable.Examples.nestedDynamicFieldStructLayout
  let nestedSlot :=
    SolidCore.Solidity.Source.fixedArrayStorageSlot recordSlot 1
  Except.ok
    (SolidCore.Solidity.Source.wordEq (state.loadSlot 0) 0 &&
      SolidCore.Solidity.Source.wordEq (state.loadSlot recordSlot) 0 &&
      SolidCore.Solidity.Source.wordEq (state.loadSlot nestedSlot) 0 &&
      SolidCore.Solidity.Source.wordEq
        (state.loadSlot
          (SolidCore.Solidity.Source.dynamicArrayStorageSlot
            nestedSlot 0)) 0)

def checkedDeleteNestedFixedStructArrayState :
    Except TypeError CoreState :=
  checkedOwnCallState 96
    Executable.Examples.deleteNestedStructArrayContract
    "clearFixed"
    Executable.Examples.deleteNestedFixedStructArrayInitialState []

def checkedDeleteNestedFixedStructArrayClearsNestedData :
    Except TypeError Bool := do
  let state ← checkedDeleteNestedFixedStructArrayState
  let recordSlot :=
    SolidCore.Solidity.Source.fixedArrayLayoutStorageSlot
      1 1 Executable.Examples.nestedDynamicFieldStructLayout
  let nestedSlot :=
    SolidCore.Solidity.Source.fixedArrayStorageSlot recordSlot 1
  Except.ok
    (SolidCore.Solidity.Source.wordEq (state.loadSlot recordSlot) 0 &&
      SolidCore.Solidity.Source.wordEq (state.loadSlot nestedSlot) 0 &&
      SolidCore.Solidity.Source.wordEq
        (state.loadSlot
          (SolidCore.Solidity.Source.dynamicArrayStorageSlot
            nestedSlot 0)) 0)

def checkedAssignNestedDynamicStructArrayState :
    Except TypeError CoreState :=
  checkedOwnCallState 96
    Executable.Examples.assignNestedDynamicStructArrayContract
    "set" Executable.Examples.assignNestedDynamicStructArrayInitialState
    [Executable.Examples.assignNestedDynamicStructArrayInput]

def checkedAssignNestedDynamicStructArrayClearsTail :
    Except TypeError Bool := do
  let state ← checkedAssignNestedDynamicStructArrayState
  let recordSlot :=
    SolidCore.Solidity.Source.dynamicArrayLayoutStorageSlot
      0 1 Executable.Examples.nestedDynamicFieldStructLayout
  let nestedSlot :=
    SolidCore.Solidity.Source.fixedArrayStorageSlot recordSlot 1
  Except.ok
    (SolidCore.Solidity.Source.wordEq (state.loadSlot 0) 1 &&
      SolidCore.Solidity.Source.wordEq (state.loadSlot recordSlot) 0 &&
      SolidCore.Solidity.Source.wordEq (state.loadSlot nestedSlot) 0 &&
      SolidCore.Solidity.Source.wordEq
        (state.loadSlot
          (SolidCore.Solidity.Source.dynamicArrayStorageSlot
            nestedSlot 0)) 0)

def checkedAssignNestedStructMappingState :
    Except TypeError CoreState :=
  checkedOwnCallState 96
    Executable.Examples.assignNestedStructMappingContract
    "set" Executable.Examples.assignNestedStructMappingInitialState
    [ SolidCore.Solidity.Source.Value.word 7
    , Executable.Examples.assignNestedStructMappingInput ]

def checkedAssignNestedStructMappingClearsNestedTail :
    Except TypeError Bool := do
  let state ← checkedAssignNestedStructMappingState
  let entrySlot :=
    SolidCore.Solidity.Source.mappingStorageSlot 0 7
  let nestedSlot :=
    SolidCore.Solidity.Source.fixedArrayStorageSlot entrySlot 1
  Except.ok
    (SolidCore.Solidity.Source.wordEq (state.loadSlot entrySlot) 11 &&
      SolidCore.Solidity.Source.wordEq (state.loadSlot nestedSlot) 1 &&
      SolidCore.Solidity.Source.wordEq
        (state.loadSlot
          (SolidCore.Solidity.Source.dynamicArrayStorageSlot
            nestedSlot 0)) 5 &&
      SolidCore.Solidity.Source.wordEq
        (state.loadSlot
          (SolidCore.Solidity.Source.dynamicArrayStorageSlot
            nestedSlot 1)) 0)

def checkedIndexedDynamicArrayStorageContractsAccepted : Bool :=
  Result.isOk
      (TypecheckedInput.checkedSourceUnit
        Executable.Examples.indexedDynamicArrayAssignmentContract) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit
        Executable.Examples.deleteNestedIndexedStorageContract) &&
    indexedDynamicArrayAssignmentAccepted &&
    deleteNestedIndexedStorageAccepted

def checkedIndexedDynamicArrayInnerSlot : Word :=
  SolidCore.Solidity.Source.dynamicArrayLayoutStorageSlot
    0 0
    (SolidCore.Solidity.Source.StorageLayout.dynamicArray
      (SolidCore.Solidity.Source.StorageLayout.scalar
        SolidCore.Solidity.Source.Ty.uint256))

def checkedIndexedDynamicArrayAssignmentMatrixState :
    Except TypeError CoreState :=
  checkedOwnCallState 96
    Executable.Examples.indexedDynamicArrayAssignmentContract
    "setMatrix"
    Executable.Examples.indexedDynamicArrayAssignmentMatrixInitialState
    [ SolidCore.Solidity.Source.Value.word 0
    , Executable.Examples.indexedDynamicArrayShortInput ]

def checkedIndexedDynamicArrayAssignmentMatrixClearsTail :
    Except TypeError Bool := do
  let state ← checkedIndexedDynamicArrayAssignmentMatrixState
  Except.ok
    (SolidCore.Solidity.Source.wordEq
        (state.loadSlot checkedIndexedDynamicArrayInnerSlot) 1 &&
      SolidCore.Solidity.Source.wordEq
        (state.loadSlot
          (SolidCore.Solidity.Source.dynamicArrayStorageSlot
            checkedIndexedDynamicArrayInnerSlot 0)) 5 &&
      SolidCore.Solidity.Source.wordEq
        (state.loadSlot
          (SolidCore.Solidity.Source.dynamicArrayStorageSlot
            checkedIndexedDynamicArrayInnerSlot 1)) 0)

def checkedIndexedDynamicArrayBucketSlot : Word :=
  SolidCore.Solidity.Source.mappingStorageSlot 1 7

def checkedIndexedDynamicArrayAssignmentMappingState :
    Except TypeError CoreState :=
  checkedOwnCallState 96
    Executable.Examples.indexedDynamicArrayAssignmentContract
    "setBucket"
    Executable.Examples.indexedDynamicArrayAssignmentMappingInitialState
    [ SolidCore.Solidity.Source.Value.word 7
    , Executable.Examples.indexedDynamicArrayShortInput ]

def checkedIndexedDynamicArrayAssignmentMappingClearsTail :
    Except TypeError Bool := do
  let state ← checkedIndexedDynamicArrayAssignmentMappingState
  Except.ok
    (SolidCore.Solidity.Source.wordEq
        (state.loadSlot checkedIndexedDynamicArrayBucketSlot) 1 &&
      SolidCore.Solidity.Source.wordEq
        (state.loadSlot
          (SolidCore.Solidity.Source.dynamicArrayStorageSlot
            checkedIndexedDynamicArrayBucketSlot 0)) 5 &&
      SolidCore.Solidity.Source.wordEq
        (state.loadSlot
          (SolidCore.Solidity.Source.dynamicArrayStorageSlot
            checkedIndexedDynamicArrayBucketSlot 1)) 0)

def checkedDeleteNestedIndexedStorageMatrixState :
    Except TypeError CoreState :=
  checkedOwnCallState 96
    Executable.Examples.deleteNestedIndexedStorageContract
    "clearMatrix"
    Executable.Examples.deleteNestedIndexedStorageMatrixInitialState
    [SolidCore.Solidity.Source.Value.word 0]

def checkedDeleteNestedIndexedStorageMatrixClearsInnerArray :
    Except TypeError Bool := do
  let state ← checkedDeleteNestedIndexedStorageMatrixState
  Except.ok
    (SolidCore.Solidity.Source.wordEq (state.loadSlot 0) 1 &&
      SolidCore.Solidity.Source.wordEq
        (state.loadSlot checkedIndexedDynamicArrayInnerSlot) 0 &&
      SolidCore.Solidity.Source.wordEq
        (state.loadSlot
          (SolidCore.Solidity.Source.dynamicArrayStorageSlot
            checkedIndexedDynamicArrayInnerSlot 0)) 0 &&
      SolidCore.Solidity.Source.wordEq
        (state.loadSlot
          (SolidCore.Solidity.Source.dynamicArrayStorageSlot
            checkedIndexedDynamicArrayInnerSlot 1)) 0)

def checkedDeleteNestedIndexedStorageEntrySlot : Word :=
  SolidCore.Solidity.Source.mappingStorageSlot 1 7

def checkedDeleteNestedIndexedStorageNestedSlot : Word :=
  SolidCore.Solidity.Source.fixedArrayStorageSlot
    checkedDeleteNestedIndexedStorageEntrySlot 1

def checkedDeleteNestedIndexedStorageMappingState :
    Except TypeError CoreState :=
  checkedOwnCallState 96
    Executable.Examples.deleteNestedIndexedStorageContract
    "clearEntry"
    Executable.Examples.deleteNestedIndexedStorageMappingInitialState
    [SolidCore.Solidity.Source.Value.word 7]

def checkedDeleteNestedIndexedStorageMappingClearsNestedData :
    Except TypeError Bool := do
  let state ← checkedDeleteNestedIndexedStorageMappingState
  Except.ok
    (SolidCore.Solidity.Source.wordEq
        (state.loadSlot checkedDeleteNestedIndexedStorageEntrySlot) 0 &&
      SolidCore.Solidity.Source.wordEq
        (state.loadSlot checkedDeleteNestedIndexedStorageNestedSlot) 0 &&
      SolidCore.Solidity.Source.wordEq
        (state.loadSlot
          (SolidCore.Solidity.Source.dynamicArrayStorageSlot
            checkedDeleteNestedIndexedStorageNestedSlot 0)) 0 &&
      SolidCore.Solidity.Source.wordEq
        (state.loadSlot
          (SolidCore.Solidity.Source.dynamicArrayStorageSlot
            checkedDeleteNestedIndexedStorageNestedSlot 1)) 0)

def checkedStorageArrayDeleteCopyContractsAccepted : Bool :=
  Result.isOk
      (TypecheckedInput.checkedSourceUnit
        Executable.Examples.dynamicStorageArrayContract) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit
        Executable.Examples.storageDeleteContract) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit
        Executable.Examples.storageArrayCopyContract)

def checkedDynamicStorageArrayPushPopState :
    Except TypeError CoreState :=
  checkedOwnCallState 32
    Executable.Examples.dynamicStorageArrayContract
    "pushTwoPop" SolidCore.Solidity.Source.State.empty []

def checkedDynamicStorageArrayLengthAfterPushPop :
    Except TypeError Bool := do
  let state ← checkedDynamicStorageArrayPushPopState
  checkedOwnCallWordMatches 16
    Executable.Examples.dynamicStorageArrayContract
    "length" state [] 1

def checkedDynamicStorageArrayGetterAfterPushPop :
    Except TypeError Bool := do
  let state ← checkedDynamicStorageArrayPushPopState
  checkedOwnCallWordMatches 16
    Executable.Examples.dynamicStorageArrayContract
    "items" state [SolidCore.Solidity.Source.Value.word 0] 7

def checkedDynamicStorageArrayPopEmptyPanics :
    Except TypeError Bool :=
  checkedOwnCallPanicMatches 16
    Executable.Examples.dynamicStorageArrayContract
    "popEmpty" SolidCore.Solidity.Source.State.empty [] 0x31

def checkedDynamicStorageArrayPushAssignMatches :
    Except TypeError Bool :=
  checkedOwnCallWordPairMatches 32
    Executable.Examples.dynamicStorageArrayContract
    "pushAssign" SolidCore.Solidity.Source.State.empty [] 1 42

def checkedStorageDeleteWrittenState :
    Except TypeError CoreState :=
  checkedOwnCallState 48
    Executable.Examples.storageDeleteContract
    "set" SolidCore.Solidity.Source.State.empty []

def checkedStorageDeleteDynamicState :
    Except TypeError CoreState := do
  let state ← checkedStorageDeleteWrittenState
  checkedOwnCallState 24
    Executable.Examples.storageDeleteContract
    "deleteDynamic" state []

def checkedStorageDeleteDynamicLengthZero :
    Except TypeError Bool := do
  let state ← checkedStorageDeleteDynamicState
  checkedOwnCallWordMatches 16
    Executable.Examples.storageDeleteContract
    "length" state [] 0

def checkedStorageDeleteDynamicIndexReverts :
    Except TypeError Bool := do
  let state ← checkedStorageDeleteDynamicState
  checkedOwnCallPanicMatches 16
    Executable.Examples.storageDeleteContract
    "readItem" state [] 0x32

def checkedStorageDeleteFixedState :
    Except TypeError CoreState := do
  let state ← checkedStorageDeleteWrittenState
  checkedOwnCallState 24
    Executable.Examples.storageDeleteContract
    "deleteFixed" state []

def checkedStorageDeleteFixedClearsElement :
    Except TypeError Bool := do
  let state ← checkedStorageDeleteFixedState
  checkedOwnCallWordMatches 16
    Executable.Examples.storageDeleteContract
    "readFixed" state [] 0

def checkedStorageDeleteMappingKeyState :
    Except TypeError CoreState := do
  let state ← checkedStorageDeleteWrittenState
  checkedOwnCallState 24
    Executable.Examples.storageDeleteContract
    "deleteMappingKey" state []

def checkedStorageDeleteMappingKeyClearsEntry :
    Except TypeError Bool := do
  let state ← checkedStorageDeleteMappingKeyState
  checkedOwnCallWordMatches 16
    Executable.Examples.storageDeleteContract
    "readMap" state [] 0

def checkedStorageArrayCopyInput : List CoreValue :=
  [ SolidCore.Solidity.Source.Value.dynamicArray
      [ SolidCore.Solidity.Source.Value.word 5
      , SolidCore.Solidity.Source.Value.word 6 ]
  , SolidCore.Solidity.Source.Value.fixedArray
      [ SolidCore.Solidity.Source.Value.word 1
      , SolidCore.Solidity.Source.Value.word 2
      , SolidCore.Solidity.Source.Value.word 3 ] ]

def checkedStorageArrayCopyState :
    Except TypeError CoreState :=
  checkedOwnCallState 48
    Executable.Examples.storageArrayCopyContract
    "copy" SolidCore.Solidity.Source.State.empty
    checkedStorageArrayCopyInput

def checkedStorageArrayCopyLengthMatches :
    Except TypeError Bool := do
  let state ← checkedStorageArrayCopyState
  checkedOwnCallWordMatches 16
    Executable.Examples.storageArrayCopyContract
    "length" state [] 2

def checkedStorageArrayCopyDynamicElementMatches :
    Except TypeError Bool := do
  let state ← checkedStorageArrayCopyState
  checkedOwnCallWordMatches 16
    Executable.Examples.storageArrayCopyContract
    "readItem" state
    [SolidCore.Solidity.Source.Value.word 1] 6

def checkedStorageArrayCopyFixedElementMatches :
    Except TypeError Bool := do
  let state ← checkedStorageArrayCopyState
  checkedOwnCallWordMatches 16
    Executable.Examples.storageArrayCopyContract
    "readFixed" state
    [SolidCore.Solidity.Source.Value.word 2] 3

def checkedStorageArrayCopyRejectsWrongFixedSize : Bool :=
  match
    ContractDecl.checkedCall? 48
      Executable.Examples.storageArrayCopyContract
      (SolidCore.Solidity.Source.CallTarget.name "copy")
      SolidCore.Solidity.Source.State.empty
      [ SolidCore.Solidity.Source.Value.dynamicArray
          [SolidCore.Solidity.Source.Value.word 5]
      , SolidCore.Solidity.Source.Value.fixedArray
          [ SolidCore.Solidity.Source.Value.word 1
          , SolidCore.Solidity.Source.Value.word 2 ] ]
  with
  | none => true
  | some _ => false

def checkedStorageArrayMutationSemanticsMatch :
    Except TypeError Bool := do
  let fixedStructAssign ← checkedAssignFixedStructArrayGetterMatches
  let dynamicStructAssign ← checkedAssignDynamicStructArrayGetterMatches
  let fixedStructIndexAssign ←
    checkedIndexAssignFixedStructArrayGetterMatches
  let dynamicStructIndexAssign ←
    checkedIndexAssignDynamicStructArrayGetterMatches
  let mappingStructIndexAssign ←
    checkedIndexAssignMappingStructGetterMatches
  let pushStructValue ← checkedPushStructArrayValueGetterMatches
  let pushStructDefault ← checkedPushStructArrayDefaultClearsElement
  let popStruct ← checkedPopStructArrayClearsElement
  let deleteDynamicStruct ← checkedDeleteDynamicStructArrayClearsElement
  let deleteNestedDynamicStruct ←
    checkedDeleteNestedDynamicStructArrayClearsNestedData
  let deleteNestedFixedStruct ←
    checkedDeleteNestedFixedStructArrayClearsNestedData
  let assignNestedDynamicStruct ←
    checkedAssignNestedDynamicStructArrayClearsTail
  let assignNestedStructMapping ←
    checkedAssignNestedStructMappingClearsNestedTail
  let indexedMatrixAssign ←
    checkedIndexedDynamicArrayAssignmentMatrixClearsTail
  let indexedMappingAssign ←
    checkedIndexedDynamicArrayAssignmentMappingClearsTail
  let indexedMatrixDelete ←
    checkedDeleteNestedIndexedStorageMatrixClearsInnerArray
  let indexedMappingDelete ←
    checkedDeleteNestedIndexedStorageMappingClearsNestedData
  let dynamicArrayLength ← checkedDynamicStorageArrayLengthAfterPushPop
  let dynamicArrayGetter ← checkedDynamicStorageArrayGetterAfterPushPop
  let dynamicArrayPopEmpty ← checkedDynamicStorageArrayPopEmptyPanics
  let dynamicArrayPushAssign ← checkedDynamicStorageArrayPushAssignMatches
  let deleteDynamicLength ← checkedStorageDeleteDynamicLengthZero
  let deleteDynamicIndex ← checkedStorageDeleteDynamicIndexReverts
  let deleteFixed ← checkedStorageDeleteFixedClearsElement
  let deleteMappingKey ← checkedStorageDeleteMappingKeyClearsEntry
  let copyLength ← checkedStorageArrayCopyLengthMatches
  let copyDynamic ← checkedStorageArrayCopyDynamicElementMatches
  let copyFixed ← checkedStorageArrayCopyFixedElementMatches
  Except.ok
    (checkedStructArrayStorageContractsAccepted &&
      checkedIndexedDynamicArrayStorageContractsAccepted &&
      checkedStorageArrayDeleteCopyContractsAccepted &&
      checkedStorageArrayCopyRejectsWrongFixedSize &&
      fixedStructAssign && dynamicStructAssign &&
      fixedStructIndexAssign && dynamicStructIndexAssign &&
      mappingStructIndexAssign &&
      pushStructValue && pushStructDefault &&
      popStruct && deleteDynamicStruct &&
      deleteNestedDynamicStruct && deleteNestedFixedStruct &&
      assignNestedDynamicStruct && assignNestedStructMapping &&
      indexedMatrixAssign && indexedMappingAssign &&
      indexedMatrixDelete && indexedMappingDelete &&
      dynamicArrayLength && dynamicArrayGetter &&
      dynamicArrayPopEmpty && dynamicArrayPushAssign &&
      deleteDynamicLength && deleteDynamicIndex &&
      deleteFixed && deleteMappingKey &&
      copyLength && copyDynamic && copyFixed)

def checkedStorageReferenceContractsAccepted : Bool :=
  Result.isOk
      (TypecheckedInput.checkedSourceUnit
        Executable.Examples.storageReferenceAliasCheckedContract) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit
        Executable.Examples.storageReturnAliasContract)

def checkedStorageReferenceDeleteAliasRejected : Bool :=
  Result.isError
    (TypecheckedInput.checkedSourceUnit
      Executable.Examples.storageReferenceAliasContract)

def checkedStorageReferenceAliasCallMatches
    (fuel : Nat) (functionName : Name) (expected : Word) :
    Except TypeError Bool :=
  checkedOwnCallWordMatches fuel
    Executable.Examples.storageReferenceAliasCheckedContract
    functionName SolidCore.Solidity.Source.State.empty [] expected

def checkedStorageReferenceAliasWriteMatches :
    Except TypeError Bool :=
  checkedStorageReferenceAliasCallMatches 48 "aliasWrite" 91

def checkedStorageReferenceMappingAliasMatches :
    Except TypeError Bool :=
  checkedStorageReferenceAliasCallMatches 48 "aliasMap" 12

def checkedStorageReferenceArrayPushMatches :
    Except TypeError Bool :=
  checkedStorageReferenceAliasCallMatches 64 "aliasPush" 26

def checkedStorageReferenceArrayPushAssignMatches :
    Except TypeError Bool :=
  checkedStorageReferenceAliasCallMatches 64 "aliasPushAssign" 21

def checkedStorageReferenceArrayPopMatches :
    Except TypeError Bool :=
  checkedStorageReferenceAliasCallMatches 64 "aliasPop" 17

def checkedStorageReferenceRebindMatches :
    Except TypeError Bool :=
  checkedStorageReferenceAliasCallMatches 80 "aliasRebind" 109

def checkedStorageReferenceRebindFromAliasMatches :
    Except TypeError Bool :=
  checkedStorageReferenceAliasCallMatches
    96 "aliasRebindFromAlias" 308

def checkedStorageInternalReferenceParamWriteMatches :
    Except TypeError Bool :=
  checkedStorageReferenceAliasCallMatches
    80 "internalStorageParamWrite" 9

def checkedStorageInternalReferenceParamAliasArgMatches :
    Except TypeError Bool :=
  checkedStorageReferenceAliasCallMatches
    96 "internalStorageParamAliasArg" 8

def checkedStorageInternalReferenceParamPushMatches :
    Except TypeError Bool :=
  checkedStorageReferenceAliasCallMatches
    96 "internalStorageParamPush" 16

def checkedStorageInternalReferenceParamPopMatches :
    Except TypeError Bool :=
  checkedStorageReferenceAliasCallMatches
    128 "internalStorageParamPop" 14

def checkedStorageInternalReferenceParamAliasPushMatches :
    Except TypeError Bool :=
  checkedStorageReferenceAliasCallMatches
    96 "internalStorageParamAliasPush" 17

def checkedStorageInternalReferenceParamRebindMatches :
    Except TypeError Bool :=
  checkedStorageReferenceAliasCallMatches
    128 "internalStorageParamRebind" 211

def checkedStorageInternalReferenceParamRebindToStateMatches :
    Except TypeError Bool :=
  checkedStorageReferenceAliasCallMatches
    128 "internalStorageParamRebindToState" 512

def checkedStorageInternalMappingParamWriteMatches :
    Except TypeError Bool :=
  checkedStorageReferenceAliasCallMatches
    96 "internalStorageMappingParamWrite" 23

def checkedStorageInternalMappingParamAliasArgMatches :
    Except TypeError Bool :=
  checkedStorageReferenceAliasCallMatches
    96 "internalStorageMappingParamAliasArg" 31

def checkedStorageReturnAliasCallMatches
    (functionName : Name) (expected : Word) :
    Except TypeError Bool :=
  checkedOwnCallWordMatches 128
    Executable.Examples.storageReturnAliasContract
    functionName SolidCore.Solidity.Source.State.empty [] expected

def checkedStorageReturnSingleBindingMatches :
    Except TypeError Bool :=
  checkedStorageReturnAliasCallMatches "bindReturnedStorage" 16

def checkedStorageReturnTupleBindingMatches :
    Except TypeError Bool :=
  checkedStorageReturnAliasCallMatches "bindReturnedStorageTuple" 16

def checkedStorageReturnDirectMutationMatches :
    Except TypeError Bool :=
  checkedStorageReturnAliasCallMatches "mutateReturnedStorage" 2

def checkedStorageReturnConditionalBindingMatches :
    Except TypeError Bool :=
  checkedStorageReturnAliasCallMatches
    "bindConditionalReturnedStorage" 127

def checkedStandaloneStorageBytesContractAccepted : Bool :=
  Result.isOk
    (TypecheckedInput.checkedSourceUnit
      Executable.Examples.storageBytesContract)

def checkedStandaloneStorageBytesInput : CoreValue :=
  SolidCore.Solidity.Source.Value.bytes [10, 20]

def checkedStandaloneStorageBytesSetState :
    Except TypeError CoreState :=
  checkedOwnCallState 24
    Executable.Examples.storageBytesContract
    "set" SolidCore.Solidity.Source.State.empty
    [checkedStandaloneStorageBytesInput]

def checkedStandaloneStorageBytesCallState
    (fuel : Nat) (functionName : Name) (state : CoreState) :
    Except TypeError CoreState :=
  checkedOwnCallState fuel
    Executable.Examples.storageBytesContract
    functionName state []

def checkedStandaloneStorageBytesAtMatches
    (state : CoreState) (index expected : Word) :
    Except TypeError Bool :=
  checkedOwnCallWordMatches 16
    Executable.Examples.storageBytesContract
    "at" state [SolidCore.Solidity.Source.Value.word index]
    expected

def checkedStandaloneStorageBytesLengthMatches :
    Except TypeError Bool := do
  let state ← checkedStandaloneStorageBytesSetState
  checkedOwnCallWordMatches 16
    Executable.Examples.storageBytesContract
    "length" state [] 2

def checkedStandaloneStorageBytesIndexMatches :
    Except TypeError Bool := do
  let state ← checkedStandaloneStorageBytesSetState
  checkedStandaloneStorageBytesAtMatches state 1 20

def checkedStandaloneStorageBytesWriteState :
    Except TypeError CoreState := do
  let state ← checkedStandaloneStorageBytesSetState
  checkedStandaloneStorageBytesCallState 16 "writeSecond" state

def checkedStandaloneStorageBytesWriteSecondMatches :
    Except TypeError Bool := do
  let state ← checkedStandaloneStorageBytesWriteState
  checkedStandaloneStorageBytesAtMatches state 1 9

def checkedStandaloneStorageBytesPushFourState :
    Except TypeError CoreState := do
  let state ← checkedStandaloneStorageBytesSetState
  checkedStandaloneStorageBytesCallState 16 "pushFour" state

def checkedStandaloneStorageBytesPushFourMatches :
    Except TypeError Bool := do
  let state ← checkedStandaloneStorageBytesPushFourState
  let length ←
    checkedOwnCallWordMatches 16
      Executable.Examples.storageBytesContract
      "length" state [] 3
  let value ← checkedStandaloneStorageBytesAtMatches state 2 4
  Except.ok (length && value)

def checkedStandaloneStorageBytesPushZeroState :
    Except TypeError CoreState := do
  let state ← checkedStandaloneStorageBytesSetState
  checkedStandaloneStorageBytesCallState 16 "pushZero" state

def checkedStandaloneStorageBytesPushZeroMatches :
    Except TypeError Bool := do
  let state ← checkedStandaloneStorageBytesPushZeroState
  checkedStandaloneStorageBytesAtMatches state 2 0

def checkedStandaloneStorageBytesPopState :
    Except TypeError CoreState := do
  let state ← checkedStandaloneStorageBytesPushFourState
  checkedStandaloneStorageBytesCallState 16 "popOne" state

def checkedStandaloneStorageBytesPopLengthMatches :
    Except TypeError Bool := do
  let state ← checkedStandaloneStorageBytesPopState
  checkedOwnCallWordMatches 16
    Executable.Examples.storageBytesContract
    "length" state [] 2

def checkedStandaloneStorageBytesAliasWriteState :
    Except TypeError CoreState := do
  let state ← checkedStandaloneStorageBytesSetState
  checkedStandaloneStorageBytesCallState 16 "aliasWriteSecond" state

def checkedStandaloneStorageBytesAliasWriteSecondMatches :
    Except TypeError Bool := do
  let state ← checkedStandaloneStorageBytesAliasWriteState
  checkedStandaloneStorageBytesAtMatches state 1 8

def checkedStandaloneStorageBytesAliasPushState :
    Except TypeError CoreState := do
  let state ← checkedStandaloneStorageBytesSetState
  checkedStandaloneStorageBytesCallState 16 "aliasPushFive" state

def checkedStandaloneStorageBytesAliasPushMatches :
    Except TypeError Bool := do
  let state ← checkedStandaloneStorageBytesAliasPushState
  let length ←
    checkedOwnCallWordMatches 16
      Executable.Examples.storageBytesContract
      "length" state [] 3
  let value ← checkedStandaloneStorageBytesAtMatches state 2 5
  Except.ok (length && value)

def checkedStandaloneStorageBytesAliasPopState :
    Except TypeError CoreState := do
  let state ← checkedStandaloneStorageBytesSetState
  checkedStandaloneStorageBytesCallState 16 "aliasPopOne" state

def checkedStandaloneStorageBytesAliasPopMatches :
    Except TypeError Bool := do
  let state ← checkedStandaloneStorageBytesAliasPopState
  let length ←
    checkedOwnCallWordMatches 16
      Executable.Examples.storageBytesContract
      "length" state [] 1
  let value ← checkedStandaloneStorageBytesAtMatches state 0 10
  Except.ok (length && value)

def checkedStandaloneStorageBytesInternalParamWriteState :
    Except TypeError CoreState := do
  let state ← checkedStandaloneStorageBytesSetState
  checkedStandaloneStorageBytesCallState
    24 "internalBytesParamWriteSecond" state

def checkedStandaloneStorageBytesInternalParamWriteSecondMatches :
    Except TypeError Bool := do
  let state ← checkedStandaloneStorageBytesInternalParamWriteState
  checkedStandaloneStorageBytesAtMatches state 1 7

def checkedStandaloneStorageBytesInternalParamAliasPushState :
    Except TypeError CoreState := do
  let state ← checkedStandaloneStorageBytesSetState
  checkedStandaloneStorageBytesCallState
    32 "internalBytesParamAliasPushSix" state

def checkedStandaloneStorageBytesInternalParamAliasPushMatches :
    Except TypeError Bool := do
  let state ← checkedStandaloneStorageBytesInternalParamAliasPushState
  let length ←
    checkedOwnCallWordMatches 16
      Executable.Examples.storageBytesContract
      "length" state [] 3
  let value ← checkedStandaloneStorageBytesAtMatches state 2 6
  Except.ok (length && value)

def checkedStandaloneStorageBytesInternalParamPopState :
    Except TypeError CoreState := do
  let state ← checkedStandaloneStorageBytesSetState
  checkedStandaloneStorageBytesCallState
    24 "internalBytesParamPopOne" state

def checkedStandaloneStorageBytesInternalParamPopMatches :
    Except TypeError Bool := do
  let state ← checkedStandaloneStorageBytesInternalParamPopState
  let length ←
    checkedOwnCallWordMatches 16
      Executable.Examples.storageBytesContract
      "length" state [] 1
  let value ← checkedStandaloneStorageBytesAtMatches state 0 10
  Except.ok (length && value)

def checkedStandaloneStorageBytesClearState :
    Except TypeError CoreState := do
  let state ← checkedStandaloneStorageBytesSetState
  checkedStandaloneStorageBytesCallState 16 "clear" state

def checkedStandaloneStorageBytesClearLengthZero :
    Except TypeError Bool := do
  let state ← checkedStandaloneStorageBytesClearState
  checkedOwnCallWordMatches 16
    Executable.Examples.storageBytesContract
    "length" state [] 0

def checkedStandaloneStorageBytesClearIndexReverts :
    Except TypeError Bool := do
  let state ← checkedStandaloneStorageBytesClearState
  checkedOwnCallPanicMatches 16
    Executable.Examples.storageBytesContract
    "at" state [SolidCore.Solidity.Source.Value.word 0]
    0x32

def checkedStandaloneStorageBytesShortRawSlotMatches :
    Except TypeError Bool := do
  let state ← checkedStandaloneStorageBytesSetState
  Except.ok
    (SolidCore.Solidity.Source.wordEq (state.loadSlot 0)
      (SolidCore.Solidity.Source.storageBytesShortWord [10, 20]))

def checkedStandaloneStorageBytesShortWriteRawSlotMatches :
    Except TypeError Bool := do
  let state ← checkedStandaloneStorageBytesWriteState
  Except.ok
    (SolidCore.Solidity.Source.wordEq (state.loadSlot 0)
      (SolidCore.Solidity.Source.storageBytesShortWord [10, 9]))

def checkedStandaloneStorageBytesShortPushRawSlotMatches :
    Except TypeError Bool := do
  let state ← checkedStandaloneStorageBytesPushFourState
  Except.ok
    (SolidCore.Solidity.Source.wordEq (state.loadSlot 0)
      (SolidCore.Solidity.Source.storageBytesShortWord [10, 20, 4]))

def checkedStandaloneStorageBytesLongSetState :
    Except TypeError CoreState :=
  checkedOwnCallState 32
    Executable.Examples.storageBytesContract
    "set" SolidCore.Solidity.Source.State.empty
    [ SolidCore.Solidity.Source.Value.bytes
        Executable.Examples.storageBytesLongBytes ]

def checkedStandaloneStorageBytesLongRawSlotMatches :
    Except TypeError Bool := do
  let state ← checkedStandaloneStorageBytesLongSetState
  Except.ok
    (SolidCore.Solidity.Source.wordEq (state.loadSlot 0)
      (SolidCore.Solidity.Source.storageBytesLongHeader 33) &&
      SolidCore.Solidity.Source.wordEq
        (state.loadSlot
          (SolidCore.Solidity.Source.storageBytesLongDataSlot 0 0))
        (Executable.Examples.storageBytesLongChunkWord
          (Executable.Examples.storageBytesLongBytes.take 32)) &&
      SolidCore.Solidity.Source.wordEq
        (state.loadSlot
          (SolidCore.Solidity.Source.storageBytesLongDataSlot 0 1))
        (Executable.Examples.storageBytesLongChunkWord [33]))

def checkedStandaloneStorageBytesLongReadMatches :
    Except TypeError Bool := do
  let state ← checkedStandaloneStorageBytesLongSetState
  let length ←
    checkedOwnCallWordMatches 16
      Executable.Examples.storageBytesContract
      "length" state [] 33
  let value ← checkedStandaloneStorageBytesAtMatches state 32 33
  Except.ok (length && value)

def checkedStandaloneStorageBytesShortToLongPushState :
    Except TypeError CoreState := do
  let state ←
    checkedOwnCallState 32
      Executable.Examples.storageBytesContract
      "set" SolidCore.Solidity.Source.State.empty
      [ SolidCore.Solidity.Source.Value.bytes
          Executable.Examples.storageBytesThirtyOneBytes ]
  checkedStandaloneStorageBytesCallState 16 "pushFour" state

def checkedStandaloneStorageBytesShortToLongPushRawSlotMatches :
    Except TypeError Bool := do
  let state ← checkedStandaloneStorageBytesShortToLongPushState
  Except.ok
    (SolidCore.Solidity.Source.wordEq (state.loadSlot 0)
      (SolidCore.Solidity.Source.storageBytesLongHeader 32) &&
      SolidCore.Solidity.Source.wordEq
        (state.loadSlot
          (SolidCore.Solidity.Source.storageBytesLongDataSlot 0 0))
        (Executable.Examples.storageBytesLongChunkWord
          (Executable.Examples.storageBytesThirtyOneBytes ++ [4])))

def checkedStandaloneStorageBytesLongToShortSetState :
    Except TypeError CoreState := do
  let state ← checkedStandaloneStorageBytesLongSetState
  checkedOwnCallState 32
    Executable.Examples.storageBytesContract
    "set" state
    [SolidCore.Solidity.Source.Value.bytes [7, 8]]

def checkedStandaloneStorageBytesLongToShortCleanupMatches :
    Except TypeError Bool := do
  let state ← checkedStandaloneStorageBytesLongToShortSetState
  Except.ok
    (SolidCore.Solidity.Source.wordEq (state.loadSlot 0)
      (SolidCore.Solidity.Source.storageBytesShortWord [7, 8]) &&
      SolidCore.Solidity.Source.wordEq
        (state.loadSlot
          (SolidCore.Solidity.Source.storageBytesLongDataSlot 0 0))
        0 &&
      SolidCore.Solidity.Source.wordEq
        (state.loadSlot
          (SolidCore.Solidity.Source.storageBytesLongDataSlot 0 1))
        0)

def checkedStandaloneStorageBytesLongPopToThirtyTwoState :
    Except TypeError CoreState := do
  let state ← checkedStandaloneStorageBytesLongSetState
  checkedStandaloneStorageBytesCallState 16 "popOne" state

def checkedStandaloneStorageBytesLongPopClearsTailMatches :
    Except TypeError Bool := do
  let state ← checkedStandaloneStorageBytesLongPopToThirtyTwoState
  Except.ok
    (SolidCore.Solidity.Source.wordEq (state.loadSlot 0)
      (SolidCore.Solidity.Source.storageBytesLongHeader 32) &&
      SolidCore.Solidity.Source.wordEq
        (state.loadSlot
          (SolidCore.Solidity.Source.storageBytesLongDataSlot 0 0))
        (Executable.Examples.storageBytesLongChunkWord
          (Executable.Examples.storageBytesLongBytes.take 32)) &&
      SolidCore.Solidity.Source.wordEq
        (state.loadSlot
          (SolidCore.Solidity.Source.storageBytesLongDataSlot 0 1))
        0)

def checkedStandaloneStorageBytesSixtyFiveSetState :
    Except TypeError CoreState :=
  checkedOwnCallState 64
    Executable.Examples.storageBytesContract
    "set" SolidCore.Solidity.Source.State.empty
    [ SolidCore.Solidity.Source.Value.bytes
        Executable.Examples.storageBytesSixtyFiveBytes ]

def checkedStandaloneStorageBytesLongShrinkSetState :
    Except TypeError CoreState := do
  let state ← checkedStandaloneStorageBytesSixtyFiveSetState
  checkedOwnCallState 64
    Executable.Examples.storageBytesContract
    "set" state
    [ SolidCore.Solidity.Source.Value.bytes
        Executable.Examples.storageBytesLongBytes ]

def checkedStandaloneStorageBytesLongShrinkCleanupMatches :
    Except TypeError Bool := do
  let state ← checkedStandaloneStorageBytesLongShrinkSetState
  Except.ok
    (SolidCore.Solidity.Source.wordEq (state.loadSlot 0)
      (SolidCore.Solidity.Source.storageBytesLongHeader 33) &&
      SolidCore.Solidity.Source.wordEq
        (state.loadSlot
          (SolidCore.Solidity.Source.storageBytesLongDataSlot 0 0))
        (Executable.Examples.storageBytesLongChunkWord
          (Executable.Examples.storageBytesLongBytes.take 32)) &&
      SolidCore.Solidity.Source.wordEq
        (state.loadSlot
          (SolidCore.Solidity.Source.storageBytesLongDataSlot 0 1))
        (Executable.Examples.storageBytesLongChunkWord [33]) &&
      SolidCore.Solidity.Source.wordEq
        (state.loadSlot
          (SolidCore.Solidity.Source.storageBytesLongDataSlot 0 2))
        0)

def checkedStorageReferenceBytesSemanticsMatch :
    Except TypeError Bool := do
  let aliasWrite ← checkedStorageReferenceAliasWriteMatches
  let mappingAlias ← checkedStorageReferenceMappingAliasMatches
  let arrayPush ← checkedStorageReferenceArrayPushMatches
  let arrayPushAssign ← checkedStorageReferenceArrayPushAssignMatches
  let arrayPop ← checkedStorageReferenceArrayPopMatches
  let rebind ← checkedStorageReferenceRebindMatches
  let rebindFromAlias ← checkedStorageReferenceRebindFromAliasMatches
  let internalWrite ← checkedStorageInternalReferenceParamWriteMatches
  let internalAliasArg ←
    checkedStorageInternalReferenceParamAliasArgMatches
  let internalPush ← checkedStorageInternalReferenceParamPushMatches
  let internalPop ← checkedStorageInternalReferenceParamPopMatches
  let internalAliasPush ←
    checkedStorageInternalReferenceParamAliasPushMatches
  let internalRebind ← checkedStorageInternalReferenceParamRebindMatches
  let internalRebindToState ←
    checkedStorageInternalReferenceParamRebindToStateMatches
  let internalMappingWrite ← checkedStorageInternalMappingParamWriteMatches
  let internalMappingAlias ←
    checkedStorageInternalMappingParamAliasArgMatches
  let returnSingle ← checkedStorageReturnSingleBindingMatches
  let returnTuple ← checkedStorageReturnTupleBindingMatches
  let returnMutation ← checkedStorageReturnDirectMutationMatches
  let returnConditional ← checkedStorageReturnConditionalBindingMatches
  let bytesLength ← checkedStandaloneStorageBytesLengthMatches
  let bytesIndex ← checkedStandaloneStorageBytesIndexMatches
  let bytesWrite ← checkedStandaloneStorageBytesWriteSecondMatches
  let bytesPushFour ← checkedStandaloneStorageBytesPushFourMatches
  let bytesPushZero ← checkedStandaloneStorageBytesPushZeroMatches
  let bytesPop ← checkedStandaloneStorageBytesPopLengthMatches
  let bytesAliasWrite ← checkedStandaloneStorageBytesAliasWriteSecondMatches
  let bytesAliasPush ← checkedStandaloneStorageBytesAliasPushMatches
  let bytesAliasPop ← checkedStandaloneStorageBytesAliasPopMatches
  let bytesInternalWrite ←
    checkedStandaloneStorageBytesInternalParamWriteSecondMatches
  let bytesInternalAliasPush ←
    checkedStandaloneStorageBytesInternalParamAliasPushMatches
  let bytesInternalPop ←
    checkedStandaloneStorageBytesInternalParamPopMatches
  let bytesClearLength ← checkedStandaloneStorageBytesClearLengthZero
  let bytesClearIndex ← checkedStandaloneStorageBytesClearIndexReverts
  let bytesShortRaw ← checkedStandaloneStorageBytesShortRawSlotMatches
  let bytesShortWriteRaw ←
    checkedStandaloneStorageBytesShortWriteRawSlotMatches
  let bytesShortPushRaw ←
    checkedStandaloneStorageBytesShortPushRawSlotMatches
  let bytesLongRaw ← checkedStandaloneStorageBytesLongRawSlotMatches
  let bytesLongRead ← checkedStandaloneStorageBytesLongReadMatches
  let bytesShortToLongRaw ←
    checkedStandaloneStorageBytesShortToLongPushRawSlotMatches
  let bytesLongToShortCleanup ←
    checkedStandaloneStorageBytesLongToShortCleanupMatches
  let bytesLongPopCleanup ←
    checkedStandaloneStorageBytesLongPopClearsTailMatches
  let bytesLongShrinkCleanup ←
    checkedStandaloneStorageBytesLongShrinkCleanupMatches
  Except.ok
    (checkedStorageReferenceContractsAccepted &&
      checkedStorageReferenceDeleteAliasRejected &&
      checkedStandaloneStorageBytesContractAccepted &&
      aliasWrite && mappingAlias && arrayPush && arrayPushAssign &&
      arrayPop && rebind && rebindFromAlias &&
      internalWrite && internalAliasArg && internalPush &&
      internalPop && internalAliasPush && internalRebind &&
      internalRebindToState &&
      internalMappingWrite && internalMappingAlias &&
      returnSingle && returnTuple && returnMutation && returnConditional &&
      bytesLength && bytesIndex && bytesWrite &&
      bytesPushFour && bytesPushZero && bytesPop &&
      bytesAliasWrite && bytesAliasPush && bytesAliasPop &&
      bytesInternalWrite && bytesInternalAliasPush && bytesInternalPop &&
      bytesClearLength && bytesClearIndex &&
      bytesShortRaw && bytesShortWriteRaw && bytesShortPushRaw &&
      bytesLongRaw && bytesLongRead && bytesShortToLongRaw &&
      bytesLongToShortCleanup && bytesLongPopCleanup &&
      bytesLongShrinkCleanup)

def checkedOverloadedDispatchContractsAccepted : Bool :=
  Result.isOk
      (TypecheckedInput.checkedSourceUnit
        Executable.Examples.overloadedDispatchContract) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit
        Executable.Examples.internalOverloadedDispatchContract)

def checkedOverloadedDirectBoolCallMatches :
    Except TypeError Bool :=
  checkedOwnCallWordMatches 16
    Executable.Examples.overloadedDispatchContract
    "pick" SolidCore.Solidity.Source.State.empty
    [SolidCore.Solidity.Source.Value.word 1] 1

def checkedOverloadedDirectUintCallMatches :
    Except TypeError Bool :=
  checkedOwnCallWordMatches 16
    Executable.Examples.overloadedDispatchContract
    "pick" SolidCore.Solidity.Source.State.empty
    [SolidCore.Solidity.Source.Value.word 7] 2

def checkedOverloadedDirectBytesCallMatches :
    Except TypeError Bool :=
  checkedOwnCallWordMatches 16
    Executable.Examples.overloadedDispatchContract
    "pick" SolidCore.Solidity.Source.State.empty
    [SolidCore.Solidity.Source.Value.bytes [1, 2]] 3

def checkedOverloadedAbiCallMatches
    (signature : String)
    (tys : List SolidCore.Solidity.Source.Ty)
    (args : List CoreValue) (expectedValue : Word) :
    Except TypeError Bool := do
  let calldata ← checkedAbiEncodeValues tys args
  let selector :=
    SolidCore.Solidity.Source.ABI.selectorFromSignature signature
  let result ←
    ContractDecl.checkedCallCalldata 16
      Executable.Examples.overloadedDispatchContract
      SolidCore.Solidity.Source.State.empty
      (SolidCore.Solidity.Source.wordToBytesBE
        SolidCore.Solidity.Source.selectorBytes selector ++ calldata)
  let expected ←
    checkedAbiEncodeValues
      [SolidCore.Solidity.Source.Ty.uint256]
      [SolidCore.Solidity.Source.Value.word expectedValue]
  Except.ok (result.success && result.output == expected)

def checkedOverloadedAbiUintCallMatches :
    Except TypeError Bool :=
  checkedOverloadedAbiCallMatches
    "pick(uint256)"
    [SolidCore.Solidity.Source.Ty.uint256]
    [SolidCore.Solidity.Source.Value.word 7] 2

def checkedOverloadedAbiBytesCallMatches :
    Except TypeError Bool :=
  checkedOverloadedAbiCallMatches
    "pick(bytes)"
    [SolidCore.Solidity.Source.Ty.bytesCalldata]
    [SolidCore.Solidity.Source.Value.bytes [1, 2]] 3

def checkedInternalOverloadedDispatchMatchesExpected :
    Except TypeError Bool :=
  checkedOwnCallWordTripleMatches 48
    Executable.Examples.internalOverloadedDispatchContract
    "run" SolidCore.Solidity.Source.State.empty [] 1 2 3

def checkedInheritedNestedEnumUdvtUnitsAccepted : Bool :=
  Result.isOk
      (TypecheckedInput.checkedSourceUnit
        Executable.Examples.inheritedNestedTypeUnit) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit
        Executable.Examples.inheritedEnumUdvtUnit)

def checkedInheritedNestedTypeShadowsUnrelatedSourceElaboration :
    Except TypeError Bool := do
  let contract ←
    CheckedInput.toCoreContract
      Executable.Examples.inheritedNestedTypeUnit
      "NestedTypeDerived"
  optionToExcept "inherited nested type source elaboration"
    (Executable.Examples.inheritedNestedTypeFunctionReturnsFirstField?
      "readInheritedX" contract)

def checkedQualifiedInheritedNestedTypeSourceElaboration :
    Except TypeError Bool := do
  let contract ←
    CheckedInput.toCoreContract
      Executable.Examples.inheritedNestedTypeUnit
      "NestedTypeDerived"
  optionToExcept "qualified inherited nested type source elaboration"
    (Executable.Examples.inheritedNestedTypeFunctionReturnsFirstField?
      "readQualifiedInheritedX" contract)

def checkedInheritedEnumMaxMatches :
    Except TypeError Bool :=
  checkedCallWordMatches 32
    Executable.Examples.inheritedEnumUdvtUnit
    "EnumUdvtDerived" "largest"
    SolidCore.Solidity.Source.State.empty [] 2

def checkedQualifiedInheritedEnumMaxMatches :
    Except TypeError Bool :=
  checkedCallWordMatches 32
    Executable.Examples.inheritedEnumUdvtUnit
    "EnumUdvtDerived" "largestQualified"
    SolidCore.Solidity.Source.State.empty [] 2

def checkedInheritedUdvtAbiEchoMatches (signature : String) :
    Except TypeError Bool := do
  let selector :=
    SolidCore.Solidity.Source.ABI.selectorFromSignature signature
  let calldata ←
    checkedAbiEncodeValues
      [SolidCore.Solidity.Source.Ty.uint256]
      [SolidCore.Solidity.Source.Value.word 5]
  let result ←
    CheckedInput.callCalldata 32
      Executable.Examples.inheritedEnumUdvtUnit
      "EnumUdvtDerived"
      SolidCore.Solidity.Source.State.empty
      (SolidCore.Solidity.Source.wordToBytesBE
        SolidCore.Solidity.Source.selectorBytes selector ++ calldata)
  let expected ←
    checkedAbiEncodeValues
      [SolidCore.Solidity.Source.Ty.uint256]
      [SolidCore.Solidity.Source.Value.word 5]
  Except.ok (result.success && result.output == expected)

def checkedInheritedUdvtAbiEchoUsesInheritedUnderlying :
    Except TypeError Bool :=
  checkedInheritedUdvtAbiEchoMatches "echoToken(uint8)"

def checkedQualifiedInheritedUdvtAbiEchoUsesInheritedUnderlying :
    Except TypeError Bool :=
  checkedInheritedUdvtAbiEchoMatches "echoQualifiedToken(uint8)"

def checkedOverloadInheritedLookupSemanticsMatch :
    Except TypeError Bool := do
  let overloadBool ← checkedOverloadedDirectBoolCallMatches
  let overloadUint ← checkedOverloadedDirectUintCallMatches
  let overloadBytes ← checkedOverloadedDirectBytesCallMatches
  let overloadAbiUint ← checkedOverloadedAbiUintCallMatches
  let overloadAbiBytes ← checkedOverloadedAbiBytesCallMatches
  let internalOverload ← checkedInternalOverloadedDispatchMatchesExpected
  let inheritedNested ←
    checkedInheritedNestedTypeShadowsUnrelatedSourceElaboration
  let qualifiedInheritedNested ←
    checkedQualifiedInheritedNestedTypeSourceElaboration
  let inheritedEnum ← checkedInheritedEnumMaxMatches
  let qualifiedInheritedEnum ← checkedQualifiedInheritedEnumMaxMatches
  let inheritedUdvt ← checkedInheritedUdvtAbiEchoUsesInheritedUnderlying
  let qualifiedInheritedUdvt ←
    checkedQualifiedInheritedUdvtAbiEchoUsesInheritedUnderlying
  Except.ok
    (checkedOverloadedDispatchContractsAccepted &&
      checkedInheritedNestedEnumUdvtUnitsAccepted &&
      overloadBool && overloadUint && overloadBytes &&
      overloadAbiUint && overloadAbiBytes && internalOverload &&
      inheritedNested && qualifiedInheritedNested &&
      inheritedEnum && qualifiedInheritedEnum &&
      inheritedUdvt && qualifiedInheritedUdvt)

def checkedMemoryAndCalldataContractAccepted : Bool :=
  Result.isOk
    (TypecheckedInput.checkedSourceUnit
      Executable.Examples.checkedMemoryAndCalldataContract)

def checkedArrayLiteralLocalMatches : Except TypeError Bool :=
  checkedOwnCallWordMatches 16
    Executable.Examples.checkedMemoryAndCalldataContract
    "middle" SolidCore.Solidity.Source.State.empty [] 9

def checkedArrayLiteralAbiEncodeMatches :
    Except TypeError Bool := do
  let expected ←
    optionToExcept "array literal ABI encoding"
      Executable.Examples.arrayLiteralAbiEncodeExpected
  checkedOwnCallBytesMatches 16
    Executable.Examples.checkedMemoryAndCalldataContract
    "encodeArrayLiteral" SolidCore.Solidity.Source.State.empty []
    expected

def checkedArrayLiteralFixedBytesWidenMatches :
    Except TypeError Bool := do
  let expected ←
    optionToExcept "fixed bytes array literal ABI encoding"
      Executable.Examples.arrayLiteralFixedBytesWidenExpected
  checkedOwnCallBytesMatches 16
    Executable.Examples.checkedMemoryAndCalldataContract
    "encodeFixedBytesArrayLiteral"
    SolidCore.Solidity.Source.State.empty [] expected

def checkedMemoryArrayAllocationMatches :
    Except TypeError Bool :=
  checkedOwnCallWordQuadMatches 16
    Executable.Examples.checkedMemoryAndCalldataContract
    "allocate" SolidCore.Solidity.Source.State.empty
    [SolidCore.Solidity.Source.Value.word 3]
    3 0 7 0

def checkedMemoryArrayAllocationOutOfBoundsPanics :
    Except TypeError Bool :=
  checkedOwnCallPanicMatches 16
    Executable.Examples.checkedMemoryAndCalldataContract
    "allocate" SolidCore.Solidity.Source.State.empty
    [SolidCore.Solidity.Source.Value.word 1] 0x32

def checkedMemoryAllocationTooLargePanicMatches
    (functionName : Name) : Except TypeError Bool := do
  let contract ←
    ContractDecl.checkedContract
      Executable.Examples.checkedMemoryAndCalldataContract
  let result ←
    CheckedContract.callFunctionWithContext 16 contract functionName
      { contract.core.context with memoryAllocationLimit? := some 3 }
      SolidCore.Solidity.Source.State.empty
      [SolidCore.Solidity.Source.Value.word 4]
  match result with
  | SolidCore.Solidity.Source.CallResult.reverted _
      (SolidCore.Solidity.Source.RevertData.panic code) =>
      Except.ok (SolidCore.Solidity.Source.wordEq code 0x41)
  | _ => Except.ok false

def checkedMemoryArrayAllocationTooLargePanics :
    Except TypeError Bool :=
  checkedMemoryAllocationTooLargePanicMatches "allocate"

def checkedMemoryBytesAllocationMatches :
    Except TypeError Bool :=
  checkedOwnCallBytesAndWordQuadMatches 16
    Executable.Examples.checkedMemoryAndCalldataContract
    "allocateBytes" SolidCore.Solidity.Source.State.empty
    [SolidCore.Solidity.Source.Value.word 3]
    [0, 0xab, 0] 3 0 0xab 0

def checkedMemoryBytesAllocationOutOfBoundsPanics :
    Except TypeError Bool :=
  checkedOwnCallPanicMatches 16
    Executable.Examples.checkedMemoryAndCalldataContract
    "allocateBytes" SolidCore.Solidity.Source.State.empty
    [SolidCore.Solidity.Source.Value.word 1] 0x32

def checkedMemoryBytesAllocationTooLargePanics :
    Except TypeError Bool :=
  checkedMemoryAllocationTooLargePanicMatches "allocateBytes"

def checkedMemoryStringAllocationMatches :
    Except TypeError Bool :=
  checkedOwnCallBytesMatches 16
    Executable.Examples.checkedMemoryAndCalldataContract
    "allocateString" SolidCore.Solidity.Source.State.empty
    [SolidCore.Solidity.Source.Value.word 3]
    [0, 0, 0]

def checkedMemoryStringAllocationTooLargePanics :
    Except TypeError Bool :=
  checkedMemoryAllocationTooLargePanicMatches "allocateString"

def checkedMemoryAllocationFootprintRuns :
    Except TypeError Bool :=
  checkedOwnCallWordMatches 32
    Executable.Examples.checkedMemoryAndCalldataContract
    "memoryFootprint" SolidCore.Solidity.Source.State.empty [] 1

def checkedMemoryArrayAliasMatches :
    Except TypeError Bool :=
  checkedOwnCallWordPairMatches 32
    Executable.Examples.checkedMemoryAndCalldataContract
    "memoryArrayAlias" SolidCore.Solidity.Source.State.empty [] 7 7

def checkedMemoryBytesAliasMatches :
    Except TypeError Bool :=
  checkedOwnCallWordPairMatches 32
    Executable.Examples.checkedMemoryAndCalldataContract
    "memoryBytesAlias" SolidCore.Solidity.Source.State.empty [] 0xab 0xab

def checkedCalldataCopyThenMemoryAliasMatches :
    Except TypeError Bool :=
  checkedOwnCallWordPairMatches 32
    Executable.Examples.checkedMemoryAndCalldataContract
    "calldataCopyThenMemoryAlias"
    SolidCore.Solidity.Source.State.empty
    [ SolidCore.Solidity.Source.Value.dynamicArray
        [ SolidCore.Solidity.Source.Value.word 4
        , SolidCore.Solidity.Source.Value.word 5 ] ]
    4 9

def checkedNestedMemoryArrayAliasMatches :
    Except TypeError Bool :=
  checkedOwnCallWordPairMatches 48
    Executable.Examples.checkedMemoryAndCalldataContract
    "nestedMemoryArrayAlias"
    SolidCore.Solidity.Source.State.empty [] 42 42

def checkedNestedMemoryArrayPathAliasMatches :
    Except TypeError Bool :=
  checkedOwnCallWordPairMatches 48
    Executable.Examples.checkedMemoryAndCalldataContract
    "nestedMemoryArrayPathAlias"
    SolidCore.Solidity.Source.State.empty [] 42 42

def checkedNestedMemoryArrayCompoundAliasMatches :
    Except TypeError Bool :=
  checkedOwnCallWordPairMatches 64
    Executable.Examples.checkedMemoryAndCalldataContract
    "nestedMemoryArrayCompoundAlias"
    SolidCore.Solidity.Source.State.empty [] 42 42

def checkedNestedMemoryArrayDeleteAliasMatches :
    Except TypeError Bool :=
  checkedOwnCallWordPairMatches 64
    Executable.Examples.checkedMemoryAndCalldataContract
    "nestedMemoryArrayDeleteAlias"
    SolidCore.Solidity.Source.State.empty [] 0 0

def checkedNestedMemoryArrayIncAliasMatches :
    Except TypeError Bool :=
  checkedOwnCallWordPairMatches 64
    Executable.Examples.checkedMemoryAndCalldataContract
    "nestedMemoryArrayIncAlias"
    SolidCore.Solidity.Source.State.empty [] 7 7

def checkedMemoryStructArrayFieldAliasMatches :
    Except TypeError Bool :=
  checkedOwnCallWordPairMatches 48
    Executable.Examples.checkedMemoryAndCalldataContract
    "memoryStructArrayFieldAlias"
    SolidCore.Solidity.Source.State.empty [] 77 77

def checkedMemoryStructWholeAssignArrayFieldAliasMatches :
    Except TypeError Bool :=
  checkedOwnCallWordPairMatches 64
    Executable.Examples.checkedMemoryAndCalldataContract
    "memoryStructWholeAssignArrayFieldAlias"
    SolidCore.Solidity.Source.State.empty [] 88 88

def checkedInvalidExprStatementFunction (functionName : Name)
    (expr : Solidity.Expr) : FunctionDecl :=
  { name := some functionName
    visibility := some Visibility.public_
    mutability := StateMutability.pure
    body := some (Stmt.expr expr) }

def checkedInvalidExprStatementContract (contractName : Name)
    (expr : Solidity.Expr) : ContractDecl :=
  { name := contractName
    items :=
      [ContractItem.function
        (checkedInvalidExprStatementFunction "bad" expr)] }

def checkedMemoryAllocationInvalidSourcesRejected : Bool :=
  Result.isError
      (TypecheckedInput.checkedSourceUnit
        (checkedInvalidExprStatementContract "BadFixedArrayNew"
          (Expr.newExpr (Ty.array (Ty.uint 256) (some 3))
            [Arg.positional
              (Expr.literal (Literal.number "3"))]))) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit
        (checkedInvalidExprStatementContract "BadDynamicArrayNewArity0"
          (Expr.newExpr (Ty.array (Ty.uint 256) none) []))) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit
        (checkedInvalidExprStatementContract "BadDynamicArrayNewArity2"
          (Expr.newExpr (Ty.array (Ty.uint 256) none)
            [ Arg.positional (Expr.literal (Literal.number "3"))
            , Arg.positional (Expr.literal (Literal.number "4")) ]))) &&
    Result.isError
      (CheckedInput.program
        (checkedInvalidExprStatementContract "BadNewBytesArity0"
          (Expr.newExpr Ty.bytes []))) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit
        (checkedInvalidExprStatementContract "BadNewBytesArity2"
          (Expr.newExpr Ty.bytes
            [ Arg.positional (Expr.literal (Literal.number "3"))
            , Arg.positional (Expr.literal (Literal.number "4")) ])))

def checkedStringEchoContractAccepted : Bool :=
  Result.isOk
    (TypecheckedInput.checkedSourceUnit
      Executable.Examples.stringEchoContract)

def checkedStringEchoDirectCallMatches :
    Except TypeError Bool :=
  checkedOwnCallBytesMatches 16
    Executable.Examples.stringEchoContract
    "echo" SolidCore.Solidity.Source.State.empty
    [SolidCore.Solidity.Source.Value.bytes
      ("ok".toList.map Char.toNat)]
    ("ok".toList.map Char.toNat)

def checkedStringEchoCalldataMatches :
    Except TypeError Bool := do
  let contract ←
    ContractDecl.checkedContract
      Executable.Examples.stringEchoContract
  let bytes := "ok".toList.map Char.toNat
  let calldata ←
    CheckedContract.functionCalldata contract "echo"
      [SolidCore.Solidity.Source.Value.bytes bytes]
  let result ←
    CheckedContract.callCalldata 16 contract
      SolidCore.Solidity.Source.State.empty calldata
  let expected ←
    checkedAbiEncodeValues
      [SolidCore.Solidity.Source.Ty.bytesCalldata]
      [SolidCore.Solidity.Source.Value.bytes bytes]
  Except.ok (result.success && result.output == expected)

def checkedCalldataArraySliceInput : CoreValue :=
  SolidCore.Solidity.Source.Value.dynamicArray
    [ SolidCore.Solidity.Source.Value.word 10
    , SolidCore.Solidity.Source.Value.word 20
    , SolidCore.Solidity.Source.Value.word 30
    , SolidCore.Solidity.Source.Value.word 40 ]

def checkedCalldataArraySliceMatches :
    Except TypeError Bool :=
  checkedOwnCallWordAndDynamicWordArrayMatches 16
    Executable.Examples.checkedMemoryAndCalldataContract
    "sliceArray" SolidCore.Solidity.Source.State.empty
    [checkedCalldataArraySliceInput] 20 [30, 40]

def checkedCalldataArraySliceAbiEncodeMatches :
    Except TypeError Bool := do
  let expected ←
    checkedAbiEncodeValues
      [SolidCore.Solidity.Source.Ty.dynamicArray
        SolidCore.Solidity.Source.Ty.uint256]
      [SolidCore.Solidity.Source.Value.dynamicArray
        (checkedWordValues [20, 30])]
  checkedOwnCallBytesMatches 16
    Executable.Examples.checkedMemoryAndCalldataContract
    "encodeSlice" SolidCore.Solidity.Source.State.empty
    [checkedCalldataArraySliceInput] expected

def checkedCalldataArraySliceOutOfBoundsPanics :
    Except TypeError Bool :=
  checkedOwnCallPanicMatches 16
    Executable.Examples.checkedMemoryAndCalldataContract
    "badSlice" SolidCore.Solidity.Source.State.empty
    [SolidCore.Solidity.Source.Value.dynamicArray
      (checkedWordValues [1, 2])] 0x32

def checkedAbiArrayContractAccepted : Bool :=
  Result.isOk
    (TypecheckedInput.checkedSourceUnit
      Executable.Examples.checkedAbiArrayContract)

def checkedFixedArrayAbiCalldataMatches :
    Except TypeError Bool :=
  checkedContractAbiOutputMatches 64
    Executable.Examples.checkedAbiArrayContract
    "sumPair"
    [ SolidCore.Solidity.Source.Value.fixedArray
        [ SolidCore.Solidity.Source.Value.word 5
        , SolidCore.Solidity.Source.Value.word 7 ]
    , SolidCore.Solidity.Source.Value.word 1 ]
    Executable.Examples.fixedArrayAbiExpectedOutput

def checkedFixedArrayThenBytesAbiCalldataMatches :
    Except TypeError Bool :=
  checkedContractAbiOutputMatches 64
    Executable.Examples.checkedAbiArrayContract
    "arrayThenBytes"
    [ SolidCore.Solidity.Source.Value.fixedArray
        [ SolidCore.Solidity.Source.Value.word 9
        , SolidCore.Solidity.Source.Value.word 10 ]
    , SolidCore.Solidity.Source.Value.bytes [1, 2, 3] ]
    Executable.Examples.fixedArrayThenBytesAbiExpectedOutput

def checkedDynamicFixedArrayAbiCalldataMatches :
    Except TypeError Bool :=
  checkedContractAbiOutputMatches 64
    Executable.Examples.checkedAbiArrayContract
    "bytesPair"
    [ Executable.Examples.dynamicFixedArrayAbiValue
    , SolidCore.Solidity.Source.Value.word 1 ]
    Executable.Examples.dynamicFixedArrayAbiExpectedOutput

def checkedStaticTupleAbiCalldataMatches :
    Except TypeError Bool :=
  checkedContractAbiOutputMatches 64
    Executable.Examples.checkedAbiArrayContract
    "staticTuple"
    [ Executable.Examples.staticTupleAbiValue
    , SolidCore.Solidity.Source.Value.word 5 ]
    Executable.Examples.staticTupleAbiExpectedOutput

def checkedDynamicTupleAbiCalldataMatches :
    Except TypeError Bool :=
  checkedContractAbiOutputMatches 64
    Executable.Examples.checkedAbiArrayContract
    "dynamicTuple"
    [ Executable.Examples.dynamicTupleAbiValue
    , SolidCore.Solidity.Source.Value.word 1 ]
    Executable.Examples.dynamicTupleAbiExpectedOutput

def checkedDynamicArrayAbiCalldataMatches :
    Except TypeError Bool :=
  checkedContractAbiOutputMatches 64
    Executable.Examples.checkedAbiArrayContract
    "arrayInfo"
    [ Executable.Examples.dynamicArrayAbiValue
    , SolidCore.Solidity.Source.Value.word 1 ]
    Executable.Examples.dynamicArrayAbiExpectedOutput

def checkedDynamicBytesArrayAbiCalldataMatches :
    Except TypeError Bool :=
  checkedContractAbiOutputMatches 64
    Executable.Examples.checkedAbiArrayContract
    "bytesArray"
    [Executable.Examples.dynamicBytesArrayAbiValue]
    Executable.Examples.dynamicBytesArrayAbiExpectedOutput

def checkedFixedBytesEchoCalldataMatches :
    Except TypeError Bool :=
  checkedContractAbiOutputMatches 16
    Executable.Examples.checkedAbiArrayContract
    "echo4"
    [SolidCore.Solidity.Source.Value.word 0xaabbccdd]
    (SolidCore.Solidity.Source.ABI.encodeValues?
      [SolidCore.Solidity.Source.Ty.fixedBytes 4]
      [SolidCore.Solidity.Source.Value.word 0xaabbccdd])

def checkedAbiBuiltinContractAccepted : Bool :=
  Result.isOk
    (TypecheckedInput.checkedSourceUnit
      Executable.Examples.checkedAbiBuiltinContract)

def checkedAbiEncodeSourceMatchesExpected :
    Except TypeError Bool := do
  let expected ←
    optionToExcept "abi.encode expected"
      Executable.Examples.abiEncodeSourceMatchesExpected
  let encoded ←
    optionToExcept "abi.encode bytes"
      (SolidCore.Solidity.Source.abiEncodeValues?
        [ SolidCore.Solidity.Source.Ty.uint256
        , SolidCore.Solidity.Source.Ty.bytesCalldata ]
        [ SolidCore.Solidity.Source.Value.word 7
        , SolidCore.Solidity.Source.Value.bytes [8, 9] ])
  let pack ←
    checkedOwnCallBytesMatches 16
      Executable.Examples.checkedAbiBuiltinContract
      "pack" SolidCore.Solidity.Source.State.empty
      [ SolidCore.Solidity.Source.Value.word 7
      , SolidCore.Solidity.Source.Value.bytes [8, 9] ] encoded
  let inferred ←
    checkedOwnCallBytesMatches 16
      Executable.Examples.checkedAbiBuiltinContract
      "packInferred" SolidCore.Solidity.Source.State.empty
      [ SolidCore.Solidity.Source.Value.word 7
      , SolidCore.Solidity.Source.Value.bytes [8, 9] ] encoded
  let localExpected ←
    checkedAbiEncodeValues
      [SolidCore.Solidity.Source.Ty.uint256]
      [SolidCore.Solidity.Source.Value.word 7]
  let localMatch ←
    checkedOwnCallBytesMatches 16
      Executable.Examples.checkedAbiBuiltinContract
      "packLocal" SolidCore.Solidity.Source.State.empty []
      localExpected
  Except.ok (expected && pack && inferred && localMatch)

def checkedKeccakAbiEncodeSourceMatchesExpected :
    Except TypeError Bool := do
  let encoded ←
    checkedAbiEncodeValues
      [ SolidCore.Solidity.Source.Ty.uint256
      , SolidCore.Solidity.Source.Ty.bytesCalldata ]
      [ SolidCore.Solidity.Source.Value.word 7
      , SolidCore.Solidity.Source.Value.bytes [8, 9] ]
  checkedOwnCallWordMatches 16
    Executable.Examples.checkedAbiBuiltinContract
    "hashPack" SolidCore.Solidity.Source.State.empty []
    (SolidCore.Solidity.Source.keccakWord encoded)

def checkedAbiEncodeWithSelectorMatchesExpected :
    Except TypeError Bool := do
  let expected ←
    optionToExcept "abi.encodeWithSelector expected"
      Executable.Examples.abiEncodeWithSelectorExpected
  let selector ←
    checkedOwnCallBytesMatches 16
      Executable.Examples.checkedAbiBuiltinContract
      "callData" SolidCore.Solidity.Source.State.empty [] expected
  let signature ←
    checkedOwnCallBytesMatches 16
      Executable.Examples.checkedAbiBuiltinContract
      "callDataBySignature" SolidCore.Solidity.Source.State.empty []
      expected
  let runtimeSignature ←
    checkedOwnCallBytesMatches 16
      Executable.Examples.checkedAbiBuiltinContract
      "callDataByRuntimeSignature"
      SolidCore.Solidity.Source.State.empty
      [ SolidCore.Solidity.Source.Value.bytes
          (Executable.stringUtf8Bytes
            Executable.Examples.selectorEncodingSignature)
      , SolidCore.Solidity.Source.Value.word 7 ] expected
  Except.ok (selector && signature && runtimeSignature)

def checkedAbiEncodePackedMatchesExpected :
    Except TypeError Bool := do
  let expectedPacked ←
    optionToExcept "abi.encodePacked expected"
      (SolidCore.Solidity.Source.abiEncodePackedValues?
        [ 0, 0, 0 ]
        [ SolidCore.Solidity.Source.Ty.fixedBytes 1
        , SolidCore.Solidity.Source.Ty.uint256
        , SolidCore.Solidity.Source.Ty.bytesCalldata ]
        [ SolidCore.Solidity.Source.Value.word 66
        , SolidCore.Solidity.Source.Value.word 3
        , SolidCore.Solidity.Source.Value.bytes [72, 105] ])
  let packed ←
    checkedOwnCallBytesMatches 16
      Executable.Examples.checkedAbiBuiltinContract
      "packed" SolidCore.Solidity.Source.State.empty []
      expectedPacked
  let inferred ←
    checkedOwnCallBytesMatches 16
      Executable.Examples.checkedAbiBuiltinContract
      "packedInferred" SolidCore.Solidity.Source.State.empty
      [ SolidCore.Solidity.Source.Value.word 66
      , SolidCore.Solidity.Source.Value.word 3
      , SolidCore.Solidity.Source.Value.bytes [72, 105] ]
      expectedPacked
  Except.ok (packed && inferred)

def checkedAbiDecodeSourceMatchesExpected :
    Except TypeError Bool := do
  let singleEncoded ←
    checkedAbiEncodeValues
      [SolidCore.Solidity.Source.Ty.uint256]
      [SolidCore.Solidity.Source.Value.word 7]
  let pairEncoded ←
    optionToExcept "abi.decode pair input"
      Executable.Examples.abiDecodeExampleBytes
  let single ←
    checkedOwnCallWordMatches 16
      Executable.Examples.checkedAbiBuiltinContract
      "decodeOne" SolidCore.Solidity.Source.State.empty
      [SolidCore.Solidity.Source.Value.bytes singleEncoded] 7
  let pair ←
    checkedOwnCallWordAndBytesMatches 16
      Executable.Examples.checkedAbiBuiltinContract
      "decodePair" SolidCore.Solidity.Source.State.empty
      [SolidCore.Solidity.Source.Value.bytes pairEncoded] 7 [8, 9]
  Except.ok (single && pair)

def checkedAbiDecodeMalformedSourceReverts :
    Except TypeError Bool :=
  checkedOwnCallPanicMatches 16
    Executable.Examples.checkedAbiBuiltinContract
    "badDecode" SolidCore.Solidity.Source.State.empty [] 0

def checkedAbiBuiltinSourceDisciplineAccepted : Bool :=
    Result.isOk
      (TypecheckedInput.checkedSourceUnit
        abiEncodeExternalFunctionPointerSource) &&
    Result.isOk (TypecheckedInput.checkedSourceUnit abiDecodeSource) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit
        abiEncodePackedStaticElementArraySource) &&
    Result.isOk (TypecheckedInput.checkedSourceUnit bytesConcatSource)

def checkedAbiBuiltinSourceDisciplineRejected : Bool :=
  Result.isError
      (TypecheckedInput.checkedSourceUnit
        abiEncodeInternalFunctionPointerSource) &&
    Result.isError (TypecheckedInput.checkedSourceUnit badAbiDecodeSource) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit
        badAbiEncodePackedStructSource) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit
        badAbiEncodePackedNestedArraySource) &&
    Result.isError (TypecheckedInput.checkedSourceUnit badBytesConcatSource)

def checkedAbiEncodeExternalFunctionPointerMatches :
    Except TypeError Bool := do
  let pointer :=
    SolidCore.Solidity.Source.Value.externalFunction
      0xbeef Executable.Examples.selectorEncodingSelector
  let expected ←
    checkedAbiEncodeValues
      [SolidCore.Solidity.Source.Ty.externalFunction] [pointer]
  let result ←
    CheckedInput.callContract 16 abiEncodeExternalFunctionPointerSource
      "AbiEncodeExternalFunctionPointer"
      (SolidCore.Solidity.Source.CallTarget.name
        "packExternalFunction")
      SolidCore.Solidity.Source.State.empty [pointer]
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _
      [SolidCore.Solidity.Source.Value.bytes bytes] =>
      Except.ok (bytes == expected)
  | _ => Except.ok false

def checkedAbiDecodeFixtureMatches : Except TypeError Bool :=
  checkedCallWordMatches 16 abiDecodeSource
    "AbiDecode" "decode" SolidCore.Solidity.Source.State.empty
    [SolidCore.Solidity.Source.Value.bytes
      (SolidCore.Solidity.Source.ABI.encodeWord 7)] 7

def checkedBytesConcatFixtureMatches : Except TypeError Bool := do
  let result ←
    CheckedInput.callContract 16 bytesConcatSource "BytesConcat"
      (SolidCore.Solidity.Source.CallTarget.name "join")
      SolidCore.Solidity.Source.State.empty []
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _
      [SolidCore.Solidity.Source.Value.bytes bytes] =>
      Except.ok (bytes == [1, 0, 0, 0, 0])
  | _ => Except.ok false

def checkedAbiBuiltinSemanticsMatch :
    Except TypeError Bool := do
  let encode ← checkedAbiEncodeSourceMatchesExpected
  let hash ← checkedKeccakAbiEncodeSourceMatchesExpected
  let selector ← checkedAbiEncodeWithSelectorMatchesExpected
  let packed ← checkedAbiEncodePackedMatchesExpected
  let decode ← checkedAbiDecodeSourceMatchesExpected
  let malformed ← checkedAbiDecodeMalformedSourceReverts
  let externalFunction ← checkedAbiEncodeExternalFunctionPointerMatches
  let decodeFixture ← checkedAbiDecodeFixtureMatches
  let bytesConcatFixture ← checkedBytesConcatFixtureMatches
  Except.ok
    (checkedAbiBuiltinContractAccepted &&
      checkedAbiBuiltinSourceDisciplineAccepted &&
      checkedAbiBuiltinSourceDisciplineRejected &&
      encode && hash && selector && packed && decode && malformed &&
      externalFunction && decodeFixture && bytesConcatFixture)

def checkedAbiEncodeCallSourceUnitAccepted : Bool :=
  Result.isOk
    (TypecheckedInput.checkedSourceUnit
      Executable.Examples.checkedAbiEncodeCallSourceUnit)

def checkedAbiEncodeCallSourceMatchesExpected :
    Except TypeError Bool := do
  let expected ←
    optionToExcept "abi.encodeCall expected"
      Executable.Examples.abiEncodeCallExpected
  let result ←
    CheckedInput.callContract 16
      Executable.Examples.checkedAbiEncodeCallSourceUnit
      "CheckedAbiEncodeCall"
      (SolidCore.Solidity.Source.CallTarget.name
        "callDataByEncodeCall")
      SolidCore.Solidity.Source.State.empty
      [ SolidCore.Solidity.Source.Value.word 0x100
      , SolidCore.Solidity.Source.Value.word 7
      , SolidCore.Solidity.Source.Value.bytes [8, 9] ]
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _
      [SolidCore.Solidity.Source.Value.bytes bytes] =>
      Except.ok (bytes == expected)
  | _ => Except.ok false

def checkedExternalFunctionPointerContractAccepted : Bool :=
  Result.isOk
    (TypecheckedInput.checkedSourceUnit
      Executable.Examples.checkedExternalFunctionPointerContract)

def checkedAbiEncodeCallExternalPointerMatchesExpected :
    Except TypeError Bool := do
  let expected ←
    optionToExcept "abi.encodeCall external pointer expected"
      Executable.Examples.abiEncodeCallExternalPointerExpected
  checkedOwnCallBytesMatches 16
    Executable.Examples.checkedExternalFunctionPointerContract
    "callDataByExternalPointer"
    SolidCore.Solidity.Source.State.empty
    [ SolidCore.Solidity.Source.Value.externalFunction
        0xbeef Executable.Examples.selectorEncodingSelector
    , SolidCore.Solidity.Source.Value.word 7 ]
    expected

def checkedExternalFunctionMembersMatch :
    Except TypeError Bool :=
  checkedOwnCallWordPairMatches 16
    Executable.Examples.checkedExternalFunctionPointerContract
    "externalFunctionMembers"
    SolidCore.Solidity.Source.State.empty
    [SolidCore.Solidity.Source.Value.externalFunction
      0xbeef Executable.Examples.selectorEncodingSelector]
    Executable.Examples.selectorEncodingSelector 0xbeef

def checkedExternalFunctionPointerEqualityMatches :
    Except TypeError Bool := do
  let pointer :=
    SolidCore.Solidity.Source.Value.externalFunction
      0xbeef Executable.Examples.selectorEncodingSelector
  let other :=
    SolidCore.Solidity.Source.Value.externalFunction
      0xbeef Executable.Examples.externalFunctionPointerOtherSelector
  let same ←
    checkedOwnCallWordPairMatches 16
      Executable.Examples.checkedExternalFunctionPointerContract
      "externalFunctionEquality"
      SolidCore.Solidity.Source.State.empty
      [pointer, pointer] 1 0
  let different ←
    checkedOwnCallWordPairMatches 16
      Executable.Examples.checkedExternalFunctionPointerContract
      "externalFunctionEquality"
      SolidCore.Solidity.Source.State.empty
      [pointer, other] 0 1
  Except.ok (same && different)

def checkedExternalFunctionAbiCleanDecodeMatches : Bool :=
  match Executable.Examples.externalFunctionAbiCleanDecodeMatches with
  | some true => true
  | _ => false

def checkedExternalFunctionAbiRejectsDirtyPadding : Bool :=
  Executable.Examples.externalFunctionAbiRejectsDirtyPadding

def checkedExternalFunctionPointerCallMatches :
    Except TypeError Bool := do
  let responder ←
    optionToExcept "external function pointer call responder"
      Executable.Examples.externalFunctionPointerCallResponder?
  let result ←
    ContractDecl.checkedCallFunctionWithContextFailOpen 16 responder
      Executable.Examples.checkedExternalFunctionPointerContract
      "callGetter" SolidCore.Solidity.Source.Context.empty
      SolidCore.Solidity.Source.State.empty
      [SolidCore.Solidity.Source.Value.externalFunction
        0xbeef Executable.Examples.externalFunctionPointerGetterSelector]
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _
      [SolidCore.Solidity.Source.Value.word value] =>
      Except.ok (SolidCore.Solidity.Source.wordEq value 99)
  | _ => Except.ok false

def checkedExternalFunctionPointerPayableCallMatches :
    Except TypeError Bool := do
  let responder ←
    optionToExcept "external function pointer payable call responder"
      Executable.Examples.externalFunctionPointerPayableCallResponder?
  let context :=
    { SolidCore.Solidity.Source.Context.empty with
      accountCodes := [(0xbeef, [1])] }
  let result ←
    ContractDecl.checkedCallFunctionWithContextFailOpen 16 responder
      Executable.Examples.checkedExternalFunctionPointerContract
      "callSetter" context SolidCore.Solidity.Source.State.empty
      [ SolidCore.Solidity.Source.Value.externalFunction
          0xbeef Executable.Examples.selectorEncodingSelector
      , SolidCore.Solidity.Source.Value.word 7 ]
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _ [] =>
      Except.ok true
  | _ => Except.ok false

def checkedExternalFunctionPointerNonpayableGasMatches :
    Except TypeError Bool := do
  let encodedArgs ←
    checkedAbiEncodeValues
      [SolidCore.Solidity.Source.Ty.uint256]
      [SolidCore.Solidity.Source.Value.word 11]
  let context :=
    { SolidCore.Solidity.Source.Context.empty with
      accountCodes := [(0xbeef, [1])] }
  let result ←
    ContractDecl.checkedCallFunctionWithContextFailOpen 16
      (SolidCore.Solidity.Source.responderOfResults
        [ { kind := SolidCore.Solidity.Source.LowLevelCallKind.call
            target := 0xbeef
            calldata :=
              SolidCore.Solidity.Source.wordToBytesBE
                SolidCore.Solidity.Source.selectorBytes
                Executable.Examples.selectorEncodingSelector ++ encodedArgs
            gas? := some 777
            success := true
            output := [] } ]
      [])
      Executable.Examples.checkedExternalFunctionPointerContract
      "callSetterWithGas" context
      SolidCore.Solidity.Source.State.empty
      [ SolidCore.Solidity.Source.Value.externalFunction
          0xbeef Executable.Examples.selectorEncodingSelector
      , SolidCore.Solidity.Source.Value.word 11 ]
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _ [] =>
      Except.ok true
  | _ => Except.ok false

def checkedExternalFunctionPointerNonpayableValueRejected :
    Bool :=
  Result.isError
    (TypecheckedInput.checkedSourceUnit
      Executable.Examples.checkedExternalFunctionPointerNonpayableValueContract)

def checkedExternalFunctionPointerTryCatchSuccessMatches :
    Except TypeError Bool := do
  let responder ←
    optionToExcept "external function pointer try/catch responder"
      Executable.Examples.externalFunctionPointerTryCatchSuccessResponder?
  let result ←
    ContractDecl.checkedCallFunctionWithContextFailOpen 16 responder
      Executable.Examples.checkedExternalFunctionPointerContract
      "tryGetter" SolidCore.Solidity.Source.Context.empty
      SolidCore.Solidity.Source.State.empty
      [SolidCore.Solidity.Source.Value.externalFunction
        0xbeef Executable.Examples.externalFunctionPointerGetterSelector]
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _
      [SolidCore.Solidity.Source.Value.word value] =>
      Except.ok (SolidCore.Solidity.Source.wordEq value 55)
  | _ => Except.ok false

def checkedExternalFunctionPointerTryCatchCatchMatches :
    Except TypeError Bool := do
  let result ←
    ContractDecl.checkedCallFunctionWithContext 16
      Executable.Examples.checkedExternalFunctionPointerContract
      "tryGetter" SolidCore.Solidity.Source.Context.empty
      SolidCore.Solidity.Source.State.empty
      [SolidCore.Solidity.Source.Value.externalFunction
        0xbeef Executable.Examples.externalFunctionPointerGetterSelector]
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _
      [SolidCore.Solidity.Source.Value.word value] =>
      Except.ok (SolidCore.Solidity.Source.wordEq value 7)
  | _ => Except.ok false

def checkedHighLevelExternalSourceAccepted : Bool :=
  Result.isOk
    (TypecheckedInput.checkedSourceUnit
      Executable.Examples.checkedHighLevelExternalSource)

def checkedHighLevelExternalCalldata (signature : String)
    (tys : List SolidCore.Solidity.Source.Ty)
    (args : List CoreValue) : Except TypeError (List Byte) :=
  optionToExcept ("external calldata " ++ signature)
    (Executable.Examples.externalCalldata? signature tys args)

def checkedHighLevelExternalWordOutput (value : Word) :
    Except TypeError (List Byte) :=
  checkedAbiEncodeValues
    [SolidCore.Solidity.Source.Ty.uint256]
    [SolidCore.Solidity.Source.Value.word value]

def checkedHighLevelExternalWordPairOutput
    (left right : Word) : Except TypeError (List Byte) :=
  checkedAbiEncodeValues
    [ SolidCore.Solidity.Source.Ty.uint256
    , SolidCore.Solidity.Source.Ty.uint256 ]
    [ SolidCore.Solidity.Source.Value.word left
    , SolidCore.Solidity.Source.Value.word right ]

def checkedHighLevelExternalResult
    (kind : SolidCore.Solidity.Source.LowLevelCallKind)
    (signature : String)
    (tys : List SolidCore.Solidity.Source.Ty)
    (args : List CoreValue) (output : List Byte)
    (value : Word := 0) (gas? : Option Word := none)
    (success : Bool := true) :
    Except TypeError SolidCore.Solidity.Source.LowLevelCallResult := do
  let calldata ← checkedHighLevelExternalCalldata signature tys args
  Except.ok
    { kind := kind
      target := 0xbeef
      calldata := calldata
      value := value
      gas? := gas?
      success := success
      output := output }

def checkedHighLevelExternalCall
    (functionName : Name) (context : CoreContext)
    (args : List CoreValue)
    (responder : SolidCore.Solidity.Source.ScriptedResponder := []) : Except TypeError CoreCallResult := do
  let contract ←
    CheckedInput.contract
      Executable.Examples.checkedHighLevelExternalSource
      "CheckedHighLevelCaller"
  CheckedContract.callFunctionWithContextFailOpen 32 responder
    contract functionName
    context SolidCore.Solidity.Source.State.empty args

def checkedHighLevelExternalContext
    (accountCodes : List (Word × List Byte) := []) :
    Except TypeError CoreContext := do
  let contract ←
    CheckedInput.contract
      Executable.Examples.checkedHighLevelExternalSource
      "CheckedHighLevelCaller"
  Except.ok
    { contract.core.context with
      accountCodes := accountCodes }

def checkedHighLevelExternalWordCallMatches
    (functionName : Name) (context : CoreContext)
    (args : List CoreValue) (expected : Word)
    (responder : SolidCore.Solidity.Source.ScriptedResponder := []) :
    Except TypeError Bool := do
  let result ←
    checkedHighLevelExternalCall functionName context args responder
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _
      [SolidCore.Solidity.Source.Value.word value] =>
      Except.ok (SolidCore.Solidity.Source.wordEq value expected)
  | _ => Except.ok false

def checkedHighLevelExternalReturnMatches :
    Except TypeError Bool := do
  let output ← checkedHighLevelExternalWordOutput 77
  let result ←
    checkedHighLevelExternalResult
      SolidCore.Solidity.Source.LowLevelCallKind.call
      "get()" [] [] output
  let context ← checkedHighLevelExternalContext
  let responder :=
    SolidCore.Solidity.Source.responderOfResults [result] []
  checkedHighLevelExternalWordCallMatches "read" context
    [SolidCore.Solidity.Source.Value.word 0xbeef] 77 responder

def checkedHighLevelExternalNamedArgsReorderedMatches :
    Except TypeError Bool := do
  let output ← checkedHighLevelExternalWordOutput 42
  let result ←
    checkedHighLevelExternalResult
      SolidCore.Solidity.Source.LowLevelCallKind.call
      "quote(uint256,uint256)"
      [ SolidCore.Solidity.Source.Ty.uint256
      , SolidCore.Solidity.Source.Ty.uint256 ]
      [ SolidCore.Solidity.Source.Value.word 40
      , SolidCore.Solidity.Source.Value.word 2 ] output
  let context ← checkedHighLevelExternalContext
  let responder :=
    SolidCore.Solidity.Source.responderOfResults [result] []
  checkedHighLevelExternalWordCallMatches "readNamed" context
    [ SolidCore.Solidity.Source.Value.word 0xbeef
    , SolidCore.Solidity.Source.Value.word 40
    , SolidCore.Solidity.Source.Value.word 2 ] 42 responder

def checkedHighLevelExternalVarDeclMatches :
    Except TypeError Bool := do
  let output ← checkedHighLevelExternalWordOutput 40
  let result ←
    checkedHighLevelExternalResult
      SolidCore.Solidity.Source.LowLevelCallKind.call
      "get()" [] [] output
  let context ← checkedHighLevelExternalContext
  let responder :=
    SolidCore.Solidity.Source.responderOfResults [result] []
  checkedHighLevelExternalWordCallMatches "readViaLocal" context
    [SolidCore.Solidity.Source.Value.word 0xbeef] 41 responder

def checkedHighLevelExternalMultiVarDeclMatches :
    Except TypeError Bool := do
  let output ← checkedHighLevelExternalWordPairOutput 20 22
  let result ←
    checkedHighLevelExternalResult
      SolidCore.Solidity.Source.LowLevelCallKind.call
      "pair()" [] [] output
  let context ← checkedHighLevelExternalContext
  let responder :=
    SolidCore.Solidity.Source.responderOfResults [result] []
  checkedHighLevelExternalWordCallMatches "readPairViaLocals" context
    [SolidCore.Solidity.Source.Value.word 0xbeef] 42 responder

def checkedHighLevelExternalPayableValueMatches :
    Except TypeError Bool := do
  let output ← checkedHighLevelExternalWordOutput 22
  let result ←
    checkedHighLevelExternalResult
      SolidCore.Solidity.Source.LowLevelCallKind.call
      "payQuote()" [] [] output 9 (some 1234)
  let context ← checkedHighLevelExternalContext
  let responder :=
    SolidCore.Solidity.Source.responderOfResults [result] []
  checkedHighLevelExternalWordCallMatches "payKnown" context
    [ SolidCore.Solidity.Source.Value.word 0xbeef
    , SolidCore.Solidity.Source.Value.word 9 ] 22 responder

def checkedHighLevelExternalNonpayableGasMatches :
    Except TypeError Bool := do
  let output ← checkedHighLevelExternalWordOutput 33
  let result ←
    checkedHighLevelExternalResult
      SolidCore.Solidity.Source.LowLevelCallKind.call
      "plainQuote()" [] [] output 0 (some 5678)
  let context ← checkedHighLevelExternalContext
  let responder :=
    SolidCore.Solidity.Source.responderOfResults [result] []
  checkedHighLevelExternalWordCallMatches "nonpayableGas" context
    [SolidCore.Solidity.Source.Value.word 0xbeef] 33 responder

def checkedHighLevelExternalAssignMatches :
    Except TypeError Bool := do
  let output ← checkedHighLevelExternalWordOutput 12
  let result ←
    checkedHighLevelExternalResult
      SolidCore.Solidity.Source.LowLevelCallKind.call
      "get()" [] [] output
  let context ← checkedHighLevelExternalContext
  let responder :=
    SolidCore.Solidity.Source.responderOfResults [result] []
  let callResult ←
    checkedHighLevelExternalCall "assignFromExternal" context
      [SolidCore.Solidity.Source.Value.word 0xbeef] responder
  match callResult with
  | SolidCore.Solidity.Source.CallResult.returned state [] =>
      Except.ok (SolidCore.Solidity.Source.wordEq (state.loadSlot 0) 12)
  | _ => Except.ok false

def checkedHighLevelExternalDiscardMatches :
    Except TypeError Bool := do
  let result ←
    checkedHighLevelExternalResult
      SolidCore.Solidity.Source.LowLevelCallKind.call
      "notify()" [] [] []
  let context ← checkedHighLevelExternalContext [(0xbeef, [1])]
  let responder :=
    SolidCore.Solidity.Source.responderOfResults [result] []
  let callResult ←
    checkedHighLevelExternalCall "notifyExternal" context
      [SolidCore.Solidity.Source.Value.word 0xbeef] responder
  match callResult with
  | SolidCore.Solidity.Source.CallResult.returned _ [] =>
      Except.ok true
  | _ => Except.ok false

def checkedHighLevelExternalNoReturnMissingCodeCaught :
    Except TypeError Bool := do
  let result ←
    checkedHighLevelExternalResult
      SolidCore.Solidity.Source.LowLevelCallKind.call
      "notify()" [] [] []
  let context ← checkedHighLevelExternalContext
  let responder :=
    SolidCore.Solidity.Source.responderOfResults [result] []
  checkedHighLevelExternalWordCallMatches "notifyOrCatch" context
    [SolidCore.Solidity.Source.Value.word 0xbeef] 2 responder

def checkedHighLevelExternalNoReturnCodePresentSucceeds :
    Except TypeError Bool := do
  let result ←
    checkedHighLevelExternalResult
      SolidCore.Solidity.Source.LowLevelCallKind.call
      "notify()" [] [] []
  let context ← checkedHighLevelExternalContext [(0xbeef, [1])]
  let responder :=
    SolidCore.Solidity.Source.responderOfResults [result] []
  checkedHighLevelExternalWordCallMatches "notifyOrCatch" context
    [SolidCore.Solidity.Source.Value.word 0xbeef] 1 responder

def checkedHighLevelExternalReturnNoCodeUsesReturndata :
    Except TypeError Bool := do
  let output ← checkedHighLevelExternalWordOutput 5
  let result ←
    checkedHighLevelExternalResult
      SolidCore.Solidity.Source.LowLevelCallKind.call
      "get()" [] [] output
  let context ← checkedHighLevelExternalContext
  let responder :=
    SolidCore.Solidity.Source.responderOfResults [result] []
  checkedHighLevelExternalWordCallMatches "readNoCodeReturn" context
    [SolidCore.Solidity.Source.Value.word 0xbeef] 5 responder

def checkedHighLevelExternalFailureBubblesRaw :
    Except TypeError Bool := do
  let result ←
    checkedHighLevelExternalResult
      SolidCore.Solidity.Source.LowLevelCallKind.call
      "get()" [] [] [0xdd, 0xee] 0 none false
  let context ← checkedHighLevelExternalContext
  let responder :=
    SolidCore.Solidity.Source.responderOfResults [result] []
  let callResult ←
    checkedHighLevelExternalCall "read" context
      [SolidCore.Solidity.Source.Value.word 0xbeef] responder
  match callResult with
  | SolidCore.Solidity.Source.CallResult.reverted _
      (SolidCore.Solidity.Source.RevertData.raw bytes) =>
      Except.ok (bytes == [0xdd, 0xee])
  | _ => Except.ok false

def checkedHighLevelExternalViewStaticcallMatches :
    Except TypeError Bool := do
  let output ← checkedHighLevelExternalWordOutput 77
  let result ←
    checkedHighLevelExternalResult
      SolidCore.Solidity.Source.LowLevelCallKind.staticcall
      "viewGet()" [] [] output
  let context ← checkedHighLevelExternalContext
  let responder :=
    SolidCore.Solidity.Source.responderOfResults [result] []
  checkedHighLevelExternalWordCallMatches "readView" context
    [SolidCore.Solidity.Source.Value.word 0xbeef] 77 responder

def checkedHighLevelExternalPureGasStaticcallMatches :
    Except TypeError Bool := do
  let output ← checkedHighLevelExternalWordOutput 88
  let result ←
    checkedHighLevelExternalResult
      SolidCore.Solidity.Source.LowLevelCallKind.staticcall
      "pureGet()" [] [] output 0 (some 4321)
  let context ← checkedHighLevelExternalContext
  let responder :=
    SolidCore.Solidity.Source.responderOfResults [result] []
  checkedHighLevelExternalWordCallMatches "readPureWithGas" context
    [SolidCore.Solidity.Source.Value.word 0xbeef] 88 responder

def checkedHighLevelExternalGetterStaticcallMatches :
    Except TypeError Bool := do
  let output ← checkedHighLevelExternalWordOutput 99
  let result ←
    checkedHighLevelExternalResult
      SolidCore.Solidity.Source.LowLevelCallKind.staticcall
      "x()" [] [] output
  let context ← checkedHighLevelExternalContext
  let responder :=
    SolidCore.Solidity.Source.responderOfResults [result] []
  checkedHighLevelExternalWordCallMatches "readGetter" context
    [SolidCore.Solidity.Source.Value.word 0xbeef] 99 responder

def checkedHighLevelThisStaticcallMatches
    (functionName signature : Name) (expected : Word) :
    Except TypeError Bool := do
  let output ← checkedHighLevelExternalWordOutput expected
  let calldata ← checkedHighLevelExternalCalldata signature [] []
  let contract ←
    CheckedInput.contract
      Executable.Examples.checkedHighLevelExternalSource
      "CheckedThisStatic"
  let result ←
    CheckedContract.callFunctionWithContextFailOpen 16
      (SolidCore.Solidity.Source.responderOfResults
          [ { kind := SolidCore.Solidity.Source.LowLevelCallKind.staticcall
              target := 0xcafe
              calldata := calldata
              success := true
              output := output } ]
      []) contract functionName
      { contract.core.context with
        self := 0xcafe }
      SolidCore.Solidity.Source.State.empty []
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _
      [SolidCore.Solidity.Source.Value.word value] =>
      Except.ok (SolidCore.Solidity.Source.wordEq value expected)
  | _ => Except.ok false

def checkedHighLevelThisViewStaticcallMatches :
    Except TypeError Bool :=
  checkedHighLevelThisStaticcallMatches "readThisView" "get()" 123

def checkedHighLevelThisGetterStaticcallMatches :
    Except TypeError Bool :=
  checkedHighLevelThisStaticcallMatches "readThisGetter" "x()" 456

def checkedHighLevelExternalInvalidSourcesRejected : Bool :=
  Result.isError
      (TypecheckedInput.checkedSourceUnit
        Executable.Examples.checkedHighLevelExternalDuplicateNamedArgsSource) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit
        Executable.Examples.checkedHighLevelExternalViewValueSource) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit
        Executable.Examples.checkedHighLevelExternalNonpayableValueSource)

def checkedCallContextContractAccepted : Bool :=
  Result.isOk
    (TypecheckedInput.checkedSourceUnit
      Executable.Examples.checkedCallContextContract)

def checkedMsgSigCalldataMatches : Except TypeError Bool := do
  let calldata ←
    ContractDecl.checkedFunctionCalldata
      Executable.Examples.checkedCallContextContract "sig" []
  let result ←
    ContractDecl.checkedCallCalldata 8
      Executable.Examples.checkedCallContextContract
      SolidCore.Solidity.Source.State.empty calldata
  let selector ←
    optionToExcept "msg.sig selector"
      (SolidCore.Solidity.Source.ABI.readSelector? calldata)
  let expected ←
    checkedAbiEncodeValues
      [SolidCore.Solidity.Source.Ty.fixedBytes 4]
      [SolidCore.Solidity.Source.Value.word selector]
  Except.ok (result.success && result.output == expected)

def checkedMsgContextCalldataMatches : Except TypeError Bool := do
  let calldata ←
    ContractDecl.checkedFunctionCalldata
      Executable.Examples.checkedCallContextContract "inspect"
      [SolidCore.Solidity.Source.Value.word 7]
  let result ←
    ContractDecl.checkedCallCalldataAtFrom 16
      Executable.Examples.checkedCallContextContract
      SolidCore.Solidity.Source.State.empty
      0xc0de 0xabc 55 calldata
  let selector ←
    optionToExcept "msg context selector"
      (SolidCore.Solidity.Source.ABI.readSelector? calldata)
  let expected ←
    checkedAbiEncodeValues
      [ SolidCore.Solidity.Source.Ty.address
      , SolidCore.Solidity.Source.Ty.uint256
      , SolidCore.Solidity.Source.Ty.fixedBytes 4
      , SolidCore.Solidity.Source.Ty.bytesCalldata ]
      [ SolidCore.Solidity.Source.Value.word 0xabc
      , SolidCore.Solidity.Source.Value.word 55
      , SolidCore.Solidity.Source.Value.word selector
      , SolidCore.Solidity.Source.Value.bytes calldata ]
  Except.ok (result.success && result.output == expected)

def checkedAbiSelfAddressAtMatches : Except TypeError Bool := do
  let calldata ←
    ContractDecl.checkedFunctionCalldata
      Executable.Examples.checkedCallContextContract "who" []
  let result ←
    ContractDecl.checkedCallCalldataAt 8
      Executable.Examples.checkedCallContextContract
      SolidCore.Solidity.Source.State.empty 0xcafe calldata
  let expected ←
    checkedAbiEncodeValues
      [SolidCore.Solidity.Source.Ty.address]
      [SolidCore.Solidity.Source.Value.word 0xcafe]
  Except.ok (result.success && result.output == expected)

def checkedCallFunctionWithContextWordPairMatches (fuel : Nat)
    (decl : SourceContractDecl) (functionName : Name)
    (context : SolidCore.Solidity.Source.Context)
    (state : CoreState) (args : List CoreValue)
    (expectedA expectedB : Word)
    (responder : SolidCore.Solidity.Source.ScriptedResponder := []) : Except TypeError Bool := do
  let result ←
    ContractDecl.checkedCallFunctionWithContextFailOpen
      fuel responder decl functionName context state args
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _
      [ SolidCore.Solidity.Source.Value.word a
      , SolidCore.Solidity.Source.Value.word b ] =>
      Except.ok
        (SolidCore.Solidity.Source.wordEq a expectedA &&
          SolidCore.Solidity.Source.wordEq b expectedB)
  | _ => Except.ok false

def checkedCallFunctionWithContextWordTripleMatches (fuel : Nat)
    (decl : SourceContractDecl) (functionName : Name)
    (context : SolidCore.Solidity.Source.Context)
    (state : CoreState) (args : List CoreValue)
    (expectedA expectedB expectedC : Word) : Except TypeError Bool := do
  let result ←
    ContractDecl.checkedCallFunctionWithContext
      fuel decl functionName context state args
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _
      [ SolidCore.Solidity.Source.Value.word a
      , SolidCore.Solidity.Source.Value.word b
      , SolidCore.Solidity.Source.Value.word c ] =>
      Except.ok
        (SolidCore.Solidity.Source.wordEq a expectedA &&
          SolidCore.Solidity.Source.wordEq b expectedB &&
          SolidCore.Solidity.Source.wordEq c expectedC)
  | _ => Except.ok false

def checkedEnvironmentContractAccepted : Bool :=
  Result.isOk
    (TypecheckedInput.checkedSourceUnit
      Executable.Examples.checkedEnvironmentContract)

def checkedEnvironmentGlobalsMatch : Except TypeError Bool := do
  let result ←
    ContractDecl.checkedCallFunctionWithContext 16
      Executable.Examples.checkedEnvironmentContract "env"
      Executable.Examples.environmentGlobalsContext
      SolidCore.Solidity.Source.State.empty []
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _
      [ SolidCore.Solidity.Source.Value.word timestamp
      , SolidCore.Solidity.Source.Value.word number
      , SolidCore.Solidity.Source.Value.word basefee
      , SolidCore.Solidity.Source.Value.word blobbasefee
      , SolidCore.Solidity.Source.Value.word chainid
      , SolidCore.Solidity.Source.Value.word coinbase
      , SolidCore.Solidity.Source.Value.word gaslimit
      , SolidCore.Solidity.Source.Value.word origin
      , SolidCore.Solidity.Source.Value.word gasprice
      , SolidCore.Solidity.Source.Value.word remaining ] =>
      Except.ok
        (SolidCore.Solidity.Source.wordEq timestamp 100 &&
          SolidCore.Solidity.Source.wordEq number 7 &&
          SolidCore.Solidity.Source.wordEq basefee 11 &&
          SolidCore.Solidity.Source.wordEq blobbasefee 12 &&
          SolidCore.Solidity.Source.wordEq chainid 1 &&
          SolidCore.Solidity.Source.wordEq coinbase 0xcb &&
          SolidCore.Solidity.Source.wordEq gaslimit 30000000 &&
          SolidCore.Solidity.Source.wordEq origin 0xabc &&
          SolidCore.Solidity.Source.wordEq gasprice 50 &&
            SolidCore.Solidity.Source.wordEq remaining 999)
  | _ => Except.ok false

def checkedEnvironmentGlobalsWithContextMatch
    (context : SolidCore.Solidity.Source.Context)
    (expectedBasefee expectedBlobbasefee expectedChainid :
      SolidCore.Solidity.Source.Word) : Except TypeError Bool := do
  let result ←
    ContractDecl.checkedCallFunctionWithContext 16
      Executable.Examples.checkedEnvironmentContract "env"
      context
      SolidCore.Solidity.Source.State.empty []
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _
      [ SolidCore.Solidity.Source.Value.word timestamp
      , SolidCore.Solidity.Source.Value.word number
      , SolidCore.Solidity.Source.Value.word basefee
      , SolidCore.Solidity.Source.Value.word blobbasefee
      , SolidCore.Solidity.Source.Value.word chainid
      , SolidCore.Solidity.Source.Value.word coinbase
      , SolidCore.Solidity.Source.Value.word gaslimit
      , SolidCore.Solidity.Source.Value.word origin
      , SolidCore.Solidity.Source.Value.word gasprice
      , SolidCore.Solidity.Source.Value.word remaining ] =>
      Except.ok
        (SolidCore.Solidity.Source.wordEq timestamp 100 &&
          SolidCore.Solidity.Source.wordEq number 7 &&
          SolidCore.Solidity.Source.wordEq basefee expectedBasefee &&
          SolidCore.Solidity.Source.wordEq blobbasefee
            expectedBlobbasefee &&
          SolidCore.Solidity.Source.wordEq chainid expectedChainid &&
          SolidCore.Solidity.Source.wordEq coinbase 0xcb &&
          SolidCore.Solidity.Source.wordEq gaslimit 30000000 &&
          SolidCore.Solidity.Source.wordEq origin 0xabc &&
          SolidCore.Solidity.Source.wordEq gasprice 50 &&
          SolidCore.Solidity.Source.wordEq remaining 999)
  | _ => Except.ok false

def checkedEnvironmentPreLondonBasefeeMatches :
    Except TypeError Bool :=
  checkedEnvironmentGlobalsWithContextMatch
    Executable.Examples.environmentGlobalsPreLondonContext 0 0 1

def checkedEnvironmentPreIstanbulChainidMatches :
    Except TypeError Bool :=
  checkedEnvironmentGlobalsWithContextMatch
    Executable.Examples.environmentGlobalsPreIstanbulContext 0 0 0

def checkedEnvironmentRandaoAliasMatches :
    Except TypeError Bool :=
  checkedCallFunctionWithContextWordPairMatches 16
    Executable.Examples.checkedEnvironmentContract
    "randaoAlias"
    Executable.Examples.environmentRandaoAliasContext
    SolidCore.Solidity.Source.State.empty [] 0x2222 0x2222

def checkedEnvironmentPreParisRandaoAliasMatches :
    Except TypeError Bool :=
  checkedCallFunctionWithContextWordPairMatches 16
    Executable.Examples.checkedEnvironmentContract
    "randaoAlias"
    Executable.Examples.environmentRandaoPreParisContext
    SolidCore.Solidity.Source.State.empty [] 0x1111 0x1111

def checkedEnvironmentHashMatches : Except TypeError Bool :=
  checkedCallFunctionWithContextWordTripleMatches 16
    Executable.Examples.checkedEnvironmentContract
    "hashes"
    Executable.Examples.environmentHashContext
    SolidCore.Solidity.Source.State.empty [] 0x1234 0x5678 0

def checkedEnvironmentHashPreCancunMatches :
    Except TypeError Bool :=
  checkedCallFunctionWithContextWordTripleMatches 16
    Executable.Examples.checkedEnvironmentContract
    "hashes"
    Executable.Examples.environmentHashPreCancunContext
    SolidCore.Solidity.Source.State.empty [] 0x1234 0 0

def checkedEnvironmentHashOutOfRangeMatches :
    Except TypeError Bool :=
  checkedCallFunctionWithContextWordTripleMatches 16
    Executable.Examples.checkedEnvironmentContract
    "hashes"
    Executable.Examples.environmentHashOutOfRangeContext
    SolidCore.Solidity.Source.State.empty [] 0 0 0

def checkedModularArithmeticContractAccepted : Bool :=
  Result.isOk
    (TypecheckedInput.checkedSourceUnit
      Executable.Examples.checkedModularArithmeticContract)

def checkedModularArithmeticMatches : Except TypeError Bool :=
  checkedOwnCallWordPairMatches 16
    Executable.Examples.checkedModularArithmeticContract
    "mods" SolidCore.Solidity.Source.State.empty [] 2 5

def checkedAddmodVariableZeroModulusPanics :
    Except TypeError Bool :=
  checkedOwnCallPanicMatches 16
    Executable.Examples.checkedModularArithmeticContract
    "addmodZero" SolidCore.Solidity.Source.State.empty
    [SolidCore.Solidity.Source.Value.word 0] 0x12

def checkedMulmodVariableZeroModulusPanics :
    Except TypeError Bool :=
  checkedOwnCallPanicMatches 16
    Executable.Examples.checkedModularArithmeticContract
    "mulmodZero" SolidCore.Solidity.Source.State.empty
    [SolidCore.Solidity.Source.Value.word 0] 0x12

-- MULMOD0: a compile-time-CONSTANT zero modulus in addmod/mulmod is Error 4195
-- "Arithmetic modulo zero" in solc's constant evaluator — a COMPILE reject.
-- These witnesses formerly pinned the pre-fix over-accept (compile then runtime
-- Panic 0x12); they now pin the corrected compile-time rejection. The RUNTIME
-- (non-constant modulus) Panic 0x12 stays covered by
-- checkedAddmodVariableZeroModulusPanics / checkedMulmodVariableZeroModulusPanics.
def checkedAddmodLiteralZeroModulusRejected : Bool :=
  Result.isError (TypecheckedInput.checkedSourceUnit addmodZeroLiteralSource)

def checkedMulmodLiteralZeroModulusRejected : Bool :=
  Result.isError (TypecheckedInput.checkedSourceUnit mulmodZeroLiteralSource)

def checkedModularArithmeticZeroLiteralSourcesRejected : Bool :=
  Result.isError
      (TypecheckedInput.checkedSourceUnit addmodZeroLiteralSource) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit mulmodZeroLiteralSource)

def checkedModularArithmeticInvalidSourcesRejected : Bool :=
  Result.isError
      (TypecheckedInput.checkedSourceUnit addmodSignedArgumentSource) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit mulmodSignedModulusSource)

def checkedHashBuiltinContractAccepted : Bool :=
  Result.isOk
    (TypecheckedInput.checkedSourceUnit
      Executable.Examples.checkedHashBuiltinContract)

def checkedKeccakBuiltinMatchesExpected : Except TypeError Bool :=
  checkedOwnCallWordMatches 16
    Executable.Examples.checkedHashBuiltinContract
    "hash" SolidCore.Solidity.Source.State.empty []
    (SolidCore.Solidity.Source.keccakWord [1, 2, 3])

def checkedErc7201BuiltinMatchesEipExample : Except TypeError Bool :=
  checkedOwnCallWordMatches 16
    Executable.Examples.checkedHashBuiltinContract
    "namespaceSlot" SolidCore.Solidity.Source.State.empty []
    0x183a6125c38840424c4a85fa12bab2ab606c4b6d0e7cc73c0c06ba5300eab500

def checkedExternalCryptoHashMatches : Except TypeError Bool :=
  checkedCallFunctionWithContextWordPairMatches 16
    Executable.Examples.checkedHashBuiltinContract
    "externalHashes"
    SolidCore.Solidity.Source.Context.empty
    SolidCore.Solidity.Source.State.empty [] 0xaaaa 0xbbbb
    Executable.Examples.externalCryptoHashResponder

def checkedExternalCryptoHashMissingPanics :
    Except TypeError Bool := do
  let result ←
    ContractDecl.checkedCallFunctionWithContext 16
      Executable.Examples.checkedHashBuiltinContract "missingHash"
      SolidCore.Solidity.Source.Context.empty
      SolidCore.Solidity.Source.State.empty []
  match result with
  | SolidCore.Solidity.Source.CallResult.reverted _
      (SolidCore.Solidity.Source.RevertData.panic code) =>
      Except.ok (SolidCore.Solidity.Source.wordEq code 0)
  | _ => Except.ok false

def checkedEcrecoverBuiltinMatches : Except TypeError Bool :=
  checkedCallFunctionWithContextWordPairMatches 16
    Executable.Examples.checkedHashBuiltinContract
    "recover"
    SolidCore.Solidity.Source.Context.empty
    SolidCore.Solidity.Source.State.empty [] 0xcafe 0
    Executable.Examples.ecrecoverBuiltinResponder

def checkedPrecompileBuiltinsStaticcallSharedResultsMatches :
    Except TypeError Bool := do
  let result ←
    ContractDecl.checkedCallFunctionWithContextFailOpen 16
      Executable.Examples.precompileBuiltinsStaticcallSharedResultsResponder
      Executable.Examples.checkedHashBuiltinContract
      "precompileBuiltinsAndCalls"
      SolidCore.Solidity.Source.Context.empty
      SolidCore.Solidity.Source.State.empty []
  let shaExpected :=
    SolidCore.Solidity.Source.wordToBytesBE
      SolidCore.Solidity.Source.wordBytes 0xaaaa
  let ripeExpected :=
    SolidCore.Solidity.Source.wordToBytesBE
      SolidCore.Solidity.Source.wordBytes 0xbbbb
  let recoverExpected :=
    SolidCore.Solidity.Source.wordToBytesBE
      SolidCore.Solidity.Source.wordBytes 0xcafe
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _
      [ SolidCore.Solidity.Source.Value.word sha
      , shaProbe
      , SolidCore.Solidity.Source.Value.word ripe
      , ripeProbe
      , SolidCore.Solidity.Source.Value.word recovered
      , recoverProbe ] => do
      let (shaSuccess, shaOutput) ←
        checkedDecodeLowLevelReturn shaProbe
      let (ripeSuccess, ripeOutput) ←
        checkedDecodeLowLevelReturn ripeProbe
      let (recoverSuccess, recoverOutput) ←
        checkedDecodeLowLevelReturn recoverProbe
      Except.ok
        (SolidCore.Solidity.Source.wordEq sha 0xaaaa &&
          SolidCore.Solidity.Source.wordEq shaSuccess 1 &&
          shaOutput == shaExpected &&
          SolidCore.Solidity.Source.wordEq ripe 0xbbbb &&
          SolidCore.Solidity.Source.wordEq ripeSuccess 1 &&
          ripeOutput == ripeExpected &&
          SolidCore.Solidity.Source.wordEq recovered 0xcafe &&
          SolidCore.Solidity.Source.wordEq recoverSuccess 1 &&
          recoverOutput == recoverExpected)
  | _ => Except.ok false

def checkedIdentityPrecompileStaticcallMatches :
    Except TypeError Bool := do
  let result ←
    ContractDecl.checkedCallFunctionWithContext 16
      Executable.Examples.checkedHashBuiltinContract
      "identityPrecompile"
      SolidCore.Solidity.Source.Context.empty
      SolidCore.Solidity.Source.State.empty []
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _ [probe] => do
      let (success, output) ← checkedDecodeLowLevelReturn probe
      Except.ok
        (SolidCore.Solidity.Source.wordEq success 1 &&
          output == Executable.Examples.identityPrecompilePayload)
  | _ => Except.ok false

def checkedModexpPrecompileStaticcallMatches :
    Except TypeError Bool := do
  let result ←
    ContractDecl.checkedCallFunctionWithContext 16
      Executable.Examples.checkedHashBuiltinContract
      "modexpPrecompile"
      SolidCore.Solidity.Source.Context.empty
      SolidCore.Solidity.Source.State.empty []
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _
      [probe, zeroProbe] => do
      let (success, output) ← checkedDecodeLowLevelReturn probe
      let (zeroSuccess, zeroOutput) ←
        checkedDecodeLowLevelReturn zeroProbe
      Except.ok
        (SolidCore.Solidity.Source.wordEq success 1 &&
          output == [6] &&
          SolidCore.Solidity.Source.wordEq zeroSuccess 1 &&
          zeroOutput == [0])
  | _ => Except.ok false

def checkedTypeMetadataSourceUnitAccepted : Bool :=
  Result.isOk
    (TypecheckedInput.checkedSourceUnit
      Executable.Examples.checkedTypeMetadataSourceUnit)

def checkedTypeInfoLimitsMatch : Except TypeError Bool := do
  let result ←
    SourceUnit.checkedCallContract 16
      Executable.Examples.checkedTypeMetadataSourceUnit
      "CheckedTypeMetadata"
      (SolidCore.Solidity.Source.CallTarget.name "limits")
      SolidCore.Solidity.Source.State.empty []
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _
      [ SolidCore.Solidity.Source.Value.word min256
      , SolidCore.Solidity.Source.Value.word max8
      , SolidCore.Solidity.Source.Value.word max256 ] =>
      Except.ok
        (SolidCore.Solidity.Source.wordEq min256 0 &&
          SolidCore.Solidity.Source.wordEq max8 255 &&
          SolidCore.Solidity.Source.wordEq max256
            (SolidCore.Solidity.Shared.wordModulus - 1))
  | _ => Except.ok false

def checkedSignedTypeInfoLimitsMatch : Except TypeError Bool := do
  let result ←
    SourceUnit.checkedCallContract 16
      Executable.Examples.checkedTypeMetadataSourceUnit
      "CheckedTypeMetadata"
      (SolidCore.Solidity.Source.CallTarget.name "signedLimits")
      SolidCore.Solidity.Source.State.empty []
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _
      [ SolidCore.Solidity.Source.Value.int min256
      , SolidCore.Solidity.Source.Value.int max256 ] =>
      Except.ok
        (SolidCore.Solidity.Source.wordEq min256
            SolidCore.Solidity.Shared.halfWordModulus &&
          SolidCore.Solidity.Source.wordEq max256
            (SolidCore.Solidity.Shared.halfWordModulus - 1))
  | _ => Except.ok false

def checkedContractTypeNameMatches : Except TypeError Bool := do
  let result ←
    SourceUnit.checkedCallContract 16
      Executable.Examples.checkedTypeMetadataSourceUnit
      "CheckedTypeMetadata"
      (SolidCore.Solidity.Source.CallTarget.name "contractName")
      SolidCore.Solidity.Source.State.empty []
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _
      [SolidCore.Solidity.Source.Value.bytes bytes] =>
      Except.ok (bytes == "Vault".toList.map Char.toNat)
  | _ => Except.ok false

def checkedTypeMetadataContractWithCodeContext :
    Except TypeError CheckedContract := do
  let program ←
    SourceUnit.checkedProgram
      Executable.Examples.checkedTypeMetadataSourceUnit
  CheckedProgram.contract program "CheckedTypeMetadata"

def checkedTypeMetadataCodeContext
    (contract : CheckedContract) :
    SolidCore.Solidity.Source.Context :=
  { contract.core.context with
    contractCreationCodes := [("Target", [1, 2, 3, 4])]
    contractRuntimeCodes := [("Target", [5, 6, 7])] }

def checkedContractTypeCodeInfoMatches : Except TypeError Bool := do
  let contract ← checkedTypeMetadataContractWithCodeContext
  let result ←
    CheckedContract.callFunctionWithContext 16 contract "codeInfo"
      (checkedTypeMetadataCodeContext contract)
      SolidCore.Solidity.Source.State.empty []
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _
      [ SolidCore.Solidity.Source.Value.word creationLen
      , SolidCore.Solidity.Source.Value.word runtimeLen
      , SolidCore.Solidity.Source.Value.bytes runtimeBytes ] =>
      Except.ok
        (SolidCore.Solidity.Source.wordEq creationLen 4 &&
          SolidCore.Solidity.Source.wordEq runtimeLen 3 &&
          runtimeBytes == [5, 6, 7])
  | _ => Except.ok false

def checkedContractTypeRuntimeCodeAbiMatches :
    Except TypeError Bool := do
  let contract ← checkedTypeMetadataContractWithCodeContext
  let expected ←
    optionToExcept "runtimeCode ABI expected"
      Executable.Examples.contractTypeRuntimeCodeAbiExpected
  let result ←
    CheckedContract.callFunctionWithContext 16 contract "runtimeCodeAbi"
      (checkedTypeMetadataCodeContext contract)
      SolidCore.Solidity.Source.State.empty []
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _
      [SolidCore.Solidity.Source.Value.bytes bytes] =>
      Except.ok (bytes == expected)
  | _ => Except.ok false

def checkedInterfaceIdMatchesExpected :
    Except TypeError Bool := do
  let result ←
    SourceUnit.checkedCallContract 32
      Executable.Examples.checkedTypeMetadataSourceUnit
      "CheckedTypeMetadata"
      (SolidCore.Solidity.Source.CallTarget.name "tokenInterfaceId")
      SolidCore.Solidity.Source.State.empty []
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _
      [SolidCore.Solidity.Source.Value.word interfaceId] =>
      Except.ok
        (SolidCore.Solidity.Source.wordEq interfaceId
            Executable.Examples.interfaceIdTokenExpected &&
          !SolidCore.Solidity.Source.wordEq interfaceId
            Executable.Examples.interfaceIdTokenIncludingInherited)
  | _ => Except.ok false

def checkedSelectorInfoContractAccepted : Bool :=
  Result.isOk
    (TypecheckedInput.checkedSourceUnit
      Executable.Examples.selectorInfoContract)

def checkedSelectorInfoMatches : Except TypeError Bool :=
  checkedOwnCallWordQuintMatches 32
    Executable.Examples.selectorInfoContract
    "selectors" SolidCore.Solidity.Source.State.empty
    [SolidCore.Solidity.Source.Value.word 0xbeef]
    (SolidCore.Solidity.Source.ABI.selectorFromSignature
      "set(uint256)")
    (SolidCore.Solidity.Source.ABI.selectorFromSignature
      "Bad(uint256)")
    (SolidCore.Solidity.Source.ABI.selectorFromSignature
      "stored()")
    0 0xbeef

def checkedOverloadedSelectorRejected : Bool :=
  Result.isError
    (TypecheckedInput.checkedSourceUnit
      Executable.Examples.overloadedSelectorRejectedContract)

def checkedAddressEnvironmentContractAccepted : Bool :=
  Result.isOk
    (TypecheckedInput.checkedSourceUnit
      Executable.Examples.checkedAddressEnvironmentContract)

def checkedAddressMembersMatch : Except TypeError Bool := do
  let contract ←
    ContractDecl.checkedContract
      Executable.Examples.checkedAddressEnvironmentContract
  let result ←
    CheckedContract.callFunctionWithContext 16 contract "accountInfo"
      { contract.core.context with
        self := 0xcafe
        accountBalances := [(0xcafe, 1000), (0xbeef, 77)]
        accountCodehashes := [(0xbeef, 0x123456)] }
      SolidCore.Solidity.Source.State.empty []
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _
      [ SolidCore.Solidity.Source.Value.word selfAddress
      , SolidCore.Solidity.Source.Value.word selfBalance
      , SolidCore.Solidity.Source.Value.word otherBalance
      , SolidCore.Solidity.Source.Value.word otherCodehash ] =>
      Except.ok
        (SolidCore.Solidity.Source.wordEq selfAddress 0xcafe &&
          SolidCore.Solidity.Source.wordEq selfBalance 1000 &&
          SolidCore.Solidity.Source.wordEq otherBalance 77 &&
          SolidCore.Solidity.Source.wordEq otherCodehash 0x123456)
  | _ => Except.ok false

def checkedAddressMembersPreConstantinopleCodehashMatches :
    Except TypeError Bool := do
  let contract ←
    ContractDecl.checkedContract
      Executable.Examples.checkedAddressEnvironmentContract
  let result ←
    CheckedContract.callFunctionWithContext 16 contract "accountInfo"
      { contract.core.context with
        evmVersion := SolidCore.Solidity.Source.EvmVersion.byzantium
        self := 0xcafe
        accountBalances := [(0xcafe, 1000), (0xbeef, 77)]
        accountCodehashes := [(0xbeef, 0x123456)] }
      SolidCore.Solidity.Source.State.empty []
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _
      [ SolidCore.Solidity.Source.Value.word selfAddress
      , SolidCore.Solidity.Source.Value.word selfBalance
      , SolidCore.Solidity.Source.Value.word otherBalance
      , SolidCore.Solidity.Source.Value.word otherCodehash ] =>
      Except.ok
        (SolidCore.Solidity.Source.wordEq selfAddress 0xcafe &&
          SolidCore.Solidity.Source.wordEq selfBalance 1000 &&
          SolidCore.Solidity.Source.wordEq otherBalance 77 &&
          SolidCore.Solidity.Source.wordEq otherCodehash 0)
  | _ => Except.ok false

def checkedAddressCodeMemberMatch : Except TypeError Bool := do
  let contract ←
    ContractDecl.checkedContract
      Executable.Examples.checkedAddressEnvironmentContract
  let result ←
    CheckedContract.callFunctionWithContext 16 contract "codeInfo"
      { contract.core.context with
        accountCodes := [(0xbeef, [1, 2, 3, 4])] }
      SolidCore.Solidity.Source.State.empty []
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _
      [ SolidCore.Solidity.Source.Value.bytes code
      , SolidCore.Solidity.Source.Value.word codeLength
      , SolidCore.Solidity.Source.Value.word missingLength ] =>
      Except.ok
        (code == [1, 2, 3, 4] &&
          SolidCore.Solidity.Source.wordEq codeLength 4 &&
          SolidCore.Solidity.Source.wordEq missingLength 0)
  | _ => Except.ok false

def checkedSelfdestructPreCancunDeletesMatches :
    Except TypeError Bool := do
  let contract ←
    ContractDecl.checkedContract
      Executable.Examples.checkedAddressEnvironmentContract
  let result ←
    CheckedContract.callFunctionWithContext 16 contract "destroy"
      { contract.core.context with
        self := 0xcafe
        evmVersion := SolidCore.Solidity.Source.EvmVersion.shanghai }
      SolidCore.Solidity.Source.State.empty
      [SolidCore.Solidity.Source.Value.word 0xbeef]
  match result with
  | SolidCore.Solidity.Source.CallResult.returned state [] =>
      match state.selfdestructEffects with
      | [record] =>
          Except.ok
            (SolidCore.Solidity.Source.wordEq record.fromAddress 0xcafe &&
              SolidCore.Solidity.Source.wordEq record.recipient 0xbeef &&
              record.deletesAccount == true)
      | _ => Except.ok false
  | _ => Except.ok false

def checkedSelfdestructCancunCreatedAccountDeletesMatches :
    Except TypeError Bool := do
  let contract ←
    ContractDecl.checkedContract
      Executable.Examples.checkedAddressEnvironmentContract
  let result ←
    CheckedContract.callFunctionWithContext 16 contract "destroy"
      { contract.core.context with
        self := 0xcafe
        createdInTransactionAccounts := [0xcafe] }
      SolidCore.Solidity.Source.State.empty
      [SolidCore.Solidity.Source.Value.word 0xbeef]
  match result with
  | SolidCore.Solidity.Source.CallResult.returned state [] =>
      match state.selfdestructEffects with
      | [record] =>
          Except.ok
            (SolidCore.Solidity.Source.wordEq record.fromAddress 0xcafe &&
              SolidCore.Solidity.Source.wordEq record.recipient 0xbeef &&
              record.deletesAccount == true)
      | _ => Except.ok false
  | _ => Except.ok false

def checkedMetadataInvalidSourcesRejected : Bool :=
  Result.isError
      (TypecheckedInput.checkedSourceUnit
        typeCreationCodeSelfSource) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit
        typeRuntimeCodeDerivedSource) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit
        pureAddressEnvMembersSource) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit
        selfdestructNonpayableAddressSource) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit
        selfdestructViewSource)

def checkedConcatBuiltinsContractAccepted : Bool :=
  Result.isOk
    (TypecheckedInput.checkedSourceUnit
      Executable.Examples.checkedConcatBuiltinsContract)

def checkedConcatBuiltinsMatch : Except TypeError Bool := do
  let result ←
    CheckedInput.ownCall 16
      Executable.Examples.checkedConcatBuiltinsContract
      (SolidCore.Solidity.Source.CallTarget.name "join")
      SolidCore.Solidity.Source.State.empty
      [ SolidCore.Solidity.Source.Value.bytes [1, 2]
      , SolidCore.Solidity.Source.Value.bytes
          ("!".toList.map Char.toNat) ]
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _
      [ SolidCore.Solidity.Source.Value.bytes joinedBytes
      , SolidCore.Solidity.Source.Value.bytes joinedString ] =>
      Except.ok
        (joinedBytes == [1, 2, 3, 4] &&
          joinedString == [104, 105, 33])
  | _ => Except.ok false

def checkedBytesConcatFixedMatchesExpected :
    Except TypeError Bool :=
  checkedOwnCallBytesMatches 16
    Executable.Examples.checkedConcatBuiltinsContract
    "joinFixed" SolidCore.Solidity.Source.State.empty
    [SolidCore.Solidity.Source.Value.bytes [1, 2]]
    [0xaa, 0xbb, 0xcc, 72, 105, 1, 2]

def checkedStringConcatUnicodeMatchesExpected :
    Except TypeError Bool :=
  checkedOwnCallBytesMatches 16
    Executable.Examples.checkedConcatBuiltinsContract
    "joinString" SolidCore.Solidity.Source.State.empty
    [SolidCore.Solidity.Source.Value.bytes
      ("!".toList.map Char.toNat)]
    [97, 0xc3, 0xa9, 33]

def checkedConcatInvalidSourcesRejected : Bool :=
  Result.isError
      (TypecheckedInput.checkedSourceUnit
        Executable.Examples.checkedBytesConcatInvalidSourceUnit) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit
        Executable.Examples.checkedStringConcatInvalidSourceUnit)

def checkedAmbientBuiltinDisciplineAccepted : Bool :=
  Result.isOk (TypecheckedInput.checkedSourceUnit pureMsgSigSource) &&
    Result.isOk (TypecheckedInput.checkedSourceUnit viewBlockTimestampSource) &&
    Result.isOk (TypecheckedInput.checkedSourceUnit viewAmbientBuiltinsSource) &&
    Result.isOk (TypecheckedInput.checkedSourceUnit viewAddressEnvMembersSource) &&
    evmVersionBuiltinDisciplineAccepted

def checkedAmbientBuiltinDisciplineRejected : Bool :=
  Result.isError (TypecheckedInput.checkedSourceUnit pureMsgValueSource) &&
    Result.isError (TypecheckedInput.checkedSourceUnit pureBlockTimestampSource) &&
    Result.isError (TypecheckedInput.checkedSourceUnit pureGasleftSource) &&
    Result.isError (TypecheckedInput.checkedSourceUnit pureBlockhashSource) &&
    Result.isError (TypecheckedInput.checkedSourceUnit badBlockhashArgSource) &&
    Result.isError (TypecheckedInput.checkedSourceUnit signedBlockhashArgSource) &&
    Result.isError (TypecheckedInput.checkedSourceUnit signedBlobhashArgSource) &&
    Result.isError (TypecheckedInput.checkedSourceUnit pureAddressEnvMembersSource) &&
    evmVersionBuiltinDisciplineRejected

def checkedLiteralConversionContractAccepted : Bool :=
  Result.isOk
    (TypecheckedInput.checkedSourceUnit
      Executable.Examples.checkedLiteralConversionContract)

def checkedBytesSliceMatches : Except TypeError Bool := do
  let result ←
    CheckedInput.ownCall 16
      Executable.Examples.checkedLiteralConversionContract
      (SolidCore.Solidity.Source.CallTarget.name "sliceBytes")
      SolidCore.Solidity.Source.State.empty
      [SolidCore.Solidity.Source.Value.bytes [10, 20, 30, 40, 50]]
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _
      [ SolidCore.Solidity.Source.Value.bytes middle
      , SolidCore.Solidity.Source.Value.bytes tail
      , SolidCore.Solidity.Source.Value.bytes head
      , SolidCore.Solidity.Source.Value.word relative ] =>
      Except.ok
        (middle == [20, 30, 40] &&
          tail == [40, 50] &&
          head == [10, 20] &&
          SolidCore.Solidity.Source.wordEq relative 20)
  | _ => Except.ok false

def checkedStringLiteralMatchesExpected : Except TypeError Bool :=
  checkedOwnCallBytesMatches 16
    Executable.Examples.checkedLiteralConversionContract
    "hello" SolidCore.Solidity.Source.State.empty [] [104, 105]

def checkedNumericLiteralMatchesExpected : Except TypeError Bool :=
  checkedOwnCallWordQuadMatches 16
    Executable.Examples.checkedLiteralConversionContract
    "numbers" SolidCore.Solidity.Source.State.empty []
    255 123000 12031 42

def checkedScaledNumericLiteralMatchesExpected :
    Except TypeError Bool :=
  checkedOwnCallWordQuadMatches 16
    Executable.Examples.checkedLiteralConversionContract
    "scaledNumbers" SolidCore.Solidity.Source.State.empty []
    20000000000 25 5 12

def checkedNumberLiteralExpressionMatchesExpected :
    Except TypeError Bool := do
  let result ←
    CheckedInput.ownCall 16
      Executable.Examples.checkedLiteralConversionContract
      (SolidCore.Solidity.Source.CallTarget.name "literalExpressions")
      SolidCore.Solidity.Source.State.empty []
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _
      [ SolidCore.Solidity.Source.Value.word halfTimesEight
      , SolidCore.Solidity.Source.Value.word dividedThenAdded
      , SolidCore.Solidity.Source.Value.word fractionalPowerScaled
      , SolidCore.Solidity.Source.Value.word halfLessThanOne
      , SolidCore.Solidity.Source.Value.word ratioEquality ] =>
      Except.ok
        (SolidCore.Solidity.Source.wordEq halfTimesEight 4 &&
          SolidCore.Solidity.Source.wordEq dividedThenAdded 3 &&
          SolidCore.Solidity.Source.wordEq fractionalPowerScaled 4 &&
          SolidCore.Solidity.Source.wordEq halfLessThanOne 1 &&
          SolidCore.Solidity.Source.wordEq ratioEquality 1)
  | _ => Except.ok false

def checkedUnitNumberLiteralMatchesExpected :
    Except TypeError Bool := do
  let result ←
    CheckedInput.ownCall 16
      Executable.Examples.checkedLiteralConversionContract
      (SolidCore.Solidity.Source.CallTarget.name "unitNumbers")
      SolidCore.Solidity.Source.State.empty []
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _
      [ SolidCore.Solidity.Source.Value.word oneWei
      , SolidCore.Solidity.Source.Value.word oneGwei
      , SolidCore.Solidity.Source.Value.word oneEther
      , SolidCore.Solidity.Source.Value.word twoPointFiveEther
      , SolidCore.Solidity.Source.Value.word twoMinutes
      , SolidCore.Solidity.Source.Value.word oneWeek
      , SolidCore.Solidity.Source.Value.word timeEquality
      , SolidCore.Solidity.Source.Value.word typedDays
      , SolidCore.Solidity.Source.Value.word payableZero ] =>
      Except.ok
        (SolidCore.Solidity.Source.wordEq oneWei 1 &&
          SolidCore.Solidity.Source.wordEq oneGwei 1000000000 &&
          SolidCore.Solidity.Source.wordEq oneEther 1000000000000000000 &&
          SolidCore.Solidity.Source.wordEq twoPointFiveEther
            2500000000000000000 &&
          SolidCore.Solidity.Source.wordEq twoMinutes 120 &&
          SolidCore.Solidity.Source.wordEq oneWeek 604800 &&
          SolidCore.Solidity.Source.wordEq timeEquality 1 &&
          SolidCore.Solidity.Source.wordEq typedDays 86400 &&
          SolidCore.Solidity.Source.wordEq payableZero 0)
  | _ => Except.ok false

def checkedTypedNumericLiteralConversionMatchesExpected :
    Except TypeError Bool := do
  let result ←
    CheckedInput.ownCall 16
      Executable.Examples.checkedLiteralConversionContract
      (SolidCore.Solidity.Source.CallTarget.name "typedLiteralConversions")
      SolidCore.Solidity.Source.State.empty []
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _
      [ SolidCore.Solidity.Source.Value.int negativeSmall
      , SolidCore.Solidity.Source.Value.int negativeMin
      , SolidCore.Solidity.Source.Value.word positiveMax
      , SolidCore.Solidity.Source.Value.int foldedInt ] =>
      Except.ok
        (SolidCore.Solidity.Shared.signedValue negativeSmall = -5 &&
          SolidCore.Solidity.Shared.signedValue negativeMin = -128 &&
          SolidCore.Solidity.Source.wordEq positiveMax 255 &&
          SolidCore.Solidity.Shared.signedValue foldedInt = 4)
  | _ => Except.ok false

def checkedTypedNumericLiteralVarDeclMatchesExpected :
    Except TypeError Bool := do
  let result ←
    CheckedInput.ownCall 16
      Executable.Examples.checkedLiteralConversionContract
      (SolidCore.Solidity.Source.CallTarget.name "typedLiteralVars")
      SolidCore.Solidity.Source.State.empty []
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _
      [ SolidCore.Solidity.Source.Value.int negative
      , SolidCore.Solidity.Source.Value.word folded ] =>
      Except.ok
        (SolidCore.Solidity.Shared.signedValue negative = -5 &&
          SolidCore.Solidity.Source.wordEq folded 4)
  | _ => Except.ok false

def checkedRuntimeIntegerCastsMatch : Except TypeError Bool := do
  let result ←
    CheckedInput.ownCall 16
      Executable.Examples.checkedLiteralConversionContract
      (SolidCore.Solidity.Source.CallTarget.name "runtimeIntegerCasts")
      SolidCore.Solidity.Source.State.empty
      [ SolidCore.Solidity.Source.Value.word 0x123456ff
      , SolidCore.Solidity.Source.Value.int
          (SolidCore.Solidity.Shared.signedToWord (-3)) ]
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _
      [ SolidCore.Solidity.Source.Value.word low8
      , SolidCore.Solidity.Source.Value.word low16
      , SolidCore.Solidity.Source.Value.int signedLow
      , SolidCore.Solidity.Source.Value.word signedAsUint
      , SolidCore.Solidity.Source.Value.word fromBytes
      , SolidCore.Solidity.Source.Value.word fromAddress
      , SolidCore.Solidity.Source.Value.word roundTripAddress ] =>
      Except.ok
        (SolidCore.Solidity.Source.wordEq low8 0xff &&
          SolidCore.Solidity.Source.wordEq low16 0x56ff &&
          SolidCore.Solidity.Shared.signedValue signedLow = -1 &&
          SolidCore.Solidity.Source.wordEq signedAsUint
            (SolidCore.Solidity.Shared.signedToWord (-3)) &&
          SolidCore.Solidity.Source.wordEq fromBytes 0xabcd &&
          SolidCore.Solidity.Source.wordEq fromAddress 0xbeef &&
          SolidCore.Solidity.Source.wordEq roundTripAddress 0x123456ff)
  | _ => Except.ok false

def checkedFixedBytesLiteralConversionMatchesExpected :
    Except TypeError Bool := do
  let result ←
    CheckedInput.ownCall 16
      Executable.Examples.checkedLiteralConversionContract
      (SolidCore.Solidity.Source.CallTarget.name "fixedByteLiterals")
      SolidCore.Solidity.Source.State.empty []
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _
      [ SolidCore.Solidity.Source.Value.word fromHexString
      , SolidCore.Solidity.Source.Value.word fromString
      , SolidCore.Solidity.Source.Value.word fromHexNumber
      , SolidCore.Solidity.Source.Value.word fromZero
      , SolidCore.Solidity.Source.Value.word fromVarDecl ] =>
      Except.ok
        (Executable.Examples.fixedBytesWordBytes 2 fromHexString ==
            [0x12, 0] &&
          Executable.Examples.fixedBytesWordBytes 2 fromString ==
            [Char.toNat 'x', 0] &&
          Executable.Examples.fixedBytesWordBytes 2 fromHexNumber ==
            [0x12, 0x34] &&
          Executable.Examples.fixedBytesWordBytes 4 fromZero ==
            [0, 0, 0, 0] &&
          Executable.Examples.fixedBytesWordBytes 3 fromVarDecl ==
            [0xab, 0, 0])
  | _ => Except.ok false

def checkedFixedBytesMembersMatch : Except TypeError Bool :=
  checkedOwnCallWordTripleMatches 16
    Executable.Examples.checkedLiteralConversionContract
    "fixedBytesMembers" SolidCore.Solidity.Source.State.empty []
    2 0xaa 0xbb

def checkedFixedBytesIndexOutOfBoundsPanics :
    Except TypeError Bool :=
  checkedOwnCallPanicMatches 16
    Executable.Examples.checkedLiteralConversionContract
    "fixedBytesIndexOutOfBounds"
    SolidCore.Solidity.Source.State.empty [] 0x32

def checkedFixedBytesRuntimeConversionsMatch :
    Except TypeError Bool := do
  let result ←
    CheckedInput.ownCall 16
      Executable.Examples.checkedLiteralConversionContract
      (SolidCore.Solidity.Source.CallTarget.name
        "fixedBytesRuntimeConversions")
      SolidCore.Solidity.Source.State.empty
      [ SolidCore.Solidity.Source.Value.bytes [1, 2, 3, 4, 5]
      , SolidCore.Solidity.Source.Value.bytes [9, 8] ]
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _
      [ SolidCore.Solidity.Source.Value.word wide
      , SolidCore.Solidity.Source.Value.word narrow
      , SolidCore.Solidity.Source.Value.word fromUint
      , SolidCore.Solidity.Source.Value.word fromAddress
      , SolidCore.Solidity.Source.Value.word fromLongData
      , SolidCore.Solidity.Source.Value.word fromShortData ] =>
      Except.ok
        (Executable.Examples.fixedBytesWordBytes 4 wide ==
            [0x12, 0x34, 0, 0] &&
          Executable.Examples.fixedBytesWordBytes 1 narrow == [0x12] &&
          Executable.Examples.fixedBytesWordBytes 2 fromUint ==
            [0xab, 0xcd] &&
          Executable.Examples.fixedBytesWordBytes 20 fromAddress ==
            (List.replicate 18 0 ++ [0xbe, 0xef]) &&
          Executable.Examples.fixedBytesWordBytes 4 fromLongData ==
            [1, 2, 3, 4] &&
          Executable.Examples.fixedBytesWordBytes 4 fromShortData ==
            [9, 8, 0, 0])
  | _ => Except.ok false

def checkedUnicodeStringLiteralMatchesUtf8 :
    Except TypeError Bool := do
  let result ←
    CheckedInput.ownCall 16
      Executable.Examples.checkedLiteralConversionContract
      (SolidCore.Solidity.Source.CallTarget.name "unicodeLiteral")
      SolidCore.Solidity.Source.State.empty []
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _
      [ SolidCore.Solidity.Source.Value.bytes text
      , SolidCore.Solidity.Source.Value.word fixed ] =>
      Except.ok
        (text == [0xc3, 0xa9] &&
          Executable.Examples.fixedBytesWordBytes 3 fixed ==
            [0xc3, 0xa9, 0])
  | _ => Except.ok false

def checkedAddressLiteralConversionMatchesExpected :
    Except TypeError Bool := do
  let result ←
    CheckedInput.ownCall 16
      Executable.Examples.checkedLiteralConversionContract
      (SolidCore.Solidity.Source.CallTarget.name
        "addressLiteralConversions")
      SolidCore.Solidity.Source.State.empty []
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _
      [ SolidCore.Solidity.Source.Value.word zeroValue
      , SolidCore.Solidity.Source.Value.word fromInteger
      , SolidCore.Solidity.Source.Value.word fromUint160
      , SolidCore.Solidity.Source.Value.word fromBytes20
      , SolidCore.Solidity.Source.Value.word payableZero
      , SolidCore.Solidity.Source.Value.word fromVarDecl ] =>
      Except.ok
        (SolidCore.Solidity.Source.wordEq zeroValue 0 &&
          SolidCore.Solidity.Source.wordEq fromInteger 0xbeef &&
          SolidCore.Solidity.Source.wordEq fromUint160 0xcafe &&
          SolidCore.Solidity.Source.wordEq fromBytes20
            0x111122223333444455556666777788889999aaaa &&
          SolidCore.Solidity.Source.wordEq payableZero 0 &&
          SolidCore.Solidity.Source.wordEq fromVarDecl 0xbeef)
  | _ => Except.ok false

def checkedHexStringLiteralMatchesExpected :
    Except TypeError Bool :=
  checkedOwnCallBytesMatches 16
    Executable.Examples.checkedLiteralConversionContract
    "hexData" SolidCore.Solidity.Source.State.empty []
    [0, 17, 34, 255]

def checkedHexStringAbiEncodeMatchesExpected :
    Except TypeError Bool := do
  let expected ←
    optionToExcept "hex string ABI encoding"
      Executable.Examples.hexStringAbiEncodeExpected
  checkedOwnCallBytesMatches 16
    Executable.Examples.checkedLiteralConversionContract
    "encodeHexData" SolidCore.Solidity.Source.State.empty [] expected

def checkedInvalidReturnFunction (functionName : Name)
    (returnTy : Ty) (expr : Solidity.Expr) : FunctionDecl :=
  { name := some functionName
    visibility := some Visibility.public_
    mutability := StateMutability.pure
    returns := [{ name := some "out", ty := returnTy }]
    body := some (Stmt.returnValues (some expr)) }

def checkedInvalidReturnContract (contractName : Name)
    (returnTy : Ty) (expr : Solidity.Expr) : ContractDecl :=
  { name := contractName
    items :=
      [ContractItem.function
        (checkedInvalidReturnFunction "bad" returnTy expr)] }

def checkedInvalidUintReturnFunction (functionName : Name)
    (expr : Solidity.Expr) : FunctionDecl :=
  checkedInvalidReturnFunction functionName (Ty.uint 256) expr

def checkedInvalidUintReturnContract (contractName : Name)
    (expr : Solidity.Expr) : ContractDecl :=
  checkedInvalidReturnContract contractName (Ty.uint 256) expr

def checkedMalformedNumericLiteralsRejected : Bool :=
  Result.isError
      (TypecheckedInput.checkedSourceUnit
        (checkedInvalidUintReturnContract "BadHexUnderscore"
          (Expr.literal (Literal.number "0x_ff")))) &&
    Result.isError
      (CheckedInput.program
        (checkedInvalidUintReturnContract "BadHexUnderscoreChecked"
          (Expr.literal (Literal.number "0x_ff")))) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit
        (checkedInvalidUintReturnContract "BadRepeatedSeparator"
          (Expr.literal (Literal.number "12__3")))) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit
        (checkedInvalidUintReturnContract "BadLeadingZero"
          (Expr.literal (Literal.number "012"))))

def checkedNonIntegralNumericLiteralsRejected : Bool :=
  Result.isError
      (TypecheckedInput.checkedSourceUnit
        (checkedInvalidUintReturnContract "BadFractionalReturn"
          (Expr.literal (Literal.number "2.5")))) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit
        (checkedInvalidUintReturnContract "BadLeadingDotReturn"
          (Expr.literal (Literal.number ".5")))) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit
        (checkedInvalidUintReturnContract "BadNegativeExponentReturn"
          (Expr.literal (Literal.number "1e-1"))))

def checkedNonIntegralNumberLiteralExpressionRejected : Bool :=
  Result.isError
    (TypecheckedInput.checkedSourceUnit
      (checkedInvalidUintReturnContract "BadFoldedFractionalReturn"
        (Expr.binary BinaryOp.mul
          (Expr.literal (Literal.number ".5"))
          (Expr.literal (Literal.number "7")))))

def checkedNumericLiteralCastBoundsRejected : Bool :=
  Result.isError
      (TypecheckedInput.checkedSourceUnit
        (checkedInvalidUintReturnContract "BadUint8LiteralCast"
          (Expr.call (Expr.typeName (Ty.uint 8))
            [Arg.positional
              (Expr.literal (Literal.number "256"))]))) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit
        (checkedInvalidUintReturnContract "BadInt8PositiveLiteralCast"
          (Expr.call (Expr.typeName (Ty.int 8))
            [Arg.positional
              (Expr.literal (Literal.number "128"))]))) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit
        (checkedInvalidUintReturnContract "BadInt8NegativeLiteralCast"
          (Expr.call (Expr.typeName (Ty.int 8))
            [Arg.positional
              (Expr.unary UnaryOp.neg
                (Expr.literal (Literal.number "129")))]))) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit
        (checkedInvalidUintReturnContract "BadUint8NegativeLiteralCast"
          (Expr.call (Expr.typeName (Ty.uint 8))
            [Arg.positional
              (Expr.unary UnaryOp.neg
                (Expr.literal (Literal.number "1")))])))

def checkedUnitNumberLiteralRejected : Bool :=
  Result.isError
      (TypecheckedInput.checkedSourceUnit
        (checkedInvalidUintReturnContract "BadHalfWei"
          (Expr.literal
            (Literal.unitNumber ".5" UnitDenomination.wei)))) &&
    Result.isError
      (CheckedInput.program
        (checkedInvalidUintReturnContract "BadSubWeiEther"
          (Expr.literal
            (Literal.unitNumber "1e-19" UnitDenomination.ether)))) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit
        (checkedInvalidReturnContract "BadUint8Ether"
          (Ty.uint 8)
          (Expr.call (Expr.typeName (Ty.uint 8))
            [Arg.positional
              (Expr.literal
                (Literal.unitNumber "1" UnitDenomination.ether))]))) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit
        (checkedInvalidReturnContract "BadPayableWei"
          (Ty.address true)
          (Expr.payableConversion
            (Expr.literal
              (Literal.unitNumber "1" UnitDenomination.wei))))) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit
        (checkedInvalidReturnContract "BadBytes4Wei"
          (Ty.bytesN 4)
          (Expr.call (Expr.typeName (Ty.bytesN 4))
            [Arg.positional
              (Expr.literal
                (Literal.unitNumber "1" UnitDenomination.wei))])))

def checkedFixedBytesLiteralConversionRejected : Bool :=
  Result.isError
      (CheckedInput.program
        (checkedInvalidReturnContract "BadHexStringToBytes2"
          (Ty.bytesN 2)
          (Expr.call (Expr.typeName (Ty.bytesN 2))
            [Arg.positional
              (Expr.literal (Literal.hexString "aabbcc"))]))) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit
        (checkedInvalidReturnContract "BadStringToBytes2"
          (Ty.bytesN 2)
          (Expr.call (Expr.typeName (Ty.bytesN 2))
            [Arg.positional
              (Expr.literal (Literal.string "xyz"))]))) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit
        (checkedInvalidReturnContract "BadNumberToBytes2"
          (Ty.bytesN 2)
          (Expr.call (Expr.typeName (Ty.bytesN 2))
            [Arg.positional
              (Expr.literal (Literal.number "0x123"))])))

def checkedRuntimeIntegerCastRejected : Bool :=
  Result.isError
      (TypecheckedInput.checkedSourceUnit
        (checkedInvalidReturnContract "BadBytes2ToUint8"
          (Ty.uint 8)
          (Expr.call (Expr.typeName (Ty.uint 8))
            [Arg.positional
              (Expr.call (Expr.typeName (Ty.bytesN 2))
                [Arg.positional
                  (Expr.literal (Literal.number "0xabcd"))])]))) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit
        (checkedInvalidReturnContract "BadAddressToInt160"
          (Ty.int 160)
          (Expr.call (Expr.typeName (Ty.int 160))
            [Arg.positional
              (Expr.literal (Literal.address 0xbeef))]))) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit
        (checkedInvalidReturnContract "BadAddressToUint256"
          (Ty.uint 256)
          (Expr.call (Expr.typeName (Ty.uint 256))
            [Arg.positional
              (Expr.literal (Literal.address 0xbeef))])))

def checkedFixedBytesRuntimeConversionRejected : Bool :=
  Result.isError
      (TypecheckedInput.checkedSourceUnit
        (checkedInvalidReturnContract "BadUint32ToBytes2"
          (Ty.bytesN 2)
          (Expr.call (Expr.typeName (Ty.bytesN 2))
            [Arg.positional
              (Expr.call (Expr.typeName (Ty.uint 32))
                [Arg.positional
                  (Expr.literal (Literal.number "1"))])]))) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit
        (checkedInvalidReturnContract "BadAddressToBytes2"
          (Ty.bytesN 2)
          (Expr.call (Expr.typeName (Ty.bytesN 2))
            [Arg.positional
              (Expr.literal (Literal.address 0xbeef))])))

def checkedAddressConversionRejected : Bool :=
  Result.isError
      (TypecheckedInput.checkedSourceUnit
        (checkedInvalidReturnContract "BadWideLiteralAddress"
          (Ty.address false)
          (Expr.call (Expr.typeName (Ty.address false))
            [Arg.positional
              (Expr.literal
                (Literal.number
                  "0x10000000000000000000000000000000000000000"))]))) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit
        (checkedInvalidReturnContract "BadUint256ToAddress"
          (Ty.address false)
          (Expr.call (Expr.typeName (Ty.address false))
            [Arg.positional
              (Expr.call (Expr.typeName (Ty.uint 256))
                [Arg.positional
                  (Expr.literal (Literal.number "1"))])]))) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit
        (checkedInvalidReturnContract "BadBytes32ToAddress"
          (Ty.address false)
          (Expr.call (Expr.typeName (Ty.address false))
            [Arg.positional
              (Expr.call (Expr.typeName (Ty.bytesN 32))
                [Arg.positional
                  (Expr.literal
                    (Literal.number
                      "0x111122223333444455556666777788889999aaaabbbbccccddddeeeeffff0000"))])]))) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit
        (checkedInvalidReturnContract "BadStringToAddress"
          (Ty.address false)
          (Expr.call (Expr.typeName (Ty.address false))
            [Arg.positional
              (Expr.literal (Literal.string "x"))]))) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit
        (checkedInvalidReturnContract "BadPayableFromOne"
          (Ty.address true)
          (Expr.payableConversion
            (Expr.literal (Literal.number "1"))))) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit
        (checkedInvalidReturnContract "BadPayableFromUint160One"
          (Ty.address true)
          (Expr.payableConversion
            (Expr.call (Expr.typeName (Ty.uint 160))
              [Arg.positional
                (Expr.literal (Literal.number "1"))]))))

def checkedPayableTypedUint160ZeroRejected : Bool :=
  Result.isError
    (TypecheckedInput.checkedSourceUnit
      (checkedInvalidReturnContract "BadPayableFromUint160Zero"
        (Ty.address true)
        (Expr.payableConversion
          (Expr.call (Expr.typeName (Ty.uint 160))
            [Arg.positional
              (Expr.literal (Literal.number "0"))]))))

def checkedPayableContractConversionMatches : Except TypeError Bool :=
  checkedCallWordMatches 16 payableContractConversionSource
    "PayableContractConversion" "asPayable"
    SolidCore.Solidity.Source.State.empty [] 0

def checkedNonpayableContractConversionRejected : Bool :=
  Result.isError
    (TypecheckedInput.checkedSourceUnit nonpayableContractConversionSource)

def checkedLiteralInvalidSourcesRejected : Bool :=
  Result.isError
      (TypecheckedInput.checkedSourceUnit memoryBytesSliceSource) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit stringIndexSource) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit stringLengthMemberSource) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit calldataSliceSignedIndexSource) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit calldataSliceMemberSource) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit fractionalWeiReturnSource) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit subWeiEtherReturnSource) &&
    checkedMalformedNumericLiteralsRejected &&
    checkedNonIntegralNumericLiteralsRejected &&
    checkedNonIntegralNumberLiteralExpressionRejected &&
    checkedNumericLiteralCastBoundsRejected &&
    checkedUnitNumberLiteralRejected &&
    checkedFixedBytesLiteralConversionRejected &&
    checkedRuntimeIntegerCastRejected &&
    checkedFixedBytesRuntimeConversionRejected &&
    checkedAddressConversionRejected &&
    checkedPayableTypedUint160ZeroRejected &&
    checkedNonpayableContractConversionRejected

def checkedLiteralConversionSemanticsMatch :
    Except TypeError Bool := do
  let bytesSlice ← checkedBytesSliceMatches
  let stringLiteral ← checkedStringLiteralMatchesExpected
  let numericLiteral ← checkedNumericLiteralMatchesExpected
  let scaledNumeric ← checkedScaledNumericLiteralMatchesExpected
  let numericExpression ← checkedNumberLiteralExpressionMatchesExpected
  let unitNumber ← checkedUnitNumberLiteralMatchesExpected
  let typedNumeric ← checkedTypedNumericLiteralConversionMatchesExpected
  let typedNumericVar ← checkedTypedNumericLiteralVarDeclMatchesExpected
  let runtimeCasts ← checkedRuntimeIntegerCastsMatch
  let fixedBytesLiteral ← checkedFixedBytesLiteralConversionMatchesExpected
  let fixedBytesMembers ← checkedFixedBytesMembersMatch
  let fixedBytesOob ← checkedFixedBytesIndexOutOfBoundsPanics
  let fixedBytesRuntime ← checkedFixedBytesRuntimeConversionsMatch
  let unicodeLiteral ← checkedUnicodeStringLiteralMatchesUtf8
  let addressLiteral ← checkedAddressLiteralConversionMatchesExpected
  let payableContract ← checkedPayableContractConversionMatches
  let hexString ← checkedHexStringLiteralMatchesExpected
  let hexStringAbi ← checkedHexStringAbiEncodeMatchesExpected
  Except.ok
    (checkedLiteralConversionContractAccepted &&
      checkedLiteralInvalidSourcesRejected &&
      bytesSlice && stringLiteral && numericLiteral && scaledNumeric &&
      numericExpression && unitNumber && typedNumeric && typedNumericVar &&
      runtimeCasts && fixedBytesLiteral && fixedBytesMembers &&
      fixedBytesOob && fixedBytesRuntime && unicodeLiteral &&
      addressLiteral && payableContract && hexString && hexStringAbi)

def checkedArithmeticContractAccepted : Bool :=
  Result.isOk
    (TypecheckedInput.checkedSourceUnit
      Executable.Examples.checkedArithmeticContract)

def checkedBinaryArithmeticAccepted :
    Except TypeError Bool :=
  Except.ok checkedArithmeticContractAccepted

def checkedOwnCallIntMatches (fuel : Nat)
    (decl : SourceContractDecl) (functionName : Name)
    (state : CoreState) (args : List CoreValue)
    (expected : Word) : Except TypeError Bool := do
  let result ←
    CheckedInput.ownCall fuel decl
      (SolidCore.Solidity.Source.CallTarget.name functionName)
      state args
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _
      [SolidCore.Solidity.Source.Value.int value] =>
      Except.ok (SolidCore.Solidity.Source.wordEq value expected)
  | _ => Except.ok false

def checkedSignedIntArithmeticMatches : Except TypeError Bool := do
  let result ←
    CheckedInput.ownCall 16
      Executable.Examples.checkedArithmeticContract
      (SolidCore.Solidity.Source.CallTarget.name "signedOps")
      SolidCore.Solidity.Source.State.empty
      [ SolidCore.Solidity.Source.Value.int
          (SolidCore.Solidity.Shared.signedToWord (-5))
      , SolidCore.Solidity.Source.Value.int 2 ]
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _
      [ SolidCore.Solidity.Source.Value.int quotient
      , SolidCore.Solidity.Source.Value.int remainder
      , SolidCore.Solidity.Source.Value.word less ] =>
      Except.ok
        (SolidCore.Solidity.Source.wordEq quotient
            (SolidCore.Solidity.Shared.signedToWord (-2)) &&
          SolidCore.Solidity.Source.wordEq remainder
            (SolidCore.Solidity.Shared.signedToWord (-1)) &&
          SolidCore.Solidity.Source.wordEq less 1)
  | _ => Except.ok false

def checkedSignedIntAbiOutputMatchesExpected : Except TypeError Bool :=
  checkedContractAbiOutputMatches 24
    Executable.Examples.checkedArithmeticContract
    "signedOps"
    [ SolidCore.Solidity.Source.Value.int
        (SolidCore.Solidity.Shared.signedToWord (-5))
    , SolidCore.Solidity.Source.Value.int 2 ]
    Executable.Examples.signedIntAbiExpectedOutput

def checkedSignedSarMatches : Except TypeError Bool :=
  checkedOwnCallIntMatches 16
    Executable.Examples.checkedArithmeticContract
    "signedSar" SolidCore.Solidity.Source.State.empty
    [ SolidCore.Solidity.Source.Value.int
        (SolidCore.Solidity.Shared.signedToWord (-5))
    , SolidCore.Solidity.Source.Value.word 1 ]
    (SolidCore.Solidity.Shared.signedToWord (-3))

def checkedSignedSarAssignMatches : Except TypeError Bool :=
  checkedOwnCallIntMatches 16
    Executable.Examples.checkedArithmeticContract
    "signedSarAssign" SolidCore.Solidity.Source.State.empty
    [ SolidCore.Solidity.Source.Value.int
        (SolidCore.Solidity.Shared.signedToWord (-5))
    , SolidCore.Solidity.Source.Value.word 1 ]
    (SolidCore.Solidity.Shared.signedToWord (-3))

def checkedAddOverflowPanics : Except TypeError Bool :=
  checkedOwnCallPanicMatches 16
    Executable.Examples.checkedArithmeticContract
    "addOverflow" SolidCore.Solidity.Source.State.empty
    [SolidCore.Solidity.Source.Value.word 1] 0x11

def checkedUncheckedAddWraps : Except TypeError Bool :=
  checkedOwnCallWordMatches 16
    Executable.Examples.checkedArithmeticContract
    "uncheckedAddWrap" SolidCore.Solidity.Source.State.empty
    [SolidCore.Solidity.Source.Value.word 1] 0

def checkedSubUnderflowPanics : Except TypeError Bool :=
  checkedOwnCallPanicMatches 16
    Executable.Examples.checkedArithmeticContract
    "subUnderflow" SolidCore.Solidity.Source.State.empty
    [SolidCore.Solidity.Source.Value.word 2] 0x11

def checkedUncheckedSubWraps : Except TypeError Bool :=
  checkedOwnCallWordMatches 16
    Executable.Examples.checkedArithmeticContract
    "uncheckedSubWrap" SolidCore.Solidity.Source.State.empty
    [SolidCore.Solidity.Source.Value.word 2] (2 ^ 256 - 1)

def checkedMulOverflowPanics : Except TypeError Bool :=
  checkedOwnCallPanicMatches 16
    Executable.Examples.checkedArithmeticContract
    "mulOverflow" SolidCore.Solidity.Source.State.empty
    [SolidCore.Solidity.Source.Value.word 2] 0x11

def checkedUncheckedMulWraps : Except TypeError Bool :=
  checkedOwnCallWordMatches 16
    Executable.Examples.checkedArithmeticContract
    "uncheckedMulWrap" SolidCore.Solidity.Source.State.empty
    [SolidCore.Solidity.Source.Value.word 2] (2 ^ 256 - 2)

def checkedSignedNegOverflowPanics : Except TypeError Bool :=
  checkedOwnCallPanicMatches 16
    Executable.Examples.checkedArithmeticContract
    "signedNeg" SolidCore.Solidity.Source.State.empty
    [SolidCore.Solidity.Source.Value.int (2 ^ 255)] 0x11

def checkedUncheckedSignedNegWraps : Except TypeError Bool :=
  checkedOwnCallIntMatches 16
    Executable.Examples.checkedArithmeticContract
    "uncheckedSignedNeg" SolidCore.Solidity.Source.State.empty
    [SolidCore.Solidity.Source.Value.int (2 ^ 255)] (2 ^ 255)

def checkedExponentiationMatches : Except TypeError Bool :=
  checkedOwnCallWordMatches 16
    Executable.Examples.checkedArithmeticContract
    "powSmall" SolidCore.Solidity.Source.State.empty [] 256

def checkedExponentOverflowPanics : Except TypeError Bool :=
  checkedOwnCallPanicMatches 16
    Executable.Examples.checkedArithmeticContract
    "powOverflow" SolidCore.Solidity.Source.State.empty
    [SolidCore.Solidity.Source.Value.word (2 ^ 128)] 0x11

def checkedUncheckedExponentWraps : Except TypeError Bool :=
  checkedOwnCallWordMatches 16
    Executable.Examples.checkedArithmeticContract
    "uncheckedPowWrap" SolidCore.Solidity.Source.State.empty
    [SolidCore.Solidity.Source.Value.word (2 ^ 128)] 0

def checkedDivisionByZeroPanics : Except TypeError Bool :=
  checkedOwnCallPanicMatches 16
    Executable.Examples.checkedArithmeticContract
    "divide" SolidCore.Solidity.Source.State.empty
    [ SolidCore.Solidity.Source.Value.word 7
    , SolidCore.Solidity.Source.Value.word 0 ] 0x12

def checkedUncheckedDivisionByZeroStillPanics :
    Except TypeError Bool :=
  checkedOwnCallPanicMatches 16
    Executable.Examples.checkedArithmeticContract
    "uncheckedDivide" SolidCore.Solidity.Source.State.empty
    [ SolidCore.Solidity.Source.Value.word 7
    , SolidCore.Solidity.Source.Value.word 0 ] 0x12

def checkedUncheckedModuloByZeroStillPanics :
    Except TypeError Bool :=
  checkedOwnCallPanicMatches 16
    Executable.Examples.checkedArithmeticContract
    "uncheckedModulo" SolidCore.Solidity.Source.State.empty
    [ SolidCore.Solidity.Source.Value.word 7
    , SolidCore.Solidity.Source.Value.word 0 ] 0x12

def checkedSignedDivisionOverflowPanics :
    Except TypeError Bool :=
  checkedOwnCallPanicMatches 16
    Executable.Examples.checkedArithmeticContract
    "signedDivide" SolidCore.Solidity.Source.State.empty
    [ SolidCore.Solidity.Source.Value.int (2 ^ 255)
    , SolidCore.Solidity.Source.Value.int
        (SolidCore.Solidity.Shared.signedToWord (-1)) ] 0x11

def checkedUncheckedSignedDivisionOverflowWraps :
    Except TypeError Bool :=
  checkedOwnCallIntMatches 16
    Executable.Examples.checkedArithmeticContract
    "uncheckedSignedDivide" SolidCore.Solidity.Source.State.empty
    [ SolidCore.Solidity.Source.Value.int (2 ^ 255)
    , SolidCore.Solidity.Source.Value.int
        (SolidCore.Solidity.Shared.signedToWord (-1)) ] (2 ^ 255)

def checkedUncheckedInternalCallCalleeOverflowReverts :
    Except TypeError Bool :=
  checkedOwnCallPanicMatches 48
    Executable.Examples.checkedArithmeticContract
    "callOverflow" SolidCore.Solidity.Source.State.empty [] 0x11

def checkedUncheckedInternalCallArgumentWraps :
    Except TypeError Bool :=
  checkedOwnCallWordMatches 48
    Executable.Examples.checkedArithmeticContract
    "callWithWrappedArg" SolidCore.Solidity.Source.State.empty [] 0

def checkedUncheckedArithmeticInvalidSourcesRejected : Bool :=
  Result.isError
      (TypecheckedInput.checkedSourceUnit nestedUncheckedSource) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit uncheckedPlaceholderSource)

def checkedArithmeticSourceDisciplineAccepted : Bool :=
  Result.isOk
      (TypecheckedInput.checkedSourceUnit callUint8LiteralSource) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit signedBaseUnsignedExponentSource) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit shiftWideCountSource) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit bytesBitwiseSource) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit compoundShiftSource)

def checkedArithmeticSourceDisciplineRejected : Bool :=
  Result.isError
      (TypecheckedInput.checkedSourceUnit badCallUint8LiteralSource) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit signedExponentSource) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit badShiftSignedCountSource) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit badBytesArithmeticSource)

def checkedNarrowLiteralArgumentMatches :
    Except TypeError Bool :=
  checkedCallWordMatches 16 callUint8LiteralSource
    "CallUint8Literal" "callSmall"
    SolidCore.Solidity.Source.State.empty [] 1

def checkedNarrowDirtyParamPanics :
    Except TypeError Bool :=
  checkedOwnCallPanicMatches 16
    Executable.Examples.checkedArithmeticContract
    "echoUint8" SolidCore.Solidity.Source.State.empty
    [SolidCore.Solidity.Source.Value.word 300] 0x11

def checkedNarrowDirtyCalldataParamPanics :
    Except TypeError Bool := do
  let payload ←
    checkedAbiEncodeValues
      [SolidCore.Solidity.Source.Ty.uint256]
      [SolidCore.Solidity.Source.Value.word 300]
  let calldata :=
    SolidCore.Solidity.Source.ABI.encodeSelector
      (SolidCore.Solidity.Source.ABI.selectorFromSignature
        "echoUint8(uint8)") ++ payload
  let result ←
    CheckedInput.ownCallCalldata 16
      Executable.Examples.checkedArithmeticContract
      SolidCore.Solidity.Source.State.empty calldata
  let expectedPayload ←
    checkedAbiEncodeValues
      [SolidCore.Solidity.Source.Ty.uint256]
      [SolidCore.Solidity.Source.Value.word 0x11]
  let expected :=
    SolidCore.Solidity.Source.ABI.encodeSelector
      SolidCore.Solidity.Source.ABI.panicSelector ++ expectedPayload
  Except.ok (!result.success && result.output == expected)

def checkedNarrowReturnOverflowPanics :
    Except TypeError Bool :=
  checkedOwnCallPanicMatches 16
    Executable.Examples.checkedArithmeticContract
    "narrowReturnOverflow" SolidCore.Solidity.Source.State.empty
    [SolidCore.Solidity.Source.Value.word 255] 0x11

def checkedNarrowUncheckedReturnWraps :
    Except TypeError Bool :=
  checkedOwnCallWordMatches 16
    Executable.Examples.checkedArithmeticContract
    "narrowUncheckedReturnWrap" SolidCore.Solidity.Source.State.empty
    [SolidCore.Solidity.Source.Value.word 255] 0

def checkedNarrowLocalOverflowPanics :
    Except TypeError Bool :=
  checkedOwnCallPanicMatches 16
    Executable.Examples.checkedArithmeticContract
    "narrowLocalOverflow" SolidCore.Solidity.Source.State.empty
    [SolidCore.Solidity.Source.Value.word 255] 0x11

def checkedNarrowUncheckedLocalWraps :
    Except TypeError Bool :=
  checkedOwnCallWordMatches 16
    Executable.Examples.checkedArithmeticContract
    "narrowUncheckedLocalWrap" SolidCore.Solidity.Source.State.empty
    [SolidCore.Solidity.Source.Value.word 255] 0

def checkedNarrowPreIncrementOverflowPanics :
    Except TypeError Bool :=
  checkedOwnCallPanicMatches 16
    Executable.Examples.checkedArithmeticContract
    "narrowPreIncrementOverflow" SolidCore.Solidity.Source.State.empty
    [SolidCore.Solidity.Source.Value.word 255] 0x11

def checkedNarrowUncheckedPreIncrementWraps :
    Except TypeError Bool :=
  checkedOwnCallWordMatches 16
    Executable.Examples.checkedArithmeticContract
    "narrowUncheckedPreIncrementWrap" SolidCore.Solidity.Source.State.empty
    [SolidCore.Solidity.Source.Value.word 255] 0

def checkedNarrowPostIncrementOverflowPanics :
    Except TypeError Bool :=
  checkedOwnCallPanicMatches 16
    Executable.Examples.checkedArithmeticContract
    "narrowPostIncrementOverflow" SolidCore.Solidity.Source.State.empty
    [SolidCore.Solidity.Source.Value.word 255] 0x11

def checkedNarrowUncheckedPostIncrementWraps :
    Except TypeError Bool := do
  let result ←
    CheckedInput.ownCall 16
      Executable.Examples.checkedArithmeticContract
      (SolidCore.Solidity.Source.CallTarget.name
        "narrowUncheckedPostIncrement")
      SolidCore.Solidity.Source.State.empty
      [SolidCore.Solidity.Source.Value.word 255]
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _
      [ SolidCore.Solidity.Source.Value.word old
      , SolidCore.Solidity.Source.Value.word next ] =>
      Except.ok
        (SolidCore.Solidity.Source.wordEq old 255 &&
          SolidCore.Solidity.Source.wordEq next 0)
  | _ => Except.ok false

def checkedShiftWideCountMatches :
    Except TypeError Bool :=
  checkedCallWordMatches 16 shiftWideCountSource
    "ShiftWideCount" "shiftWide"
    SolidCore.Solidity.Source.State.empty [] 4

def checkedBytesBitwiseMatches :
    Except TypeError Bool :=
  checkedCallWordMatches 16 bytesBitwiseSource
    "BytesBitwise" "bytesBitwise"
    SolidCore.Solidity.Source.State.empty []
    (SolidCore.Solidity.Source.bytesToWordBE [1, 2, 3, 4])

def checkedCompoundShiftMatches :
    Except TypeError Bool :=
  checkedCallWordMatches 16 compoundShiftSource
    "CompoundShift" "compoundShift"
    SolidCore.Solidity.Source.State.empty [] 4

def checkedEmptyInlineAssemblyRejected : Bool :=
  Result.isError (CheckedInput.program emptyInlineAssemblySource)

def checkedNonemptyInlineAssemblyRejected : Bool :=
  Result.isError (CheckedInput.program nonemptyInlineAssemblySource)

def checkedInlineAssemblyBoundarySemanticsMatch :
    Except TypeError Bool :=
  Except.ok
    (checkedEmptyInlineAssemblyRejected && checkedNonemptyInlineAssemblyRejected)

def checkedIncrementExpressionVarDeclMatches :
    Except TypeError Bool :=
  checkedOwnCallWordTripleMatches 32
    Executable.Examples.expressionTargetEffectsContract
    "incrementVarDecl" SolidCore.Solidity.Source.State.empty [] 1 3 3

def checkedDecrementExpressionVarDeclMatches :
    Except TypeError Bool :=
  checkedOwnCallWordTripleMatches 32
    Executable.Examples.expressionTargetEffectsContract
    "decrementVarDecl" SolidCore.Solidity.Source.State.empty [] 3 1 1

def checkedIncrementExpressionAssignmentMatches :
    Except TypeError Bool :=
  checkedOwnCallWordTripleMatches 32
    Executable.Examples.expressionTargetEffectsContract
    "incrementAssignment" SolidCore.Solidity.Source.State.empty [] 11 13 3

def checkedSignedIncrementExpressionVarDeclMatches :
    Except TypeError Bool :=
  checkedOwnCallIntTripleMatches 32
    Executable.Examples.expressionTargetEffectsContract
    "signedIncrementVarDecl" SolidCore.Solidity.Source.State.empty [] 1 3 3

def checkedAssignmentExpressionVarDeclMatches :
    Except TypeError Bool :=
  checkedOwnCallWordTripleMatches 32
    Executable.Examples.expressionTargetEffectsContract
    "assignmentVarDecl" SolidCore.Solidity.Source.State.empty [] 5 7 7

def checkedAssignmentExpressionReturnMatches :
    Except TypeError Bool :=
  checkedOwnCallWordPairMatches 32
    Executable.Examples.expressionTargetEffectsContract
    "assignmentReturn" SolidCore.Solidity.Source.State.empty [] 9 1

def checkedIndexedAssignmentTargetEffectsMatches :
    Except TypeError Bool :=
  checkedOwnCallWordTripleMatches 48
    Executable.Examples.expressionTargetEffectsContract
    "indexedAssignment" SolidCore.Solidity.Source.State.empty [] 1 99 20

def checkedIndexedCompoundTargetEffectsMatches :
    Except TypeError Bool :=
  checkedOwnCallWordTripleMatches 48
    Executable.Examples.expressionTargetEffectsContract
    "indexedCompound" SolidCore.Solidity.Source.State.empty [] 1 17 20

def checkedTupleIndexedAssignmentTargetEffectsMatches :
    Except TypeError Bool :=
  checkedOwnCallWordTripleMatches 48
    Executable.Examples.expressionTargetEffectsContract
    "tupleIndexedAssignment" SolidCore.Solidity.Source.State.empty [] 2 7 8

def checkedStorageIndexedCompoundTargetEffectsMatches :
    Except TypeError Bool :=
  checkedOwnCallWordTripleMatches 64
    Executable.Examples.storageIndexedCompoundTargetEffectsContract
    "run" SolidCore.Solidity.Source.State.empty [] 1 17 20

def checkedIndexedDeleteAndIncrementTargetEffectsMatches :
    Except TypeError Bool :=
  checkedOwnCallWordQuintMatches 64
    Executable.Examples.expressionTargetEffectsContract
    "indexedDeleteAndIncrement"
    SolidCore.Solidity.Source.State.empty [] 20 2 0 21 30

def checkedRequireCustomArgumentEvaluationMatches :
    Except TypeError Bool :=
  checkedOwnCallWordMatches 32
    Executable.Examples.expressionTargetEffectsContract
    "requireCustomArgument" SolidCore.Solidity.Source.State.empty [] 5

def checkedEventArgumentEvaluationMatches :
    Except TypeError Bool := do
  let result ←
    CheckedInput.ownCall 32
      Executable.Examples.expressionTargetEffectsContract
      (SolidCore.Solidity.Source.CallTarget.name "eventArgument")
      SolidCore.Solidity.Source.State.empty []
  match result with
  | SolidCore.Solidity.Source.CallResult.returned state
      [SolidCore.Solidity.Source.Value.word final] =>
      match state.events with
      | [{ name := "Seen"
           data := [SolidCore.Solidity.Source.Value.word emitted]
           .. }] =>
          Except.ok
            (SolidCore.Solidity.Source.wordEq final 5 &&
              SolidCore.Solidity.Source.wordEq emitted 5)
      | _ => Except.ok false
  | _ => Except.ok false

def checkedRevertCustomArgumentEvaluationMatches :
    Except TypeError Bool := do
  let result ←
    CheckedInput.ownCall 32
      Executable.Examples.expressionTargetEffectsContract
      (SolidCore.Solidity.Source.CallTarget.name "revertCustomArgument")
      SolidCore.Solidity.Source.State.empty []
  match result with
  | SolidCore.Solidity.Source.CallResult.reverted _
      (SolidCore.Solidity.Source.RevertData.custom "NeedsEval"
        [SolidCore.Solidity.Source.Value.word arg]) =>
      Except.ok (SolidCore.Solidity.Source.wordEq arg 5)
  | _ => Except.ok false

def checkedDynamicRequireReasonMatches :
    Except TypeError Bool := do
  let expected ←
    optionToExcept "dynamic require reason"
      (Executable.Examples.errorStringBytes? "Nope")
  let result ←
    CheckedInput.ownCall 32
      Executable.Examples.expressionTargetEffectsContract
      (SolidCore.Solidity.Source.CallTarget.name "dynamicRequireReason")
      SolidCore.Solidity.Source.State.empty []
  match result with
  | SolidCore.Solidity.Source.CallResult.reverted _
      (SolidCore.Solidity.Source.RevertData.raw bytes) =>
      Except.ok (bytes == expected)
  | _ => Except.ok false

def checkedDynamicRevertReasonMatches :
    Except TypeError Bool := do
  let expected ←
    optionToExcept "dynamic revert reason"
      (Executable.Examples.errorStringBytes? "Gone")
  let result ←
    CheckedInput.ownCall 32
      Executable.Examples.expressionTargetEffectsContract
      (SolidCore.Solidity.Source.CallTarget.name "dynamicRevertReason")
      SolidCore.Solidity.Source.State.empty []
  match result with
  | SolidCore.Solidity.Source.CallResult.reverted _
      (SolidCore.Solidity.Source.RevertData.raw bytes) =>
      Except.ok (bytes == expected)
  | _ => Except.ok false

def checkedExpressionTargetEffectSemanticsMatch :
    Except TypeError Bool := do
  let incVar ← checkedIncrementExpressionVarDeclMatches
  let decVar ← checkedDecrementExpressionVarDeclMatches
  let incAssign ← checkedIncrementExpressionAssignmentMatches
  let signedInc ← checkedSignedIncrementExpressionVarDeclMatches
  let assignVar ← checkedAssignmentExpressionVarDeclMatches
  let assignReturn ← checkedAssignmentExpressionReturnMatches
  let indexedAssign ← checkedIndexedAssignmentTargetEffectsMatches
  let indexedCompound ← checkedIndexedCompoundTargetEffectsMatches
  let tupleIndexed ← checkedTupleIndexedAssignmentTargetEffectsMatches
  let storageIndexed ← checkedStorageIndexedCompoundTargetEffectsMatches
  let indexedDeleteInc ← checkedIndexedDeleteAndIncrementTargetEffectsMatches
  let requireCustom ← checkedRequireCustomArgumentEvaluationMatches
  let eventArg ← checkedEventArgumentEvaluationMatches
  let revertCustom ← checkedRevertCustomArgumentEvaluationMatches
  let dynamicRequire ← checkedDynamicRequireReasonMatches
  let dynamicRevert ← checkedDynamicRevertReasonMatches
  Except.ok
    (checkedTargetEffectContractsAccepted &&
      incVar && decVar && incAssign && signedInc &&
      assignVar && assignReturn &&
      indexedAssign && indexedCompound && tupleIndexed && storageIndexed &&
      indexedDeleteInc &&
      requireCustom && eventArg && revertCustom &&
      dynamicRequire && dynamicRevert)

def checkedUsingMathLibrary : Solidity.ContractDecl :=
  { name := "CheckedMath"
    kind := ContractKind.library
    items :=
      [ ContractItem.function
          { name := some "inc"
            visibility := some Visibility.internal_
            mutability := StateMutability.pure
            params := [{ name := some "self", ty := Ty.uint 256 }]
            returns := [{ name := some "out", ty := Ty.uint 256 }]
            body :=
              some
                (Solidity.Stmt.returnValues
                  (some
                    (Solidity.Expr.binary BinaryOp.add
                      (Solidity.Expr.ident "self")
                      (Solidity.Expr.literal
                        (Solidity.Literal.number "1"))))) }
      , ContractItem.function
          { name := some "mix"
            visibility := some Visibility.internal_
            mutability := StateMutability.pure
            params :=
              [ { name := some "self", ty := Ty.uint 256 }
              , { name := some "right", ty := Ty.uint 256 } ]
            returns := [{ name := some "out", ty := Ty.uint 256 }]
            body :=
              some
                (Solidity.Stmt.returnValues
                  (some
                    (Solidity.Expr.binary BinaryOp.add
                      (Solidity.Expr.binary BinaryOp.mul
                        (Solidity.Expr.ident "self")
                        (Solidity.Expr.literal
                          (Solidity.Literal.number "10")))
                      (Solidity.Expr.ident "right")))) } ] }

def checkedUsingFreeIncFunction : Solidity.FunctionDecl :=
  { name := some "checkedFreeInc"
    params := [{ name := some "self", ty := Ty.uint 256 }]
    returns := [{ name := some "out", ty := Ty.uint 256 }]
    mutability := StateMutability.pure
    body :=
      some
        (Solidity.Stmt.returnValues
          (some
            (Solidity.Expr.binary BinaryOp.add
              (Solidity.Expr.ident "self")
              (Solidity.Expr.literal
                (Solidity.Literal.number "1"))))) }

def checkedUsingMethodContract : Solidity.ContractDecl :=
  { name := "CheckedUsingMethod"
    items :=
      [ ContractItem.usingDecl
          { library := { segments := ["CheckedMath"] }
            target := some (Ty.uint 256) }
      , ContractItem.function
          { name := some "run"
            visibility := some Visibility.public_
            params := [{ name := some "x", ty := Ty.uint 256 }]
            returns := [{ name := some "out", ty := Ty.uint 256 }]
            body :=
              some
                (Solidity.Stmt.returnValues
                  (some
                    (Solidity.Expr.call
                      (Solidity.Expr.member
                        (Solidity.Expr.ident "x") "inc")
                      []))) } ] }

def checkedUsingDirectContract : Solidity.ContractDecl :=
  { name := "CheckedUsingDirect"
    items :=
      [ ContractItem.function
          { name := some "run"
            visibility := some Visibility.public_
            params := [{ name := some "x", ty := Ty.uint 256 }]
            returns := [{ name := some "out", ty := Ty.uint 256 }]
            body :=
              some
                (Solidity.Stmt.returnValues
                  (some
                    (Solidity.Expr.call
                      (Solidity.Expr.member
                        (Solidity.Expr.ident "CheckedMath")
                        "inc")
                      [Solidity.Arg.positional
                        (Solidity.Expr.ident "x")]))) } ] }

def checkedUsingSourceLevelContract :
    Solidity.ContractDecl :=
  { name := "CheckedUsingSourceLevel"
    items :=
      [ ContractItem.function
          { name := some "run"
            visibility := some Visibility.public_
            params := [{ name := some "x", ty := Ty.uint 256 }]
            returns := [{ name := some "out", ty := Ty.uint 256 }]
            body :=
              some
                (Solidity.Stmt.returnValues
                  (some
                    (Solidity.Expr.call
                      (Solidity.Expr.member
                        (Solidity.Expr.ident "x") "inc")
                      []))) } ] }

def checkedUsingStorageContract : Solidity.ContractDecl :=
  { name := "CheckedUsingStorage"
    items :=
      [ ContractItem.stateVar { name := "x", ty := Ty.uint 256 }
      , ContractItem.usingDecl
          { library := { segments := ["CheckedMath"] }
            target := some (Ty.uint 256) }
      , ContractItem.function
          { name := some "bump"
            visibility := some Visibility.public_
            body :=
              some
                (Solidity.Stmt.expr
                  (Solidity.Expr.assign
                    (Solidity.Expr.ident "x")
                    AssignOp.assign
                    (Solidity.Expr.call
                      (Solidity.Expr.member
                        (Solidity.Expr.ident "x") "inc")
                      []))) } ] }

def checkedUsingNamedMethodContract :
    Solidity.ContractDecl :=
  { name := "CheckedUsingNamedMethod"
    items :=
      [ ContractItem.usingDecl
          { library := { segments := ["CheckedMath"] }
            target := some (Ty.uint 256) }
      , ContractItem.function
          { name := some "run"
            visibility := some Visibility.public_
            params := [{ name := some "x", ty := Ty.uint 256 }]
            returns := [{ name := some "out", ty := Ty.uint 256 }]
            body :=
              some
                (Solidity.Stmt.returnValues
                  (some
                    (Solidity.Expr.call
                      (Solidity.Expr.member
                        (Solidity.Expr.ident "x") "mix")
                      [Solidity.Arg.named "right"
                        (Solidity.Expr.literal
                          (Solidity.Literal.number "2"))]))) } ] }

def checkedUsingExplicitFunctionContract :
    Solidity.ContractDecl :=
  { name := "CheckedUsingExplicitFunction"
    items :=
      [ ContractItem.usingDecl
          { library := { segments := [] }
            functions :=
              [{ function := { segments := ["CheckedMath", "mix"] } }]
            target := some (Ty.uint 256) }
      , ContractItem.function
          { name := some "run"
            visibility := some Visibility.public_
            params := [{ name := some "x", ty := Ty.uint 256 }]
            returns := [{ name := some "out", ty := Ty.uint 256 }]
            body :=
              some
                (Solidity.Stmt.returnValues
                  (some
                    (Solidity.Expr.call
                      (Solidity.Expr.member
                        (Solidity.Expr.ident "x") "mix")
                      [Solidity.Arg.positional
                        (Solidity.Expr.literal
                          (Solidity.Literal.number "2"))]))) } ] }

def checkedUsingExplicitFreeFunctionContract :
    Solidity.ContractDecl :=
  { name := "CheckedUsingExplicitFreeFunction"
    items :=
      [ ContractItem.usingDecl
          { library := { segments := [] }
            functions :=
              [{ function := { segments := ["checkedFreeInc"] } }]
            target := some (Ty.uint 256) }
      , ContractItem.function
          { name := some "run"
            visibility := some Visibility.public_
            params := [{ name := some "x", ty := Ty.uint 256 }]
            returns := [{ name := some "out", ty := Ty.uint 256 }]
            body :=
              some
                (Solidity.Stmt.returnValues
                  (some
                    (Solidity.Expr.call
                      (Solidity.Expr.member
                        (Solidity.Expr.ident "x")
                        "checkedFreeInc")
                      []))) } ] }

def checkedUsingNamedDirectContract :
    Solidity.ContractDecl :=
  { name := "CheckedUsingNamedDirect"
    items :=
      [ ContractItem.function
          { name := some "run"
            visibility := some Visibility.public_
            returns := [{ name := some "out", ty := Ty.uint 256 }]
            body :=
              some
                (Solidity.Stmt.returnValues
                  (some
                    (Solidity.Expr.call
                      (Solidity.Expr.member
                        (Solidity.Expr.ident "CheckedMath")
                        "mix")
                      [ Solidity.Arg.named "right"
                          (Solidity.Expr.literal
                            (Solidity.Literal.number "2"))
                      , Solidity.Arg.named "self"
                          (Solidity.Expr.literal
                            (Solidity.Literal.number "4")) ]))) } ] }

def checkedUsingLibraryUnit : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract checkedUsingMathLibrary
      , Solidity.SourceItem.freeFunction
          checkedUsingFreeIncFunction
      , Solidity.SourceItem.contract
          checkedUsingMethodContract
      , Solidity.SourceItem.contract
          checkedUsingDirectContract
      , Solidity.SourceItem.contract
          checkedUsingStorageContract
      , Solidity.SourceItem.contract
          checkedUsingNamedMethodContract
      , Solidity.SourceItem.contract
          checkedUsingExplicitFunctionContract
      , Solidity.SourceItem.contract
          checkedUsingExplicitFreeFunctionContract
      , Solidity.SourceItem.contract
          checkedUsingNamedDirectContract ] }

def checkedUsingSourceLevelUnit : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract checkedUsingMathLibrary
      , Solidity.SourceItem.usingDecl
          { library := { segments := ["CheckedMath"] }
            target := some (Ty.uint 256) }
      , Solidity.SourceItem.contract
          checkedUsingSourceLevelContract ] }

def checkedUsingLibraryMethodMatches : Except TypeError Bool :=
  checkedCallWordMatches 32 checkedUsingLibraryUnit
    "CheckedUsingMethod" "run"
    SolidCore.Solidity.Source.State.empty
    [SolidCore.Solidity.Source.Value.word 41] 42

def checkedUsingLibraryDirectCallMatches :
    Except TypeError Bool :=
  checkedCallWordMatches 32 checkedUsingLibraryUnit
    "CheckedUsingDirect" "run"
    SolidCore.Solidity.Source.State.empty
    [SolidCore.Solidity.Source.Value.word 11] 12

def checkedUsingSourceLevelMatches : Except TypeError Bool :=
  checkedCallWordMatches 32 checkedUsingSourceLevelUnit
    "CheckedUsingSourceLevel" "run"
    SolidCore.Solidity.Source.State.empty
    [SolidCore.Solidity.Source.Value.word 6] 7

def checkedUsingStorageReceiverMatches : Except TypeError Bool :=
  checkedCallSlotMatches 32 checkedUsingLibraryUnit
    "CheckedUsingStorage" "bump"
    (SolidCore.Solidity.Source.State.empty.storeSlot 0 9)
    [] 0 10

def checkedUsingNamedMethodMatches : Except TypeError Bool :=
  checkedCallWordMatches 32 checkedUsingLibraryUnit
    "CheckedUsingNamedMethod" "run"
    SolidCore.Solidity.Source.State.empty
    [SolidCore.Solidity.Source.Value.word 4] 42

def checkedUsingExplicitFunctionMatches :
    Except TypeError Bool :=
  checkedCallWordMatches 32 checkedUsingLibraryUnit
    "CheckedUsingExplicitFunction" "run"
    SolidCore.Solidity.Source.State.empty
    [SolidCore.Solidity.Source.Value.word 4] 42

def checkedUsingExplicitFreeFunctionMatches :
    Except TypeError Bool :=
  checkedCallWordMatches 32 checkedUsingLibraryUnit
    "CheckedUsingExplicitFreeFunction" "run"
    SolidCore.Solidity.Source.State.empty
    [SolidCore.Solidity.Source.Value.word 8] 9

def checkedUsingNamedDirectCallMatches :
    Except TypeError Bool :=
  checkedCallWordMatches 32 checkedUsingLibraryUnit
    "CheckedUsingNamedDirect" "run"
    SolidCore.Solidity.Source.State.empty [] 42

def checkedCanonicalUsingLibraryUnitsAccepted : Bool :=
  Result.isOk
    (TypecheckedInput.checkedSourceUnit
      Executable.Examples.usingLibraryUnit) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit
        Executable.Examples.usingHigherOrderUnit) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit
        Executable.Examples.globalUsingPriceUnit)

def checkedCanonicalUsingLibraryMethodMatches :
    Except TypeError Bool :=
  checkedCallWordMatches 32 Executable.Examples.usingLibraryUnit
    "UsingMethod" "run"
    SolidCore.Solidity.Source.State.empty
    [SolidCore.Solidity.Source.Value.word 41] 42

def checkedCanonicalUsingLibraryDirectCallMatches :
    Except TypeError Bool :=
  checkedCallWordMatches 32 Executable.Examples.usingLibraryUnit
    "UsingDirect" "run"
    SolidCore.Solidity.Source.State.empty
    [SolidCore.Solidity.Source.Value.word 11] 12

def checkedCanonicalUsingSourceLevelMatches :
    Except TypeError Bool :=
  checkedCallWordMatches 32 Executable.Examples.usingLibraryUnit
    "UsingSourceLevel" "run"
    SolidCore.Solidity.Source.State.empty
    [SolidCore.Solidity.Source.Value.word 6] 7

def checkedCanonicalUsingStorageReceiverMatches :
    Except TypeError Bool :=
  checkedCallSlotMatches 32 Executable.Examples.usingLibraryUnit
    "UsingStorage" "bump"
    (SolidCore.Solidity.Source.State.empty.storeSlot 0 9)
    [] 0 10

def checkedCanonicalUsingNamedMethodMatches :
    Except TypeError Bool :=
  checkedCallWordMatches 32 Executable.Examples.usingLibraryUnit
    "UsingNamedMethod" "run"
    SolidCore.Solidity.Source.State.empty
    [SolidCore.Solidity.Source.Value.word 4] 42

def checkedCanonicalUsingExplicitFunctionMatches :
    Except TypeError Bool :=
  checkedCallWordMatches 32 Executable.Examples.usingLibraryUnit
    "UsingExplicitFunction" "run"
    SolidCore.Solidity.Source.State.empty
    [SolidCore.Solidity.Source.Value.word 4] 42

def checkedCanonicalUsingExplicitFreeFunctionMatches :
    Except TypeError Bool :=
  checkedCallWordMatches 32 Executable.Examples.usingLibraryUnit
    "UsingExplicitFreeFunction" "run"
    SolidCore.Solidity.Source.State.empty
    [SolidCore.Solidity.Source.Value.word 8] 9

def checkedCanonicalUsingNamedDirectCallMatches :
    Except TypeError Bool :=
  checkedCallWordMatches 32 Executable.Examples.usingLibraryUnit
    "UsingNamedDirect" "run"
    SolidCore.Solidity.Source.State.empty [] 42

def checkedCanonicalUsingHigherOrderFunctionPointerMatches :
    Except TypeError Bool :=
  checkedCallWordMatches 64 Executable.Examples.usingHigherOrderUnit
    "UsingHigherOrder" "run"
    SolidCore.Solidity.Source.State.empty
    [SolidCore.Solidity.Source.Value.word 21] 42

def checkedCanonicalUsingHigherOrderNamedFunctionPointerMatches :
    Except TypeError Bool :=
  checkedCallWordMatches 64 Executable.Examples.usingHigherOrderUnit
    "UsingHigherOrder" "runNamed"
    SolidCore.Solidity.Source.State.empty
    [SolidCore.Solidity.Source.Value.word 21] 42

def checkedCanonicalGlobalUsingPriceMatches :
    Except TypeError Bool :=
  checkedCallWordMatches 48 Executable.Examples.globalUsingPriceUnit
    "GlobalUsingPrice" "run"
    SolidCore.Solidity.Source.State.empty
    [SolidCore.Solidity.Source.Value.word 41] 42

def checkedCanonicalGlobalUsingPriceLocalMatches :
    Except TypeError Bool :=
  checkedCallWordMatches 48 Executable.Examples.globalUsingPriceUnit
    "GlobalUsingPrice" "runLocal"
    SolidCore.Solidity.Source.State.empty
    [SolidCore.Solidity.Source.Value.word 9] 10

def checkedCanonicalGlobalUsingPriceAssignMatches :
    Except TypeError Bool :=
  checkedCallWordMatches 48 Executable.Examples.globalUsingPriceUnit
    "GlobalUsingPrice" "runAssign"
    SolidCore.Solidity.Source.State.empty
    [SolidCore.Solidity.Source.Value.word 17] 18

def checkedCanonicalGlobalUsingPriceOperatorUnitAccepted : Bool :=
  Result.isOk
    (TypecheckedInput.checkedSourceUnit
      Executable.Examples.globalUsingPriceOperatorUnit)

def checkedCanonicalGlobalUsingPriceAddOperatorMatches :
    Except TypeError Bool :=
  checkedCallWordMatches 48
    Executable.Examples.globalUsingPriceOperatorUnit
    "GlobalUsingPriceOperator" "sum"
    SolidCore.Solidity.Source.State.empty
    [ SolidCore.Solidity.Source.Value.word 14
    , SolidCore.Solidity.Source.Value.word 28 ] 42

def checkedCanonicalGlobalUsingPriceLtOperatorMatches :
    Except TypeError Bool :=
  checkedCallWordMatches 48
    Executable.Examples.globalUsingPriceOperatorUnit
    "GlobalUsingPriceOperator" "less"
    SolidCore.Solidity.Source.State.empty
    [ SolidCore.Solidity.Source.Value.word 14
    , SolidCore.Solidity.Source.Value.word 28 ] 1

def checkedCanonicalGlobalUsingPriceUnaryOperatorsMatch :
    Except TypeError Bool := do
  let result ←
    CheckedInput.callContract 48
      Executable.Examples.globalUsingPriceOperatorUnit
      "GlobalUsingPriceOperator"
      (SolidCore.Solidity.Source.CallTarget.name "unary")
      SolidCore.Solidity.Source.State.empty
      [SolidCore.Solidity.Source.Value.word 14]
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _
      [ SolidCore.Solidity.Source.Value.word negated
      , SolidCore.Solidity.Source.Value.word inverted ] =>
      Except.ok
        (SolidCore.Solidity.Source.wordEq negated 15 &&
          SolidCore.Solidity.Source.wordEq inverted 16)
  | _ => Except.ok false

def checkedCanonicalExternalLibraryUsingFixturesAccepted : Bool :=
  Result.isOk
    (TypecheckedInput.checkedSourceUnit
      Executable.Examples.externalLibraryUnit) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit
        Executable.Examples.usingModifierUnit) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit
        Executable.Examples.usingConstructorUnit)

def checkedCanonicalExternalLibraryDelegateCallMatches
    (contractName : Name) (input output : Word) :
    Except TypeError Bool := do
  let contract ←
    CheckedInput.contract
      Executable.Examples.externalLibraryUnit contractName
  let callResult ←
    optionToExcept "canonical external library call result"
      (Executable.Examples.externalLibraryCallResult? input output)
  let result ←
    CheckedInput.callFunctionWithContextFailOpen 64
      (SolidCore.Solidity.Source.responderOfResults
                               [callResult]
      [])
      Executable.Examples.externalLibraryUnit contractName "run"
      { contract.core.context with
        contractAddresses := [("ExternalMath", 0xbeef)] }
      SolidCore.Solidity.Source.State.empty
      [SolidCore.Solidity.Source.Value.word input]
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _
      [SolidCore.Solidity.Source.Value.word value] =>
      Except.ok (SolidCore.Solidity.Source.wordEq value output)
  | _ => Except.ok false

def checkedCanonicalExternalLibraryDirectDelegateCallMatches :
    Except TypeError Bool :=
  checkedCanonicalExternalLibraryDelegateCallMatches
    "ExternalLibraryDirect" 41 42

def checkedCanonicalExternalLibraryUsingDelegateCallMatches :
    Except TypeError Bool :=
  checkedCanonicalExternalLibraryDelegateCallMatches
    "ExternalLibraryUsing" 6 7

def checkedCanonicalUsingModifierLibraryExpansionMatches :
    Except TypeError Bool :=
  checkedCallSlotMatches 64 Executable.Examples.usingModifierUnit
    "UsingModifier" "run"
    SolidCore.Solidity.Source.State.empty
    [SolidCore.Solidity.Source.Value.word 40] 0 42

def checkedCanonicalUsingConstructorMatches :
    Except TypeError Bool :=
  checkedConstructSlotMatches 32
    Executable.Examples.usingConstructorUnit
    "UsingConstructor"
    SolidCore.Solidity.Source.State.empty
    [SolidCore.Solidity.Source.Value.word 41] 0 42

def checkedUsingHigherOrderFunctionPointerMatches :
    Except TypeError Bool :=
  checkedCallWordMatches 64 usingHigherOrderFunctionSource
    "UsingHigherOrder" "usingHigherOrder"
    SolidCore.Solidity.Source.State.empty
    [SolidCore.Solidity.Source.Value.word 21] 42

def checkedUsingHigherOrderNamedFunctionPointerMatches :
    Except TypeError Bool :=
  checkedCallWordMatches 64 usingHigherOrderNamedFunctionSource
    "UsingHigherOrderNamed" "usingHigherOrderNamed"
    SolidCore.Solidity.Source.State.empty
    [SolidCore.Solidity.Source.Value.word 21] 42

def checkedGlobalUsingPriceMatches : Except TypeError Bool :=
  checkedCallWordMatches 48 globalUsingPriceSource
    "GlobalUsingPrice" "run"
    SolidCore.Solidity.Source.State.empty
    [SolidCore.Solidity.Source.Value.word 41] 42

def checkedGlobalUsingPriceOperatorContract :
    Solidity.ContractDecl :=
  { name := "CheckedGlobalUsingPriceOperator"
    items :=
      [ ContractItem.function
          { name := some "sum"
            visibility := some Visibility.public_
            params :=
              [ { name := some "left", ty := Ty.uint 256 }
              , { name := some "right", ty := Ty.uint 256 } ]
            returns := [{ name := some "out", ty := Ty.uint 256 }]
            body :=
              some
                (Solidity.Stmt.block
                  [ Solidity.Stmt.varDecl
                      [{ name := some "a", ty := some priceTy }]
                      (some
                        (Solidity.Expr.call
                          (Solidity.Expr.member
                            (Solidity.Expr.typeName priceTy)
                            "wrap")
                          [Solidity.Arg.positional
                            (Solidity.Expr.ident "left")]))
                  , Solidity.Stmt.varDecl
                      [{ name := some "b", ty := some priceTy }]
                      (some
                        (Solidity.Expr.call
                          (Solidity.Expr.member
                            (Solidity.Expr.typeName priceTy)
                            "wrap")
                          [Solidity.Arg.positional
                            (Solidity.Expr.ident "right")]))
                  , Solidity.Stmt.returnValues
                      (some
                        (Solidity.Expr.call
                          (Solidity.Expr.member
                            (Solidity.Expr.typeName priceTy)
                            "unwrap")
                          [ Solidity.Arg.positional
                              (Solidity.Expr.binary BinaryOp.add
                                (Solidity.Expr.ident "a")
                                (Solidity.Expr.ident "b")) ])) ]) }
      , ContractItem.function
          { name := some "less"
            visibility := some Visibility.public_
            params :=
              [ { name := some "left", ty := Ty.uint 256 }
              , { name := some "right", ty := Ty.uint 256 } ]
            returns := [{ name := some "out", ty := Ty.bool }]
            body :=
              some
                (Solidity.Stmt.block
                  [ Solidity.Stmt.varDecl
                      [{ name := some "a", ty := some priceTy }]
                      (some
                        (Solidity.Expr.call
                          (Solidity.Expr.member
                            (Solidity.Expr.typeName priceTy)
                            "wrap")
                          [Solidity.Arg.positional
                            (Solidity.Expr.ident "left")]))
                  , Solidity.Stmt.varDecl
                      [{ name := some "b", ty := some priceTy }]
                      (some
                        (Solidity.Expr.call
                          (Solidity.Expr.member
                            (Solidity.Expr.typeName priceTy)
                            "wrap")
                          [Solidity.Arg.positional
                            (Solidity.Expr.ident "right")]))
                  , Solidity.Stmt.returnValues
                      (some
                        (Solidity.Expr.binary BinaryOp.lt
                          (Solidity.Expr.ident "a")
                          (Solidity.Expr.ident "b"))) ]) }
      , ContractItem.function
          { name := some "unary"
            visibility := some Visibility.public_
            params := [{ name := some "raw", ty := Ty.uint 256 }]
            returns :=
              [ { name := some "negated", ty := Ty.uint 256 }
              , { name := some "inverted", ty := Ty.uint 256 } ]
            body :=
              some
                (Solidity.Stmt.block
                  [ Solidity.Stmt.varDecl
                      [{ name := some "a", ty := some priceTy }]
                      (some
                        (Solidity.Expr.call
                          (Solidity.Expr.member
                            (Solidity.Expr.typeName priceTy)
                            "wrap")
                          [Solidity.Arg.positional
                            (Solidity.Expr.ident "raw")]))
                  , Solidity.Stmt.varDecl
                      [{ name := some "negated", ty := some priceTy }]
                      (some
                        (Solidity.Expr.unary UnaryOp.neg
                          (Solidity.Expr.ident "a")))
                  , Solidity.Stmt.varDecl
                      [{ name := some "inverted", ty := some priceTy }]
                      (some
                        (Solidity.Expr.unary UnaryOp.bitNot
                          (Solidity.Expr.ident "a")))
                  , Solidity.Stmt.returnValues
                      (some
                        (Solidity.Expr.tuple
                          [ Solidity.TupleItem.value
                              (Solidity.Expr.call
                                (Solidity.Expr.member
                                  (Solidity.Expr.typeName priceTy)
                                  "unwrap")
                                [Solidity.Arg.positional
                                  (Solidity.Expr.ident
                                    "negated")])
                          , Solidity.TupleItem.value
                              (Solidity.Expr.call
                                (Solidity.Expr.member
                                  (Solidity.Expr.typeName priceTy)
                                  "unwrap")
                                [Solidity.Arg.positional
                                  (Solidity.Expr.ident
                                    "inverted")]) ])) ]) } ] }

def checkedGlobalUsingPriceOperatorUnit :
    Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.freeUserValueType priceDecl
      , Solidity.SourceItem.freeFunction
          priceOperatorAddFunction
      , Solidity.SourceItem.freeFunction
          priceOperatorLtFunction
      , Solidity.SourceItem.freeFunction
          priceOperatorNegFunction
      , Solidity.SourceItem.freeFunction
          priceOperatorBitNotFunction
      , Solidity.SourceItem.usingDecl
          { library := { segments := [] }
            functions :=
              [ { function := { segments := ["priceAdd"] }
                  operator? := some
                    (UsingOperator.binary BinaryOp.add) }
              , { function := { segments := ["priceLt"] }
                  operator? := some
                    (UsingOperator.binary BinaryOp.lt) }
              , { function := { segments := ["priceNeg"] }
                  operator? := some
                    (UsingOperator.unary UnaryOp.neg) }
              , { function := { segments := ["priceBitNot"] }
                  operator? := some
                    (UsingOperator.unary UnaryOp.bitNot) } ]
            target := some priceTy
            global := true }
      , Solidity.SourceItem.contract
          checkedGlobalUsingPriceOperatorContract ] }

def checkedGlobalUsingPriceAddOperatorMatches :
    Except TypeError Bool :=
  checkedCallWordMatches 48 checkedGlobalUsingPriceOperatorUnit
    "CheckedGlobalUsingPriceOperator" "sum"
    SolidCore.Solidity.Source.State.empty
    [ SolidCore.Solidity.Source.Value.word 14
    , SolidCore.Solidity.Source.Value.word 28 ] 42

def checkedGlobalUsingPriceLtOperatorMatches :
    Except TypeError Bool :=
  checkedCallWordMatches 48 checkedGlobalUsingPriceOperatorUnit
    "CheckedGlobalUsingPriceOperator" "less"
    SolidCore.Solidity.Source.State.empty
    [ SolidCore.Solidity.Source.Value.word 14
    , SolidCore.Solidity.Source.Value.word 28 ] 1

def checkedGlobalUsingPriceUnaryOperatorsMatch :
    Except TypeError Bool := do
  let result ←
    CheckedInput.callContract 48 checkedGlobalUsingPriceOperatorUnit
      "CheckedGlobalUsingPriceOperator"
      (SolidCore.Solidity.Source.CallTarget.name "unary")
      SolidCore.Solidity.Source.State.empty
      [SolidCore.Solidity.Source.Value.word 14]
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _
      [ SolidCore.Solidity.Source.Value.word negated
      , SolidCore.Solidity.Source.Value.word inverted ] =>
      Except.ok
        (SolidCore.Solidity.Source.wordEq negated 15 &&
          SolidCore.Solidity.Source.wordEq inverted 16)
  | _ => Except.ok false

def checkedExternalLibraryMath :
    Solidity.ContractDecl :=
  { name := "CheckedExternalMath"
    kind := ContractKind.library
    items :=
      [ ContractItem.function
          { name := some "plusOne"
            visibility := some Visibility.public_
            mutability := StateMutability.pure
            params := [{ name := some "self", ty := Ty.uint 256 }]
            returns := [{ name := some "out", ty := Ty.uint 256 }]
            body :=
              some
                (Solidity.Stmt.returnValues
                  (some
                    (Solidity.Expr.binary BinaryOp.add
                      (Solidity.Expr.ident "self")
                      (Solidity.Expr.literal
                        (Solidity.Literal.number "1"))))) } ] }

def checkedExternalLibraryDirectContract :
    Solidity.ContractDecl :=
  { name := "CheckedExternalLibraryDirect"
    items :=
      [ ContractItem.function
          { name := some "run"
            visibility := some Visibility.public_
            params := [{ name := some "x", ty := Ty.uint 256 }]
            returns := [{ name := some "out", ty := Ty.uint 256 }]
            body :=
              some
                (Solidity.Stmt.returnValues
                  (some
                    (Solidity.Expr.call
                      (Solidity.Expr.member
                        (Solidity.Expr.ident
                          "CheckedExternalMath")
                        "plusOne")
                      [Solidity.Arg.positional
                        (Solidity.Expr.ident "x")]))) } ] }

def checkedExternalLibraryUsingContract :
    Solidity.ContractDecl :=
  { name := "CheckedExternalLibraryUsing"
    items :=
      [ ContractItem.usingDecl
          { library := { segments := ["CheckedExternalMath"] }
            target := some (Ty.uint 256) }
      , ContractItem.function
          { name := some "run"
            visibility := some Visibility.public_
            params := [{ name := some "x", ty := Ty.uint 256 }]
            returns := [{ name := some "out", ty := Ty.uint 256 }]
            body :=
              some
                (Solidity.Stmt.returnValues
                  (some
                    (Solidity.Expr.call
                      (Solidity.Expr.member
                        (Solidity.Expr.ident "x") "plusOne")
                      []))) } ] }

def checkedExternalLibraryUnit : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          checkedExternalLibraryMath
      , Solidity.SourceItem.contract
          checkedExternalLibraryDirectContract
      , Solidity.SourceItem.contract
          checkedExternalLibraryUsingContract ] }

def checkedExternalLibraryDelegateCallMatches
    (contractName : Name) (input output : Word) :
    Except TypeError Bool := do
  let contract ← CheckedInput.contract checkedExternalLibraryUnit contractName
  let callResult ←
    optionToExcept "external library call result"
      (Executable.Examples.externalLibraryCallResult? input output)
  let result ←
    CheckedInput.callFunctionWithContextFailOpen 64
      (SolidCore.Solidity.Source.responderOfResults
                               [callResult]
      []) checkedExternalLibraryUnit
      contractName "run"
      { contract.core.context with
        contractAddresses := [("CheckedExternalMath", 0xbeef)] }
      SolidCore.Solidity.Source.State.empty
      [SolidCore.Solidity.Source.Value.word input]
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _
      [SolidCore.Solidity.Source.Value.word value] =>
      Except.ok (SolidCore.Solidity.Source.wordEq value output)
  | _ => Except.ok false

def checkedExternalLibraryDirectDelegateCallMatches :
    Except TypeError Bool :=
  checkedExternalLibraryDelegateCallMatches
    "CheckedExternalLibraryDirect" 41 42

def checkedExternalLibraryUsingDelegateCallMatches :
    Except TypeError Bool :=
  checkedExternalLibraryDelegateCallMatches
    "CheckedExternalLibraryUsing" 6 7

def checkedUsingModifierContract : Solidity.ContractDecl :=
  { name := "CheckedUsingModifier"
    items :=
      [ ContractItem.stateVar { name := "x", ty := Ty.uint 256 }
      , ContractItem.usingDecl
          { library := { segments := ["CheckedMath"] }
            target := some (Ty.uint 256) }
      , ContractItem.modifierDecl
          { name := "withBump"
            params := [{ name := some "start", ty := Ty.uint 256 }]
            body :=
              some
                (Solidity.Stmt.block
                  [ Solidity.Stmt.expr
                      (Solidity.Expr.assign
                        (Solidity.Expr.ident "x")
                        AssignOp.assign
                        (Solidity.Expr.call
                          (Solidity.Expr.member
                            (Solidity.Expr.ident "start")
                            "inc")
                          []))
                  , Solidity.Stmt.modifierPlaceholder ]) }
      , ContractItem.function
          { name := some "run"
            visibility := some Visibility.public_
            params := [{ name := some "seed", ty := Ty.uint 256 }]
            modifiers :=
              [ { target := { segments := ["withBump"] }
                  args :=
                    [ Solidity.Arg.positional
                        (Solidity.Expr.call
                          (Solidity.Expr.member
                            (Solidity.Expr.ident "seed")
                            "inc")
                          []) ] } ]
            body := some Solidity.Stmt.empty } ] }

def checkedUsingModifierUnit : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract checkedUsingMathLibrary
      , Solidity.SourceItem.contract
          checkedUsingModifierContract ] }

def checkedUsingModifierLibraryExpansionMatches :
    Except TypeError Bool :=
  checkedCallSlotMatches 64 checkedUsingModifierUnit
    "CheckedUsingModifier" "run"
    SolidCore.Solidity.Source.State.empty
    [SolidCore.Solidity.Source.Value.word 40] 0 42

def checkedCanonicalModifierContractsAccepted : Bool :=
  Result.isOk
    (TypecheckedInput.checkedSourceUnit
      Executable.Examples.modifierContract) &&
  Result.isOk
    (TypecheckedInput.checkedSourceUnit
      Executable.Examples.multiPlaceholderModifierContract) &&
  Result.isOk
    (TypecheckedInput.checkedSourceUnit
      Executable.Examples.namedArgsModifierContract) &&
  Result.isOk
    (TypecheckedInput.checkedSourceUnit
      Executable.Examples.returnsThroughModifierContract)

def checkedModifierSourceDisciplineAccepted : Bool :=
  Result.isOk (TypecheckedInput.checkedSourceUnit modifierInvocationSource) &&
    Result.isOk (TypecheckedInput.checkedSourceUnit returnThroughModifierSource)

def checkedModifierSourceDisciplineRejected : Bool :=
  Result.isError (TypecheckedInput.checkedSourceUnit unknownModifierSource) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit duplicateModifierParamNameSource)

def checkedModifierInvocationFixtureMatches :
    Except TypeError Bool :=
  checkedCallWordMatches 16 modifierInvocationSource
    "ModifierUser" "withModifier"
    SolidCore.Solidity.Source.State.empty [] 7

def checkedReturnThroughModifierFixtureMatches :
    Except TypeError Bool := do
  let result ←
    CheckedInput.callContract 32 returnThroughModifierSource
      "ReturnThroughModifier"
      (SolidCore.Solidity.Source.CallTarget.name "run")
      SolidCore.Solidity.Source.State.empty []
  match result with
  | SolidCore.Solidity.Source.CallResult.returned state
      [SolidCore.Solidity.Source.Value.word value] =>
      Except.ok
        (SolidCore.Solidity.Source.wordEq value 11 &&
          SolidCore.Solidity.Source.wordEq (state.loadSlot 0) 0)
  | _ => Except.ok false

def checkedCanonicalModifierCallMatches : Except TypeError Bool := do
  let result ←
    ContractDecl.checkedCall 32 Executable.Examples.modifierContract
      (SolidCore.Solidity.Source.CallTarget.name "run")
      SolidCore.Solidity.Source.State.empty []
  match result with
  | SolidCore.Solidity.Source.CallResult.returned state [] =>
      Except.ok (SolidCore.Solidity.Source.wordEq (state.loadSlot 0) 5)
  | _ => Except.ok false

def checkedMultiPlaceholderModifierMatches : Except TypeError Bool := do
  let result ←
    ContractDecl.checkedCall 64
      Executable.Examples.multiPlaceholderModifierContract
      (SolidCore.Solidity.Source.CallTarget.name "run")
      SolidCore.Solidity.Source.State.empty []
  match result with
  | SolidCore.Solidity.Source.CallResult.returned state [] =>
      Except.ok (SolidCore.Solidity.Source.wordEq (state.loadSlot 0) 112)
  | _ => Except.ok false

def checkedNamedArgsModifierMatches : Except TypeError Bool := do
  let result ←
    ContractDecl.checkedCall 32
      Executable.Examples.namedArgsModifierContract
      (SolidCore.Solidity.Source.CallTarget.name "run")
      SolidCore.Solidity.Source.State.empty []
  match result with
  | SolidCore.Solidity.Source.CallResult.returned state [] =>
      Except.ok (SolidCore.Solidity.Source.wordEq (state.loadSlot 0) 42)
  | _ => Except.ok false

def checkedReturnsThroughModifierMatches : Except TypeError Bool := do
  let result ←
    ContractDecl.checkedCall 32
      Executable.Examples.returnsThroughModifierContract
      (SolidCore.Solidity.Source.CallTarget.name "run")
      SolidCore.Solidity.Source.State.empty []
  match result with
  | SolidCore.Solidity.Source.CallResult.returned state
      [SolidCore.Solidity.Source.Value.word value] =>
      Except.ok
        (SolidCore.Solidity.Source.wordEq value 11 &&
          SolidCore.Solidity.Source.wordEq (state.loadSlot 0) 0)
  | _ => Except.ok false

def checkedModifierExternalTargetTy : Ty :=
  Ty.user { segments := ["CheckedModifierTarget"] }

def checkedModifierExternalTargetContract :
    Solidity.ContractDecl :=
  { name := "CheckedModifierTarget"
    kind := ContractKind.interface
    items :=
      [ ContractItem.function
          { name := some "ping"
            visibility := some Visibility.external_
            mutability := StateMutability.view
            returns := [{ name := some "out", ty := Ty.uint 256 }] }
      , ContractItem.function
          { name := some "get"
            visibility := some Visibility.external_
            mutability := StateMutability.view
            returns := [{ name := some "out", ty := Ty.uint 256 }] } ] }

def checkedTryCatchAroundModifierFunction :
    Solidity.FunctionDecl :=
  { Executable.Examples.tryCatchAroundModifierFunction with
    params :=
      [{ name := some "target", ty := checkedModifierExternalTargetTy }]
    modifiers :=
      [ { target := { segments := ["aroundTry"] }
          args := [Arg.positional (Expr.ident "target")] } ]
    visibility := some Visibility.public_ }

def checkedTryCatchAroundModifier :
    Solidity.ModifierDecl :=
  { Executable.Examples.tryCatchAroundModifier with
    params :=
      [{ name := some "target", ty := checkedModifierExternalTargetTy }] }

def checkedTryCatchAroundModifierContract :
    Solidity.ContractDecl :=
  { name := "CheckedTryCatchModifier"
    items :=
      [ ContractItem.stateVar { name := "x", ty := Ty.uint 256 }
      , ContractItem.stateVar { name := "mark", ty := Ty.uint 256 }
      , ContractItem.modifierDecl checkedTryCatchAroundModifier
      , ContractItem.function checkedTryCatchAroundModifierFunction ] }

def checkedTryCatchAroundModifierUnit :
    Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          checkedModifierExternalTargetContract
      , Solidity.SourceItem.contract
          checkedTryCatchAroundModifierContract ] }

def checkedTryCatchAroundModifierSourceAccepted : Bool :=
  Result.isOk
    (TypecheckedInput.checkedSourceUnit
      checkedTryCatchAroundModifierUnit)

def checkedTryCatchAroundModifierSuccessMatches :
    Except TypeError Bool := do
  let calldata ←
    optionToExcept "modifier try/catch calldata"
      (Executable.Examples.externalCalldata? "ping()" [] [])
  let output ←
    checkedAbiEncodeValues
      [SolidCore.Solidity.Source.Ty.uint256]
      [SolidCore.Solidity.Source.Value.word 42]
  let contract ←
    CheckedInput.contract checkedTryCatchAroundModifierUnit
      "CheckedTryCatchModifier"
  let result ←
    CheckedContract.callFunctionWithContextFailOpen 64
      (SolidCore.Solidity.Source.responderOfResults
          [ { kind := SolidCore.Solidity.Source.LowLevelCallKind.staticcall
              target := 0xbeef
              calldata := calldata
              success := true
              output := output } ]
      []) contract "run"
      { contract.core.context with
        accountCodes := [(0xbeef, [1])] }
      SolidCore.Solidity.Source.State.empty
      [SolidCore.Solidity.Source.Value.word 0xbeef]
  match result with
  | SolidCore.Solidity.Source.CallResult.returned state [] =>
      Except.ok
        (SolidCore.Solidity.Source.wordEq (state.loadSlot 0) 7 &&
          SolidCore.Solidity.Source.wordEq (state.loadSlot 1) 42)
  | _ => Except.ok false

def checkedTryCatchAroundModifierCatchMatches :
    Except TypeError Bool := do
  let calldata ←
    optionToExcept "modifier try/catch calldata"
      (Executable.Examples.externalCalldata? "ping()" [] [])
  let contract ←
    CheckedInput.contract checkedTryCatchAroundModifierUnit
      "CheckedTryCatchModifier"
  let result ←
    CheckedContract.callFunctionWithContextFailOpen 64
      (SolidCore.Solidity.Source.responderOfResults
          [ { kind := SolidCore.Solidity.Source.LowLevelCallKind.staticcall
              target := 0xbeef
              calldata := calldata
              success := false
              output := [0xca, 0xfe] } ]
      []) contract "run"
      { contract.core.context with
        accountCodes := [(0xbeef, [1])] }
      SolidCore.Solidity.Source.State.empty
      [SolidCore.Solidity.Source.Value.word 0xbeef]
  match result with
  | SolidCore.Solidity.Source.CallResult.returned state [] =>
      Except.ok
        (SolidCore.Solidity.Source.wordEq (state.loadSlot 0) 7 &&
          SolidCore.Solidity.Source.wordEq (state.loadSlot 1) 99)
  | _ => Except.ok false

def checkedDirectExternalCallModifier :
    Solidity.ModifierDecl :=
  { Executable.Examples.directExternalCallModifier with
    params :=
      [{ name := some "watched", ty := checkedModifierExternalTargetTy }] }

def checkedDirectExternalCallModifierFunction :
    Solidity.FunctionDecl :=
  { Executable.Examples.directExternalCallModifierFunction with
    params :=
      [{ name := some "target", ty := checkedModifierExternalTargetTy }]
    visibility := some Visibility.public_ }

def checkedDirectExternalCallModifierContract :
    Solidity.ContractDecl :=
  { name := "CheckedDirectExternalModifier"
    items :=
      [ ContractItem.stateVar { name := "x", ty := Ty.uint 256 }
      , ContractItem.stateVar { name := "mark", ty := Ty.uint 256 }
      , ContractItem.modifierDecl checkedDirectExternalCallModifier
      , ContractItem.function
          checkedDirectExternalCallModifierFunction ] }

def checkedDirectExternalCallModifierUnit :
    Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          checkedModifierExternalTargetContract
      , Solidity.SourceItem.contract
          checkedDirectExternalCallModifierContract ] }

def checkedDirectExternalCallModifierSourceAccepted : Bool :=
  Result.isOk
    (TypecheckedInput.checkedSourceUnit
      checkedDirectExternalCallModifierUnit)

def checkedDirectExternalCallModifierMatches :
    Except TypeError Bool := do
  let calldata ←
    optionToExcept "modifier external calldata"
      (Executable.Examples.externalCalldata? "get()" [] [])
  let output ←
    checkedAbiEncodeValues
      [SolidCore.Solidity.Source.Ty.uint256]
      [SolidCore.Solidity.Source.Value.word 77]
  let contract ←
    CheckedInput.contract checkedDirectExternalCallModifierUnit
      "CheckedDirectExternalModifier"
  let result ←
    CheckedContract.callFunctionWithContextFailOpen 64
      (SolidCore.Solidity.Source.responderOfResults
          [ { kind := SolidCore.Solidity.Source.LowLevelCallKind.staticcall
              target := 0xbeef
              calldata := calldata
              success := true
              output := output } ]
      []) contract "run"
      { contract.core.context with
        accountCodes := [(0xbeef, [1])] }
      SolidCore.Solidity.Source.State.empty
      [SolidCore.Solidity.Source.Value.word 0xbeef]
  match result with
  | SolidCore.Solidity.Source.CallResult.returned state [] =>
      Except.ok
        (SolidCore.Solidity.Source.wordEq (state.loadSlot 0) 7 &&
          SolidCore.Solidity.Source.wordEq (state.loadSlot 1) 77)
  | _ => Except.ok false

def checkedUsingConstructorContract :
    Solidity.ContractDecl :=
  { name := "CheckedUsingConstructor"
    items :=
      [ ContractItem.stateVar { name := "x", ty := Ty.uint 256 }
      , ContractItem.usingDecl
          { library := { segments := ["CheckedMath"] }
            target := some (Ty.uint 256) }
      , ContractItem.function
          { kind := FunctionKind.constructor
            params := [{ name := some "seed", ty := Ty.uint 256 }]
            body :=
              some
                (Solidity.Stmt.expr
                  (Solidity.Expr.assign
                    (Solidity.Expr.ident "x")
                    AssignOp.assign
                    (Solidity.Expr.call
                      (Solidity.Expr.member
                        (Solidity.Expr.ident "seed") "inc")
                      []))) } ] }

def checkedUsingConstructorUnit : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract checkedUsingMathLibrary
      , Solidity.SourceItem.contract
          checkedUsingConstructorContract ] }

def checkedUsingConstructorMatches : Except TypeError Bool :=
  checkedConstructSlotMatches 32 checkedUsingConstructorUnit
    "CheckedUsingConstructor"
    SolidCore.Solidity.Source.State.empty
    [SolidCore.Solidity.Source.Value.word 41] 0 42

def checkedUsingUnknownLibraryRejected : Bool :=
  Result.isError (CheckedInput.program usingUnknownLibrarySource)

def checkedUsingNonLibraryRejected : Bool :=
  Result.isError (CheckedInput.program usingNonLibrarySource)

def checkedBadExplicitUsingFreeFunctionRejected : Bool :=
  Result.isError (CheckedInput.program badExplicitUsingFreeFunctionSource)

def checkedBadExplicitUsingFunctionRejected : Bool :=
  Result.isError (CheckedInput.program badExplicitUsingFunctionSource)

def checkedBadUsingLibraryReceiverRejected : Bool :=
  Result.isError (CheckedInput.program badUsingLibraryReceiverSource)

def checkedContractUsingOperatorRejected : Bool :=
  Result.isError (CheckedInput.program contractUsingOperatorSource)

def checkedNonPureUsingOperatorRejected : Bool :=
  Result.isError (CheckedInput.program nonPureUsingOperatorSource)

def checkedContractGlobalUsingRejected : Bool :=
  Result.isError (CheckedInput.program contractGlobalUsingSource)

def checkedGlobalUsingNonUserValueRejected : Bool :=
  Result.isError (CheckedInput.program globalUsingNonUserValueSource)

def checkedInheritedBaseFunctionDispatchMatches :
    Except TypeError Bool :=
  checkedCallWordMatches 32 inheritanceSource
    "Derived" "f"
    SolidCore.Solidity.Source.State.empty [] 7

def checkedVirtualOverrideDispatchMatches :
    Except TypeError Bool :=
  checkedCallWordMatches 32 virtualOverrideSource
    "VirtualDerived" "value"
    SolidCore.Solidity.Source.State.empty [] 2

def checkedSuperValueCallMatches : Except TypeError Bool :=
  checkedCallWordMatches 32 superCallSource
    "SuperTypeDerived" "value"
    SolidCore.Solidity.Source.State.empty [] 3

def checkedExplicitBaseCallMatches : Except TypeError Bool :=
  checkedCallWordMatches 32 explicitBaseCallSource
    "ExplicitBaseTypeDerived" "directBase"
    SolidCore.Solidity.Source.State.empty [] 11

def checkedCanonicalSuperBaseSourceUnitsAccepted : Bool :=
  Result.isOk
    (TypecheckedInput.checkedSourceUnit
      Executable.Examples.superSourceUnit) &&
  Result.isOk
    (TypecheckedInput.checkedSourceUnit
      Executable.Examples.explicitBaseSourceUnit) &&
  Result.isOk
    (TypecheckedInput.checkedSourceUnit
      Executable.Examples.superChainSourceUnit)

def checkedCanonicalSuperValueCallMatches : Except TypeError Bool :=
  checkedCallWordMatches 32 Executable.Examples.superSourceUnit
    "SuperDerived" "value"
    SolidCore.Solidity.Source.State.empty [] 3

def checkedCanonicalSuperStorageCallMatches :
    Except TypeError Bool :=
  checkedCallSlotMatches 32 Executable.Examples.superSourceUnit
    "SuperDerived" "setViaSuper"
    SolidCore.Solidity.Source.State.empty [] 0 5

def checkedExplicitBaseDirectLeftMatches :
    Except TypeError Bool :=
  checkedCallWordMatches 32 Executable.Examples.explicitBaseSourceUnit
    "ExplicitBaseFinal" "directLeft"
    SolidCore.Solidity.Source.State.empty [] 11

def checkedExplicitBaseDirectRightMatches :
    Except TypeError Bool :=
  checkedCallWordMatches 32 Executable.Examples.explicitBaseSourceUnit
    "ExplicitBaseFinal" "directRight"
    SolidCore.Solidity.Source.State.empty [] 22

def checkedExplicitBaseVirtualDispatchMatches :
    Except TypeError Bool :=
  checkedCallWordMatches 32 Executable.Examples.explicitBaseSourceUnit
    "ExplicitBaseFinal" "virtualValue"
    SolidCore.Solidity.Source.State.empty [] 22

def checkedSuperChainValueMatches : Except TypeError Bool :=
  checkedCallWordMatches 64 Executable.Examples.superChainSourceUnit
    "SuperChainTop" "value"
    SolidCore.Solidity.Source.State.empty [] 77

def checkedC3DispatchSourceUnitAccepted : Bool :=
  Result.isOk (CheckedInput.program Executable.Examples.c3SourceUnit)

def checkedC3DispatchOrderMatches : Except TypeError Bool := do
  let program ← CheckedInput.program Executable.Examples.c3SourceUnit
  let final ←
    optionToExcept "C3 final source contract"
      (CheckedProgram.findSourceContract? program "C3Final")
  let order ←
    optionToExcept "C3 dispatch order"
      (Solidity.Executable.ContractDecl.dispatchOrder?
        (CheckedProgram.contracts program) final)
  Except.ok
    (order.map Solidity.ContractDecl.name ==
      ["C3Final", "C3Right", "C3Left", "C3Root"])

def checkedInheritedStateReadMatches : Except TypeError Bool := do
  let deployed ←
    CheckedInput.constructContract 32 inheritedStateReadSource
      "InheritedStateDerived" SolidCore.Solidity.Source.State.empty []
  match deployed with
  | SolidCore.Solidity.Source.CallResult.returned state _ =>
      checkedCallWordMatches 32 inheritedStateReadSource
        "InheritedStateDerived" "read" state [] 1
  | _ => Except.ok false

def checkedSuperStorageBaseContract :
    Solidity.ContractDecl :=
  { name := "CheckedSuperStorageBase"
    items :=
      [ ContractItem.stateVar { name := "x", ty := Ty.uint 256 }
      , ContractItem.function
          { name := some "setX"
            visibility := some Visibility.public_
            body :=
              some
                (Solidity.Stmt.expr
                  (Solidity.Expr.assign
                    (Solidity.Expr.ident "x")
                    AssignOp.assign
                    (Solidity.Expr.literal
                      (Solidity.Literal.number "5")))) } ] }

def checkedSuperStorageDerivedContract :
    Solidity.ContractDecl :=
  { name := "CheckedSuperStorageDerived"
    bases := [{ base := { segments := ["CheckedSuperStorageBase"] } }]
    items :=
      [ ContractItem.function
          { name := some "setViaSuper"
            visibility := some Visibility.public_
            body :=
              some
                (Solidity.Stmt.expr
                  (Solidity.Expr.call
                    (Solidity.Expr.member
                      (Solidity.Expr.ident "super") "setX")
                    [])) } ] }

def checkedSuperStorageSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          checkedSuperStorageBaseContract
      , Solidity.SourceItem.contract
          checkedSuperStorageDerivedContract ] }

def checkedSuperStorageCallMatches : Except TypeError Bool :=
  checkedCallSlotMatches 32 checkedSuperStorageSource
    "CheckedSuperStorageDerived" "setViaSuper"
    SolidCore.Solidity.Source.State.empty [] 0 5

def checkedStorageLayoutFieldsMatch : Except TypeError Bool := do
  let contract ←
    CheckedInput.contract storageLayoutAcceptedSource "StorageLayoutTop"
  match contract.core.storageFields with
  | [x, y] =>
      Except.ok
        (x.name == "x" &&
          SolidCore.Solidity.Source.wordEq x.slot 5 &&
          !x.transient &&
          y.name == "y" &&
          SolidCore.Solidity.Source.wordEq y.slot 6 &&
          !y.transient)
  | _ => Except.ok false

def checkedStorageLayoutInitMatches : Except TypeError Bool := do
  let result ←
    CheckedInput.constructContract 32 storageLayoutAcceptedSource
      "StorageLayoutTop" SolidCore.Solidity.Source.State.empty []
  match result with
  | SolidCore.Solidity.Source.CallResult.returned state _ =>
      Except.ok
        (SolidCore.Solidity.Source.wordEq (state.loadSlot 0) 0 &&
          SolidCore.Solidity.Source.wordEq (state.loadSlot 5) 1 &&
          SolidCore.Solidity.Source.wordEq (state.loadSlot 6) 2)
  | _ => Except.ok false

def checkedConstantStorageLayoutMatches : Except TypeError Bool := do
  let result ←
    CheckedInput.constructContract 32 constantStorageLayoutSource
      "ConstantStorageLayout" SolidCore.Solidity.Source.State.empty []
  match result with
  | SolidCore.Solidity.Source.CallResult.returned state _ =>
      Except.ok
        (SolidCore.Solidity.Source.wordEq (state.loadSlot 0) 0 &&
          SolidCore.Solidity.Source.wordEq (state.loadSlot 9) 1)
  | _ => Except.ok false

def checkedFileConstantContractMatches : Except TypeError Bool :=
  checkedCallWordMatches 32
    Executable.Examples.fileConstantContractUnit
    "UsesFileConstant" "run"
    SolidCore.Solidity.Source.State.empty [] 42

def checkedFileConstantFreeFunctionMatches :
    Except TypeError Bool := do
  let fromFree ←
    checkedCallWordMatches 32
      Executable.Examples.fileConstantShadowingUnit
      "FileConstantShadowing" "fromFree"
      SolidCore.Solidity.Source.State.empty [] 42
  let fromContract ←
    checkedCallWordMatches 32
      Executable.Examples.fileConstantShadowingUnit
      "FileConstantShadowing" "fromContract"
      SolidCore.Solidity.Source.State.empty [] 100
  Except.ok (fromFree && fromContract)

def checkedFileConstantConstructorMatches : Except TypeError Bool :=
  checkedConstructSlotMatches 32
    Executable.Examples.fileConstantConstructorUnit
    "FileConstantConstructor"
    SolidCore.Solidity.Source.State.empty [] 0 41

def checkedConstantReadMatches : Except TypeError Bool := do
  let result ←
    ContractDecl.checkedCall 32
      Executable.Examples.constantReadContract
      (SolidCore.Solidity.Source.CallTarget.name "run")
      SolidCore.Solidity.Source.State.empty []
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _
      [SolidCore.Solidity.Source.Value.word value] =>
      Except.ok (SolidCore.Solidity.Source.wordEq value 42)
  | _ => Except.ok false

def checkedConstantPublicGetterMatches :
    Except TypeError Bool := do
  let result ←
    ContractDecl.checkedCall 32
      Executable.Examples.constantReadContract
      (SolidCore.Solidity.Source.CallTarget.name "LIMIT")
      SolidCore.Solidity.Source.State.empty []
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _
      [SolidCore.Solidity.Source.Value.word value] =>
      Except.ok (SolidCore.Solidity.Source.wordEq value 41)
  | _ => Except.ok false

def checkedConstantStorageFieldsSkipConstantsAndImmutables :
    Except TypeError Bool := do
  let contract ←
    ContractDecl.checkedContract
      Executable.Examples.constantLayoutContract
  match contract.core.storageFields, contract.core.immutableFields with
  | [a, b], [i] =>
      Except.ok
        (a.name == "a" &&
          SolidCore.Solidity.Source.wordEq a.slot 0 &&
          b.name == "b" &&
          SolidCore.Solidity.Source.wordEq b.slot 1 &&
          i.name == "I")
  | _, _ => Except.ok false

def checkedConstantInitializerMatches : Except TypeError Bool := do
  let result ←
    ContractDecl.checkedConstruct 32
      Executable.Examples.constantInitializerContract
      SolidCore.Solidity.Source.State.empty []
  match result with
  | SolidCore.Solidity.Source.CallResult.returned state _ =>
      Except.ok (SolidCore.Solidity.Source.wordEq (state.loadSlot 0) 6)
  | _ => Except.ok false

def checkedImmutableInlineConstantPureReadMatches :
    Except TypeError Bool := do
  let deployed ←
    CheckedInput.constructContract 32 immutableInlineConstantPureReadSource
      "ImmutableInlineConstantPureRead"
      SolidCore.Solidity.Source.State.empty []
  match deployed with
  | SolidCore.Solidity.Source.CallResult.returned state _ =>
      checkedCallWordMatches 32 immutableInlineConstantPureReadSource
        "ImmutableInlineConstantPureRead" "f" state [] 1
  | _ => Except.ok false

def checkedConstantImmutableTypecheckerAccepts : Bool :=
  Result.isOk (CheckedInput.program constantWithInitSource) &&
    Result.isOk (CheckedInput.program bytesConstantSource) &&
    Result.isOk (CheckedInput.program fileConstantInContractSource) &&
    Result.isOk (CheckedInput.program stateConstantPureReadSource) &&
    Result.isOk (CheckedInput.program immutableAssignedInConstructorSource) &&
    Result.isOk (CheckedInput.program immutableInlineConstantPureReadSource)

def checkedConstantImmutableTypecheckerRejects : Bool :=
  Result.isError (CheckedInput.program constantWithoutInitSource) &&
    Result.isError (CheckedInput.program badArrayConstantSource) &&
    Result.isError (CheckedInput.program badFreeMutableSource) &&
    Result.isError (CheckedInput.program constantFromStateSource) &&
    Result.isError (CheckedInput.program assignConstantSource) &&
    Result.isError (CheckedInput.program badFileConstantVisibilitySource) &&
    Result.isError (CheckedInput.program badFileConstantOverrideSource) &&
    Result.isError (CheckedInput.program badImmutableExternalFunctionSource) &&
    Result.isError (CheckedInput.program badImmutableStringSource) &&
    Result.isError (CheckedInput.program immutableAssignedInFunctionSource) &&
    Result.isError (CheckedInput.program immutableRuntimePureReadSource)

def checkedErc7201StorageLayoutMatches : Except TypeError Bool := do
  let result ←
    CheckedInput.constructContract 32 erc7201StorageLayoutSource
      "Erc7201StorageLayout" SolidCore.Solidity.Source.State.empty []
  let slot :=
    SolidCore.Solidity.Source.erc7201Slot
      (Executable.stringUtf8Bytes "example.main")
  match result with
  | SolidCore.Solidity.Source.CallResult.returned state _ =>
      Except.ok
        (SolidCore.Solidity.Source.wordEq (state.loadSlot slot) 1)
  | _ => Except.ok false

def checkedErc7201MinusOneStorageLayoutMatches :
    Except TypeError Bool := do
  let result ←
    CheckedInput.constructContract 32 erc7201MinusOneStorageLayoutSource
      "Erc7201MinusOneStorageLayout"
      SolidCore.Solidity.Source.State.empty []
  let slot :=
    SolidCore.Solidity.Shared.subWord
      (SolidCore.Solidity.Source.erc7201Slot
        (Executable.stringUtf8Bytes "example.main"))
      1
  match result with
  | SolidCore.Solidity.Source.CallResult.returned state _ =>
      Except.ok
        (SolidCore.Solidity.Source.wordEq (state.loadSlot slot) 1)
  | _ => Except.ok false

def checkedUnknownBaseRejected : Bool :=
  Result.isError (CheckedInput.program unknownBaseSource)

def checkedMissingOverrideRejected : Bool :=
  Result.isError (CheckedInput.program missingOverrideSource)

def checkedNonvirtualOverrideRejected : Bool :=
  Result.isError (CheckedInput.program nonvirtualOverrideSource)

def checkedBadSuperCallRejected : Bool :=
  Result.isError (CheckedInput.program badSuperCallSource)

def checkedSuperCallOptionsRejected : Bool :=
  Result.isError (CheckedInput.program superCallOptionsSource)

def checkedBadExplicitBaseCallRejected : Bool :=
  Result.isError (CheckedInput.program badExplicitBaseCallSource)

def checkedC3BadRejected : Bool :=
  Result.isError (CheckedInput.program c3BadSource)

def checkedInheritedStorageLayoutRejected : Bool :=
  Result.isError (CheckedInput.program inheritedStorageLayoutSource)

def checkedBadErc7201StorageLayoutRejected : Bool :=
  Result.isError (CheckedInput.program badErc7201StorageLayoutSource)

def checkedBadErc7201ConcatStorageLayoutRejected : Bool :=
  Result.isError
    (CheckedInput.program badErc7201ConcatStorageLayoutSource)

def checkedBadKeccakStorageLayoutRejected : Bool :=
  Result.isError (CheckedInput.program badKeccakStorageLayoutSource)

def checkedStorageLayoutSourceDisciplineAccepted : Bool :=
  Result.isOk (CheckedInput.program storageLayoutAcceptedSource) &&
    Result.isOk (CheckedInput.program constantStorageLayoutSource) &&
    Result.isOk (CheckedInput.program erc7201StorageLayoutSource) &&
    Result.isOk (CheckedInput.program erc7201MinusOneStorageLayoutSource)

def checkedStorageLayoutSourceDisciplineRejected : Bool :=
  Result.isError (CheckedInput.program unknownConstantStorageLayoutSource) &&
    Result.isError (CheckedInput.program abstractStorageLayoutSource) &&
    Result.isError (CheckedInput.program mutableStorageLayoutBaseSource) &&
    checkedInheritedStorageLayoutRejected &&
    checkedBadErc7201StorageLayoutRejected &&
    checkedBadErc7201ConcatStorageLayoutRejected &&
    checkedBadKeccakStorageLayoutRejected

def checkedPayableConstructorValueMatches :
    Except TypeError Bool := do
  let result ←
    ContractDecl.checkedConstructFrom 16
      Executable.Examples.payableConstructorValueContract
      SolidCore.Solidity.Source.State.empty
      0xabcd 13 []
  match result with
  | SolidCore.Solidity.Source.CallResult.returned state [] =>
      Except.ok
        (SolidCore.Solidity.Source.wordEq (state.loadSlot 0) 13)
  | _ => Except.ok false

def checkedNonpayableConstructorValueContract :
    Solidity.ContractDecl :=
  { name := "CheckedNonpayableCtor"
    items :=
      [ Solidity.ContractItem.stateVar
          { name := "x", ty := Ty.uint 256 }
      , Solidity.ContractItem.function
          { kind := FunctionKind.constructor
            mutability := StateMutability.nonpayable
            body :=
              some
                (Solidity.Stmt.expr
                  (Solidity.Expr.assign
                    (Solidity.Expr.ident "x")
                    AssignOp.assign
                    (Solidity.Expr.literal
                      (Solidity.Literal.number "17")))) } ] }

def checkedNonpayableConstructorRejectsValueMatches :
    Except TypeError Bool := do
  let result ←
    ContractDecl.checkedConstructFrom 16
      checkedNonpayableConstructorValueContract
      SolidCore.Solidity.Source.State.empty
      0xabcd 13 []
  match result with
  | SolidCore.Solidity.Source.CallResult.reverted state
      SolidCore.Solidity.Source.RevertData.empty =>
      Except.ok
        (SolidCore.Solidity.Source.wordEq (state.loadSlot 0) 0)
  | _ => Except.ok false

def checkedPublicConstructorVisibilityRuns :
    Except TypeError Bool :=
  checkedConstructSlotMatches 32 publicConstructorVisibilitySource
    "PublicConstructorVisibility"
    SolidCore.Solidity.Source.State.empty
    [SolidCore.Solidity.Source.Value.word 44] 0 44

def checkedConstructorInitializesStateMatches :
    Except TypeError Bool := do
  let result ←
    ContractDecl.checkedConstruct 16
      Executable.Examples.constructorContract
      SolidCore.Solidity.Source.State.empty
      [SolidCore.Solidity.Source.Value.word 42]
  match result with
  | SolidCore.Solidity.Source.CallResult.returned state [] =>
      Except.ok
        (SolidCore.Solidity.Source.wordEq (state.loadSlot 0) 1 &&
          SolidCore.Solidity.Source.wordEq (state.loadSlot 1) 42)
  | _ => Except.ok false

def checkedRevertingConstructorRollsBackMatches :
    Except TypeError Bool := do
  let result ←
    ContractDecl.checkedConstruct 16
      Executable.Examples.revertingConstructorContract
      SolidCore.Solidity.Source.State.empty []
  match result with
  | SolidCore.Solidity.Source.CallResult.reverted state
      SolidCore.Solidity.Source.RevertData.empty =>
      Except.ok
        (SolidCore.Solidity.Source.wordEq (state.loadSlot 0) 0)
  | _ => Except.ok false

def checkedImmutableConstructorContract :
    Solidity.ContractDecl :=
  { name := "CheckedImmutableConstructor"
    items :=
      [ Solidity.ContractItem.stateVar
          { name := "SEED"
            ty := Ty.uint 256
            visibility := some Visibility.public_
            mutability := VarMutability.immutable
            init :=
              some
                (Solidity.Expr.literal
                  (Solidity.Literal.number "3")) }
      , Solidity.ContractItem.stateVar
          { name := "x"
            ty := Ty.uint 256
            visibility := some Visibility.public_
            mutability := VarMutability.immutable }
      , Solidity.ContractItem.function
          { kind := FunctionKind.constructor
            params := [{ name := some "value", ty := Ty.uint 256 }]
            body :=
              some
                (Solidity.Stmt.expr
                  (Solidity.Expr.assign
                    (Solidity.Expr.ident "x")
                    AssignOp.assign
                    (Solidity.Expr.binary BinaryOp.add
                      (Solidity.Expr.ident "value")
                      (Solidity.Expr.ident "SEED")))) }
      , Solidity.ContractItem.function
          { name := some "sum"
            visibility := some Visibility.public_
            returns := [{ name := some "out", ty := Ty.uint 256 }]
            mutability := StateMutability.view
            body :=
              some
                (Solidity.Stmt.returnValues
                  (some
                    (Solidity.Expr.binary BinaryOp.add
                      (Solidity.Expr.ident "x")
                      (Solidity.Expr.ident "SEED")))) } ] }

def checkedImmutableConstructorMatches :
    Except TypeError Bool := do
  let deployed ←
    ContractDecl.checkedConstruct 32 checkedImmutableConstructorContract
      SolidCore.Solidity.Source.State.empty
      [SolidCore.Solidity.Source.Value.word 9]
  match deployed with
  | SolidCore.Solidity.Source.CallResult.returned state _ => do
      let result ←
        ContractDecl.checkedCall 32 checkedImmutableConstructorContract
          (SolidCore.Solidity.Source.CallTarget.name "sum") state []
      match result with
      | SolidCore.Solidity.Source.CallResult.returned _
          [SolidCore.Solidity.Source.Value.word value] =>
          Except.ok (SolidCore.Solidity.Source.wordEq value 15)
      | _ => Except.ok false
  | _ => Except.ok false

def checkedImmutablePublicGetterMatches :
    Except TypeError Bool := do
  let deployed ←
    ContractDecl.checkedConstruct 32 checkedImmutableConstructorContract
      SolidCore.Solidity.Source.State.empty
      [SolidCore.Solidity.Source.Value.word 9]
  match deployed with
  | SolidCore.Solidity.Source.CallResult.returned state _ => do
      let result ←
        ContractDecl.checkedCall 32 checkedImmutableConstructorContract
          (SolidCore.Solidity.Source.CallTarget.name "x") state []
      match result with
      | SolidCore.Solidity.Source.CallResult.returned _
          [SolidCore.Solidity.Source.Value.word value] =>
          Except.ok (SolidCore.Solidity.Source.wordEq value 12)
      | _ => Except.ok false
  | _ => Except.ok false

def checkedImmutableRuntimeWriteContract :
    Solidity.ContractDecl :=
  { checkedImmutableConstructorContract with
    name := "CheckedImmutableRuntimeWrite"
    items :=
      checkedImmutableConstructorContract.items ++
        [ Solidity.ContractItem.function
            { name := some "mutate"
              visibility := some Visibility.public_
              body :=
                some
                  (Solidity.Stmt.expr
                    (Solidity.Expr.assign
                      (Solidity.Expr.ident "x")
                      AssignOp.assign
                      (Solidity.Expr.literal
                        (Solidity.Literal.number "1")))) } ] }

def checkedImmutableRuntimeWriteRejectedByTypechecker : Bool :=
  Result.isError
    (ContractDecl.checkedContract checkedImmutableRuntimeWriteContract)

def checkedConstructorInternalCallContract :
    Solidity.ContractDecl :=
  { name := "CheckedCtorInternalCall"
    items :=
      [ Solidity.ContractItem.stateVar
          { name := "x", ty := Ty.uint 256 }
      , Solidity.ContractItem.function
          { name := some "double"
            visibility := some Visibility.internal_
            params := [{ name := some "value", ty := Ty.uint 256 }]
            returns := [{ name := some "out", ty := Ty.uint 256 }]
            body :=
              some
                (Solidity.Stmt.returnValues
                  (some
                    (Solidity.Expr.binary BinaryOp.mul
                      (Solidity.Expr.ident "value")
                      (Solidity.Expr.literal
                        (Solidity.Literal.number "2"))))) }
      , Solidity.ContractItem.function
          { kind := FunctionKind.constructor
            params := [{ name := some "seed", ty := Ty.uint 256 }]
            body :=
              some
                (Solidity.Stmt.expr
                  (Solidity.Expr.assign
                    (Solidity.Expr.ident "x")
                    AssignOp.assign
                    (Solidity.Expr.call
                      (Solidity.Expr.ident "double")
                      [Solidity.Arg.positional
                        (Solidity.Expr.ident "seed")]))) } ] }

def checkedConstructorInternalCallMatches :
    Except TypeError Bool := do
  let result ←
    ContractDecl.checkedConstruct 32
      checkedConstructorInternalCallContract
      SolidCore.Solidity.Source.State.empty
      [SolidCore.Solidity.Source.Value.word 21]
  match result with
  | SolidCore.Solidity.Source.CallResult.returned state _ =>
      Except.ok
        (SolidCore.Solidity.Source.wordEq (state.loadSlot 0) 42)
  | _ => Except.ok false

def checkedConstructorFreeFunctionMatches :
    Except TypeError Bool := do
  let result ←
    SourceUnit.checkedConstructContract 32
      Executable.Examples.constructorFreeFunctionUnit
      "CtorFreeFunction"
      SolidCore.Solidity.Source.State.empty
      [SolidCore.Solidity.Source.Value.word 21]
  match result with
  | SolidCore.Solidity.Source.CallResult.returned state _ =>
      Except.ok
        (SolidCore.Solidity.Source.wordEq (state.loadSlot 0) 42)
  | _ => Except.ok false

def checkedInheritedBaseConstructorNamedArgMatches :
    Except TypeError Bool := do
  let result ←
    SourceUnit.checkedConstructContract 32
      Executable.Examples.baseConstructorNamedArgUnit
      "NamedDerivedArg"
      SolidCore.Solidity.Source.State.empty []
  match result with
  | SolidCore.Solidity.Source.CallResult.returned state [] =>
      Except.ok
        (SolidCore.Solidity.Source.wordEq (state.loadSlot 0) 4 &&
          SolidCore.Solidity.Source.wordEq (state.loadSlot 1) 9)
  | _ => Except.ok false

def checkedInheritedBaseConstructorPositionalArgMatches :
    Except TypeError Bool := do
  let result ←
    SourceUnit.checkedConstructContract 32
      Executable.Examples.baseConstructorArgUnit
      "DerivedArg"
      SolidCore.Solidity.Source.State.empty
      [SolidCore.Solidity.Source.Value.word 34]
  match result with
  | SolidCore.Solidity.Source.CallResult.returned state _ =>
      Except.ok
        (SolidCore.Solidity.Source.wordEq (state.loadSlot 0) 12 &&
          SolidCore.Solidity.Source.wordEq (state.loadSlot 1) 34)
  | _ => Except.ok false

def checkedInheritedBaseConstructorDuplicateNamedArgRejected : Bool :=
  Result.isError
    (CheckedInput.program
      Executable.Examples.baseConstructorDuplicateNamedArgUnit)

def checkedInheritedBaseConstructorModifierArgMatches :
    Except TypeError Bool := do
  let result ←
    SourceUnit.checkedConstructContract 32
      Executable.Examples.baseConstructorModifierArgUnit
      "DerivedModifierArg"
      SolidCore.Solidity.Source.State.empty
      [SolidCore.Solidity.Source.Value.word 6]
  match result with
  | SolidCore.Solidity.Source.CallResult.returned state _ =>
      Except.ok
        (SolidCore.Solidity.Source.wordEq (state.loadSlot 0) 36 &&
          SolidCore.Solidity.Source.wordEq (state.loadSlot 1) 7)
  | _ => Except.ok false

def checkedInheritedBaseConstructorDeferredArgMatches :
    Except TypeError Bool := do
  let result ←
    SourceUnit.checkedConstructContract 32
      Executable.Examples.baseConstructorDeferredArgUnit
      "DeferredArgDerived"
      SolidCore.Solidity.Source.State.empty
      [SolidCore.Solidity.Source.Value.word 6]
  match result with
  | SolidCore.Solidity.Source.CallResult.returned state _ =>
      Except.ok
        (SolidCore.Solidity.Source.wordEq (state.loadSlot 0) 16 &&
          SolidCore.Solidity.Source.wordEq (state.loadSlot 1) 6)
  | _ => Except.ok false

def checkedBaseConstructorObligationSourcesAccepted : Bool :=
  Result.isOk (CheckedInput.program baseConstructorArgsSource) &&
    Result.isOk (CheckedInput.program namedBaseConstructorArgsSource) &&
    Result.isOk (CheckedInput.program baseConstructorFileConstantSource) &&
    Result.isOk (CheckedInput.program baseConstructorModifierArgsSource) &&
    Result.isOk
      (CheckedInput.program abstractMissingBaseConstructorArgsSource) &&
    Result.isOk
      (CheckedInput.program indirectBaseConstructorModifierArgsSource) &&
    Result.isOk
      (CheckedInput.program
        Executable.Examples.baseConstructorDeferredArgUnit)

def checkedBaseConstructorObligationSourcesRejected : Bool :=
  Result.isError
      (CheckedInput.program duplicateNamedBaseConstructorArgsSource) &&
    Result.isError (CheckedInput.program baseConstructorStateArgSource) &&
    Result.isError (CheckedInput.program badBaseConstructorArgsSource) &&
    Result.isError (CheckedInput.program duplicateBaseConstructorArgsSource) &&
    Result.isError
      (CheckedInput.program concreteMissingBaseConstructorArgsSource) &&
    Result.isError
      (CheckedInput.program nonconstructorBaseConstructorInvocationSource) &&
    Result.isError
      (CheckedInput.program
        Executable.Examples.baseConstructorDuplicateNamedArgUnit)

def checkedEventErrorAbiRollbackContractsAccepted : Bool :=
  Result.isOk
      (TypecheckedInput.checkedSourceUnit
        Executable.Examples.requireCustomErrorContract) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit
        Executable.Examples.eventAbiContract) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit
        Executable.Examples.anonymousEventAbiContract) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit
        Executable.Examples.dynamicEventAbiContract) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit
        Executable.Examples.storageRollbackContract)

def checkedRequireCustomErrorAbiMatches :
    Except TypeError Bool := do
  let contract ←
    ContractDecl.checkedContract
      Executable.Examples.requireCustomErrorContract
  let calldata ←
    CheckedContract.functionCalldata contract "check"
      [SolidCore.Solidity.Source.Value.word 4]
  let result ←
    CheckedContract.callCalldata 16 contract
      SolidCore.Solidity.Source.State.empty calldata
  let encoded ←
    optionToExcept "custom error ABI argument"
      (SolidCore.Solidity.Source.ABI.encodeValues?
        [SolidCore.Solidity.Source.Ty.uint256]
        [SolidCore.Solidity.Source.Value.word 4])
  let expected :=
    SolidCore.Solidity.Source.ABI.encodeSelector
      (SolidCore.Solidity.Source.ABI.selectorFromSignature
        "TooSmall(uint256)") ++ encoded
  Except.ok (!result.success && result.output == expected)

def checkedEventAbiTopicsMatchExpected :
    Except TypeError Bool := do
  let expected ←
    optionToExcept "event ABI topics"
      Executable.Examples.eventAbiExpectedTopics
  let result ←
    CheckedInput.ownCall 16 Executable.Examples.eventAbiContract
      (SolidCore.Solidity.Source.CallTarget.name "emitIt")
      SolidCore.Solidity.Source.State.empty []
  match result with
  | SolidCore.Solidity.Source.CallResult.returned state _ =>
      match state.events with
      | [event] => Except.ok (event.topics == expected)
      | _ => Except.ok false
  | _ => Except.ok false

def checkedEventAbiDataBytesMatchExpected :
    Except TypeError Bool := do
  let result ←
    CheckedInput.ownCall 16 Executable.Examples.eventAbiContract
      (SolidCore.Solidity.Source.CallTarget.name "emitIt")
      SolidCore.Solidity.Source.State.empty []
  match result with
  | SolidCore.Solidity.Source.CallResult.returned state _ =>
      match state.events with
      | [event] =>
          Except.ok
            (event.dataBytes ==
              Executable.Examples.eventAbiExpectedDataBytes)
      | _ => Except.ok false
  | _ => Except.ok false

def checkedAnonymousEventAbiTopicsMatchExpected :
    Except TypeError Bool := do
  let result ←
    CheckedInput.ownCall 16
      Executable.Examples.anonymousEventAbiContract
      (SolidCore.Solidity.Source.CallTarget.name "emitIt")
      SolidCore.Solidity.Source.State.empty []
  match result with
  | SolidCore.Solidity.Source.CallResult.returned state _ =>
      match state.events with
      | [event] => Except.ok (event.topics == [1, 2, 3, 4])
      | _ => Except.ok false
  | _ => Except.ok false

def checkedAnonymousEventAbiDataBytesEmpty :
    Except TypeError Bool := do
  let result ←
    CheckedInput.ownCall 16
      Executable.Examples.anonymousEventAbiContract
      (SolidCore.Solidity.Source.CallTarget.name "emitIt")
      SolidCore.Solidity.Source.State.empty []
  match result with
  | SolidCore.Solidity.Source.CallResult.returned state _ =>
      match state.events with
      | [event] => Except.ok event.dataBytes.isEmpty
      | _ => Except.ok false
  | _ => Except.ok false

def checkedRevertedEventRollbackDropsLog :
    Except TypeError Bool := do
  let result ←
    CheckedInput.ownCall 16 Executable.Examples.eventAbiContract
      (SolidCore.Solidity.Source.CallTarget.name "emitThenRevert")
      SolidCore.Solidity.Source.State.empty []
  match result with
  | SolidCore.Solidity.Source.CallResult.reverted state _ =>
      Except.ok state.events.isEmpty
  | _ => Except.ok false

def checkedRevertedEventRollbackPreservesPriorLogs :
    Except TypeError Bool := do
  let emitted ←
    CheckedInput.ownCall 16 Executable.Examples.eventAbiContract
      (SolidCore.Solidity.Source.CallTarget.name "emitIt")
      SolidCore.Solidity.Source.State.empty []
  let (state, beforeName) ←
    match emitted with
    | SolidCore.Solidity.Source.CallResult.returned state _ =>
        match state.events with
        | [event] => Except.ok (state, event.name)
        | _ => Except.error (executableFailure "event ABI initial log")
    | _ => Except.error (executableFailure "event ABI initial call")
  let result ←
    CheckedInput.ownCall 16 Executable.Examples.eventAbiContract
      (SolidCore.Solidity.Source.CallTarget.name "emitThenRevert")
      state []
  match result with
  | SolidCore.Solidity.Source.CallResult.reverted revertedState _ =>
      match revertedState.events with
      | [event] => Except.ok (event.name == beforeName)
      | _ => Except.ok false
  | _ => Except.ok false

def checkedStorageRollbackDropsWrite :
    Except TypeError Bool := do
  let result ←
    CheckedInput.ownCall 24 Executable.Examples.storageRollbackContract
      (SolidCore.Solidity.Source.CallTarget.name "writeThenRevert")
      SolidCore.Solidity.Source.State.empty
      [SolidCore.Solidity.Source.Value.word 9]
  match result with
  | SolidCore.Solidity.Source.CallResult.reverted state _ =>
      let getter ←
        CheckedInput.ownCall 16
          Executable.Examples.storageRollbackContract
          (SolidCore.Solidity.Source.CallTarget.name "x")
          state []
      match getter with
      | SolidCore.Solidity.Source.CallResult.returned _
          [SolidCore.Solidity.Source.Value.word value] =>
          Except.ok (value == 0)
      | _ => Except.ok false
  | _ => Except.ok false

def checkedStorageRollbackPreservesPriorValue :
    Except TypeError Bool := do
  let setResult ←
    CheckedInput.ownCall 24 Executable.Examples.storageRollbackContract
      (SolidCore.Solidity.Source.CallTarget.name "set")
      SolidCore.Solidity.Source.State.empty
      [SolidCore.Solidity.Source.Value.word 5]
  let setState ←
    match setResult with
    | SolidCore.Solidity.Source.CallResult.returned state _ =>
        Except.ok state
    | _ => Except.error (executableFailure "storage rollback set")
  let result ←
    CheckedInput.ownCall 24 Executable.Examples.storageRollbackContract
      (SolidCore.Solidity.Source.CallTarget.name "writeThenRevert")
      setState [SolidCore.Solidity.Source.Value.word 11]
  match result with
  | SolidCore.Solidity.Source.CallResult.reverted revertedState _ =>
      let getter ←
        CheckedInput.ownCall 16
          Executable.Examples.storageRollbackContract
          (SolidCore.Solidity.Source.CallTarget.name "x")
          revertedState []
      match getter with
      | SolidCore.Solidity.Source.CallResult.returned _
          [SolidCore.Solidity.Source.Value.word value] =>
          Except.ok (value == 5)
      | _ => Except.ok false
  | _ => Except.ok false

def checkedDynamicEventAbiTopicsMatchExpected :
    Except TypeError Bool := do
  let expected ←
    optionToExcept "dynamic event ABI topics"
      Executable.Examples.dynamicEventAbiExpectedTopics
  let result ←
    CheckedInput.ownCall 16
      Executable.Examples.dynamicEventAbiContract
      (SolidCore.Solidity.Source.CallTarget.name "emitIt")
      SolidCore.Solidity.Source.State.empty []
  match result with
  | SolidCore.Solidity.Source.CallResult.returned state _ =>
      match state.events with
      | [event] => Except.ok (event.topics == expected)
      | _ => Except.ok false
  | _ => Except.ok false

def checkedDynamicEventAbiDataBytesMatchExpected :
    Except TypeError Bool := do
  let expected ←
    optionToExcept "dynamic event ABI data"
      Executable.Examples.dynamicEventAbiExpectedDataBytes
  let result ←
    CheckedInput.ownCall 16
      Executable.Examples.dynamicEventAbiContract
      (SolidCore.Solidity.Source.CallTarget.name "emitIt")
      SolidCore.Solidity.Source.State.empty []
  match result with
  | SolidCore.Solidity.Source.CallResult.returned state _ =>
      match state.events with
      | [event] => Except.ok (event.dataBytes == expected)
      | _ => Except.ok false
  | _ => Except.ok false

def checkedFreeEventErrorShadowUnitsAccepted : Bool :=
  Result.isOk (CheckedInput.program Executable.Examples.freeErrorUnit) &&
    Result.isOk
      (CheckedInput.program Executable.Examples.shadowedFreeErrorUnit) &&
    Result.isOk (CheckedInput.program Executable.Examples.freeEventUnit) &&
    Result.isOk
      (CheckedInput.program Executable.Examples.shadowedFreeEventUnit) &&
    Result.isOk
      (CheckedInput.program
        Executable.Examples.inheritedEventErrorShadowUnit)

def checkedEventErrorDeclarationDisciplineAccepted : Bool :=
    Result.isOk (TypecheckedInput.checkedSourceUnit emitPingSource) &&
    Result.isOk (TypecheckedInput.checkedSourceUnit freeEventEmitSource) &&
    Result.isOk (TypecheckedInput.checkedSourceUnit eventSelectorSource) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit freeEventSelectorSource) &&
    Result.isOk (TypecheckedInput.checkedSourceUnit overloadedEventSource) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit freeAndContractSameEventSource) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit
        freeAndContractEventNameShadowAcceptedSource) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit externalFunctionEventParamSource) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit threeIndexedEventSource) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit anonymousFourIndexedEventSource) &&
    Result.isOk (TypecheckedInput.checkedSourceUnit revertBoomSource) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit freeAndContractSameErrorSource) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit
        freeAndContractErrorNameShadowAcceptedSource)

def checkedEventErrorDeclarationDisciplineRejected : Bool :=
  Result.isError (TypecheckedInput.checkedSourceUnit reservedErrorSource) &&
    Result.isError (TypecheckedInput.checkedSourceUnit reservedPanicSource) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit duplicateErrorParamNameSource) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit duplicateEventSource) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit duplicateFreeEventSource) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit duplicateEventParamNameSource) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit
        freeAndContractEventNameShadowRejectsFreeMatchSource) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit
        freeEventFunctionNameCollisionSource) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit mappingEventParamSource) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit freeMappingEventParamSource) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit internalFunctionEventParamSource) &&
    Result.isError (TypecheckedInput.checkedSourceUnit fourIndexedEventSource) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit overloadedEventSelectorSource) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit anonymousEventSelectorSource) &&
    Result.isError (TypecheckedInput.checkedSourceUnit unknownEventSource) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit
        freeAndContractErrorNameShadowRejectsFreeMatchSource) &&
    Result.isError (TypecheckedInput.checkedSourceUnit unknownErrorSource)

def checkedInheritedNamespaceShadowingAccepted : Bool :=
  Result.isOk
      (TypecheckedInput.checkedSourceUnit
        privateStateShadowsInheritedPrivateFunctionSource) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit
        functionShadowsInheritedPrivateStateSource) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit
        (inheritedPrivateStateNameItemSource
          inheritedStateNameModifierItem)) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit
        (inheritedPrivateStateNameItemSource inheritedStateNameEventItem)) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit
        (inheritedPrivateStateNameItemSource inheritedStateNameErrorItem)) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit
        (inheritedPrivateStateNameItemSource inheritedStateNameStructItem)) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit
        (inheritedPrivateStateNameItemSource inheritedStateNameEnumItem)) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit
        (inheritedPrivateStateNameItemSource
          inheritedStateNameUserValueTypeItem)) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit
        eventShadowsInheritedPrivateFunctionSource) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit
        (inheritedEventNameItemSource
          (Solidity.ContractItem.eventDecl
            { name := "announced"
              params := [{ name := none, ty := uint256 }] }))) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit
        (inheritedErrorNameItemSource
          (Solidity.ContractItem.function
            revertInheritedErrorFunction))) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit
        (inheritedErrorShadowsFreeErrorSource
          revertInheritedErrorSignatureFunction)) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit
        (inheritedEventShadowsFreeEventSource
          emitInheritedEventSignatureFunction)) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit inheritedUserTypesStateSource) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit
        qualifiedInheritedStructStateSource) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit
        freeStructShadowedByInheritedSource) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit modifierOverrideSource) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit inheritedModifierSource)

def checkedInheritedNamespaceShadowingRejected : Bool :=
  Result.isError
      (TypecheckedInput.checkedSourceUnit
        privateStateShadowsInheritedFunctionSource) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit functionShadowsInheritedStateSource) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit
        (inheritedStateNameItemSource inheritedStateNameModifierItem)) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit
        (inheritedStateNameItemSource inheritedStateNameEventItem)) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit
        (inheritedStateNameItemSource inheritedStateNameErrorItem)) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit
        (inheritedStateNameItemSource inheritedStateNameStructItem)) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit
        (inheritedStateNameItemSource inheritedStateNameEnumItem)) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit
        (inheritedStateNameItemSource
          inheritedStateNameUserValueTypeItem)) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit
        eventShadowsInheritedFunctionSource) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit
        modifierShadowsInheritedFunctionSource) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit
        (inheritedModifierNameItemSource
          (Solidity.ContractItem.function
            functionShadowsInheritedModifierFunction))) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit
        (inheritedModifierNameItemSource stateShadowsInheritedModifierItem)) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit
        (inheritedModifierNameItemSource inheritedStateNameEventItem)) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit
        (inheritedEventNameItemSource
          (Solidity.ContractItem.function
            functionShadowsInheritedEventFunction))) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit
        (inheritedEventNameItemSource
          (Solidity.ContractItem.stateVar
            { name := "announced"
              ty := uint256
              visibility := some Visibility.private_ }))) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit
        (inheritedEventNameItemSource
          (Solidity.ContractItem.errorDecl
            { name := "announced" }))) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit
        (inheritedEventNameItemSource
          (Solidity.ContractItem.eventDecl
            { name := "announced" }))) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit
        (inheritedErrorNameItemSource
          (Solidity.ContractItem.eventDecl
            { name := "Problem"
              params := [{ name := none, ty := uint256 }] }))) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit
        (inheritedErrorShadowsFreeErrorSource
          revertFreeErrorSignatureFunction)) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit
        (inheritedEventShadowsFreeEventSource
          emitFreeEventSignatureFunction)) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit
        ({ items :=
            [ inheritedStructNameBaseSourceItem
            , Solidity.SourceItem.contract
                { name := "BadFunctionShadowsInheritedType"
                  bases :=
                    [{ base := userPath "InheritedStructNameBase"
                       args := [] }]
                  items :=
                    [ Solidity.ContractItem.function
                        { simpleReturnFunction with
                          name := some "record"
                          mutability := StateMutability.pure } ] } ] } :
          Solidity.SourceUnit)) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit
        freeStructFieldHiddenByInheritedSource) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit missingModifierOverrideSource)

def checkedMutabilityDisciplineAccepted : Bool :=
  Result.isOk
      (TypecheckedInput.checkedSourceUnit viewStateReadSource) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit nonpayableStateWriteSource) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit modifierArgFromParamSource) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit viewWithStateReadModifierSource) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit
        nonpayableWithStateWriteModifierSource) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit viewCallsPureSource)

def checkedMutabilityDisciplineRejected : Bool :=
  Result.isError
      (TypecheckedInput.checkedSourceUnit pureStateReadSource) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit viewStateWriteSource) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit pureWithStateReadModifierSource) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit viewWithStateWriteModifierSource) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit pureCallsViewSource) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit viewEmitSource) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit viewCreatesContractSource)

def checkedContractFormDisciplineAccepted : Bool :=
  Result.isOk (TypecheckedInput.checkedSourceUnit interfaceSource) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit interfaceFallbackSource) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit interfaceReceiveSource) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit interfaceTypedFallbackSource) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit abstractMissingBodySource) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit
        abstractInheritsAbstractFunctionSource) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit
        implementedInterfaceFunctionSource) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit
        implementedInterfaceFallbackSource) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit
        implementedInterfaceReceiveSource) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit abstractBodylessModifierSource) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit
        abstractInheritsAbstractModifierSource) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit implementedAbstractModifierSource) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit libraryConstantSource) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit libraryModifierSource)

def checkedCallableFormDisciplineAccepted : Bool :=
  Result.isOk (TypecheckedInput.checkedSourceUnit typedFallbackSource) &&
    Result.isOk (TypecheckedInput.checkedSourceUnit untypedFallbackSource) &&
    Result.isOk (TypecheckedInput.checkedSourceUnit payableFallbackSource) &&
    Result.isOk (TypecheckedInput.checkedSourceUnit receiveSource) &&
    Result.isOk (TypecheckedInput.checkedSourceUnit fallbackOverrideSource) &&
    Result.isOk (TypecheckedInput.checkedSourceUnit receiveOverrideSource) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit publicConstructorVisibilitySource) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit
        abstractInternalConstructorVisibilitySource)

def checkedCallableFormDisciplineRejected : Bool :=
  Result.isError (TypecheckedInput.checkedSourceUnit badFallbackViewSource) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit badFallbackPublicSource) &&
    Result.isError (TypecheckedInput.checkedSourceUnit badFallbackParamSource) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit
        badTypedFallbackMemoryParamSource) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit
        badTypedFallbackCalldataReturnSource) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit badTypedFallbackNoReturnSource) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit badReceiveNonpayableSource) &&
    Result.isError (TypecheckedInput.checkedSourceUnit badReceivePublicSource) &&
    Result.isError (TypecheckedInput.checkedSourceUnit badReceiveParamSource) &&
    Result.isError (TypecheckedInput.checkedSourceUnit badReceiveReturnSource) &&
    Result.isError (TypecheckedInput.checkedSourceUnit multipleReceiveSource) &&
    Result.isError (TypecheckedInput.checkedSourceUnit multipleFallbackSource) &&
    Result.isError (TypecheckedInput.checkedSourceUnit libraryFallbackSource) &&
    Result.isError (TypecheckedInput.checkedSourceUnit libraryReceiveSource) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit missingFallbackOverrideSource) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit payableFallbackOverrideSource) &&
    Result.isError (TypecheckedInput.checkedSourceUnit constructorVirtualSource) &&
    Result.isError (TypecheckedInput.checkedSourceUnit freeVirtualSource) &&
    Result.isError (TypecheckedInput.checkedSourceUnit freePayableSource) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit
        concreteInternalConstructorVisibilitySource) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit
        abstractPublicConstructorVisibilitySource) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit privateConstructorVisibilitySource) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit externalConstructorVisibilitySource) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit abstractFallbackWithoutVirtualSource)

def checkedContractFormDisciplineRejected : Bool :=
  Result.isError
      (TypecheckedInput.checkedSourceUnit badInterfaceBodySource) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit badInterfaceFallbackBodySource) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit interfaceConstructorSource) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit abstractInterfaceSource) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit nonAbstractMissingBodySource) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit inheritedAbstractFunctionSource) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit inheritedInterfaceFunctionSource) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit inheritedInterfaceFallbackSource) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit inheritedInterfaceReceiveSource) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit
        abstractBodylessModifierNoVirtualSource) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit nonAbstractBodylessModifierSource) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit inheritedAbstractModifierSource) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit libraryStateVarSource) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit libraryImmutableSource) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit libraryVirtualFunctionSource) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit libraryVirtualModifierSource) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit interfaceUsingDirectiveSource)

def checkedFunctionTypeDisciplineAccepted : Bool :=
  Result.isOk
      (TypecheckedInput.checkedSourceUnit
        externalFunctionTakingFunctionSource) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit externalPayableFunctionTypeSource) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit
        functionTypeMutabilityConversionSource) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit
        internalFunctionPointerAliasSource) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit
        internalFunctionPointerReassignSource) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit
        internalFunctionPointerAssignAfterDeclSource) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit
        internalFunctionPointerDeleteThenAssignSource) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit
        internalFunctionPointerUninitializedCallSource) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit
        internalFunctionPointerDeletedCallSource) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit
        internalFunctionPointerCopySource) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit internalFunctionPointerParamSource) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit
        externalFunctionPointerGasCallSource) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit
        publicExternalFunctionPointerStateVarSource)

def checkedFunctionTypeDisciplineRejected : Bool :=
  Result.isError
      (TypecheckedInput.checkedSourceUnit
        externalFunctionTakingInternalFunctionSource) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit
        externalFunctionTakingMappingSource) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit internalPayableFunctionTypeSource) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit
        internalFunctionPointerAliasOverloadedSource) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit
        internalFunctionPointerParamOverloadedSource) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit
        publicInternalFunctionPointerParamSource) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit
        invalidPublicFunctionTypeParamSource) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit
        publicInternalFunctionPointerStateVarSource) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit
        publicStructInternalFunctionGetterSource)

def checkedTryCatchDisciplineAccepted : Bool :=
  Result.isOk
      (TypecheckedInput.checkedSourceUnit tryExternalFunctionCallSource) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit tryContractMemberCallSource) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit tryReturnBytesMemorySource) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit tryCatchErrorSource) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit tryCatchFullSource) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit tryContractCreationSource)

def checkedTryCatchDisciplineRejected : Bool :=
  Result.isError
      (TypecheckedInput.checkedSourceUnit tryInternalFunctionCallSource) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit tryLowLevelCallSource) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit tryArrayPushSource) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit tryLiteralSource) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit tryReturnMismatchSource) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit tryReturnsNoCatchSource) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit tryNoCatchSource) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit badTryReturnBytesCalldataSource) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit badTryReturnBytesStorageSource) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit badTryReturnBytesNoLocationSource) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit duplicateTryReturnNameSource) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit badCatchErrorSource) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit duplicateCatchErrorSource) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit duplicateCatchPanicSource) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit duplicateLowLevelCatchSource)

def checkedContextualArrayDisciplineAccepted : Bool :=
  Result.isOk
      (TypecheckedInput.checkedSourceUnit contextualArrayLiteralArgSource) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit
        contextualNamedArrayLiteralArgSource) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit
        contextualUsingArrayLiteralArgSource) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit
        contextualUsingNamedArrayLiteralArgSource) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit contextualArrayTupleReturnSource) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit
        contextualArrayTupleAssignmentSource) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit contextualArrayAssignmentSource) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit
        contextualArrayTernaryAssignmentSource) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit contextualArrayTernaryLocalSource) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit contextualArrayTernaryReturnSource) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit contextualArrayTernaryArgSource) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit
        contextualArrayStructConstructorSource) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit
        contextualNamedArrayStructConstructorSource) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit contextualArrayLiteralEventSource) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit
        contextualNamedArrayLiteralEventSource) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit contextualArrayLiteralErrorSource) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit
        contextualNamedArrayLiteralErrorSource) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit
        contextualArrayLiteralRequireErrorSource) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit
        contextualArrayLiteralModifierSource) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit
        contextualArrayConstructorCreateSource) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit
        contextualNamedArrayConstructorCreateSource) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit
        contextualArrayConstructorSaltedCreateSource) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit contextualArrayBaseSpecifierSource) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit contextualArrayBaseModifierSource) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit contextualArrayAbiEncodeCallSource) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit
        contextualArrayTernaryAbiEncodeCallSource) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit
        contextualArrayExternalMemberCallSource) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit
        contextualArrayExternalMemberCallWithOptionsSource) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit
        contextualArrayExternalMemberNamedCallSource) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit
        contextualArrayTryExternalMemberCallSource) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit
        contextualArrayExternalFunctionValueCallSource) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit
        contextualArrayExternalFunctionValueCallWithOptionsSource) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit
        contextualArrayTryExternalFunctionValueCallSource) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit contextualArrayDirectLibraryCallSource) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit
        contextualArrayDirectLibraryNamedCallSource) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit contextualArrayExplicitBaseCallSource) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit
        contextualArrayExplicitBaseNamedCallSource) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit contextualArraySuperCallSource) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit contextualArraySuperNamedCallSource)

def checkedContextualArrayDisciplineRejected : Bool :=
  Result.isError
      (TypecheckedInput.checkedSourceUnit
        contextualArrayLiteralArgOverflowSource) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit
        contextualNamedArrayLiteralArgOverflowSource) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit
        contextualUsingArrayLiteralArgOverflowSource) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit
        contextualUsingNamedArrayLiteralArgOverflowSource) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit
        contextualArrayTupleReturnOverflowSource) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit
        contextualArrayTupleAssignmentOverflowSource) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit
        contextualArrayAssignmentOverflowSource) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit
        contextualArrayTernaryAssignmentOverflowSource) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit
        contextualArrayTernaryLocalOverflowSource) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit
        contextualArrayTernaryReturnOverflowSource) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit
        contextualArrayTernaryArgOverflowSource) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit
        contextualArrayStructConstructorOverflowSource) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit
        contextualNamedArrayStructConstructorOverflowSource) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit
        contextualArrayLiteralEventOverflowSource) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit
        contextualNamedArrayLiteralEventOverflowSource) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit
        contextualArrayLiteralErrorOverflowSource) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit
        contextualNamedArrayLiteralErrorOverflowSource) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit
        contextualArrayLiteralRequireErrorOverflowSource) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit
        contextualArrayLiteralModifierOverflowSource) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit
        contextualArrayConstructorCreateOverflowSource) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit
        contextualNamedArrayConstructorCreateOverflowSource) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit
        contextualArrayBaseSpecifierOverflowSource) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit
        contextualArrayBaseModifierOverflowSource) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit
        contextualArrayAbiEncodeCallOverflowSource) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit
        contextualArrayTernaryAbiEncodeCallOverflowSource) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit
        contextualArrayExternalMemberCallOverflowSource) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit
        contextualArrayExternalMemberNamedCallOverflowSource) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit
        contextualArrayTryExternalMemberCallOverflowSource) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit
        contextualArrayExternalFunctionValueCallOverflowSource) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit
        contextualArrayTryExternalFunctionValueCallOverflowSource) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit
        contextualArrayDirectLibraryCallOverflowSource) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit
        contextualArrayDirectLibraryNamedCallOverflowSource) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit
        contextualArrayExplicitBaseCallOverflowSource) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit
        contextualArrayExplicitBaseNamedCallOverflowSource) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit
        contextualArraySuperCallOverflowSource) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit
        contextualArraySuperNamedCallOverflowSource)

def checkedAbiEncodeCallDisciplineAccepted : Bool :=
  Result.isOk
      (TypecheckedInput.checkedSourceUnit abiEncodeCallSource) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit abiEncodeCallNewTargetSource) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit abiEncodeCallConversionTargetSource) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit abiEncodeCallTypeNameSource) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit
        abiEncodeCallExternalFunctionPointerSource)

def checkedAbiEncodeCallDisciplineRejected : Bool :=
  Result.isError
      (TypecheckedInput.checkedSourceUnit
        badAbiEncodeCallNewTargetViewSource) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit
        badAbiEncodeCallTernaryTargetConditionSource) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit
        badAbiEncodeCallTernaryTargetBranchSource) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit badAbiEncodeCallSource) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit
        badAbiEncodeCallInternalFunctionPointerSource) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit badAbiEncodeCallBareFunctionSource) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit badAbiEncodeCallThisInPureSource)

def checkedDataLocationDisciplineAccepted : Bool :=
  Result.isOk
      (TypecheckedInput.checkedSourceUnit storageReturnBindingSource) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit storageParamCallSource) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit libraryStorageParamSource) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit calldataArrayCopySource) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit calldataToStorageAssignSource) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit storageArrayPushPopSource) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit storageBytesPushPopSource) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit newStringSource) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit calldataBytesSliceSource) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit calldataStringSliceSource) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit calldataBytesSliceIndexSource) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit calldataBytesSliceLocalSource) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit
        calldataBytesSliceMemoryLocalSource) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit
        calldataBytesSliceMemoryLocalMutationSource) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit calldataStringSliceLocalSource) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit
        calldataStringSliceMemoryLocalSource) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit calldataArraySliceSource) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit
        calldataArraySliceMemoryLocalSource) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit
        calldataArraySliceMemoryLocalMutationSource) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit calldataArraySliceIndexSource) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit calldataArraySliceLocalSource) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit structSource) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit
        abstractStorageConstructorParamSource) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit modifierStorageParamSource) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit modifierMemoryParamSource) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit modifierCalldataParamSource)

def checkedDataLocationDisciplineRejected : Bool :=
  Result.isError
      (TypecheckedInput.checkedSourceUnit memoryToStorageReturnSource) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit uninitializedStorageAliasSource) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit memoryToStorageAliasSource) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit viewWritesStorageAliasSource) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit memoryToStorageParamSource) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit publicStorageParamSource) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit valueTypeMemoryParamSource) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit signedArrayIndexSource) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit signedNewArrayLengthSource) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit calldataArrayWriteSource) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit calldataStructFieldWriteSource) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit viewArrayPushSource) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit memoryArrayPushSource) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit fixedArrayPushSource) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit calldataBytesPopSource) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit signedBytesIndexSource) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit signedNewBytesLengthSource) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit namedNewStringLengthSource) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit signedNewStringLengthSource) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit memoryBytesSliceSource) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit memoryStringSliceSource) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit memoryArraySliceSource) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit storageBytesSliceSource) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit storageStringSliceSource) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit storageArraySliceSource) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit stringIndexSource) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit stringLengthMemberSource) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit calldataSliceSignedIndexSource) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit calldataSliceMemberSource) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit calldataStringSliceMemberSource) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit calldataStringSliceIndexSource) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit calldataArraySliceMemberSource) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit missingStructLocationSource) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit
        missingStructReturnLocationSource) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit
        concreteStorageConstructorParamSource) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit calldataConstructorParamSource) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit missingConstructorLocationSource) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit valueTypeMemoryConstructorSource) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit modifierMissingLocationSource) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit modifierValueMemoryParamSource) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit stringErrorWithLocationSource) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit memoryMappingLocalSource) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit publicMappingParamSource) &&
    checkedMemoryAllocationInvalidSourcesRejected

def checkedTupleLocalBindingDisciplineAccepted : Bool :=
  Result.isOk
      (TypecheckedInput.checkedSourceUnit tupleReturnSource) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit tupleVarDeclSource) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit tupleVarDeclOmittedLiteralSource) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit tupleVarDeclOmittedReturnSource) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit nestedBlockLocalShadowSource) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit tupleAssignmentSource) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit tupleAssignmentHoleSource) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit tupleAssignmentFromReturnSource)

def checkedTupleLocalBindingDisciplineRejected : Bool :=
  Result.isError
      (TypecheckedInput.checkedSourceUnit tupleVarDeclOmittedNoInitSource) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit badTupleVarDeclSource) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit duplicateBlockLocalSource) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit badTupleAssignmentAritySource) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit badTupleAssignmentTypeSource) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit badTupleAssignmentTargetSource)

def checkedMappingDisciplineAccepted : Bool :=
    Result.isOk
      (TypecheckedInput.checkedSourceUnit mappingReadSource) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit deleteMappingValueSource) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit userValueMappingKeySource) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit signedMappingKeySource) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit
        mappingStructStorageRebindSource) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit
        mappingStructInternalStorageParamSource)

def checkedMappingDisciplineRejected : Bool :=
  Result.isError
      (TypecheckedInput.checkedSourceUnit badMappingIndexSource) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit deleteMappingVariableSource) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit
        mappingStructStorageCopySource) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit
        mappingStructMemoryLocalSource) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit
        mappingStructCalldataParamSource)

def checkedFixedPointTypeDisciplineAccepted : Bool :=
  fixedPointSourceDisciplineAccepted &&
    Result.isOk (TypecheckedInput.checkedSourceUnit fixedPointSource)

def checkedFixedPointTypeDisciplineRejected : Bool :=
  fixedPointSourceDisciplineRejected

def checkedCallOptionDisciplineRejected : Bool :=
  Result.isError
      (TypecheckedInput.checkedSourceUnit superCallOptionsSource) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit signedValueOptionExternalSource) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit signedGasOptionExternalSource) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit unknownCallOptionExternalSource) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit saltCallOptionExternalSource) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit duplicateCallOptionExternalSource) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit duplicateValueOptionExternalSource) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit
        internalIdentifierCallOptionsSource) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit
        internalFunctionPointerCallOptionsSource) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit lowLevelNamedArgumentSource) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit lowLevelSaltOptionSource) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit
        lowLevelStaticValueOptionSource) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit
        lowLevelDelegateValueOptionSource) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit
        lowLevelStaticSignedGasOptionSource) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit arrayMemberCallOptionsSource)

def checkedDeclarationNamespaceDisciplineAccepted : Bool :=
  Result.isOk
    (TypecheckedInput.checkedSourceUnit internalAbiTwinSource)

def checkedDeclarationNamespaceDisciplineRejected : Bool :=
  Result.isError
      (TypecheckedInput.checkedSourceUnit duplicateSignatureSource) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit stateFunctionNameClashSource) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit functionEventNameClashSource) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit
        topLevelFunctionContractNameClashSource) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit freeErrorOverloadSource) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit abiExternalSignatureClashSource)

def checkedStaticSourceDisciplineSemanticsMatch : Bool :=
  checkedPreValidityBoundarySemanticsMatch &&
    checkedInheritedNamespaceShadowingAccepted &&
    checkedInheritedNamespaceShadowingRejected &&
    checkedMutabilityDisciplineAccepted &&
    checkedMutabilityDisciplineRejected &&
    checkedContractFormDisciplineAccepted &&
    checkedContractFormDisciplineRejected &&
    checkedCallableFormDisciplineAccepted &&
    checkedCallableFormDisciplineRejected &&
    checkedFunctionTypeDisciplineAccepted &&
    checkedFunctionTypeDisciplineRejected &&
    checkedContextualArrayDisciplineAccepted &&
    checkedContextualArrayDisciplineRejected &&
    checkedAbiEncodeCallDisciplineAccepted &&
    checkedAbiEncodeCallDisciplineRejected &&
    checkedDataLocationDisciplineAccepted &&
    checkedDataLocationDisciplineRejected &&
    checkedTupleLocalBindingDisciplineAccepted &&
    checkedTupleLocalBindingDisciplineRejected &&
    checkedMappingDisciplineAccepted &&
    checkedMappingDisciplineRejected &&
    checkedFixedPointTypeDisciplineAccepted &&
    checkedFixedPointTypeDisciplineRejected &&
    checkedCallOptionDisciplineRejected &&
    checkedDeclarationNamespaceDisciplineAccepted &&
    checkedDeclarationNamespaceDisciplineRejected

def checkedFreeErrorAbiMatches : Except TypeError Bool := do
  let program ← CheckedInput.program Executable.Examples.freeErrorUnit
  let contract ← CheckedProgram.contract program "UsesFreeError"
  let calldata ←
    CheckedContract.functionCalldata contract "check"
      [SolidCore.Solidity.Source.Value.word 4]
  let result ←
    CheckedContract.callCalldata 16 contract
      SolidCore.Solidity.Source.State.empty calldata
  let payload ←
    optionToExcept "free error ABI payload"
      (SolidCore.Solidity.Source.ABI.encodeValues?
        [SolidCore.Solidity.Source.Ty.uint256]
        [SolidCore.Solidity.Source.Value.word 4])
  let selector :=
    SolidCore.Solidity.Source.ABI.encodeSelector
      (SolidCore.Solidity.Source.ABI.selectorFromSignature
        "TooSmall(uint256)")
  Except.ok (!result.success && result.output == selector ++ payload)

def checkedLocalErrorShadowsFreeAbiMatches :
    Except TypeError Bool := do
  let contract ←
    CheckedInput.contract Executable.Examples.shadowedFreeErrorUnit
      "LocalErrorShadow"
  match contract.core.errorDecls with
  | [decl] =>
      match decl.fields with
      | [SolidCore.Solidity.Source.Ty.address] =>
          Except.ok
            (decl.name == "TooSmall" &&
              SolidCore.Solidity.Source.wordEq decl.selector
                (SolidCore.Solidity.Source.ABI.selectorFromSignature
                  "TooSmall(address)"))
      | _ => Except.ok false
  | _ => Except.ok false

def checkedCanonicalFreeEventEmitMatches :
    Except TypeError Bool := do
  let result ←
    SourceUnit.checkedCallContract 32
      Executable.Examples.freeEventUnit "UsesFreeEvent"
      (SolidCore.Solidity.Source.CallTarget.name "emitIt")
      SolidCore.Solidity.Source.State.empty []
  match result with
  | SolidCore.Solidity.Source.CallResult.returned state [] =>
      match state.events with
      | [event] =>
          match event.data with
          | [SolidCore.Solidity.Source.Value.word value] =>
              Except.ok
                (event.name == "FilePing" &&
                  SolidCore.Solidity.Source.wordEq value 5)
          | _ => Except.ok false
      | _ => Except.ok false
  | _ => Except.ok false

def checkedLocalEventShadowsFreeAbiMatches :
    Except TypeError Bool := do
  let contract ←
    CheckedInput.contract Executable.Examples.shadowedFreeEventUnit
      "LocalEventShadow"
  match contract.core.eventDecls with
  | [decl] =>
      match decl.fields with
      | [{ ty := SolidCore.Solidity.Source.Ty.address, indexed := false }] =>
          Except.ok
            (decl.name == "FilePing" &&
              decl.topic? ==
                some
                  (SolidCore.Solidity.Source.Keccak.digestWord
                    "FilePing(address)"))
      | _ => Except.ok false
  | _ => Except.ok false

def checkedInheritedErrorShadowsFreeAbiMatches :
    Except TypeError Bool := do
  let contract ←
    CheckedInput.contract
      Executable.Examples.inheritedEventErrorShadowUnit
      "InheritedEventErrorDerived"
  match contract.core.errorDecls with
  | [decl] =>
      match decl.fields with
      | [] =>
          Except.ok
            (decl.name == "Collision" &&
              SolidCore.Solidity.Source.wordEq decl.selector
                (SolidCore.Solidity.Source.ABI.selectorFromSignature
                  "Collision()"))
      | _ => Except.ok false
  | _ => Except.ok false

def checkedInheritedEventShadowsFreeAbiMatches :
    Except TypeError Bool := do
  let contract ←
    CheckedInput.contract
      Executable.Examples.inheritedEventErrorShadowUnit
      "InheritedEventErrorDerived"
  match contract.core.eventDecls with
  | [decl] =>
      match decl.fields with
      | [] =>
          Except.ok
            (decl.name == "CollisionEvent" &&
              decl.topic? ==
                some
                  (SolidCore.Solidity.Source.Keccak.digestWord
                    "CollisionEvent()"))
      | _ => Except.ok false
  | _ => Except.ok false

def checkedFreeEventEmitMatches :
    Except TypeError Bool := do
  let result ←
    SourceUnit.checkedCallContract 32 freeEventEmitSource "EmitFreePing"
      (SolidCore.Solidity.Source.CallTarget.name "emitPing")
      SolidCore.Solidity.Source.State.empty []
  match result with
  | SolidCore.Solidity.Source.CallResult.returned state
      [SolidCore.Solidity.Source.Value.word ret] =>
      match state.events with
      | [event] =>
          match event.data with
          | [SolidCore.Solidity.Source.Value.word value] =>
              Except.ok
                (event.name == "Ping" &&
                  SolidCore.Solidity.Source.wordEq ret 1 &&
                  SolidCore.Solidity.Source.wordEq value 1)
          | _ => Except.ok false
      | _ => Except.ok false
  | _ => Except.ok false

def checkedEventSelectorMatches :
    Except TypeError Bool := do
  let result ←
    SourceUnit.checkedCallContract 32 eventSelectorSource "EventSelector"
      (SolidCore.Solidity.Source.CallTarget.name "selector")
      SolidCore.Solidity.Source.State.empty []
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _
      [SolidCore.Solidity.Source.Value.word selector] =>
      Except.ok
        (SolidCore.Solidity.Source.wordEq selector
          (SolidCore.Solidity.Source.Keccak.digestWord
            "Ping(uint256)"))
  | _ => Except.ok false

def checkedFreeEventSelectorMatches :
    Except TypeError Bool := do
  let result ←
    SourceUnit.checkedCallContract 32 freeEventSelectorSource
      "FreeEventSelector"
      (SolidCore.Solidity.Source.CallTarget.name "selector")
      SolidCore.Solidity.Source.State.empty []
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _
      [SolidCore.Solidity.Source.Value.word selector] =>
      Except.ok
        (SolidCore.Solidity.Source.wordEq selector
          (SolidCore.Solidity.Source.Keccak.digestWord
            "Ping(uint256)"))
  | _ => Except.ok false

def checkedFreeErrorRevertMatches :
    Except TypeError Bool := do
  let result ←
    SourceUnit.checkedCallContract 32 revertBoomSource "RevertBoom"
      (SolidCore.Solidity.Source.CallTarget.name "revertBoom")
      SolidCore.Solidity.Source.State.empty []
  match result with
  | SolidCore.Solidity.Source.CallResult.reverted _
      (SolidCore.Solidity.Source.RevertData.custom "Boom"
        [SolidCore.Solidity.Source.Value.word value]) =>
      Except.ok (SolidCore.Solidity.Source.wordEq value 1)
  | _ => Except.ok false

def checkedNamedEventArgumentOrderMatches :
    Except TypeError Bool := do
  let result ←
    SourceUnit.checkedCallContract 32 emitPairNamedSource
      "EmitPairNamed"
      (SolidCore.Solidity.Source.CallTarget.name "emitPairNamed")
      SolidCore.Solidity.Source.State.empty []
  match result with
  | SolidCore.Solidity.Source.CallResult.returned state
      [SolidCore.Solidity.Source.Value.word ret] =>
      match state.events with
      | [event] =>
          match event.data with
          | [ SolidCore.Solidity.Source.Value.word first
            , SolidCore.Solidity.Source.Value.word second ] =>
              Except.ok
                (event.name == "PairSeen" &&
                  SolidCore.Solidity.Source.wordEq ret 1 &&
                  SolidCore.Solidity.Source.wordEq first 40 &&
                  SolidCore.Solidity.Source.wordEq second 2)
          | _ => Except.ok false
      | _ => Except.ok false
  | _ => Except.ok false

def checkedNamedErrorArgumentOrderMatches :
    Except TypeError Bool := do
  let result ←
    SourceUnit.checkedCallContract 32 revertPairNamedSource
      "RevertPairNamed"
      (SolidCore.Solidity.Source.CallTarget.name "revertPairNamed")
      SolidCore.Solidity.Source.State.empty []
  match result with
  | SolidCore.Solidity.Source.CallResult.reverted _
      (SolidCore.Solidity.Source.RevertData.custom "PairBad"
        [ SolidCore.Solidity.Source.Value.word first
        , SolidCore.Solidity.Source.Value.word second ]) =>
      Except.ok
        (SolidCore.Solidity.Source.wordEq first 40 &&
          SolidCore.Solidity.Source.wordEq second 2)
  | _ => Except.ok false

def checkedRequireCustomErrorMatches :
    Except TypeError Bool := do
  let result ←
    SourceUnit.checkedCallContract 32 requirePairNamedSource
      "RequirePairNamed"
      (SolidCore.Solidity.Source.CallTarget.name "requirePairNamed")
      SolidCore.Solidity.Source.State.empty []
  match result with
  | SolidCore.Solidity.Source.CallResult.reverted _
      (SolidCore.Solidity.Source.RevertData.custom "PairBad"
        [ SolidCore.Solidity.Source.Value.word first
        , SolidCore.Solidity.Source.Value.word second ]) =>
      Except.ok
        (SolidCore.Solidity.Source.wordEq first 40 &&
          SolidCore.Solidity.Source.wordEq second 2)
  | _ => Except.ok false

def checkedEventArgumentSideEffectContract :
    Solidity.ContractDecl :=
  { name := "CheckedEventArgumentSideEffect"
    items :=
      [ Solidity.ContractItem.eventDecl
          { name := "Seen"
            params :=
              [{ name := some "value"
                 ty := Ty.uint 256
                 indexed := false }] }
      , Solidity.ContractItem.stateVar
          { name := "x", ty := Ty.uint 256 }
      , Solidity.ContractItem.function
          { name := some "value"
            visibility := some Visibility.internal_
            returns := [{ name := some "out", ty := Ty.uint 256 }]
            body :=
              some
                (Solidity.Stmt.block
                  [ Solidity.Stmt.expr
                      (Solidity.Expr.assign
                        (Solidity.Expr.ident "x")
                        AssignOp.assign
                        (Solidity.Expr.literal
                          (Solidity.Literal.number "7")))
                  , Solidity.Stmt.returnValues
                      (some (Solidity.Expr.ident "x")) ]) }
      , Solidity.ContractItem.function
          { name := some "run"
            visibility := some Visibility.public_
            returns := [{ name := some "out", ty := Ty.uint 256 }]
            body :=
              some
                (Solidity.Stmt.block
                  [ Solidity.Stmt.emitEvent
                      (Solidity.Expr.call
                        (Solidity.Expr.ident "Seen")
                        [Solidity.Arg.positional
                          (Solidity.Expr.call
                            (Solidity.Expr.ident "value") [])])
                  , Solidity.Stmt.returnValues
                      (some (Solidity.Expr.ident "x")) ]) } ] }

def checkedEventArgumentSideEffectMatches :
    Except TypeError Bool := do
  let result ←
    ContractDecl.checkedCall 64 checkedEventArgumentSideEffectContract
      (SolidCore.Solidity.Source.CallTarget.name "run")
      SolidCore.Solidity.Source.State.empty []
  match result with
  | SolidCore.Solidity.Source.CallResult.returned state
      [SolidCore.Solidity.Source.Value.word ret] =>
      match state.events with
      | [event] =>
          match event.data with
          | [SolidCore.Solidity.Source.Value.word value] =>
              Except.ok
                (event.name == "Seen" &&
                  SolidCore.Solidity.Source.wordEq ret 7 &&
                  SolidCore.Solidity.Source.wordEq value 7 &&
                  SolidCore.Solidity.Source.wordEq (state.loadSlot 0) 7)
          | _ => Except.ok false
      | _ => Except.ok false
  | _ => Except.ok false

def checkedErrorRollbackContract :
    Solidity.ContractDecl :=
  { name := "CheckedErrorRollback"
    items :=
      [ Solidity.ContractItem.errorDecl
          { name := "Bad"
            params := [{ name := some "value", ty := Ty.uint 256 }] }
      , Solidity.ContractItem.stateVar
          { name := "x", ty := Ty.uint 256 }
      , Solidity.ContractItem.function
          { name := some "value"
            visibility := some Visibility.internal_
            returns := [{ name := some "out", ty := Ty.uint 256 }]
            body :=
              some
                (Solidity.Stmt.block
                  [ Solidity.Stmt.expr
                      (Solidity.Expr.assign
                        (Solidity.Expr.ident "x")
                        AssignOp.assign
                        (Solidity.Expr.literal
                          (Solidity.Literal.number "7")))
                  , Solidity.Stmt.returnValues
                      (some (Solidity.Expr.ident "x")) ]) }
      , Solidity.ContractItem.function
          { name := some "run"
            visibility := some Visibility.public_
            returns := [{ name := some "out", ty := Ty.uint 256 }]
            body :=
              some
                (Solidity.Stmt.block
                  [ Solidity.Stmt.revertCall
                      (Solidity.Expr.call
                        (Solidity.Expr.ident "Bad")
                        [Solidity.Arg.positional
                          (Solidity.Expr.call
                            (Solidity.Expr.ident "value") [])])
                  , Solidity.Stmt.returnValues
                      (some (Solidity.Expr.ident "x")) ]) } ] }

def checkedErrorRollbackMatches :
    Except TypeError Bool := do
  let result ←
    ContractDecl.checkedCall 64 checkedErrorRollbackContract
      (SolidCore.Solidity.Source.CallTarget.name "run")
      SolidCore.Solidity.Source.State.empty []
  match result with
  | SolidCore.Solidity.Source.CallResult.reverted state
      (SolidCore.Solidity.Source.RevertData.custom "Bad"
        [SolidCore.Solidity.Source.Value.word value]) =>
      match state.events with
      | [] =>
          Except.ok
            (SolidCore.Solidity.Source.wordEq value 7 &&
              SolidCore.Solidity.Source.wordEq (state.loadSlot 0) 0)
      | _ => Except.ok false
  | _ => Except.ok false

def checkedInheritedErrorAbiPayloadMatches :
    Except TypeError Bool := do
  let program ←
    SourceUnit.checkedProgram
      Executable.Examples.inheritedEventErrorShadowUnit
  let contract ←
    CheckedProgram.contract program "InheritedEventErrorDerived"
  let calldata ←
    CheckedContract.functionCalldata contract "fail" []
  let result ←
    CheckedContract.callCalldata 16 contract
      SolidCore.Solidity.Source.State.empty calldata
  let selector :=
    SolidCore.Solidity.Source.ABI.encodeSelector
      (SolidCore.Solidity.Source.ABI.selectorFromSignature
        "Collision()")
  Except.ok (!result.success && result.output == selector)

def checkedInheritedEventEmitMatches :
    Except TypeError Bool := do
  let result ←
    SourceUnit.checkedCallContract 32
      Executable.Examples.inheritedEventErrorShadowUnit
      "InheritedEventErrorDerived"
      (SolidCore.Solidity.Source.CallTarget.name "emitIt")
      SolidCore.Solidity.Source.State.empty []
  match result with
  | SolidCore.Solidity.Source.CallResult.returned state [] =>
      match state.events with
      | [event] =>
          match event.data, event.topics with
          | [], [topic] =>
              Except.ok
                (event.name == "CollisionEvent" &&
                  SolidCore.Solidity.Source.wordEq topic
                    (SolidCore.Solidity.Source.Keccak.digestWord
                      "CollisionEvent()"))
          | _, _ => Except.ok false
      | _ => Except.ok false
  | _ => Except.ok false

def checkedLowLevelCallContract : Solidity.ContractDecl :=
  { name := "CheckedLowLevelCall"
    items :=
      [ Solidity.ContractItem.function
          { name := some "probe"
            visibility := some Visibility.public_
            params :=
              [ { name := some "target", ty := Ty.address false }
              , { name := some "payload"
                  ty := Ty.bytes
                  location := some DataLocation.memory } ]
            returns :=
              [{ name := some "out"
                 ty := lowLevelCallReturnTy
                 location := some DataLocation.memory }]
            body :=
              some
                (Solidity.Stmt.returnValues
                  (some
                    (Solidity.Expr.call
                      (Solidity.Expr.member
                        (Solidity.Expr.ident "target") "call")
                      [Solidity.Arg.positional
                        (Solidity.Expr.ident "payload")]))) }
      , Solidity.ContractItem.function
          { name := some "payWithOptions"
            visibility := some Visibility.public_
            mutability := StateMutability.payable
            returns :=
              [{ name := some "out"
                 ty := lowLevelCallReturnTy
                 location := some DataLocation.memory }]
            body :=
              some
                (Solidity.Stmt.returnValues
                  (some
                    (Solidity.Expr.callWithOptions
                      (Solidity.Expr.member
                        (Solidity.Expr.literal
                          (Solidity.Literal.address 0xbeef))
                        "call")
                      [ Solidity.CallOption.named "gas"
                          (Solidity.Expr.literal
                            (Solidity.Literal.number "1000000"))
                      , Solidity.CallOption.named "value"
                          (Solidity.Expr.literal
                            (Solidity.Literal.number "5")) ]
                      [Solidity.Arg.positional
                        (Solidity.Expr.literal
                          (Solidity.Literal.bytes [1, 2]))]))) }
      , Solidity.ContractItem.function
          { name := some "payWithOptionEffects"
            visibility := some Visibility.public_
            mutability := StateMutability.payable
            returns :=
              [ { name := some "gasSeen", ty := Ty.uint 256 }
              , { name := some "sent", ty := Ty.uint 256 } ]
            body :=
              some
                (Solidity.Stmt.block
                  [ Solidity.Stmt.varDecl
                      [{ name := some "gasSeen"
                         ty := some (Ty.uint 256) }]
                      (some
                        (Solidity.Expr.literal
                          (Solidity.Literal.number "0")))
                  , Solidity.Stmt.varDecl
                      [{ name := some "sent"
                         ty := some (Ty.uint 256) }]
                      (some
                        (Solidity.Expr.literal
                          (Solidity.Literal.number "0")))
                  , Solidity.Stmt.expr
                      (Solidity.Expr.callWithOptions
                        (Solidity.Expr.member
                          (Solidity.Expr.literal
                            (Solidity.Literal.address 0xbeef))
                          "call")
                        [ Solidity.CallOption.named "gas"
                            (Solidity.Expr.assign
                              (Solidity.Expr.ident
                                "gasSeen")
                              AssignOp.assign
                              (Solidity.Expr.literal
                                (Solidity.Literal.number
                                  "11")))
                        , Solidity.CallOption.named "value"
                            (Solidity.Expr.assign
                              (Solidity.Expr.ident "sent")
                              AssignOp.assign
                              (Solidity.Expr.literal
                                (Solidity.Literal.number
                                  "5"))) ]
                        [Solidity.Arg.positional
                          (Solidity.Expr.literal
                            (Solidity.Literal.bytes
                              [1, 2]))])
                  , Solidity.Stmt.returnValues
                      (some
                        (Solidity.Expr.tuple
                          [ Solidity.TupleItem.value
                              (Solidity.Expr.ident "gasSeen")
                          , Solidity.TupleItem.value
                              (Solidity.Expr.ident "sent") ])) ]) }
      , Solidity.ContractItem.function
          { name := some "probeBoth"
            visibility := some Visibility.public_
            params :=
              [ { name := some "target", ty := Ty.address false }
              , { name := some "payload"
                  ty := Ty.bytes
                  location := some DataLocation.memory } ]
            returns :=
              [ { name := some "staticOut"
                  ty := lowLevelCallReturnTy
                  location := some DataLocation.memory }
              , { name := some "delegateOut"
                  ty := lowLevelCallReturnTy
                  location := some DataLocation.memory } ]
            body :=
              some
                (Solidity.Stmt.returnValues
                  (some
                    (Solidity.Expr.tuple
                      [ Solidity.TupleItem.value
                          (Solidity.Expr.callWithOptions
                            (Solidity.Expr.member
                              (Solidity.Expr.ident "target")
                              "staticcall")
                            [Solidity.CallOption.named "gas"
                              (Solidity.Expr.literal
                                (Solidity.Literal.number
                                  "50000"))]
                            [Solidity.Arg.positional
                              (Solidity.Expr.ident "payload")])
                      , Solidity.TupleItem.value
                          (Solidity.Expr.call
                            (Solidity.Expr.member
                              (Solidity.Expr.ident "target")
                              "delegatecall")
                            [Solidity.Arg.positional
                              (Solidity.Expr.ident "payload")]) ]))) }
      , Solidity.ContractItem.function
          { name := some "delegateGas"
            visibility := some Visibility.public_
            params :=
              [ { name := some "target", ty := Ty.address false }
              , { name := some "payload"
                  ty := Ty.bytes
                  location := some DataLocation.memory } ]
            returns :=
              [{ name := some "out"
                 ty := lowLevelCallReturnTy
                 location := some DataLocation.memory }]
            body :=
              some
                (Solidity.Stmt.returnValues
                  (some
                    (Solidity.Expr.callWithOptions
                      (Solidity.Expr.member
                        (Solidity.Expr.ident "target")
                        "delegatecall")
                      [Solidity.CallOption.named "gas"
                        (Solidity.Expr.literal
                          (Solidity.Literal.number "900"))]
                      [Solidity.Arg.positional
                        (Solidity.Expr.ident "payload")]))) }
      , Solidity.ContractItem.function
          { name := some "staticGasExpr"
            visibility := some Visibility.public_
            params :=
              [ { name := some "target", ty := Ty.address false }
              , { name := some "payload"
                  ty := Ty.bytes
                  location := some DataLocation.memory } ]
            returns :=
              [{ name := some "gasSeen", ty := Ty.uint 256 }]
            body :=
              some
                (Solidity.Stmt.block
                  [ Solidity.Stmt.varDecl
                      [{ name := some "gasSeen"
                         ty := some (Ty.uint 256) }]
                      (some
                        (Solidity.Expr.literal
                          (Solidity.Literal.number "0")))
                  , Solidity.Stmt.expr
                      (Solidity.Expr.callWithOptions
                        (Solidity.Expr.member
                          (Solidity.Expr.ident "target")
                          "staticcall")
                        [Solidity.CallOption.named "gas"
                          (Solidity.Expr.assign
                            (Solidity.Expr.ident
                              "gasSeen")
                            AssignOp.assign
                            (Solidity.Expr.literal
                              (Solidity.Literal.number
                                "12")))]
                        [Solidity.Arg.positional
                          (Solidity.Expr.ident
                            "payload")])
                  , Solidity.Stmt.returnValues
                      (some
                        (Solidity.Expr.ident "gasSeen")) ]) } ] }

def checkedLowLevelStaticCallValueOptionContract :
    Solidity.ContractDecl :=
  { name := "CheckedBadStaticValue"
    items :=
      [ Solidity.ContractItem.function
          { name := some "badStaticValue"
            visibility := some Visibility.public_
            params :=
              [ { name := some "target", ty := Ty.address false }
              , { name := some "payload"
                  ty := Ty.bytes
                  location := some DataLocation.memory } ]
            returns :=
              [{ name := some "out"
                 ty := lowLevelCallReturnTy
                 location := some DataLocation.memory }]
            body :=
              some
                (Solidity.Stmt.returnValues
                  (some
                    (Solidity.Expr.callWithOptions
                      (Solidity.Expr.member
                        (Solidity.Expr.ident "target")
                        "staticcall")
                      [Solidity.CallOption.named "value"
                        (Solidity.Expr.literal
                          (Solidity.Literal.number "1"))]
                      [Solidity.Arg.positional
                        (Solidity.Expr.ident "payload")]))) } ] }

def checkedLowLevelDelegateCallValueOptionContract :
    Solidity.ContractDecl :=
  { name := "CheckedBadDelegateValue"
    items :=
      [ Solidity.ContractItem.function
          { name := some "badDelegateValue"
            visibility := some Visibility.public_
            params :=
              [ { name := some "target", ty := Ty.address false }
              , { name := some "payload"
                  ty := Ty.bytes
                  location := some DataLocation.memory } ]
            returns :=
              [{ name := some "out"
                 ty := lowLevelCallReturnTy
                 location := some DataLocation.memory }]
            body :=
              some
                (Solidity.Stmt.returnValues
                  (some
                    (Solidity.Expr.callWithOptions
                      (Solidity.Expr.member
                        (Solidity.Expr.ident "target")
                        "delegatecall")
                      [Solidity.CallOption.named "value"
                        (Solidity.Expr.literal
                          (Solidity.Literal.number "1"))]
                      [Solidity.Arg.positional
                        (Solidity.Expr.ident "payload")]))) } ] }

def checkedLowLevelCallMatches : Except TypeError Bool := do
  let contract ← ContractDecl.checkedContract checkedLowLevelCallContract
  let result ←
    CheckedContract.callFunctionWithContextFailOpen 16
      (SolidCore.Solidity.Source.responderOfResults
          [ { kind := SolidCore.Solidity.Source.LowLevelCallKind.call
              target := 0xbeef
              calldata := [1, 2, 3]
              success := true
              output := [9, 8] } ]
      []) contract "probe"
      (contract.core.context)
      SolidCore.Solidity.Source.State.empty
      [ SolidCore.Solidity.Source.Value.word 0xbeef
      , SolidCore.Solidity.Source.Value.bytes [1, 2, 3] ]
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _ [value] => do
      let (success, output) ← checkedDecodeLowLevelReturn value
      Except.ok
        (SolidCore.Solidity.Source.wordEq success 1 &&
          output == [9, 8])
  | _ => Except.ok false

def checkedLowLevelCallValueMatches : Except TypeError Bool := do
  let contract ← ContractDecl.checkedContract checkedLowLevelCallContract
  let result ←
    CheckedContract.callFunctionWithContextFailOpen 16
      (SolidCore.Solidity.Source.responderOfResults
          [ { kind := SolidCore.Solidity.Source.LowLevelCallKind.call
              target := 0xbeef
              calldata := [1, 2]
              value := 5
              gas? := some 1000000
              success := true
              output := [4, 5, 6] } ]
      []) contract "payWithOptions"
      (contract.core.context)
      SolidCore.Solidity.Source.State.empty []
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _ [value] => do
      let (success, output) ← checkedDecodeLowLevelReturn value
      Except.ok
        (SolidCore.Solidity.Source.wordEq success 1 &&
          output == [4, 5, 6])
  | _ => Except.ok false

def checkedLowLevelCallGasMismatchReturnsFalse :
    Except TypeError Bool := do
  let contract ← ContractDecl.checkedContract checkedLowLevelCallContract
  let result ←
    CheckedContract.callFunctionWithContextFailOpen 16
      (SolidCore.Solidity.Source.responderOfResults
          [ { kind := SolidCore.Solidity.Source.LowLevelCallKind.call
              target := 0xbeef
              calldata := [1, 2]
              value := 5
              gas? := some 999999
              success := true
              output := [4, 5, 6] } ]
      []) contract "payWithOptions"
      (contract.core.context)
      SolidCore.Solidity.Source.State.empty []
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _ [value] => do
      let (success, output) ← checkedDecodeLowLevelReturn value
      Except.ok
        (SolidCore.Solidity.Source.wordEq success 0 &&
          output == [])
  | _ => Except.ok false

def checkedLowLevelCallOptionEffectsMatches :
    Except TypeError Bool := do
  let contract ← ContractDecl.checkedContract checkedLowLevelCallContract
  let result ←
    CheckedContract.callFunctionWithContextFailOpen 32
      (SolidCore.Solidity.Source.responderOfResults
          [ { kind := SolidCore.Solidity.Source.LowLevelCallKind.call
              target := 0xbeef
              calldata := [1, 2]
              value := 5
              gas? := some 11
              success := true
              output := [4, 5, 6] } ]
      []) contract "payWithOptionEffects"
      (contract.core.context)
      SolidCore.Solidity.Source.State.empty []
  match result with
  | SolidCore.Solidity.Source.CallResult.returned state
      [ SolidCore.Solidity.Source.Value.word gasSeen
      , SolidCore.Solidity.Source.Value.word sent] =>
      let observed :=
        match state.externalInteractions with
        | [SolidCore.Solidity.Source.ExternalInteraction.lowLevelCall call] =>
            SolidCore.Solidity.Source.LowLevelCallResult.matches call
              SolidCore.Solidity.Source.LowLevelCallKind.call
              0xbeef [1, 2] 5 (some 11) &&
              call.success && call.output == [4, 5, 6]
        | _ => false
      Except.ok
        (observed &&
          SolidCore.Solidity.Source.wordEq gasSeen 11 &&
          SolidCore.Solidity.Source.wordEq sent 5)
  | _ => Except.ok false

def checkedLowLevelStaticDelegateMatches :
    Except TypeError Bool := do
  let contract ← ContractDecl.checkedContract checkedLowLevelCallContract
  let result ←
    CheckedContract.callFunctionWithContextFailOpen 16
      (SolidCore.Solidity.Source.responderOfResults
          [ { kind := SolidCore.Solidity.Source.LowLevelCallKind.staticcall
              target := 0xcafe
              calldata := [7, 7]
              gas? := some 50000
              success := true
              output := [1] }
          , { kind := SolidCore.Solidity.Source.LowLevelCallKind.delegatecall
              target := 0xcafe
              calldata := [7, 7]
              success := false
              output := [2, 3] } ]
      []) contract "probeBoth"
      (contract.core.context)
      SolidCore.Solidity.Source.State.empty
      [ SolidCore.Solidity.Source.Value.word 0xcafe
      , SolidCore.Solidity.Source.Value.bytes [7, 7] ]
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _
      [staticValue, delegateValue] => do
      let (staticSuccess, staticOutput) ←
        checkedDecodeLowLevelReturn staticValue
      let (delegateSuccess, delegateOutput) ←
        checkedDecodeLowLevelReturn delegateValue
      Except.ok
        (SolidCore.Solidity.Source.wordEq staticSuccess 1 &&
          staticOutput == [1] &&
          SolidCore.Solidity.Source.wordEq delegateSuccess 0 &&
          delegateOutput == [2, 3])
  | _ => Except.ok false

def checkedLowLevelDelegateCallGasOptionMatches :
    Except TypeError Bool := do
  let contract ← ContractDecl.checkedContract checkedLowLevelCallContract
  let result ←
    CheckedContract.callFunctionWithContextFailOpen 16
      (SolidCore.Solidity.Source.responderOfResults
          [ { kind := SolidCore.Solidity.Source.LowLevelCallKind.delegatecall
              target := 0xcafe
              calldata := [7, 7]
              gas? := some 900
              success := true
              output := [9, 0] } ]
      []) contract "delegateGas"
      (contract.core.context)
      SolidCore.Solidity.Source.State.empty
      [ SolidCore.Solidity.Source.Value.word 0xcafe
      , SolidCore.Solidity.Source.Value.bytes [7, 7] ]
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _ [value] => do
      let (success, output) ← checkedDecodeLowLevelReturn value
      Except.ok
        (SolidCore.Solidity.Source.wordEq success 1 &&
          output == [9, 0])
  | _ => Except.ok false

def checkedLowLevelStaticCallOptionGasEffectsMatches :
    Except TypeError Bool := do
  let contract ← ContractDecl.checkedContract checkedLowLevelCallContract
  let result ←
    CheckedContract.callFunctionWithContextFailOpen 32
      (SolidCore.Solidity.Source.responderOfResults
          [ { kind := SolidCore.Solidity.Source.LowLevelCallKind.staticcall
              target := 0xcafe
              calldata := [7, 7]
              gas? := some 12
              success := true
              output := [1] } ]
      []) contract "staticGasExpr"
      (contract.core.context)
      SolidCore.Solidity.Source.State.empty
      [ SolidCore.Solidity.Source.Value.word 0xcafe
      , SolidCore.Solidity.Source.Value.bytes [7, 7] ]
  match result with
  | SolidCore.Solidity.Source.CallResult.returned state
      [SolidCore.Solidity.Source.Value.word gasSeen] =>
      let observed :=
        match state.externalInteractions with
        | [SolidCore.Solidity.Source.ExternalInteraction.lowLevelCall call] =>
            SolidCore.Solidity.Source.LowLevelCallResult.matches call
              SolidCore.Solidity.Source.LowLevelCallKind.staticcall
              0xcafe [7, 7] 0 (some 12) &&
              call.success && call.output == [1]
        | _ => false
      Except.ok
        (observed &&
          SolidCore.Solidity.Source.wordEq gasSeen 12)
  | _ => Except.ok false

def checkedLowLevelStaticCallValueOptionRejected : Bool :=
  Result.isError
    (ContractDecl.checkedContract
      checkedLowLevelStaticCallValueOptionContract)

def checkedLowLevelDelegateCallValueOptionRejected : Bool :=
  Result.isError
    (ContractDecl.checkedContract
      checkedLowLevelDelegateCallValueOptionContract)

def checkedLowLevelMissingResultMatches : Except TypeError Bool := do
  let contract ← ContractDecl.checkedContract checkedLowLevelCallContract
  let result ←
    CheckedContract.callFunctionWithContext 16 contract "probe"
      contract.core.context
      SolidCore.Solidity.Source.State.empty
      [ SolidCore.Solidity.Source.Value.word 0xbeef
      , SolidCore.Solidity.Source.Value.bytes [1, 2, 3] ]
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _ [value] => do
      let (success, output) ← checkedDecodeLowLevelReturn value
      Except.ok
        (SolidCore.Solidity.Source.wordEq success 0 &&
          output == [])
  | _ => Except.ok false

def checkedLowLevelCallAbiTyMatches : Except TypeError Bool := do
  let function ←
    ContractDecl.checkedCoreFunction checkedLowLevelCallContract "probe"
  match function.returns with
  | [{ ty := SolidCore.Solidity.Source.Ty.tuple
          [ SolidCore.Solidity.Source.Ty.bool
          , SolidCore.Solidity.Source.Ty.bytesCalldata ]
       .. }] =>
      Except.ok true
  | _ => Except.ok false

def checkedLowLevelSendMatches : Except TypeError Bool := do
  let program ← SourceUnit.checkedProgram lowLevelSendSource
  let contract ← CheckedProgram.contract program "LowLevelSend"
  let result ←
    CheckedContract.callFunctionWithContextFailOpen 16
      (SolidCore.Solidity.Source.responderOfResults
          [ { kind := SolidCore.Solidity.Source.LowLevelCallKind.call
              target := 0xbeef
              calldata := []
              value := 1
              gas? := some 2300
              success := true
              output := [] } ]
      []) contract "sendIt"
      (contract.core.context)
      SolidCore.Solidity.Source.State.empty
      [SolidCore.Solidity.Source.Value.word 0xbeef]
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _
      [SolidCore.Solidity.Source.Value.word ok] =>
      Except.ok (SolidCore.Solidity.Source.wordEq ok 1)
  | _ => Except.ok false

def checkedLowLevelSendFailureReturnsFalse :
    Except TypeError Bool := do
  let program ← SourceUnit.checkedProgram lowLevelSendSource
  let contract ← CheckedProgram.contract program "LowLevelSend"
  let result ←
    CheckedContract.callFunctionWithContextFailOpen 16
      (SolidCore.Solidity.Source.responderOfResults
          [ { kind := SolidCore.Solidity.Source.LowLevelCallKind.call
              target := 0xbeef
              calldata := []
              value := 1
              gas? := some 2300
              success := false
              output := [0xde, 0xad] } ]
      []) contract "sendIt"
      (contract.core.context)
      SolidCore.Solidity.Source.State.empty
      [SolidCore.Solidity.Source.Value.word 0xbeef]
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _
      [SolidCore.Solidity.Source.Value.word ok] =>
      Except.ok (SolidCore.Solidity.Source.wordEq ok 0)
  | _ => Except.ok false

def checkedLowLevelSendNonpayableAddressRejected : Bool :=
  Result.isError (SourceUnit.checkedProgram
    lowLevelSendNonpayableAddressSource)

def checkedLowLevelSendSignedAmountRejected : Bool :=
  Result.isError (SourceUnit.checkedProgram
    lowLevelSendSignedAmountSource)

def checkedLowLevelTransferSignedAmountRejected : Bool :=
  Result.isError (SourceUnit.checkedProgram
    lowLevelTransferSignedAmountSource)

def checkedTransferValueContract : Solidity.ContractDecl :=
  { name := "CheckedTransferValue"
    items :=
      [ Solidity.ContractItem.stateVar
          { name := "x", ty := Ty.uint 256 }
      , Solidity.ContractItem.function
          { name := some "pay"
            visibility := some Visibility.public_
            params :=
              [ { name := some "target", ty := Ty.address true }
              , { name := some "amount", ty := Ty.uint 256 } ]
            body :=
              some
                (Solidity.Stmt.block
                  [ Solidity.Stmt.expr
                      (Solidity.Expr.assign
                        (Solidity.Expr.ident "x")
                        AssignOp.assign
                        (Solidity.Expr.literal
                          (Solidity.Literal.number "1")))
                  , Solidity.Stmt.expr
                      (Solidity.Expr.call
                        (Solidity.Expr.member
                          (Solidity.Expr.ident "target")
                          "transfer")
                        [Solidity.Arg.positional
                          (Solidity.Expr.ident "amount")])
                  , Solidity.Stmt.expr
                      (Solidity.Expr.assign
                        (Solidity.Expr.ident "x")
                        AssignOp.assign
                        (Solidity.Expr.literal
                          (Solidity.Literal.number "2"))) ]) } ] }

def checkedTransferValueSuccessMatches : Except TypeError Bool := do
  let contract ← ContractDecl.checkedContract checkedTransferValueContract
  let result ←
    CheckedContract.callFunctionWithContextFailOpen 16
      (SolidCore.Solidity.Source.responderOfResults
          [ { kind := SolidCore.Solidity.Source.LowLevelCallKind.call
              target := 0xbeef
              calldata := []
              value := 5
              gas? := some 2300
              success := true
              output := [] } ]
      []) contract "pay"
      (contract.core.context)
      SolidCore.Solidity.Source.State.empty
      [ SolidCore.Solidity.Source.Value.word 0xbeef
      , SolidCore.Solidity.Source.Value.word 5 ]
  match result with
  | SolidCore.Solidity.Source.CallResult.returned state [] =>
      Except.ok (SolidCore.Solidity.Source.wordEq (state.loadSlot 0) 2)
  | _ => Except.ok false

def checkedTransferValueFailureReverts : Except TypeError Bool := do
  let contract ← ContractDecl.checkedContract checkedTransferValueContract
  let result ←
    CheckedContract.callFunctionWithContextFailOpen 16
      (SolidCore.Solidity.Source.responderOfResults
          [ { kind := SolidCore.Solidity.Source.LowLevelCallKind.call
              target := 0xbeef
              calldata := []
              value := 5
              gas? := some 2300
              success := false
              output := [0xba, 0xad] } ]
      []) contract "pay"
      (contract.core.context)
      SolidCore.Solidity.Source.State.empty
      [ SolidCore.Solidity.Source.Value.word 0xbeef
      , SolidCore.Solidity.Source.Value.word 5 ]
  match result with
  | SolidCore.Solidity.Source.CallResult.reverted state
      (SolidCore.Solidity.Source.RevertData.raw bytes) =>
      Except.ok
        (SolidCore.Solidity.Source.wordEq (state.loadSlot 0) 0 &&
          bytes == [0xba, 0xad])
  | _ => Except.ok false

def checkedPrecompileStaticcallContract :
    Solidity.ContractDecl :=
  { name := "CheckedPrecompileStaticcall"
    items :=
      [ Solidity.ContractItem.function
          { name := some "hashAndProbe"
            visibility := some Visibility.public_
            mutability := StateMutability.view
            returns :=
              [ { name := some "sha", ty := Ty.bytesN 32 }
              , { name := some "probe"
                  ty := lowLevelCallReturnTy
                  location := some DataLocation.memory } ]
            body :=
              some
                (Solidity.Stmt.returnValues
                  (some
                    (Solidity.Expr.tuple
                      [ Solidity.TupleItem.value
                          (Solidity.Expr.call
                            (Solidity.Expr.ident "sha256")
                            [Solidity.Arg.positional
                              (Solidity.Expr.literal
                                (Solidity.Literal.bytes
                                  [1, 2]))])
                      , Solidity.TupleItem.value
                          (Solidity.Expr.call
                            (Solidity.Expr.member
                              (Solidity.Expr.literal
                                (Solidity.Literal.address
                                  (SolidCore.Solidity.Shared.Precompile.address
                                    SolidCore.Solidity.Shared.Precompile.Kind.sha256)))
                              "staticcall")
                            [Solidity.Arg.positional
                              (Solidity.Expr.literal
                                (Solidity.Literal.bytes
                                  [1, 2]))]) ]))) } ] }

def checkedPrecompileStaticcallMatches :
    Except TypeError Bool := do
  let contract ←
    ContractDecl.checkedContract checkedPrecompileStaticcallContract
  let expectedOutput :=
    SolidCore.Solidity.Source.wordToBytesBE
      SolidCore.Solidity.Source.wordBytes 0xaaaa
  let result ←
    CheckedContract.callFunctionWithContextFailOpen 16
      (SolidCore.Solidity.Source.responderOfResults
          [ Executable.Examples.successfulPrecompileWordCall
              SolidCore.Solidity.Shared.Precompile.Kind.sha256 [1, 2] 0xaaaa ]
      []) contract "hashAndProbe"
      (contract.core.context)
      SolidCore.Solidity.Source.State.empty []
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _
      [SolidCore.Solidity.Source.Value.word sha, probe] => do
      let (success, output) ← checkedDecodeLowLevelReturn probe
      Except.ok
        (SolidCore.Solidity.Source.wordEq sha 0xaaaa &&
          SolidCore.Solidity.Source.wordEq success 1 &&
          output == expectedOutput)
  | _ => Except.ok false

def checkedCreatedChildTy : Ty :=
  Ty.user { segments := ["CheckedCreatedChild"] }

def checkedCreatedChildContract : Solidity.ContractDecl :=
  { name := "CheckedCreatedChild"
    items :=
      [ Solidity.ContractItem.function
          (seedConstructor StateMutability.nonpayable) ] }

def checkedNamedCreatedChildTy : Ty :=
  Ty.user { segments := ["CheckedNamedCreatedChild"] }

def checkedNamedCreatedChildContract :
    Solidity.ContractDecl :=
  { name := "CheckedNamedCreatedChild"
    items :=
      [ Solidity.ContractItem.function
          { kind := FunctionKind.constructor
            params :=
              [ { name := some "amount", ty := Ty.uint 256 }
              , { name := some "bonus", ty := Ty.uint 256 } ]
            mutability := StateMutability.payable
            body := some Solidity.Stmt.empty } ] }

def checkedContractCreationCaller :
    Solidity.ContractDecl :=
  { name := "CheckedCreateCaller"
    items :=
      [ Solidity.ContractItem.stateVar
          { name := "x", ty := Ty.uint 256 }
      , Solidity.ContractItem.function
          { name := some "make"
            visibility := some Visibility.public_
            params := [{ name := some "seed", ty := Ty.uint 256 }]
            returns :=
              [{ name := some "created", ty := checkedCreatedChildTy }]
            body :=
              some
                (Solidity.Stmt.returnValues
                  (some
                    (Solidity.Expr.newExpr
                      checkedCreatedChildTy
                      [Solidity.Arg.positional
                        (Solidity.Expr.ident "seed")]))) }
      , Solidity.ContractItem.function
          { name := some "makeNamed"
            visibility := some Visibility.public_
            params :=
              [ { name := some "amount", ty := Ty.uint 256 }
              , { name := some "bonus", ty := Ty.uint 256 } ]
            returns :=
              [{ name := some "created", ty := checkedNamedCreatedChildTy }]
            body :=
              some
                (Solidity.Stmt.returnValues
                  (some
                    (Solidity.Expr.newExpr
                      checkedNamedCreatedChildTy
                      [ Solidity.Arg.named "bonus"
                          (Solidity.Expr.ident "bonus")
                      , Solidity.Arg.named "amount"
                          (Solidity.Expr.ident "amount") ]))) }
      , Solidity.ContractItem.function
          { name := some "makeNamedSalted"
            visibility := some Visibility.public_
            params :=
              [ { name := some "amount", ty := Ty.uint 256 }
              , { name := some "bonus", ty := Ty.uint 256 }
              , { name := some "payment", ty := Ty.uint 256 }
              , { name := some "salt", ty := Ty.bytesN 32 } ]
            returns :=
              [{ name := some "created", ty := checkedNamedCreatedChildTy }]
            body :=
              some
                (Solidity.Stmt.returnValues
                  (some
                    (Solidity.Expr.callWithOptions
                      (Solidity.Expr.newExpr
                        checkedNamedCreatedChildTy [])
                      [ Solidity.CallOption.named "value"
                          (Solidity.Expr.ident "payment")
                      , Solidity.CallOption.named "salt"
                          (Solidity.Expr.ident "salt") ]
                      [ Solidity.Arg.named "bonus"
                          (Solidity.Expr.ident "bonus")
                      , Solidity.Arg.named "amount"
                          (Solidity.Expr.ident "amount") ]))) }
      , Solidity.ContractItem.function
          { name := some "makeFailure"
            visibility := some Visibility.public_
            body :=
              some
                (Solidity.Stmt.block
                  [ Solidity.Stmt.expr
                      (Solidity.Expr.assign
                        (Solidity.Expr.ident "x")
                        AssignOp.assign
                        (Solidity.Expr.literal
                          (Solidity.Literal.number "1")))
                  , Solidity.Stmt.expr
                      (Solidity.Expr.newExpr
                        checkedCreatedChildTy
                        [Solidity.Arg.positional
                          (Solidity.Expr.literal
                            (Solidity.Literal.number "7"))])
                  , Solidity.Stmt.expr
                      (Solidity.Expr.assign
                        (Solidity.Expr.ident "x")
                        AssignOp.assign
                        (Solidity.Expr.literal
                          (Solidity.Literal.number "2"))) ]) }
      , Solidity.ContractItem.function
          { name := some "tryMake"
            visibility := some Visibility.public_
            returns := [{ name := some "out", ty := Ty.uint 256 }]
            body :=
              some
                (Solidity.Stmt.block
                  [ Solidity.Stmt.tryCatch
                      (Solidity.Expr.newExpr
                        checkedCreatedChildTy
                        [Solidity.Arg.positional
                          (Solidity.Expr.literal
                            (Solidity.Literal.number "7"))])
                      [ Solidity.CatchClause.clause none []
                          (Solidity.Stmt.returnValues
                            (some
                              (Solidity.Expr.literal
                                (Solidity.Literal.number
                                  "0")))) ]
                  , Solidity.Stmt.returnValues
                      (some
                        (Solidity.Expr.literal
                          (Solidity.Literal.number "1"))) ]) } ] }

def checkedDuplicateNamedCreateCaller :
    Solidity.ContractDecl :=
  { name := "CheckedDuplicateNamedCreateCaller"
    items :=
      [ Solidity.ContractItem.function
          { name := some "badNamed"
            visibility := some Visibility.public_
            params :=
              [ { name := some "amount", ty := Ty.uint 256 }
              , { name := some "bonus", ty := Ty.uint 256 } ]
            returns :=
              [{ name := some "created", ty := checkedNamedCreatedChildTy }]
            body :=
              some
                (Solidity.Stmt.returnValues
                  (some
                    (Solidity.Expr.newExpr
                      checkedNamedCreatedChildTy
                      [ Solidity.Arg.named "amount"
                          (Solidity.Expr.ident "amount")
                      , Solidity.Arg.named "amount"
                          (Solidity.Expr.ident "bonus") ]))) } ] }

def checkedContractCreationSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          checkedCreatedChildContract
      , Solidity.SourceItem.contract
          checkedNamedCreatedChildContract
      , Solidity.SourceItem.contract
          checkedContractCreationCaller ] }

def checkedContractCreationMatches : Except TypeError Bool := do
  let constructorArgs ←
    checkedAbiEncodeValues
      [SolidCore.Solidity.Source.Ty.uint256]
      [SolidCore.Solidity.Source.Value.word 7]
  let program ← SourceUnit.checkedProgram checkedContractCreationSource
  let contract ← CheckedProgram.contract program "CheckedCreateCaller"
  let result ←
    CheckedContract.callFunctionWithContextFailOpen 16
      (SolidCore.Solidity.Source.responderOfResults
      []
          [ { contractName := "CheckedCreatedChild"
              constructorArgs := constructorArgs
              success := true
              address := 0xc0de } ]) contract "make"
      (contract.core.context)
      SolidCore.Solidity.Source.State.empty
      [SolidCore.Solidity.Source.Value.word 7]
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _
      [SolidCore.Solidity.Source.Value.word address] =>
      Except.ok (SolidCore.Solidity.Source.wordEq address 0xc0de)
  | _ => Except.ok false

def checkedContractCreationSuccessMatches : Except TypeError Bool :=
  checkedContractCreationMatches

def checkedContractCreationNamedArgsMatches :
    Except TypeError Bool := do
  let constructorArgs ←
    checkedAbiEncodeValues
      [ SolidCore.Solidity.Source.Ty.uint256
      , SolidCore.Solidity.Source.Ty.uint256 ]
      [ SolidCore.Solidity.Source.Value.word 40
      , SolidCore.Solidity.Source.Value.word 2 ]
  let program ← SourceUnit.checkedProgram checkedContractCreationSource
  let contract ← CheckedProgram.contract program "CheckedCreateCaller"
  let result ←
    CheckedContract.callFunctionWithContextFailOpen 16
      (SolidCore.Solidity.Source.responderOfResults
      []
          [ { contractName := "CheckedNamedCreatedChild"
              constructorArgs := constructorArgs
              success := true
              address := 0xc0de } ]) contract "makeNamed"
      (contract.core.context)
      SolidCore.Solidity.Source.State.empty
      [ SolidCore.Solidity.Source.Value.word 40
      , SolidCore.Solidity.Source.Value.word 2 ]
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _
      [SolidCore.Solidity.Source.Value.word address] =>
      Except.ok (SolidCore.Solidity.Source.wordEq address 0xc0de)
  | _ => Except.ok false

def checkedContractCreationNamedArgsReorderedMatches :
    Except TypeError Bool :=
  checkedContractCreationNamedArgsMatches

def checkedContractCreationValueSaltMatches :
    Except TypeError Bool := do
  let constructorArgs ←
    checkedAbiEncodeValues
      [ SolidCore.Solidity.Source.Ty.uint256
      , SolidCore.Solidity.Source.Ty.uint256 ]
      [ SolidCore.Solidity.Source.Value.word 40
      , SolidCore.Solidity.Source.Value.word 2 ]
  let program ← SourceUnit.checkedProgram checkedContractCreationSource
  let contract ← CheckedProgram.contract program "CheckedCreateCaller"
  let result ←
    CheckedContract.callFunctionWithContextFailOpen 16
      (SolidCore.Solidity.Source.responderOfResults
      []
          [ { contractName := "CheckedNamedCreatedChild"
              constructorArgs := constructorArgs
              value := 5
              salt? := some 0x1234
              success := true
              address := 0xcafe } ]) contract "makeNamedSalted"
      (contract.core.context)
      SolidCore.Solidity.Source.State.empty
      [ SolidCore.Solidity.Source.Value.word 40
      , SolidCore.Solidity.Source.Value.word 2
      , SolidCore.Solidity.Source.Value.word 5
      , SolidCore.Solidity.Source.Value.word 0x1234 ]
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _
      [SolidCore.Solidity.Source.Value.word address] =>
      Except.ok (SolidCore.Solidity.Source.wordEq address 0xcafe)
  | _ => Except.ok false

def checkedContractCreationNamedArgsWithOptionsMatches :
    Except TypeError Bool :=
  checkedContractCreationValueSaltMatches

def checkedContractCreationDuplicateNamedArgsRejected : Bool :=
  Result.isError
    (SourceUnit.checkedProgram
      { items :=
          [ Solidity.SourceItem.contract
              checkedNamedCreatedChildContract
          , Solidity.SourceItem.contract
              checkedDuplicateNamedCreateCaller ] })

def checkedContractCreationFailureReverts :
    Except TypeError Bool := do
  let constructorArgs ←
    checkedAbiEncodeValues
      [SolidCore.Solidity.Source.Ty.uint256]
      [SolidCore.Solidity.Source.Value.word 7]
  let program ← SourceUnit.checkedProgram checkedContractCreationSource
  let contract ← CheckedProgram.contract program "CheckedCreateCaller"
  let result ←
    CheckedContract.callFunctionWithContextFailOpen 16
      (SolidCore.Solidity.Source.responderOfResults
      []
          [ { contractName := "CheckedCreatedChild"
              constructorArgs := constructorArgs
              success := false
              output := [0xca, 0xfe] } ]) contract "makeFailure"
      (contract.core.context)
      SolidCore.Solidity.Source.State.empty []
  match result with
  | SolidCore.Solidity.Source.CallResult.reverted state
      (SolidCore.Solidity.Source.RevertData.raw bytes) =>
      Except.ok
        (SolidCore.Solidity.Source.wordEq (state.loadSlot 0) 0 &&
          bytes == [0xca, 0xfe])
  | _ => Except.ok false

def checkedContractCreationMissingResultReverts :
    Except TypeError Bool := do
  let program ← SourceUnit.checkedProgram checkedContractCreationSource
  let contract ← CheckedProgram.contract program "CheckedCreateCaller"
  let result ←
    CheckedContract.callFunctionWithContext 16 contract "make"
      contract.core.context
      SolidCore.Solidity.Source.State.empty
      [SolidCore.Solidity.Source.Value.word 7]
  match result with
  | SolidCore.Solidity.Source.CallResult.reverted _
      SolidCore.Solidity.Source.RevertData.empty =>
      Except.ok true
  | _ => Except.ok false

def checkedTryCatchContractCreationSuccessMatches :
    Except TypeError Bool := do
  let constructorArgs ←
    checkedAbiEncodeValues
      [SolidCore.Solidity.Source.Ty.uint256]
      [SolidCore.Solidity.Source.Value.word 7]
  let program ← SourceUnit.checkedProgram checkedContractCreationSource
  let contract ← CheckedProgram.contract program "CheckedCreateCaller"
  let result ←
    CheckedContract.callFunctionWithContextFailOpen 16
      (SolidCore.Solidity.Source.responderOfResults
      []
          [ { contractName := "CheckedCreatedChild"
              constructorArgs := constructorArgs
              success := true
              address := 0xc0de } ]) contract "tryMake"
      (contract.core.context)
      SolidCore.Solidity.Source.State.empty []
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _
      [SolidCore.Solidity.Source.Value.word value] =>
      Except.ok (SolidCore.Solidity.Source.wordEq value 1)
  | _ => Except.ok false

def checkedTryCatchContractCreationFailureMatches :
    Except TypeError Bool := do
  let constructorArgs ←
    checkedAbiEncodeValues
      [SolidCore.Solidity.Source.Ty.uint256]
      [SolidCore.Solidity.Source.Value.word 7]
  let program ← SourceUnit.checkedProgram checkedContractCreationSource
  let contract ← CheckedProgram.contract program "CheckedCreateCaller"
  let result ←
    CheckedContract.callFunctionWithContextFailOpen 16
      (SolidCore.Solidity.Source.responderOfResults
      []
          [ { contractName := "CheckedCreatedChild"
              constructorArgs := constructorArgs
              success := false
              output := [0xca, 0xfe] } ]) contract "tryMake"
      (contract.core.context)
      SolidCore.Solidity.Source.State.empty []
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _
      [SolidCore.Solidity.Source.Value.word value] =>
      Except.ok (SolidCore.Solidity.Source.wordEq value 0)
  | _ => Except.ok false

def checkedTryOperandTargetTy : Ty :=
  Ty.user { segments := ["CheckedTryOperandTarget"] }

def checkedTryOperandTargetContract :
    Solidity.ContractDecl :=
  { name := "CheckedTryOperandTarget"
    kind := ContractKind.interface
    items :=
      [ ContractItem.function
          { name := some "ping"
            visibility := some Visibility.external_
            mutability := StateMutability.payable
            params := [{ name := some "x", ty := Ty.uint 256 }]
            returns := [{ name := some "out", ty := Ty.uint 256 }] } ] }

def checkedTryExternalCallOperandEffectsContract :
    Solidity.ContractDecl :=
  { name := "CheckedTryExternalCallOperandEffects"
    items :=
      [ ContractItem.function
          { name := some "run"
            visibility := some Visibility.public_
            returns :=
              [ { name := some "target", ty := Ty.address false }
              , { name := some "value", ty := Ty.uint 256 }
              , { name := some "arg", ty := Ty.uint 256 }
              , { name := some "out", ty := Ty.uint 256 } ]
            body :=
              some
                (Solidity.Stmt.block
                  [ Solidity.Stmt.varDecl
                      [{ name := some "target"
                         ty := some checkedTryOperandTargetTy }]
                      (some
                        (Solidity.Expr.call
                          (Solidity.Expr.typeName
                            checkedTryOperandTargetTy)
                          [ Solidity.Arg.positional
                              (Solidity.Expr.literal
                                (Solidity.Literal.address 0)) ]))
                  , Solidity.Stmt.varDecl
                      [{ name := some "value", ty := some (Ty.uint 256) }]
                      (some
                        (Solidity.Expr.literal
                          (Solidity.Literal.number "0")))
                  , Solidity.Stmt.varDecl
                      [{ name := some "arg", ty := some (Ty.uint 256) }]
                      (some
                        (Solidity.Expr.literal
                          (Solidity.Literal.number "0")))
                  , Solidity.Stmt.tryCatchReturns
                      (Solidity.Expr.callWithOptions
                        (Solidity.Expr.member
                          (Solidity.Expr.assign
                            (Solidity.Expr.ident "target")
                            AssignOp.assign
                            (Solidity.Expr.call
                              (Solidity.Expr.typeName
                                checkedTryOperandTargetTy)
                              [ Solidity.Arg.positional
                                  (Solidity.Expr.literal
                                    (Solidity.Literal.address
                                      51966)) ]))
                          "ping")
                        [ Solidity.CallOption.named "value"
                            (Solidity.Expr.assign
                              (Solidity.Expr.ident "value")
                              AssignOp.assign
                              (Solidity.Expr.literal
                                (Solidity.Literal.number "7"))) ]
                        [ Solidity.Arg.positional
                            (Solidity.Expr.call
                              (Solidity.Expr.typeName
                                (Ty.uint 256))
                              [ Solidity.Arg.positional
                                  (Solidity.Expr.assign
                                    (Solidity.Expr.ident "arg")
                                    AssignOp.assign
                                    (Solidity.Expr.literal
                                      (Solidity.Literal.number
                                        "3"))) ]) ])
                      [{ name := some "out", ty := Ty.uint 256 }]
                      (Solidity.Stmt.returnValues
                        (some
                          (Solidity.Expr.tuple
                            [ Solidity.TupleItem.value
                                (Solidity.Expr.call
                                  (Solidity.Expr.typeName
                                    (Ty.address false))
                                  [ Solidity.Arg.positional
                                      (Solidity.Expr.ident
                                        "target") ])
                            , Solidity.TupleItem.value
                                (Solidity.Expr.ident "value")
                            , Solidity.TupleItem.value
                                (Solidity.Expr.ident "arg")
                            , Solidity.TupleItem.value
                                (Solidity.Expr.ident "out") ])))
                      [ Solidity.CatchClause.clause none []
                          (Solidity.Stmt.returnValues
                            (some
                              (Solidity.Expr.tuple
                                [ Solidity.TupleItem.value
                                    (Solidity.Expr.literal
                                      (Solidity.Literal.address
                                        0))
                                , Solidity.TupleItem.value
                                    (Solidity.Expr.literal
                                      (Solidity.Literal.number
                                        "0"))
                                , Solidity.TupleItem.value
                                    (Solidity.Expr.literal
                                      (Solidity.Literal.number
                                        "0"))
                                , Solidity.TupleItem.value
                                    (Solidity.Expr.literal
                                      (Solidity.Literal.number
                                        "0")) ]))) ] ]) } ] }

def checkedTryOperandMadeTy : Ty :=
  Ty.user { segments := ["CheckedTryOperandMade"] }

def checkedTryOperandMadeContract : Solidity.ContractDecl :=
  { name := "CheckedTryOperandMade"
    items :=
      [ ContractItem.function
          { kind := FunctionKind.constructor
            params := [{ name := some "x", ty := Ty.uint 256 }]
            mutability := StateMutability.payable
            body := some Solidity.Stmt.empty } ] }

def checkedTryContractCreateOperandEffectsContract :
    Solidity.ContractDecl :=
  { name := "CheckedTryContractCreateOperandEffects"
    items :=
      [ ContractItem.function
          { name := some "run"
            visibility := some Visibility.public_
            returns :=
              [ { name := some "value", ty := Ty.uint 256 }
              , { name := some "salt", ty := Ty.bytesN 32 }
              , { name := some "arg", ty := Ty.uint 256 }
              , { name := some "made", ty := Ty.address false } ]
            body :=
              some
                (Solidity.Stmt.block
                  [ Solidity.Stmt.varDecl
                      [{ name := some "value", ty := some (Ty.uint 256) }]
                      (some
                        (Solidity.Expr.literal
                          (Solidity.Literal.number "0")))
                  , Solidity.Stmt.varDecl
                      [{ name := some "salt", ty := some (Ty.bytesN 32) }]
                      (some
                        (Solidity.Expr.call
                          (Solidity.Expr.typeName
                            (Ty.bytesN 32))
                          [ Solidity.Arg.positional
                              (Solidity.Expr.literal
                                (Solidity.Literal.number
                                  "0")) ]))
                  , Solidity.Stmt.varDecl
                      [{ name := some "arg", ty := some (Ty.uint 256) }]
                      (some
                        (Solidity.Expr.literal
                          (Solidity.Literal.number "0")))
                  , Solidity.Stmt.tryCatchReturns
                      (Solidity.Expr.callWithOptions
                        (Solidity.Expr.newExpr
                          checkedTryOperandMadeTy [])
                        [ Solidity.CallOption.named "value"
                            (Solidity.Expr.assign
                              (Solidity.Expr.ident "value")
                              AssignOp.assign
                              (Solidity.Expr.literal
                                (Solidity.Literal.number "7")))
                        , Solidity.CallOption.named "salt"
                            (Solidity.Expr.assign
                              (Solidity.Expr.ident "salt")
                              AssignOp.assign
                              (Solidity.Expr.call
                                (Solidity.Expr.typeName
                                  (Ty.bytesN 32))
                                [ Solidity.Arg.positional
                                    (Solidity.Expr.literal
                                      (Solidity.Literal.hexString
                                        "0000000000000000000000000000000000000000000000000000000000000005")) ])) ]
                        [ Solidity.Arg.positional
                            (Solidity.Expr.call
                              (Solidity.Expr.typeName
                                (Ty.uint 256))
                              [ Solidity.Arg.positional
                                  (Solidity.Expr.assign
                                    (Solidity.Expr.ident "arg")
                                    AssignOp.assign
                                    (Solidity.Expr.literal
                                      (Solidity.Literal.number
                                        "3"))) ]) ])
                      [{ name := some "made"
                         ty := checkedTryOperandMadeTy }]
                      (Solidity.Stmt.returnValues
                        (some
                          (Solidity.Expr.tuple
                            [ Solidity.TupleItem.value
                                (Solidity.Expr.ident "value")
                            , Solidity.TupleItem.value
                                (Solidity.Expr.ident "salt")
                            , Solidity.TupleItem.value
                                (Solidity.Expr.ident "arg")
                            , Solidity.TupleItem.value
                                (Solidity.Expr.call
                                  (Solidity.Expr.typeName
                                    (Ty.address false))
                                  [ Solidity.Arg.positional
                                      (Solidity.Expr.ident
                                        "made") ]) ])))
                      [ Solidity.CatchClause.clause none []
                          (Solidity.Stmt.returnValues
                            (some
                              (Solidity.Expr.tuple
                                [ Solidity.TupleItem.value
                                    (Solidity.Expr.literal
                                      (Solidity.Literal.number
                                        "0"))
                                , Solidity.TupleItem.value
                                    (Solidity.Expr.call
                                      (Solidity.Expr.typeName
                                        (Ty.bytesN 32))
                                      [ Solidity.Arg.positional
                                          (Solidity.Expr.literal
                                            (Solidity.Literal.number
                                              "0")) ])
                                , Solidity.TupleItem.value
                                    (Solidity.Expr.literal
                                      (Solidity.Literal.number
                                        "0"))
                                , Solidity.TupleItem.value
                                    (Solidity.Expr.literal
                                      (Solidity.Literal.address
                                        0)) ]))) ] ]) } ] }

def checkedTryOperandEffectsUnit : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          checkedTryOperandTargetContract
      , Solidity.SourceItem.contract
          checkedTryExternalCallOperandEffectsContract
      , Solidity.SourceItem.contract
          checkedTryOperandMadeContract
      , Solidity.SourceItem.contract
          checkedTryContractCreateOperandEffectsContract ] }

def checkedTryOperandEffectsUnitAccepted : Bool :=
  Result.isOk
    (TypecheckedInput.checkedSourceUnit checkedTryOperandEffectsUnit)

def checkedTryExternalCallOperandEffectsMatches :
    Except TypeError Bool := do
  let callData ←
    checkedHighLevelExternalCalldata "ping(uint256)"
      [SolidCore.Solidity.Source.Ty.uint256]
      [SolidCore.Solidity.Source.Value.word 3]
  let output ← checkedHighLevelExternalWordOutput 99
  let result ←
    checkedSourceFunctionCallWithContextFailOpen 32
      (SolidCore.Solidity.Source.responderOfResults
          [ { kind := SolidCore.Solidity.Source.LowLevelCallKind.call
              target := 51966
              calldata := callData
              value := 7
              success := true
              output := output } ]
      []) checkedTryOperandEffectsUnit
      "CheckedTryExternalCallOperandEffects" "run"
      (SolidCore.Solidity.Source.Context.empty)
      SolidCore.Solidity.Source.State.empty []
  match result with
  | SolidCore.Solidity.Source.CallResult.returned state
      [ SolidCore.Solidity.Source.Value.word target
      , SolidCore.Solidity.Source.Value.word value
      , SolidCore.Solidity.Source.Value.word arg
      , SolidCore.Solidity.Source.Value.word out ] =>
      let observed :=
        match state.externalInteractions with
        | [SolidCore.Solidity.Source.ExternalInteraction.lowLevelCall call] =>
            SolidCore.Solidity.Source.LowLevelCallResult.matches call
              SolidCore.Solidity.Source.LowLevelCallKind.call
              51966 callData 7 none &&
              call.success && call.output == output
        | _ => false
      Except.ok
        (observed &&
          SolidCore.Solidity.Source.wordEq target 51966 &&
          SolidCore.Solidity.Source.wordEq value 7 &&
          SolidCore.Solidity.Source.wordEq arg 3 &&
          SolidCore.Solidity.Source.wordEq out 99)
  | _ => Except.ok false

def checkedTryContractCreateOperandEffectsMatches :
    Except TypeError Bool := do
  let constructorArgs ←
    checkedAbiEncodeValues
      [SolidCore.Solidity.Source.Ty.uint256]
      [SolidCore.Solidity.Source.Value.word 3]
  let result ←
    checkedSourceFunctionCallWithContextFailOpen 32
      (SolidCore.Solidity.Source.responderOfResults
      []
          [ { contractName := "CheckedTryOperandMade"
              constructorArgs := constructorArgs
              value := 7
              salt? := some 5
              success := true
              address := 51966
              output := [] } ]) checkedTryOperandEffectsUnit
      "CheckedTryContractCreateOperandEffects" "run"
      (SolidCore.Solidity.Source.Context.empty)
      SolidCore.Solidity.Source.State.empty []
  match result with
  | SolidCore.Solidity.Source.CallResult.returned state
      [ SolidCore.Solidity.Source.Value.word value
      , SolidCore.Solidity.Source.Value.word salt
      , SolidCore.Solidity.Source.Value.word arg
      , SolidCore.Solidity.Source.Value.word made ] =>
      let observed :=
        match state.externalInteractions with
        | [SolidCore.Solidity.Source.ExternalInteraction.contractCreation create] =>
            SolidCore.Solidity.Source.ContractCreationResult.matches
              create "CheckedTryOperandMade" constructorArgs 7 (some 5) &&
              create.success &&
              SolidCore.Solidity.Source.wordEq create.address 51966
        | _ => false
      Except.ok
        (observed &&
          SolidCore.Solidity.Source.wordEq value 7 &&
          SolidCore.Solidity.Source.wordEq salt 5 &&
          SolidCore.Solidity.Source.wordEq arg 3 &&
          SolidCore.Solidity.Source.wordEq made 51966)
  | _ => Except.ok false

def checkedBadConstructorTypeRejected : Bool :=
  Result.isError (SourceUnit.checkedProgram badConstructorTypeSource)

def checkedMissingConstructorArgRejected : Bool :=
  Result.isError (SourceUnit.checkedProgram missingConstructorArgSource)

def checkedUintSaltConstructorCreateRejected : Bool :=
  Result.isError (SourceUnit.checkedProgram uintSaltConstructorCreateSource)

def checkedLiteralSaltConstructorCreateRejected : Bool :=
  Result.isError (SourceUnit.checkedProgram literalSaltConstructorCreateSource)

def checkedNonpayableConstructorValueRejected : Bool :=
  Result.isError (SourceUnit.checkedProgram nonpayableConstructorValueSource)

def checkedViewCreatesContractRejected : Bool :=
  Result.isError (SourceUnit.checkedProgram viewCreatesContractSource)

def checkedTransientStorageContract : Solidity.ContractDecl :=
  { name := "CheckedTransientStorage"
    items :=
      [ Solidity.ContractItem.stateVar
          { name := "persistent", ty := Ty.uint 256 }
      , Solidity.ContractItem.stateVar
          { name := "scratch"
            ty := Ty.uint 256
            visibility := some Visibility.public_
            mutability := VarMutability.transient }
      , Solidity.ContractItem.function
          { name := some "setBoth"
            visibility := some Visibility.public_
            returns := [{ name := some "out", ty := Ty.uint 256 }]
            body :=
              some
                (Solidity.Stmt.block
                  [ Solidity.Stmt.expr
                      (Solidity.Expr.assign
                        (Solidity.Expr.ident "persistent")
                        AssignOp.assign
                        (Solidity.Expr.literal
                          (Solidity.Literal.number "7")))
                  , Solidity.Stmt.expr
                      (Solidity.Expr.assign
                        (Solidity.Expr.ident "scratch")
                        AssignOp.assign
                        (Solidity.Expr.literal
                          (Solidity.Literal.number "9")))
                  , Solidity.Stmt.returnValues
                      (some
                        (Solidity.Expr.binary BinaryOp.add
                          (Solidity.Expr.binary BinaryOp.mul
                            (Solidity.Expr.ident "persistent")
                            (Solidity.Expr.literal
                              (Solidity.Literal.number "10")))
                          (Solidity.Expr.ident "scratch"))) ]) }
      , Solidity.ContractItem.function
          { name := some "readScratch"
            visibility := some Visibility.public_
            returns := [{ name := some "out", ty := Ty.uint 256 }]
            body :=
              some
                (Solidity.Stmt.returnValues
                  (some (Solidity.Expr.ident "scratch"))) }
      , Solidity.ContractItem.function
          { name := some "writeScratchThenRevert"
            visibility := some Visibility.public_
            params := [{ name := some "value", ty := Ty.uint 256 }]
            body :=
              some
                (Solidity.Stmt.block
                  [ Solidity.Stmt.expr
                      (Solidity.Expr.assign
                        (Solidity.Expr.ident "scratch")
                        AssignOp.assign
                        (Solidity.Expr.ident "value"))
                  , Solidity.Stmt.revertCall
                      (Solidity.Expr.call
                        (Solidity.Expr.ident "revert") []) ]) } ] }

def checkedTransientStorageContractAccepted : Bool :=
  Result.isOk (CheckedInput.program checkedTransientStorageContract)

def checkedTransientStorageSourceDisciplineAccepted : Bool :=
  Result.isOk (CheckedInput.program transientUintSource) &&
    checkedTransientStorageContractAccepted

def checkedTransientStorageSourceDisciplineRejected : Bool :=
  Result.isError (CheckedInput.program badTransientInitSource) &&
    Result.isError (CheckedInput.program badTransientStringSource)

def checkedTransientUintSourceFieldMarkedTransient :
    Except TypeError Bool := do
  let contract ← CheckedInput.contract transientUintSource "TransientUint"
  match contract.core.storageFields with
  | [field] =>
      Except.ok
        (field.name == "flag" &&
          SolidCore.Solidity.Source.wordEq field.slot 0 &&
          field.transient)
  | _ => Except.ok false

def checkedTransientIndependentSlotsMatches :
    Except TypeError Bool := do
  let result ←
    ContractDecl.checkedCall 32 checkedTransientStorageContract
      (SolidCore.Solidity.Source.CallTarget.name "setBoth")
      SolidCore.Solidity.Source.State.empty []
  match result with
  | SolidCore.Solidity.Source.CallResult.returned state
      [SolidCore.Solidity.Source.Value.word value] =>
      Except.ok
        (SolidCore.Solidity.Source.wordEq value 79 &&
          SolidCore.Solidity.Source.wordEq (state.loadSlot 0) 7 &&
          !state.transient.isEmpty)
  | _ => Except.ok false

def checkedTransientPublicGetterMatches :
    Except TypeError Bool := do
  let writeResult ←
    ContractDecl.checkedCall 32 checkedTransientStorageContract
      (SolidCore.Solidity.Source.CallTarget.name "setBoth")
      SolidCore.Solidity.Source.State.empty []
  let state ←
    match writeResult with
    | SolidCore.Solidity.Source.CallResult.returned state
        [SolidCore.Solidity.Source.Value.word value] =>
        if SolidCore.Solidity.Source.wordEq value 79 then
          Except.ok state
        else
          Except.error (executableFailure "transient write result")
    | _ => Except.error (executableFailure "transient write result")
  let result ←
    ContractDecl.checkedCall 32 checkedTransientStorageContract
      (SolidCore.Solidity.Source.CallTarget.name "scratch")
      state []
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _
      [SolidCore.Solidity.Source.Value.word value] =>
      Except.ok (SolidCore.Solidity.Source.wordEq value 9)
  | _ => Except.ok false

def checkedTransientPersistsWithinRawAbiFrameMatches :
    Except TypeError Bool := do
  let setCalldata ←
    checkedFunctionCalldata checkedTransientStorageContract "setBoth" []
  let readCalldata ←
    checkedFunctionCalldata checkedTransientStorageContract "readScratch" []
  let writeResult ←
    ContractDecl.checkedCallCalldata 32 checkedTransientStorageContract
      SolidCore.Solidity.Source.State.empty setCalldata
  let writeValue ← checkedDecodeUint256 writeResult.output
  let readResult ←
    ContractDecl.checkedCallCalldata 32 checkedTransientStorageContract
      writeResult.state readCalldata
  let readValue ← checkedDecodeUint256 readResult.output
  Except.ok
    (writeResult.success &&
      readResult.success &&
      SolidCore.Solidity.Source.wordEq writeValue 79 &&
      SolidCore.Solidity.Source.wordEq readValue 9 &&
      SolidCore.Solidity.Source.wordEq
        (readResult.state.loadSlot 0) 7 &&
      !readResult.state.transient.isEmpty)

def checkedTransientClearedAtAbiTransactionBoundaryMatches :
    Except TypeError Bool := do
  let setCalldata ←
    checkedFunctionCalldata checkedTransientStorageContract "setBoth" []
  let readCalldata ←
    checkedFunctionCalldata checkedTransientStorageContract "readScratch" []
  let writeResult ←
    ContractDecl.checkedCallCalldataTransaction 32
      checkedTransientStorageContract
      SolidCore.Solidity.Source.State.empty setCalldata
  let writeValue ← checkedDecodeUint256 writeResult.output
  let readResult ←
    ContractDecl.checkedCallCalldataTransaction 32
      checkedTransientStorageContract
      writeResult.state readCalldata
  let readValue ← checkedDecodeUint256 readResult.output
  Except.ok
    (writeResult.success &&
      readResult.success &&
      SolidCore.Solidity.Source.wordEq writeValue 79 &&
      SolidCore.Solidity.Source.wordEq readValue 0 &&
      SolidCore.Solidity.Source.wordEq
        (readResult.state.loadSlot 0) 7 &&
      writeResult.state.transient.isEmpty &&
      readResult.state.transient.isEmpty)

def checkedRevertedTransientWriteDropsWrite :
    Except TypeError Bool := do
  let result ←
    ContractDecl.checkedCall 32 checkedTransientStorageContract
      (SolidCore.Solidity.Source.CallTarget.name
        "writeScratchThenRevert")
      SolidCore.Solidity.Source.State.empty
      [SolidCore.Solidity.Source.Value.word 11]
  match result with
  | SolidCore.Solidity.Source.CallResult.reverted state _ => do
      let getter ←
        ContractDecl.checkedCall 32 checkedTransientStorageContract
          (SolidCore.Solidity.Source.CallTarget.name "scratch")
          state []
      match getter with
      | SolidCore.Solidity.Source.CallResult.returned _
          [SolidCore.Solidity.Source.Value.word value] =>
          Except.ok
            (SolidCore.Solidity.Source.wordEq value 0 &&
              state.transient.isEmpty)
      | _ => Except.ok false
  | _ => Except.ok false

def checkedRevertedTransientWritePreservesPriorValue :
    Except TypeError Bool := do
  let writeResult ←
    ContractDecl.checkedCall 32 checkedTransientStorageContract
      (SolidCore.Solidity.Source.CallTarget.name "setBoth")
      SolidCore.Solidity.Source.State.empty []
  let state ←
    match writeResult with
    | SolidCore.Solidity.Source.CallResult.returned state
        [SolidCore.Solidity.Source.Value.word value] =>
        if SolidCore.Solidity.Source.wordEq value 79 then
          Except.ok state
        else
          Except.error (executableFailure "transient write result")
    | _ => Except.error (executableFailure "transient write result")
  let result ←
    ContractDecl.checkedCall 32 checkedTransientStorageContract
      (SolidCore.Solidity.Source.CallTarget.name
        "writeScratchThenRevert")
      state [SolidCore.Solidity.Source.Value.word 11]
  match result with
  | SolidCore.Solidity.Source.CallResult.reverted revertedState _ => do
      let getter ←
        ContractDecl.checkedCall 32 checkedTransientStorageContract
          (SolidCore.Solidity.Source.CallTarget.name "scratch")
          revertedState []
      match getter with
      | SolidCore.Solidity.Source.CallResult.returned _
          [SolidCore.Solidity.Source.Value.word value] =>
          Except.ok
            (SolidCore.Solidity.Source.wordEq value 9 &&
              revertedState.transient == state.transient)
      | _ => Except.ok false
  | _ => Except.ok false

def checkedPackedTransientStorageContractAccepted : Bool :=
  Result.isOk
    (CheckedInput.program
      Executable.Examples.packedTransientStorageContract)

def checkedPackedTransientStorageFieldsMatch :
    Except TypeError Bool := do
  let contract ←
    CheckedInput.contract
      Executable.Examples.packedTransientStorageContract
      "PackedTransientStorage"
  match contract.core.storageFields with
  | [persistent, a, b, c, s, d] =>
      Except.ok
        (persistent.name == "persistent" &&
          SolidCore.Solidity.Source.wordEq persistent.slot 0 &&
          !persistent.transient &&
          a.name == "a" &&
          SolidCore.Solidity.Source.wordEq a.slot 0 &&
          a.transient &&
          a.packedOffset == 0 && a.packedBytes == 1 &&
          b.name == "b" &&
          SolidCore.Solidity.Source.wordEq b.slot 0 &&
          b.transient &&
          b.packedOffset == 1 && b.packedBytes == 2 &&
          c.name == "c" &&
          SolidCore.Solidity.Source.wordEq c.slot 0 &&
          c.transient &&
          c.packedOffset == 3 && c.packedBytes == 1 &&
          s.name == "s" &&
          SolidCore.Solidity.Source.wordEq s.slot 0 &&
          s.transient &&
          s.packedOffset == 4 && s.packedBytes == 1 &&
          s.packedSigned &&
          d.name == "d" &&
          SolidCore.Solidity.Source.wordEq d.slot 1 &&
          d.transient &&
          d.packedOffset == 0 &&
          d.packedBytes == SolidCore.Solidity.Source.wordBytes)
  | _ => Except.ok false

def checkedPackedTransientStorageState :
    Except TypeError CoreState := do
  let result ←
    ContractDecl.checkedCall 64
      Executable.Examples.packedTransientStorageContract
      (SolidCore.Solidity.Source.CallTarget.name "setAll")
      SolidCore.Solidity.Source.State.empty []
  match result with
  | SolidCore.Solidity.Source.CallResult.returned state
      [SolidCore.Solidity.Source.Value.word value] =>
      if SolidCore.Solidity.Source.wordEq value 9 then
        Except.ok state
      else
        Except.error
          (executableFailure "packed transient setAll result")
  | _ =>
      Except.error
        (executableFailure "packed transient setAll result")

def checkedPackedTransientStorageRawSlotMatches :
    Except TypeError Bool := do
  let state ← checkedPackedTransientStorageState
  Except.ok
    (SolidCore.Solidity.Source.wordEq (state.loadSlot 0) 7 &&
      SolidCore.Solidity.Source.wordEq
        (state.loadTransientSlot 0) 0xff01345612 &&
      SolidCore.Solidity.Source.wordEq
        (state.loadTransientSlot 1) 9)

def checkedPackedTransientStorageGetterMatches :
    Except TypeError Bool := do
  let state ← checkedPackedTransientStorageState
  let aResult ←
    ContractDecl.checkedCall 16
      Executable.Examples.packedTransientStorageContract
      (SolidCore.Solidity.Source.CallTarget.name "a") state []
  let bResult ←
    ContractDecl.checkedCall 16
      Executable.Examples.packedTransientStorageContract
      (SolidCore.Solidity.Source.CallTarget.name "b") state []
  let cResult ←
    ContractDecl.checkedCall 16
      Executable.Examples.packedTransientStorageContract
      (SolidCore.Solidity.Source.CallTarget.name "c") state []
  let sResult ←
    ContractDecl.checkedCall 16
      Executable.Examples.packedTransientStorageContract
      (SolidCore.Solidity.Source.CallTarget.name "s") state []
  let dResult ←
    ContractDecl.checkedCall 16
      Executable.Examples.packedTransientStorageContract
      (SolidCore.Solidity.Source.CallTarget.name "d") state []
  match aResult, bResult, cResult, sResult, dResult with
  | SolidCore.Solidity.Source.CallResult.returned _
      [SolidCore.Solidity.Source.Value.word a],
    SolidCore.Solidity.Source.CallResult.returned _
      [SolidCore.Solidity.Source.Value.word b],
    SolidCore.Solidity.Source.CallResult.returned _
      [SolidCore.Solidity.Source.Value.word c],
    SolidCore.Solidity.Source.CallResult.returned _
      [SolidCore.Solidity.Source.Value.int s],
    SolidCore.Solidity.Source.CallResult.returned _
      [SolidCore.Solidity.Source.Value.word d] =>
      Except.ok
        (SolidCore.Solidity.Source.wordEq a 0x12 &&
          SolidCore.Solidity.Source.wordEq b 0x3456 &&
          SolidCore.Solidity.Source.wordEq c 1 &&
          SolidCore.Solidity.Source.wordEq s
            (SolidCore.Solidity.Shared.signedToWord (-1)) &&
          SolidCore.Solidity.Source.wordEq d 9)
  | _, _, _, _, _ => Except.ok false

def checkedTransientStorageSemanticsMatch :
    Except TypeError Bool := do
  let sourceField ← checkedTransientUintSourceFieldMarkedTransient
  let independent ← checkedTransientIndependentSlotsMatches
  let getter ← checkedTransientPublicGetterMatches
  let rawFrame ← checkedTransientPersistsWithinRawAbiFrameMatches
  let transaction ←
    checkedTransientClearedAtAbiTransactionBoundaryMatches
  let dropsRevertedWrite ← checkedRevertedTransientWriteDropsWrite
  let preservesPrior ← checkedRevertedTransientWritePreservesPriorValue
  let packedFields ← checkedPackedTransientStorageFieldsMatch
  let packedRawSlots ← checkedPackedTransientStorageRawSlotMatches
  let packedGetters ← checkedPackedTransientStorageGetterMatches
  Except.ok
    (checkedTransientStorageSourceDisciplineAccepted &&
      checkedTransientStorageSourceDisciplineRejected &&
      checkedPackedTransientStorageContractAccepted &&
      sourceField && independent && getter && rawFrame && transaction &&
      dropsRevertedWrite && preservesPrior &&
      packedFields && packedRawSlots && packedGetters)

def checkedTryCatchTargetContract : Solidity.ContractDecl :=
  { name := "CheckedTryCatchTarget"
    items :=
      [ Solidity.ContractItem.function
          tryMemberTargetFunction ] }

def checkedTryCatchMemberFunction (name : Name)
    (clauses : List Solidity.CatchClause) :
    Solidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some name
    params :=
      [ { name := some "feed"
          ty := Ty.user { segments := ["CheckedTryCatchTarget"] }
          location := none } ]
    mutability := StateMutability.view
    body :=
      some
        (Solidity.Stmt.tryCatchReturns
          (Solidity.Expr.call
            (Solidity.Expr.member
              (Solidity.Expr.ident "feed") "read") [])
          [{ name := some "value", ty := Ty.uint 256, location := none }]
          (Solidity.Stmt.returnValues
            (some (Solidity.Expr.ident "value")))
          clauses) }

def checkedTryCatchSource (contractName functionName : Name)
    (clauses : List Solidity.CatchClause) :
    Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract checkedTryCatchTargetContract
      , Solidity.SourceItem.contract
          { name := contractName
            items :=
              [ Solidity.ContractItem.function
                  (checkedTryCatchMemberFunction functionName clauses) ] } ] }

def checkedTryCatchErrorMatches : Except TypeError Bool := do
  let callData ←
    optionToExcept "try/catch calldata"
      (Executable.Examples.externalCalldata? "read()" [] [])
  let errorBytes ←
    optionToExcept "try/catch Error(string)"
      (Executable.Examples.externalErrorBytes? "bad")
  let result ←
    checkedSourceFunctionCallWithContextFailOpen 16
      (SolidCore.Solidity.Source.responderOfResults
          [ { kind := SolidCore.Solidity.Source.LowLevelCallKind.staticcall
              target := 0xbeef
              calldata := callData
              success := false
              output := errorBytes } ]
      [])
      (checkedTryCatchSource "CheckedTryCatchError" "readError"
        [ Solidity.CatchClause.clause (some "Error")
            [{ name := some "reason"
               ty := Ty.string
               location := some DataLocation.memory }]
            (Solidity.Stmt.returnValues
              (some
                (Solidity.Expr.literal
                  (Solidity.Literal.number "3"))))
        , Solidity.CatchClause.clause none []
            (Solidity.Stmt.returnValues
              (some
                (Solidity.Expr.literal
                  (Solidity.Literal.number "999")))) ])
      "CheckedTryCatchError" "readError"
      (SolidCore.Solidity.Source.Context.empty)
      SolidCore.Solidity.Source.State.empty
      [SolidCore.Solidity.Source.Value.word 0xbeef]
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _
      [SolidCore.Solidity.Source.Value.word value] =>
      Except.ok (value == 3)
  | _ => Except.ok false

def checkedTryCatchPanicMatches : Except TypeError Bool := do
  let callData ←
    optionToExcept "try/catch calldata"
      (Executable.Examples.externalCalldata? "read()" [] [])
  let panicBytes ←
    optionToExcept "try/catch Panic(uint256)"
      (Executable.Examples.externalPanicBytes? 0x11)
  let result ←
    checkedSourceFunctionCallWithContextFailOpen 16
      (SolidCore.Solidity.Source.responderOfResults
          [ { kind := SolidCore.Solidity.Source.LowLevelCallKind.staticcall
              target := 0xbeef
              calldata := callData
              success := false
              output := panicBytes } ]
      [])
      (checkedTryCatchSource "CheckedTryCatchPanic" "readPanic"
        [ Solidity.CatchClause.clause (some "Panic")
            [{ name := some "code"
               ty := Ty.uint 256
               location := none }]
            (Solidity.Stmt.returnValues
              (some (Solidity.Expr.ident "code"))) ])
      "CheckedTryCatchPanic" "readPanic"
      (SolidCore.Solidity.Source.Context.empty)
      SolidCore.Solidity.Source.State.empty
      [SolidCore.Solidity.Source.Value.word 0xbeef]
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _
      [SolidCore.Solidity.Source.Value.word value] =>
      Except.ok (value == 0x11)
  | _ => Except.ok false

def checkedTryCatchLowLevelMatches : Except TypeError Bool := do
  let callData ←
    optionToExcept "try/catch calldata"
      (Executable.Examples.externalCalldata? "read()" [] [])
  let result ←
    checkedSourceFunctionCallWithContextFailOpen 16
      (SolidCore.Solidity.Source.responderOfResults
          [ { kind := SolidCore.Solidity.Source.LowLevelCallKind.staticcall
              target := 0xbeef
              calldata := callData
              success := false
              output := [0xaa, 0xbb, 0xcc] } ]
      [])
      (checkedTryCatchSource "CheckedTryCatchLowLevel" "readRaw"
        [ Solidity.CatchClause.clause none
            [{ name := some "data"
               ty := Ty.bytes
               location := some DataLocation.memory }]
            (Solidity.Stmt.returnValues
              (some
                (Solidity.Expr.literal
                  (Solidity.Literal.number "3")))) ])
      "CheckedTryCatchLowLevel" "readRaw"
      (SolidCore.Solidity.Source.Context.empty)
      SolidCore.Solidity.Source.State.empty
      [SolidCore.Solidity.Source.Value.word 0xbeef]
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _
      [SolidCore.Solidity.Source.Value.word value] =>
      Except.ok (value == 3)
  | _ => Except.ok false

end Examples

end TypeCheck
end Solidity
end SolidCore

import SolidCore.Spine.L00_SourceSolidity.TypeCheck

namespace SolidCore
namespace Spine
namespace L00_SourceSolidity
namespace TypeCheck

abbrev CoreContract := L00_SourceSolidity.Executable.CoreContract
abbrev CoreValue := L00_SourceSolidity.Executable.CoreValue
abbrev CoreState := L00_SourceSolidity.Executable.CoreState
abbrev CoreCallResult := L00_SourceSolidity.Executable.CoreCallResult
abbrev CoreAbiCallResult := SolidCore.Solidity.Source.ABI.AbiCallResult
abbrev CallTarget := SolidCore.Solidity.Source.CallTarget

namespace Result

def toOption {α : Type} : Except TypeError α -> Option α
  | Except.ok value => some value
  | Except.error _ => none

end Result

def executableFailure (what : String) : TypeError :=
  TypeError.unsupported ("checked executable " ++ what)

def optionToExcept {α : Type} (what : String) : Option α ->
    Except TypeError α
  | some value => Except.ok value
  | none => Except.error (executableFailure what)

/-
The common checked source layer for execution-facing users.

`Interface.lean` still contains the raw executable translators because the
typechecker depends on the source surface defined there. Callers that want
Solidity validity as part of execution should enter through this wrapper so
`SourceUnit.check` is run before any source-to-core translation or call.
-/
namespace CheckedSourceUnit

def toCoreContract? (checked : CheckedSourceUnit) (name : Name) :
    Option CoreContract :=
  L00_SourceSolidity.Executable.SourceUnit.toCoreContract?
    checked.source name

def toCoreContract (checked : CheckedSourceUnit) (name : Name) :
    Except TypeError CoreContract :=
  optionToExcept ("contract translation " ++ name)
    (toCoreContract? checked name)

def toCoreContracts? (checked : CheckedSourceUnit) :
    Option (List CoreContract) :=
  L00_SourceSolidity.Executable.SourceUnit.toCoreContracts?
    checked.source

def toCoreContracts (checked : CheckedSourceUnit) :
    Except TypeError (List CoreContract) :=
  optionToExcept "source-unit translation"
    (toCoreContracts? checked)

def constructContractFrom? (fuel : Nat) (checked : CheckedSourceUnit)
    (name : Name) (state : CoreState) (sender value : Word)
    (args : List CoreValue) : Option CoreCallResult :=
  L00_SourceSolidity.Executable.SourceUnit.constructContractFrom?
    fuel checked.source name state sender value args

def constructContractFrom (fuel : Nat) (checked : CheckedSourceUnit)
    (name : Name) (state : CoreState) (sender value : Word)
    (args : List CoreValue) : Except TypeError CoreCallResult :=
  optionToExcept ("constructor call " ++ name)
    (constructContractFrom?
      fuel checked name state sender value args)

def constructContract? (fuel : Nat) (checked : CheckedSourceUnit)
    (name : Name) (state : CoreState) (args : List CoreValue) :
    Option CoreCallResult :=
  L00_SourceSolidity.Executable.SourceUnit.constructContract?
    fuel checked.source name state args

def constructContract (fuel : Nat) (checked : CheckedSourceUnit)
    (name : Name) (state : CoreState) (args : List CoreValue) :
    Except TypeError CoreCallResult :=
  optionToExcept ("constructor call " ++ name)
    (constructContract? fuel checked name state args)

def callContract? (fuel : Nat) (checked : CheckedSourceUnit)
    (name : Name) (target : CallTarget) (state : CoreState)
    (args : List CoreValue) : Option CoreCallResult :=
  L00_SourceSolidity.Executable.SourceUnit.callContract?
    fuel checked.source name target state args

def callContract (fuel : Nat) (checked : CheckedSourceUnit)
    (name : Name) (target : CallTarget) (state : CoreState)
    (args : List CoreValue) : Except TypeError CoreCallResult :=
  optionToExcept ("contract call " ++ name)
    (callContract? fuel checked name target state args)

def callContractTransaction? (fuel : Nat) (checked : CheckedSourceUnit)
    (name : Name) (target : CallTarget) (state : CoreState)
    (args : List CoreValue) : Option CoreCallResult :=
  L00_SourceSolidity.Executable.SourceUnit.callContractTransaction?
    fuel checked.source name target state args

def callContractTransaction (fuel : Nat) (checked : CheckedSourceUnit)
    (name : Name) (target : CallTarget) (state : CoreState)
    (args : List CoreValue) : Except TypeError CoreCallResult :=
  optionToExcept ("contract transaction " ++ name)
    (callContractTransaction?
      fuel checked name target state args)

def callCalldataFrom? (fuel : Nat) (checked : CheckedSourceUnit)
    (name : Name) (state : CoreState) (sender value : Word)
    (calldata : List Byte) : Option CoreAbiCallResult := do
  let contract ← toCoreContract? checked name
  SolidCore.Solidity.Source.ABI.Contract.callCalldataFrom?
    fuel contract state sender value calldata

def callCalldataFrom (fuel : Nat) (checked : CheckedSourceUnit)
    (name : Name) (state : CoreState) (sender value : Word)
    (calldata : List Byte) : Except TypeError CoreAbiCallResult :=
  optionToExcept ("ABI calldata call " ++ name)
    (callCalldataFrom? fuel checked name state sender value calldata)

def callCalldata? (fuel : Nat) (checked : CheckedSourceUnit)
    (name : Name) (state : CoreState) (calldata : List Byte) :
    Option CoreAbiCallResult :=
  callCalldataFrom? fuel checked name state 0 0 calldata

def callCalldata (fuel : Nat) (checked : CheckedSourceUnit)
    (name : Name) (state : CoreState) (calldata : List Byte) :
    Except TypeError CoreAbiCallResult :=
  callCalldataFrom fuel checked name state 0 0 calldata

end CheckedSourceUnit

namespace SourceUnit

def checked? (source : L00_SourceSolidity.SourceUnit) :
    Option CheckedSourceUnit :=
  Result.toOption
    (_root_.SolidCore.Spine.L00_SourceSolidity.TypeCheck.SourceUnit.check
      source)

def checkedToCoreContract? (source : L00_SourceSolidity.SourceUnit)
    (name : Name) : Option CoreContract := do
  let checked ← checked? source
  _root_.SolidCore.Spine.L00_SourceSolidity.TypeCheck.CheckedSourceUnit.toCoreContract?
    checked name

def checkedToCoreContract (source : L00_SourceSolidity.SourceUnit)
    (name : Name) : Except TypeError CoreContract := do
  let checked ←
    _root_.SolidCore.Spine.L00_SourceSolidity.TypeCheck.SourceUnit.check
      source
  _root_.SolidCore.Spine.L00_SourceSolidity.TypeCheck.CheckedSourceUnit.toCoreContract
    checked name

def checkedToCoreContracts? (source : L00_SourceSolidity.SourceUnit) :
    Option (List CoreContract) := do
  let checked ← checked? source
  _root_.SolidCore.Spine.L00_SourceSolidity.TypeCheck.CheckedSourceUnit.toCoreContracts?
    checked

def checkedToCoreContracts (source : L00_SourceSolidity.SourceUnit) :
    Except TypeError (List CoreContract) := do
  let checked ←
    _root_.SolidCore.Spine.L00_SourceSolidity.TypeCheck.SourceUnit.check
      source
  _root_.SolidCore.Spine.L00_SourceSolidity.TypeCheck.CheckedSourceUnit.toCoreContracts
    checked

def checkedConstructContractFrom? (fuel : Nat)
    (source : L00_SourceSolidity.SourceUnit) (name : Name)
    (state : CoreState) (sender value : Word) (args : List CoreValue) :
    Option CoreCallResult := do
  let checked ← checked? source
  _root_.SolidCore.Spine.L00_SourceSolidity.TypeCheck.CheckedSourceUnit.constructContractFrom?
    fuel checked name state sender value args

def checkedConstructContractFrom (fuel : Nat)
    (source : L00_SourceSolidity.SourceUnit) (name : Name)
    (state : CoreState) (sender value : Word) (args : List CoreValue) :
    Except TypeError CoreCallResult := do
  let checked ←
    _root_.SolidCore.Spine.L00_SourceSolidity.TypeCheck.SourceUnit.check
      source
  _root_.SolidCore.Spine.L00_SourceSolidity.TypeCheck.CheckedSourceUnit.constructContractFrom
    fuel checked name state sender value args

def checkedConstructContract? (fuel : Nat)
    (source : L00_SourceSolidity.SourceUnit) (name : Name)
    (state : CoreState) (args : List CoreValue) :
    Option CoreCallResult := do
  let checked ← checked? source
  _root_.SolidCore.Spine.L00_SourceSolidity.TypeCheck.CheckedSourceUnit.constructContract?
    fuel checked name state args

def checkedConstructContract (fuel : Nat)
    (source : L00_SourceSolidity.SourceUnit) (name : Name)
    (state : CoreState) (args : List CoreValue) :
    Except TypeError CoreCallResult := do
  let checked ←
    _root_.SolidCore.Spine.L00_SourceSolidity.TypeCheck.SourceUnit.check
      source
  _root_.SolidCore.Spine.L00_SourceSolidity.TypeCheck.CheckedSourceUnit.constructContract
    fuel checked name state args

def checkedCallContract? (fuel : Nat)
    (source : L00_SourceSolidity.SourceUnit) (name : Name)
    (target : CallTarget) (state : CoreState) (args : List CoreValue) :
    Option CoreCallResult := do
  let checked ← checked? source
  _root_.SolidCore.Spine.L00_SourceSolidity.TypeCheck.CheckedSourceUnit.callContract?
    fuel checked name target state args

def checkedCallContract (fuel : Nat)
    (source : L00_SourceSolidity.SourceUnit) (name : Name)
    (target : CallTarget) (state : CoreState) (args : List CoreValue) :
    Except TypeError CoreCallResult := do
  let checked ←
    _root_.SolidCore.Spine.L00_SourceSolidity.TypeCheck.SourceUnit.check
      source
  _root_.SolidCore.Spine.L00_SourceSolidity.TypeCheck.CheckedSourceUnit.callContract
    fuel checked name target state args

def checkedCallContractTransaction? (fuel : Nat)
    (source : L00_SourceSolidity.SourceUnit) (name : Name)
    (target : CallTarget) (state : CoreState) (args : List CoreValue) :
    Option CoreCallResult := do
  let checked ← checked? source
  _root_.SolidCore.Spine.L00_SourceSolidity.TypeCheck.CheckedSourceUnit.callContractTransaction?
    fuel checked name target state args

def checkedCallContractTransaction (fuel : Nat)
    (source : L00_SourceSolidity.SourceUnit) (name : Name)
    (target : CallTarget) (state : CoreState) (args : List CoreValue) :
    Except TypeError CoreCallResult := do
  let checked ←
    _root_.SolidCore.Spine.L00_SourceSolidity.TypeCheck.SourceUnit.check
      source
  _root_.SolidCore.Spine.L00_SourceSolidity.TypeCheck.CheckedSourceUnit.callContractTransaction
    fuel checked name target state args

def checkedCallCalldataFrom? (fuel : Nat)
    (source : L00_SourceSolidity.SourceUnit) (name : Name)
    (state : CoreState) (sender value : Word) (calldata : List Byte) :
    Option CoreAbiCallResult := do
  let checked ← checked? source
  _root_.SolidCore.Spine.L00_SourceSolidity.TypeCheck.CheckedSourceUnit.callCalldataFrom?
    fuel checked name state sender value calldata

def checkedCallCalldataFrom (fuel : Nat)
    (source : L00_SourceSolidity.SourceUnit) (name : Name)
    (state : CoreState) (sender value : Word) (calldata : List Byte) :
    Except TypeError CoreAbiCallResult := do
  let checked ←
    _root_.SolidCore.Spine.L00_SourceSolidity.TypeCheck.SourceUnit.check
      source
  _root_.SolidCore.Spine.L00_SourceSolidity.TypeCheck.CheckedSourceUnit.callCalldataFrom
    fuel checked name state sender value calldata

def checkedCallCalldata? (fuel : Nat)
    (source : L00_SourceSolidity.SourceUnit) (name : Name)
    (state : CoreState) (calldata : List Byte) :
    Option CoreAbiCallResult :=
  checkedCallCalldataFrom? fuel source name state 0 0 calldata

def checkedCallCalldata (fuel : Nat)
    (source : L00_SourceSolidity.SourceUnit) (name : Name)
    (state : CoreState) (calldata : List Byte) :
    Except TypeError CoreAbiCallResult :=
  checkedCallCalldataFrom fuel source name state 0 0 calldata

end SourceUnit

namespace ContractDecl

def sourceUnit (decl : L00_SourceSolidity.ContractDecl) :
    L00_SourceSolidity.SourceUnit :=
  { items := [L00_SourceSolidity.SourceItem.contract decl] }

def checked? (decl : L00_SourceSolidity.ContractDecl) :
    Option CheckedSourceUnit :=
  SourceUnit.checked? (sourceUnit decl)

def checkedToCore? (decl : L00_SourceSolidity.ContractDecl) :
    Option CoreContract :=
  SourceUnit.checkedToCoreContract? (sourceUnit decl) decl.name

def checkedToCore (decl : L00_SourceSolidity.ContractDecl) :
    Except TypeError CoreContract :=
  SourceUnit.checkedToCoreContract (sourceUnit decl) decl.name

def checkedConstructFrom? (fuel : Nat)
    (decl : L00_SourceSolidity.ContractDecl) (state : CoreState)
    (sender value : Word) (args : List CoreValue) :
    Option CoreCallResult :=
  SourceUnit.checkedConstructContractFrom?
    fuel (sourceUnit decl) decl.name state sender value args

def checkedConstructFrom (fuel : Nat)
    (decl : L00_SourceSolidity.ContractDecl) (state : CoreState)
    (sender value : Word) (args : List CoreValue) :
    Except TypeError CoreCallResult :=
  SourceUnit.checkedConstructContractFrom
    fuel (sourceUnit decl) decl.name state sender value args

def checkedConstruct? (fuel : Nat)
    (decl : L00_SourceSolidity.ContractDecl) (state : CoreState)
    (args : List CoreValue) : Option CoreCallResult :=
  SourceUnit.checkedConstructContract?
    fuel (sourceUnit decl) decl.name state args

def checkedConstruct (fuel : Nat)
    (decl : L00_SourceSolidity.ContractDecl) (state : CoreState)
    (args : List CoreValue) : Except TypeError CoreCallResult :=
  SourceUnit.checkedConstructContract
    fuel (sourceUnit decl) decl.name state args

def checkedCall? (fuel : Nat)
    (decl : L00_SourceSolidity.ContractDecl) (target : CallTarget)
    (state : CoreState) (args : List CoreValue) : Option CoreCallResult :=
  SourceUnit.checkedCallContract?
    fuel (sourceUnit decl) decl.name target state args

def checkedCall (fuel : Nat)
    (decl : L00_SourceSolidity.ContractDecl) (target : CallTarget)
    (state : CoreState) (args : List CoreValue) :
    Except TypeError CoreCallResult :=
  SourceUnit.checkedCallContract
    fuel (sourceUnit decl) decl.name target state args

def checkedCallTransaction? (fuel : Nat)
    (decl : L00_SourceSolidity.ContractDecl) (target : CallTarget)
    (state : CoreState) (args : List CoreValue) : Option CoreCallResult :=
  SourceUnit.checkedCallContractTransaction?
    fuel (sourceUnit decl) decl.name target state args

def checkedCallTransaction (fuel : Nat)
    (decl : L00_SourceSolidity.ContractDecl) (target : CallTarget)
    (state : CoreState) (args : List CoreValue) :
    Except TypeError CoreCallResult :=
  SourceUnit.checkedCallContractTransaction
    fuel (sourceUnit decl) decl.name target state args

def checkedCallCalldataFrom? (fuel : Nat)
    (decl : L00_SourceSolidity.ContractDecl) (state : CoreState)
    (sender value : Word) (calldata : List Byte) :
    Option CoreAbiCallResult :=
  SourceUnit.checkedCallCalldataFrom?
    fuel (sourceUnit decl) decl.name state sender value calldata

def checkedCallCalldataFrom (fuel : Nat)
    (decl : L00_SourceSolidity.ContractDecl) (state : CoreState)
    (sender value : Word) (calldata : List Byte) :
    Except TypeError CoreAbiCallResult :=
  SourceUnit.checkedCallCalldataFrom
    fuel (sourceUnit decl) decl.name state sender value calldata

def checkedCallCalldata? (fuel : Nat)
    (decl : L00_SourceSolidity.ContractDecl) (state : CoreState)
    (calldata : List Byte) : Option CoreAbiCallResult :=
  checkedCallCalldataFrom? fuel decl state 0 0 calldata

def checkedCallCalldata (fuel : Nat)
    (decl : L00_SourceSolidity.ContractDecl) (state : CoreState)
    (calldata : List Byte) : Except TypeError CoreAbiCallResult :=
  checkedCallCalldataFrom fuel decl state 0 0 calldata

end ContractDecl

namespace Examples

def checkedSourceFunctionCallWithContext (fuel : Nat)
    (source : L00_SourceSolidity.SourceUnit) (contractName functionName : Name)
    (context : SolidCore.Solidity.Source.Context)
    (state : CoreState) (args : List CoreValue) :
    Except TypeError CoreCallResult := do
  let contract ← SourceUnit.checkedToCoreContract source contractName
  let function ←
    optionToExcept ("function lookup " ++ functionName)
      (contract.findFunctionByName? functionName)
  optionToExcept ("function call " ++ functionName)
    (SolidCore.Solidity.Source.FunctionDef.call?
      fuel context function state args)

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

def missingVisibilityExecutableContract : L00_SourceSolidity.ContractDecl :=
  { name := "MissingVisibilityExecutable"
    items :=
      [ L00_SourceSolidity.ContractItem.function
          { name := some "run"
            returns := [{ name := some "out", ty := Ty.uint 256 }]
            body :=
              some
                (L00_SourceSolidity.Stmt.returnValues
                  (some
                    (L00_SourceSolidity.Expr.literal
                      (L00_SourceSolidity.Literal.number "7")))) } ] }

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

def checkedFallbackReceiveContract : L00_SourceSolidity.ContractDecl :=
  { name := "CheckedFallbackReceive"
    items :=
      [ L00_SourceSolidity.ContractItem.stateVar
          { name := "x", ty := Ty.uint 256 }
      , L00_SourceSolidity.ContractItem.function
          { kind := FunctionKind.fallback
            visibility := some Visibility.external_
            body :=
              some
                (L00_SourceSolidity.Stmt.expr
                  (L00_SourceSolidity.Expr.assign
                    (L00_SourceSolidity.Expr.ident "x")
                    AssignOp.assign
                    (L00_SourceSolidity.Expr.literal
                      (L00_SourceSolidity.Literal.number "1")))) }
      , L00_SourceSolidity.ContractItem.function
          { kind := FunctionKind.receive
            visibility := some Visibility.external_
            mutability := StateMutability.payable
            body :=
              some
                (L00_SourceSolidity.Stmt.expr
                  (L00_SourceSolidity.Expr.assign
                    (L00_SourceSolidity.Expr.ident "x")
                    AssignOp.assign
                    (L00_SourceSolidity.Expr.literal
                      (L00_SourceSolidity.Literal.number "2")))) } ] }

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
    L00_SourceSolidity.ContractDecl :=
  { name := "CheckedFallbackValue"
    items :=
      [ L00_SourceSolidity.ContractItem.stateVar
          { name := "last", ty := Ty.uint 256 }
      , L00_SourceSolidity.ContractItem.function
          { kind := FunctionKind.fallback
            visibility := some Visibility.external_
            mutability := StateMutability.payable
            body :=
              some
                (L00_SourceSolidity.Stmt.expr
                  (L00_SourceSolidity.Expr.assign
                    (L00_SourceSolidity.Expr.ident "last")
                    AssignOp.assign
                    (L00_SourceSolidity.Expr.member
                      (L00_SourceSolidity.Expr.ident "msg") "value"))) } ] }

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

def checkedMissingFallbackContract : L00_SourceSolidity.ContractDecl :=
  { name := "CheckedMissingFallback"
    items :=
      [ L00_SourceSolidity.ContractItem.stateVar
          { name := "x", ty := Ty.uint 256 }
      , L00_SourceSolidity.ContractItem.function
          { name := some "touch"
            visibility := some Visibility.public_
            body :=
              some
                (L00_SourceSolidity.Stmt.expr
                  (L00_SourceSolidity.Expr.assign
                    (L00_SourceSolidity.Expr.ident "x")
                    AssignOp.assign
                    (L00_SourceSolidity.Expr.literal
                      (L00_SourceSolidity.Literal.number "9")))) } ] }

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

def checkedTryCatchTargetContract : L00_SourceSolidity.ContractDecl :=
  { name := "CheckedTryCatchTarget"
    items :=
      [ L00_SourceSolidity.ContractItem.function
          tryMemberTargetFunction ] }

def checkedTryCatchMemberFunction (name : Name)
    (clauses : List L00_SourceSolidity.CatchClause) :
    L00_SourceSolidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some name
    params :=
      [ { name := some "feed"
          ty := Ty.user { segments := ["CheckedTryCatchTarget"] }
          location := none } ]
    mutability := StateMutability.view
    body :=
      some
        (L00_SourceSolidity.Stmt.tryCatchReturns
          (L00_SourceSolidity.Expr.call
            (L00_SourceSolidity.Expr.member
              (L00_SourceSolidity.Expr.ident "feed") "read") [])
          [{ name := some "value", ty := Ty.uint 256, location := none }]
          (L00_SourceSolidity.Stmt.returnValues
            (some (L00_SourceSolidity.Expr.ident "value")))
          clauses) }

def checkedTryCatchSource (contractName functionName : Name)
    (clauses : List L00_SourceSolidity.CatchClause) :
    L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract checkedTryCatchTargetContract
      , L00_SourceSolidity.SourceItem.contract
          { name := contractName
            items :=
              [ L00_SourceSolidity.ContractItem.function
                  (checkedTryCatchMemberFunction functionName clauses) ] } ] }

def checkedTryCatchErrorMatches : Except TypeError Bool := do
  let callData ←
    optionToExcept "try/catch calldata"
      (Executable.Examples.externalCalldata? "read()" [] [])
  let errorBytes ←
    optionToExcept "try/catch Error(string)"
      (Executable.Examples.externalErrorBytes? "bad")
  let result ←
    checkedSourceFunctionCallWithContext 16
      (checkedTryCatchSource "CheckedTryCatchError" "readError"
        [ L00_SourceSolidity.CatchClause.clause (some "Error")
            [{ name := some "reason"
               ty := Ty.string
               location := some DataLocation.memory }]
            (L00_SourceSolidity.Stmt.returnValues
              (some
                (L00_SourceSolidity.Expr.literal
                  (L00_SourceSolidity.Literal.number "3"))))
        , L00_SourceSolidity.CatchClause.clause none []
            (L00_SourceSolidity.Stmt.returnValues
              (some
                (L00_SourceSolidity.Expr.literal
                  (L00_SourceSolidity.Literal.number "999")))) ])
      "CheckedTryCatchError" "readError"
      { SolidCore.Solidity.Source.Context.empty with
        lowLevelCallResults :=
          [ { kind := SolidCore.Solidity.Source.LowLevelCallKind.staticcall
              target := 0xbeef
              calldata := callData
              success := false
              output := errorBytes } ] }
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
    checkedSourceFunctionCallWithContext 16
      (checkedTryCatchSource "CheckedTryCatchPanic" "readPanic"
        [ L00_SourceSolidity.CatchClause.clause (some "Panic")
            [{ name := some "code"
               ty := Ty.uint 256
               location := none }]
            (L00_SourceSolidity.Stmt.returnValues
              (some (L00_SourceSolidity.Expr.ident "code"))) ])
      "CheckedTryCatchPanic" "readPanic"
      { SolidCore.Solidity.Source.Context.empty with
        lowLevelCallResults :=
          [ { kind := SolidCore.Solidity.Source.LowLevelCallKind.staticcall
              target := 0xbeef
              calldata := callData
              success := false
              output := panicBytes } ] }
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
    checkedSourceFunctionCallWithContext 16
      (checkedTryCatchSource "CheckedTryCatchLowLevel" "readRaw"
        [ L00_SourceSolidity.CatchClause.clause none
            [{ name := some "data"
               ty := Ty.bytes
               location := some DataLocation.memory }]
            (L00_SourceSolidity.Stmt.returnValues
              (some
                (L00_SourceSolidity.Expr.literal
                  (L00_SourceSolidity.Literal.number "3")))) ])
      "CheckedTryCatchLowLevel" "readRaw"
      { SolidCore.Solidity.Source.Context.empty with
        lowLevelCallResults :=
          [ { kind := SolidCore.Solidity.Source.LowLevelCallKind.staticcall
              target := 0xbeef
              calldata := callData
              success := false
              output := [0xaa, 0xbb, 0xcc] } ] }
      SolidCore.Solidity.Source.State.empty
      [SolidCore.Solidity.Source.Value.word 0xbeef]
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _
      [SolidCore.Solidity.Source.Value.word value] =>
      Except.ok (value == 3)
  | _ => Except.ok false

end Examples

end TypeCheck
end L00_SourceSolidity
end Spine
end SolidCore

import SolidCore.Spine.L00_SourceSolidity.TypeCheck

namespace SolidCore
namespace Spine
namespace L00_SourceSolidity
namespace TypeCheck

abbrev CoreContract := L00_SourceSolidity.Executable.CoreContract
abbrev CoreValue := L00_SourceSolidity.Executable.CoreValue
abbrev CoreState := L00_SourceSolidity.Executable.CoreState
abbrev CoreCallResult := L00_SourceSolidity.Executable.CoreCallResult
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

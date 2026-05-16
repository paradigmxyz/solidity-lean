import SolidCore.Spine.L00_SourceSolidity.TypeCheck

namespace SolidCore
namespace Spine
namespace L00_SourceSolidity
namespace TypeCheck

abbrev CoreContract := L00_SourceSolidity.Executable.CoreContract
abbrev CoreValue := L00_SourceSolidity.Executable.CoreValue
abbrev CoreState := L00_SourceSolidity.Executable.CoreState
abbrev CoreContext := L00_SourceSolidity.Executable.CoreContext
abbrev CoreCallResult := L00_SourceSolidity.Executable.CoreCallResult
abbrev CoreFunctionDef := L00_SourceSolidity.Executable.CoreFunctionDef
abbrev CoreAbiCallResult := SolidCore.Solidity.Source.ABI.AbiCallResult
abbrev CallTarget := SolidCore.Solidity.Source.CallTarget

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
structure CheckedProgram where
  checked : CheckedSourceUnit
  source : SourceUnitAst
  deriving Repr

structure CheckedContract where
  program : CheckedProgram
  decl : SourceContractDecl
  core : CoreContract
  deriving Repr

namespace CheckedProgram

def fromChecked? (checked : CheckedSourceUnit) :
    Option CheckedProgram := do
  let source ←
    L00_SourceSolidity.Executable.SourceUnit.resolveSourceTypesContextual?
      checked.source
  some { checked := checked, source := source }

def fromChecked (checked : CheckedSourceUnit) :
    Except TypeError CheckedProgram :=
  optionToExcept "source type resolution" (fromChecked? checked)

def fromSource? (source : SourceUnitAst) : Option CheckedProgram := do
  let checked ← TypecheckedInput.checkedSourceUnit? source
  fromChecked? checked

def fromSource (source : SourceUnitAst) :
    Except TypeError CheckedProgram := do
  let checked ← TypecheckedInput.checkedSourceUnit source
  fromChecked checked

def usingDecls (program : CheckedProgram) :
    List L00_SourceSolidity.UsingDecl :=
  L00_SourceSolidity.Executable.SourceUnit.usingDecls program.source

def freeFunctions (program : CheckedProgram) :
    List L00_SourceSolidity.FunctionDecl :=
  L00_SourceSolidity.Executable.SourceUnit.freeFunctions program.source

def freeEvents (program : CheckedProgram) :
    List L00_SourceSolidity.EventDecl :=
  L00_SourceSolidity.Executable.SourceUnit.freeEvents program.source

def freeErrors (program : CheckedProgram) :
    List L00_SourceSolidity.ErrorDecl :=
  L00_SourceSolidity.Executable.SourceUnit.freeErrors program.source

def freeConstants (program : CheckedProgram) :
    List L00_SourceSolidity.StateVarDecl :=
  L00_SourceSolidity.Executable.SourceUnit.freeConstants program.source

def contracts (program : CheckedProgram) :
    List SourceContractDecl :=
  L00_SourceSolidity.Executable.SourceUnit.contracts program.source

def findSourceContract? (program : CheckedProgram) (name : Name) :
    Option SourceContractDecl :=
  L00_SourceSolidity.Executable.SourceUnit.findContract?
    program.source name

def toCoreContractFor? (program : CheckedProgram)
    (decl : SourceContractDecl) : Option CoreContract :=
  L00_SourceSolidity.Executable.ContractDecl.toCoreWithBasesAndUsing?
    (usingDecls program) (freeFunctions program)
    (freeEvents program) (freeErrors program)
    (freeConstants program) (contracts program) decl

def toCoreContract? (program : CheckedProgram) (name : Name) :
    Option CoreContract := do
  let decl ← findSourceContract? program name
  toCoreContractFor? program decl

def toCoreContract (program : CheckedProgram) (name : Name) :
    Except TypeError CoreContract :=
  optionToExcept ("contract translation " ++ name)
    (toCoreContract? program name)

def toCoreContracts? (program : CheckedProgram) :
    Option (List CoreContract) :=
  L00_SourceSolidity.Executable.mapOption
    (fun decl => toCoreContractFor? program decl)
    (contracts program)

def toCoreContracts (program : CheckedProgram) :
    Except TypeError (List CoreContract) :=
  optionToExcept "source-unit translation" (toCoreContracts? program)

def constructorFunctionFor? (program : CheckedProgram)
    (decl : SourceContractDecl) : Option CoreFunctionDef :=
  L00_SourceSolidity.Executable.ContractDecl.constructorFunctionWithBasesAndSource?
    (usingDecls program) (freeFunctions program)
    (freeEvents program) (freeErrors program)
    (freeConstants program) (contracts program) decl

def constructorFunction? (program : CheckedProgram) (name : Name) :
    Option CoreFunctionDef := do
  let decl ← findSourceContract? program name
  constructorFunctionFor? program decl

def contract? (program : CheckedProgram) (name : Name) :
    Option CheckedContract := do
  let decl ← findSourceContract? program name
  let core ← toCoreContractFor? program decl
  some { program := program, decl := decl, core := core }

def contract (program : CheckedProgram) (name : Name) :
    Except TypeError CheckedContract :=
  optionToExcept ("checked contract " ++ name) (contract? program name)

end CheckedProgram

namespace CheckedContract

def constructFrom? (fuel : Nat) (contract : CheckedContract)
    (state : CoreState) (sender value : Word) (args : List CoreValue) :
    Option CoreCallResult := do
  let constructor ←
    CheckedProgram.constructorFunctionFor? contract.program contract.decl
  SolidCore.Solidity.Source.FunctionDef.call?
    fuel
    { contract.core.context with
      sender := sender
      value := value
      construction := true }
    constructor state args

def constructFrom (fuel : Nat) (contract : CheckedContract)
    (state : CoreState) (sender value : Word) (args : List CoreValue) :
    Except TypeError CoreCallResult :=
  optionToExcept ("constructor call " ++ contract.decl.name)
    (constructFrom? fuel contract state sender value args)

def construct? (fuel : Nat) (contract : CheckedContract)
    (state : CoreState) (args : List CoreValue) :
    Option CoreCallResult :=
  constructFrom? fuel contract state 0 0 args

def construct (fuel : Nat) (contract : CheckedContract)
    (state : CoreState) (args : List CoreValue) :
    Except TypeError CoreCallResult :=
  constructFrom fuel contract state 0 0 args

def call? (fuel : Nat) (contract : CheckedContract)
    (target : CallTarget) (state : CoreState)
    (args : List CoreValue) : Option CoreCallResult :=
  SolidCore.Solidity.Source.Contract.call?
    fuel contract.core target state args

def call (fuel : Nat) (contract : CheckedContract)
    (target : CallTarget) (state : CoreState)
    (args : List CoreValue) : Except TypeError CoreCallResult :=
  optionToExcept ("contract call " ++ contract.decl.name)
    (call? fuel contract target state args)

def callTransaction? (fuel : Nat) (contract : CheckedContract)
    (target : CallTarget) (state : CoreState)
    (args : List CoreValue) : Option CoreCallResult :=
  SolidCore.Solidity.Source.Contract.callTransaction?
    fuel contract.core target state args

def callTransaction (fuel : Nat) (contract : CheckedContract)
    (target : CallTarget) (state : CoreState)
    (args : List CoreValue) : Except TypeError CoreCallResult :=
  optionToExcept ("contract transaction " ++ contract.decl.name)
    (callTransaction? fuel contract target state args)

def coreFunction? (contract : CheckedContract) (functionName : Name) :
    Option CoreFunctionDef :=
  contract.core.findFunctionByName? functionName

def coreFunction (contract : CheckedContract) (functionName : Name) :
    Except TypeError CoreFunctionDef :=
  optionToExcept ("function lookup " ++ functionName)
    (coreFunction? contract functionName)

def functionCalldata? (contract : CheckedContract)
    (functionName : Name) (args : List CoreValue) :
    Option (List Byte) := do
  let function ← coreFunction? contract functionName
  SolidCore.Solidity.Source.ABI.calldataFor? function args

def functionCalldata (contract : CheckedContract)
    (functionName : Name) (args : List CoreValue) :
    Except TypeError (List Byte) :=
  optionToExcept ("ABI calldata " ++ functionName)
    (functionCalldata? contract functionName args)

def callFunctionWithContext? (fuel : Nat)
    (contract : CheckedContract) (functionName : Name)
    (context : SolidCore.Solidity.Source.Context)
    (state : CoreState) (args : List CoreValue) :
    Option CoreCallResult := do
  let function ← coreFunction? contract functionName
  SolidCore.Solidity.Source.FunctionDef.call?
    fuel context function state args

def callFunctionWithContext (fuel : Nat)
    (contract : CheckedContract) (functionName : Name)
    (context : SolidCore.Solidity.Source.Context)
    (state : CoreState) (args : List CoreValue) :
    Except TypeError CoreCallResult :=
  optionToExcept ("function call " ++ functionName)
    (callFunctionWithContext?
      fuel contract functionName context state args)

def callCalldataFrom? (fuel : Nat) (contract : CheckedContract)
    (state : CoreState) (sender value : Word) (calldata : List Byte) :
    Option CoreAbiCallResult :=
  SolidCore.Solidity.Source.ABI.Contract.callCalldataFrom?
    fuel contract.core state sender value calldata

def callCalldataFrom (fuel : Nat) (contract : CheckedContract)
    (state : CoreState) (sender value : Word) (calldata : List Byte) :
    Except TypeError CoreAbiCallResult :=
  optionToExcept ("ABI calldata call " ++ contract.decl.name)
    (callCalldataFrom? fuel contract state sender value calldata)

def callCalldataAtFrom? (fuel : Nat) (contract : CheckedContract)
    (state : CoreState) (self sender value : Word)
    (calldata : List Byte) : Option CoreAbiCallResult :=
  SolidCore.Solidity.Source.ABI.Contract.callCalldataAtFrom?
    fuel contract.core state self sender value calldata

def callCalldataAtFrom (fuel : Nat) (contract : CheckedContract)
    (state : CoreState) (self sender value : Word)
    (calldata : List Byte) : Except TypeError CoreAbiCallResult :=
  optionToExcept ("ABI calldata call " ++ contract.decl.name)
    (callCalldataAtFrom?
      fuel contract state self sender value calldata)

def callCalldataAt? (fuel : Nat) (contract : CheckedContract)
    (state : CoreState) (self : Word) (calldata : List Byte) :
    Option CoreAbiCallResult :=
  callCalldataAtFrom? fuel contract state self 0 0 calldata

def callCalldataAt (fuel : Nat) (contract : CheckedContract)
    (state : CoreState) (self : Word) (calldata : List Byte) :
    Except TypeError CoreAbiCallResult :=
  callCalldataAtFrom fuel contract state self 0 0 calldata

def callCalldata? (fuel : Nat) (contract : CheckedContract)
    (state : CoreState) (calldata : List Byte) :
    Option CoreAbiCallResult :=
  callCalldataFrom? fuel contract state 0 0 calldata

def callCalldata (fuel : Nat) (contract : CheckedContract)
    (state : CoreState) (calldata : List Byte) :
    Except TypeError CoreAbiCallResult :=
  callCalldataFrom fuel contract state 0 0 calldata

def callCalldataTransactionFrom? (fuel : Nat)
    (contract : CheckedContract) (state : CoreState)
    (sender value : Word) (calldata : List Byte) :
    Option CoreAbiCallResult :=
  SolidCore.Solidity.Source.ABI.Contract.callCalldataTransactionFrom?
    fuel contract.core state sender value calldata

def callCalldataTransactionFrom (fuel : Nat)
    (contract : CheckedContract) (state : CoreState)
    (sender value : Word) (calldata : List Byte) :
    Except TypeError CoreAbiCallResult :=
  optionToExcept ("ABI calldata transaction " ++ contract.decl.name)
    (callCalldataTransactionFrom?
      fuel contract state sender value calldata)

def callCalldataTransactionAtFrom? (fuel : Nat)
    (contract : CheckedContract) (state : CoreState)
    (self sender value : Word) (calldata : List Byte) :
    Option CoreAbiCallResult :=
  SolidCore.Solidity.Source.ABI.Contract.callCalldataTransactionAtFrom?
    fuel contract.core state self sender value calldata

def callCalldataTransactionAtFrom (fuel : Nat)
    (contract : CheckedContract) (state : CoreState)
    (self sender value : Word) (calldata : List Byte) :
    Except TypeError CoreAbiCallResult :=
  optionToExcept ("ABI calldata transaction " ++ contract.decl.name)
    (callCalldataTransactionAtFrom?
      fuel contract state self sender value calldata)

def callCalldataTransactionAt? (fuel : Nat)
    (contract : CheckedContract) (state : CoreState)
    (self : Word) (calldata : List Byte) :
    Option CoreAbiCallResult :=
  callCalldataTransactionAtFrom? fuel contract state self 0 0 calldata

def callCalldataTransactionAt (fuel : Nat)
    (contract : CheckedContract) (state : CoreState)
    (self : Word) (calldata : List Byte) :
    Except TypeError CoreAbiCallResult :=
  callCalldataTransactionAtFrom fuel contract state self 0 0 calldata

def callCalldataTransaction? (fuel : Nat)
    (contract : CheckedContract) (state : CoreState)
    (calldata : List Byte) : Option CoreAbiCallResult :=
  callCalldataTransactionFrom? fuel contract state 0 0 calldata

def callCalldataTransaction (fuel : Nat)
    (contract : CheckedContract) (state : CoreState)
    (calldata : List Byte) : Except TypeError CoreAbiCallResult :=
  callCalldataTransactionFrom fuel contract state 0 0 calldata

end CheckedContract

namespace CheckedProgram

def constructContractFrom? (fuel : Nat) (program : CheckedProgram)
    (name : Name) (state : CoreState) (sender value : Word)
    (args : List CoreValue) : Option CoreCallResult := do
  let contract ← contract? program name
  CheckedContract.constructFrom? fuel contract state sender value args

def constructContractFrom (fuel : Nat) (program : CheckedProgram)
    (name : Name) (state : CoreState) (sender value : Word)
    (args : List CoreValue) : Except TypeError CoreCallResult := do
  let contract ← contract program name
  CheckedContract.constructFrom fuel contract state sender value args

def constructContract? (fuel : Nat) (program : CheckedProgram)
    (name : Name) (state : CoreState) (args : List CoreValue) :
    Option CoreCallResult :=
  constructContractFrom? fuel program name state 0 0 args

def constructContract (fuel : Nat) (program : CheckedProgram)
    (name : Name) (state : CoreState) (args : List CoreValue) :
    Except TypeError CoreCallResult :=
  constructContractFrom fuel program name state 0 0 args

def callContract? (fuel : Nat) (program : CheckedProgram)
    (name : Name) (target : CallTarget) (state : CoreState)
    (args : List CoreValue) : Option CoreCallResult := do
  let contract ← contract? program name
  CheckedContract.call? fuel contract target state args

def callContract (fuel : Nat) (program : CheckedProgram)
    (name : Name) (target : CallTarget) (state : CoreState)
    (args : List CoreValue) : Except TypeError CoreCallResult := do
  let contract ← contract program name
  CheckedContract.call fuel contract target state args

def callContractTransaction? (fuel : Nat) (program : CheckedProgram)
    (name : Name) (target : CallTarget) (state : CoreState)
    (args : List CoreValue) : Option CoreCallResult := do
  let contract ← contract? program name
  CheckedContract.callTransaction? fuel contract target state args

def callContractTransaction (fuel : Nat) (program : CheckedProgram)
    (name : Name) (target : CallTarget) (state : CoreState)
    (args : List CoreValue) : Except TypeError CoreCallResult := do
  let contract ← contract program name
  CheckedContract.callTransaction fuel contract target state args

def coreFunction? (program : CheckedProgram)
    (name functionName : Name) : Option CoreFunctionDef := do
  let contract ← contract? program name
  CheckedContract.coreFunction? contract functionName

def coreFunction (program : CheckedProgram)
    (name functionName : Name) : Except TypeError CoreFunctionDef := do
  let contract ← contract program name
  CheckedContract.coreFunction contract functionName

def functionCalldata? (program : CheckedProgram)
    (name functionName : Name) (args : List CoreValue) :
    Option (List Byte) := do
  let contract ← contract? program name
  CheckedContract.functionCalldata? contract functionName args

def functionCalldata (program : CheckedProgram)
    (name functionName : Name) (args : List CoreValue) :
    Except TypeError (List Byte) := do
  let contract ← contract program name
  CheckedContract.functionCalldata contract functionName args

def callFunctionWithContext? (fuel : Nat)
    (program : CheckedProgram) (name functionName : Name)
    (context : SolidCore.Solidity.Source.Context)
    (state : CoreState) (args : List CoreValue) :
    Option CoreCallResult := do
  let contract ← contract? program name
  CheckedContract.callFunctionWithContext?
    fuel contract functionName context state args

def callFunctionWithContext (fuel : Nat)
    (program : CheckedProgram) (name functionName : Name)
    (context : SolidCore.Solidity.Source.Context)
    (state : CoreState) (args : List CoreValue) :
    Except TypeError CoreCallResult := do
  let contract ← contract program name
  CheckedContract.callFunctionWithContext
    fuel contract functionName context state args

def callCalldataFrom? (fuel : Nat) (program : CheckedProgram)
    (name : Name) (state : CoreState) (sender value : Word)
    (calldata : List Byte) : Option CoreAbiCallResult := do
  let contract ← contract? program name
  CheckedContract.callCalldataFrom? fuel contract state sender value calldata

def callCalldataFrom (fuel : Nat) (program : CheckedProgram)
    (name : Name) (state : CoreState) (sender value : Word)
    (calldata : List Byte) : Except TypeError CoreAbiCallResult := do
  let contract ← contract program name
  CheckedContract.callCalldataFrom fuel contract state sender value calldata

def callCalldataAtFrom? (fuel : Nat) (program : CheckedProgram)
    (name : Name) (state : CoreState) (self sender value : Word)
    (calldata : List Byte) : Option CoreAbiCallResult := do
  let contract ← contract? program name
  CheckedContract.callCalldataAtFrom?
    fuel contract state self sender value calldata

def callCalldataAtFrom (fuel : Nat) (program : CheckedProgram)
    (name : Name) (state : CoreState) (self sender value : Word)
    (calldata : List Byte) : Except TypeError CoreAbiCallResult := do
  let contract ← contract program name
  CheckedContract.callCalldataAtFrom
    fuel contract state self sender value calldata

def callCalldataAt? (fuel : Nat) (program : CheckedProgram)
    (name : Name) (state : CoreState) (self : Word)
    (calldata : List Byte) : Option CoreAbiCallResult :=
  callCalldataAtFrom? fuel program name state self 0 0 calldata

def callCalldataAt (fuel : Nat) (program : CheckedProgram)
    (name : Name) (state : CoreState) (self : Word)
    (calldata : List Byte) : Except TypeError CoreAbiCallResult :=
  callCalldataAtFrom fuel program name state self 0 0 calldata

def callCalldata? (fuel : Nat) (program : CheckedProgram)
    (name : Name) (state : CoreState) (calldata : List Byte) :
    Option CoreAbiCallResult :=
  callCalldataFrom? fuel program name state 0 0 calldata

def callCalldata (fuel : Nat) (program : CheckedProgram)
    (name : Name) (state : CoreState) (calldata : List Byte) :
    Except TypeError CoreAbiCallResult :=
  callCalldataFrom fuel program name state 0 0 calldata

def callCalldataTransactionFrom? (fuel : Nat)
    (program : CheckedProgram) (name : Name)
    (state : CoreState) (sender value : Word) (calldata : List Byte) :
    Option CoreAbiCallResult := do
  let contract ← contract? program name
  CheckedContract.callCalldataTransactionFrom?
    fuel contract state sender value calldata

def callCalldataTransactionFrom (fuel : Nat)
    (program : CheckedProgram) (name : Name)
    (state : CoreState) (sender value : Word) (calldata : List Byte) :
    Except TypeError CoreAbiCallResult := do
  let contract ← contract program name
  CheckedContract.callCalldataTransactionFrom
    fuel contract state sender value calldata

def callCalldataTransactionAtFrom? (fuel : Nat)
    (program : CheckedProgram) (name : Name)
    (state : CoreState) (self sender value : Word) (calldata : List Byte) :
    Option CoreAbiCallResult := do
  let contract ← contract? program name
  CheckedContract.callCalldataTransactionAtFrom?
    fuel contract state self sender value calldata

def callCalldataTransactionAtFrom (fuel : Nat)
    (program : CheckedProgram) (name : Name)
    (state : CoreState) (self sender value : Word) (calldata : List Byte) :
    Except TypeError CoreAbiCallResult := do
  let contract ← contract program name
  CheckedContract.callCalldataTransactionAtFrom
    fuel contract state self sender value calldata

def callCalldataTransactionAt? (fuel : Nat)
    (program : CheckedProgram) (name : Name)
    (state : CoreState) (self : Word) (calldata : List Byte) :
    Option CoreAbiCallResult :=
  callCalldataTransactionAtFrom?
    fuel program name state self 0 0 calldata

def callCalldataTransactionAt (fuel : Nat)
    (program : CheckedProgram) (name : Name)
    (state : CoreState) (self : Word) (calldata : List Byte) :
    Except TypeError CoreAbiCallResult :=
  callCalldataTransactionAtFrom
    fuel program name state self 0 0 calldata

def callCalldataTransaction? (fuel : Nat)
    (program : CheckedProgram) (name : Name)
    (state : CoreState) (calldata : List Byte) :
    Option CoreAbiCallResult :=
  callCalldataTransactionFrom? fuel program name state 0 0 calldata

def callCalldataTransaction (fuel : Nat)
    (program : CheckedProgram) (name : Name)
    (state : CoreState) (calldata : List Byte) :
    Except TypeError CoreAbiCallResult :=
  callCalldataTransactionFrom fuel program name state 0 0 calldata

end CheckedProgram

class CheckedInput (α : Type) where
  checkedProgramOf : α -> Except TypeError CheckedProgram
  defaultContractName? : α -> Option Name

instance checkedInputCheckedProgram : CheckedInput CheckedProgram where
  checkedProgramOf program := Except.ok program
  defaultContractName? _ := none

instance checkedInputCheckedSourceUnit :
    CheckedInput CheckedSourceUnit where
  checkedProgramOf checked := do
    let checked ← TypecheckedInput.checkedSourceUnit checked
    CheckedProgram.fromChecked checked
  defaultContractName? :=
    TypecheckedInput.defaultContractName?

instance checkedInputSourceUnit : CheckedInput SourceUnitAst where
  checkedProgramOf source := do
    let checked ← TypecheckedInput.checkedSourceUnit source
    CheckedProgram.fromChecked checked
  defaultContractName? :=
    TypecheckedInput.defaultContractName?

instance checkedInputContractDecl : CheckedInput SourceContractDecl where
  checkedProgramOf decl := do
    let checked ← TypecheckedInput.checkedSourceUnit decl
    CheckedProgram.fromChecked checked
  defaultContractName? :=
    TypecheckedInput.defaultContractName?

namespace CheckedInput

def program? {α : Type} [CheckedInput α] (input : α) :
    Option CheckedProgram :=
  Result.toOption (checkedProgramOf input)

def program {α : Type} [CheckedInput α] (input : α) :
    Except TypeError CheckedProgram :=
  checkedProgramOf input

def checkedSourceUnit? {α : Type} [CheckedInput α] (input : α) :
    Option CheckedSourceUnit := do
  let checkedProgram ← program? input
  some checkedProgram.checked

def checkedSourceUnit {α : Type} [CheckedInput α] (input : α) :
    Except TypeError CheckedSourceUnit := do
  let checkedProgram ← program input
  Except.ok checkedProgram.checked

def defaultContractName {α : Type} [CheckedInput α] (input : α) :
    Except TypeError Name :=
  optionToExcept "default contract name" (defaultContractName? input)

def contract? {α : Type} [CheckedInput α] (input : α)
    (name : Name) : Option CheckedContract := do
  let checkedProgram ← program? input
  CheckedProgram.contract? checkedProgram name

def contract {α : Type} [CheckedInput α] (input : α)
    (name : Name) : Except TypeError CheckedContract := do
  let checkedProgram ← program input
  CheckedProgram.contract checkedProgram name

def ownContract? {α : Type} [CheckedInput α] (input : α) :
    Option CheckedContract := do
  let name ← defaultContractName? input
  contract? input name

def ownContract {α : Type} [CheckedInput α] (input : α) :
    Except TypeError CheckedContract := do
  let name ← defaultContractName input
  contract input name

def toCoreContract? {α : Type} [CheckedInput α] (input : α)
    (name : Name) : Option CoreContract := do
  let checkedProgram ← program? input
  CheckedProgram.toCoreContract? checkedProgram name

def toCoreContract {α : Type} [CheckedInput α] (input : α)
    (name : Name) : Except TypeError CoreContract := do
  let checkedProgram ← program input
  CheckedProgram.toCoreContract checkedProgram name

def ownToCoreContract? {α : Type} [CheckedInput α] (input : α) :
    Option CoreContract := do
  let checkedContract ← ownContract? input
  some checkedContract.core

def ownToCoreContract {α : Type} [CheckedInput α] (input : α) :
    Except TypeError CoreContract := do
  let checkedContract ← ownContract input
  Except.ok checkedContract.core

def toCoreContracts? {α : Type} [CheckedInput α] (input : α) :
    Option (List CoreContract) := do
  let checkedProgram ← program? input
  CheckedProgram.toCoreContracts? checkedProgram

def toCoreContracts {α : Type} [CheckedInput α] (input : α) :
    Except TypeError (List CoreContract) := do
  let checkedProgram ← program input
  CheckedProgram.toCoreContracts checkedProgram

def constructContractFrom? {α : Type} [CheckedInput α]
    (fuel : Nat) (input : α) (name : Name) (state : CoreState)
    (sender value : Word) (args : List CoreValue) :
    Option CoreCallResult := do
  let checkedProgram ← program? input
  CheckedProgram.constructContractFrom?
    fuel checkedProgram name state sender value args

def constructContractFrom {α : Type} [CheckedInput α]
    (fuel : Nat) (input : α) (name : Name) (state : CoreState)
    (sender value : Word) (args : List CoreValue) :
    Except TypeError CoreCallResult := do
  let checkedProgram ← program input
  CheckedProgram.constructContractFrom
    fuel checkedProgram name state sender value args

def constructContract? {α : Type} [CheckedInput α]
    (fuel : Nat) (input : α) (name : Name) (state : CoreState)
    (args : List CoreValue) : Option CoreCallResult :=
  constructContractFrom? fuel input name state 0 0 args

def constructContract {α : Type} [CheckedInput α]
    (fuel : Nat) (input : α) (name : Name) (state : CoreState)
    (args : List CoreValue) : Except TypeError CoreCallResult :=
  constructContractFrom fuel input name state 0 0 args

def ownConstructFrom? {α : Type} [CheckedInput α]
    (fuel : Nat) (input : α) (state : CoreState)
    (sender value : Word) (args : List CoreValue) :
    Option CoreCallResult := do
  let checkedContract ← ownContract? input
  CheckedContract.constructFrom? fuel checkedContract state sender value args

def ownConstructFrom {α : Type} [CheckedInput α]
    (fuel : Nat) (input : α) (state : CoreState)
    (sender value : Word) (args : List CoreValue) :
    Except TypeError CoreCallResult := do
  let checkedContract ← ownContract input
  CheckedContract.constructFrom fuel checkedContract state sender value args

def ownConstruct? {α : Type} [CheckedInput α]
    (fuel : Nat) (input : α) (state : CoreState)
    (args : List CoreValue) : Option CoreCallResult :=
  ownConstructFrom? fuel input state 0 0 args

def ownConstruct {α : Type} [CheckedInput α]
    (fuel : Nat) (input : α) (state : CoreState)
    (args : List CoreValue) : Except TypeError CoreCallResult :=
  ownConstructFrom fuel input state 0 0 args

def callContract? {α : Type} [CheckedInput α]
    (fuel : Nat) (input : α) (name : Name) (target : CallTarget)
    (state : CoreState) (args : List CoreValue) :
    Option CoreCallResult := do
  let checkedProgram ← program? input
  CheckedProgram.callContract? fuel checkedProgram name target state args

def callContract {α : Type} [CheckedInput α]
    (fuel : Nat) (input : α) (name : Name) (target : CallTarget)
    (state : CoreState) (args : List CoreValue) :
    Except TypeError CoreCallResult := do
  let checkedProgram ← program input
  CheckedProgram.callContract fuel checkedProgram name target state args

def ownCall? {α : Type} [CheckedInput α]
    (fuel : Nat) (input : α) (target : CallTarget)
    (state : CoreState) (args : List CoreValue) :
    Option CoreCallResult := do
  let checkedContract ← ownContract? input
  CheckedContract.call? fuel checkedContract target state args

def ownCall {α : Type} [CheckedInput α]
    (fuel : Nat) (input : α) (target : CallTarget)
    (state : CoreState) (args : List CoreValue) :
    Except TypeError CoreCallResult := do
  let checkedContract ← ownContract input
  CheckedContract.call fuel checkedContract target state args

def callContractTransaction? {α : Type} [CheckedInput α]
    (fuel : Nat) (input : α) (name : Name) (target : CallTarget)
    (state : CoreState) (args : List CoreValue) :
    Option CoreCallResult := do
  let checkedProgram ← program? input
  CheckedProgram.callContractTransaction?
    fuel checkedProgram name target state args

def callContractTransaction {α : Type} [CheckedInput α]
    (fuel : Nat) (input : α) (name : Name) (target : CallTarget)
    (state : CoreState) (args : List CoreValue) :
    Except TypeError CoreCallResult := do
  let checkedProgram ← program input
  CheckedProgram.callContractTransaction
    fuel checkedProgram name target state args

def ownCallTransaction? {α : Type} [CheckedInput α]
    (fuel : Nat) (input : α) (target : CallTarget)
    (state : CoreState) (args : List CoreValue) :
    Option CoreCallResult := do
  let checkedContract ← ownContract? input
  CheckedContract.callTransaction? fuel checkedContract target state args

def ownCallTransaction {α : Type} [CheckedInput α]
    (fuel : Nat) (input : α) (target : CallTarget)
    (state : CoreState) (args : List CoreValue) :
    Except TypeError CoreCallResult := do
  let checkedContract ← ownContract input
  CheckedContract.callTransaction fuel checkedContract target state args

def coreFunction? {α : Type} [CheckedInput α] (input : α)
    (name functionName : Name) : Option CoreFunctionDef := do
  let checkedProgram ← program? input
  CheckedProgram.coreFunction? checkedProgram name functionName

def coreFunction {α : Type} [CheckedInput α] (input : α)
    (name functionName : Name) : Except TypeError CoreFunctionDef := do
  let checkedProgram ← program input
  CheckedProgram.coreFunction checkedProgram name functionName

def ownCoreFunction? {α : Type} [CheckedInput α] (input : α)
    (functionName : Name) : Option CoreFunctionDef := do
  let checkedContract ← ownContract? input
  CheckedContract.coreFunction? checkedContract functionName

def ownCoreFunction {α : Type} [CheckedInput α] (input : α)
    (functionName : Name) : Except TypeError CoreFunctionDef := do
  let checkedContract ← ownContract input
  CheckedContract.coreFunction checkedContract functionName

def functionCalldata? {α : Type} [CheckedInput α] (input : α)
    (name functionName : Name) (args : List CoreValue) :
    Option (List Byte) := do
  let checkedProgram ← program? input
  CheckedProgram.functionCalldata? checkedProgram name functionName args

def functionCalldata {α : Type} [CheckedInput α] (input : α)
    (name functionName : Name) (args : List CoreValue) :
    Except TypeError (List Byte) := do
  let checkedProgram ← program input
  CheckedProgram.functionCalldata checkedProgram name functionName args

def ownFunctionCalldata? {α : Type} [CheckedInput α] (input : α)
    (functionName : Name) (args : List CoreValue) :
    Option (List Byte) := do
  let checkedContract ← ownContract? input
  CheckedContract.functionCalldata? checkedContract functionName args

def ownFunctionCalldata {α : Type} [CheckedInput α] (input : α)
    (functionName : Name) (args : List CoreValue) :
    Except TypeError (List Byte) := do
  let checkedContract ← ownContract input
  CheckedContract.functionCalldata checkedContract functionName args

def callFunctionWithContext? {α : Type} [CheckedInput α]
    (fuel : Nat) (input : α) (name functionName : Name)
    (context : SolidCore.Solidity.Source.Context)
    (state : CoreState) (args : List CoreValue) :
    Option CoreCallResult := do
  let checkedProgram ← program? input
  CheckedProgram.callFunctionWithContext?
    fuel checkedProgram name functionName context state args

def callFunctionWithContext {α : Type} [CheckedInput α]
    (fuel : Nat) (input : α) (name functionName : Name)
    (context : SolidCore.Solidity.Source.Context)
    (state : CoreState) (args : List CoreValue) :
    Except TypeError CoreCallResult := do
  let checkedProgram ← program input
  CheckedProgram.callFunctionWithContext
    fuel checkedProgram name functionName context state args

def ownCallFunctionWithContext? {α : Type} [CheckedInput α]
    (fuel : Nat) (input : α) (functionName : Name)
    (context : SolidCore.Solidity.Source.Context)
    (state : CoreState) (args : List CoreValue) :
    Option CoreCallResult := do
  let checkedContract ← ownContract? input
  CheckedContract.callFunctionWithContext?
    fuel checkedContract functionName context state args

def ownCallFunctionWithContext {α : Type} [CheckedInput α]
    (fuel : Nat) (input : α) (functionName : Name)
    (context : SolidCore.Solidity.Source.Context)
    (state : CoreState) (args : List CoreValue) :
    Except TypeError CoreCallResult := do
  let checkedContract ← ownContract input
  CheckedContract.callFunctionWithContext
    fuel checkedContract functionName context state args

def callCalldataFrom? {α : Type} [CheckedInput α]
    (fuel : Nat) (input : α) (name : Name) (state : CoreState)
    (sender value : Word) (calldata : List Byte) :
    Option CoreAbiCallResult := do
  let checkedProgram ← program? input
  CheckedProgram.callCalldataFrom?
    fuel checkedProgram name state sender value calldata

def callCalldataFrom {α : Type} [CheckedInput α]
    (fuel : Nat) (input : α) (name : Name) (state : CoreState)
    (sender value : Word) (calldata : List Byte) :
    Except TypeError CoreAbiCallResult := do
  let checkedProgram ← program input
  CheckedProgram.callCalldataFrom
    fuel checkedProgram name state sender value calldata

def callCalldataAtFrom? {α : Type} [CheckedInput α]
    (fuel : Nat) (input : α) (name : Name) (state : CoreState)
    (self sender value : Word) (calldata : List Byte) :
    Option CoreAbiCallResult := do
  let checkedProgram ← program? input
  CheckedProgram.callCalldataAtFrom?
    fuel checkedProgram name state self sender value calldata

def callCalldataAtFrom {α : Type} [CheckedInput α]
    (fuel : Nat) (input : α) (name : Name) (state : CoreState)
    (self sender value : Word) (calldata : List Byte) :
    Except TypeError CoreAbiCallResult := do
  let checkedProgram ← program input
  CheckedProgram.callCalldataAtFrom
    fuel checkedProgram name state self sender value calldata

def callCalldataAt? {α : Type} [CheckedInput α]
    (fuel : Nat) (input : α) (name : Name) (state : CoreState)
    (self : Word) (calldata : List Byte) : Option CoreAbiCallResult :=
  callCalldataAtFrom? fuel input name state self 0 0 calldata

def callCalldataAt {α : Type} [CheckedInput α]
    (fuel : Nat) (input : α) (name : Name) (state : CoreState)
    (self : Word) (calldata : List Byte) :
    Except TypeError CoreAbiCallResult :=
  callCalldataAtFrom fuel input name state self 0 0 calldata

def callCalldata? {α : Type} [CheckedInput α]
    (fuel : Nat) (input : α) (name : Name) (state : CoreState)
    (calldata : List Byte) : Option CoreAbiCallResult :=
  callCalldataFrom? fuel input name state 0 0 calldata

def callCalldata {α : Type} [CheckedInput α]
    (fuel : Nat) (input : α) (name : Name) (state : CoreState)
    (calldata : List Byte) : Except TypeError CoreAbiCallResult :=
  callCalldataFrom fuel input name state 0 0 calldata

def ownCallCalldataFrom? {α : Type} [CheckedInput α]
    (fuel : Nat) (input : α) (state : CoreState)
    (sender value : Word) (calldata : List Byte) :
    Option CoreAbiCallResult := do
  let checkedContract ← ownContract? input
  CheckedContract.callCalldataFrom?
    fuel checkedContract state sender value calldata

def ownCallCalldataFrom {α : Type} [CheckedInput α]
    (fuel : Nat) (input : α) (state : CoreState)
    (sender value : Word) (calldata : List Byte) :
    Except TypeError CoreAbiCallResult := do
  let checkedContract ← ownContract input
  CheckedContract.callCalldataFrom
    fuel checkedContract state sender value calldata

def ownCallCalldataAtFrom? {α : Type} [CheckedInput α]
    (fuel : Nat) (input : α) (state : CoreState)
    (self sender value : Word) (calldata : List Byte) :
    Option CoreAbiCallResult := do
  let checkedContract ← ownContract? input
  CheckedContract.callCalldataAtFrom?
    fuel checkedContract state self sender value calldata

def ownCallCalldataAtFrom {α : Type} [CheckedInput α]
    (fuel : Nat) (input : α) (state : CoreState)
    (self sender value : Word) (calldata : List Byte) :
    Except TypeError CoreAbiCallResult := do
  let checkedContract ← ownContract input
  CheckedContract.callCalldataAtFrom
    fuel checkedContract state self sender value calldata

def ownCallCalldataAt? {α : Type} [CheckedInput α]
    (fuel : Nat) (input : α) (state : CoreState)
    (self : Word) (calldata : List Byte) : Option CoreAbiCallResult :=
  ownCallCalldataAtFrom? fuel input state self 0 0 calldata

def ownCallCalldataAt {α : Type} [CheckedInput α]
    (fuel : Nat) (input : α) (state : CoreState)
    (self : Word) (calldata : List Byte) :
    Except TypeError CoreAbiCallResult :=
  ownCallCalldataAtFrom fuel input state self 0 0 calldata

def ownCallCalldata? {α : Type} [CheckedInput α]
    (fuel : Nat) (input : α) (state : CoreState)
    (calldata : List Byte) : Option CoreAbiCallResult :=
  ownCallCalldataFrom? fuel input state 0 0 calldata

def ownCallCalldata {α : Type} [CheckedInput α]
    (fuel : Nat) (input : α) (state : CoreState)
    (calldata : List Byte) : Except TypeError CoreAbiCallResult :=
  ownCallCalldataFrom fuel input state 0 0 calldata

def callCalldataTransactionFrom? {α : Type} [CheckedInput α]
    (fuel : Nat) (input : α) (name : Name) (state : CoreState)
    (sender value : Word) (calldata : List Byte) :
    Option CoreAbiCallResult := do
  let checkedProgram ← program? input
  CheckedProgram.callCalldataTransactionFrom?
    fuel checkedProgram name state sender value calldata

def callCalldataTransactionFrom {α : Type} [CheckedInput α]
    (fuel : Nat) (input : α) (name : Name) (state : CoreState)
    (sender value : Word) (calldata : List Byte) :
    Except TypeError CoreAbiCallResult := do
  let checkedProgram ← program input
  CheckedProgram.callCalldataTransactionFrom
    fuel checkedProgram name state sender value calldata

def callCalldataTransactionAtFrom? {α : Type} [CheckedInput α]
    (fuel : Nat) (input : α) (name : Name) (state : CoreState)
    (self sender value : Word) (calldata : List Byte) :
    Option CoreAbiCallResult := do
  let checkedProgram ← program? input
  CheckedProgram.callCalldataTransactionAtFrom?
    fuel checkedProgram name state self sender value calldata

def callCalldataTransactionAtFrom {α : Type} [CheckedInput α]
    (fuel : Nat) (input : α) (name : Name) (state : CoreState)
    (self sender value : Word) (calldata : List Byte) :
    Except TypeError CoreAbiCallResult := do
  let checkedProgram ← program input
  CheckedProgram.callCalldataTransactionAtFrom
    fuel checkedProgram name state self sender value calldata

def callCalldataTransactionAt? {α : Type} [CheckedInput α]
    (fuel : Nat) (input : α) (name : Name) (state : CoreState)
    (self : Word) (calldata : List Byte) : Option CoreAbiCallResult :=
  callCalldataTransactionAtFrom?
    fuel input name state self 0 0 calldata

def callCalldataTransactionAt {α : Type} [CheckedInput α]
    (fuel : Nat) (input : α) (name : Name) (state : CoreState)
    (self : Word) (calldata : List Byte) :
    Except TypeError CoreAbiCallResult :=
  callCalldataTransactionAtFrom
    fuel input name state self 0 0 calldata

def callCalldataTransaction? {α : Type} [CheckedInput α]
    (fuel : Nat) (input : α) (name : Name) (state : CoreState)
    (calldata : List Byte) : Option CoreAbiCallResult :=
  callCalldataTransactionFrom? fuel input name state 0 0 calldata

def callCalldataTransaction {α : Type} [CheckedInput α]
    (fuel : Nat) (input : α) (name : Name) (state : CoreState)
    (calldata : List Byte) : Except TypeError CoreAbiCallResult :=
  callCalldataTransactionFrom fuel input name state 0 0 calldata

def ownCallCalldataTransactionFrom? {α : Type} [CheckedInput α]
    (fuel : Nat) (input : α) (state : CoreState)
    (sender value : Word) (calldata : List Byte) :
    Option CoreAbiCallResult := do
  let checkedContract ← ownContract? input
  CheckedContract.callCalldataTransactionFrom?
    fuel checkedContract state sender value calldata

def ownCallCalldataTransactionFrom {α : Type} [CheckedInput α]
    (fuel : Nat) (input : α) (state : CoreState)
    (sender value : Word) (calldata : List Byte) :
    Except TypeError CoreAbiCallResult := do
  let checkedContract ← ownContract input
  CheckedContract.callCalldataTransactionFrom
    fuel checkedContract state sender value calldata

def ownCallCalldataTransactionAtFrom? {α : Type} [CheckedInput α]
    (fuel : Nat) (input : α) (state : CoreState)
    (self sender value : Word) (calldata : List Byte) :
    Option CoreAbiCallResult := do
  let checkedContract ← ownContract? input
  CheckedContract.callCalldataTransactionAtFrom?
    fuel checkedContract state self sender value calldata

def ownCallCalldataTransactionAtFrom {α : Type} [CheckedInput α]
    (fuel : Nat) (input : α) (state : CoreState)
    (self sender value : Word) (calldata : List Byte) :
    Except TypeError CoreAbiCallResult := do
  let checkedContract ← ownContract input
  CheckedContract.callCalldataTransactionAtFrom
    fuel checkedContract state self sender value calldata

def ownCallCalldataTransactionAt? {α : Type} [CheckedInput α]
    (fuel : Nat) (input : α) (state : CoreState)
    (self : Word) (calldata : List Byte) : Option CoreAbiCallResult :=
  ownCallCalldataTransactionAtFrom?
    fuel input state self 0 0 calldata

def ownCallCalldataTransactionAt {α : Type} [CheckedInput α]
    (fuel : Nat) (input : α) (state : CoreState)
    (self : Word) (calldata : List Byte) :
    Except TypeError CoreAbiCallResult :=
  ownCallCalldataTransactionAtFrom
    fuel input state self 0 0 calldata

def ownCallCalldataTransaction? {α : Type} [CheckedInput α]
    (fuel : Nat) (input : α) (state : CoreState)
    (calldata : List Byte) : Option CoreAbiCallResult :=
  ownCallCalldataTransactionFrom? fuel input state 0 0 calldata

def ownCallCalldataTransaction {α : Type} [CheckedInput α]
    (fuel : Nat) (input : α) (state : CoreState)
    (calldata : List Byte) : Except TypeError CoreAbiCallResult :=
  ownCallCalldataTransactionFrom fuel input state 0 0 calldata

end CheckedInput

namespace CheckedSourceUnit

def toCoreContract? (checked : CheckedSourceUnit) (name : Name) :
    Option CoreContract :=
  CheckedInput.toCoreContract? checked name

def toCoreContract (checked : CheckedSourceUnit) (name : Name) :
    Except TypeError CoreContract :=
  CheckedInput.toCoreContract checked name

def toCoreContracts? (checked : CheckedSourceUnit) :
    Option (List CoreContract) :=
  CheckedInput.toCoreContracts? checked

def toCoreContracts (checked : CheckedSourceUnit) :
    Except TypeError (List CoreContract) :=
  CheckedInput.toCoreContracts checked

def constructContractFrom? (fuel : Nat) (checked : CheckedSourceUnit)
    (name : Name) (state : CoreState) (sender value : Word)
    (args : List CoreValue) : Option CoreCallResult :=
  CheckedInput.constructContractFrom?
    fuel checked name state sender value args

def constructContractFrom (fuel : Nat) (checked : CheckedSourceUnit)
    (name : Name) (state : CoreState) (sender value : Word)
    (args : List CoreValue) : Except TypeError CoreCallResult :=
  CheckedInput.constructContractFrom
    fuel checked name state sender value args

def constructContract? (fuel : Nat) (checked : CheckedSourceUnit)
    (name : Name) (state : CoreState) (args : List CoreValue) :
    Option CoreCallResult :=
  CheckedInput.constructContract? fuel checked name state args

def constructContract (fuel : Nat) (checked : CheckedSourceUnit)
    (name : Name) (state : CoreState) (args : List CoreValue) :
    Except TypeError CoreCallResult :=
  CheckedInput.constructContract fuel checked name state args

def callContract? (fuel : Nat) (checked : CheckedSourceUnit)
    (name : Name) (target : CallTarget) (state : CoreState)
    (args : List CoreValue) : Option CoreCallResult :=
  CheckedInput.callContract? fuel checked name target state args

def callContract (fuel : Nat) (checked : CheckedSourceUnit)
    (name : Name) (target : CallTarget) (state : CoreState)
    (args : List CoreValue) : Except TypeError CoreCallResult :=
  CheckedInput.callContract fuel checked name target state args

def callContractTransaction? (fuel : Nat) (checked : CheckedSourceUnit)
    (name : Name) (target : CallTarget) (state : CoreState)
    (args : List CoreValue) : Option CoreCallResult :=
  CheckedInput.callContractTransaction?
    fuel checked name target state args

def callContractTransaction (fuel : Nat) (checked : CheckedSourceUnit)
    (name : Name) (target : CallTarget) (state : CoreState)
    (args : List CoreValue) : Except TypeError CoreCallResult :=
  CheckedInput.callContractTransaction
    fuel checked name target state args

def coreFunction? (checked : CheckedSourceUnit)
    (name functionName : Name) : Option CoreFunctionDef :=
  CheckedInput.coreFunction? checked name functionName

def coreFunction (checked : CheckedSourceUnit)
    (name functionName : Name) : Except TypeError CoreFunctionDef :=
  CheckedInput.coreFunction checked name functionName

def functionCalldata? (checked : CheckedSourceUnit)
    (name functionName : Name) (args : List CoreValue) :
    Option (List Byte) :=
  CheckedInput.functionCalldata? checked name functionName args

def functionCalldata (checked : CheckedSourceUnit)
    (name functionName : Name) (args : List CoreValue) :
    Except TypeError (List Byte) :=
  CheckedInput.functionCalldata checked name functionName args

def callFunctionWithContext? (fuel : Nat)
    (checked : CheckedSourceUnit) (name functionName : Name)
    (context : SolidCore.Solidity.Source.Context)
    (state : CoreState) (args : List CoreValue) :
    Option CoreCallResult :=
  CheckedInput.callFunctionWithContext?
    fuel checked name functionName context state args

def callFunctionWithContext (fuel : Nat)
    (checked : CheckedSourceUnit) (name functionName : Name)
    (context : SolidCore.Solidity.Source.Context)
    (state : CoreState) (args : List CoreValue) :
    Except TypeError CoreCallResult :=
  CheckedInput.callFunctionWithContext
    fuel checked name functionName context state args

def callCalldataFrom? (fuel : Nat) (checked : CheckedSourceUnit)
    (name : Name) (state : CoreState) (sender value : Word)
    (calldata : List Byte) : Option CoreAbiCallResult :=
  CheckedInput.callCalldataFrom?
    fuel checked name state sender value calldata

def callCalldataFrom (fuel : Nat) (checked : CheckedSourceUnit)
    (name : Name) (state : CoreState) (sender value : Word)
    (calldata : List Byte) : Except TypeError CoreAbiCallResult :=
  CheckedInput.callCalldataFrom
    fuel checked name state sender value calldata

def callCalldataAtFrom? (fuel : Nat) (checked : CheckedSourceUnit)
    (name : Name) (state : CoreState) (self sender value : Word)
    (calldata : List Byte) : Option CoreAbiCallResult :=
  CheckedInput.callCalldataAtFrom?
    fuel checked name state self sender value calldata

def callCalldataAtFrom (fuel : Nat) (checked : CheckedSourceUnit)
    (name : Name) (state : CoreState) (self sender value : Word)
    (calldata : List Byte) : Except TypeError CoreAbiCallResult :=
  CheckedInput.callCalldataAtFrom
    fuel checked name state self sender value calldata

def callCalldataAt? (fuel : Nat) (checked : CheckedSourceUnit)
    (name : Name) (state : CoreState) (self : Word)
    (calldata : List Byte) : Option CoreAbiCallResult :=
  CheckedInput.callCalldataAt? fuel checked name state self calldata

def callCalldataAt (fuel : Nat) (checked : CheckedSourceUnit)
    (name : Name) (state : CoreState) (self : Word)
    (calldata : List Byte) : Except TypeError CoreAbiCallResult :=
  CheckedInput.callCalldataAt fuel checked name state self calldata

def callCalldata? (fuel : Nat) (checked : CheckedSourceUnit)
    (name : Name) (state : CoreState) (calldata : List Byte) :
    Option CoreAbiCallResult :=
  CheckedInput.callCalldata? fuel checked name state calldata

def callCalldata (fuel : Nat) (checked : CheckedSourceUnit)
    (name : Name) (state : CoreState) (calldata : List Byte) :
    Except TypeError CoreAbiCallResult :=
  CheckedInput.callCalldata fuel checked name state calldata

def callCalldataTransactionFrom? (fuel : Nat)
    (checked : CheckedSourceUnit) (name : Name)
    (state : CoreState) (sender value : Word) (calldata : List Byte) :
    Option CoreAbiCallResult :=
  CheckedInput.callCalldataTransactionFrom?
    fuel checked name state sender value calldata

def callCalldataTransactionFrom (fuel : Nat)
    (checked : CheckedSourceUnit) (name : Name)
    (state : CoreState) (sender value : Word) (calldata : List Byte) :
    Except TypeError CoreAbiCallResult :=
  CheckedInput.callCalldataTransactionFrom
    fuel checked name state sender value calldata

def callCalldataTransactionAtFrom? (fuel : Nat)
    (checked : CheckedSourceUnit) (name : Name)
    (state : CoreState) (self sender value : Word)
    (calldata : List Byte) : Option CoreAbiCallResult :=
  CheckedInput.callCalldataTransactionAtFrom?
    fuel checked name state self sender value calldata

def callCalldataTransactionAtFrom (fuel : Nat)
    (checked : CheckedSourceUnit) (name : Name)
    (state : CoreState) (self sender value : Word)
    (calldata : List Byte) : Except TypeError CoreAbiCallResult :=
  CheckedInput.callCalldataTransactionAtFrom
    fuel checked name state self sender value calldata

def callCalldataTransactionAt? (fuel : Nat)
    (checked : CheckedSourceUnit) (name : Name)
    (state : CoreState) (self : Word) (calldata : List Byte) :
    Option CoreAbiCallResult :=
  CheckedInput.callCalldataTransactionAt?
    fuel checked name state self calldata

def callCalldataTransactionAt (fuel : Nat)
    (checked : CheckedSourceUnit) (name : Name)
    (state : CoreState) (self : Word) (calldata : List Byte) :
    Except TypeError CoreAbiCallResult :=
  CheckedInput.callCalldataTransactionAt
    fuel checked name state self calldata

def callCalldataTransaction? (fuel : Nat)
    (checked : CheckedSourceUnit) (name : Name)
    (state : CoreState) (calldata : List Byte) :
    Option CoreAbiCallResult :=
  CheckedInput.callCalldataTransaction? fuel checked name state calldata

def callCalldataTransaction (fuel : Nat)
    (checked : CheckedSourceUnit) (name : Name)
    (state : CoreState) (calldata : List Byte) :
    Except TypeError CoreAbiCallResult :=
  CheckedInput.callCalldataTransaction fuel checked name state calldata

end CheckedSourceUnit

namespace SourceUnit

def checked? (source : SourceUnitAst) :
    Option CheckedSourceUnit :=
  CheckedInput.checkedSourceUnit? source

def checkedProgram? (source : SourceUnitAst) :
    Option CheckedProgram :=
  CheckedInput.program? source

def checkedProgram (source : SourceUnitAst) :
    Except TypeError CheckedProgram :=
  CheckedInput.program source

def checkedToCoreContract? (source : SourceUnitAst)
    (name : Name) : Option CoreContract :=
  CheckedInput.toCoreContract? source name

def checkedToCoreContract (source : SourceUnitAst)
    (name : Name) : Except TypeError CoreContract :=
  CheckedInput.toCoreContract source name

def checkedToCoreContracts? (source : SourceUnitAst) :
    Option (List CoreContract) :=
  CheckedInput.toCoreContracts? source

def checkedToCoreContracts (source : SourceUnitAst) :
    Except TypeError (List CoreContract) :=
  CheckedInput.toCoreContracts source

def checkedConstructContractFrom? (fuel : Nat)
    (source : SourceUnitAst) (name : Name)
    (state : CoreState) (sender value : Word) (args : List CoreValue) :
    Option CoreCallResult :=
  CheckedInput.constructContractFrom?
    fuel source name state sender value args

def checkedConstructContractFrom (fuel : Nat)
    (source : SourceUnitAst) (name : Name)
    (state : CoreState) (sender value : Word) (args : List CoreValue) :
    Except TypeError CoreCallResult :=
  CheckedInput.constructContractFrom
    fuel source name state sender value args

def checkedConstructContract? (fuel : Nat)
    (source : SourceUnitAst) (name : Name)
    (state : CoreState) (args : List CoreValue) :
    Option CoreCallResult :=
  CheckedInput.constructContract? fuel source name state args

def checkedConstructContract (fuel : Nat)
    (source : SourceUnitAst) (name : Name)
    (state : CoreState) (args : List CoreValue) :
    Except TypeError CoreCallResult :=
  CheckedInput.constructContract fuel source name state args

def checkedCallContract? (fuel : Nat)
    (source : SourceUnitAst) (name : Name)
    (target : CallTarget) (state : CoreState) (args : List CoreValue) :
    Option CoreCallResult :=
  CheckedInput.callContract? fuel source name target state args

def checkedCallContract (fuel : Nat)
    (source : SourceUnitAst) (name : Name)
    (target : CallTarget) (state : CoreState) (args : List CoreValue) :
    Except TypeError CoreCallResult :=
  CheckedInput.callContract fuel source name target state args

def checkedCallContractTransaction? (fuel : Nat)
    (source : SourceUnitAst) (name : Name)
    (target : CallTarget) (state : CoreState) (args : List CoreValue) :
    Option CoreCallResult :=
  CheckedInput.callContractTransaction?
    fuel source name target state args

def checkedCallContractTransaction (fuel : Nat)
    (source : SourceUnitAst) (name : Name)
    (target : CallTarget) (state : CoreState) (args : List CoreValue) :
    Except TypeError CoreCallResult :=
  CheckedInput.callContractTransaction
    fuel source name target state args

def checkedCoreFunction? (source : SourceUnitAst)
    (name functionName : Name) : Option CoreFunctionDef :=
  CheckedInput.coreFunction? source name functionName

def checkedCoreFunction (source : SourceUnitAst)
    (name functionName : Name) : Except TypeError CoreFunctionDef :=
  CheckedInput.coreFunction source name functionName

def checkedFunctionCalldata? (source : SourceUnitAst)
    (name functionName : Name) (args : List CoreValue) :
    Option (List Byte) :=
  CheckedInput.functionCalldata? source name functionName args

def checkedFunctionCalldata (source : SourceUnitAst)
    (name functionName : Name) (args : List CoreValue) :
    Except TypeError (List Byte) :=
  CheckedInput.functionCalldata source name functionName args

def checkedCallFunctionWithContext? (fuel : Nat)
    (source : SourceUnitAst) (name functionName : Name)
    (context : SolidCore.Solidity.Source.Context)
    (state : CoreState) (args : List CoreValue) :
    Option CoreCallResult :=
  CheckedInput.callFunctionWithContext?
    fuel source name functionName context state args

def checkedCallFunctionWithContext (fuel : Nat)
    (source : SourceUnitAst) (name functionName : Name)
    (context : SolidCore.Solidity.Source.Context)
    (state : CoreState) (args : List CoreValue) :
    Except TypeError CoreCallResult :=
  CheckedInput.callFunctionWithContext
    fuel source name functionName context state args

def checkedCallCalldataFrom? (fuel : Nat)
    (source : SourceUnitAst) (name : Name)
    (state : CoreState) (sender value : Word) (calldata : List Byte) :
    Option CoreAbiCallResult :=
  CheckedInput.callCalldataFrom?
    fuel source name state sender value calldata

def checkedCallCalldataFrom (fuel : Nat)
    (source : SourceUnitAst) (name : Name)
    (state : CoreState) (sender value : Word) (calldata : List Byte) :
    Except TypeError CoreAbiCallResult :=
  CheckedInput.callCalldataFrom
    fuel source name state sender value calldata

def checkedCallCalldataAtFrom? (fuel : Nat)
    (source : SourceUnitAst) (name : Name)
    (state : CoreState) (self sender value : Word)
    (calldata : List Byte) : Option CoreAbiCallResult :=
  CheckedInput.callCalldataAtFrom?
    fuel source name state self sender value calldata

def checkedCallCalldataAtFrom (fuel : Nat)
    (source : SourceUnitAst) (name : Name)
    (state : CoreState) (self sender value : Word)
    (calldata : List Byte) : Except TypeError CoreAbiCallResult :=
  CheckedInput.callCalldataAtFrom
    fuel source name state self sender value calldata

def checkedCallCalldataAt? (fuel : Nat)
    (source : SourceUnitAst) (name : Name)
    (state : CoreState) (self : Word) (calldata : List Byte) :
    Option CoreAbiCallResult :=
  CheckedInput.callCalldataAt? fuel source name state self calldata

def checkedCallCalldataAt (fuel : Nat)
    (source : SourceUnitAst) (name : Name)
    (state : CoreState) (self : Word) (calldata : List Byte) :
    Except TypeError CoreAbiCallResult :=
  CheckedInput.callCalldataAt fuel source name state self calldata

def checkedCallCalldata? (fuel : Nat)
    (source : SourceUnitAst) (name : Name)
    (state : CoreState) (calldata : List Byte) :
    Option CoreAbiCallResult :=
  CheckedInput.callCalldata? fuel source name state calldata

def checkedCallCalldata (fuel : Nat)
    (source : SourceUnitAst) (name : Name)
    (state : CoreState) (calldata : List Byte) :
    Except TypeError CoreAbiCallResult :=
  CheckedInput.callCalldata fuel source name state calldata

def checkedCallCalldataTransactionFrom? (fuel : Nat)
    (source : SourceUnitAst) (name : Name)
    (state : CoreState) (sender value : Word) (calldata : List Byte) :
    Option CoreAbiCallResult :=
  CheckedInput.callCalldataTransactionFrom?
    fuel source name state sender value calldata

def checkedCallCalldataTransactionFrom (fuel : Nat)
    (source : SourceUnitAst) (name : Name)
    (state : CoreState) (sender value : Word) (calldata : List Byte) :
    Except TypeError CoreAbiCallResult :=
  CheckedInput.callCalldataTransactionFrom
    fuel source name state sender value calldata

def checkedCallCalldataTransactionAtFrom? (fuel : Nat)
    (source : SourceUnitAst) (name : Name)
    (state : CoreState) (self sender value : Word)
    (calldata : List Byte) : Option CoreAbiCallResult :=
  CheckedInput.callCalldataTransactionAtFrom?
    fuel source name state self sender value calldata

def checkedCallCalldataTransactionAtFrom (fuel : Nat)
    (source : SourceUnitAst) (name : Name)
    (state : CoreState) (self sender value : Word)
    (calldata : List Byte) : Except TypeError CoreAbiCallResult :=
  CheckedInput.callCalldataTransactionAtFrom
    fuel source name state self sender value calldata

def checkedCallCalldataTransactionAt? (fuel : Nat)
    (source : SourceUnitAst) (name : Name)
    (state : CoreState) (self : Word) (calldata : List Byte) :
    Option CoreAbiCallResult :=
  CheckedInput.callCalldataTransactionAt?
    fuel source name state self calldata

def checkedCallCalldataTransactionAt (fuel : Nat)
    (source : SourceUnitAst) (name : Name)
    (state : CoreState) (self : Word) (calldata : List Byte) :
    Except TypeError CoreAbiCallResult :=
  CheckedInput.callCalldataTransactionAt
    fuel source name state self calldata

def checkedCallCalldataTransaction? (fuel : Nat)
    (source : SourceUnitAst) (name : Name)
    (state : CoreState) (calldata : List Byte) :
    Option CoreAbiCallResult :=
  CheckedInput.callCalldataTransaction? fuel source name state calldata

def checkedCallCalldataTransaction (fuel : Nat)
    (source : SourceUnitAst) (name : Name)
    (state : CoreState) (calldata : List Byte) :
    Except TypeError CoreAbiCallResult :=
  CheckedInput.callCalldataTransaction fuel source name state calldata

end SourceUnit

namespace ContractDecl

def checked? (decl : SourceContractDecl) :
    Option CheckedSourceUnit :=
  CheckedInput.checkedSourceUnit? decl

def checkedProgram? (decl : SourceContractDecl) :
    Option CheckedProgram :=
  CheckedInput.program? decl

def checkedProgram (decl : SourceContractDecl) :
    Except TypeError CheckedProgram :=
  CheckedInput.program decl

def checkedContract? (decl : SourceContractDecl) :
    Option CheckedContract :=
  CheckedInput.ownContract? decl

def checkedContract (decl : SourceContractDecl) :
    Except TypeError CheckedContract :=
  CheckedInput.ownContract decl

def checkedToCore? (decl : SourceContractDecl) :
    Option CoreContract :=
  CheckedInput.ownToCoreContract? decl

def checkedToCore (decl : SourceContractDecl) :
    Except TypeError CoreContract :=
  CheckedInput.ownToCoreContract decl

def checkedConstructFrom? (fuel : Nat)
    (decl : SourceContractDecl) (state : CoreState)
    (sender value : Word) (args : List CoreValue) :
    Option CoreCallResult :=
  CheckedInput.ownConstructFrom? fuel decl state sender value args

def checkedConstructFrom (fuel : Nat)
    (decl : SourceContractDecl) (state : CoreState)
    (sender value : Word) (args : List CoreValue) :
    Except TypeError CoreCallResult :=
  CheckedInput.ownConstructFrom fuel decl state sender value args

def checkedConstruct? (fuel : Nat)
    (decl : SourceContractDecl) (state : CoreState)
    (args : List CoreValue) : Option CoreCallResult :=
  CheckedInput.ownConstruct? fuel decl state args

def checkedConstruct (fuel : Nat)
    (decl : SourceContractDecl) (state : CoreState)
    (args : List CoreValue) : Except TypeError CoreCallResult :=
  CheckedInput.ownConstruct fuel decl state args

def checkedCall? (fuel : Nat)
    (decl : SourceContractDecl) (target : CallTarget)
    (state : CoreState) (args : List CoreValue) : Option CoreCallResult :=
  CheckedInput.ownCall? fuel decl target state args

def checkedCall (fuel : Nat)
    (decl : SourceContractDecl) (target : CallTarget)
    (state : CoreState) (args : List CoreValue) :
    Except TypeError CoreCallResult :=
  CheckedInput.ownCall fuel decl target state args

def checkedCallTransaction? (fuel : Nat)
    (decl : SourceContractDecl) (target : CallTarget)
    (state : CoreState) (args : List CoreValue) : Option CoreCallResult :=
  CheckedInput.ownCallTransaction? fuel decl target state args

def checkedCallTransaction (fuel : Nat)
    (decl : SourceContractDecl) (target : CallTarget)
    (state : CoreState) (args : List CoreValue) :
    Except TypeError CoreCallResult :=
  CheckedInput.ownCallTransaction fuel decl target state args

def checkedCoreFunction? (decl : SourceContractDecl)
    (functionName : Name) : Option CoreFunctionDef :=
  CheckedInput.ownCoreFunction? decl functionName

def checkedCoreFunction (decl : SourceContractDecl)
    (functionName : Name) : Except TypeError CoreFunctionDef :=
  CheckedInput.ownCoreFunction decl functionName

def checkedFunctionCalldata? (decl : SourceContractDecl)
    (functionName : Name) (args : List CoreValue) :
    Option (List Byte) :=
  CheckedInput.ownFunctionCalldata? decl functionName args

def checkedFunctionCalldata (decl : SourceContractDecl)
    (functionName : Name) (args : List CoreValue) :
    Except TypeError (List Byte) :=
  CheckedInput.ownFunctionCalldata decl functionName args

def checkedCallFunctionWithContext? (fuel : Nat)
    (decl : SourceContractDecl) (functionName : Name)
    (context : SolidCore.Solidity.Source.Context)
    (state : CoreState) (args : List CoreValue) :
    Option CoreCallResult :=
  CheckedInput.ownCallFunctionWithContext?
    fuel decl functionName context state args

def checkedCallFunctionWithContext (fuel : Nat)
    (decl : SourceContractDecl) (functionName : Name)
    (context : SolidCore.Solidity.Source.Context)
    (state : CoreState) (args : List CoreValue) :
    Except TypeError CoreCallResult :=
  CheckedInput.ownCallFunctionWithContext
    fuel decl functionName context state args

def checkedCallCalldataFrom? (fuel : Nat)
    (decl : SourceContractDecl) (state : CoreState)
    (sender value : Word) (calldata : List Byte) :
    Option CoreAbiCallResult :=
  CheckedInput.ownCallCalldataFrom?
    fuel decl state sender value calldata

def checkedCallCalldataFrom (fuel : Nat)
    (decl : SourceContractDecl) (state : CoreState)
    (sender value : Word) (calldata : List Byte) :
    Except TypeError CoreAbiCallResult :=
  CheckedInput.ownCallCalldataFrom
    fuel decl state sender value calldata

def checkedCallCalldataAtFrom? (fuel : Nat)
    (decl : SourceContractDecl) (state : CoreState)
    (self sender value : Word) (calldata : List Byte) :
    Option CoreAbiCallResult :=
  CheckedInput.ownCallCalldataAtFrom?
    fuel decl state self sender value calldata

def checkedCallCalldataAtFrom (fuel : Nat)
    (decl : SourceContractDecl) (state : CoreState)
    (self sender value : Word) (calldata : List Byte) :
    Except TypeError CoreAbiCallResult :=
  CheckedInput.ownCallCalldataAtFrom
    fuel decl state self sender value calldata

def checkedCallCalldataAt? (fuel : Nat)
    (decl : SourceContractDecl) (state : CoreState)
    (self : Word) (calldata : List Byte) :
    Option CoreAbiCallResult :=
  CheckedInput.ownCallCalldataAt? fuel decl state self calldata

def checkedCallCalldataAt (fuel : Nat)
    (decl : SourceContractDecl) (state : CoreState)
    (self : Word) (calldata : List Byte) :
    Except TypeError CoreAbiCallResult :=
  CheckedInput.ownCallCalldataAt fuel decl state self calldata

def checkedCallCalldata? (fuel : Nat)
    (decl : SourceContractDecl) (state : CoreState)
    (calldata : List Byte) : Option CoreAbiCallResult :=
  CheckedInput.ownCallCalldata? fuel decl state calldata

def checkedCallCalldata (fuel : Nat)
    (decl : SourceContractDecl) (state : CoreState)
    (calldata : List Byte) : Except TypeError CoreAbiCallResult :=
  CheckedInput.ownCallCalldata fuel decl state calldata

def checkedCallCalldataTransactionFrom? (fuel : Nat)
    (decl : SourceContractDecl) (state : CoreState)
    (sender value : Word) (calldata : List Byte) :
    Option CoreAbiCallResult :=
  CheckedInput.ownCallCalldataTransactionFrom?
    fuel decl state sender value calldata

def checkedCallCalldataTransactionFrom (fuel : Nat)
    (decl : SourceContractDecl) (state : CoreState)
    (sender value : Word) (calldata : List Byte) :
    Except TypeError CoreAbiCallResult :=
  CheckedInput.ownCallCalldataTransactionFrom
    fuel decl state sender value calldata

def checkedCallCalldataTransactionAtFrom? (fuel : Nat)
    (decl : SourceContractDecl) (state : CoreState)
    (self sender value : Word) (calldata : List Byte) :
    Option CoreAbiCallResult :=
  CheckedInput.ownCallCalldataTransactionAtFrom?
    fuel decl state self sender value calldata

def checkedCallCalldataTransactionAtFrom (fuel : Nat)
    (decl : SourceContractDecl) (state : CoreState)
    (self sender value : Word) (calldata : List Byte) :
    Except TypeError CoreAbiCallResult :=
  CheckedInput.ownCallCalldataTransactionAtFrom
    fuel decl state self sender value calldata

def checkedCallCalldataTransactionAt? (fuel : Nat)
    (decl : SourceContractDecl) (state : CoreState)
    (self : Word) (calldata : List Byte) :
    Option CoreAbiCallResult :=
  CheckedInput.ownCallCalldataTransactionAt?
    fuel decl state self calldata

def checkedCallCalldataTransactionAt (fuel : Nat)
    (decl : SourceContractDecl) (state : CoreState)
    (self : Word) (calldata : List Byte) :
    Except TypeError CoreAbiCallResult :=
  CheckedInput.ownCallCalldataTransactionAt
    fuel decl state self calldata

def checkedCallCalldataTransaction? (fuel : Nat)
    (decl : SourceContractDecl) (state : CoreState)
    (calldata : List Byte) : Option CoreAbiCallResult :=
  CheckedInput.ownCallCalldataTransaction? fuel decl state calldata

def checkedCallCalldataTransaction (fuel : Nat)
    (decl : SourceContractDecl) (state : CoreState)
    (calldata : List Byte) : Except TypeError CoreAbiCallResult :=
  CheckedInput.ownCallCalldataTransaction fuel decl state calldata

end ContractDecl

namespace Examples

def checkedSourceFunctionCallWithContext (fuel : Nat)
    (source : L00_SourceSolidity.SourceUnit) (contractName functionName : Name)
    (context : SolidCore.Solidity.Source.Context)
    (state : CoreState) (args : List CoreValue) :
    Except TypeError CoreCallResult :=
  SourceUnit.checkedCallFunctionWithContext
    fuel source contractName functionName context state args

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

def checkedFunctionCalldata (decl : L00_SourceSolidity.ContractDecl)
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
      (L00_SourceSolidity.Executable.SourceUnit.findContract?
        simpleSource "C")
  let rawChecked ← TypecheckedInput.checkedSourceUnit simpleSource
  let rawCheckedViaNamespace ← SourceUnit.typechecked simpleSource
  let declChecked ← TypecheckedInput.checkedSourceUnit decl
  let declCheckedViaNamespace ← ContractDecl.typechecked decl
  let declSource ← TypecheckedInput.source decl
  let defaultName ← TypecheckedInput.defaultContractName decl
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
  let abiValue ← checkedDecodeUint256 abiResult.output
  match directResult, contractResult, functionResult, declResult with
  | SolidCore.Solidity.Source.CallResult.returned _
      [SolidCore.Solidity.Source.Value.word direct],
    SolidCore.Solidity.Source.CallResult.returned _
      [SolidCore.Solidity.Source.Value.word viaContract],
    SolidCore.Solidity.Source.CallResult.returned _
      [SolidCore.Solidity.Source.Value.word viaFunction],
    SolidCore.Solidity.Source.CallResult.returned _
      [SolidCore.Solidity.Source.Value.word viaDecl] =>
      Except.ok
        (direct == 7 &&
          viaContract == 7 &&
          viaFunction == 7 &&
          viaDecl == 7 &&
          abiResult.success &&
          abiValue == 7 &&
          function.name == some "f" &&
          rawChecked.source.items.length == simpleSource.items.length &&
          rawCheckedViaNamespace.source.items.length ==
            simpleSource.items.length &&
          declChecked.source.items.length == 1 &&
          declCheckedViaNamespace.source.items.length == 1 &&
          declSource.items.length == 1 &&
          defaultName == "C")
  | _, _, _, _ => Except.ok false

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

def checkedStructFieldAssignmentMatches : Except TypeError Bool :=
  checkedCallWordMatches 48 Executable.Examples.structSourceUnit
    "StructDemo" "replaceY" SolidCore.Solidity.Source.State.empty [] 9

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
    (SolidCore.Solidity.Source.wordEq
      (state.loadSlot
        Executable.Examples.structStoragePathBlobSlot) 3 &&
      SolidCore.Solidity.Source.wordEq
        (state.loadSlot
          (Executable.Examples.structStoragePathBlobValueSlot 2)) 18)

def checkedStructStoragePathDirectBlobPushAssignMatches :
    Except TypeError Bool := do
  let state ←
    checkedStructStoragePathCallState 80 "directPathBlobPushAssign"
      [checkedStructStoragePathWord 7, checkedStructStoragePathWord 19]
  Except.ok
    (SolidCore.Solidity.Source.wordEq
      (state.loadSlot
        Executable.Examples.structStoragePathBlobSlot) 3 &&
      SolidCore.Solidity.Source.wordEq
        (state.loadSlot
          (Executable.Examples.structStoragePathBlobValueSlot 2)) 19)

def checkedStructStoragePathDirectBlobPopMatches :
    Except TypeError Bool := do
  let state ←
    checkedStructStoragePathCallState 80 "directPathBlobPop"
      [checkedStructStoragePathWord 7]
  Except.ok
    (SolidCore.Solidity.Source.wordEq
      (state.loadSlot
        Executable.Examples.structStoragePathBlobSlot) 1 &&
      SolidCore.Solidity.Source.wordEq
        (state.loadSlot
          (Executable.Examples.structStoragePathBlobValueSlot 1)) 0)

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
    (SolidCore.Solidity.Source.wordEq
      (state.loadSlot
        Executable.Examples.structStoragePathBlobSlot) 3 &&
      SolidCore.Solidity.Source.wordEq
        (state.loadSlot
          (Executable.Examples.structStoragePathBlobValueSlot 2)) 5)

def checkedStructStoragePathAliasBlobPushAssignMatches :
    Except TypeError Bool := do
  let state ←
    checkedStructStoragePathCallState 80 "aliasBlobPushAssign"
      [checkedStructStoragePathWord 7, checkedStructStoragePathWord 20]
  Except.ok
    (SolidCore.Solidity.Source.wordEq
      (state.loadSlot
        Executable.Examples.structStoragePathBlobSlot) 3 &&
      SolidCore.Solidity.Source.wordEq
        (state.loadSlot
          (Executable.Examples.structStoragePathBlobValueSlot 2)) 20)

def checkedStructStoragePathAliasBlobPopMatches :
    Except TypeError Bool := do
  let state ←
    checkedStructStoragePathCallState 80 "aliasBlobPop"
      [checkedStructStoragePathWord 7]
  Except.ok
    (SolidCore.Solidity.Source.wordEq
      (state.loadSlot
        Executable.Examples.structStoragePathBlobSlot) 1 &&
      SolidCore.Solidity.Source.wordEq
        (state.loadSlot
          (Executable.Examples.structStoragePathBlobValueSlot 1)) 0)

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
    (SolidCore.Solidity.Source.wordEq
      (state.loadSlot
        Executable.Examples.structStoragePathBlobSlot) 3 &&
      SolidCore.Solidity.Source.wordEq
        (state.loadSlot
          (Executable.Examples.structStoragePathBlobValueSlot 2)) 13)

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
    (SolidCore.Solidity.Source.wordEq
      (state.loadSlot
        Executable.Examples.structStoragePathBlobSlot) 3 &&
      SolidCore.Solidity.Source.wordEq
        (state.loadSlot
          (Executable.Examples.structStoragePathBlobValueSlot 2)) 15)

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
  Except.ok
    (read &&
      SolidCore.Solidity.Source.wordEq (state.loadSlot 0) 1 &&
      SolidCore.Solidity.Source.wordEq
        (state.loadSlot checkedNestedBytesStoragePathElementSlot) 2 &&
      SolidCore.Solidity.Source.wordEq
        (state.loadSlot
          (SolidCore.Solidity.Source.dynamicArrayStorageSlot
            checkedNestedBytesStoragePathElementSlot 1)) 90)

def checkedNestedBytesStoragePathClearMatches :
    Except TypeError Bool := do
  let state ←
    checkedOwnCallState 64
      Executable.Examples.nestedBytesStoragePathContract
      "clearByte"
      Executable.Examples.nestedBytesStoragePathInitialState
      [ checkedNestedStoragePathWord 0
      , checkedNestedStoragePathWord 1 ]
  Except.ok
    (SolidCore.Solidity.Source.wordEq (state.loadSlot 0) 1 &&
      SolidCore.Solidity.Source.wordEq
        (state.loadSlot checkedNestedBytesStoragePathElementSlot) 2 &&
      SolidCore.Solidity.Source.wordEq
        (state.loadSlot
          (SolidCore.Solidity.Source.dynamicArrayStorageSlot
            checkedNestedBytesStoragePathElementSlot 0)) 10 &&
      SolidCore.Solidity.Source.wordEq
        (state.loadSlot
          (SolidCore.Solidity.Source.dynamicArrayStorageSlot
            checkedNestedBytesStoragePathElementSlot 1)) 0)

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
        Executable.Examples.namedReturnContract)

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
  let runDefault ←
    CheckedInput.ownCall 32
      Executable.Examples.namedReturnContract
      (SolidCore.Solidity.Source.CallTarget.name "runDefault")
      SolidCore.Solidity.Source.State.empty []
  match stop, runFallthrough, runDefault with
  | SolidCore.Solidity.Source.CallResult.returned stopState [],
    SolidCore.Solidity.Source.CallResult.returned _
      [SolidCore.Solidity.Source.Value.word runFallthroughValue],
    SolidCore.Solidity.Source.CallResult.returned _
      [SolidCore.Solidity.Source.Value.word runDefaultValue] =>
      Except.ok
        (SolidCore.Solidity.Source.wordEq
          (stopState.loadSlot 0) 1 &&
          SolidCore.Solidity.Source.wordEq runFallthroughValue 9 &&
          SolidCore.Solidity.Source.wordEq runDefaultValue 0)
  | _, _, _ => Except.ok false

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
      (SharedSemantics.notWord 0) 11
  let runNeg ←
    checkedOwnCallIntAndSlotMatches 64
      Executable.Examples.internalUnaryLocalCallContract
      "runNeg" SolidCore.Solidity.Source.State.empty []
      (SharedSemantics.signedToWord 5) 13
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
        Executable.Examples.namedErrorArgumentOrderContract)

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
        Executable.Examples.storageDeleteCheckedContract) &&
    Result.isOk
      (TypecheckedInput.checkedSourceUnit
        Executable.Examples.storageArrayCopyContract)

def checkedStorageDeleteWholeMappingRejected : Bool :=
  Result.isError
    (TypecheckedInput.checkedSourceUnit
      Executable.Examples.storageDeleteContract)

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
    Executable.Examples.storageDeleteCheckedContract
    "set" SolidCore.Solidity.Source.State.empty []

def checkedStorageDeleteDynamicState :
    Except TypeError CoreState := do
  let state ← checkedStorageDeleteWrittenState
  checkedOwnCallState 24
    Executable.Examples.storageDeleteCheckedContract
    "deleteDynamic" state []

def checkedStorageDeleteDynamicLengthZero :
    Except TypeError Bool := do
  let state ← checkedStorageDeleteDynamicState
  checkedOwnCallWordMatches 16
    Executable.Examples.storageDeleteCheckedContract
    "length" state [] 0

def checkedStorageDeleteDynamicIndexReverts :
    Except TypeError Bool := do
  let state ← checkedStorageDeleteDynamicState
  checkedOwnCallPanicMatches 16
    Executable.Examples.storageDeleteCheckedContract
    "readItem" state [] 0x32

def checkedStorageDeleteFixedState :
    Except TypeError CoreState := do
  let state ← checkedStorageDeleteWrittenState
  checkedOwnCallState 24
    Executable.Examples.storageDeleteCheckedContract
    "deleteFixed" state []

def checkedStorageDeleteFixedClearsElement :
    Except TypeError Bool := do
  let state ← checkedStorageDeleteFixedState
  checkedOwnCallWordMatches 16
    Executable.Examples.storageDeleteCheckedContract
    "readFixed" state [] 0

def checkedStorageDeleteMappingKeyState :
    Except TypeError CoreState := do
  let state ← checkedStorageDeleteWrittenState
  checkedOwnCallState 24
    Executable.Examples.storageDeleteCheckedContract
    "deleteMappingKey" state []

def checkedStorageDeleteMappingKeyClearsEntry :
    Except TypeError Bool := do
  let state ← checkedStorageDeleteMappingKeyState
  checkedOwnCallWordMatches 16
    Executable.Examples.storageDeleteCheckedContract
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

def checkedInheritedNestedTypeShadowsUnrelatedLowering :
    Except TypeError Bool := do
  let contract ←
    CheckedInput.toCoreContract
      Executable.Examples.inheritedNestedTypeUnit
      "NestedTypeDerived"
  optionToExcept "inherited nested type lowering"
    (Executable.Examples.inheritedNestedTypeFunctionReturnsFirstField?
      "readInheritedX" contract)

def checkedQualifiedInheritedNestedTypeLowering :
    Except TypeError Bool := do
  let contract ←
    CheckedInput.toCoreContract
      Executable.Examples.inheritedNestedTypeUnit
      "NestedTypeDerived"
  optionToExcept "qualified inherited nested type lowering"
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

def checkedMemoryStringAllocationMatches :
    Except TypeError Bool :=
  checkedOwnCallBytesMatches 16
    Executable.Examples.checkedMemoryAndCalldataContract
    "allocateString" SolidCore.Solidity.Source.State.empty
    [SolidCore.Solidity.Source.Value.word 3]
    [0, 0, 0]

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

def checkedExternalFunctionAbiCleanDecodeMatches : Bool :=
  match Executable.Examples.externalFunctionAbiCleanDecodeMatches with
  | some true => true
  | _ => false

def checkedExternalFunctionAbiRejectsDirtyPadding : Bool :=
  Executable.Examples.externalFunctionAbiRejectsDirtyPadding

def checkedExternalFunctionPointerCallMatches :
    Except TypeError Bool := do
  let context ←
    optionToExcept "external function pointer call context"
      Executable.Examples.externalFunctionPointerCallContext
  let result ←
    ContractDecl.checkedCallFunctionWithContext 16
      Executable.Examples.checkedExternalFunctionPointerContract
      "callGetter" context SolidCore.Solidity.Source.State.empty
      [SolidCore.Solidity.Source.Value.externalFunction
        0xbeef Executable.Examples.externalFunctionPointerGetterSelector]
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _
      [SolidCore.Solidity.Source.Value.word value] =>
      Except.ok (SolidCore.Solidity.Source.wordEq value 99)
  | _ => Except.ok false

def checkedExternalFunctionPointerPayableCallMatches :
    Except TypeError Bool := do
  let context ←
    optionToExcept "external function pointer payable call context"
      Executable.Examples.externalFunctionPointerPayableCallContext
  let context := { context with accountCodes := [(0xbeef, [1])] }
  let result ←
    ContractDecl.checkedCallFunctionWithContext 16
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
      accountCodes := [(0xbeef, [1])]
      lowLevelCallResults :=
        [ { kind := SolidCore.Solidity.Source.LowLevelCallKind.call
            target := 0xbeef
            calldata :=
              SolidCore.Solidity.Source.wordToBytesBE
                SolidCore.Solidity.Source.selectorBytes
                Executable.Examples.selectorEncodingSelector ++ encodedArgs
            gas? := some 777
            success := true
            output := [] } ] }
  let result ←
    ContractDecl.checkedCallFunctionWithContext 16
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
  let context ←
    optionToExcept "external function pointer try/catch context"
      Executable.Examples.externalFunctionPointerTryCatchSuccessContext
  let result ←
    ContractDecl.checkedCallFunctionWithContext 16
      Executable.Examples.checkedExternalFunctionPointerContract
      "tryGetter" context SolidCore.Solidity.Source.State.empty
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
    (args : List CoreValue) : Except TypeError CoreCallResult := do
  let contract ←
    CheckedInput.contract
      Executable.Examples.checkedHighLevelExternalSource
      "CheckedHighLevelCaller"
  CheckedContract.callFunctionWithContext 32 contract functionName
    context SolidCore.Solidity.Source.State.empty args

def checkedHighLevelExternalContext
    (results : List SolidCore.Solidity.Source.LowLevelCallResult)
    (accountCodes : List (Word × List Byte) := []) :
    Except TypeError CoreContext := do
  let contract ←
    CheckedInput.contract
      Executable.Examples.checkedHighLevelExternalSource
      "CheckedHighLevelCaller"
  Except.ok
    { contract.core.context with
      accountCodes := accountCodes
      lowLevelCallResults := results }

def checkedHighLevelExternalWordCallMatches
    (functionName : Name) (context : CoreContext)
    (args : List CoreValue) (expected : Word) :
    Except TypeError Bool := do
  let result ←
    checkedHighLevelExternalCall functionName context args
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
  let context ← checkedHighLevelExternalContext [result]
  checkedHighLevelExternalWordCallMatches "read" context
    [SolidCore.Solidity.Source.Value.word 0xbeef] 77

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
  let context ← checkedHighLevelExternalContext [result]
  checkedHighLevelExternalWordCallMatches "readNamed" context
    [ SolidCore.Solidity.Source.Value.word 0xbeef
    , SolidCore.Solidity.Source.Value.word 40
    , SolidCore.Solidity.Source.Value.word 2 ] 42

def checkedHighLevelExternalVarDeclMatches :
    Except TypeError Bool := do
  let output ← checkedHighLevelExternalWordOutput 40
  let result ←
    checkedHighLevelExternalResult
      SolidCore.Solidity.Source.LowLevelCallKind.call
      "get()" [] [] output
  let context ← checkedHighLevelExternalContext [result]
  checkedHighLevelExternalWordCallMatches "readViaLocal" context
    [SolidCore.Solidity.Source.Value.word 0xbeef] 41

def checkedHighLevelExternalMultiVarDeclMatches :
    Except TypeError Bool := do
  let output ← checkedHighLevelExternalWordPairOutput 20 22
  let result ←
    checkedHighLevelExternalResult
      SolidCore.Solidity.Source.LowLevelCallKind.call
      "pair()" [] [] output
  let context ← checkedHighLevelExternalContext [result]
  checkedHighLevelExternalWordCallMatches "readPairViaLocals" context
    [SolidCore.Solidity.Source.Value.word 0xbeef] 42

def checkedHighLevelExternalPayableValueMatches :
    Except TypeError Bool := do
  let output ← checkedHighLevelExternalWordOutput 22
  let result ←
    checkedHighLevelExternalResult
      SolidCore.Solidity.Source.LowLevelCallKind.call
      "payQuote()" [] [] output 9 (some 1234)
  let context ← checkedHighLevelExternalContext [result]
  checkedHighLevelExternalWordCallMatches "payKnown" context
    [ SolidCore.Solidity.Source.Value.word 0xbeef
    , SolidCore.Solidity.Source.Value.word 9 ] 22

def checkedHighLevelExternalNonpayableGasMatches :
    Except TypeError Bool := do
  let output ← checkedHighLevelExternalWordOutput 33
  let result ←
    checkedHighLevelExternalResult
      SolidCore.Solidity.Source.LowLevelCallKind.call
      "plainQuote()" [] [] output 0 (some 5678)
  let context ← checkedHighLevelExternalContext [result]
  checkedHighLevelExternalWordCallMatches "nonpayableGas" context
    [SolidCore.Solidity.Source.Value.word 0xbeef] 33

def checkedHighLevelExternalAssignMatches :
    Except TypeError Bool := do
  let output ← checkedHighLevelExternalWordOutput 12
  let result ←
    checkedHighLevelExternalResult
      SolidCore.Solidity.Source.LowLevelCallKind.call
      "get()" [] [] output
  let context ← checkedHighLevelExternalContext [result]
  let callResult ←
    checkedHighLevelExternalCall "assignFromExternal" context
      [SolidCore.Solidity.Source.Value.word 0xbeef]
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
  let context ← checkedHighLevelExternalContext [result] [(0xbeef, [1])]
  let callResult ←
    checkedHighLevelExternalCall "notifyExternal" context
      [SolidCore.Solidity.Source.Value.word 0xbeef]
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
  let context ← checkedHighLevelExternalContext [result]
  checkedHighLevelExternalWordCallMatches "notifyOrCatch" context
    [SolidCore.Solidity.Source.Value.word 0xbeef] 2

def checkedHighLevelExternalNoReturnCodePresentSucceeds :
    Except TypeError Bool := do
  let result ←
    checkedHighLevelExternalResult
      SolidCore.Solidity.Source.LowLevelCallKind.call
      "notify()" [] [] []
  let context ← checkedHighLevelExternalContext [result] [(0xbeef, [1])]
  checkedHighLevelExternalWordCallMatches "notifyOrCatch" context
    [SolidCore.Solidity.Source.Value.word 0xbeef] 1

def checkedHighLevelExternalReturnNoCodeUsesReturndata :
    Except TypeError Bool := do
  let output ← checkedHighLevelExternalWordOutput 5
  let result ←
    checkedHighLevelExternalResult
      SolidCore.Solidity.Source.LowLevelCallKind.call
      "get()" [] [] output
  let context ← checkedHighLevelExternalContext [result]
  checkedHighLevelExternalWordCallMatches "readNoCodeReturn" context
    [SolidCore.Solidity.Source.Value.word 0xbeef] 5

def checkedHighLevelExternalFailureBubblesRaw :
    Except TypeError Bool := do
  let result ←
    checkedHighLevelExternalResult
      SolidCore.Solidity.Source.LowLevelCallKind.call
      "get()" [] [] [0xdd, 0xee] 0 none false
  let context ← checkedHighLevelExternalContext [result]
  let callResult ←
    checkedHighLevelExternalCall "read" context
      [SolidCore.Solidity.Source.Value.word 0xbeef]
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
  let context ← checkedHighLevelExternalContext [result]
  checkedHighLevelExternalWordCallMatches "readView" context
    [SolidCore.Solidity.Source.Value.word 0xbeef] 77

def checkedHighLevelExternalPureGasStaticcallMatches :
    Except TypeError Bool := do
  let output ← checkedHighLevelExternalWordOutput 88
  let result ←
    checkedHighLevelExternalResult
      SolidCore.Solidity.Source.LowLevelCallKind.staticcall
      "pureGet()" [] [] output 0 (some 4321)
  let context ← checkedHighLevelExternalContext [result]
  checkedHighLevelExternalWordCallMatches "readPureWithGas" context
    [SolidCore.Solidity.Source.Value.word 0xbeef] 88

def checkedHighLevelExternalGetterStaticcallMatches :
    Except TypeError Bool := do
  let output ← checkedHighLevelExternalWordOutput 99
  let result ←
    checkedHighLevelExternalResult
      SolidCore.Solidity.Source.LowLevelCallKind.staticcall
      "x()" [] [] output
  let context ← checkedHighLevelExternalContext [result]
  checkedHighLevelExternalWordCallMatches "readGetter" context
    [SolidCore.Solidity.Source.Value.word 0xbeef] 99

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
    CheckedContract.callFunctionWithContext 16 contract functionName
      { contract.core.context with
        self := 0xcafe
        lowLevelCallResults :=
          [ { kind := SolidCore.Solidity.Source.LowLevelCallKind.staticcall
              target := 0xcafe
              calldata := calldata
              success := true
              output := output } ] }
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
    (expectedA expectedB : Word) : Except TypeError Bool := do
  let result ←
    ContractDecl.checkedCallFunctionWithContext
      fuel decl functionName context state args
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

def checkedEnvironmentRandaoAliasMatches :
    Except TypeError Bool :=
  checkedCallFunctionWithContextWordPairMatches 16
    Executable.Examples.checkedEnvironmentContract
    "randaoAlias"
    Executable.Examples.environmentRandaoAliasContext
    SolidCore.Solidity.Source.State.empty [] 0x2222 0x2222

def checkedEnvironmentHashMatches : Except TypeError Bool :=
  checkedCallFunctionWithContextWordTripleMatches 16
    Executable.Examples.checkedEnvironmentContract
    "hashes"
    Executable.Examples.environmentHashContext
    SolidCore.Solidity.Source.State.empty [] 0x1234 0x5678 0

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

def checkedModularArithmeticInvalidSourcesRejected : Bool :=
  Result.isError
      (TypecheckedInput.checkedSourceUnit addmodZeroLiteralSource) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit mulmodZeroLiteralSource) &&
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
    Executable.Examples.externalCryptoHashContext
    SolidCore.Solidity.Source.State.empty [] 0xaaaa 0xbbbb

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
    Executable.Examples.ecrecoverBuiltinContext
    SolidCore.Solidity.Source.State.empty [] 0xcafe 0

def checkedPrecompileBuiltinsStaticcallSharedResultsMatches :
    Except TypeError Bool := do
  let result ←
    ContractDecl.checkedCallFunctionWithContext 16
      Executable.Examples.checkedHashBuiltinContract
      "precompileBuiltinsAndCalls"
      Executable.Examples.precompileBuiltinsStaticcallSharedResultsContext
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
            (SharedSemantics.wordModulus - 1))
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
            SharedSemantics.halfWordModulus &&
          SolidCore.Solidity.Source.wordEq max256
            (SharedSemantics.halfWordModulus - 1))
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

def checkedSelfdestructRecordsAndStopsMatches :
    Except TypeError Bool := do
  let contract ←
    ContractDecl.checkedContract
      Executable.Examples.checkedAddressEnvironmentContract
  let result ←
    CheckedContract.callFunctionWithContext 16 contract "destroy"
      { contract.core.context with self := 0xcafe }
      SolidCore.Solidity.Source.State.empty
      [SolidCore.Solidity.Source.Value.word 0xbeef]
  match result with
  | SolidCore.Solidity.Source.CallResult.returned state [] =>
      match state.selfdestructs with
      | [(fromAddress, recipient)] =>
          Except.ok
            (SolidCore.Solidity.Source.wordEq fromAddress 0xcafe &&
              SolidCore.Solidity.Source.wordEq recipient 0xbeef &&
              SolidCore.Solidity.Source.wordEq (state.loadSlot 0) 0)
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
        (SharedSemantics.signedValue negativeSmall = -5 &&
          SharedSemantics.signedValue negativeMin = -128 &&
          SolidCore.Solidity.Source.wordEq positiveMax 255 &&
          SharedSemantics.signedValue foldedInt = 4)
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
        (SharedSemantics.signedValue negative = -5 &&
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
          (SharedSemantics.signedToWord (-3)) ]
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
          SharedSemantics.signedValue signedLow = -1 &&
          SolidCore.Solidity.Source.wordEq signedAsUint
            (SharedSemantics.signedToWord (-3)) &&
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

def checkedLiteralInvalidSourcesRejected : Bool :=
  Result.isError
      (TypecheckedInput.checkedSourceUnit memoryBytesSliceSource) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit calldataSliceSignedIndexSource) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit calldataSliceMemberSource) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit fractionalWeiReturnSource) &&
    Result.isError
      (TypecheckedInput.checkedSourceUnit subWeiEtherReturnSource)

def checkedArithmeticContractAccepted : Bool :=
  Result.isOk
    (TypecheckedInput.checkedSourceUnit
      Executable.Examples.checkedArithmeticContract)

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
          (SharedSemantics.signedToWord (-5))
      , SolidCore.Solidity.Source.Value.int 2 ]
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _
      [ SolidCore.Solidity.Source.Value.int quotient
      , SolidCore.Solidity.Source.Value.int remainder
      , SolidCore.Solidity.Source.Value.word less ] =>
      Except.ok
        (SolidCore.Solidity.Source.wordEq quotient
            (SharedSemantics.signedToWord (-2)) &&
          SolidCore.Solidity.Source.wordEq remainder
            (SharedSemantics.signedToWord (-1)) &&
          SolidCore.Solidity.Source.wordEq less 1)
  | _ => Except.ok false

def checkedSignedIntAbiOutputMatchesExpected : Except TypeError Bool :=
  checkedContractAbiOutputMatches 24
    Executable.Examples.checkedArithmeticContract
    "signedOps"
    [ SolidCore.Solidity.Source.Value.int
        (SharedSemantics.signedToWord (-5))
    , SolidCore.Solidity.Source.Value.int 2 ]
    Executable.Examples.signedIntAbiExpectedOutput

def checkedSignedSarMatches : Except TypeError Bool :=
  checkedOwnCallIntMatches 16
    Executable.Examples.checkedArithmeticContract
    "signedSar" SolidCore.Solidity.Source.State.empty
    [ SolidCore.Solidity.Source.Value.int
        (SharedSemantics.signedToWord (-5))
    , SolidCore.Solidity.Source.Value.word 1 ]
    (SharedSemantics.signedToWord (-3))

def checkedSignedSarAssignMatches : Except TypeError Bool :=
  checkedOwnCallIntMatches 16
    Executable.Examples.checkedArithmeticContract
    "signedSarAssign" SolidCore.Solidity.Source.State.empty
    [ SolidCore.Solidity.Source.Value.int
        (SharedSemantics.signedToWord (-5))
    , SolidCore.Solidity.Source.Value.word 1 ]
    (SharedSemantics.signedToWord (-3))

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
        (SharedSemantics.signedToWord (-1)) ] 0x11

def checkedUncheckedSignedDivisionOverflowWraps :
    Except TypeError Bool :=
  checkedOwnCallIntMatches 16
    Executable.Examples.checkedArithmeticContract
    "uncheckedSignedDivide" SolidCore.Solidity.Source.State.empty
    [ SolidCore.Solidity.Source.Value.int (2 ^ 255)
    , SolidCore.Solidity.Source.Value.int
        (SharedSemantics.signedToWord (-1)) ] (2 ^ 255)

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
    "assignmentReturn" SolidCore.Solidity.Source.State.empty [] 9 9

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

def checkedUsingMathLibrary : L00_SourceSolidity.ContractDecl :=
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
                (L00_SourceSolidity.Stmt.returnValues
                  (some
                    (L00_SourceSolidity.Expr.binary BinaryOp.add
                      (L00_SourceSolidity.Expr.ident "self")
                      (L00_SourceSolidity.Expr.literal
                        (L00_SourceSolidity.Literal.number "1"))))) }
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
                (L00_SourceSolidity.Stmt.returnValues
                  (some
                    (L00_SourceSolidity.Expr.binary BinaryOp.add
                      (L00_SourceSolidity.Expr.binary BinaryOp.mul
                        (L00_SourceSolidity.Expr.ident "self")
                        (L00_SourceSolidity.Expr.literal
                          (L00_SourceSolidity.Literal.number "10")))
                      (L00_SourceSolidity.Expr.ident "right")))) } ] }

def checkedUsingFreeIncFunction : L00_SourceSolidity.FunctionDecl :=
  { name := some "checkedFreeInc"
    params := [{ name := some "self", ty := Ty.uint 256 }]
    returns := [{ name := some "out", ty := Ty.uint 256 }]
    mutability := StateMutability.pure
    body :=
      some
        (L00_SourceSolidity.Stmt.returnValues
          (some
            (L00_SourceSolidity.Expr.binary BinaryOp.add
              (L00_SourceSolidity.Expr.ident "self")
              (L00_SourceSolidity.Expr.literal
                (L00_SourceSolidity.Literal.number "1"))))) }

def checkedUsingMethodContract : L00_SourceSolidity.ContractDecl :=
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
                (L00_SourceSolidity.Stmt.returnValues
                  (some
                    (L00_SourceSolidity.Expr.call
                      (L00_SourceSolidity.Expr.member
                        (L00_SourceSolidity.Expr.ident "x") "inc")
                      []))) } ] }

def checkedUsingDirectContract : L00_SourceSolidity.ContractDecl :=
  { name := "CheckedUsingDirect"
    items :=
      [ ContractItem.function
          { name := some "run"
            visibility := some Visibility.public_
            params := [{ name := some "x", ty := Ty.uint 256 }]
            returns := [{ name := some "out", ty := Ty.uint 256 }]
            body :=
              some
                (L00_SourceSolidity.Stmt.returnValues
                  (some
                    (L00_SourceSolidity.Expr.call
                      (L00_SourceSolidity.Expr.member
                        (L00_SourceSolidity.Expr.ident "CheckedMath")
                        "inc")
                      [L00_SourceSolidity.Arg.positional
                        (L00_SourceSolidity.Expr.ident "x")]))) } ] }

def checkedUsingSourceLevelContract :
    L00_SourceSolidity.ContractDecl :=
  { name := "CheckedUsingSourceLevel"
    items :=
      [ ContractItem.function
          { name := some "run"
            visibility := some Visibility.public_
            params := [{ name := some "x", ty := Ty.uint 256 }]
            returns := [{ name := some "out", ty := Ty.uint 256 }]
            body :=
              some
                (L00_SourceSolidity.Stmt.returnValues
                  (some
                    (L00_SourceSolidity.Expr.call
                      (L00_SourceSolidity.Expr.member
                        (L00_SourceSolidity.Expr.ident "x") "inc")
                      []))) } ] }

def checkedUsingStorageContract : L00_SourceSolidity.ContractDecl :=
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
                (L00_SourceSolidity.Stmt.expr
                  (L00_SourceSolidity.Expr.assign
                    (L00_SourceSolidity.Expr.ident "x")
                    AssignOp.assign
                    (L00_SourceSolidity.Expr.call
                      (L00_SourceSolidity.Expr.member
                        (L00_SourceSolidity.Expr.ident "x") "inc")
                      []))) } ] }

def checkedUsingNamedMethodContract :
    L00_SourceSolidity.ContractDecl :=
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
                (L00_SourceSolidity.Stmt.returnValues
                  (some
                    (L00_SourceSolidity.Expr.call
                      (L00_SourceSolidity.Expr.member
                        (L00_SourceSolidity.Expr.ident "x") "mix")
                      [L00_SourceSolidity.Arg.named "right"
                        (L00_SourceSolidity.Expr.literal
                          (L00_SourceSolidity.Literal.number "2"))]))) } ] }

def checkedUsingExplicitFunctionContract :
    L00_SourceSolidity.ContractDecl :=
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
                (L00_SourceSolidity.Stmt.returnValues
                  (some
                    (L00_SourceSolidity.Expr.call
                      (L00_SourceSolidity.Expr.member
                        (L00_SourceSolidity.Expr.ident "x") "mix")
                      [L00_SourceSolidity.Arg.positional
                        (L00_SourceSolidity.Expr.literal
                          (L00_SourceSolidity.Literal.number "2"))]))) } ] }

def checkedUsingExplicitFreeFunctionContract :
    L00_SourceSolidity.ContractDecl :=
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
                (L00_SourceSolidity.Stmt.returnValues
                  (some
                    (L00_SourceSolidity.Expr.call
                      (L00_SourceSolidity.Expr.member
                        (L00_SourceSolidity.Expr.ident "x")
                        "checkedFreeInc")
                      []))) } ] }

def checkedUsingNamedDirectContract :
    L00_SourceSolidity.ContractDecl :=
  { name := "CheckedUsingNamedDirect"
    items :=
      [ ContractItem.function
          { name := some "run"
            visibility := some Visibility.public_
            returns := [{ name := some "out", ty := Ty.uint 256 }]
            body :=
              some
                (L00_SourceSolidity.Stmt.returnValues
                  (some
                    (L00_SourceSolidity.Expr.call
                      (L00_SourceSolidity.Expr.member
                        (L00_SourceSolidity.Expr.ident "CheckedMath")
                        "mix")
                      [ L00_SourceSolidity.Arg.named "right"
                          (L00_SourceSolidity.Expr.literal
                            (L00_SourceSolidity.Literal.number "2"))
                      , L00_SourceSolidity.Arg.named "self"
                          (L00_SourceSolidity.Expr.literal
                            (L00_SourceSolidity.Literal.number "4")) ]))) } ] }

def checkedUsingLibraryUnit : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract checkedUsingMathLibrary
      , L00_SourceSolidity.SourceItem.freeFunction
          checkedUsingFreeIncFunction
      , L00_SourceSolidity.SourceItem.contract
          checkedUsingMethodContract
      , L00_SourceSolidity.SourceItem.contract
          checkedUsingDirectContract
      , L00_SourceSolidity.SourceItem.contract
          checkedUsingStorageContract
      , L00_SourceSolidity.SourceItem.contract
          checkedUsingNamedMethodContract
      , L00_SourceSolidity.SourceItem.contract
          checkedUsingExplicitFunctionContract
      , L00_SourceSolidity.SourceItem.contract
          checkedUsingExplicitFreeFunctionContract
      , L00_SourceSolidity.SourceItem.contract
          checkedUsingNamedDirectContract ] }

def checkedUsingSourceLevelUnit : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract checkedUsingMathLibrary
      , L00_SourceSolidity.SourceItem.usingDecl
          { library := { segments := ["CheckedMath"] }
            target := some (Ty.uint 256) }
      , L00_SourceSolidity.SourceItem.contract
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
    CheckedInput.callFunctionWithContext 64
      Executable.Examples.externalLibraryUnit contractName "run"
      { contract.core.context with
        contractAddresses := [("ExternalMath", 0xbeef)]
        lowLevelCallResults := [callResult] }
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
    L00_SourceSolidity.ContractDecl :=
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
                (L00_SourceSolidity.Stmt.block
                  [ L00_SourceSolidity.Stmt.varDecl
                      [{ name := some "a", ty := some priceTy }]
                      (some
                        (L00_SourceSolidity.Expr.call
                          (L00_SourceSolidity.Expr.member
                            (L00_SourceSolidity.Expr.typeName priceTy)
                            "wrap")
                          [L00_SourceSolidity.Arg.positional
                            (L00_SourceSolidity.Expr.ident "left")]))
                  , L00_SourceSolidity.Stmt.varDecl
                      [{ name := some "b", ty := some priceTy }]
                      (some
                        (L00_SourceSolidity.Expr.call
                          (L00_SourceSolidity.Expr.member
                            (L00_SourceSolidity.Expr.typeName priceTy)
                            "wrap")
                          [L00_SourceSolidity.Arg.positional
                            (L00_SourceSolidity.Expr.ident "right")]))
                  , L00_SourceSolidity.Stmt.returnValues
                      (some
                        (L00_SourceSolidity.Expr.call
                          (L00_SourceSolidity.Expr.member
                            (L00_SourceSolidity.Expr.typeName priceTy)
                            "unwrap")
                          [ L00_SourceSolidity.Arg.positional
                              (L00_SourceSolidity.Expr.binary BinaryOp.add
                                (L00_SourceSolidity.Expr.ident "a")
                                (L00_SourceSolidity.Expr.ident "b")) ])) ]) }
      , ContractItem.function
          { name := some "less"
            visibility := some Visibility.public_
            params :=
              [ { name := some "left", ty := Ty.uint 256 }
              , { name := some "right", ty := Ty.uint 256 } ]
            returns := [{ name := some "out", ty := Ty.bool }]
            body :=
              some
                (L00_SourceSolidity.Stmt.block
                  [ L00_SourceSolidity.Stmt.varDecl
                      [{ name := some "a", ty := some priceTy }]
                      (some
                        (L00_SourceSolidity.Expr.call
                          (L00_SourceSolidity.Expr.member
                            (L00_SourceSolidity.Expr.typeName priceTy)
                            "wrap")
                          [L00_SourceSolidity.Arg.positional
                            (L00_SourceSolidity.Expr.ident "left")]))
                  , L00_SourceSolidity.Stmt.varDecl
                      [{ name := some "b", ty := some priceTy }]
                      (some
                        (L00_SourceSolidity.Expr.call
                          (L00_SourceSolidity.Expr.member
                            (L00_SourceSolidity.Expr.typeName priceTy)
                            "wrap")
                          [L00_SourceSolidity.Arg.positional
                            (L00_SourceSolidity.Expr.ident "right")]))
                  , L00_SourceSolidity.Stmt.returnValues
                      (some
                        (L00_SourceSolidity.Expr.binary BinaryOp.lt
                          (L00_SourceSolidity.Expr.ident "a")
                          (L00_SourceSolidity.Expr.ident "b"))) ]) }
      , ContractItem.function
          { name := some "unary"
            visibility := some Visibility.public_
            params := [{ name := some "raw", ty := Ty.uint 256 }]
            returns :=
              [ { name := some "negated", ty := Ty.uint 256 }
              , { name := some "inverted", ty := Ty.uint 256 } ]
            body :=
              some
                (L00_SourceSolidity.Stmt.block
                  [ L00_SourceSolidity.Stmt.varDecl
                      [{ name := some "a", ty := some priceTy }]
                      (some
                        (L00_SourceSolidity.Expr.call
                          (L00_SourceSolidity.Expr.member
                            (L00_SourceSolidity.Expr.typeName priceTy)
                            "wrap")
                          [L00_SourceSolidity.Arg.positional
                            (L00_SourceSolidity.Expr.ident "raw")]))
                  , L00_SourceSolidity.Stmt.varDecl
                      [{ name := some "negated", ty := some priceTy }]
                      (some
                        (L00_SourceSolidity.Expr.unary UnaryOp.neg
                          (L00_SourceSolidity.Expr.ident "a")))
                  , L00_SourceSolidity.Stmt.varDecl
                      [{ name := some "inverted", ty := some priceTy }]
                      (some
                        (L00_SourceSolidity.Expr.unary UnaryOp.bitNot
                          (L00_SourceSolidity.Expr.ident "a")))
                  , L00_SourceSolidity.Stmt.returnValues
                      (some
                        (L00_SourceSolidity.Expr.tuple
                          [ L00_SourceSolidity.TupleItem.value
                              (L00_SourceSolidity.Expr.call
                                (L00_SourceSolidity.Expr.member
                                  (L00_SourceSolidity.Expr.typeName priceTy)
                                  "unwrap")
                                [L00_SourceSolidity.Arg.positional
                                  (L00_SourceSolidity.Expr.ident
                                    "negated")])
                          , L00_SourceSolidity.TupleItem.value
                              (L00_SourceSolidity.Expr.call
                                (L00_SourceSolidity.Expr.member
                                  (L00_SourceSolidity.Expr.typeName priceTy)
                                  "unwrap")
                                [L00_SourceSolidity.Arg.positional
                                  (L00_SourceSolidity.Expr.ident
                                    "inverted")]) ])) ]) } ] }

def checkedGlobalUsingPriceOperatorUnit :
    L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.freeUserValueType priceDecl
      , L00_SourceSolidity.SourceItem.freeFunction
          priceOperatorAddFunction
      , L00_SourceSolidity.SourceItem.freeFunction
          priceOperatorLtFunction
      , L00_SourceSolidity.SourceItem.freeFunction
          priceOperatorNegFunction
      , L00_SourceSolidity.SourceItem.freeFunction
          priceOperatorBitNotFunction
      , L00_SourceSolidity.SourceItem.usingDecl
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
      , L00_SourceSolidity.SourceItem.contract
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
    L00_SourceSolidity.ContractDecl :=
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
                (L00_SourceSolidity.Stmt.returnValues
                  (some
                    (L00_SourceSolidity.Expr.binary BinaryOp.add
                      (L00_SourceSolidity.Expr.ident "self")
                      (L00_SourceSolidity.Expr.literal
                        (L00_SourceSolidity.Literal.number "1"))))) } ] }

def checkedExternalLibraryDirectContract :
    L00_SourceSolidity.ContractDecl :=
  { name := "CheckedExternalLibraryDirect"
    items :=
      [ ContractItem.function
          { name := some "run"
            visibility := some Visibility.public_
            params := [{ name := some "x", ty := Ty.uint 256 }]
            returns := [{ name := some "out", ty := Ty.uint 256 }]
            body :=
              some
                (L00_SourceSolidity.Stmt.returnValues
                  (some
                    (L00_SourceSolidity.Expr.call
                      (L00_SourceSolidity.Expr.member
                        (L00_SourceSolidity.Expr.ident
                          "CheckedExternalMath")
                        "plusOne")
                      [L00_SourceSolidity.Arg.positional
                        (L00_SourceSolidity.Expr.ident "x")]))) } ] }

def checkedExternalLibraryUsingContract :
    L00_SourceSolidity.ContractDecl :=
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
                (L00_SourceSolidity.Stmt.returnValues
                  (some
                    (L00_SourceSolidity.Expr.call
                      (L00_SourceSolidity.Expr.member
                        (L00_SourceSolidity.Expr.ident "x") "plusOne")
                      []))) } ] }

def checkedExternalLibraryUnit : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          checkedExternalLibraryMath
      , L00_SourceSolidity.SourceItem.contract
          checkedExternalLibraryDirectContract
      , L00_SourceSolidity.SourceItem.contract
          checkedExternalLibraryUsingContract ] }

def checkedExternalLibraryDelegateCallMatches
    (contractName : Name) (input output : Word) :
    Except TypeError Bool := do
  let contract ← CheckedInput.contract checkedExternalLibraryUnit contractName
  let callResult ←
    optionToExcept "external library call result"
      (Executable.Examples.externalLibraryCallResult? input output)
  let result ←
    CheckedInput.callFunctionWithContext 64 checkedExternalLibraryUnit
      contractName "run"
      { contract.core.context with
        contractAddresses := [("CheckedExternalMath", 0xbeef)]
        lowLevelCallResults := [callResult] }
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

def checkedUsingModifierContract : L00_SourceSolidity.ContractDecl :=
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
                (L00_SourceSolidity.Stmt.block
                  [ L00_SourceSolidity.Stmt.expr
                      (L00_SourceSolidity.Expr.assign
                        (L00_SourceSolidity.Expr.ident "x")
                        AssignOp.assign
                        (L00_SourceSolidity.Expr.call
                          (L00_SourceSolidity.Expr.member
                            (L00_SourceSolidity.Expr.ident "start")
                            "inc")
                          []))
                  , L00_SourceSolidity.Stmt.modifierPlaceholder ]) }
      , ContractItem.function
          { name := some "run"
            visibility := some Visibility.public_
            params := [{ name := some "seed", ty := Ty.uint 256 }]
            modifiers :=
              [ { target := { segments := ["withBump"] }
                  args :=
                    [ L00_SourceSolidity.Arg.positional
                        (L00_SourceSolidity.Expr.call
                          (L00_SourceSolidity.Expr.member
                            (L00_SourceSolidity.Expr.ident "seed")
                            "inc")
                          []) ] } ]
            body := some L00_SourceSolidity.Stmt.empty } ] }

def checkedUsingModifierUnit : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract checkedUsingMathLibrary
      , L00_SourceSolidity.SourceItem.contract
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
    L00_SourceSolidity.ContractDecl :=
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
    L00_SourceSolidity.FunctionDecl :=
  { Executable.Examples.tryCatchAroundModifierFunction with
    params :=
      [{ name := some "target", ty := checkedModifierExternalTargetTy }]
    modifiers :=
      [ { target := { segments := ["aroundTry"] }
          args := [Arg.positional (Expr.ident "target")] } ]
    visibility := some Visibility.public_ }

def checkedTryCatchAroundModifier :
    L00_SourceSolidity.ModifierDecl :=
  { Executable.Examples.tryCatchAroundModifier with
    params :=
      [{ name := some "target", ty := checkedModifierExternalTargetTy }] }

def checkedTryCatchAroundModifierContract :
    L00_SourceSolidity.ContractDecl :=
  { name := "CheckedTryCatchModifier"
    items :=
      [ ContractItem.stateVar { name := "x", ty := Ty.uint 256 }
      , ContractItem.stateVar { name := "mark", ty := Ty.uint 256 }
      , ContractItem.modifierDecl checkedTryCatchAroundModifier
      , ContractItem.function checkedTryCatchAroundModifierFunction ] }

def checkedTryCatchAroundModifierUnit :
    L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          checkedModifierExternalTargetContract
      , L00_SourceSolidity.SourceItem.contract
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
    CheckedContract.callFunctionWithContext 64 contract "run"
      { contract.core.context with
        accountCodes := [(0xbeef, [1])]
        lowLevelCallResults :=
          [ { kind := SolidCore.Solidity.Source.LowLevelCallKind.staticcall
              target := 0xbeef
              calldata := calldata
              success := true
              output := output } ] }
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
    CheckedContract.callFunctionWithContext 64 contract "run"
      { contract.core.context with
        accountCodes := [(0xbeef, [1])]
        lowLevelCallResults :=
          [ { kind := SolidCore.Solidity.Source.LowLevelCallKind.staticcall
              target := 0xbeef
              calldata := calldata
              success := false
              output := [0xca, 0xfe] } ] }
      SolidCore.Solidity.Source.State.empty
      [SolidCore.Solidity.Source.Value.word 0xbeef]
  match result with
  | SolidCore.Solidity.Source.CallResult.returned state [] =>
      Except.ok
        (SolidCore.Solidity.Source.wordEq (state.loadSlot 0) 7 &&
          SolidCore.Solidity.Source.wordEq (state.loadSlot 1) 99)
  | _ => Except.ok false

def checkedDirectExternalCallModifier :
    L00_SourceSolidity.ModifierDecl :=
  { Executable.Examples.directExternalCallModifier with
    params :=
      [{ name := some "watched", ty := checkedModifierExternalTargetTy }] }

def checkedDirectExternalCallModifierFunction :
    L00_SourceSolidity.FunctionDecl :=
  { Executable.Examples.directExternalCallModifierFunction with
    params :=
      [{ name := some "target", ty := checkedModifierExternalTargetTy }]
    visibility := some Visibility.public_ }

def checkedDirectExternalCallModifierContract :
    L00_SourceSolidity.ContractDecl :=
  { name := "CheckedDirectExternalModifier"
    items :=
      [ ContractItem.stateVar { name := "x", ty := Ty.uint 256 }
      , ContractItem.stateVar { name := "mark", ty := Ty.uint 256 }
      , ContractItem.modifierDecl checkedDirectExternalCallModifier
      , ContractItem.function
          checkedDirectExternalCallModifierFunction ] }

def checkedDirectExternalCallModifierUnit :
    L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          checkedModifierExternalTargetContract
      , L00_SourceSolidity.SourceItem.contract
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
    CheckedContract.callFunctionWithContext 64 contract "run"
      { contract.core.context with
        accountCodes := [(0xbeef, [1])]
        lowLevelCallResults :=
          [ { kind := SolidCore.Solidity.Source.LowLevelCallKind.staticcall
              target := 0xbeef
              calldata := calldata
              success := true
              output := output } ] }
      SolidCore.Solidity.Source.State.empty
      [SolidCore.Solidity.Source.Value.word 0xbeef]
  match result with
  | SolidCore.Solidity.Source.CallResult.returned state [] =>
      Except.ok
        (SolidCore.Solidity.Source.wordEq (state.loadSlot 0) 7 &&
          SolidCore.Solidity.Source.wordEq (state.loadSlot 1) 77)
  | _ => Except.ok false

def checkedUsingConstructorContract :
    L00_SourceSolidity.ContractDecl :=
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
                (L00_SourceSolidity.Stmt.expr
                  (L00_SourceSolidity.Expr.assign
                    (L00_SourceSolidity.Expr.ident "x")
                    AssignOp.assign
                    (L00_SourceSolidity.Expr.call
                      (L00_SourceSolidity.Expr.member
                        (L00_SourceSolidity.Expr.ident "seed") "inc")
                      []))) } ] }

def checkedUsingConstructorUnit : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract checkedUsingMathLibrary
      , L00_SourceSolidity.SourceItem.contract
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
    L00_SourceSolidity.ContractDecl :=
  { name := "CheckedSuperStorageBase"
    items :=
      [ ContractItem.stateVar { name := "x", ty := Ty.uint 256 }
      , ContractItem.function
          { name := some "setX"
            visibility := some Visibility.public_
            body :=
              some
                (L00_SourceSolidity.Stmt.expr
                  (L00_SourceSolidity.Expr.assign
                    (L00_SourceSolidity.Expr.ident "x")
                    AssignOp.assign
                    (L00_SourceSolidity.Expr.literal
                      (L00_SourceSolidity.Literal.number "5")))) } ] }

def checkedSuperStorageDerivedContract :
    L00_SourceSolidity.ContractDecl :=
  { name := "CheckedSuperStorageDerived"
    bases := [{ base := { segments := ["CheckedSuperStorageBase"] } }]
    items :=
      [ ContractItem.function
          { name := some "setViaSuper"
            visibility := some Visibility.public_
            body :=
              some
                (L00_SourceSolidity.Stmt.expr
                  (L00_SourceSolidity.Expr.call
                    (L00_SourceSolidity.Expr.member
                      (L00_SourceSolidity.Expr.ident "super") "setX")
                    [])) } ] }

def checkedSuperStorageSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          checkedSuperStorageBaseContract
      , L00_SourceSolidity.SourceItem.contract
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

def checkedBadKeccakStorageLayoutRejected : Bool :=
  Result.isError (CheckedInput.program badKeccakStorageLayoutSource)

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
    L00_SourceSolidity.ContractDecl :=
  { name := "CheckedNonpayableCtor"
    items :=
      [ L00_SourceSolidity.ContractItem.stateVar
          { name := "x", ty := Ty.uint 256 }
      , L00_SourceSolidity.ContractItem.function
          { kind := FunctionKind.constructor
            mutability := StateMutability.nonpayable
            body :=
              some
                (L00_SourceSolidity.Stmt.expr
                  (L00_SourceSolidity.Expr.assign
                    (L00_SourceSolidity.Expr.ident "x")
                    AssignOp.assign
                    (L00_SourceSolidity.Expr.literal
                      (L00_SourceSolidity.Literal.number "17")))) } ] }

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

def checkedImmutableConstructorContract :
    L00_SourceSolidity.ContractDecl :=
  { name := "CheckedImmutableConstructor"
    items :=
      [ L00_SourceSolidity.ContractItem.stateVar
          { name := "SEED"
            ty := Ty.uint 256
            visibility := some Visibility.public_
            mutability := VarMutability.immutable
            init :=
              some
                (L00_SourceSolidity.Expr.literal
                  (L00_SourceSolidity.Literal.number "3")) }
      , L00_SourceSolidity.ContractItem.stateVar
          { name := "x"
            ty := Ty.uint 256
            visibility := some Visibility.public_
            mutability := VarMutability.immutable }
      , L00_SourceSolidity.ContractItem.function
          { kind := FunctionKind.constructor
            params := [{ name := some "value", ty := Ty.uint 256 }]
            body :=
              some
                (L00_SourceSolidity.Stmt.expr
                  (L00_SourceSolidity.Expr.assign
                    (L00_SourceSolidity.Expr.ident "x")
                    AssignOp.assign
                    (L00_SourceSolidity.Expr.binary BinaryOp.add
                      (L00_SourceSolidity.Expr.ident "value")
                      (L00_SourceSolidity.Expr.ident "SEED")))) }
      , L00_SourceSolidity.ContractItem.function
          { name := some "sum"
            visibility := some Visibility.public_
            returns := [{ name := some "out", ty := Ty.uint 256 }]
            mutability := StateMutability.view
            body :=
              some
                (L00_SourceSolidity.Stmt.returnValues
                  (some
                    (L00_SourceSolidity.Expr.binary BinaryOp.add
                      (L00_SourceSolidity.Expr.ident "x")
                      (L00_SourceSolidity.Expr.ident "SEED")))) } ] }

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
    L00_SourceSolidity.ContractDecl :=
  { checkedImmutableConstructorContract with
    name := "CheckedImmutableRuntimeWrite"
    items :=
      checkedImmutableConstructorContract.items ++
        [ L00_SourceSolidity.ContractItem.function
            { name := some "mutate"
              visibility := some Visibility.public_
              body :=
                some
                  (L00_SourceSolidity.Stmt.expr
                    (L00_SourceSolidity.Expr.assign
                      (L00_SourceSolidity.Expr.ident "x")
                      AssignOp.assign
                      (L00_SourceSolidity.Expr.literal
                        (L00_SourceSolidity.Literal.number "1")))) } ] }

def checkedImmutableRuntimeWriteRejectedByTypechecker : Bool :=
  Result.isError
    (ContractDecl.checkedContract checkedImmutableRuntimeWriteContract)

def checkedConstructorInternalCallContract :
    L00_SourceSolidity.ContractDecl :=
  { name := "CheckedCtorInternalCall"
    items :=
      [ L00_SourceSolidity.ContractItem.stateVar
          { name := "x", ty := Ty.uint 256 }
      , L00_SourceSolidity.ContractItem.function
          { name := some "double"
            visibility := some Visibility.internal_
            params := [{ name := some "value", ty := Ty.uint 256 }]
            returns := [{ name := some "out", ty := Ty.uint 256 }]
            body :=
              some
                (L00_SourceSolidity.Stmt.returnValues
                  (some
                    (L00_SourceSolidity.Expr.binary BinaryOp.mul
                      (L00_SourceSolidity.Expr.ident "value")
                      (L00_SourceSolidity.Expr.literal
                        (L00_SourceSolidity.Literal.number "2"))))) }
      , L00_SourceSolidity.ContractItem.function
          { kind := FunctionKind.constructor
            params := [{ name := some "seed", ty := Ty.uint 256 }]
            body :=
              some
                (L00_SourceSolidity.Stmt.expr
                  (L00_SourceSolidity.Expr.assign
                    (L00_SourceSolidity.Expr.ident "x")
                    AssignOp.assign
                    (L00_SourceSolidity.Expr.call
                      (L00_SourceSolidity.Expr.ident "double")
                      [L00_SourceSolidity.Arg.positional
                        (L00_SourceSolidity.Expr.ident "seed")]))) } ] }

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
    L00_SourceSolidity.ContractDecl :=
  { name := "CheckedEventArgumentSideEffect"
    items :=
      [ L00_SourceSolidity.ContractItem.eventDecl
          { name := "Seen"
            params :=
              [{ name := some "value"
                 ty := Ty.uint 256
                 indexed := false }] }
      , L00_SourceSolidity.ContractItem.stateVar
          { name := "x", ty := Ty.uint 256 }
      , L00_SourceSolidity.ContractItem.function
          { name := some "value"
            visibility := some Visibility.internal_
            returns := [{ name := some "out", ty := Ty.uint 256 }]
            body :=
              some
                (L00_SourceSolidity.Stmt.block
                  [ L00_SourceSolidity.Stmt.expr
                      (L00_SourceSolidity.Expr.assign
                        (L00_SourceSolidity.Expr.ident "x")
                        AssignOp.assign
                        (L00_SourceSolidity.Expr.literal
                          (L00_SourceSolidity.Literal.number "7")))
                  , L00_SourceSolidity.Stmt.returnValues
                      (some (L00_SourceSolidity.Expr.ident "x")) ]) }
      , L00_SourceSolidity.ContractItem.function
          { name := some "run"
            visibility := some Visibility.public_
            returns := [{ name := some "out", ty := Ty.uint 256 }]
            body :=
              some
                (L00_SourceSolidity.Stmt.block
                  [ L00_SourceSolidity.Stmt.emitEvent
                      (L00_SourceSolidity.Expr.call
                        (L00_SourceSolidity.Expr.ident "Seen")
                        [L00_SourceSolidity.Arg.positional
                          (L00_SourceSolidity.Expr.call
                            (L00_SourceSolidity.Expr.ident "value") [])])
                  , L00_SourceSolidity.Stmt.returnValues
                      (some (L00_SourceSolidity.Expr.ident "x")) ]) } ] }

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
    L00_SourceSolidity.ContractDecl :=
  { name := "CheckedErrorRollback"
    items :=
      [ L00_SourceSolidity.ContractItem.errorDecl
          { name := "Bad"
            params := [{ name := some "value", ty := Ty.uint 256 }] }
      , L00_SourceSolidity.ContractItem.stateVar
          { name := "x", ty := Ty.uint 256 }
      , L00_SourceSolidity.ContractItem.function
          { name := some "value"
            visibility := some Visibility.internal_
            returns := [{ name := some "out", ty := Ty.uint 256 }]
            body :=
              some
                (L00_SourceSolidity.Stmt.block
                  [ L00_SourceSolidity.Stmt.expr
                      (L00_SourceSolidity.Expr.assign
                        (L00_SourceSolidity.Expr.ident "x")
                        AssignOp.assign
                        (L00_SourceSolidity.Expr.literal
                          (L00_SourceSolidity.Literal.number "7")))
                  , L00_SourceSolidity.Stmt.returnValues
                      (some (L00_SourceSolidity.Expr.ident "x")) ]) }
      , L00_SourceSolidity.ContractItem.function
          { name := some "run"
            visibility := some Visibility.public_
            returns := [{ name := some "out", ty := Ty.uint 256 }]
            body :=
              some
                (L00_SourceSolidity.Stmt.block
                  [ L00_SourceSolidity.Stmt.revertCall
                      (L00_SourceSolidity.Expr.call
                        (L00_SourceSolidity.Expr.ident "Bad")
                        [L00_SourceSolidity.Arg.positional
                          (L00_SourceSolidity.Expr.call
                            (L00_SourceSolidity.Expr.ident "value") [])])
                  , L00_SourceSolidity.Stmt.returnValues
                      (some (L00_SourceSolidity.Expr.ident "x")) ]) } ] }

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

def checkedLowLevelCallContract : L00_SourceSolidity.ContractDecl :=
  { name := "CheckedLowLevelCall"
    items :=
      [ L00_SourceSolidity.ContractItem.function
          { name := some "probe"
            visibility := some Visibility.public_
            params :=
              [ { name := some "target", ty := Ty.address false }
              , { name := some "payload"
                  ty := Ty.bytes
                  location := some DataLocation.memory } ]
            returns := [{ name := some "out", ty := lowLevelCallReturnTy }]
            body :=
              some
                (L00_SourceSolidity.Stmt.returnValues
                  (some
                    (L00_SourceSolidity.Expr.call
                      (L00_SourceSolidity.Expr.member
                        (L00_SourceSolidity.Expr.ident "target") "call")
                      [L00_SourceSolidity.Arg.positional
                        (L00_SourceSolidity.Expr.ident "payload")]))) }
      , L00_SourceSolidity.ContractItem.function
          { name := some "payWithOptions"
            visibility := some Visibility.public_
            mutability := StateMutability.payable
            returns := [{ name := some "out", ty := lowLevelCallReturnTy }]
            body :=
              some
                (L00_SourceSolidity.Stmt.returnValues
                  (some
                    (L00_SourceSolidity.Expr.callWithOptions
                      (L00_SourceSolidity.Expr.member
                        (L00_SourceSolidity.Expr.literal
                          (L00_SourceSolidity.Literal.address 0xbeef))
                        "call")
                      [ L00_SourceSolidity.CallOption.named "gas"
                          (L00_SourceSolidity.Expr.literal
                            (L00_SourceSolidity.Literal.number "1000000"))
                      , L00_SourceSolidity.CallOption.named "value"
                          (L00_SourceSolidity.Expr.literal
                            (L00_SourceSolidity.Literal.number "5")) ]
                      [L00_SourceSolidity.Arg.positional
                        (L00_SourceSolidity.Expr.literal
                          (L00_SourceSolidity.Literal.bytes [1, 2]))]))) }
      , L00_SourceSolidity.ContractItem.function
          { name := some "payWithOptionEffects"
            visibility := some Visibility.public_
            mutability := StateMutability.payable
            returns :=
              [ { name := some "out", ty := lowLevelCallReturnTy }
              , { name := some "gasSeen", ty := Ty.uint 256 }
              , { name := some "sent", ty := Ty.uint 256 } ]
            body :=
              some
                (L00_SourceSolidity.Stmt.block
                  [ L00_SourceSolidity.Stmt.varDecl
                      [{ name := some "gasSeen"
                         ty := some (Ty.uint 256) }]
                      (some
                        (L00_SourceSolidity.Expr.literal
                          (L00_SourceSolidity.Literal.number "0")))
                  , L00_SourceSolidity.Stmt.varDecl
                      [{ name := some "sent"
                         ty := some (Ty.uint 256) }]
                      (some
                        (L00_SourceSolidity.Expr.literal
                          (L00_SourceSolidity.Literal.number "0")))
                  , L00_SourceSolidity.Stmt.returnValues
                      (some
                        (L00_SourceSolidity.Expr.tuple
                          [ L00_SourceSolidity.TupleItem.value
                              (L00_SourceSolidity.Expr.callWithOptions
                                (L00_SourceSolidity.Expr.member
                                  (L00_SourceSolidity.Expr.literal
                                    (L00_SourceSolidity.Literal.address
                                      0xbeef))
                                  "call")
                                [ L00_SourceSolidity.CallOption.named "gas"
                                    (L00_SourceSolidity.Expr.assign
                                      (L00_SourceSolidity.Expr.ident
                                        "gasSeen")
                                      AssignOp.assign
                                      (L00_SourceSolidity.Expr.literal
                                        (L00_SourceSolidity.Literal.number
                                          "11")))
                                , L00_SourceSolidity.CallOption.named "value"
                                    (L00_SourceSolidity.Expr.assign
                                      (L00_SourceSolidity.Expr.ident "sent")
                                      AssignOp.assign
                                      (L00_SourceSolidity.Expr.literal
                                        (L00_SourceSolidity.Literal.number
                                          "5"))) ]
                                [L00_SourceSolidity.Arg.positional
                                  (L00_SourceSolidity.Expr.literal
                                    (L00_SourceSolidity.Literal.bytes
                                      [1, 2]))])
                          , L00_SourceSolidity.TupleItem.value
                              (L00_SourceSolidity.Expr.ident "gasSeen")
                          , L00_SourceSolidity.TupleItem.value
                              (L00_SourceSolidity.Expr.ident "sent") ])) ]) }
      , L00_SourceSolidity.ContractItem.function
          { name := some "probeBoth"
            visibility := some Visibility.public_
            params :=
              [ { name := some "target", ty := Ty.address false }
              , { name := some "payload"
                  ty := Ty.bytes
                  location := some DataLocation.memory } ]
            returns :=
              [ { name := some "staticOut", ty := lowLevelCallReturnTy }
              , { name := some "delegateOut", ty := lowLevelCallReturnTy } ]
            body :=
              some
                (L00_SourceSolidity.Stmt.returnValues
                  (some
                    (L00_SourceSolidity.Expr.tuple
                      [ L00_SourceSolidity.TupleItem.value
                          (L00_SourceSolidity.Expr.callWithOptions
                            (L00_SourceSolidity.Expr.member
                              (L00_SourceSolidity.Expr.ident "target")
                              "staticcall")
                            [L00_SourceSolidity.CallOption.named "gas"
                              (L00_SourceSolidity.Expr.literal
                                (L00_SourceSolidity.Literal.number
                                  "50000"))]
                            [L00_SourceSolidity.Arg.positional
                              (L00_SourceSolidity.Expr.ident "payload")])
                      , L00_SourceSolidity.TupleItem.value
                          (L00_SourceSolidity.Expr.call
                            (L00_SourceSolidity.Expr.member
                              (L00_SourceSolidity.Expr.ident "target")
                              "delegatecall")
                            [L00_SourceSolidity.Arg.positional
                              (L00_SourceSolidity.Expr.ident "payload")]) ]))) }
      , L00_SourceSolidity.ContractItem.function
          { name := some "delegateGas"
            visibility := some Visibility.public_
            params :=
              [ { name := some "target", ty := Ty.address false }
              , { name := some "payload"
                  ty := Ty.bytes
                  location := some DataLocation.memory } ]
            returns := [{ name := some "out", ty := lowLevelCallReturnTy }]
            body :=
              some
                (L00_SourceSolidity.Stmt.returnValues
                  (some
                    (L00_SourceSolidity.Expr.callWithOptions
                      (L00_SourceSolidity.Expr.member
                        (L00_SourceSolidity.Expr.ident "target")
                        "delegatecall")
                      [L00_SourceSolidity.CallOption.named "gas"
                        (L00_SourceSolidity.Expr.literal
                          (L00_SourceSolidity.Literal.number "900"))]
                      [L00_SourceSolidity.Arg.positional
                        (L00_SourceSolidity.Expr.ident "payload")]))) } ] }

def checkedLowLevelCallMatches : Except TypeError Bool := do
  let contract ← ContractDecl.checkedContract checkedLowLevelCallContract
  let result ←
    CheckedContract.callFunctionWithContext 16 contract "probe"
      { contract.core.context with
        lowLevelCallResults :=
          [ { kind := SolidCore.Solidity.Source.LowLevelCallKind.call
              target := 0xbeef
              calldata := [1, 2, 3]
              success := true
              output := [9, 8] } ] }
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
    CheckedContract.callFunctionWithContext 16 contract "payWithOptions"
      { contract.core.context with
        lowLevelCallResults :=
          [ { kind := SolidCore.Solidity.Source.LowLevelCallKind.call
              target := 0xbeef
              calldata := [1, 2]
              value := 5
              gas? := some 1000000
              success := true
              output := [4, 5, 6] } ] }
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
    CheckedContract.callFunctionWithContext 16 contract "payWithOptions"
      { contract.core.context with
        lowLevelCallResults :=
          [ { kind := SolidCore.Solidity.Source.LowLevelCallKind.call
              target := 0xbeef
              calldata := [1, 2]
              value := 5
              gas? := some 999999
              success := true
              output := [4, 5, 6] } ] }
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
    CheckedContract.callFunctionWithContext 32 contract "payWithOptionEffects"
      { contract.core.context with
        lowLevelCallResults :=
          [ { kind := SolidCore.Solidity.Source.LowLevelCallKind.call
              target := 0xbeef
              calldata := [1, 2]
              value := 5
              gas? := some 11
              success := true
              output := [4, 5, 6] } ] }
      SolidCore.Solidity.Source.State.empty []
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _
      [value, SolidCore.Solidity.Source.Value.word gasSeen,
        SolidCore.Solidity.Source.Value.word sent] => do
      let (success, output) ← checkedDecodeLowLevelReturn value
      Except.ok
        (SolidCore.Solidity.Source.wordEq success 1 &&
          output == [4, 5, 6] &&
          SolidCore.Solidity.Source.wordEq gasSeen 11 &&
          SolidCore.Solidity.Source.wordEq sent 5)
  | _ => Except.ok false

def checkedLowLevelStaticDelegateMatches :
    Except TypeError Bool := do
  let contract ← ContractDecl.checkedContract checkedLowLevelCallContract
  let result ←
    CheckedContract.callFunctionWithContext 16 contract "probeBoth"
      { contract.core.context with
        lowLevelCallResults :=
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
              output := [2, 3] } ] }
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
    CheckedContract.callFunctionWithContext 16 contract "delegateGas"
      { contract.core.context with
        lowLevelCallResults :=
          [ { kind := SolidCore.Solidity.Source.LowLevelCallKind.delegatecall
              target := 0xcafe
              calldata := [7, 7]
              gas? := some 900
              success := true
              output := [9, 0] } ] }
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

def checkedLowLevelSendMatches : Except TypeError Bool := do
  let program ← SourceUnit.checkedProgram lowLevelSendSource
  let contract ← CheckedProgram.contract program "LowLevelSend"
  let result ←
    CheckedContract.callFunctionWithContext 16 contract "sendIt"
      { contract.core.context with
        lowLevelCallResults :=
          [ { kind := SolidCore.Solidity.Source.LowLevelCallKind.call
              target := 0xbeef
              calldata := []
              value := 1
              gas? := some 2300
              success := true
              output := [] } ] }
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
    CheckedContract.callFunctionWithContext 16 contract "sendIt"
      { contract.core.context with
        lowLevelCallResults :=
          [ { kind := SolidCore.Solidity.Source.LowLevelCallKind.call
              target := 0xbeef
              calldata := []
              value := 1
              gas? := some 2300
              success := false
              output := [0xde, 0xad] } ] }
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

def checkedTransferValueContract : L00_SourceSolidity.ContractDecl :=
  { name := "CheckedTransferValue"
    items :=
      [ L00_SourceSolidity.ContractItem.stateVar
          { name := "x", ty := Ty.uint 256 }
      , L00_SourceSolidity.ContractItem.function
          { name := some "pay"
            visibility := some Visibility.public_
            params :=
              [ { name := some "target", ty := Ty.address true }
              , { name := some "amount", ty := Ty.uint 256 } ]
            body :=
              some
                (L00_SourceSolidity.Stmt.block
                  [ L00_SourceSolidity.Stmt.expr
                      (L00_SourceSolidity.Expr.assign
                        (L00_SourceSolidity.Expr.ident "x")
                        AssignOp.assign
                        (L00_SourceSolidity.Expr.literal
                          (L00_SourceSolidity.Literal.number "1")))
                  , L00_SourceSolidity.Stmt.expr
                      (L00_SourceSolidity.Expr.call
                        (L00_SourceSolidity.Expr.member
                          (L00_SourceSolidity.Expr.ident "target")
                          "transfer")
                        [L00_SourceSolidity.Arg.positional
                          (L00_SourceSolidity.Expr.ident "amount")])
                  , L00_SourceSolidity.Stmt.expr
                      (L00_SourceSolidity.Expr.assign
                        (L00_SourceSolidity.Expr.ident "x")
                        AssignOp.assign
                        (L00_SourceSolidity.Expr.literal
                          (L00_SourceSolidity.Literal.number "2"))) ]) } ] }

def checkedTransferValueSuccessMatches : Except TypeError Bool := do
  let contract ← ContractDecl.checkedContract checkedTransferValueContract
  let result ←
    CheckedContract.callFunctionWithContext 16 contract "pay"
      { contract.core.context with
        lowLevelCallResults :=
          [ { kind := SolidCore.Solidity.Source.LowLevelCallKind.call
              target := 0xbeef
              calldata := []
              value := 5
              gas? := some 2300
              success := true
              output := [] } ] }
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
    CheckedContract.callFunctionWithContext 16 contract "pay"
      { contract.core.context with
        lowLevelCallResults :=
          [ { kind := SolidCore.Solidity.Source.LowLevelCallKind.call
              target := 0xbeef
              calldata := []
              value := 5
              gas? := some 2300
              success := false
              output := [0xba, 0xad] } ] }
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
    L00_SourceSolidity.ContractDecl :=
  { name := "CheckedPrecompileStaticcall"
    items :=
      [ L00_SourceSolidity.ContractItem.function
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
                (L00_SourceSolidity.Stmt.returnValues
                  (some
                    (L00_SourceSolidity.Expr.tuple
                      [ L00_SourceSolidity.TupleItem.value
                          (L00_SourceSolidity.Expr.call
                            (L00_SourceSolidity.Expr.ident "sha256")
                            [L00_SourceSolidity.Arg.positional
                              (L00_SourceSolidity.Expr.literal
                                (L00_SourceSolidity.Literal.bytes
                                  [1, 2]))])
                      , L00_SourceSolidity.TupleItem.value
                          (L00_SourceSolidity.Expr.call
                            (L00_SourceSolidity.Expr.member
                              (L00_SourceSolidity.Expr.literal
                                (L00_SourceSolidity.Literal.address
                                  (SharedSemantics.Precompile.address
                                    SharedSemantics.Precompile.Kind.sha256)))
                              "staticcall")
                            [L00_SourceSolidity.Arg.positional
                              (L00_SourceSolidity.Expr.literal
                                (L00_SourceSolidity.Literal.bytes
                                  [1, 2]))]) ]))) } ] }

def checkedPrecompileStaticcallMatches :
    Except TypeError Bool := do
  let contract ←
    ContractDecl.checkedContract checkedPrecompileStaticcallContract
  let expectedOutput :=
    SolidCore.Solidity.Source.wordToBytesBE
      SolidCore.Solidity.Source.wordBytes 0xaaaa
  let result ←
    CheckedContract.callFunctionWithContext 16 contract "hashAndProbe"
      { contract.core.context with
        lowLevelCallResults :=
          [ Executable.Examples.successfulPrecompileWordCall
              SharedSemantics.Precompile.Kind.sha256 [1, 2] 0xaaaa ] }
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

def checkedCreatedChildContract : L00_SourceSolidity.ContractDecl :=
  { name := "CheckedCreatedChild"
    items :=
      [ L00_SourceSolidity.ContractItem.function
          (seedConstructor StateMutability.nonpayable) ] }

def checkedNamedCreatedChildTy : Ty :=
  Ty.user { segments := ["CheckedNamedCreatedChild"] }

def checkedNamedCreatedChildContract :
    L00_SourceSolidity.ContractDecl :=
  { name := "CheckedNamedCreatedChild"
    items :=
      [ L00_SourceSolidity.ContractItem.function
          { kind := FunctionKind.constructor
            params :=
              [ { name := some "amount", ty := Ty.uint 256 }
              , { name := some "bonus", ty := Ty.uint 256 } ]
            mutability := StateMutability.payable
            body := some L00_SourceSolidity.Stmt.empty } ] }

def checkedContractCreationCaller :
    L00_SourceSolidity.ContractDecl :=
  { name := "CheckedCreateCaller"
    items :=
      [ L00_SourceSolidity.ContractItem.stateVar
          { name := "x", ty := Ty.uint 256 }
      , L00_SourceSolidity.ContractItem.function
          { name := some "make"
            visibility := some Visibility.public_
            params := [{ name := some "seed", ty := Ty.uint 256 }]
            returns :=
              [{ name := some "created", ty := checkedCreatedChildTy }]
            body :=
              some
                (L00_SourceSolidity.Stmt.returnValues
                  (some
                    (L00_SourceSolidity.Expr.newExpr
                      checkedCreatedChildTy
                      [L00_SourceSolidity.Arg.positional
                        (L00_SourceSolidity.Expr.ident "seed")]))) }
      , L00_SourceSolidity.ContractItem.function
          { name := some "makeNamed"
            visibility := some Visibility.public_
            params :=
              [ { name := some "amount", ty := Ty.uint 256 }
              , { name := some "bonus", ty := Ty.uint 256 } ]
            returns :=
              [{ name := some "created", ty := checkedNamedCreatedChildTy }]
            body :=
              some
                (L00_SourceSolidity.Stmt.returnValues
                  (some
                    (L00_SourceSolidity.Expr.newExpr
                      checkedNamedCreatedChildTy
                      [ L00_SourceSolidity.Arg.named "bonus"
                          (L00_SourceSolidity.Expr.ident "bonus")
                      , L00_SourceSolidity.Arg.named "amount"
                          (L00_SourceSolidity.Expr.ident "amount") ]))) }
      , L00_SourceSolidity.ContractItem.function
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
                (L00_SourceSolidity.Stmt.returnValues
                  (some
                    (L00_SourceSolidity.Expr.callWithOptions
                      (L00_SourceSolidity.Expr.newExpr
                        checkedNamedCreatedChildTy [])
                      [ L00_SourceSolidity.CallOption.named "value"
                          (L00_SourceSolidity.Expr.ident "payment")
                      , L00_SourceSolidity.CallOption.named "salt"
                          (L00_SourceSolidity.Expr.ident "salt") ]
                      [ L00_SourceSolidity.Arg.named "bonus"
                          (L00_SourceSolidity.Expr.ident "bonus")
                      , L00_SourceSolidity.Arg.named "amount"
                          (L00_SourceSolidity.Expr.ident "amount") ]))) }
      , L00_SourceSolidity.ContractItem.function
          { name := some "makeFailure"
            visibility := some Visibility.public_
            body :=
              some
                (L00_SourceSolidity.Stmt.block
                  [ L00_SourceSolidity.Stmt.expr
                      (L00_SourceSolidity.Expr.assign
                        (L00_SourceSolidity.Expr.ident "x")
                        AssignOp.assign
                        (L00_SourceSolidity.Expr.literal
                          (L00_SourceSolidity.Literal.number "1")))
                  , L00_SourceSolidity.Stmt.expr
                      (L00_SourceSolidity.Expr.newExpr
                        checkedCreatedChildTy
                        [L00_SourceSolidity.Arg.positional
                          (L00_SourceSolidity.Expr.literal
                            (L00_SourceSolidity.Literal.number "7"))])
                  , L00_SourceSolidity.Stmt.expr
                      (L00_SourceSolidity.Expr.assign
                        (L00_SourceSolidity.Expr.ident "x")
                        AssignOp.assign
                        (L00_SourceSolidity.Expr.literal
                          (L00_SourceSolidity.Literal.number "2"))) ]) }
      , L00_SourceSolidity.ContractItem.function
          { name := some "tryMake"
            visibility := some Visibility.public_
            returns := [{ name := some "out", ty := Ty.uint 256 }]
            body :=
              some
                (L00_SourceSolidity.Stmt.block
                  [ L00_SourceSolidity.Stmt.tryCatch
                      (L00_SourceSolidity.Expr.newExpr
                        checkedCreatedChildTy
                        [L00_SourceSolidity.Arg.positional
                          (L00_SourceSolidity.Expr.literal
                            (L00_SourceSolidity.Literal.number "7"))])
                      [ L00_SourceSolidity.CatchClause.clause none []
                          (L00_SourceSolidity.Stmt.returnValues
                            (some
                              (L00_SourceSolidity.Expr.literal
                                (L00_SourceSolidity.Literal.number
                                  "0")))) ]
                  , L00_SourceSolidity.Stmt.returnValues
                      (some
                        (L00_SourceSolidity.Expr.literal
                          (L00_SourceSolidity.Literal.number "1"))) ]) } ] }

def checkedContractCreationSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          checkedCreatedChildContract
      , L00_SourceSolidity.SourceItem.contract
          checkedNamedCreatedChildContract
      , L00_SourceSolidity.SourceItem.contract
          checkedContractCreationCaller ] }

def checkedContractCreationMatches : Except TypeError Bool := do
  let constructorArgs ←
    checkedAbiEncodeValues
      [SolidCore.Solidity.Source.Ty.uint256]
      [SolidCore.Solidity.Source.Value.word 7]
  let program ← SourceUnit.checkedProgram checkedContractCreationSource
  let contract ← CheckedProgram.contract program "CheckedCreateCaller"
  let result ←
    CheckedContract.callFunctionWithContext 16 contract "make"
      { contract.core.context with
        contractCreationResults :=
          [ { contractName := "CheckedCreatedChild"
              constructorArgs := constructorArgs
              success := true
              address := 0xc0de } ] }
      SolidCore.Solidity.Source.State.empty
      [SolidCore.Solidity.Source.Value.word 7]
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _
      [SolidCore.Solidity.Source.Value.word address] =>
      Except.ok (SolidCore.Solidity.Source.wordEq address 0xc0de)
  | _ => Except.ok false

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
    CheckedContract.callFunctionWithContext 16 contract "makeNamed"
      { contract.core.context with
        contractCreationResults :=
          [ { contractName := "CheckedNamedCreatedChild"
              constructorArgs := constructorArgs
              success := true
              address := 0xc0de } ] }
      SolidCore.Solidity.Source.State.empty
      [ SolidCore.Solidity.Source.Value.word 40
      , SolidCore.Solidity.Source.Value.word 2 ]
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _
      [SolidCore.Solidity.Source.Value.word address] =>
      Except.ok (SolidCore.Solidity.Source.wordEq address 0xc0de)
  | _ => Except.ok false

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
    CheckedContract.callFunctionWithContext 16 contract "makeNamedSalted"
      { contract.core.context with
        contractCreationResults :=
          [ { contractName := "CheckedNamedCreatedChild"
              constructorArgs := constructorArgs
              value := 5
              salt? := some 0x1234
              success := true
              address := 0xcafe } ] }
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

def checkedContractCreationFailureReverts :
    Except TypeError Bool := do
  let constructorArgs ←
    checkedAbiEncodeValues
      [SolidCore.Solidity.Source.Ty.uint256]
      [SolidCore.Solidity.Source.Value.word 7]
  let program ← SourceUnit.checkedProgram checkedContractCreationSource
  let contract ← CheckedProgram.contract program "CheckedCreateCaller"
  let result ←
    CheckedContract.callFunctionWithContext 16 contract "makeFailure"
      { contract.core.context with
        contractCreationResults :=
          [ { contractName := "CheckedCreatedChild"
              constructorArgs := constructorArgs
              success := false
              output := [0xca, 0xfe] } ] }
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
    CheckedContract.callFunctionWithContext 16 contract "tryMake"
      { contract.core.context with
        contractCreationResults :=
          [ { contractName := "CheckedCreatedChild"
              constructorArgs := constructorArgs
              success := true
              address := 0xc0de } ] }
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
    CheckedContract.callFunctionWithContext 16 contract "tryMake"
      { contract.core.context with
        contractCreationResults :=
          [ { contractName := "CheckedCreatedChild"
              constructorArgs := constructorArgs
              success := false
              output := [0xca, 0xfe] } ] }
      SolidCore.Solidity.Source.State.empty []
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _
      [SolidCore.Solidity.Source.Value.word value] =>
      Except.ok (SolidCore.Solidity.Source.wordEq value 0)
  | _ => Except.ok false

def checkedTryOperandTargetTy : Ty :=
  Ty.user { segments := ["CheckedTryOperandTarget"] }

def checkedTryOperandTargetContract :
    L00_SourceSolidity.ContractDecl :=
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
    L00_SourceSolidity.ContractDecl :=
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
                (L00_SourceSolidity.Stmt.block
                  [ L00_SourceSolidity.Stmt.varDecl
                      [{ name := some "target"
                         ty := some checkedTryOperandTargetTy }]
                      (some
                        (L00_SourceSolidity.Expr.call
                          (L00_SourceSolidity.Expr.typeName
                            checkedTryOperandTargetTy)
                          [ L00_SourceSolidity.Arg.positional
                              (L00_SourceSolidity.Expr.literal
                                (L00_SourceSolidity.Literal.address 0)) ]))
                  , L00_SourceSolidity.Stmt.varDecl
                      [{ name := some "value", ty := some (Ty.uint 256) }]
                      (some
                        (L00_SourceSolidity.Expr.literal
                          (L00_SourceSolidity.Literal.number "0")))
                  , L00_SourceSolidity.Stmt.varDecl
                      [{ name := some "arg", ty := some (Ty.uint 256) }]
                      (some
                        (L00_SourceSolidity.Expr.literal
                          (L00_SourceSolidity.Literal.number "0")))
                  , L00_SourceSolidity.Stmt.tryCatchReturns
                      (L00_SourceSolidity.Expr.callWithOptions
                        (L00_SourceSolidity.Expr.member
                          (L00_SourceSolidity.Expr.assign
                            (L00_SourceSolidity.Expr.ident "target")
                            AssignOp.assign
                            (L00_SourceSolidity.Expr.call
                              (L00_SourceSolidity.Expr.typeName
                                checkedTryOperandTargetTy)
                              [ L00_SourceSolidity.Arg.positional
                                  (L00_SourceSolidity.Expr.literal
                                    (L00_SourceSolidity.Literal.address
                                      51966)) ]))
                          "ping")
                        [ L00_SourceSolidity.CallOption.named "value"
                            (L00_SourceSolidity.Expr.assign
                              (L00_SourceSolidity.Expr.ident "value")
                              AssignOp.assign
                              (L00_SourceSolidity.Expr.literal
                                (L00_SourceSolidity.Literal.number "7"))) ]
                        [ L00_SourceSolidity.Arg.positional
                            (L00_SourceSolidity.Expr.call
                              (L00_SourceSolidity.Expr.typeName
                                (Ty.uint 256))
                              [ L00_SourceSolidity.Arg.positional
                                  (L00_SourceSolidity.Expr.assign
                                    (L00_SourceSolidity.Expr.ident "arg")
                                    AssignOp.assign
                                    (L00_SourceSolidity.Expr.literal
                                      (L00_SourceSolidity.Literal.number
                                        "3"))) ]) ])
                      [{ name := some "out", ty := Ty.uint 256 }]
                      (L00_SourceSolidity.Stmt.returnValues
                        (some
                          (L00_SourceSolidity.Expr.tuple
                            [ L00_SourceSolidity.TupleItem.value
                                (L00_SourceSolidity.Expr.call
                                  (L00_SourceSolidity.Expr.typeName
                                    (Ty.address false))
                                  [ L00_SourceSolidity.Arg.positional
                                      (L00_SourceSolidity.Expr.ident
                                        "target") ])
                            , L00_SourceSolidity.TupleItem.value
                                (L00_SourceSolidity.Expr.ident "value")
                            , L00_SourceSolidity.TupleItem.value
                                (L00_SourceSolidity.Expr.ident "arg")
                            , L00_SourceSolidity.TupleItem.value
                                (L00_SourceSolidity.Expr.ident "out") ])))
                      [ L00_SourceSolidity.CatchClause.clause none []
                          (L00_SourceSolidity.Stmt.returnValues
                            (some
                              (L00_SourceSolidity.Expr.tuple
                                [ L00_SourceSolidity.TupleItem.value
                                    (L00_SourceSolidity.Expr.literal
                                      (L00_SourceSolidity.Literal.address
                                        0))
                                , L00_SourceSolidity.TupleItem.value
                                    (L00_SourceSolidity.Expr.literal
                                      (L00_SourceSolidity.Literal.number
                                        "0"))
                                , L00_SourceSolidity.TupleItem.value
                                    (L00_SourceSolidity.Expr.literal
                                      (L00_SourceSolidity.Literal.number
                                        "0"))
                                , L00_SourceSolidity.TupleItem.value
                                    (L00_SourceSolidity.Expr.literal
                                      (L00_SourceSolidity.Literal.number
                                        "0")) ]))) ] ]) } ] }

def checkedTryOperandMadeTy : Ty :=
  Ty.user { segments := ["CheckedTryOperandMade"] }

def checkedTryOperandMadeContract : L00_SourceSolidity.ContractDecl :=
  { name := "CheckedTryOperandMade"
    items :=
      [ ContractItem.function
          { kind := FunctionKind.constructor
            params := [{ name := some "x", ty := Ty.uint 256 }]
            mutability := StateMutability.payable
            body := some L00_SourceSolidity.Stmt.empty } ] }

def checkedTryContractCreateOperandEffectsContract :
    L00_SourceSolidity.ContractDecl :=
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
                (L00_SourceSolidity.Stmt.block
                  [ L00_SourceSolidity.Stmt.varDecl
                      [{ name := some "value", ty := some (Ty.uint 256) }]
                      (some
                        (L00_SourceSolidity.Expr.literal
                          (L00_SourceSolidity.Literal.number "0")))
                  , L00_SourceSolidity.Stmt.varDecl
                      [{ name := some "salt", ty := some (Ty.bytesN 32) }]
                      (some
                        (L00_SourceSolidity.Expr.call
                          (L00_SourceSolidity.Expr.typeName
                            (Ty.bytesN 32))
                          [ L00_SourceSolidity.Arg.positional
                              (L00_SourceSolidity.Expr.literal
                                (L00_SourceSolidity.Literal.number
                                  "0")) ]))
                  , L00_SourceSolidity.Stmt.varDecl
                      [{ name := some "arg", ty := some (Ty.uint 256) }]
                      (some
                        (L00_SourceSolidity.Expr.literal
                          (L00_SourceSolidity.Literal.number "0")))
                  , L00_SourceSolidity.Stmt.tryCatchReturns
                      (L00_SourceSolidity.Expr.callWithOptions
                        (L00_SourceSolidity.Expr.newExpr
                          checkedTryOperandMadeTy [])
                        [ L00_SourceSolidity.CallOption.named "value"
                            (L00_SourceSolidity.Expr.assign
                              (L00_SourceSolidity.Expr.ident "value")
                              AssignOp.assign
                              (L00_SourceSolidity.Expr.literal
                                (L00_SourceSolidity.Literal.number "7")))
                        , L00_SourceSolidity.CallOption.named "salt"
                            (L00_SourceSolidity.Expr.assign
                              (L00_SourceSolidity.Expr.ident "salt")
                              AssignOp.assign
                              (L00_SourceSolidity.Expr.call
                                (L00_SourceSolidity.Expr.typeName
                                  (Ty.bytesN 32))
                                [ L00_SourceSolidity.Arg.positional
                                    (L00_SourceSolidity.Expr.literal
                                      (L00_SourceSolidity.Literal.number
                                        "5")) ])) ]
                        [ L00_SourceSolidity.Arg.positional
                            (L00_SourceSolidity.Expr.call
                              (L00_SourceSolidity.Expr.typeName
                                (Ty.uint 256))
                              [ L00_SourceSolidity.Arg.positional
                                  (L00_SourceSolidity.Expr.assign
                                    (L00_SourceSolidity.Expr.ident "arg")
                                    AssignOp.assign
                                    (L00_SourceSolidity.Expr.literal
                                      (L00_SourceSolidity.Literal.number
                                        "3"))) ]) ])
                      [{ name := some "made"
                         ty := checkedTryOperandMadeTy }]
                      (L00_SourceSolidity.Stmt.returnValues
                        (some
                          (L00_SourceSolidity.Expr.tuple
                            [ L00_SourceSolidity.TupleItem.value
                                (L00_SourceSolidity.Expr.ident "value")
                            , L00_SourceSolidity.TupleItem.value
                                (L00_SourceSolidity.Expr.ident "salt")
                            , L00_SourceSolidity.TupleItem.value
                                (L00_SourceSolidity.Expr.ident "arg")
                            , L00_SourceSolidity.TupleItem.value
                                (L00_SourceSolidity.Expr.call
                                  (L00_SourceSolidity.Expr.typeName
                                    (Ty.address false))
                                  [ L00_SourceSolidity.Arg.positional
                                      (L00_SourceSolidity.Expr.ident
                                        "made") ]) ])))
                      [ L00_SourceSolidity.CatchClause.clause none []
                          (L00_SourceSolidity.Stmt.returnValues
                            (some
                              (L00_SourceSolidity.Expr.tuple
                                [ L00_SourceSolidity.TupleItem.value
                                    (L00_SourceSolidity.Expr.literal
                                      (L00_SourceSolidity.Literal.number
                                        "0"))
                                , L00_SourceSolidity.TupleItem.value
                                    (L00_SourceSolidity.Expr.call
                                      (L00_SourceSolidity.Expr.typeName
                                        (Ty.bytesN 32))
                                      [ L00_SourceSolidity.Arg.positional
                                          (L00_SourceSolidity.Expr.literal
                                            (L00_SourceSolidity.Literal.number
                                              "0")) ])
                                , L00_SourceSolidity.TupleItem.value
                                    (L00_SourceSolidity.Expr.literal
                                      (L00_SourceSolidity.Literal.number
                                        "0"))
                                , L00_SourceSolidity.TupleItem.value
                                    (L00_SourceSolidity.Expr.literal
                                      (L00_SourceSolidity.Literal.address
                                        0)) ]))) ] ]) } ] }

def checkedTryOperandEffectsUnit : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          checkedTryOperandTargetContract
      , L00_SourceSolidity.SourceItem.contract
          checkedTryExternalCallOperandEffectsContract
      , L00_SourceSolidity.SourceItem.contract
          checkedTryOperandMadeContract
      , L00_SourceSolidity.SourceItem.contract
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
    checkedSourceFunctionCallWithContext 32 checkedTryOperandEffectsUnit
      "CheckedTryExternalCallOperandEffects" "run"
      { SolidCore.Solidity.Source.Context.empty with
        lowLevelCallResults :=
          [ { kind := SolidCore.Solidity.Source.LowLevelCallKind.call
              target := 51966
              calldata := callData
              value := 7
              success := true
              output := output } ] }
      SolidCore.Solidity.Source.State.empty []
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _
      [ SolidCore.Solidity.Source.Value.word target
      , SolidCore.Solidity.Source.Value.word value
      , SolidCore.Solidity.Source.Value.word arg
      , SolidCore.Solidity.Source.Value.word out ] =>
      Except.ok
        (SolidCore.Solidity.Source.wordEq target 51966 &&
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
    checkedSourceFunctionCallWithContext 32 checkedTryOperandEffectsUnit
      "CheckedTryContractCreateOperandEffects" "run"
      { SolidCore.Solidity.Source.Context.empty with
        contractCreationResults :=
          [ { contractName := "CheckedTryOperandMade"
              constructorArgs := constructorArgs
              value := 7
              salt? := some 5
              success := true
              address := 51966
              output := [] } ] }
      SolidCore.Solidity.Source.State.empty []
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _
      [ SolidCore.Solidity.Source.Value.word value
      , SolidCore.Solidity.Source.Value.word salt
      , SolidCore.Solidity.Source.Value.word arg
      , SolidCore.Solidity.Source.Value.word made ] =>
      Except.ok
        (SolidCore.Solidity.Source.wordEq value 7 &&
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

def checkedTransientStorageContract : L00_SourceSolidity.ContractDecl :=
  { name := "CheckedTransientStorage"
    items :=
      [ L00_SourceSolidity.ContractItem.stateVar
          { name := "persistent", ty := Ty.uint 256 }
      , L00_SourceSolidity.ContractItem.stateVar
          { name := "scratch"
            ty := Ty.uint 256
            visibility := some Visibility.public_
            mutability := VarMutability.transient }
      , L00_SourceSolidity.ContractItem.function
          { name := some "setBoth"
            visibility := some Visibility.public_
            returns := [{ name := some "out", ty := Ty.uint 256 }]
            body :=
              some
                (L00_SourceSolidity.Stmt.block
                  [ L00_SourceSolidity.Stmt.expr
                      (L00_SourceSolidity.Expr.assign
                        (L00_SourceSolidity.Expr.ident "persistent")
                        AssignOp.assign
                        (L00_SourceSolidity.Expr.literal
                          (L00_SourceSolidity.Literal.number "7")))
                  , L00_SourceSolidity.Stmt.expr
                      (L00_SourceSolidity.Expr.assign
                        (L00_SourceSolidity.Expr.ident "scratch")
                        AssignOp.assign
                        (L00_SourceSolidity.Expr.literal
                          (L00_SourceSolidity.Literal.number "9")))
                  , L00_SourceSolidity.Stmt.returnValues
                      (some
                        (L00_SourceSolidity.Expr.binary BinaryOp.add
                          (L00_SourceSolidity.Expr.binary BinaryOp.mul
                            (L00_SourceSolidity.Expr.ident "persistent")
                            (L00_SourceSolidity.Expr.literal
                              (L00_SourceSolidity.Literal.number "10")))
                          (L00_SourceSolidity.Expr.ident "scratch"))) ]) }
      , L00_SourceSolidity.ContractItem.function
          { name := some "readScratch"
            visibility := some Visibility.public_
            returns := [{ name := some "out", ty := Ty.uint 256 }]
            body :=
              some
                (L00_SourceSolidity.Stmt.returnValues
                  (some (L00_SourceSolidity.Expr.ident "scratch"))) }
      , L00_SourceSolidity.ContractItem.function
          { name := some "writeScratchThenRevert"
            visibility := some Visibility.public_
            params := [{ name := some "value", ty := Ty.uint 256 }]
            body :=
              some
                (L00_SourceSolidity.Stmt.block
                  [ L00_SourceSolidity.Stmt.expr
                      (L00_SourceSolidity.Expr.assign
                        (L00_SourceSolidity.Expr.ident "scratch")
                        AssignOp.assign
                        (L00_SourceSolidity.Expr.ident "value"))
                  , L00_SourceSolidity.Stmt.revertCall
                      (L00_SourceSolidity.Expr.call
                        (L00_SourceSolidity.Expr.ident "revert") []) ]) } ] }

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
      writeResult.state.transient == [] &&
      readResult.state.transient == [])

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
              state.transient == [])
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

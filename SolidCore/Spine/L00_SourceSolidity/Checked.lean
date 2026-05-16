import SolidCore.Spine.L00_SourceSolidity.TypeCheck

namespace SolidCore
namespace Spine
namespace L00_SourceSolidity
namespace TypeCheck

abbrev CoreContract := L00_SourceSolidity.Executable.CoreContract
abbrev CoreValue := L00_SourceSolidity.Executable.CoreValue
abbrev CoreState := L00_SourceSolidity.Executable.CoreState
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
              , { name := some "probe", ty := lowLevelCallReturnTy } ]
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
                  (some (L00_SourceSolidity.Expr.ident "scratch"))) } ] }

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

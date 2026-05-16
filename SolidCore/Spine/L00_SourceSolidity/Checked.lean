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
abbrev SourceUnitAst := L00_SourceSolidity.SourceUnit
abbrev SourceContractDecl := L00_SourceSolidity.ContractDecl

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

def checkSourceUnit (source : SourceUnitAst) :
    Except TypeError CheckedSourceUnit :=
  _root_.SolidCore.Spine.L00_SourceSolidity.TypeCheck.SourceUnit.check
    source

def checkSourceUnit? (source : SourceUnitAst) :
    Option CheckedSourceUnit :=
  Result.toOption (checkSourceUnit source)

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
  let checked ← checkSourceUnit? source
  fromChecked? checked

def fromSource (source : SourceUnitAst) :
    Except TypeError CheckedProgram := do
  let checked ← checkSourceUnit source
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

namespace CheckedSourceUnit

def toCoreContract? (checked : CheckedSourceUnit) (name : Name) :
    Option CoreContract := do
  let program ← CheckedProgram.fromChecked? checked
  CheckedProgram.toCoreContract? program name

def toCoreContract (checked : CheckedSourceUnit) (name : Name) :
    Except TypeError CoreContract := do
  let program ← CheckedProgram.fromChecked checked
  CheckedProgram.toCoreContract program name

def toCoreContracts? (checked : CheckedSourceUnit) :
    Option (List CoreContract) := do
  let program ← CheckedProgram.fromChecked? checked
  CheckedProgram.toCoreContracts? program

def toCoreContracts (checked : CheckedSourceUnit) :
    Except TypeError (List CoreContract) := do
  let program ← CheckedProgram.fromChecked checked
  CheckedProgram.toCoreContracts program

def constructContractFrom? (fuel : Nat) (checked : CheckedSourceUnit)
    (name : Name) (state : CoreState) (sender value : Word)
    (args : List CoreValue) : Option CoreCallResult := do
  let program ← CheckedProgram.fromChecked? checked
  CheckedProgram.constructContractFrom?
    fuel program name state sender value args

def constructContractFrom (fuel : Nat) (checked : CheckedSourceUnit)
    (name : Name) (state : CoreState) (sender value : Word)
    (args : List CoreValue) : Except TypeError CoreCallResult := do
  let program ← CheckedProgram.fromChecked checked
  CheckedProgram.constructContractFrom
    fuel program name state sender value args

def constructContract? (fuel : Nat) (checked : CheckedSourceUnit)
    (name : Name) (state : CoreState) (args : List CoreValue) :
    Option CoreCallResult := do
  let program ← CheckedProgram.fromChecked? checked
  CheckedProgram.constructContract? fuel program name state args

def constructContract (fuel : Nat) (checked : CheckedSourceUnit)
    (name : Name) (state : CoreState) (args : List CoreValue) :
    Except TypeError CoreCallResult := do
  let program ← CheckedProgram.fromChecked checked
  CheckedProgram.constructContract fuel program name state args

def callContract? (fuel : Nat) (checked : CheckedSourceUnit)
    (name : Name) (target : CallTarget) (state : CoreState)
    (args : List CoreValue) : Option CoreCallResult := do
  let program ← CheckedProgram.fromChecked? checked
  CheckedProgram.callContract? fuel program name target state args

def callContract (fuel : Nat) (checked : CheckedSourceUnit)
    (name : Name) (target : CallTarget) (state : CoreState)
    (args : List CoreValue) : Except TypeError CoreCallResult := do
  let program ← CheckedProgram.fromChecked checked
  CheckedProgram.callContract fuel program name target state args

def callContractTransaction? (fuel : Nat) (checked : CheckedSourceUnit)
    (name : Name) (target : CallTarget) (state : CoreState)
    (args : List CoreValue) : Option CoreCallResult := do
  let program ← CheckedProgram.fromChecked? checked
  CheckedProgram.callContractTransaction?
    fuel program name target state args

def callContractTransaction (fuel : Nat) (checked : CheckedSourceUnit)
    (name : Name) (target : CallTarget) (state : CoreState)
    (args : List CoreValue) : Except TypeError CoreCallResult := do
  let program ← CheckedProgram.fromChecked checked
  CheckedProgram.callContractTransaction
    fuel program name target state args

def coreFunction? (checked : CheckedSourceUnit)
    (name functionName : Name) : Option CoreFunctionDef := do
  let program ← CheckedProgram.fromChecked? checked
  CheckedProgram.coreFunction? program name functionName

def coreFunction (checked : CheckedSourceUnit)
    (name functionName : Name) : Except TypeError CoreFunctionDef := do
  let program ← CheckedProgram.fromChecked checked
  CheckedProgram.coreFunction program name functionName

def functionCalldata? (checked : CheckedSourceUnit)
    (name functionName : Name) (args : List CoreValue) :
    Option (List Byte) := do
  let program ← CheckedProgram.fromChecked? checked
  CheckedProgram.functionCalldata? program name functionName args

def functionCalldata (checked : CheckedSourceUnit)
    (name functionName : Name) (args : List CoreValue) :
    Except TypeError (List Byte) := do
  let program ← CheckedProgram.fromChecked checked
  CheckedProgram.functionCalldata program name functionName args

def callFunctionWithContext? (fuel : Nat)
    (checked : CheckedSourceUnit) (name functionName : Name)
    (context : SolidCore.Solidity.Source.Context)
    (state : CoreState) (args : List CoreValue) :
    Option CoreCallResult := do
  let program ← CheckedProgram.fromChecked? checked
  CheckedProgram.callFunctionWithContext?
    fuel program name functionName context state args

def callFunctionWithContext (fuel : Nat)
    (checked : CheckedSourceUnit) (name functionName : Name)
    (context : SolidCore.Solidity.Source.Context)
    (state : CoreState) (args : List CoreValue) :
    Except TypeError CoreCallResult := do
  let program ← CheckedProgram.fromChecked checked
  CheckedProgram.callFunctionWithContext
    fuel program name functionName context state args

def callCalldataFrom? (fuel : Nat) (checked : CheckedSourceUnit)
    (name : Name) (state : CoreState) (sender value : Word)
    (calldata : List Byte) : Option CoreAbiCallResult := do
  let program ← CheckedProgram.fromChecked? checked
  CheckedProgram.callCalldataFrom?
    fuel program name state sender value calldata

def callCalldataFrom (fuel : Nat) (checked : CheckedSourceUnit)
    (name : Name) (state : CoreState) (sender value : Word)
    (calldata : List Byte) : Except TypeError CoreAbiCallResult := do
  let program ← CheckedProgram.fromChecked checked
  CheckedProgram.callCalldataFrom
    fuel program name state sender value calldata

def callCalldata? (fuel : Nat) (checked : CheckedSourceUnit)
    (name : Name) (state : CoreState) (calldata : List Byte) :
    Option CoreAbiCallResult :=
  callCalldataFrom? fuel checked name state 0 0 calldata

def callCalldata (fuel : Nat) (checked : CheckedSourceUnit)
    (name : Name) (state : CoreState) (calldata : List Byte) :
    Except TypeError CoreAbiCallResult :=
  callCalldataFrom fuel checked name state 0 0 calldata

def callCalldataTransactionFrom? (fuel : Nat)
    (checked : CheckedSourceUnit) (name : Name)
    (state : CoreState) (sender value : Word) (calldata : List Byte) :
    Option CoreAbiCallResult := do
  let program ← CheckedProgram.fromChecked? checked
  CheckedProgram.callCalldataTransactionFrom?
    fuel program name state sender value calldata

def callCalldataTransactionFrom (fuel : Nat)
    (checked : CheckedSourceUnit) (name : Name)
    (state : CoreState) (sender value : Word) (calldata : List Byte) :
    Except TypeError CoreAbiCallResult := do
  let program ← CheckedProgram.fromChecked checked
  CheckedProgram.callCalldataTransactionFrom
    fuel program name state sender value calldata

def callCalldataTransaction? (fuel : Nat)
    (checked : CheckedSourceUnit) (name : Name)
    (state : CoreState) (calldata : List Byte) :
    Option CoreAbiCallResult :=
  callCalldataTransactionFrom? fuel checked name state 0 0 calldata

def callCalldataTransaction (fuel : Nat)
    (checked : CheckedSourceUnit) (name : Name)
    (state : CoreState) (calldata : List Byte) :
    Except TypeError CoreAbiCallResult :=
  callCalldataTransactionFrom fuel checked name state 0 0 calldata

end CheckedSourceUnit

namespace SourceUnit

def checked? (source : SourceUnitAst) :
    Option CheckedSourceUnit :=
  checkSourceUnit? source

def checkedProgram? (source : SourceUnitAst) :
    Option CheckedProgram :=
  CheckedProgram.fromSource? source

def checkedProgram (source : SourceUnitAst) :
    Except TypeError CheckedProgram :=
  CheckedProgram.fromSource source

def checkedToCoreContract? (source : SourceUnitAst)
    (name : Name) : Option CoreContract := do
  let program ← checkedProgram? source
  CheckedProgram.toCoreContract? program name

def checkedToCoreContract (source : SourceUnitAst)
    (name : Name) : Except TypeError CoreContract := do
  let program ← checkedProgram source
  CheckedProgram.toCoreContract program name

def checkedToCoreContracts? (source : SourceUnitAst) :
    Option (List CoreContract) := do
  let program ← checkedProgram? source
  CheckedProgram.toCoreContracts? program

def checkedToCoreContracts (source : SourceUnitAst) :
    Except TypeError (List CoreContract) := do
  let program ← checkedProgram source
  CheckedProgram.toCoreContracts program

def checkedConstructContractFrom? (fuel : Nat)
    (source : SourceUnitAst) (name : Name)
    (state : CoreState) (sender value : Word) (args : List CoreValue) :
    Option CoreCallResult := do
  let program ← checkedProgram? source
  CheckedProgram.constructContractFrom?
    fuel program name state sender value args

def checkedConstructContractFrom (fuel : Nat)
    (source : SourceUnitAst) (name : Name)
    (state : CoreState) (sender value : Word) (args : List CoreValue) :
    Except TypeError CoreCallResult := do
  let program ← checkedProgram source
  CheckedProgram.constructContractFrom
    fuel program name state sender value args

def checkedConstructContract? (fuel : Nat)
    (source : SourceUnitAst) (name : Name)
    (state : CoreState) (args : List CoreValue) :
    Option CoreCallResult := do
  let program ← checkedProgram? source
  CheckedProgram.constructContract? fuel program name state args

def checkedConstructContract (fuel : Nat)
    (source : SourceUnitAst) (name : Name)
    (state : CoreState) (args : List CoreValue) :
    Except TypeError CoreCallResult := do
  let program ← checkedProgram source
  CheckedProgram.constructContract fuel program name state args

def checkedCallContract? (fuel : Nat)
    (source : SourceUnitAst) (name : Name)
    (target : CallTarget) (state : CoreState) (args : List CoreValue) :
    Option CoreCallResult := do
  let program ← checkedProgram? source
  CheckedProgram.callContract? fuel program name target state args

def checkedCallContract (fuel : Nat)
    (source : SourceUnitAst) (name : Name)
    (target : CallTarget) (state : CoreState) (args : List CoreValue) :
    Except TypeError CoreCallResult := do
  let program ← checkedProgram source
  CheckedProgram.callContract fuel program name target state args

def checkedCallContractTransaction? (fuel : Nat)
    (source : SourceUnitAst) (name : Name)
    (target : CallTarget) (state : CoreState) (args : List CoreValue) :
    Option CoreCallResult := do
  let program ← checkedProgram? source
  CheckedProgram.callContractTransaction?
    fuel program name target state args

def checkedCallContractTransaction (fuel : Nat)
    (source : SourceUnitAst) (name : Name)
    (target : CallTarget) (state : CoreState) (args : List CoreValue) :
    Except TypeError CoreCallResult := do
  let program ← checkedProgram source
  CheckedProgram.callContractTransaction
    fuel program name target state args

def checkedCoreFunction? (source : SourceUnitAst)
    (name functionName : Name) : Option CoreFunctionDef := do
  let program ← checkedProgram? source
  CheckedProgram.coreFunction? program name functionName

def checkedCoreFunction (source : SourceUnitAst)
    (name functionName : Name) : Except TypeError CoreFunctionDef := do
  let program ← checkedProgram source
  CheckedProgram.coreFunction program name functionName

def checkedFunctionCalldata? (source : SourceUnitAst)
    (name functionName : Name) (args : List CoreValue) :
    Option (List Byte) := do
  let program ← checkedProgram? source
  CheckedProgram.functionCalldata? program name functionName args

def checkedFunctionCalldata (source : SourceUnitAst)
    (name functionName : Name) (args : List CoreValue) :
    Except TypeError (List Byte) := do
  let program ← checkedProgram source
  CheckedProgram.functionCalldata program name functionName args

def checkedCallFunctionWithContext? (fuel : Nat)
    (source : SourceUnitAst) (name functionName : Name)
    (context : SolidCore.Solidity.Source.Context)
    (state : CoreState) (args : List CoreValue) :
    Option CoreCallResult := do
  let program ← checkedProgram? source
  CheckedProgram.callFunctionWithContext?
    fuel program name functionName context state args

def checkedCallFunctionWithContext (fuel : Nat)
    (source : SourceUnitAst) (name functionName : Name)
    (context : SolidCore.Solidity.Source.Context)
    (state : CoreState) (args : List CoreValue) :
    Except TypeError CoreCallResult := do
  let program ← checkedProgram source
  CheckedProgram.callFunctionWithContext
    fuel program name functionName context state args

def checkedCallCalldataFrom? (fuel : Nat)
    (source : SourceUnitAst) (name : Name)
    (state : CoreState) (sender value : Word) (calldata : List Byte) :
    Option CoreAbiCallResult := do
  let program ← checkedProgram? source
  CheckedProgram.callCalldataFrom?
    fuel program name state sender value calldata

def checkedCallCalldataFrom (fuel : Nat)
    (source : SourceUnitAst) (name : Name)
    (state : CoreState) (sender value : Word) (calldata : List Byte) :
    Except TypeError CoreAbiCallResult := do
  let program ← checkedProgram source
  CheckedProgram.callCalldataFrom
    fuel program name state sender value calldata

def checkedCallCalldata? (fuel : Nat)
    (source : SourceUnitAst) (name : Name)
    (state : CoreState) (calldata : List Byte) :
    Option CoreAbiCallResult :=
  checkedCallCalldataFrom? fuel source name state 0 0 calldata

def checkedCallCalldata (fuel : Nat)
    (source : SourceUnitAst) (name : Name)
    (state : CoreState) (calldata : List Byte) :
    Except TypeError CoreAbiCallResult :=
  checkedCallCalldataFrom fuel source name state 0 0 calldata

def checkedCallCalldataTransactionFrom? (fuel : Nat)
    (source : SourceUnitAst) (name : Name)
    (state : CoreState) (sender value : Word) (calldata : List Byte) :
    Option CoreAbiCallResult := do
  let program ← checkedProgram? source
  CheckedProgram.callCalldataTransactionFrom?
    fuel program name state sender value calldata

def checkedCallCalldataTransactionFrom (fuel : Nat)
    (source : SourceUnitAst) (name : Name)
    (state : CoreState) (sender value : Word) (calldata : List Byte) :
    Except TypeError CoreAbiCallResult := do
  let program ← checkedProgram source
  CheckedProgram.callCalldataTransactionFrom
    fuel program name state sender value calldata

def checkedCallCalldataTransaction? (fuel : Nat)
    (source : SourceUnitAst) (name : Name)
    (state : CoreState) (calldata : List Byte) :
    Option CoreAbiCallResult :=
  checkedCallCalldataTransactionFrom? fuel source name state 0 0 calldata

def checkedCallCalldataTransaction (fuel : Nat)
    (source : SourceUnitAst) (name : Name)
    (state : CoreState) (calldata : List Byte) :
    Except TypeError CoreAbiCallResult :=
  checkedCallCalldataTransactionFrom
    fuel source name state 0 0 calldata

end SourceUnit

namespace ContractDecl

def sourceUnit (decl : SourceContractDecl) : SourceUnitAst :=
  { items := [L00_SourceSolidity.SourceItem.contract decl] }

def checked? (decl : SourceContractDecl) :
    Option CheckedSourceUnit :=
  SourceUnit.checked? (sourceUnit decl)

def checkedProgram? (decl : SourceContractDecl) :
    Option CheckedProgram :=
  SourceUnit.checkedProgram? (sourceUnit decl)

def checkedProgram (decl : SourceContractDecl) :
    Except TypeError CheckedProgram :=
  SourceUnit.checkedProgram (sourceUnit decl)

def checkedContract? (decl : SourceContractDecl) :
    Option CheckedContract := do
  let program ← checkedProgram? decl
  CheckedProgram.contract? program decl.name

def checkedContract (decl : SourceContractDecl) :
    Except TypeError CheckedContract := do
  let program ← checkedProgram decl
  CheckedProgram.contract program decl.name

def checkedToCore? (decl : SourceContractDecl) :
    Option CoreContract := do
  let contract ← checkedContract? decl
  some contract.core

def checkedToCore (decl : SourceContractDecl) :
    Except TypeError CoreContract := do
  let contract ← checkedContract decl
  Except.ok contract.core

def checkedConstructFrom? (fuel : Nat)
    (decl : SourceContractDecl) (state : CoreState)
    (sender value : Word) (args : List CoreValue) :
    Option CoreCallResult := do
  let contract ← checkedContract? decl
  CheckedContract.constructFrom? fuel contract state sender value args

def checkedConstructFrom (fuel : Nat)
    (decl : SourceContractDecl) (state : CoreState)
    (sender value : Word) (args : List CoreValue) :
    Except TypeError CoreCallResult := do
  let contract ← checkedContract decl
  CheckedContract.constructFrom fuel contract state sender value args

def checkedConstruct? (fuel : Nat)
    (decl : SourceContractDecl) (state : CoreState)
    (args : List CoreValue) : Option CoreCallResult := do
  let contract ← checkedContract? decl
  CheckedContract.construct? fuel contract state args

def checkedConstruct (fuel : Nat)
    (decl : SourceContractDecl) (state : CoreState)
    (args : List CoreValue) : Except TypeError CoreCallResult := do
  let contract ← checkedContract decl
  CheckedContract.construct fuel contract state args

def checkedCall? (fuel : Nat)
    (decl : SourceContractDecl) (target : CallTarget)
    (state : CoreState) (args : List CoreValue) : Option CoreCallResult := do
  let contract ← checkedContract? decl
  CheckedContract.call? fuel contract target state args

def checkedCall (fuel : Nat)
    (decl : SourceContractDecl) (target : CallTarget)
    (state : CoreState) (args : List CoreValue) :
    Except TypeError CoreCallResult := do
  let contract ← checkedContract decl
  CheckedContract.call fuel contract target state args

def checkedCallTransaction? (fuel : Nat)
    (decl : SourceContractDecl) (target : CallTarget)
    (state : CoreState) (args : List CoreValue) : Option CoreCallResult := do
  let contract ← checkedContract? decl
  CheckedContract.callTransaction? fuel contract target state args

def checkedCallTransaction (fuel : Nat)
    (decl : SourceContractDecl) (target : CallTarget)
    (state : CoreState) (args : List CoreValue) :
    Except TypeError CoreCallResult := do
  let contract ← checkedContract decl
  CheckedContract.callTransaction fuel contract target state args

def checkedCoreFunction? (decl : SourceContractDecl)
    (functionName : Name) : Option CoreFunctionDef := do
  let contract ← checkedContract? decl
  CheckedContract.coreFunction? contract functionName

def checkedCoreFunction (decl : SourceContractDecl)
    (functionName : Name) : Except TypeError CoreFunctionDef := do
  let contract ← checkedContract decl
  CheckedContract.coreFunction contract functionName

def checkedFunctionCalldata? (decl : SourceContractDecl)
    (functionName : Name) (args : List CoreValue) :
    Option (List Byte) := do
  let contract ← checkedContract? decl
  CheckedContract.functionCalldata? contract functionName args

def checkedFunctionCalldata (decl : SourceContractDecl)
    (functionName : Name) (args : List CoreValue) :
    Except TypeError (List Byte) := do
  let contract ← checkedContract decl
  CheckedContract.functionCalldata contract functionName args

def checkedCallFunctionWithContext? (fuel : Nat)
    (decl : SourceContractDecl) (functionName : Name)
    (context : SolidCore.Solidity.Source.Context)
    (state : CoreState) (args : List CoreValue) :
    Option CoreCallResult := do
  let contract ← checkedContract? decl
  CheckedContract.callFunctionWithContext?
    fuel contract functionName context state args

def checkedCallFunctionWithContext (fuel : Nat)
    (decl : SourceContractDecl) (functionName : Name)
    (context : SolidCore.Solidity.Source.Context)
    (state : CoreState) (args : List CoreValue) :
    Except TypeError CoreCallResult := do
  let contract ← checkedContract decl
  CheckedContract.callFunctionWithContext
    fuel contract functionName context state args

def checkedCallCalldataFrom? (fuel : Nat)
    (decl : SourceContractDecl) (state : CoreState)
    (sender value : Word) (calldata : List Byte) :
    Option CoreAbiCallResult := do
  let contract ← checkedContract? decl
  CheckedContract.callCalldataFrom?
    fuel contract state sender value calldata

def checkedCallCalldataFrom (fuel : Nat)
    (decl : SourceContractDecl) (state : CoreState)
    (sender value : Word) (calldata : List Byte) :
    Except TypeError CoreAbiCallResult := do
  let contract ← checkedContract decl
  CheckedContract.callCalldataFrom
    fuel contract state sender value calldata

def checkedCallCalldata? (fuel : Nat)
    (decl : SourceContractDecl) (state : CoreState)
    (calldata : List Byte) : Option CoreAbiCallResult :=
  checkedCallCalldataFrom? fuel decl state 0 0 calldata

def checkedCallCalldata (fuel : Nat)
    (decl : SourceContractDecl) (state : CoreState)
    (calldata : List Byte) : Except TypeError CoreAbiCallResult :=
  checkedCallCalldataFrom fuel decl state 0 0 calldata

def checkedCallCalldataTransactionFrom? (fuel : Nat)
    (decl : SourceContractDecl) (state : CoreState)
    (sender value : Word) (calldata : List Byte) :
    Option CoreAbiCallResult := do
  let contract ← checkedContract? decl
  CheckedContract.callCalldataTransactionFrom?
    fuel contract state sender value calldata

def checkedCallCalldataTransactionFrom (fuel : Nat)
    (decl : SourceContractDecl) (state : CoreState)
    (sender value : Word) (calldata : List Byte) :
    Except TypeError CoreAbiCallResult := do
  let contract ← checkedContract decl
  CheckedContract.callCalldataTransactionFrom
    fuel contract state sender value calldata

def checkedCallCalldataTransaction? (fuel : Nat)
    (decl : SourceContractDecl) (state : CoreState)
    (calldata : List Byte) : Option CoreAbiCallResult :=
  checkedCallCalldataTransactionFrom?
    fuel decl state 0 0 calldata

def checkedCallCalldataTransaction (fuel : Nat)
    (decl : SourceContractDecl) (state : CoreState)
    (calldata : List Byte) : Except TypeError CoreAbiCallResult :=
  checkedCallCalldataTransactionFrom
    fuel decl state 0 0 calldata

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

def checkedAbiEncodeValues
    (tys : List SolidCore.Solidity.Source.Ty)
    (values : List CoreValue) : Except TypeError (List Byte) :=
  optionToExcept "ABI encode values"
    (SolidCore.Solidity.Source.ABI.encodeValues? tys values)

def checkedProgramCommonLayerMatches : Except TypeError Bool := do
  let program ← SourceUnit.checkedProgram simpleSource
  let _core ← CheckedProgram.toCoreContract program "C"
  let function ← CheckedProgram.coreFunction program "C" "f"
  let directResult ←
    CheckedProgram.callContract 16 program "C"
      (SolidCore.Solidity.Source.CallTarget.name "f")
      SolidCore.Solidity.Source.State.empty []
  let contract ← CheckedProgram.contract program "C"
  let contractResult ←
    CheckedContract.call 16 contract
      (SolidCore.Solidity.Source.CallTarget.name "f")
      SolidCore.Solidity.Source.State.empty []
  let functionResult ←
    CheckedProgram.callFunctionWithContext 16 program "C" "f"
      contract.core.context
      SolidCore.Solidity.Source.State.empty []
  let calldata ←
    CheckedProgram.functionCalldata program "C" "f" []
  let abiResult ←
    CheckedProgram.callCalldata 16 program "C"
      SolidCore.Solidity.Source.State.empty calldata
  let abiValue ← checkedDecodeUint256 abiResult.output
  match directResult, contractResult, functionResult with
  | SolidCore.Solidity.Source.CallResult.returned _
      [SolidCore.Solidity.Source.Value.word direct],
    SolidCore.Solidity.Source.CallResult.returned _
      [SolidCore.Solidity.Source.Value.word viaContract],
    SolidCore.Solidity.Source.CallResult.returned _
      [SolidCore.Solidity.Source.Value.word viaFunction] =>
      Except.ok
        (direct == 7 &&
          viaContract == 7 &&
          viaFunction == 7 &&
          abiResult.success &&
          abiValue == 7 &&
          function.name == some "f")
  | _, _, _ => Except.ok false

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

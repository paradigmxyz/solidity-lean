import SolidCore.Solidity.TypeCheck

namespace SolidCore
namespace Solidity
namespace TypeCheck

abbrev CoreContract := Solidity.Executable.CoreContract
abbrev CoreValue := Solidity.Executable.CoreValue
abbrev CoreState := Solidity.Executable.CoreState
abbrev CoreContext := Solidity.Executable.CoreContext
abbrev CoreCallResult := Solidity.Executable.CoreCallResult
abbrev CoreFunctionDef := Solidity.Executable.CoreFunctionDef
abbrev CoreAbiCallResult := SolidCore.Solidity.Source.ABI.AbiCallResult
abbrev CallTarget := SolidCore.Solidity.Source.CallTarget
abbrev SolI := SolidCore.Solidity.Source.SolI
abbrev ScriptedResponder := SolidCore.Solidity.Source.ScriptedResponder

def executableFailure (what : String) : TypeError :=
  TypeError.unsupported ("checked executable " ++ what)

def optionToExcept {α : Type} (what : String) : Option α ->
    Except TypeError α
  | some value => Except.ok value
  | none => Except.error (executableFailure what)

/-- Stage 2 — fold a tree entry (`Option (SolI α)`) under a scripted responder to
    the same `Except TypeError α` the `?`/`Except` adapters produce, but
    fail-closed: a `none` tree is static absence (`optionToExcept`), and an
    unmatched external request aborts with a diagnostic `TypeError`. -/
def foldResponder {α : Type} (responder : ScriptedResponder) (what : String) :
    Option (SolI α) → Except TypeError α
  | none => Except.error (executableFailure what)
  | some tree =>
      match SolidCore.Solidity.Source.SolI.runWith responder tree with
      | Except.ok a => Except.ok a
      | Except.error (SolidCore.Solidity.Source.ResponderFailure.solidity _) =>
          Except.error (executableFailure what)
      | Except.error (SolidCore.Solidity.Source.ResponderFailure.unmatched _) =>
          Except.error
            (TypeError.unsupported ("unmatched external request in " ++ what))

/-- Witness-facing fail-open fold: rows answer matched external requests,
    misses take the default (failure) answer — mirrors the retired context
    oracle exactly (see `SolI.runFailOpen`). The corpus manifest uses the
    fail-closed `foldResponder` instead. -/
def foldFailOpen {α : Type} (responder : ScriptedResponder) (what : String) :
    Option (SolI α) → Except TypeError α
  | none => Except.error (executableFailure what)
  | some tree =>
      match SolidCore.Solidity.Source.SolI.runFailOpen responder tree with
      | Except.ok a => Except.ok a
      | Except.error _ => Except.error (executableFailure what)

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
    Solidity.Executable.SourceUnit.resolveSourceTypesContextual?
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

def rawSource (program : CheckedProgram) : SourceUnitAst :=
  program.checked.source

def rawUsingDecls (program : CheckedProgram) :
    List Solidity.UsingDecl :=
  Solidity.Executable.SourceUnit.usingDecls
    (rawSource program)

def rawFreeFunctions (program : CheckedProgram) :
    List Solidity.FunctionDecl :=
  Solidity.Executable.SourceUnit.freeFunctions
    (rawSource program)

def rawFreeEvents (program : CheckedProgram) :
    List Solidity.EventDecl :=
  Solidity.Executable.SourceUnit.freeEvents
    (rawSource program)

def rawFreeErrors (program : CheckedProgram) :
    List Solidity.ErrorDecl :=
  Solidity.Executable.SourceUnit.freeErrors
    (rawSource program)

def rawFreeEnums (program : CheckedProgram) :
    List Solidity.EnumDecl :=
  Solidity.Executable.SourceUnit.freeEnums
    (rawSource program)

def rawFreeStructs (program : CheckedProgram) :
    List Solidity.StructDecl :=
  Solidity.Executable.SourceUnit.freeStructs
    (rawSource program)

def rawFreeConstants (program : CheckedProgram) :
    List Solidity.StateVarDecl :=
  Solidity.Executable.SourceUnit.freeConstants
    (rawSource program)

def rawFreeUserValueTypes (program : CheckedProgram) :
    List Solidity.UserValueTypeDecl :=
  Solidity.Executable.SourceUnit.freeUserValueTypes
    (rawSource program)

def rawContracts (program : CheckedProgram) :
    List SourceContractDecl :=
  Solidity.Executable.SourceUnit.contracts
    (rawSource program)

def findRawSourceContract? (program : CheckedProgram) (name : Name) :
    Option SourceContractDecl :=
  Solidity.Executable.SourceUnit.findContract?
    (rawSource program) name

def usingDecls (program : CheckedProgram) :
    List Solidity.UsingDecl :=
  Solidity.Executable.SourceUnit.usingDecls program.source

def freeFunctions (program : CheckedProgram) :
    List Solidity.FunctionDecl :=
  Solidity.Executable.SourceUnit.freeFunctions program.source

def freeEvents (program : CheckedProgram) :
    List Solidity.EventDecl :=
  Solidity.Executable.SourceUnit.freeEvents program.source

def freeErrors (program : CheckedProgram) :
    List Solidity.ErrorDecl :=
  Solidity.Executable.SourceUnit.freeErrors program.source

def freeConstants (program : CheckedProgram) :
    List Solidity.StateVarDecl :=
  Solidity.Executable.SourceUnit.freeConstants program.source

def contracts (program : CheckedProgram) :
    List SourceContractDecl :=
  Solidity.Executable.SourceUnit.contracts program.source

def findSourceContract? (program : CheckedProgram) (name : Name) :
    Option SourceContractDecl :=
  Solidity.Executable.SourceUnit.findContract?
    program.source name

def toCoreContractFor? (program : CheckedProgram)
    (decl : SourceContractDecl) : Option CoreContract := do
  let decl ← findRawSourceContract? program decl.name
  Solidity.Executable.ContractDecl.toCoreWithBasesAndUsing?
    (rawUsingDecls program) (rawFreeFunctions program)
    (rawFreeEvents program) (rawFreeErrors program)
    (rawFreeConstants program) (rawFreeUserValueTypes program)
    (rawFreeEnums program) (rawFreeStructs program)
    (rawContracts program) decl

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
  Solidity.Executable.mapOption
    (fun decl => toCoreContractFor? program decl)
    (contracts program)

def toCoreContracts (program : CheckedProgram) :
    Except TypeError (List CoreContract) :=
  optionToExcept "source-unit translation" (toCoreContracts? program)

def constructorFunctionFor? (program : CheckedProgram)
    (decl : SourceContractDecl) : Option CoreFunctionDef := do
  let decl ← findRawSourceContract? program decl.name
  Solidity.Executable.ContractDecl.constructorFunctionWithBasesAndSource?
    (rawUsingDecls program) (rawFreeFunctions program)
    (rawFreeEvents program) (rawFreeErrors program)
    (rawFreeConstants program) (rawFreeUserValueTypes program)
    (rawFreeEnums program) (rawFreeStructs program)
    (rawContracts program) decl

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
    fuel contract.core.table
    { contract.core.context with
      sender := sender
      value := value
      construction := true }
    constructor state args

def constructWithContext? (fuel : Nat) (contract : CheckedContract)
    (context : CoreContext) (state : CoreState) (sender value : Word)
    (args : List CoreValue) : Option CoreCallResult := do
  let constructor ←
    CheckedProgram.constructorFunctionFor? contract.program contract.decl
  SolidCore.Solidity.Source.FunctionDef.call?
    fuel contract.core.table
    { context with
      sender := sender
      value := value
      construction := true }
    constructor state args

def constructFrom (fuel : Nat) (contract : CheckedContract)
    (state : CoreState) (sender value : Word) (args : List CoreValue) :
    Except TypeError CoreCallResult :=
  optionToExcept ("constructor call " ++ contract.decl.name)
    (constructFrom? fuel contract state sender value args)

def constructWithContext (fuel : Nat) (contract : CheckedContract)
    (context : CoreContext) (state : CoreState) (sender value : Word)
    (args : List CoreValue) : Except TypeError CoreCallResult :=
  optionToExcept ("constructor call with context " ++ contract.decl.name)
    (constructWithContext? fuel contract context state sender value args)

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
    fuel contract.core.table context function state args

def callFunctionWithContext (fuel : Nat)
    (contract : CheckedContract) (functionName : Name)
    (context : SolidCore.Solidity.Source.Context)
    (state : CoreState) (args : List CoreValue) :
    Except TypeError CoreCallResult :=
  optionToExcept ("function call " ++ functionName)
    (callFunctionWithContext?
      fuel contract functionName context state args)

def callTargetWithContext? (fuel : Nat)
    (contract : CheckedContract) (target : CallTarget)
    (context : SolidCore.Solidity.Source.Context)
    (state : CoreState) (args : List CoreValue) :
    Option CoreCallResult :=
  match contract.core.resolveCallFunction? target args with
  | some function =>
      SolidCore.Solidity.Source.FunctionDef.call?
        fuel contract.core.table context function state args
  | none => none

def callTargetWithContext (fuel : Nat)
    (contract : CheckedContract) (target : CallTarget)
    (context : SolidCore.Solidity.Source.Context)
    (state : CoreState) (args : List CoreValue) :
    Except TypeError CoreCallResult :=
  optionToExcept ("function call target")
    (callTargetWithContext?
      fuel contract target context state args)

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

def callCalldataAtFromWithContext? (fuel : Nat)
    (contract : CheckedContract) (context : CoreContext)
    (state : CoreState) (self sender value : Word)
    (calldata : List Byte) : Option CoreAbiCallResult :=
  SolidCore.Solidity.Source.ABI.Contract.callCalldataAtFromWithContext?
    fuel contract.core context state self sender value calldata

def callCalldataAtFromWithContext (fuel : Nat)
    (contract : CheckedContract) (context : CoreContext)
    (state : CoreState) (self sender value : Word)
    (calldata : List Byte) : Except TypeError CoreAbiCallResult :=
  optionToExcept ("ABI calldata call with context " ++ contract.decl.name)
    (callCalldataAtFromWithContext?
      fuel contract context state self sender value calldata)

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

/-! ### Stage 1e — `SolI`-tree-returning twins of the checked entry points.

Additive: the `?`/`Except TypeError` entries above are unchanged (they already
fold at `FunctionDef.call?`).  These twins return the execution as an
interaction tree for the manifest to consume at stage 3. -/

def constructFromTree (fuel : Nat) (contract : CheckedContract)
    (state : CoreState) (sender value : Word) (args : List CoreValue) :
    Option (SolI CoreCallResult) := do
  let constructor ←
    CheckedProgram.constructorFunctionFor? contract.program contract.decl
  SolidCore.Solidity.Source.FunctionDef.call
    fuel contract.core.table
    { contract.core.context with
      sender := sender
      value := value
      construction := true }
    constructor state args

def constructWithContextTree (fuel : Nat) (contract : CheckedContract)
    (context : CoreContext) (state : CoreState) (sender value : Word)
    (args : List CoreValue) : Option (SolI CoreCallResult) := do
  let constructor ←
    CheckedProgram.constructorFunctionFor? contract.program contract.decl
  SolidCore.Solidity.Source.FunctionDef.call
    fuel contract.core.table
    { context with
      sender := sender
      value := value
      construction := true }
    constructor state args

def constructTree (fuel : Nat) (contract : CheckedContract)
    (state : CoreState) (args : List CoreValue) :
    Option (SolI CoreCallResult) :=
  constructFromTree fuel contract state 0 0 args

def callTree (fuel : Nat) (contract : CheckedContract)
    (target : CallTarget) (state : CoreState)
    (args : List CoreValue) : Option (SolI CoreCallResult) :=
  SolidCore.Solidity.Source.Contract.call
    fuel contract.core target state args

def callTransactionTree (fuel : Nat) (contract : CheckedContract)
    (target : CallTarget) (state : CoreState)
    (args : List CoreValue) : Option (SolI CoreCallResult) :=
  SolidCore.Solidity.Source.Contract.callTransaction
    fuel contract.core target state args

def callFunctionWithContextTree (fuel : Nat)
    (contract : CheckedContract) (functionName : Name)
    (context : SolidCore.Solidity.Source.Context)
    (state : CoreState) (args : List CoreValue) :
    Option (SolI CoreCallResult) := do
  let function ← coreFunction? contract functionName
  SolidCore.Solidity.Source.FunctionDef.call
    fuel contract.core.table context function state args

def callTargetWithContextTree (fuel : Nat)
    (contract : CheckedContract) (target : CallTarget)
    (context : SolidCore.Solidity.Source.Context)
    (state : CoreState) (args : List CoreValue) :
    Option (SolI CoreCallResult) :=
  match contract.core.resolveCallFunction? target args with
  | some function =>
      SolidCore.Solidity.Source.FunctionDef.call
        fuel contract.core.table context function state args
  | none => none

def callCalldataFromTree (fuel : Nat) (contract : CheckedContract)
    (state : CoreState) (sender value : Word) (calldata : List Byte) :
    Option (SolI CoreAbiCallResult) :=
  SolidCore.Solidity.Source.ABI.Contract.callCalldataFrom
    fuel contract.core state sender value calldata

def callCalldataAtFromTree (fuel : Nat) (contract : CheckedContract)
    (state : CoreState) (self sender value : Word)
    (calldata : List Byte) : Option (SolI CoreAbiCallResult) :=
  SolidCore.Solidity.Source.ABI.Contract.callCalldataAtFrom
    fuel contract.core state self sender value calldata

def callCalldataAtFromWithContextTree (fuel : Nat)
    (contract : CheckedContract) (context : CoreContext)
    (state : CoreState) (self sender value : Word)
    (calldata : List Byte) : Option (SolI CoreAbiCallResult) :=
  SolidCore.Solidity.Source.ABI.Contract.callCalldataAtFromWithContext
    fuel contract.core context state self sender value calldata

def callCalldataAtTree (fuel : Nat) (contract : CheckedContract)
    (state : CoreState) (self : Word) (calldata : List Byte) :
    Option (SolI CoreAbiCallResult) :=
  callCalldataAtFromTree fuel contract state self 0 0 calldata

def callCalldataTree (fuel : Nat) (contract : CheckedContract)
    (state : CoreState) (calldata : List Byte) :
    Option (SolI CoreAbiCallResult) :=
  callCalldataFromTree fuel contract state 0 0 calldata

/-! ### Stage 2 — responder-folding twins of the checked entry points.

Each builds the interaction tree via the `*Tree` twin (from `context`) and folds
it under the explicit `responder`, fail-closed. The manifest switches to these
at stage 3 (the `context` no longer carries oracle rows then; the responder does
the answering). -/

def constructFromResponder (fuel : Nat) (contract : CheckedContract)
    (state : CoreState) (sender value : Word) (args : List CoreValue)
    (responder : ScriptedResponder) : Except TypeError CoreCallResult :=
  foldResponder responder ("constructor call " ++ contract.decl.name)
    (constructFromTree fuel contract state sender value args)

def constructWithContextResponder (fuel : Nat) (contract : CheckedContract)
    (context : CoreContext) (state : CoreState) (sender value : Word)
    (args : List CoreValue) (responder : ScriptedResponder) :
    Except TypeError CoreCallResult :=
  foldResponder responder ("constructor call with context " ++ contract.decl.name)
    (constructWithContextTree fuel contract context state sender value args)

def constructResponder (fuel : Nat) (contract : CheckedContract)
    (state : CoreState) (args : List CoreValue) (responder : ScriptedResponder) :
    Except TypeError CoreCallResult :=
  constructFromResponder fuel contract state 0 0 args responder

def callResponder (fuel : Nat) (contract : CheckedContract)
    (target : CallTarget) (state : CoreState) (args : List CoreValue)
    (responder : ScriptedResponder) : Except TypeError CoreCallResult :=
  foldResponder responder ("contract call " ++ contract.decl.name)
    (callTree fuel contract target state args)

def callTransactionResponder (fuel : Nat) (contract : CheckedContract)
    (target : CallTarget) (state : CoreState) (args : List CoreValue)
    (responder : ScriptedResponder) : Except TypeError CoreCallResult :=
  foldResponder responder ("contract transaction " ++ contract.decl.name)
    (callTransactionTree fuel contract target state args)

def callFunctionWithContextResponder (fuel : Nat)
    (contract : CheckedContract) (functionName : Name)
    (context : SolidCore.Solidity.Source.Context)
    (state : CoreState) (args : List CoreValue) (responder : ScriptedResponder) :
    Except TypeError CoreCallResult :=
  foldResponder responder ("function call " ++ functionName)
    (callFunctionWithContextTree fuel contract functionName context state args)

def callTargetWithContextResponder (fuel : Nat)
    (contract : CheckedContract) (target : CallTarget)
    (context : SolidCore.Solidity.Source.Context)
    (state : CoreState) (args : List CoreValue) (responder : ScriptedResponder) :
    Except TypeError CoreCallResult :=
  foldResponder responder "function call target"
    (callTargetWithContextTree fuel contract target context state args)

def callCalldataFromResponder (fuel : Nat) (contract : CheckedContract)
    (state : CoreState) (sender value : Word) (calldata : List Byte)
    (responder : ScriptedResponder) : Except TypeError CoreAbiCallResult :=
  foldResponder responder ("ABI calldata call " ++ contract.decl.name)
    (callCalldataFromTree fuel contract state sender value calldata)

def callCalldataAtFromResponder (fuel : Nat) (contract : CheckedContract)
    (state : CoreState) (self sender value : Word) (calldata : List Byte)
    (responder : ScriptedResponder) : Except TypeError CoreAbiCallResult :=
  foldResponder responder ("ABI calldata call " ++ contract.decl.name)
    (callCalldataAtFromTree fuel contract state self sender value calldata)

def callCalldataAtFromWithContextResponder (fuel : Nat)
    (contract : CheckedContract) (context : CoreContext)
    (state : CoreState) (self sender value : Word) (calldata : List Byte)
    (responder : ScriptedResponder) : Except TypeError CoreAbiCallResult :=
  foldResponder responder ("ABI calldata call with context " ++ contract.decl.name)
    (callCalldataAtFromWithContextTree
      fuel contract context state self sender value calldata)

def callCalldataAtResponder (fuel : Nat) (contract : CheckedContract)
    (state : CoreState) (self : Word) (calldata : List Byte)
    (responder : ScriptedResponder) : Except TypeError CoreAbiCallResult :=
  callCalldataAtFromResponder fuel contract state self 0 0 calldata responder

def callCalldataResponder (fuel : Nat) (contract : CheckedContract)
    (state : CoreState) (calldata : List Byte) (responder : ScriptedResponder) :
    Except TypeError CoreAbiCallResult :=
  callCalldataFromResponder fuel contract state 0 0 calldata responder

/-- Witness fail-open twin of `callFunctionWithContext` (responder after fuel;
    see `foldFailOpen`). -/
def callFunctionWithContextFailOpen (fuel : Nat)
    (responder : ScriptedResponder)
    (contract : CheckedContract) (functionName : Name)
    (context : SolidCore.Solidity.Source.Context)
    (state : CoreState) (args : List CoreValue) :
    Except TypeError CoreCallResult :=
  foldFailOpen responder ("function call " ++ functionName)
    (callFunctionWithContextTree fuel contract functionName context state args)

/-! ### Manifest wrappers (`*UnderResponder`) — fail-closed fold, responder
after fuel so the manifest's oracle rows sit where the old context rows did. -/

def callFunctionWithContextUnderResponder (fuel : Nat)
    (responder : ScriptedResponder)
    (contract : CheckedContract) (functionName : Name)
    (context : SolidCore.Solidity.Source.Context)
    (state : CoreState) (args : List CoreValue) :
    Except TypeError CoreCallResult :=
  callFunctionWithContextResponder
    fuel contract functionName context state args responder

def callTargetWithContextUnderResponder (fuel : Nat)
    (responder : ScriptedResponder)
    (contract : CheckedContract) (target : CallTarget)
    (context : SolidCore.Solidity.Source.Context)
    (state : CoreState) (args : List CoreValue) :
    Except TypeError CoreCallResult :=
  callTargetWithContextResponder
    fuel contract target context state args responder

def callCalldataAtFromWithContextUnderResponder (fuel : Nat)
    (responder : ScriptedResponder)
    (contract : CheckedContract) (context : CoreContext)
    (state : CoreState) (self sender value : Word) (calldata : List Byte) :
    Except TypeError CoreAbiCallResult :=
  callCalldataAtFromWithContextResponder
    fuel contract context state self sender value calldata responder

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

def constructContractWithContext? (fuel : Nat) (program : CheckedProgram)
    (name : Name) (context : CoreContext) (state : CoreState)
    (sender value : Word) (args : List CoreValue) :
    Option CoreCallResult := do
  let contract ← contract? program name
  CheckedContract.constructWithContext?
    fuel contract context state sender value args

def constructContractWithContext (fuel : Nat) (program : CheckedProgram)
    (name : Name) (context : CoreContext) (state : CoreState)
    (sender value : Word) (args : List CoreValue) :
    Except TypeError CoreCallResult := do
  let contract ← contract program name
  CheckedContract.constructWithContext
    fuel contract context state sender value args

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

/-! ### Stage 1e — program-level `SolI`-tree twins (additive). -/

def constructContractFromTree (fuel : Nat) (program : CheckedProgram)
    (name : Name) (state : CoreState) (sender value : Word)
    (args : List CoreValue) : Option (SolI CoreCallResult) := do
  let contract ← contract? program name
  CheckedContract.constructFromTree fuel contract state sender value args

def constructContractWithContextTree (fuel : Nat) (program : CheckedProgram)
    (name : Name) (context : CoreContext) (state : CoreState)
    (sender value : Word) (args : List CoreValue) :
    Option (SolI CoreCallResult) := do
  let contract ← contract? program name
  CheckedContract.constructWithContextTree
    fuel contract context state sender value args

def constructContractTree (fuel : Nat) (program : CheckedProgram)
    (name : Name) (state : CoreState) (args : List CoreValue) :
    Option (SolI CoreCallResult) :=
  constructContractFromTree fuel program name state 0 0 args

def callContractTree (fuel : Nat) (program : CheckedProgram)
    (name : Name) (target : CallTarget) (state : CoreState)
    (args : List CoreValue) : Option (SolI CoreCallResult) := do
  let contract ← contract? program name
  CheckedContract.callTree fuel contract target state args

def callFunctionWithContextTree (fuel : Nat)
    (program : CheckedProgram) (name functionName : Name)
    (context : SolidCore.Solidity.Source.Context)
    (state : CoreState) (args : List CoreValue) :
    Option (SolI CoreCallResult) := do
  let contract ← contract? program name
  CheckedContract.callFunctionWithContextTree
    fuel contract functionName context state args

def constructContractFromResponder (fuel : Nat) (program : CheckedProgram)
    (name : Name) (state : CoreState) (sender value : Word)
    (args : List CoreValue) (responder : ScriptedResponder) :
    Except TypeError CoreCallResult := do
  let contract ← contract program name
  CheckedContract.constructFromResponder
    fuel contract state sender value args responder

def constructContractWithContextResponder (fuel : Nat) (program : CheckedProgram)
    (name : Name) (context : CoreContext) (state : CoreState)
    (sender value : Word) (args : List CoreValue) (responder : ScriptedResponder) :
    Except TypeError CoreCallResult := do
  let contract ← contract program name
  CheckedContract.constructWithContextResponder
    fuel contract context state sender value args responder

def constructContractResponder (fuel : Nat) (program : CheckedProgram)
    (name : Name) (state : CoreState) (args : List CoreValue)
    (responder : ScriptedResponder) : Except TypeError CoreCallResult :=
  constructContractFromResponder fuel program name state 0 0 args responder

def callFunctionWithContextResponder (fuel : Nat)
    (program : CheckedProgram) (name functionName : Name)
    (context : SolidCore.Solidity.Source.Context)
    (state : CoreState) (args : List CoreValue) (responder : ScriptedResponder) :
    Except TypeError CoreCallResult := do
  let contract ← contract program name
  CheckedContract.callFunctionWithContextResponder
    fuel contract functionName context state args responder

/-- Witness fail-open twin (responder after fuel; see `foldFailOpen`). -/
def callFunctionWithContextFailOpen (fuel : Nat)
    (responder : ScriptedResponder)
    (program : CheckedProgram) (name functionName : Name)
    (context : SolidCore.Solidity.Source.Context)
    (state : CoreState) (args : List CoreValue) :
    Except TypeError CoreCallResult := do
  let contract ← contract program name
  CheckedContract.callFunctionWithContextFailOpen
    fuel responder contract functionName context state args

/-- Manifest wrapper — fail-closed fold, responder after fuel. -/
def constructContractWithContextUnderResponder (fuel : Nat)
    (responder : ScriptedResponder)
    (program : CheckedProgram) (name : Name) (context : CoreContext)
    (state : CoreState) (sender value : Word) (args : List CoreValue) :
    Except TypeError CoreCallResult :=
  constructContractWithContextResponder
    fuel program name context state sender value args responder

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

def constructContractWithContext? {α : Type} [CheckedInput α]
    (fuel : Nat) (input : α) (name : Name) (context : CoreContext)
    (state : CoreState) (sender value : Word) (args : List CoreValue) :
    Option CoreCallResult := do
  let checkedProgram ← program? input
  CheckedProgram.constructContractWithContext?
    fuel checkedProgram name context state sender value args

def constructContractWithContext {α : Type} [CheckedInput α]
    (fuel : Nat) (input : α) (name : Name) (context : CoreContext)
    (state : CoreState) (sender value : Word) (args : List CoreValue) :
    Except TypeError CoreCallResult := do
  let checkedProgram ← program input
  CheckedProgram.constructContractWithContext
    fuel checkedProgram name context state sender value args

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

/-- Witness fail-open twin (responder after fuel; see `foldFailOpen`). -/
def callFunctionWithContextFailOpen {α : Type} [CheckedInput α]
    (fuel : Nat) (responder : ScriptedResponder)
    (input : α) (name functionName : Name)
    (context : SolidCore.Solidity.Source.Context)
    (state : CoreState) (args : List CoreValue) :
    Except TypeError CoreCallResult := do
  let checkedProgram ← program input
  CheckedProgram.callFunctionWithContextFailOpen
    fuel responder checkedProgram name functionName context state args

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

/-- Witness fail-open twin (responder after fuel; see `foldFailOpen`). -/
def ownCallFunctionWithContextFailOpen {α : Type} [CheckedInput α]
    (fuel : Nat) (responder : ScriptedResponder)
    (input : α) (functionName : Name)
    (context : SolidCore.Solidity.Source.Context)
    (state : CoreState) (args : List CoreValue) :
    Except TypeError CoreCallResult := do
  let checkedContract ← ownContract input
  CheckedContract.callFunctionWithContextFailOpen
    fuel responder checkedContract functionName context state args

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

def ownCallCalldataAtFromWithContext? {α : Type} [CheckedInput α]
    (fuel : Nat) (input : α) (context : CoreContext)
    (state : CoreState) (self sender value : Word)
    (calldata : List Byte) : Option CoreAbiCallResult := do
  let checkedContract ← ownContract? input
  CheckedContract.callCalldataAtFromWithContext?
    fuel checkedContract context state self sender value calldata

def ownCallCalldataAtFromWithContext {α : Type} [CheckedInput α]
    (fuel : Nat) (input : α) (context : CoreContext)
    (state : CoreState) (self sender value : Word)
    (calldata : List Byte) : Except TypeError CoreAbiCallResult := do
  let checkedContract ← ownContract input
  CheckedContract.callCalldataAtFromWithContext
    fuel checkedContract context state self sender value calldata

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

def constructContractWithContext? (fuel : Nat) (checked : CheckedSourceUnit)
    (name : Name) (context : CoreContext) (state : CoreState)
    (sender value : Word) (args : List CoreValue) :
    Option CoreCallResult :=
  CheckedInput.constructContractWithContext?
    fuel checked name context state sender value args

def constructContractWithContext (fuel : Nat) (checked : CheckedSourceUnit)
    (name : Name) (context : CoreContext) (state : CoreState)
    (sender value : Word) (args : List CoreValue) :
    Except TypeError CoreCallResult :=
  CheckedInput.constructContractWithContext
    fuel checked name context state sender value args

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

/-- Witness fail-open twin (responder after fuel; see `foldFailOpen`). -/
def checkedCallFunctionWithContextFailOpen (fuel : Nat)
    (responder : ScriptedResponder)
    (source : SourceUnitAst) (name functionName : Name)
    (context : SolidCore.Solidity.Source.Context)
    (state : CoreState) (args : List CoreValue) :
    Except TypeError CoreCallResult :=
  CheckedInput.callFunctionWithContextFailOpen
    fuel responder source name functionName context state args

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

/-- Witness fail-open twin (responder after fuel; see `foldFailOpen`). -/
def checkedCallFunctionWithContextFailOpen (fuel : Nat)
    (responder : ScriptedResponder)
    (decl : SourceContractDecl) (functionName : Name)
    (context : SolidCore.Solidity.Source.Context)
    (state : CoreState) (args : List CoreValue) :
    Except TypeError CoreCallResult :=
  CheckedInput.ownCallFunctionWithContextFailOpen
    fuel responder decl functionName context state args

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


end TypeCheck
end Solidity
end SolidCore

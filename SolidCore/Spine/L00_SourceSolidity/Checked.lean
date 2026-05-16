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

end TypeCheck
end L00_SourceSolidity
end Spine
end SolidCore

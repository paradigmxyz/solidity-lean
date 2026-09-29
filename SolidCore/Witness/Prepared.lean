import SolidCore.Solidity.Checked

/-! Shared, immutable checked contracts for executable regression suites.
Preparation does not execute a constructor or retain a call's state. Each check
continues to supply its original state, context, fuel, arguments and expectation.
-/
namespace SolidCore.Solidity.Witness.Prepared
open SolidCore.Solidity.Source SolidCore.Solidity.TypeCheck

abbrev Contract := Except TypeError CheckedContract

def call (fuel : Nat) (contract : Contract) (target : SolidCore.Solidity.Source.CallTarget)
    (state : CoreState) (args : List CoreValue) : Except TypeError CoreCallResult := do
  CheckedContract.call fuel (← contract) target state args

def construct (fuel : Nat) (contract : Contract) (state : CoreState)
    (args : List CoreValue) : Except TypeError CoreCallResult := do
  CheckedContract.construct fuel (← contract) state args

/-- Sharing preparation leaves the existing call entry point unchanged. -/
theorem call_ownContract (fuel : Nat) (decl : SourceContractDecl)
    (target : SolidCore.Solidity.Source.CallTarget) (state : CoreState) (args : List CoreValue) :
    call fuel (CheckedInput.ownContract decl) target state args =
      CheckedInput.ownCall fuel decl target state args := by
  rfl

def wordMatches (fuel : Nat) (contract : Contract) (functionName : Name)
    (state : CoreState) (args : List CoreValue) (expected : Word) :
    Except TypeError Bool := do
  match ← call fuel contract (.name functionName) state args with
  | .returned _ [value] =>
    match value.asWord? with
    | some word => pure (wordEq word expected)
    | none => pure false
  | _ => pure false

def panicMatches (fuel : Nat) (contract : Contract) (functionName : Name)
    (state : CoreState) (args : List CoreValue) (expected : Word) :
    Except TypeError Bool := do
  match ← call fuel contract (.name functionName) state args with
  | .reverted _ (.panic code) => pure (wordEq code expected)
  | _ => pure false

def bytesMatches (fuel : Nat) (contract : Contract) (functionName : Name)
    (state : CoreState) (args : List CoreValue) (expected : List Byte) :
    Except TypeError Bool := do
  match ← call fuel contract (.name functionName) state args with
  | .returned _ [.bytes bytes] => pure (bytes == expected)
  | _ => pure false

/-- Named runtime assertions retain useful diagnostics while sharing one evaluator. -/
def assertChecks (checks : List (String × Bool)) : IO Unit := do
  let failed := checks.filterMap fun (label, ok) => if ok then none else some label
  unless failed.isEmpty do
    throw (IO.userError ("regression checks failed: " ++ String.intercalate ", " failed))

end SolidCore.Solidity.Witness.Prepared

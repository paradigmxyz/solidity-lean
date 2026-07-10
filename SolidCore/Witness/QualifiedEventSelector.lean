import SolidCore.Solidity.Checked
import SolidCore.Witness.Checked

set_option maxHeartbeats 8000000

/-!
#137 `.selector` — type-qualified EVENT selector witnesses.

`Event.selector` in Solidity is the 32-byte topic0. A type-qualified
`Base.Ev.selector` / `L.Ping.selector` used to be OVER-REJECTED by the model
(the qualified-selector typecheck fallback `contractSelectorMemberTy?` omitted
events), and the event-selector lowering was by-name (a same-name library event
collision would mis-target). The fix accepts event `.selector` (bytes32) and
resolves it path-qualified (`Contract.Ev` key over all contracts/libraries).

`#eval`-confirmed booleans pinned with `#guard`; real-EVM Forge ground truth in
`tests/forge-harness/qualified-event-selector`.
-/

open SolidCore.Solidity.Source
open SolidCore.Solidity

namespace SolidCore
namespace Solidity
namespace Witness
namespace QualifiedEventSelector

def importedSourceName : String := "/private/tmp/claude-502/-Users-dan-Projects-solid-core-spine/a31e5b4d-dfd9-4ad6-82fd-d3eba32b9252/scratchpad/wt-qual-collision/tests/forge-harness/qualified-event-selector/src/QualifiedEventSelector.sol"

def importedContractDecl0 : ContractDecl :=
{ kind := ContractKind.library
  name := "L"
  abstract := false
  bases := []
  items := [(ContractItem.eventDecl
  { name := "Ping",
    params := [{ name := some "x", ty := Ty.uint 256, indexed := false }],
    anonymous := false })] }

def importedContractDecl1 : ContractDecl :=
{ kind := ContractKind.contract
  name := "Base"
  abstract := false
  bases := []
  items := [(ContractItem.eventDecl
  { name := "Ev",
    params := [{ name := some "x", ty := Ty.uint 256, indexed := false }],
    anonymous := false })] }

def importedContractDecl2 : ContractDecl :=
{ kind := ContractKind.contract
  name := "QualifiedEventSelectorTarget"
  abstract := false
  bases := [{ base := { segments := ["Base"] }, args := [] }]
  items := [(ContractItem.eventDecl
  { name := "Ping",
    params := [{ name := some "a", ty := Ty.address false, indexed := false }],
    anonymous := false }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "ownEv",
    visibility := some Visibility.external_,
    mutability := StateMutability.pure,
    params := [],
    returns := [{ name := none, ty := Ty.bytesN 32, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.member (Expr.ident "Ev") "selector"))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "ownPing",
    visibility := some Visibility.external_,
    mutability := StateMutability.pure,
    params := [],
    returns := [{ name := none, ty := Ty.bytesN 32, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.member (Expr.ident "Ping") "selector"))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "baseEv",
    visibility := some Visibility.external_,
    mutability := StateMutability.pure,
    params := [],
    returns := [{ name := none, ty := Ty.bytesN 32, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.member (Expr.member (Expr.typeName (Ty.user ({ segments := ["Base"] }))) "Ev") "selector"))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "libPing",
    visibility := some Visibility.external_,
    mutability := StateMutability.pure,
    params := [],
    returns := [{ name := none, ty := Ty.bytesN 32, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.member (Expr.member (Expr.typeName (Ty.user ({ segments := ["L"] }))) "Ping") "selector"))]) })] }

def importedContract : ContractDecl :=
  importedContractDecl2

def importedContracts : List ContractDecl :=
  [importedContractDecl0, importedContractDecl1, importedContractDecl2]

def importedSourceUnit : SourceUnit :=
  { items := [SourceItem.pragma "solidity" "^0.8.35", SourceItem.contract importedContractDecl0, SourceItem.contract importedContractDecl1, SourceItem.contract importedContractDecl2] }

def importedContractAccepted : Bool :=
  TypeCheck.Result.isOk (TypeCheck.TypecheckedInput.checkedSourceUnit importedSourceUnit)

-- (source unit above; witnesses below)

open SolidCore.Solidity

private def selectorWordOf (fn : String) : Option SolidCore.Solidity.Source.Word :=
  match SolidCore.Solidity.TypeCheck.CheckedInput.program importedSourceUnit with
  | Except.ok program =>
      match SolidCore.Solidity.TypeCheck.CheckedProgram.contract program
              "QualifiedEventSelectorTarget" with
      | Except.ok c =>
          match SolidCore.Solidity.TypeCheck.CheckedContract.functionCalldata c fn [] with
          | Except.ok cd =>
              match SolidCore.Solidity.TypeCheck.CheckedContract.callCalldata 64 c
                      SolidCore.Solidity.Source.State.empty cd with
              | Except.ok r =>
                  if r.success then some (SolidCore.Solidity.Source.bytesToWordBE r.output)
                  else none
              | _ => none
          | _ => none
      | _ => none
  | _ => none

private def topic0Of (sig : String) : SolidCore.Solidity.Source.Word :=
  SolidCore.Solidity.Source.Keccak.digestWord sig

def qualifiedEventSelectorAccepted : Bool := importedContractAccepted
def ownEvSelectorUnchanged : Bool :=
  selectorWordOf "ownEv" == some (topic0Of "Ev(uint256)")
def ownPingSelectorUnchanged : Bool :=
  selectorWordOf "ownPing" == some (topic0Of "Ping(address)")
def baseEvSelectorResolves : Bool :=
  selectorWordOf "baseEv" == some (topic0Of "Ev(uint256)")
def libPingSelectorResolvesLibrary : Bool :=
  selectorWordOf "libPing" == some (topic0Of "Ping(uint256)")

#guard qualifiedEventSelectorAccepted
#guard ownEvSelectorUnchanged
#guard ownPingSelectorUnchanged
#guard baseEvSelectorResolves
#guard libPingSelectorResolvesLibrary

end QualifiedEventSelector
end Witness
end Solidity
end SolidCore

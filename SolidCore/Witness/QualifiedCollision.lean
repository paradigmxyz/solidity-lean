import SolidCore.Solidity.Checked
import SolidCore.Witness.Checked

/-!
#136/#137 QUALIFIED-COLLISION witnesses.

A type-qualified custom-error revert `revert L.E(...)` and event emit
`emit L.Ev(...)` where the contract ALSO declares its own same-name error/event
with a DIFFERENT signature.  solc encodes the LIBRARY member (its selector /
topic0), NOT the contract's; a library-qualified emit/revert with no colliding
contract member is likewise accepted and resolves to the library member.

The model formerly lowered a qualified emit/revert to the BARE name and resolved
first-match against a by-name runtime table — mis-targeting on a collision
(wrong topic0 / selector) or over-rejecting the no-collision library event.  The
fix lowers a type-qualified emit/revert to a `.`-joined key (mirroring qualified
constants) and registers matching keyed runtime entries whose topic/selector are
the DECLARING scope's, so the runtime emits the correct value.

`#eval`-confirmed booleans pinned with `#guard` (the project avoids
`native_decide`, and `rfl` cannot reduce the fuel-recursive interpreter).
Real-EVM Forge ground truth is in `tests/forge-harness/qualified-collision`.
-/

open SolidCore.Solidity.Source
open SolidCore.Solidity

namespace SolidCore
namespace Solidity
namespace Witness
namespace QualifiedCollision

def importedSourceName : String := "/private/tmp/claude-502/-Users-dan-Projects-solid-core-spine/a31e5b4d-dfd9-4ad6-82fd-d3eba32b9252/scratchpad/wt-qual-collision/tests/forge-harness/qualified-collision/src/QualifiedCollision.sol"

def importedContractDecl0 : ContractDecl :=
{ kind := ContractKind.library
  name := "L"
  abstract := false
  bases := []
  items := [(ContractItem.eventDecl
  { name := "Ev",
    params := [{ name := some "x", ty := Ty.uint 8, indexed := false }],
    anonymous := false }), (ContractItem.errorDecl
  { name := "E",
    params := [{ name := some "x", ty := Ty.uint 8, location := none }] })] }

def importedContractDecl1 : ContractDecl :=
{ kind := ContractKind.library
  name := "N"
  abstract := false
  bases := []
  items := [(ContractItem.eventDecl
  { name := "Ping",
    params := [{ name := some "p", ty := Ty.uint 64, indexed := false }],
    anonymous := false }), (ContractItem.errorDecl
  { name := "Bad",
    params := [{ name := some "b", ty := Ty.uint 64, location := none }] })] }

def importedContractDecl2 : ContractDecl :=
{ kind := ContractKind.contract
  name := "QualifiedCollisionTarget"
  abstract := false
  bases := []
  items := [(ContractItem.eventDecl
  { name := "Ev",
    params := [{ name := some "x", ty := Ty.uint 256, indexed := false }],
    anonymous := false }), (ContractItem.errorDecl
  { name := "E",
    params := [{ name := some "x", ty := Ty.uint 256, location := none }] }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "emitLib",
    visibility := some Visibility.external_,
    mutability := StateMutability.nonpayable,
    params := [],
    returns := [],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.emitEvent (Expr.call (Expr.member (Expr.typeName (Ty.user ({ segments := ["L"] }))) "Ev") [Arg.positional (Expr.literal (Literal.number "5"))])]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "revertLib",
    visibility := some Visibility.external_,
    mutability := StateMutability.nonpayable,
    params := [],
    returns := [],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.revertCall (Expr.call (Expr.member (Expr.typeName (Ty.user ({ segments := ["L"] }))) "E") [Arg.positional (Expr.literal (Literal.number "5"))])]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "emitOwn",
    visibility := some Visibility.external_,
    mutability := StateMutability.nonpayable,
    params := [],
    returns := [],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.emitEvent (Expr.call (Expr.ident "Ev") [Arg.positional (Expr.literal (Literal.number "9"))])]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "revertOwn",
    visibility := some Visibility.external_,
    mutability := StateMutability.nonpayable,
    params := [],
    returns := [],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.revertCall (Expr.call (Expr.ident "E") [Arg.positional (Expr.literal (Literal.number "9"))])]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "emitLibNoCollision",
    visibility := some Visibility.external_,
    mutability := StateMutability.nonpayable,
    params := [],
    returns := [],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.emitEvent (Expr.call (Expr.member (Expr.typeName (Ty.user ({ segments := ["N"] }))) "Ping") [Arg.positional (Expr.literal (Literal.number "3"))])]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "revertLibNoCollision",
    visibility := some Visibility.external_,
    mutability := StateMutability.nonpayable,
    params := [],
    returns := [],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.revertCall (Expr.call (Expr.member (Expr.typeName (Ty.user ({ segments := ["N"] }))) "Bad") [Arg.positional (Expr.literal (Literal.number "3"))])]) })] }

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

private def topic0Of (sig : String) : Word :=
  SolidCore.Solidity.Source.Keccak.digestWord sig

private def selBytes (sig : String) : List SolidCore.Solidity.Source.Byte :=
  SolidCore.Solidity.Source.ABI.encodeSelector
    (SolidCore.Solidity.Source.ABI.selectorFromSignature sig)

/-- topic0 of the single event emitted by external `fn`, if exactly one. -/
private def emitTopic0? (fn : String) : Option Word :=
  match
    SolidCore.Solidity.TypeCheck.CheckedInput.callContract 64 importedSourceUnit
      "QualifiedCollisionTarget"
      (SolidCore.Solidity.Source.CallTarget.name fn)
      SolidCore.Solidity.Source.State.empty [] with
  | Except.ok (SolidCore.Solidity.Source.CallResult.returned state []) =>
      match state.events with
      | [event] => event.topics.head?
      | _ => none
  | _ => none

/-- ABI selector (first 4 output bytes) of the revert produced by external `fn`. -/
private def revertSelector? (fn : String) : Option (List SolidCore.Solidity.Source.Byte) :=
  match SolidCore.Solidity.TypeCheck.CheckedInput.program importedSourceUnit with
  | Except.ok program =>
      match SolidCore.Solidity.TypeCheck.CheckedProgram.contract program
              "QualifiedCollisionTarget" with
      | Except.ok c =>
          match SolidCore.Solidity.TypeCheck.CheckedContract.functionCalldata c fn [] with
          | Except.ok cd =>
              match SolidCore.Solidity.TypeCheck.CheckedContract.callCalldata 64 c
                      SolidCore.Solidity.Source.State.empty cd with
              | Except.ok r => if r.success then none else some (r.output.take 4)
              | _ => none
          | _ => none
      | _ => none
  | _ => none

-- The whole unit (library L + N + contract, colliding names) is ACCEPTED.
def qualifiedCollisionAccepted : Bool := importedContractAccepted

-- Event side (#137): library-qualified emit resolves to the LIBRARY topic0 even
-- under a name collision; the bare (own) event is unchanged; the no-collision
-- library event is accepted and resolves to the library topic0.
def emitLibResolvesLibraryTopic : Bool :=
  emitTopic0? "emitLib" == some (topic0Of "Ev(uint8)")
def emitOwnUnchanged : Bool :=
  emitTopic0? "emitOwn" == some (topic0Of "Ev(uint256)")
def emitLibNoCollisionAccepted : Bool :=
  emitTopic0? "emitLibNoCollision" == some (topic0Of "Ping(uint64)")

-- Error side (#136): library-qualified revert encodes the LIBRARY selector even
-- under a name collision; the bare (own) error is unchanged; the no-collision
-- library error resolves to the library selector.
def revertLibResolvesLibrarySelector : Bool :=
  revertSelector? "revertLib" == some (selBytes "E(uint8)")
def revertOwnUnchanged : Bool :=
  revertSelector? "revertOwn" == some (selBytes "E(uint256)")
def revertLibNoCollisionResolves : Bool :=
  revertSelector? "revertLibNoCollision" == some (selBytes "Bad(uint64)")

#guard qualifiedCollisionAccepted
#guard emitLibResolvesLibraryTopic
#guard emitOwnUnchanged
#guard emitLibNoCollisionAccepted
#guard revertLibResolvesLibrarySelector
#guard revertOwnUnchanged
#guard revertLibNoCollisionResolves

end QualifiedCollision
end Witness
end Solidity
end SolidCore

import SolidCore.Solidity.Checked
import SolidCore.Witness.Checked

set_option maxHeartbeats 8000000

/-!
INHERITED-SCOPE witnesses (#197 + #199) — two over-rejects where a DERIVED
contract's environment omitted BASE-declared things.

#197 INHERITED-STRUCT-FIELD-ACCESS: a field access on a BASE-declared storage
struct from a derived contract (`p.a` for `P internal p;` in a base) failed to
lower (`TypeError.unsupported "checked executable checked contract C"`).
Root cause: `ContractDecl.resolveStructs` (Interface.lean) built its
member-rewrite type environment from the contract's OWN `decl.items` state
variables only, so inherited struct-typed variables never received the
member→fieldIndex rewrite. Fix: seed the type environment with the (C3-
linearized, non-private) INHERITED state variables at every resolveStructs
call site (`ContractDecl.resolveStructsWithInheritedVars` /
`resolveStructsInHierarchy`, and the contextual
`SourceUnit.resolveContractSourceTypes?` path).

#199 MODIFIER-BODY-PRIVATE-VAR-SCOPE: a base MODIFIER whose body reads a
PRIVATE state variable of its declaring contract, attached to a function
declared in a DERIVED contract, was rejected
(`TypeError.unknownIdentifier "_owner"`) — blocking the whole OZ
Ownable/Pausable mixin pattern. Root cause:
`ModifierInvocation.checkBodyForCaller` (TypeCheck.lean) re-typechecked the
modifier body in the CALLING contract's env (own + non-private-inherited
variables), where the declaring contract's privates are absent. solc resolves
a modifier body in its DECLARING contract's scope. Fix: seed the declaring
contract's private state variables into the modifier-body env
(`CheckEnv.modifierDeclaringPrivateStateVars`), between the modifier's
parameters and the caller's scope, so a same-name private redeclared in the
caller does not capture the base modifier's read.

Ground truth: pinned solc 0.8.35 + real EVM via Forge
(`tests/forge-harness/inherited-struct-field`,
`tests/forge-harness/modifier-private-scope`). All values below match the
Forge runs (42s, owner-gate pass/revert, shadow binds the BASE slot: 7).
-/

namespace SolidCore
namespace Solidity
namespace SolcAstImport
namespace InheritedStructFieldWitness

def importedSourceName : String := "tests/forge-harness/inherited-struct-field/src/InheritedStructField.sol"

def importedContractDecl0 : ContractDecl :=
{ kind := ContractKind.contract
  name := "StructBase"
  abstract := false
  bases := []
  items := [(ContractItem.structDecl
  { name := "P",
    fields := [{ name := "a", ty := Ty.uint 256 }, { name := "b", ty := Ty.uint 256 }] }), (ContractItem.structDecl
  { name := "Item",
    fields := [{ name := "amount", ty := Ty.uint 256 }, { name := "ts", ty := Ty.uint 256 }] }), (ContractItem.stateVar
  { name := "p",
    ty := Ty.user ({ segments := ["P"] }),
    visibility := some Visibility.internal_,
    mutability := VarMutability.mutable,
    override? := none,
    init := none }), (ContractItem.stateVar
  { name := "_items",
    ty := Ty.mapping (Ty.uint 256) (Ty.user ({ segments := ["Item"] })),
    visibility := some Visibility.internal_,
    mutability := VarMutability.mutable,
    override? := none,
    init := none }), (ContractItem.stateVar
  { name := "arr",
    ty := Ty.array (Ty.user ({ segments := ["P"] })) (none),
    visibility := some Visibility.internal_,
    mutability := VarMutability.mutable,
    override? := none,
    init := none })] }

def importedContractDecl1 : ContractDecl :=
{ kind := ContractKind.contract
  name := "StructMid"
  abstract := false
  bases := [{ base := { segments := ["StructBase"] }, args := [] }]
  items := [] }

def importedContractDecl2 : ContractDecl :=
{ kind := ContractKind.contract
  name := "InheritedStructFieldTarget"
  abstract := false
  bases := [{ base := { segments := ["StructMid"] }, args := [] }]
  items := [(ContractItem.function
  { kind := FunctionKind.function,
    name := some "setA",
    visibility := some Visibility.public_,
    mutability := StateMutability.nonpayable,
    params := [{ name := some "v", ty := Ty.uint 256, location := none }],
    returns := [],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.expr (Expr.assign (Expr.member (Expr.ident "p") "a") AssignOp.assign (Expr.ident "v"))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "getA",
    visibility := some Visibility.public_,
    mutability := StateMutability.view,
    params := [],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.member (Expr.ident "p") "a"))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "addItem",
    visibility := some Visibility.public_,
    mutability := StateMutability.nonpayable,
    params := [{ name := some "k", ty := Ty.uint 256, location := none }, { name := some "v", ty := Ty.uint 256, location := none }],
    returns := [],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.expr (Expr.assign (Expr.member (Expr.index (Expr.ident "_items") (Expr.ident "k")) "amount") AssignOp.assign (Expr.ident "v"))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "bumpItem",
    visibility := some Visibility.public_,
    mutability := StateMutability.nonpayable,
    params := [{ name := some "k", ty := Ty.uint 256, location := none }],
    returns := [],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.expr (Expr.assign (Expr.member (Expr.index (Expr.ident "_items") (Expr.ident "k")) "amount") AssignOp.addAssign (Expr.literal (Literal.number "1")))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "itemAmount",
    visibility := some Visibility.public_,
    mutability := StateMutability.view,
    params := [{ name := some "k", ty := Ty.uint 256, location := none }],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.member (Expr.index (Expr.ident "_items") (Expr.ident "k")) "amount"))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "pushArr",
    visibility := some Visibility.public_,
    mutability := StateMutability.nonpayable,
    params := [{ name := some "v", ty := Ty.uint 256, location := none }],
    returns := [],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.expr (Expr.call (Expr.member (Expr.ident "arr") "push") [Arg.positional (Expr.call (Expr.typeName (Ty.user ({ segments := ["P"] }))) [Arg.positional (Expr.ident "v"), Arg.positional (Expr.binary BinaryOp.add (Expr.ident "v") (Expr.literal (Literal.number "1")))])])]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "firstA",
    visibility := some Visibility.public_,
    mutability := StateMutability.view,
    params := [],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.member (Expr.index (Expr.ident "arr") (Expr.literal (Literal.number "0"))) "a"))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "getViaCopy",
    visibility := some Visibility.public_,
    mutability := StateMutability.view,
    params := [],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.varDecl [{ name := some "q", ty := Ty.user ({ segments := ["P"] }), location := some DataLocation.memory }] (some (Expr.ident "p")), Stmt.returnValues (some (Expr.member (Expr.ident "q") "a"))]) })] }

def importedContractDecl3 : ContractDecl :=
{ kind := ContractKind.contract
  name := "StructBaseSelf"
  abstract := false
  bases := []
  items := [(ContractItem.structDecl
  { name := "P",
    fields := [{ name := "a", ty := Ty.uint 256 }, { name := "b", ty := Ty.uint 256 }] }), (ContractItem.stateVar
  { name := "p",
    ty := Ty.user ({ segments := ["P"] }),
    visibility := some Visibility.internal_,
    mutability := VarMutability.mutable,
    override? := none,
    init := none }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "setA",
    visibility := some Visibility.public_,
    mutability := StateMutability.nonpayable,
    params := [{ name := some "v", ty := Ty.uint 256, location := none }],
    returns := [],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.expr (Expr.assign (Expr.member (Expr.ident "p") "a") AssignOp.assign (Expr.ident "v"))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "getA",
    visibility := some Visibility.public_,
    mutability := StateMutability.view,
    params := [],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.member (Expr.ident "p") "a"))]) })] }

def importedContractDecl4 : ContractDecl :=
{ kind := ContractKind.contract
  name := "StructTypeFromBase"
  abstract := false
  bases := [{ base := { segments := ["StructBase"] }, args := [] }]
  items := [(ContractItem.stateVar
  { name := "own",
    ty := Ty.user ({ segments := ["P"] }),
    visibility := some Visibility.internal_,
    mutability := VarMutability.mutable,
    override? := none,
    init := none }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "setOwn",
    visibility := some Visibility.public_,
    mutability := StateMutability.nonpayable,
    params := [{ name := some "v", ty := Ty.uint 256, location := none }],
    returns := [],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.expr (Expr.assign (Expr.member (Expr.ident "own") "a") AssignOp.assign (Expr.ident "v"))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "getOwn",
    visibility := some Visibility.public_,
    mutability := StateMutability.view,
    params := [],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.member (Expr.ident "own") "a"))]) })] }

def importedContract : ContractDecl :=
  importedContractDecl2

def importedContracts : List ContractDecl :=
  [importedContractDecl0, importedContractDecl1, importedContractDecl2, importedContractDecl3, importedContractDecl4]

def importedSourceUnit : SourceUnit :=
  { items := [SourceItem.pragma "solidity" "^0.8.35", SourceItem.contract importedContractDecl0, SourceItem.contract importedContractDecl1, SourceItem.contract importedContractDecl2, SourceItem.contract importedContractDecl3, SourceItem.contract importedContractDecl4] }

def importedContractAccepted : Bool :=
  TypeCheck.Result.isOk (TypeCheck.TypecheckedInput.checkedSourceUnit importedSourceUnit)

end InheritedStructFieldWitness

namespace ModifierPrivateScopeWitness

def importedSourceName : String := "tests/forge-harness/modifier-private-scope/src/ModifierPrivateScope.sol"

def importedContractDecl0 : ContractDecl :=
{ kind := ContractKind.contract
  name := "Ownable2"
  abstract := true
  bases := []
  items := [(ContractItem.stateVar
  { name := "_owner",
    ty := Ty.address false,
    visibility := some Visibility.private_,
    mutability := VarMutability.mutable,
    override? := none,
    init := none }), (ContractItem.function
  { kind := FunctionKind.constructor,
    name := none,
    visibility := some Visibility.internal_,
    mutability := StateMutability.nonpayable,
    params := [],
    returns := [],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.expr (Expr.assign (Expr.ident "_owner") AssignOp.assign (Expr.member (Expr.ident "msg") "sender"))]) }), ContractItem.modifierDecl
  { name := "onlyOwner"
    params := []
    virtual := false
    override? := none
    body := some (Stmt.block [Stmt.expr (Expr.call (Expr.ident "require") [Arg.positional (Expr.binary BinaryOp.eq (Expr.member (Expr.ident "msg") "sender") (Expr.ident "_owner")), Arg.positional (Expr.literal (Literal.string "own"))]), Stmt.modifierPlaceholder]) }, (ContractItem.function
  { kind := FunctionKind.function,
    name := some "owner",
    visibility := some Visibility.public_,
    mutability := StateMutability.view,
    params := [],
    returns := [{ name := none, ty := Ty.address false, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.ident "_owner"))]) })] }

def importedContractDecl1 : ContractDecl :=
{ kind := ContractKind.contract
  name := "Pausable2"
  abstract := true
  bases := [{ base := { segments := ["Ownable2"] }, args := [] }]
  items := [(ContractItem.stateVar
  { name := "_paused",
    ty := Ty.bool,
    visibility := some Visibility.private_,
    mutability := VarMutability.mutable,
    override? := none,
    init := none }), ContractItem.modifierDecl
  { name := "whenNotPaused"
    params := []
    virtual := false
    override? := none
    body := some (Stmt.block [Stmt.expr (Expr.call (Expr.ident "require") [Arg.positional (Expr.unary UnaryOp.logicalNot (Expr.ident "_paused")), Arg.positional (Expr.literal (Literal.string "paused"))]), Stmt.modifierPlaceholder]) }, (ContractItem.function
  { kind := FunctionKind.function,
    name := some "pause",
    visibility := some Visibility.external_,
    mutability := StateMutability.nonpayable,
    params := [],
    returns := [],
    virtual := false,
    override? := none,
    modifiers := [{ target := { segments := ["onlyOwner"] }, args := [], hasArgList := false }],
    body := some (Stmt.block [Stmt.expr (Expr.assign (Expr.ident "_paused") AssignOp.assign (Expr.literal (Literal.bool true)))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "isPaused",
    visibility := some Visibility.public_,
    mutability := StateMutability.view,
    params := [],
    returns := [{ name := none, ty := Ty.bool, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.ident "_paused"))]) })] }

def importedContractDecl2 : ContractDecl :=
{ kind := ContractKind.contract
  name := "Guard2"
  abstract := true
  bases := []
  items := [(ContractItem.stateVar
  { name := "_lock",
    ty := Ty.uint 256,
    visibility := some Visibility.private_,
    mutability := VarMutability.mutable,
    override? := none,
    init := none }), ContractItem.modifierDecl
  { name := "guarded"
    params := []
    virtual := false
    override? := none
    body := some (Stmt.block [Stmt.expr (Expr.call (Expr.ident "require") [Arg.positional (Expr.binary BinaryOp.eq (Expr.ident "_lock") (Expr.literal (Literal.number "0"))), Arg.positional (Expr.literal (Literal.string "lock"))]), Stmt.expr (Expr.assign (Expr.ident "_lock") AssignOp.assign (Expr.literal (Literal.number "1"))), Stmt.modifierPlaceholder, Stmt.expr (Expr.assign (Expr.ident "_lock") AssignOp.assign (Expr.literal (Literal.number "0")))]) }] }

def importedContractDecl3 : ContractDecl :=
{ kind := ContractKind.contract
  name := "Vault2"
  abstract := false
  bases := [{ base := { segments := ["Pausable2"] }, args := [] }, { base := { segments := ["Guard2"] }, args := [] }]
  items := [(ContractItem.stateVar
  { name := "_bal",
    ty := Ty.mapping (Ty.address false) (Ty.uint 256),
    visibility := some Visibility.private_,
    mutability := VarMutability.mutable,
    override? := none,
    init := none }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "deposit",
    visibility := some Visibility.external_,
    mutability := StateMutability.nonpayable,
    params := [{ name := some "amt", ty := Ty.uint 256, location := none }],
    returns := [],
    virtual := false,
    override? := none,
    modifiers := [{ target := { segments := ["whenNotPaused"] }, args := [], hasArgList := false }, { target := { segments := ["guarded"] }, args := [], hasArgList := false }],
    body := some (Stmt.block [Stmt.expr (Expr.assign (Expr.index (Expr.ident "_bal") (Expr.member (Expr.ident "msg") "sender")) AssignOp.addAssign (Expr.ident "amt"))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "balanceOf",
    visibility := some Visibility.public_,
    mutability := StateMutability.view,
    params := [{ name := some "who", ty := Ty.address false, location := none }],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.index (Expr.ident "_bal") (Expr.ident "who")))]) })] }

def importedContractDecl4 : ContractDecl :=
{ kind := ContractKind.contract
  name := "ShadowBase"
  abstract := true
  bases := []
  items := [(ContractItem.stateVar
  { name := "_x",
    ty := Ty.uint 256,
    visibility := some Visibility.private_,
    mutability := VarMutability.mutable,
    override? := none,
    init := none }), (ContractItem.function
  { kind := FunctionKind.constructor,
    name := none,
    visibility := some Visibility.internal_,
    mutability := StateMutability.nonpayable,
    params := [],
    returns := [],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.expr (Expr.assign (Expr.ident "_x") AssignOp.assign (Expr.literal (Literal.number "7")))]) }), ContractItem.modifierDecl
  { name := "gate"
    params := []
    virtual := false
    override? := none
    body := some (Stmt.block [Stmt.expr (Expr.call (Expr.ident "require") [Arg.positional (Expr.binary BinaryOp.eq (Expr.ident "_x") (Expr.literal (Literal.number "7"))), Arg.positional (Expr.literal (Literal.string "gate"))]), Stmt.modifierPlaceholder]) }, (ContractItem.function
  { kind := FunctionKind.function,
    name := some "baseX",
    visibility := some Visibility.public_,
    mutability := StateMutability.view,
    params := [],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.ident "_x"))]) })] }

def importedContractDecl5 : ContractDecl :=
{ kind := ContractKind.contract
  name := "ShadowDerived"
  abstract := false
  bases := [{ base := { segments := ["ShadowBase"] }, args := [] }]
  items := [(ContractItem.stateVar
  { name := "_x",
    ty := Ty.uint 256,
    visibility := some Visibility.private_,
    mutability := VarMutability.mutable,
    override? := none,
    init := none }), (ContractItem.stateVar
  { name := "n",
    ty := Ty.uint 256,
    visibility := some Visibility.public_,
    mutability := VarMutability.mutable,
    override? := none,
    init := none }), (ContractItem.function
  { kind := FunctionKind.constructor,
    name := none,
    visibility := some Visibility.public_,
    mutability := StateMutability.nonpayable,
    params := [],
    returns := [],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.expr (Expr.assign (Expr.ident "_x") AssignOp.assign (Expr.literal (Literal.number "99")))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "f",
    visibility := some Visibility.external_,
    mutability := StateMutability.nonpayable,
    params := [],
    returns := [],
    virtual := false,
    override? := none,
    modifiers := [{ target := { segments := ["gate"] }, args := [], hasArgList := false }],
    body := some (Stmt.block [Stmt.expr (Expr.assign (Expr.ident "n") AssignOp.assign (Expr.binary BinaryOp.add (Expr.ident "n") (Expr.literal (Literal.number "1"))))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "derivedX",
    visibility := some Visibility.public_,
    mutability := StateMutability.view,
    params := [],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.ident "_x"))]) })] }

def importedContractDecl6 : ContractDecl :=
{ kind := ContractKind.contract
  name := "InternalOwned"
  abstract := true
  bases := []
  items := [(ContractItem.stateVar
  { name := "_keeper",
    ty := Ty.address false,
    visibility := some Visibility.internal_,
    mutability := VarMutability.mutable,
    override? := none,
    init := none }), (ContractItem.function
  { kind := FunctionKind.constructor,
    name := none,
    visibility := some Visibility.internal_,
    mutability := StateMutability.nonpayable,
    params := [],
    returns := [],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.expr (Expr.assign (Expr.ident "_keeper") AssignOp.assign (Expr.member (Expr.ident "msg") "sender"))]) }), ContractItem.modifierDecl
  { name := "onlyKeeper"
    params := []
    virtual := false
    override? := none
    body := some (Stmt.block [Stmt.expr (Expr.call (Expr.ident "require") [Arg.positional (Expr.binary BinaryOp.eq (Expr.member (Expr.ident "msg") "sender") (Expr.ident "_keeper")), Arg.positional (Expr.literal (Literal.string "keep"))]), Stmt.modifierPlaceholder]) }] }

def importedContractDecl7 : ContractDecl :=
{ kind := ContractKind.contract
  name := "InternalOwnedTarget"
  abstract := false
  bases := [{ base := { segments := ["InternalOwned"] }, args := [] }]
  items := [(ContractItem.stateVar
  { name := "n",
    ty := Ty.uint 256,
    visibility := some Visibility.public_,
    mutability := VarMutability.mutable,
    override? := none,
    init := none }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "f",
    visibility := some Visibility.external_,
    mutability := StateMutability.nonpayable,
    params := [],
    returns := [],
    virtual := false,
    override? := none,
    modifiers := [{ target := { segments := ["onlyKeeper"] }, args := [], hasArgList := false }],
    body := some (Stmt.block [Stmt.expr (Expr.assign (Expr.ident "n") AssignOp.assign (Expr.binary BinaryOp.add (Expr.ident "n") (Expr.literal (Literal.number "1"))))]) })] }

def importedContract : ContractDecl :=
  importedContractDecl3

def importedContracts : List ContractDecl :=
  [importedContractDecl0, importedContractDecl1, importedContractDecl2, importedContractDecl3, importedContractDecl4, importedContractDecl5, importedContractDecl6, importedContractDecl7]

def importedSourceUnit : SourceUnit :=
  { items := [SourceItem.pragma "solidity" "^0.8.35", SourceItem.contract importedContractDecl0, SourceItem.contract importedContractDecl1, SourceItem.contract importedContractDecl2, SourceItem.contract importedContractDecl3, SourceItem.contract importedContractDecl4, SourceItem.contract importedContractDecl5, SourceItem.contract importedContractDecl6, SourceItem.contract importedContractDecl7] }

def importedContractAccepted : Bool :=
  TypeCheck.Result.isOk (TypeCheck.TypecheckedInput.checkedSourceUnit importedSourceUnit)

end ModifierPrivateScopeWitness

end SolcAstImport
end Solidity
end SolidCore

namespace SolidCore
namespace Solidity
namespace Witness
namespace InheritedScope

open SolidCore.Solidity.Source
open SolidCore.Solidity.TypeCheck
open SolidCore.Solidity.TypeCheck.Examples

private def succeeds : Except TypeError Bool -> Bool
  | Except.ok b => b
  | Except.error _ => false

private def structUnit : SourceUnit :=
  SolcAstImport.InheritedStructFieldWitness.importedSourceUnit

private def modifierUnit : SourceUnit :=
  SolcAstImport.ModifierPrivateScopeWitness.importedSourceUnit

/-! ## #197 — inherited struct field access lowers and computes real-EVM values -/

#guard SolcAstImport.InheritedStructFieldWitness.importedContractAccepted

private def structTargetChecks : Except TypeError Bool := do
  let target := "InheritedStructFieldTarget"
  -- Grandparent(-via-StructMid) struct var: write then read → 42.
  let r1 ← CheckedInput.callContractTransaction 500 structUnit target
    (CallTarget.name "setA") State.empty [Value.word 42]
  match r1 with
  | CallResult.returned st1 _ => do
      let getA ← checkedCallWordMatches 500 structUnit target "getA" st1 [] 42
      -- Control: whole-struct memory copy of the inherited storage struct.
      let viaCopy ← checkedCallWordMatches 500 structUnit target "getViaCopy" st1 [] 42
      -- Inherited mapping(=>struct) element: write, compound `+= 1`, read → 42.
      let r2 ← CheckedInput.callContractTransaction 500 structUnit target
        (CallTarget.name "addItem") st1 [Value.word 7, Value.word 41]
      match r2 with
      | CallResult.returned st2 _ => do
          let r3 ← CheckedInput.callContractTransaction 500 structUnit target
            (CallTarget.name "bumpItem") st2 [Value.word 7]
          match r3 with
          | CallResult.returned st3 _ => do
              let item ← checkedCallWordMatches 500 structUnit target "itemAmount" st3
                [Value.word 7] 42
              -- Inherited struct[] element: push + element field read → 42.
              let r4 ← CheckedInput.callContractTransaction 500 structUnit target
                (CallTarget.name "pushArr") st3 [Value.word 42]
              match r4 with
              | CallResult.returned st4 _ => do
                  let first ← checkedCallWordMatches 500 structUnit target "firstA" st4 [] 42
                  Except.ok (getA && viaCopy && item && first)
              | _ => Except.ok false
          | _ => Except.ok false
      | _ => Except.ok false
  | _ => Except.ok false

#guard succeeds structTargetChecks

/-- Control: the base reading its OWN field is unaffected. -/
private def structBaseSelfCheck : Except TypeError Bool := do
  let r ← CheckedInput.callContractTransaction 500 structUnit "StructBaseSelf"
    (CallTarget.name "setA") State.empty [Value.word 42]
  match r with
  | CallResult.returned st _ =>
      checkedCallWordMatches 500 structUnit "StructBaseSelf" "getA" st [] 42
  | _ => Except.ok false

#guard succeeds structBaseSelfCheck

/-- Control: struct TYPE from the base, state var declared in the derived. -/
private def structTypeFromBaseCheck : Except TypeError Bool := do
  let r ← CheckedInput.callContractTransaction 500 structUnit "StructTypeFromBase"
    (CallTarget.name "setOwn") State.empty [Value.word 42]
  match r with
  | CallResult.returned st _ =>
      checkedCallWordMatches 500 structUnit "StructTypeFromBase" "getOwn" st [] 42
  | _ => Except.ok false

#guard succeeds structTypeFromBaseCheck

/-! ## #199 — base modifier reading its declaring contract's PRIVATE variable -/

#guard SolcAstImport.ModifierPrivateScopeWitness.importedContractAccepted

private def ownerWord : Word := 0xAA
private def outsiderWord : Word := 0xBB

private def constructedState (name : Name) (sender : Word) :
    Except TypeError State := do
  let program ← CheckedInput.program modifierUnit
  let result ← CheckedProgram.constructContractFrom 500 program name
    State.empty sender 0 []
  match result with
  | CallResult.returned st _ => Except.ok st
  | _ => Except.error (TypeError.unsupported "constructor")

/-- The triple mixin `Vault2 is Pausable2 (is Ownable2), Guard2`: deposit
    passes `whenNotPaused`+`guarded`, non-owner `pause()` reverts "own"
    (Ownable2's PRIVATE `_owner` read by `onlyOwner` on a function declared
    two contracts below), owner pauses, deposit then reverts "paused". -/
private def mixinChecks : Except TypeError Bool := do
  let program ← CheckedInput.program modifierUnit
  let vault ← CheckedProgram.contract program "Vault2"
  let st0 ← constructedState "Vault2" ownerWord
  let depositCd ← CheckedContract.functionCalldata vault "deposit" [Value.word 42]
  let deposit ← CheckedContract.callCalldataFrom 500 vault st0 outsiderWord 0 depositCd
  let balance ← checkedCallWordMatches 500 modifierUnit "Vault2" "balanceOf"
    deposit.state [Value.word outsiderWord] 42
  let pauseCd ← CheckedContract.functionCalldata vault "pause" []
  let pauseByOutsider ← CheckedContract.callCalldataFrom 500 vault deposit.state
    outsiderWord 0 pauseCd
  let pauseByOwner ← CheckedContract.callCalldataFrom 500 vault deposit.state
    ownerWord 0 pauseCd
  let paused ← checkedCallWordMatches 500 modifierUnit "Vault2" "isPaused"
    pauseByOwner.state [] 1
  let depositWhilePaused ← CheckedContract.callCalldataFrom 500 vault
    pauseByOwner.state outsiderWord 0 depositCd
  Except.ok
    (deposit.success && balance && !pauseByOutsider.success &&
      pauseByOwner.success && paused && !depositWhilePaused.success)

#guard succeeds mixinChecks

/-- Control: a derived PRIVATE `_x` shadowing the base's does NOT capture the
    base modifier's read — `gate` binds the BASE slot (7), so `f()` passes
    while `derivedX` still reads the derived slot (99). -/
private def shadowChecks : Except TypeError Bool := do
  let program ← CheckedInput.program modifierUnit
  let shadow ← CheckedProgram.contract program "ShadowDerived"
  let st0 ← constructedState "ShadowDerived" ownerWord
  let baseX ← checkedCallWordMatches 500 modifierUnit "ShadowDerived" "baseX" st0 [] 7
  let derivedX ← checkedCallWordMatches 500 modifierUnit "ShadowDerived" "derivedX" st0 [] 99
  let f ← CheckedContract.callTransaction 500 shadow (CallTarget.name "f") st0 []
  match f with
  | CallResult.returned st1 _ => do
      let n ← checkedCallWordMatches 500 modifierUnit "ShadowDerived" "n" st1 [] 1
      Except.ok (baseX && derivedX && n)
  | _ => Except.ok false

#guard succeeds shadowChecks

/-- Control: an INTERNAL base variable read by the base modifier keeps
    working (and still gates: non-keeper reverts). -/
private def internalControlChecks : Except TypeError Bool := do
  let program ← CheckedInput.program modifierUnit
  let target ← CheckedProgram.contract program "InternalOwnedTarget"
  let st0 ← constructedState "InternalOwnedTarget" ownerWord
  let fCd ← CheckedContract.functionCalldata target "f" []
  let byKeeper ← CheckedContract.callCalldataFrom 500 target st0 ownerWord 0 fCd
  let byOther ← CheckedContract.callCalldataFrom 500 target st0 outsiderWord 0 fCd
  let n ← checkedCallWordMatches 500 modifierUnit "InternalOwnedTarget" "n"
    byKeeper.state [] 1
  Except.ok (byKeeper.success && !byOther.success && n)

#guard succeeds internalControlChecks

end InheritedScope
end Witness
end Solidity
end SolidCore

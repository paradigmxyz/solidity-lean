import SolidCore.Solidity.Checked
import SolidCore.Witness.Checked

set_option maxHeartbeats 8000000

/-!
Regression for a `bytes memory` to `bytesN` conversion inside the index key
of an assignment target. `m[uint32(bytes4(v))] = 7` must take the first four
bytes of `v` exactly as the read `m[uint32(bytes4(v))]` does; the target's
keys used to skip the source-type annotation, so the conversion lost its
`bytes` operand type and the store reverted with Panic(0x00). Covers mapping
and memory-array targets, a short source padded on the right, a `bytes4`
mapping key with compound assignment, and a key read through a local as
control.
-/

namespace SolidCore.Solidity.Witness.LvalueKeyBytesConversion

open SolidCore.Solidity
open SolidCore.Solidity.Source
open SolidCore.Solidity.TypeCheck

def contract : ContractDecl :=
{ kind := ContractKind.contract
  name := "C"
  abstract := false
  bases := []
  items := [(ContractItem.stateVar
  { name := "m",
    ty := Ty.mapping (Ty.uint 256) (Ty.uint 256),
    visibility := some Visibility.internal_,
    mutability := VarMutability.mutable,
    override? := none,
    init := none }), (ContractItem.stateVar
  { name := "mb",
    ty := Ty.mapping (Ty.bytesN 4) (Ty.uint 256),
    visibility := some Visibility.internal_,
    mutability := VarMutability.mutable,
    override? := none,
    init := none }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "f",
    visibility := some Visibility.external_,
    mutability := StateMutability.nonpayable,
    params := [],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.varDecl [{ name := some "v", ty := Ty.bytes, location := some DataLocation.memory }] (some (Expr.literal (Literal.string "lean"))), Stmt.expr (Expr.assign (Expr.index (Expr.ident "m") (Expr.call (Expr.typeName (Ty.uint 32)) [Arg.positional (Expr.call (Expr.typeName (Ty.bytesN 4)) [Arg.positional (Expr.ident "v")])])) AssignOp.assign (Expr.literal (Literal.number "7"))), Stmt.returnValues (some (Expr.index (Expr.ident "m") (Expr.call (Expr.typeName (Ty.uint 32)) [Arg.positional (Expr.call (Expr.typeName (Ty.bytesN 4)) [Arg.positional (Expr.ident "v")])])))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "short",
    visibility := some Visibility.external_,
    mutability := StateMutability.nonpayable,
    params := [],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.varDecl [{ name := some "v", ty := Ty.bytes, location := some DataLocation.memory }] (some (Expr.literal (Literal.hexString "aa"))), Stmt.expr (Expr.assign (Expr.index (Expr.ident "m") (Expr.call (Expr.typeName (Ty.uint 32)) [Arg.positional (Expr.call (Expr.typeName (Ty.bytesN 4)) [Arg.positional (Expr.ident "v")])])) AssignOp.assign (Expr.literal (Literal.number "1"))), Stmt.returnValues (some (Expr.index (Expr.ident "m") (Expr.literal (Literal.number "2852126720"))))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "arr",
    visibility := some Visibility.external_,
    mutability := StateMutability.pure,
    params := [],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.varDecl [{ name := some "v", ty := Ty.bytes, location := some DataLocation.memory }] (some (Expr.literal (Literal.hexString "0102"))), Stmt.varDecl [{ name := some "a", ty := Ty.array (Ty.uint 256) (none), location := some DataLocation.memory }] (some (Expr.newExpr (Ty.array (Ty.uint 256) (none)) [Arg.positional (Expr.literal (Literal.number "3"))])), Stmt.expr (Expr.assign (Expr.index (Expr.ident "a") (Expr.call (Expr.typeName (Ty.uint 8)) [Arg.positional (Expr.call (Expr.typeName (Ty.bytesN 1)) [Arg.positional (Expr.ident "v")])])) AssignOp.assign (Expr.literal (Literal.number "9"))), Stmt.returnValues (some (Expr.index (Expr.ident "a") (Expr.literal (Literal.number "1"))))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "bkey",
    visibility := some Visibility.external_,
    mutability := StateMutability.nonpayable,
    params := [],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.varDecl [{ name := some "v", ty := Ty.bytes, location := some DataLocation.memory }] (some (Expr.literal (Literal.string "lean"))), Stmt.expr (Expr.assign (Expr.index (Expr.ident "mb") (Expr.call (Expr.typeName (Ty.bytesN 4)) [Arg.positional (Expr.ident "v")])) AssignOp.assign (Expr.literal (Literal.number "3"))), Stmt.expr (Expr.assign (Expr.index (Expr.ident "mb") (Expr.call (Expr.typeName (Ty.bytesN 4)) [Arg.positional (Expr.ident "v")])) AssignOp.addAssign (Expr.literal (Literal.number "2"))), Stmt.returnValues (some (Expr.index (Expr.ident "mb") (Expr.call (Expr.typeName (Ty.bytesN 4)) [Arg.positional (Expr.ident "v")])))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "control",
    visibility := some Visibility.external_,
    mutability := StateMutability.nonpayable,
    params := [],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.varDecl [{ name := some "v", ty := Ty.bytes, location := some DataLocation.memory }] (some (Expr.literal (Literal.string "lean"))), Stmt.varDecl [{ name := some "b", ty := Ty.bytesN 4, location := none }] (some (Expr.call (Expr.typeName (Ty.bytesN 4)) [Arg.positional (Expr.ident "v")])), Stmt.expr (Expr.assign (Expr.index (Expr.ident "m") (Expr.call (Expr.typeName (Ty.uint 32)) [Arg.positional (Expr.ident "b")])) AssignOp.assign (Expr.literal (Literal.number "6"))), Stmt.returnValues (some (Expr.index (Expr.ident "m") (Expr.call (Expr.typeName (Ty.uint 32)) [Arg.positional (Expr.ident "b")])))]) })] }

def sourceUnit : SourceUnit :=
  { items := [SourceItem.pragma "solidity" "^0.8.28",
      SourceItem.contract contract] }

private def ok : Except TypeCheck.TypeError Bool -> Bool
  | Except.ok true => true
  | _ => false

def accepted : Bool :=
  TypeCheck.Result.isOk
    (TypeCheck.TypecheckedInput.checkedSourceUnit sourceUnit)

private def returns (name : String) (expected : Word) :
    Except TypeCheck.TypeError Bool :=
  Examples.checkedOwnCallWordMatches 1024 contract name State.empty []
    expected

#guard accepted
#guard ok (returns "f" 7)
#guard ok (returns "short" 1)
#guard ok (returns "arr" 9)
#guard ok (returns "bkey" 5)
#guard ok (returns "control" 6)

end SolidCore.Solidity.Witness.LvalueKeyBytesConversion


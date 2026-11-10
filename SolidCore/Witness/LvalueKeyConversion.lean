import SolidCore.Solidity.Checked
import SolidCore.Witness.Checked

set_option maxHeartbeats 8000000

/-!
Regression for explicit conversions inside the index keys of assignment
targets. `s[uint256(p)] = 7` with `int256 p` must convert the key exactly as
the read `s[uint256(p)]` does; the target's keys used to skip the source-type
annotation, so the signed value reached the store unconverted and reverted with
Panic(0x00). Covers storage arrays, mapping keys, compound assignment,
increment, delete, memory arrays and the out-of-range `uint256(-1)` index
(Panic(0x32)), with a key computed through a local as control.
-/

namespace SolidCore.Solidity.Witness.LvalueKeyConversion

open SolidCore.Solidity
open SolidCore.Solidity.Source
open SolidCore.Solidity.TypeCheck

def contract : ContractDecl :=
{ kind := ContractKind.contract
  name := "C"
  abstract := false
  bases := []
  items := [(ContractItem.stateVar
  { name := "s",
    ty := Ty.array (Ty.uint 256) (some 4),
    visibility := some Visibility.internal_,
    mutability := VarMutability.mutable,
    override? := none,
    init := none }), (ContractItem.stateVar
  { name := "m",
    ty := Ty.mapping (Ty.uint 256) (Ty.uint 256),
    visibility := some Visibility.internal_,
    mutability := VarMutability.mutable,
    override? := none,
    init := none }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "store",
    visibility := some Visibility.external_,
    mutability := StateMutability.nonpayable,
    params := [{ name := some "p", ty := Ty.int 256, location := none }],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.expr (Expr.assign (Expr.index (Expr.ident "s") (Expr.call (Expr.typeName (Ty.uint 256)) [Arg.positional (Expr.ident "p")])) AssignOp.assign (Expr.literal (Literal.number "7"))), Stmt.returnValues (some (Expr.index (Expr.ident "s") (Expr.literal (Literal.number "0"))))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "key",
    visibility := some Visibility.external_,
    mutability := StateMutability.nonpayable,
    params := [{ name := some "p", ty := Ty.int 256, location := none }],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.expr (Expr.assign (Expr.index (Expr.ident "m") (Expr.call (Expr.typeName (Ty.uint 256)) [Arg.positional (Expr.ident "p")])) AssignOp.assign (Expr.literal (Literal.number "5"))), Stmt.returnValues (some (Expr.index (Expr.ident "m") (Expr.call (Expr.typeName (Ty.uint 256)) [Arg.positional (Expr.ident "p")])))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "compound",
    visibility := some Visibility.external_,
    mutability := StateMutability.nonpayable,
    params := [{ name := some "p", ty := Ty.int 256, location := none }],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.expr (Expr.assign (Expr.index (Expr.ident "s") (Expr.call (Expr.typeName (Ty.uint 256)) [Arg.positional (Expr.ident "p")])) AssignOp.addAssign (Expr.literal (Literal.number "3"))), Stmt.expr (Expr.unary UnaryOp.postIncrement (Expr.index (Expr.ident "s") (Expr.call (Expr.typeName (Ty.uint 256)) [Arg.positional (Expr.ident "p")]))), Stmt.returnValues (some (Expr.index (Expr.ident "s") (Expr.call (Expr.typeName (Ty.uint 256)) [Arg.positional (Expr.ident "p")])))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "mem",
    visibility := some Visibility.external_,
    mutability := StateMutability.pure,
    params := [{ name := some "p", ty := Ty.int 256, location := none }],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.varDecl [{ name := some "a", ty := Ty.array (Ty.uint 256) (none), location := some DataLocation.memory }] (some (Expr.newExpr (Ty.array (Ty.uint 256) (none)) [Arg.positional (Expr.literal (Literal.number "3"))])), Stmt.expr (Expr.assign (Expr.index (Expr.ident "a") (Expr.call (Expr.typeName (Ty.uint 256)) [Arg.positional (Expr.ident "p")])) AssignOp.assign (Expr.literal (Literal.number "9"))), Stmt.returnValues (some (Expr.index (Expr.ident "a") (Expr.literal (Literal.number "1"))))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "wipe",
    visibility := some Visibility.external_,
    mutability := StateMutability.nonpayable,
    params := [{ name := some "p", ty := Ty.int 256, location := none }],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.expr (Expr.assign (Expr.index (Expr.ident "s") (Expr.literal (Literal.number "1"))) AssignOp.assign (Expr.literal (Literal.number "4"))), Stmt.expr (Expr.unary UnaryOp.delete (Expr.index (Expr.ident "s") (Expr.call (Expr.typeName (Ty.uint 256)) [Arg.positional (Expr.ident "p")]))), Stmt.returnValues (some (Expr.index (Expr.ident "s") (Expr.literal (Literal.number "1"))))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "control",
    visibility := some Visibility.external_,
    mutability := StateMutability.nonpayable,
    params := [{ name := some "p", ty := Ty.int 256, location := none }],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.varDecl [{ name := some "k", ty := Ty.uint 256, location := none }] (some (Expr.call (Expr.typeName (Ty.uint 256)) [Arg.positional (Expr.ident "p")])), Stmt.expr (Expr.assign (Expr.index (Expr.ident "s") (Expr.ident "k")) AssignOp.assign (Expr.literal (Literal.number "8"))), Stmt.returnValues (some (Expr.index (Expr.ident "s") (Expr.ident "k")))]) })] }

def sourceUnit : SourceUnit :=
  { items := [SourceItem.pragma "solidity" "^0.8.28",
      SourceItem.contract contract] }

private def ok : Except TypeCheck.TypeError Bool -> Bool
  | Except.ok true => true
  | _ => false

def accepted : Bool :=
  TypeCheck.Result.isOk
    (TypeCheck.TypecheckedInput.checkedSourceUnit sourceUnit)

private def returns (name : String) (p : Word) (expected : Word) :
    Except TypeCheck.TypeError Bool :=
  Examples.checkedOwnCallWordMatches 1024 contract name State.empty
    [Value.int p] expected

private def panics (name : String) (p : Word) (code : Nat) :
    Except TypeCheck.TypeError Bool :=
  Examples.checkedOwnCallPanicMatches 1024 contract name State.empty
    [Value.int p] code

#guard accepted
#guard ok (returns "store" 0 7)
#guard ok (panics "store" (2 ^ 256 - 1) 0x32)
#guard ok (returns "key" (2 ^ 256 - 3) 5)
#guard ok (returns "compound" 2 4)
#guard ok (returns "mem" 1 9)
#guard ok (panics "mem" 3 0x32)
#guard ok (returns "wipe" 1 0)
#guard ok (returns "control" 2 8)

end SolidCore.Solidity.Witness.LvalueKeyConversion


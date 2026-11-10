import SolidCore.Solidity.Checked
import SolidCore.Witness.Checked

set_option maxHeartbeats 8000000

/-!
Regression for a typed zero modulus in `addmod`/`mulmod`. solc rejects only a
modulus that folds as an untyped rational constant (`0`, `1 - 1`); an
explicit conversion such as `uint256(0)` (or a constant initialized with
one) is a typed value that compiles and reverts with Panic(0x12) at runtime.
The type checker used to fold through the conversion and reject the contract.
A non-zero typed modulus is the control; `addmod(x, x, 1 - 1)` stays rejected.
-/

namespace SolidCore.Solidity.Witness.ModArithTypedZeroModulus

open SolidCore.Solidity
open SolidCore.Solidity.Source
open SolidCore.Solidity.TypeCheck

def contract : ContractDecl :=
{ kind := ContractKind.contract
  name := "C"
  abstract := false
  bases := []
  items := [(ContractItem.stateVar
  { name := "W",
    ty := Ty.uint 256,
    visibility := some Visibility.internal_,
    mutability := VarMutability.constant,
    override? := none,
    init := some (Expr.call (Expr.typeName (Ty.uint 256)) [Arg.positional (Expr.literal (Literal.number "0"))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "add0",
    visibility := some Visibility.external_,
    mutability := StateMutability.pure,
    params := [{ name := some "x", ty := Ty.uint 256, location := none }],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.call (Expr.ident "addmod") [Arg.positional (Expr.ident "x"), Arg.positional (Expr.ident "x"), Arg.positional (Expr.call (Expr.typeName (Ty.uint 256)) [Arg.positional (Expr.literal (Literal.number "0"))])]))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "mul0",
    visibility := some Visibility.external_,
    mutability := StateMutability.pure,
    params := [{ name := some "x", ty := Ty.uint 256, location := none }],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.call (Expr.ident "mulmod") [Arg.positional (Expr.ident "x"), Arg.positional (Expr.ident "x"), Arg.positional (Expr.call (Expr.typeName (Ty.uint 256)) [Arg.positional (Expr.literal (Literal.number "0"))])]))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "add8",
    visibility := some Visibility.external_,
    mutability := StateMutability.pure,
    params := [{ name := some "x", ty := Ty.uint 256, location := none }],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.call (Expr.ident "addmod") [Arg.positional (Expr.ident "x"), Arg.positional (Expr.ident "x"), Arg.positional (Expr.call (Expr.typeName (Ty.uint 8)) [Arg.positional (Expr.literal (Literal.number "0"))])]))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "mulW",
    visibility := some Visibility.external_,
    mutability := StateMutability.pure,
    params := [{ name := some "x", ty := Ty.uint 256, location := none }],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.call (Expr.ident "mulmod") [Arg.positional (Expr.ident "x"), Arg.positional (Expr.ident "x"), Arg.positional (Expr.ident "W")]))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "control",
    visibility := some Visibility.external_,
    mutability := StateMutability.pure,
    params := [{ name := some "x", ty := Ty.uint 256, location := none }],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.binary BinaryOp.add (Expr.call (Expr.ident "addmod") [Arg.positional (Expr.ident "x"), Arg.positional (Expr.ident "x"), Arg.positional (Expr.call (Expr.typeName (Ty.uint 256)) [Arg.positional (Expr.literal (Literal.number "7"))])]) (Expr.call (Expr.ident "mulmod") [Arg.positional (Expr.ident "x"), Arg.positional (Expr.literal (Literal.number "3")), Arg.positional (Expr.literal (Literal.number "7"))])))]) })] }

def sourceUnit : SourceUnit :=
  { items := [SourceItem.pragma "solidity" "^0.8.28",
      SourceItem.contract contract] }

private def untypedZero : ContractDecl :=
  { kind := ContractKind.contract
    name := "D"
    abstract := false
    bases := []
    items := [ContractItem.function
      { kind := FunctionKind.function
        name := some "f"
        visibility := some Visibility.external_
        mutability := StateMutability.pure
        params := [{ name := some "x", ty := Ty.uint 256, location := none }]
        returns := [{ name := none, ty := Ty.uint 256, location := none }]
        virtual := false
        override? := none
        modifiers := []
        body := some (Stmt.block [Stmt.returnValues (some
          (Expr.call (Expr.ident "addmod")
            [ Arg.positional (Expr.ident "x"), Arg.positional (Expr.ident "x")
            , Arg.positional (Expr.binary BinaryOp.sub
                (Expr.literal (Literal.number "1"))
                (Expr.literal (Literal.number "1"))) ]))]) }] }

private def ok : Except TypeCheck.TypeError Bool -> Bool
  | Except.ok true => true
  | _ => false

def accepted : Bool :=
  TypeCheck.Result.isOk
    (TypeCheck.TypecheckedInput.checkedSourceUnit sourceUnit)

def untypedZeroRejected : Bool :=
  !TypeCheck.Result.isOk
    (TypeCheck.TypecheckedInput.checkedSourceUnit
      ({ items := [SourceItem.pragma "solidity" "^0.8.28",
          SourceItem.contract untypedZero] } : SourceUnit))

private def panics (name : String) : Except TypeCheck.TypeError Bool :=
  Examples.checkedOwnCallPanicMatches 1024 contract name State.empty
    [Value.word 1] 0x12

#guard accepted
#guard untypedZeroRejected
#guard ok (panics "add0")
#guard ok (panics "mul0")
#guard ok (panics "add8")
#guard ok (panics "mulW")
#guard ok (Examples.checkedOwnCallWordMatches 1024 contract "control"
  State.empty [Value.word 5] 4)

end SolidCore.Solidity.Witness.ModArithTypedZeroModulus


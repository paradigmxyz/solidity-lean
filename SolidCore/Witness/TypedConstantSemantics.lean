import SolidCore.Solidity.Checked
import SolidCore.Witness.Checked

set_option maxHeartbeats 8000000

/-!
Typed constant uses and compound literal adoption.

A declared integer constant retains its declared type at each use.  Substituting
`uint constant a = 12` as the raw rational literal `12` made `(a / 10) * 10`
fold with rational arithmetic to `12`; Solidity performs `uint256` division and
returns `10`.  Constant inlining now inserts a pure typed-use barrier.

A complete raw constant expression also adopts the other operand's concrete type
when it fits.  Thus `type(int).max == 2**255 - 1` compares two `int256` values;
treating only a direct literal as adoptable left the right side as `uint256` and
caused a core type-mismatch Panic(0).
-/

namespace SolidCore.Solidity.Witness.TypedConstantSemantics

open SolidCore.Solidity.Source
open SolidCore.Solidity.TypeCheck

private def num (s : String) : Expr := Expr.literal (Literal.number s)

private def constDecl (name value : String) : ContractItem :=
  ContractItem.stateVar
    { name := name, ty := Ty.uint 256,
      mutability := VarMutability.constant,
      init := some (num value) }

private def constExpr : Expr :=
  Expr.binary BinaryOp.mul
    (Expr.binary BinaryOp.div (Expr.ident "a") (Expr.ident "b"))
    (Expr.ident "b")

private def constFn : ContractItem :=
  ContractItem.function
    { kind := FunctionKind.function, name := some "f",
      visibility := some Visibility.public_,
      mutability := StateMutability.pure,
      params := [],
      returns :=
        [ { name := none, ty := Ty.uint 256, location := none }
        , { name := none, ty := Ty.uint 256, location := none } ],
      body := some (Stmt.block
        [ Stmt.varDecl
            [{ name := some "x",
               ty := some (Ty.array (Ty.uint 256) (some 10)),
               location := some DataLocation.memory }] none
        , Stmt.returnValues (some (Expr.tuple
            [ TupleItem.value (Expr.member (Expr.ident "x") "length")
            , TupleItem.value constExpr ])) ]) }

def constantContract : ContractDecl :=
  { kind := ContractKind.contract, name := "Constants", abstract := false,
    bases := [], items := [constDecl "a" "12", constDecl "b" "10", constFn] }

private def intMaxExpr : Expr :=
  Expr.member (Expr.typeName (Ty.int 256)) "max"

private def intMaxLiteral : Expr :=
  Expr.binary BinaryOp.sub
    (Expr.binary BinaryOp.exp (num "2") (num "255")) (num "1")

private def intMaxFn : ContractItem :=
  ContractItem.function
    { kind := FunctionKind.function, name := some "basic",
      visibility := some Visibility.public_,
      mutability := StateMutability.pure,
      params := [], returns := [{ name := none, ty := Ty.bool, location := none }],
      body := some (Stmt.block
        [ Stmt.varDecl
            [{ name := some "int_max", ty := some (Ty.int 256) }]
            (some intMaxExpr)
        , Stmt.expr (Expr.call (Expr.ident "require")
            [Arg.positional
              (Expr.binary BinaryOp.eq (Expr.ident "int_max") intMaxLiteral)]) ]) }

def intMaxContract : ContractDecl :=
  { kind := ContractKind.contract, name := "IntMax", abstract := false,
    bases := [], items := [intMaxFn] }

private def localShadowFn : ContractItem :=
  ContractItem.function
    { kind := FunctionKind.function, name := some "run",
      visibility := some Visibility.public_,
      mutability := StateMutability.pure,
      params := [],
      returns := [{ name := none, ty := Ty.uint 256, location := none }],
      body := some (Stmt.block
        [ Stmt.varDecl
            [{ name := some "K", ty := some (Ty.uint 256), location := none }]
            (some (num "3"))
        , Stmt.returnValues (some
            (Expr.binary BinaryOp.add (Expr.ident "K") (num "1"))) ]) }

def localShadowContract : ContractDecl :=
  { kind := ContractKind.contract, name := "LocalShadow", abstract := false,
    bases := [], items := [constDecl "K" "7", localShadowFn] }

private def isOkTrue : Except TypeError Bool -> Bool
  | Except.ok true => true
  | _ => false

def constant_pair_is_ten : Except TypeError Bool :=
  Examples.checkedOwnCallWordPairMatches 128 constantContract "f" State.empty [] 10 10

def int_max_comparison_succeeds : Except TypeError Bool :=
  Examples.checkedOwnCallWordMatches 64 intMaxContract "basic" State.empty [] 0

def local_shadow_returns_four : Except TypeError Bool :=
  Examples.checkedOwnCallWordMatches 128 localShadowContract "run" State.empty [] 4

#guard isOkTrue constant_pair_is_ten
#guard isOkTrue int_max_comparison_succeeds
#guard isOkTrue local_shadow_returns_four

end SolidCore.Solidity.Witness.TypedConstantSemantics

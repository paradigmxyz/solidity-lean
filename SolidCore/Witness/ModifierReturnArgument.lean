import SolidCore.Solidity.Checked
import SolidCore.Witness.Checked

set_option maxHeartbeats 8000000

/-!
A modifier argument may read a named return variable before the function body.
The return binding is initialized to its default value before modifier execution.
The submitted `mod2(r)` therefore binds a zero `bytes7`; its string-literal
comparison is false and the call returns the default zero value.

The modifier placeholder lowering is env-free after splicing.  Annotating a
binary operation now records the implicit conversion of a direct literal to the
other operand's known type, so `bytes7 a == "1234567"` compares two fixed-byte
values instead of reaching the core evaluator as `fixedBytes == bytes` and
raising Panic(0).
-/

namespace SolidCore.Solidity.Witness.ModifierReturnArgument

open SolidCore.Solidity.Source
open SolidCore.Solidity.TypeCheck

private def num (s : String) : Expr := Expr.literal (Literal.number s)

private def mod1 : ContractItem :=
  ContractItem.modifierDecl
    { name := "mod1",
      params :=
        [ { name := some "a", ty := Ty.uint 256, location := none }
        , { name := some "b", ty := Ty.bool, location := none } ],
      body := some (Stmt.block
        [Stmt.ifElse (Expr.ident "b") Stmt.modifierPlaceholder none]) }

private def mod2 : ContractItem :=
  ContractItem.modifierDecl
    { name := "mod2",
      params := [{ name := some "a", ty := Ty.bytesN 7, location := none }],
      body := some (Stmt.block
        [Stmt.whileLoop
          (Expr.binary BinaryOp.eq (Expr.ident "a")
            (Expr.literal (Literal.string "1234567")))
          Stmt.modifierPlaceholder]) }

private def f : ContractItem :=
  ContractItem.function
    { kind := FunctionKind.function, name := some "f",
      visibility := some Visibility.public_, mutability := StateMutability.pure,
      params := [{ name := some "a", ty := Ty.uint 8, location := none }],
      returns := [{ name := some "r", ty := Ty.bytesN 7, location := none }],
      modifiers :=
        [ { target := { segments := ["mod1"] },
            args := [Arg.positional (Expr.ident "a"),
                     Arg.positional (Expr.literal (Literal.bool true))],
            hasArgList := true }
        , { target := { segments := ["mod2"] },
            args := [Arg.positional (Expr.ident "r")],
            hasArgList := true } ],
      body := some (Stmt.block []) }

def contract : ContractDecl :=
  { kind := ContractKind.contract, name := "B", abstract := false,
    bases := [], items := [f, mod1, mod2] }

private def isOkTrue : Except TypeError Bool -> Bool
  | Except.ok true => true
  | _ => false

def returns_default_zero : Except TypeError Bool :=
  Examples.checkedOwnCallWordMatches 128 contract "f" State.empty
    [Value.word 5] 0

#guard isOkTrue returns_default_zero

end SolidCore.Solidity.Witness.ModifierReturnArgument

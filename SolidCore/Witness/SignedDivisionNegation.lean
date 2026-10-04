import SolidCore.Solidity.Checked
import SolidCore.Witness.Checked

set_option maxHeartbeats 8000000

/-! A signed division under unary minus remains executable after ABI
annotation inserts an explicit signed cast around its literal divisor. -/

namespace SolidCore.Solidity.Witness.SignedDivisionNegation

open SolidCore.Solidity
open SolidCore.Solidity.TypeCheck

private def num (n : String) : Expr := Expr.literal (Literal.number n)
private def i256 (expr : Expr) : Expr :=
  Expr.call (Expr.typeName (Ty.int 256)) [Arg.positional expr]

private def initializer : Expr :=
  Expr.unary UnaryOp.neg
    (Expr.binary BinaryOp.div (i256 (num "1")) (num "2"))

private def result : Expr :=
  Expr.call (Expr.typeName (Ty.uint 256))
    [Arg.positional (Expr.binary BinaryOp.add (Expr.ident "fraction") (num "1"))]

def contract : ContractDecl :=
  { kind := ContractKind.contract
    name := "C"
    items :=
      [ContractItem.function
        { kind := FunctionKind.function
          name := some "run"
          visibility := some Visibility.external_
          mutability := StateMutability.pure
          returns := [{ name := none, ty := Ty.uint 256 }]
          body := some (Stmt.block
            [Stmt.varDecl
              [{ name := some "fraction", ty := Ty.int 256, location := none }]
              (some initializer),
             Stmt.returnValues (some result)]) }] }

def sourceUnit : SourceUnit :=
  { items := [SourceItem.pragma "solidity" "0.8.35",
              SourceItem.contract contract] }

def accepted : Bool :=
  TypeCheck.Result.isOk
    (TypeCheck.TypecheckedInput.checkedSourceUnit sourceUnit)

private def isOkTrue : Except TypeError Bool -> Bool
  | Except.ok true => true
  | _ => false

def returnMatches : Except TypeError Bool :=
  Examples.checkedOwnCallWordMatches 4096 contract "run" Source.State.empty [] 1

#guard accepted
#guard isOkTrue returnMatches

end SolidCore.Solidity.Witness.SignedDivisionNegation

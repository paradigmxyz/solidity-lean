import SolidCore.Solidity.Checked
import SolidCore.Witness.Checked
import SolidCore.Witness.TypeCheck

set_option maxHeartbeats 8000000

/-!
NARROW-SIGNED-COMPARISON-IN-CONDITION (C, typecheck over-reject).

solc 0.8.35 accepts `int8(-1) != int8(0)` and the EVM runs it to `true`; the
submitted program returns `1`. solidity-lean FAILED CLOSED at typecheck with
`TypeError.expectedType (Ty.int 8) (Ty.int 8)` — the printed expected and actual
types coincide because the operands are two *typed* `int8` values, yet the error
came from the constant-comparison mobile-type gate.

Root cause: the `==`/`!=` and `<`/`<=`/`>`/`>=` arms of `checkExpr` unconditionally
ran `numberComparisonFoldable?` on the raw operands. That gate reproduces solc's
rule that two UNTYPED rational constants must share a common mobile type (so
opposite-sign `-1 != 0` is rejected). But `numberLiteralRat?` folds *through* an
explicit conversion (`int8(-1)` → the rational `-1`), so the gate mistook two
concrete `int8` values for an opposite-sign untyped pair and rejected a valid
typed comparison. In solc an explicit conversion yields a concrete typed value,
not a `rational_const`, so the mobile-type gate never applies to it.

Fix: gate `numberComparisonFoldable?` behind
`exprIsUntypedNumberLiteralExpression` on BOTH operands (that predicate already
does not recurse into a conversion). Untyped opposite-sign pairs stay rejected;
typed conversions fall through to the normal type-compatibility checks. One
change per comparison arm covers all nine boolean-condition positions (they all
route through the same `checkExpr` comparison node).

Below: run witnesses proving the accepted programs return `1`, plus typecheck
controls pinning that the untyped opposite-sign twin STAYS rejected and same-sign
untyped folding STAYS accepted.
-/

namespace SolidCore
namespace Solidity
namespace Witness
namespace NarrowSignedComparisonCondition

open SolidCore.Solidity.Source
open SolidCore.Solidity.TypeCheck

-- `int8(e)` explicit conversion.
private def int8 (e : Solidity.Expr) : Solidity.Expr :=
  Solidity.Expr.call (Solidity.Expr.typeName (Solidity.Ty.int 8))
    [Solidity.Arg.positional e]
private def num (s : String) : Solidity.Expr := Solidity.Expr.literal (Solidity.Literal.number s)
private def neg (e : Solidity.Expr) : Solidity.Expr := Solidity.Expr.unary Solidity.UnaryOp.neg e
private def cmp (op : Solidity.BinaryOp) (l r : Solidity.Expr) : Solidity.Expr :=
  Solidity.Expr.binary op l r

-- `int8(-1)` and `int8(0)`.
private def m1 : Solidity.Expr := int8 (neg (num "1"))
private def z : Solidity.Expr := int8 (num "0")

private def assignR (v : String) : Solidity.Stmt :=
  Solidity.Stmt.expr
    (Solidity.Expr.assign (Solidity.Expr.ident "r") Solidity.AssignOp.assign (num v))

private def runFn (body : Solidity.Stmt) : Solidity.ContractItem :=
  Solidity.ContractItem.function
    { kind := Solidity.FunctionKind.function, name := some "run",
      visibility := some Solidity.Visibility.public_,
      mutability := Solidity.StateMutability.pure,
      params := [],
      returns := [{ name := none, ty := Solidity.Ty.uint 256, location := none }],
      body := some body }

-- The submitted program: `uint256 r = 0; if (int8(-1) != int8(0)) r = 1; else r = 2; return r;`
private def ifBody : Solidity.Stmt :=
  Solidity.Stmt.block
    [ Solidity.Stmt.varDecl [{ name := some "r", ty := some (Solidity.Ty.uint 256) }] (some (num "0"))
    , Solidity.Stmt.ifElse (cmp Solidity.BinaryOp.ne m1 z)
        (Solidity.Stmt.block [assignR "1"])
        (some (Solidity.Stmt.block [assignR "2"]))
    , Solidity.Stmt.returnValues (some (Solidity.Expr.ident "r")) ]

-- Ternary condition: `return int8(-1) != int8(0) ? 1 : 2;`
private def ternaryBody : Solidity.Stmt :=
  Solidity.Stmt.returnValues
    (some (Solidity.Expr.ternary (cmp Solidity.BinaryOp.ne m1 z) (num "1") (num "2")))

-- require position: `require(int8(-1) != int8(0)); return 1;`
private def requireBody : Solidity.Stmt :=
  Solidity.Stmt.block
    [ Solidity.Stmt.expr
        (Solidity.Expr.call (Solidity.Expr.ident "require")
          [Solidity.Arg.positional (cmp Solidity.BinaryOp.ne m1 z)])
    , Solidity.Stmt.returnValues (some (num "1")) ]

-- Ordered comparison (covers the `<`/`<=`/`>`/`>=` arm): `int8(-1) < int8(0)` is true.
private def ltBody : Solidity.Stmt :=
  Solidity.Stmt.returnValues
    (some (Solidity.Expr.ternary (cmp Solidity.BinaryOp.lt m1 z) (num "1") (num "2")))

private def contractOf (body : Solidity.Stmt) : Solidity.ContractDecl :=
  { kind := Solidity.ContractKind.contract, name := "T",
    abstract := false, bases := [], items := [runFn body] }

def ifContract : Solidity.ContractDecl := contractOf ifBody
def ternaryContract : Solidity.ContractDecl := contractOf ternaryBody
def requireContract : Solidity.ContractDecl := contractOf requireBody
def ltContract : Solidity.ContractDecl := contractOf ltBody

private def isOkTrue : Except TypeError Bool -> Bool
  | Except.ok true => true
  | _ => false

-- Each accepted program runs to the observable `1` (matches solc+EVM).
def if_returns_one : Except TypeError Bool :=
  Examples.checkedOwnCallWordMatches 300 ifContract "run" State.empty [] 1
def ternary_returns_one : Except TypeError Bool :=
  Examples.checkedOwnCallWordMatches 300 ternaryContract "run" State.empty [] 1
def require_returns_one : Except TypeError Bool :=
  Examples.checkedOwnCallWordMatches 300 requireContract "run" State.empty [] 1
def lt_returns_one : Except TypeError Bool :=
  Examples.checkedOwnCallWordMatches 300 ltContract "run" State.empty [] 1

-- Typecheck controls: the untyped opposite-sign twin STAYS rejected, and
-- same-sign untyped literal folding STAYS accepted (no over-accept regression).
private def suOf (body : Solidity.Stmt) : Solidity.SourceUnit :=
  { items := [Solidity.SourceItem.pragma "solidity" "^0.8.35",
              Solidity.SourceItem.contract (contractOf body)] }

-- `return -1 != 0 ? 1 : 2;`  (untyped mixed-sign — solc REJECTS; must stay rejected)
def untypedMixedSignRejected : Bool :=
  !(Result.isOk (TypecheckedInput.checkedSourceUnit
      (suOf (Solidity.Stmt.returnValues
        (some (Solidity.Expr.ternary
          (cmp Solidity.BinaryOp.ne (neg (num "1")) (num "0")) (num "1") (num "2")))))))

-- `return 1 != 2 ? 1 : 2;`  (untyped same-sign — solc ACCEPTS; must stay accepted)
def untypedSameSignAccepted : Bool :=
  Result.isOk (TypecheckedInput.checkedSourceUnit
    (suOf (Solidity.Stmt.returnValues
      (some (Solidity.Expr.ternary
        (cmp Solidity.BinaryOp.ne (num "1") (num "2")) (num "1") (num "2"))))))

#guard isOkTrue if_returns_one
#guard isOkTrue ternary_returns_one
#guard isOkTrue require_returns_one
#guard isOkTrue lt_returns_one
#guard untypedMixedSignRejected
#guard untypedSameSignAccepted

end NarrowSignedComparisonCondition
end Witness
end Solidity
end SolidCore

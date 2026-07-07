/-
A1 rational-constant witnesses.

Named boolean checks referenced by the `rational-constants` corpus lane in
`tests/forge-harness/manifest.json`. They pin the A1 fix on the Lean side:

  * the three formerly over-rejected negative constants now fold to solc's
    exact signed value and are accepted into `int256`, and
  * the rejection boundary still holds — a genuinely-fractional constant into an
    integer type, and a negative folded value into an unsigned type, both stay
    rejected (the Int-widening must not over-correct into unsoundness).

Kept in the built library so `lake build SolidCore` regression-guards them.
-/
import SolidCore.Solidity.Interface

namespace SolidCore
namespace Solidity
namespace Executable
namespace RationalConstants

private def num (s : String) : Expr := Expr.literal (Literal.number s)
private def subE (x y : Expr) : Expr := Expr.binary BinaryOp.sub x y
private def mulE (x y : Expr) : Expr := Expr.binary BinaryOp.mul x y
private def divE (x y : Expr) : Expr := Expr.binary BinaryOp.div x y

-- N_FRACNEG source expression: 7 / 2 * 2 - 100  (folds to -93 in exact ℚ).
private def fracNegExpr : Expr :=
  subE (mulE (divE (num "7") (num "2")) (num "2")) (num "100")

-- The three A1 over-rejects: each now folds to solc's exact signed value.
def negFiveFolds : Bool :=
  Expr.numberLiteralInt? (subE (num "0") (num "5")) == some (-5)

def negSubFolds : Bool :=
  Expr.numberLiteralInt? (subE (num "3") (num "10")) == some (-7)

def fracNegFolds : Bool :=
  Expr.numberLiteralInt? fracNegExpr == some (-93)

-- And each is now accepted into int256 (was rejected before the widening).
def fracNegAcceptedInt256 : Bool :=
  (Expr.toCoreNumericLiteralAs? (Ty.int 256) fracNegExpr).isSome

-- Rejection boundary #1: a genuinely-fractional constant into an integer type
-- must stay rejected (no truncation to 3).
def fractionalIntoIntRejected : Bool :=
  (Expr.toCoreNumericLiteralAs? (Ty.int 256) (divE (num "7") (num "2"))).isNone

-- Rejection boundary #2: a negative folded value into an unsigned type must
-- stay rejected (solc rule (3): signed literal -> unsigned type).
def negIntoUintRejected : Bool :=
  (Expr.toCoreNumericLiteralAs? (Ty.uint 256) (subE (num "0") (num "1"))).isNone

end RationalConstants
end Executable
end Solidity
end SolidCore

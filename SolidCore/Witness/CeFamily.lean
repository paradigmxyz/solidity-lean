/-
CE-family constant-folder witnesses.

Named boolean checks referenced by the `cefamily` corpus lane in
`tests/forge-harness/manifest.json`. They pin, on the Lean side:

  * the CE-1..CE-6b over-rejects now fold to solc's exact folded value (negative
    exponents, unary `~`, negative shift/bitwise operands with SAR floor,
    fractional `%`, fractional denominated literals), and
  * the CE-6a over-accepts are now rejected exactly as solc rejects them: the
    4096-bit / uint32 resource caps make the fold fail, `~0` fails closed into an
    unsigned type, and a comparison of two literals with no common mobile type is
    no longer folded.

Every folded value here was cross-checked against pinned solc 0.8.35's AST
`typeString` (see `docs/solc-const-eval-env-review.md`). Kept in the built
library so `lake build SolidCore` regression-guards them.
-/
import SolidCore.Solidity.Interface

namespace SolidCore
namespace Solidity
namespace Executable
namespace CeFamily

private def num (s : String) : Expr := Expr.literal (Literal.number s)
private def weiLit (s : String) : Expr :=
  Expr.literal (Literal.unitNumber s UnitDenomination.wei)
private def neg (x : Expr) : Expr := Expr.unary UnaryOp.neg x
private def bnot (x : Expr) : Expr := Expr.unary UnaryOp.bitNot x
private def bin (op : BinaryOp) (x y : Expr) : Expr := Expr.binary op x y

private def foldsTo (e : Expr) (v : Int) : Bool :=
  Expr.numberLiteralInt? e == some v

-- CE-1: negative constant exponents (incl. the 0**-1 = 0 base short-circuit).
def p1Folds : Bool := foldsTo (bin BinaryOp.mul (num "4")
  (bin BinaryOp.exp (num "2") (neg (num "1")))) 2
def p17Folds : Bool := foldsTo (bin BinaryOp.mul
  (bin BinaryOp.exp (num "2") (neg (num "2"))) (num "16")) 4
def p2Folds : Bool := foldsTo (bin BinaryOp.exp (num "0") (neg (num "1"))) 0

-- CE-2a: unary ~ folded on integer rationals.
def p10Folds : Bool := foldsTo (bnot (num "5")) (-6)
def p15Folds : Bool := foldsTo (bnot (neg (num "3"))) 2
def x250Folds : Bool := foldsTo (bin BinaryOp.bitAnd (bnot (num "5")) (num "0xFF")) 250

-- CE-3: negative operands in constant shifts/bitwise; SAR floors toward -inf.
def p6Folds : Bool := foldsTo (bin BinaryOp.shl (neg (num "1")) (num "2")) (-4)
def p7Folds : Bool := foldsTo (bin BinaryOp.shr (neg (num "7")) (num "1")) (-4)
def p8Folds : Bool := foldsTo (bin BinaryOp.shr (neg (num "1")) (num "100")) (-1)
def p12Folds : Bool := foldsTo (bin BinaryOp.bitOr (neg (num "4")) (num "1")) (-3)

-- CE-4: fractional constant %.
def p9Folds : Bool := foldsTo (bin BinaryOp.mod (num "7") (num "2.5")) 2

-- CE-5: fractional denominated literal (0.5 wei * 2 = 1).
def p14Folds : Bool := foldsTo (bin BinaryOp.mul (weiLit "0.5") (num "2")) 1

-- CE-6b: bases 0/1/-1 fold without materializing the exponent (no hang).
def p5Folds : Bool :=
  foldsTo (bin BinaryOp.exp (num "1") (bin BinaryOp.exp (num "2") (num "100"))) 1
def pzpFolds : Bool :=
  foldsTo (bin BinaryOp.exp (num "0") (bin BinaryOp.exp (num "10") (num "60"))) 0
def pnpFolds : Bool :=
  foldsTo (bin BinaryOp.exp (neg (num "1")) (bin BinaryOp.exp (num "2") (num "100"))) 1

-- Accepted comparisons still fold (guard against over-rejecting).
def cmp1lt2Foldable : Bool :=
  Expr.numberComparisonFoldable? (num "1") (num "2")
-- #117 FRAC-CMP: a fractional-vs-fractional comparison (`1/2 == 0.5`) is REJECTED
-- by solc 0.8.35 ("Not yet implemented - FixedPointType."), so it is NOT foldable.
def cmpHalfEqRejected : Bool :=
  !(Expr.numberComparisonFoldable?
    (bin BinaryOp.div (num "1") (num "2")) (num "0.5"))

-- CE-2b: ~0 into an unsigned type fails closed (folds to -1, does not fit, and is
-- a raw literal so lowering rejects instead of evaluating ~0 at runtime).
def tildeZeroIntoUintRejected : Bool :=
  (Expr.toCoreNumericLiteralAs? (Ty.uint 256) (bnot (num "0"))).isNone &&
    Expr.isRawNumberLiteralExpression (bnot (num "0"))

-- ~0 into a *signed* type still accepts and folds to -1 (parity with solc).
def tildeZeroIntoIntAccepted : Bool :=
  (Expr.toCoreNumericLiteralAs? (Ty.int 256) (bnot (num "0"))).isSome

-- CE-6a: resource caps make the fold fail (⇒ the constant is rejected).
def expPrecisionRejected : Bool :=
  (Expr.numberLiteralRat?
    (bin BinaryOp.div (bin BinaryOp.exp (num "2") (num "5000"))
      (bin BinaryOp.exp (num "2") (num "5000")))).isNone
def literalExponentRejected : Bool :=
  (Expr.numberLiteralRat? (num "1e2000")).isNone
def shiftPrecisionRejected : Bool :=
  (Expr.numberLiteralRat?
    (bin BinaryOp.shr (bin BinaryOp.shl (num "1") (num "4200")) (num "4200"))).isNone
def shiftExponentCapRejected : Bool :=
  (Expr.numberLiteralRat?
    (bin BinaryOp.shl (num "0") (bin BinaryOp.exp (num "2") (num "33")))).isNone

-- CE-6a: comparisons whose operands lack a common mobile type are no longer
-- foldable (the checker rejects them).
def compareOutOfRangeRejected : Bool :=
  !(Expr.numberComparisonFoldable?
    (bin BinaryOp.exp (num "2") (num "300")) (bin BinaryOp.exp (num "2") (num "301")))
def compareNoCommonTypeRejected : Bool :=
  !(Expr.numberComparisonFoldable? (bin BinaryOp.div (num "1") (num "2")) (num "1"))

-- One conjunction the manifest can pin as a single eval.
def allCeFamilyWitnesses : Bool :=
  p1Folds && p17Folds && p2Folds &&
    p10Folds && p15Folds && x250Folds &&
    p6Folds && p7Folds && p8Folds && p12Folds &&
    p9Folds && p14Folds &&
    p5Folds && pzpFolds && pnpFolds &&
    cmp1lt2Foldable && cmpHalfEqRejected &&
    tildeZeroIntoUintRejected && tildeZeroIntoIntAccepted &&
    expPrecisionRejected && literalExponentRejected &&
    shiftPrecisionRejected && shiftExponentCapRejected &&
    compareOutOfRangeRejected && compareNoCommonTypeRejected

end CeFamily
end Executable
end Solidity
end SolidCore

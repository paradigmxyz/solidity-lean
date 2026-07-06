import SolidCore.Solidity.Interface
open SolidCore.Solidity
open SolidCore.Solidity.Executable

def n (s : String) : Expr := Expr.literal (Literal.number s)
def u (s : String) (d : UnitDenomination) : Expr := Expr.literal (Literal.unitNumber s d)
def b (op : BinaryOp) (x y : Expr) : Expr := Expr.binary op x y
def ng (x : Expr) : Expr := Expr.unary UnaryOp.neg x

-- Show folded rational (num/den) for the raw fold, before any fit check.
#eval Expr.numberLiteralRat? (n "1e18")                         -- SCI_1E18
#eval Expr.numberLiteralRat? (n "1.5e3")                        -- SCI_1_5E3
#eval Expr.numberLiteralRat? (b BinaryOp.mul (n "2e-2") (n "100")) -- SCI_2EM2X
#eval Expr.numberLiteralRat? (u "1" UnitDenomination.ether)     -- D_ETHER
#eval Expr.numberLiteralRat? (u "3" UnitDenomination.gwei)      -- D_GWEI
#eval Expr.numberLiteralRat? (b BinaryOp.add (u "2" UnitDenomination.minutes) (u "30" UnitDenomination.seconds)) -- D_MIXTIME
#eval Expr.numberLiteralRat? (b BinaryOp.mul (b BinaryOp.div (u "1" UnitDenomination.ether) (n "3")) (n "3")) -- F_ETHER3
#eval Expr.numberLiteralRat? (b BinaryOp.mul (b BinaryOp.div (n "7") (n "2")) (n "2")) -- F_7_2_2
#eval Expr.numberLiteralRat? (b BinaryOp.div (b BinaryOp.exp (n "2") (n "256")) (b BinaryOp.exp (n "2") (n "255"))) -- P_256_255
#eval Expr.numberLiteralRat? (b BinaryOp.add (b BinaryOp.div (n "1") (n "2")) (b BinaryOp.div (n "1") (n "2"))) -- M_HALFSUM

-- Typed accept/reject + value via the checker's fit function.
-- ACCEPTS into uint256:
#eval Expr.toCoreNumericLiteralAs? (Ty.uint 256) (n "1e18")                       -- expect word 1e18
#eval Expr.toCoreNumericLiteralAs? (Ty.uint 256) (b BinaryOp.mul (b BinaryOp.div (n "7") (n "2")) (n "2")) -- expect word 7
#eval Expr.toCoreNumericLiteralAs? (Ty.uint 256) (b BinaryOp.mul (b BinaryOp.div (u "1" UnitDenomination.ether) (n "3")) (n "3")) -- expect word 1e18
#eval Expr.toCoreNumericLiteralAs? (Ty.uint 256) (b BinaryOp.add (b BinaryOp.div (n "1") (n "2")) (b BinaryOp.div (n "1") (n "2"))) -- M_HALFSUM expect word 1
-- ACCEPTS into int256 (negatives):
#eval Expr.toCoreNumericLiteralAs? (Ty.int 256) (b BinaryOp.sub (n "0") (n "5"))  -- N_NEG5 expect -5
#eval Expr.toCoreNumericLiteralAs? (Ty.int 256) (b BinaryOp.sub (n "3") (n "10")) -- N_SUB expect -7
#eval Expr.toCoreNumericLiteralAs? (Ty.int 256) (b BinaryOp.sub (b BinaryOp.mul (b BinaryOp.div (n "7") (n "2")) (n "2")) (n "100")) -- N_FRACNEG expect -93
#eval Expr.toCoreNumericLiteralAs? (Ty.int 256) (ng (n "3"))                      -- N_UNARY expect -3
#eval Expr.toCoreNumericLiteralAs? (Ty.int 8) (ng (n "128"))                      -- B_I8_MIN expect -128
-- fit boundary:
#eval Expr.toCoreNumericLiteralAs? (Ty.uint 8) (n "255")                          -- expect 255
#eval Expr.toCoreNumericLiteralAs? (Ty.uint 8) (n "256")                          -- expect none (reject)

-- REJECTS (expect none):
#eval Expr.toCoreNumericLiteralAs? (Ty.uint 256) (b BinaryOp.div (n "7") (n "2")) -- r01
#eval Expr.toCoreNumericLiteralAs? (Ty.uint 256) (n "1.5")                        -- r02
#eval Expr.toCoreNumericLiteralAs? (Ty.uint 256) (n "2e-2")                       -- r03
#eval Expr.toCoreNumericLiteralAs? (Ty.uint 8) (n "1e18")                         -- r04
#eval Expr.toCoreNumericLiteralAs? (Ty.uint 256) (b BinaryOp.sub (n "0") (n "1")) -- r05 neg into uint
#eval Expr.toCoreNumericLiteralAs? (Ty.int 8) (ng (n "129"))                      -- r08 i8 underflow

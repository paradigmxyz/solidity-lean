/-
MULMOD0 acceptance-boundary witnesses (2026-07-09).

solc 0.8.35's constant evaluator (`ConstantEvaluator.cpp`) folds the modulus
argument of `addmod`/`mulmod` and raises Error 4195 "Arithmetic modulo zero"
whenever it folds to a constant zero — regardless of whether the other operands
are constant. solidity-lean formerly ACCEPTED a compile-time-constant zero
modulus and produced a runtime Panic 0x12. These witnesses pin the tightened
boundary on the Lean side:

  * `addmod(_,_,0)` / `mulmod(_,_,0)` with a constant-zero modulus (a literal
    `0`, or a constant expression like `1 - 1` that folds to zero) is now
    REJECTED by the typechecker, and
  * the neighbors solc still ACCEPTS — a NON-constant modulus (`mulmod(2,3,m)`
    with `m` a parameter, whose runtime zero stays a Panic 0x12) and a constant
    NON-zero modulus (`mulmod(2,3,7)`) — stay accepted; the tightening must not
    over-reject.

The paired solc-REJECT `.sol` fixtures live under
`tests/forge-harness/mulmod-zero/invalid/` and are compiled by the differential
harness to confirm pinned solc rejects them. Helpers (`su_singleContract`,
`simpleReturnFunction`, `su_uint256`, `numberExpr`, `SourceUnit.check`,
`Result.isError`, `sourceUnitAccepted?`) come from `SolidCore.Witness.TypeCheck`.
-/
import SolidCore.Witness.TypeCheck

namespace SolidCore
namespace Solidity
namespace TypeCheck
namespace Examples

open Solidity

-- `name(a, b, modulus)` as a builtin-ident call expression.
private def modCall (name : Name) (a b modulus : Expr) : Expr :=
  Expr.call (Expr.ident name)
    [ Arg.positional a, Arg.positional b, Arg.positional modulus ]

private def two : Expr := numberExpr "2"
private def three : Expr := numberExpr "3"
private def zero : Expr := numberExpr "0"
-- `1 - 1`: a constant EXPRESSION that folds to zero (must still be caught).
private def exprZero : Expr := Expr.binary BinaryOp.sub (numberExpr "1") (numberExpr "1")

private def returnModCall (name : Name) (modulus : Expr)
    (params : List Solidity.Parameter) : Solidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "f"
    params := params
    returns := [{ name := none, ty := su_uint256, location := none }]
    body :=
      some (Solidity.Stmt.returnValues (some (modCall name two three modulus))) }

-- REJECTED: constant-zero modulus (literal 0).
def mulmodConstantZeroFn : Solidity.FunctionDecl := returnModCall "mulmod" zero []
def addmodConstantZeroFn : Solidity.FunctionDecl := returnModCall "addmod" zero []

def mulmodConstantZeroRejected : Bool :=
  Result.isError (SourceUnit.check (su_singleContract "MulmodZero" mulmodConstantZeroFn))

def addmodConstantZeroRejected : Bool :=
  Result.isError (SourceUnit.check (su_singleContract "AddmodZero" addmodConstantZeroFn))

-- REJECTED: constant EXPRESSION modulus that folds to zero (`1 - 1`).
def mulmodConstantExprZeroFn : Solidity.FunctionDecl := returnModCall "mulmod" exprZero []
def addmodConstantExprZeroFn : Solidity.FunctionDecl := returnModCall "addmod" exprZero []

def mulmodConstantExprZeroRejected : Bool :=
  Result.isError
    (SourceUnit.check (su_singleContract "MulmodExprZero" mulmodConstantExprZeroFn))

def addmodConstantExprZeroRejected : Bool :=
  Result.isError
    (SourceUnit.check (su_singleContract "AddmodExprZero" addmodConstantExprZeroFn))

-- ACCEPTED neighbor: NON-constant modulus (parameter `m`); runtime zero stays a
-- Panic 0x12, not a compile error.
def mulmodRuntimeModulusFn : Solidity.FunctionDecl :=
  returnModCall "mulmod" (Expr.ident "m")
    [{ name := some "m", ty := su_uint256, location := none }]

def mulmodRuntimeModulusAccepted : Bool :=
  sourceUnitAccepted? (su_singleContract "MulmodRuntime" mulmodRuntimeModulusFn)

-- ACCEPTED neighbor: constant NON-zero modulus.
def mulmodConstantNonzeroFn : Solidity.FunctionDecl :=
  returnModCall "mulmod" (numberExpr "7") []

def mulmodConstantNonzeroAccepted : Bool :=
  sourceUnitAccepted? (su_singleContract "MulmodNonzero" mulmodConstantNonzeroFn)

-- Whole boundary in one flag.
def mulmodZeroBoundaryHolds : Bool :=
  mulmodConstantZeroRejected &&
    addmodConstantZeroRejected &&
    mulmodConstantExprZeroRejected &&
    addmodConstantExprZeroRejected &&
    mulmodRuntimeModulusAccepted &&
    mulmodConstantNonzeroAccepted

end Examples
end TypeCheck
end Solidity
end SolidCore

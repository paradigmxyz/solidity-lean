import SolidCore.Solidity.Checked
import SolidCore.Witness.Checked

set_option maxHeartbeats 8000000

/-!
NEGATED-FRACTIONAL-LITERAL (coverage gap, over-reject): a NEGATED FRACTIONAL
literal (a rational constant such as `-1.5`) anywhere in a constant expression
must lower as an untyped rational constant — solc `-` on a `RationalNumberType`
yields a (negated) `RationalNumberType`, valid for any rational operand:

  function f() external pure returns (int256) {
    return -1.5 * 2;
  }

solc 0.8.35 + EVM: folds `-1.5 * 2 = -3`, returns int256 `-3`
(`0xff…fd`). solidity-lean USED TO fail closed at typecheck with
`expectedInteger (uint256)`: the unary-`neg` arm only accepted an INTEGRAL
negated literal (`-3`), and a fractional operand fell into a signed-operand
`require` that rejects the `uint256` a bare fractional literal is typed as.
Fixed: the negation of any untyped number-literal (rational-constant) operand
is accepted, carrying the operand's literal type; a fractional value survives
only where it folds to an integer downstream (so `return -1.5 * 2` types and
runs, while a bare `return -1.5;` still fails the implicit-fit).
-/

namespace SolidCore
namespace Solidity
namespace Witness
namespace NegatedFractionalLiteral

open SolidCore.Solidity.Source
open SolidCore.Solidity.TypeCheck

private def i256 : Ty := Ty.int 256
private def lit (s : String) : Expr := Expr.literal (Literal.number s)

-- return -1.5 * 2  ==  (neg 1.5) * 2
private def body : Expr :=
  Expr.binary BinaryOp.mul
    (Expr.unary UnaryOp.neg (lit "1.5"))
    (lit "2")

private def fFn : FunctionDecl :=
  { kind := FunctionKind.function, name := some "f"
    visibility := some Visibility.external_, mutability := StateMutability.pure
    params := [], returns := [{ name := none, ty := i256, location := none }]
    virtual := false, override? := none, modifiers := []
    body := some (Stmt.block [ Stmt.returnValues (some body) ]) }

def runContract : ContractDecl :=
{ kind := ContractKind.contract, name := "C", abstract := false, bases := []
  items := [ ContractItem.function fFn ] }

def runSourceUnit : SourceUnit :=
  { items := [SourceItem.pragma "solidity" "^0.8.35", SourceItem.contract runContract] }

def accepted : Bool :=
  TypeCheck.Result.isOk (TypeCheck.TypecheckedInput.checkedSourceUnit runSourceUnit)

open SolidCore.Solidity.Source in
def rawResult : Except TypeError (CallResult) :=
  CheckedInput.ownCall 4096 runContract (CallTarget.name "f") State.empty []

-- signedToWord (-3) = 2^256 - 3 = 0xff…fd, matching the EVM measurement
-- (`0xff…fd`). The returned int256 value carries a `Value.int` payload.
open SolidCore.Solidity.Source in
def run_result : Except TypeError Bool := do
  let result ← rawResult
  match result with
  | CallResult.returned _ [Value.int v] =>
      Except.ok (wordEq v (SolidCore.Solidity.Shared.signedToWord (-3)))
  | CallResult.returned _ [Value.word v] =>
      Except.ok (wordEq v (SolidCore.Solidity.Shared.signedToWord (-3)))
  | _ => Except.ok false

private def isOkTrue : Except TypeError Bool → Bool
  | Except.ok true => true
  | _ => false

open SolidCore.Solidity.Source in
def describe : String :=
  match rawResult with
  | Except.error _ => "typeerror"
  | Except.ok (CallResult.returned _ vs) => s!"returned {repr vs}"
  | Except.ok (CallResult.reverted _ w) => s!"reverted {repr w}"

#eval accepted
#eval run_result
#eval describe

#guard accepted
#guard isOkTrue run_result

end NegatedFractionalLiteral
end Witness
end Solidity
end SolidCore

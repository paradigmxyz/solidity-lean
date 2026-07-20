import SolidCore.Solidity.Checked
import SolidCore.Witness.Checked

set_option maxHeartbeats 8000000

/-!
TERNARY-LITERAL-VAR-WIDTH-UNIFY — a conditional whose branches are an untyped
number literal and a typed integer variable of a NARROWER width
(`c ? 300 : a` with `a : uint8`).

solc `TypeChecker::visit(Conditional)` sets the conditional's type to the
`commonType` of the branch types. An untyped number-literal branch contributes
its `mobileType()` (`RationalNumberType::mobileType`, `Types.cpp:1210`) — the
SMALLEST-fitting `uintN`/`intN` — NOT the `uint256` that a checked literal gets.
So `300`'s mobile type is `uint16`, and `commonType(uint16, uint8) = uint16`.
solc ACCEPTS `return c ? 300 : a;` for a `uint16` return, and `run(true)` returns
`300` (`0x12c`).

solidity-lean formerly FAILED CLOSED at typecheck on this in-scope program:
`TypeError.expectedType (uint 16) (uint 256)`. Root cause: the ternary result
type only substituted the mobile type when BOTH branches were untyped literals
(`untypedLiteralMobileTy? expr`). In the mixed case it fell back to the raw
branch types, where the literal `300` is the checked `uint256` from `literalTy?`,
so the conditional typed as `uint256` and would not implicitly convert to the
declared `uint16`. The fix mirrors the binary-operand handling
(`commonArrayElementTy?`): substitute each untyped-literal branch's mobile type,
then take the common implicit type — `commonImplicit?(uint16, uint8) = uint16`.

Runtime word is pinned with `#guard` (real-EVM ground truth per the adjudicator
measurement: `run(true)` returns `0x12c` = 300). Neighbor controls keep the
tightening honest: a narrower `uint8` return still rejects (the `uint16` common
type is not implicitly convertible to `uint8`), and the else branch
(`run(false)`) still returns `a`'s value `7`.
-/

namespace SolidCore
namespace Solidity
namespace SolcAstImport
namespace TernaryLiteralVarWidthUnify

open SolidCore.Solidity.Source

private def num (s : String) : Expr := Expr.literal (Literal.number s)

-- `c ? 300 : a` — literal `300` (mobile `uint16`) meets `a : uint8` → common `uint16`.
private def litVarTernary : Expr :=
  Expr.ternary (Expr.ident "c") (num "300") (Expr.ident "a")

-- The submission's `run`:
--   function run(bool c) external pure returns (uint16) {
--     uint8 a = 7;
--     return c ? 300 : a;
--   }
private def runFn : ContractItem := ContractItem.function
  { kind := FunctionKind.function, name := some "run",
    visibility := some Visibility.external_, mutability := StateMutability.pure,
    params := [{ name := some "c", ty := Ty.bool, location := none }],
    returns := [{ name := none, ty := Ty.uint 16, location := none }],
    virtual := false, override? := none, modifiers := [],
    body := some (Stmt.block
      [ Stmt.varDecl [{ name := some "a", ty := Ty.uint 8, location := none }]
          (some (num "7"))
      , Stmt.returnValues (some litVarTernary) ]) }

def submissionContract : ContractDecl :=
  { kind := ContractKind.contract, name := "C",
    abstract := false, bases := [], items := [runFn] }

def submissionSourceUnit : SourceUnit :=
  { items := [SourceItem.pragma "solidity" "0.8.35",
      SourceItem.contract submissionContract] }

def submissionAccepted : Bool :=
  TypeCheck.Result.isOk (TypeCheck.TypecheckedInput.checkedSourceUnit submissionSourceUnit)

-- NEIGHBOR CONTROL (must REJECT): declaring the same conditional as the NARROWER
-- `uint8` return — solc rejects (`uint16` common type is not implicitly
-- convertible to `uint8`), and so must we.
private def narrowFn : ContractItem := ContractItem.function
  { kind := FunctionKind.function, name := some "run",
    visibility := some Visibility.external_, mutability := StateMutability.pure,
    params := [{ name := some "c", ty := Ty.bool, location := none }],
    returns := [{ name := none, ty := Ty.uint 8, location := none }],
    virtual := false, override? := none, modifiers := [],
    body := some (Stmt.block
      [ Stmt.varDecl [{ name := some "a", ty := Ty.uint 8, location := none }]
          (some (num "7"))
      , Stmt.returnValues (some litVarTernary) ]) }

def narrowSourceUnit : SourceUnit :=
  { items := [SourceItem.pragma "solidity" "0.8.35",
      SourceItem.contract
        { kind := ContractKind.contract, name := "C",
          abstract := false, bases := [], items := [narrowFn] }] }

def narrowRejected : Bool :=
  TypeCheck.Result.isError (TypeCheck.TypecheckedInput.checkedSourceUnit narrowSourceUnit)

end TernaryLiteralVarWidthUnify
end SolcAstImport
end Solidity
end SolidCore

namespace SolidCore
namespace Solidity
namespace Witness
namespace TernaryLiteralVarWidthUnify

open SolidCore.Solidity.Source
open SolidCore.Solidity.TypeCheck

abbrev Fam := SolidCore.Solidity.SolcAstImport.TernaryLiteralVarWidthUnify.submissionContract

def accepted : Bool :=
  SolidCore.Solidity.SolcAstImport.TernaryLiteralVarWidthUnify.submissionAccepted

def narrowRejected : Bool :=
  SolidCore.Solidity.SolcAstImport.TernaryLiteralVarWidthUnify.narrowRejected

-- `run(true)`: the `300` branch → the conditional value `300` = `0x12c` (the
-- adjudicator's measured EVM return data).
def run_true_is_300 : Except TypeError Bool :=
  Examples.checkedOwnCallWordMatches 256 Fam "run" State.empty
    [Value.word 1] 300

-- `run(false)`: the `a` branch → `a`'s value `7`.
def run_false_is_7 : Except TypeError Bool :=
  Examples.checkedOwnCallWordMatches 256 Fam "run" State.empty
    [Value.word 0] 7

private def isOkTrue : Except TypeError Bool -> Bool
  | Except.ok true => true
  | _ => false

#guard accepted
#guard narrowRejected
#guard isOkTrue run_true_is_300
#guard isOkTrue run_false_is_7

end TernaryLiteralVarWidthUnify
end Witness
end Solidity
end SolidCore

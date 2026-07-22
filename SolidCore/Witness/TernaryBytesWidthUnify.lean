import SolidCore.Solidity.Checked
import SolidCore.Witness.Checked

set_option maxHeartbeats 8000000

/-!
TERNARY-BYTES-WIDTH-UNIFY — a conditional whose two branches are fixed-bytes
values of DIFFERENT widths (`x < 5 ? bytes1(0xAA) : bytes2(0xBBCC)`).

solc `TypeChecker::visit(Conditional)` unifies the branch types by their COMMON
type: `commonType(bytes1, bytes2) = bytes2` (`FixedBytesType::isImplicitlyConvertibleTo`
is widening — `bytes1` right-pads to `bytes2`, so `0xAA` becomes `0xAA00`). So
solc ACCEPTS `bytes2 c = x < 5 ? bytes1(0xAA) : bytes2(0xBBCC);` and, for `run(3)`,
`abi.encodePacked(c)` is the two bytes `0xAA00`.

solidity-lean formerly FAILED CLOSED at typecheck on this in-scope program:
`TypeError.expectedType (bytesN 2) (uint 16)`. Root cause: the ternary result
type used `Expr.untypedLiteralMobileTy?`, whose base case folded through an
explicit `T(x)` conversion via `numberLiteralRat?` and so reported a TYPED branch
`bytes2(0xBBCC)` as an untyped `uint16` literal (the whole conditional's "mobile
type" became `uint16`, which is not implicitly convertible to the declared
`bytes2`). The fix bases `untypedLiteralMobileTy?` on the STRICT
`untypedNumberLiteralRat?` (no conversion / enum folding), matching the function's
documented contract ("Returns none for … a typed conversion branch") and solc:
a typed conversion branch now yields `none`, so the conditional falls back to the
branches' common implicit type (`bytes2`).

Runtime bytes are pinned with `#guard` (real-EVM ground truth per the adjudicator
measurement: `run(3)` returns `0xAA00`). Negative/neighbor controls keep the
tightening honest: a narrower `bytes1` target still rejects, and a pure
untyped-literal conditional still adopts its common mobile type.
-/

namespace SolidCore
namespace Solidity
namespace SolcAstImport
namespace TernaryBytesWidthUnify

open SolidCore.Solidity.Source

private def num (s : String) : Expr := Expr.literal (Literal.number s)
private def conv (t : Ty) (e : Expr) : Expr :=
  Expr.call (Expr.typeName t) [Arg.positional e]
private def encodePacked (e : Expr) : Expr :=
  Expr.call (Expr.member (Expr.ident "abi") "encodePacked") [Arg.positional e]

-- `x < 5 ? bytes1(0xAA) : bytes2(0xBBCC)` — common type bytes2 (bytes1 right-pads).
private def widthUnifyTernary : Expr :=
  Expr.ternary
    (Expr.binary BinaryOp.lt (Expr.ident "x") (num "5"))
    (conv (Ty.bytesN 1) (num "0xAA"))
    (conv (Ty.bytesN 2) (num "0xBBCC"))

-- The submission's `run`:
--   function run(uint256 x) external pure returns (bytes memory) {
--     if (x == 0) return "";
--     bytes2 c = x < 5 ? bytes1(0xAA) : bytes2(0xBBCC);
--     return abi.encodePacked(c);
--   }
private def runFn : ContractItem := ContractItem.function
  { kind := FunctionKind.function, name := some "run",
    visibility := some Visibility.external_, mutability := StateMutability.pure,
    params := [{ name := some "x", ty := Ty.uint 256, location := none }],
    returns := [{ name := none, ty := Ty.bytes, location := some DataLocation.memory }],
    virtual := false, override? := none, modifiers := [],
    body := some (Stmt.block
      [ Stmt.ifElse (Expr.binary BinaryOp.eq (Expr.ident "x") (num "0"))
          (Stmt.returnValues (some (Expr.literal (Literal.string "")))) none
      , Stmt.varDecl [{ name := some "c", ty := Ty.bytesN 2, location := none }]
          (some widthUnifyTernary)
      , Stmt.returnValues (some (encodePacked (Expr.ident "c"))) ]) }

def submissionContract : ContractDecl :=
  { kind := ContractKind.contract, name := "C",
    abstract := false, bases := [], items := [runFn] }

def submissionSourceUnit : SourceUnit :=
  { items := [SourceItem.pragma "solidity" "^0.8.35",
      SourceItem.contract submissionContract] }

def submissionAccepted : Bool :=
  TypeCheck.Result.isOk (TypeCheck.TypecheckedInput.checkedSourceUnit submissionSourceUnit)

-- NEIGHBOR CONTROL (must REJECT): declaring the same conditional as the NARROWER
-- `bytes1` — solc rejects (`bytes2` common type is not implicitly convertible to
-- `bytes1`), and so must we.
private def narrowFn : ContractItem := ContractItem.function
  { kind := FunctionKind.function, name := some "run",
    visibility := some Visibility.external_, mutability := StateMutability.pure,
    params := [{ name := some "x", ty := Ty.uint 256, location := none }],
    returns := [{ name := none, ty := Ty.bytesN 1, location := none }],
    virtual := false, override? := none, modifiers := [],
    body := some (Stmt.block
      [ Stmt.varDecl [{ name := some "c", ty := Ty.bytesN 1, location := none }]
          (some widthUnifyTernary)
      , Stmt.returnValues (some (Expr.ident "c")) ]) }

def narrowSourceUnit : SourceUnit :=
  { items := [SourceItem.pragma "solidity" "^0.8.35",
      SourceItem.contract
        { kind := ContractKind.contract, name := "C",
          abstract := false, bases := [], items := [narrowFn] }] }

def narrowRejected : Bool :=
  TypeCheck.Result.isError (TypeCheck.TypecheckedInput.checkedSourceUnit narrowSourceUnit)

-- NEIGHBOR CONTROL (must ACCEPT, mobile type preserved): a pure untyped-literal
-- conditional `(x < 5 ? 63 : 255)` still adopts its common mobile type `uint8`
-- (fits the declared `uint16`) — the fix does not disturb genuine literals.
private def mobileFn : ContractItem := ContractItem.function
  { kind := FunctionKind.function, name := some "run",
    visibility := some Visibility.external_, mutability := StateMutability.pure,
    params := [{ name := some "x", ty := Ty.uint 256, location := none }],
    returns := [{ name := none, ty := Ty.uint 16, location := none }],
    virtual := false, override? := none, modifiers := [],
    body := some (Stmt.block
      [ Stmt.varDecl [{ name := some "c", ty := Ty.uint 16, location := none }]
          (some (Expr.ternary
            (Expr.binary BinaryOp.lt (Expr.ident "x") (num "5"))
            (num "63") (num "255")))
      , Stmt.returnValues (some (Expr.ident "c")) ]) }

def mobileSourceUnit : SourceUnit :=
  { items := [SourceItem.pragma "solidity" "^0.8.35",
      SourceItem.contract
        { kind := ContractKind.contract, name := "C",
          abstract := false, bases := [], items := [mobileFn] }] }

def mobileAccepted : Bool :=
  TypeCheck.Result.isOk (TypeCheck.TypecheckedInput.checkedSourceUnit mobileSourceUnit)

end TernaryBytesWidthUnify
end SolcAstImport
end Solidity
end SolidCore

namespace SolidCore
namespace Solidity
namespace Witness
namespace TernaryBytesWidthUnify

open SolidCore.Solidity.Source
open SolidCore.Solidity.TypeCheck

abbrev Fam := SolidCore.Solidity.SolcAstImport.TernaryBytesWidthUnify.submissionContract

def accepted : Bool :=
  SolidCore.Solidity.SolcAstImport.TernaryBytesWidthUnify.submissionAccepted

def narrowRejected : Bool :=
  SolidCore.Solidity.SolcAstImport.TernaryBytesWidthUnify.narrowRejected

def mobileAccepted : Bool :=
  SolidCore.Solidity.SolcAstImport.TernaryBytesWidthUnify.mobileAccepted

-- `run(3)`: x < 5 → the `bytes1(0xAA)` branch, widened to `bytes2` = 0xAA00.
-- `abi.encodePacked(bytes2(0xAA00))` = the two bytes 0xAA 0x00 (the adjudicator's
-- measured EVM return data).
def run_3_is_aa00 : Except TypeError Bool :=
  Examples.checkedOwnCallBytesMatches 256 Fam "run" State.empty
    [Value.word 3] [0xAA, 0x00]

-- `run(7)`: x ≥ 5 → the `bytes2(0xBBCC)` branch = 0xBBCC.
def run_7_is_bbcc : Except TypeError Bool :=
  Examples.checkedOwnCallBytesMatches 256 Fam "run" State.empty
    [Value.word 7] [0xBB, 0xCC]

-- `run(0)`: the guard returns the empty `bytes`.
def run_0_is_empty : Except TypeError Bool :=
  Examples.checkedOwnCallBytesMatches 256 Fam "run" State.empty
    [Value.word 0] []

private def isOkTrue : Except TypeError Bool -> Bool
  | Except.ok true => true
  | _ => false

#guard accepted
#guard narrowRejected
#guard mobileAccepted
#guard isOkTrue run_3_is_aa00
#guard isOkTrue run_7_is_bbcc
#guard isOkTrue run_0_is_empty

end TernaryBytesWidthUnify
end Witness
end Solidity
end SolidCore

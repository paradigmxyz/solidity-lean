import SolidCore.Solidity.Checked
import SolidCore.Witness.Checked

set_option maxHeartbeats 8000000

/-!
LITERAL-BASE-WIDE-TYPE — a literal base of `**` or a literal left operand of a shift
with a NON-literal right operand (`4 ** k`, `1 << k` with `uint8 k`).

Since Solidity 0.7.0 such an operation is computed in `uint256` (`int256` for a
negative literal), not in the literal's mobile type: solc 0.8.35's AST types `4 ** k` as
`uint256` and the base `int_const 4` takes `uint256` too. solidity-lean formerly
typed the expression at the base's mobile type (`4` → `uint8`) in the ABI typers
(`Expr.abiTy?`, `Expr.abiTyWithEnv?`), so a lowering that read the expression's type there
ran it at 8 bits: `4 ** 4` wrapped (or panicked) at 256 where solc and the EVM give 256.

Witnesses: `4 ** k` at `k = 4` is 256; `1 << k` at `k = 8` is 256; and verify/arith's
comparison `4 ** k == 2 ** (2 * uint256(k))`, inside `unchecked`, holds at `k = 4`.
-/

namespace SolidCore
namespace Solidity
namespace SolcAstImport
namespace LiteralBaseWideType

open SolidCore.Solidity.Source

private def num (s : String) : Expr := Expr.literal (Literal.number s)

private def fn (name : String) (ret : Ty) (body : Stmt) : ContractItem := ContractItem.function
  { kind := FunctionKind.function, name := some name,
    visibility := some Visibility.external_, mutability := StateMutability.pure,
    params := [{ name := some "k", ty := Ty.uint 8, location := none }],
    returns := [{ name := none, ty := ret, location := none }],
    virtual := false, override? := none, modifiers := [],
    body := some (Stmt.block [body]) }

-- function pow(uint8 k) external pure returns (uint256) { return 4 ** k; }
private def powFn : ContractItem :=
  fn "pow" (Ty.uint 256) (Stmt.returnValues (some (Expr.binary BinaryOp.exp (num "4") (Expr.ident "k"))))

-- function shl(uint8 k) external pure returns (uint256) { return 1 << k; }
private def shlFn : ContractItem :=
  fn "shl" (Ty.uint 256) (Stmt.returnValues (some (Expr.binary BinaryOp.shl (num "1") (Expr.ident "k"))))

-- function cmp(uint8 k) external pure returns (bool) {
--   unchecked { return 4 ** k == 2 ** (2 * uint256(k)); } }
private def cmpFn : ContractItem :=
  fn "cmp" Ty.bool (Stmt.unchecked (Stmt.block [Stmt.returnValues (some
    (Expr.binary BinaryOp.eq (Expr.binary BinaryOp.exp (num "4") (Expr.ident "k"))
      (Expr.binary BinaryOp.exp (num "2")
        (Expr.binary BinaryOp.mul (num "2")
          (Expr.call (Expr.typeName (Ty.uint 256)) [Arg.positional (Expr.ident "k")])))))]))

def submissionContract : ContractDecl :=
  { kind := ContractKind.contract, name := "C",
    abstract := false, bases := [], items := [powFn, shlFn, cmpFn] }

def submissionSourceUnit : SourceUnit :=
  { items := [SourceItem.pragma "solidity" "0.8.35",
      SourceItem.contract submissionContract] }

def submissionAccepted : Bool :=
  TypeCheck.Result.isOk (TypeCheck.TypecheckedInput.checkedSourceUnit submissionSourceUnit)

end LiteralBaseWideType
end SolcAstImport
end Solidity
end SolidCore

namespace SolidCore
namespace Solidity
namespace Witness
namespace LiteralBaseWideType

open SolidCore.Solidity.Source
open SolidCore.Solidity.TypeCheck

abbrev Fam := SolidCore.Solidity.SolcAstImport.LiteralBaseWideType.submissionContract

def accepted : Bool := SolidCore.Solidity.SolcAstImport.LiteralBaseWideType.submissionAccepted

/-- `4 ** 4 = 256`: computed in `uint256`, so neither wrapped nor a Panic(0x11). -/
def pow_4_is_256 : Except TypeError Bool :=
  Examples.checkedOwnCallWordMatches 256 Fam "pow" State.empty [Value.word 4] 256

/-- `1 << 8 = 256`. -/
def shl_8_is_256 : Except TypeError Bool :=
  Examples.checkedOwnCallWordMatches 256 Fam "shl" State.empty [Value.word 8] 256

/-- verify/arith's `ok_pow_lit_base` comparison holds at `k = 4`: `256 == 256`. -/
def cmp_4_holds : Except TypeError Bool :=
  Examples.checkedOwnCallWordMatches 256 Fam "cmp" State.empty [Value.word 4] 1

private def isOkTrue : Except TypeError Bool -> Bool
  | Except.ok true => true
  | _ => false

#guard accepted
#guard isOkTrue pow_4_is_256
#guard isOkTrue shl_8_is_256
#guard isOkTrue cmp_4_holds

end LiteralBaseWideType
end Witness
end Solidity
end SolidCore

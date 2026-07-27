import SolidCore.Solidity.Checked
import SolidCore.Witness.Checked

set_option maxHeartbeats 8000000

/-!
CONST-DIV-BY-CAST-ZERO (#64) — `1 / uint256(0)` over-rejected at typecheck.

solc raises the constant division/modulo-by-zero error (Error 2271,
`TypeChecker::binaryOperatorResult`, TypeChecker.cpp:1709-1712) ONLY when BOTH
operands are `RationalNumberType` — i.e. untyped number literals (or folds of
them). An explicit `T(x)` conversion produces a TYPED `IntegerType`, so the fold
does not fire: `1 / uint256(0)` is a runtime division and pinned solc 0.8.35
ACCEPTS it, reverting at runtime with Panic 0x12 (division by zero).

solidity-lean formerly gated the div/mod arm on `Expr.numberLiteralRat?`, which
looks THROUGH an explicit `T(x)` conversion (and `enumFromUInt`) and so folded
the typed divisor `uint256(0)` into a constant-zero rational — over-rejecting
`1 / uint256(0)` at typecheck with `constant division or modulo by zero`. The fix
switches the gate to the STRICT `Expr.untypedNumberLiteralRat?` (no `T(x)` /
`enumFromUInt` arm), so a typed divisor yields `none` and stays a runtime Panic
0x12, while a genuine untyped constant-zero divisor (`1 / 0`, `1 / (2 - 2)`)
stays rejected exactly as solc rejects it.

Ground truth (EVM): `f()` reverts Panic 0x12. `#eval`-confirmed, pinned `#guard`.
-/

namespace SolidCore
namespace Solidity
namespace SolcAstImport
namespace ConstDivByCastZero

def importedContractDecl0 : ContractDecl :=
{ kind := ContractKind.contract
  name := "T"
  abstract := false
  bases := []
  items := [(ContractItem.function
  { kind := FunctionKind.function,
    name := some "f",
    visibility := some Visibility.external_,
    mutability := StateMutability.pure,
    params := [],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some
      (Expr.binary BinaryOp.div
        (Expr.literal (Literal.number "1"))
        (Expr.call (Expr.typeName (Ty.uint 256))
          [Arg.positional (Expr.literal (Literal.number "0"))])))]) })] }

def importedContract : ContractDecl :=
  importedContractDecl0

def importedSourceUnit : SourceUnit :=
  { items := [SourceItem.pragma "solidity" "^0.8.35", SourceItem.contract importedContractDecl0] }

def importedContractAccepted : Bool :=
  TypeCheck.Result.isOk (TypeCheck.TypecheckedInput.checkedSourceUnit importedSourceUnit)

end ConstDivByCastZero
end SolcAstImport
end Solidity
end SolidCore

namespace SolidCore
namespace Solidity
namespace Witness
namespace ConstDivByCastZero

open SolidCore.Solidity.Source
open SolidCore.Solidity.TypeCheck

abbrev Fam := SolidCore.Solidity.SolcAstImport.ConstDivByCastZero.importedContract

-- The imported contract type-checks (accepted): `1 / uint256(0)` is a runtime
-- division, NOT a constant fold, so the div-by-zero gate must not fire.
def accepted : Bool :=
  SolidCore.Solidity.SolcAstImport.ConstDivByCastZero.importedContractAccepted

-- Runtime observable: `f()` reverts with Panic 0x12 (division by zero).
def f_panics_0x12 : Except TypeError Bool :=
  Examples.checkedOwnCallPanicMatches 64 Fam "f" State.empty [] 0x12

-- Acceptance ISOLATION LADDER. Single pure `f() returns (rt) { return e; }`.
private def lit (s : String) : Expr := Expr.literal (Literal.number s)

private def castTo (t : Ty) (e : Expr) : Expr :=
  Expr.call (Expr.typeName t) [Arg.positional e]

private def mkUnit (rt : Ty) (e : Expr) : SourceUnit :=
  let fn : ContractItem := ContractItem.function
    { kind := FunctionKind.function,
      name := some "f",
      visibility := some Visibility.public_,
      mutability := StateMutability.pure,
      params := [],
      returns := [{ name := none, ty := rt, location := none }],
      virtual := false, override? := none, modifiers := [],
      body := some (Stmt.block [Stmt.returnValues (some e)]) }
  let c : ContractDecl :=
    { kind := ContractKind.contract, name := "C", abstract := false,
      bases := [], items := [fn] }
  { items := [SourceItem.pragma "solidity" "^0.8.35", SourceItem.contract c] }

private def accepts (rt : Ty) (e : Expr) : Bool :=
  TypeCheck.Result.isOk (TypeCheck.TypecheckedInput.checkedSourceUnit (mkUnit rt e))

private def u256 : Ty := Ty.uint 256

-- Must be ACCEPT (were over-rejected before the fix): a TYPED zero divisor via a
-- `T(x)` cast is a runtime division, not a constant fold.
def acc_div_castZero : Bool :=
  accepts u256 (Expr.binary BinaryOp.div (lit "1") (castTo u256 (lit "0")))
def acc_mod_castZero : Bool :=
  accepts u256 (Expr.binary BinaryOp.mod (lit "1") (castTo u256 (lit "0")))
-- A typed dividend too (`uint256(1) / uint256(0)`), and mixed literal dividend.
def acc_div_bothCast : Bool :=
  accepts u256 (Expr.binary BinaryOp.div (castTo u256 (lit "1")) (castTo u256 (lit "0")))
-- Narrower typed operands (`int8(1) / int8(0)`) — also runtime, also accepted.
def acc_div_int8Cast : Bool :=
  accepts (Ty.int 8) (Expr.binary BinaryOp.div (castTo (Ty.int 8) (lit "1")) (castTo (Ty.int 8) (lit "0")))

-- Must stay REJECT (no over-accept traded in): a genuine UNTYPED constant-zero
-- divisor still folds and is rejected exactly as solc rejects it.
def rej_div_litZero : Bool :=
  accepts u256 (Expr.binary BinaryOp.div (lit "1") (lit "0"))
def rej_mod_litZero : Bool :=
  accepts u256 (Expr.binary BinaryOp.mod (lit "1") (lit "0"))
def rej_div_foldedZero : Bool :=
  accepts u256 (Expr.binary BinaryOp.div (lit "1") (Expr.binary BinaryOp.sub (lit "2") (lit "2")))

private def isOkTrue : Except TypeError Bool → Bool
  | Except.ok true => true
  | _ => false

#guard accepted
#guard isOkTrue f_panics_0x12

#guard acc_div_castZero
#guard acc_mod_castZero
#guard acc_div_bothCast
#guard acc_div_int8Cast

#guard !rej_div_litZero
#guard !rej_mod_litZero
#guard !rej_div_foldedZero

end ConstDivByCastZero
end Witness
end Solidity
end SolidCore

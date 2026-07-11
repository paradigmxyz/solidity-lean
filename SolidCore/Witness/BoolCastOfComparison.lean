import SolidCore.Solidity.Checked
import SolidCore.Witness.Checked

set_option maxHeartbeats 8000000

/-!
BOOL-CAST-OF-COMPARISON (#165) — `bool(1 == 2)` is an IDENTITY conversion.

A comparison/equality/logical operator over untyped number literals folds to a
`bool` constant (solc `RationalNumberType` → `BoolType`), NOT to a rational
number. So `bool(boolExpr)` is a bool→bool identity conversion, which pinned
solc 0.8.35 ACCEPTS: `bool(1==2)`, `bool(1<2)`, `bool(1<2 && 2<3)`,
`bool(!(1==2))`.

solidity-lean formerly classified ANY `Expr.binary _ lhs rhs` over untyped
number literals as an untyped NUMBER literal (no operator restriction), so a
comparison was mislabeled a number; `Ty.canExplicitlyConvert`'s
untyped-number-literal branch then preempted the `actual == target` identity
fast-path and, finding no numeric target for `bool`, over-rejected with
`invalidConversion bool bool`. The fix restricts the binary arm of
`exprIsUntypedNumberLiteralExpression` to ARITHMETIC/BITWISE operators only
(`+ - * / % ** & | ^ << >>`) — the ones that genuinely yield a number.
Comparison/equality/logical operators are excluded, so `bool(1==2)` reaches the
identity fast-path and is accepted. Arithmetic-literal casts (`uint8(1+2)`,
`uint16(1<<3)`) stay classified as untyped numbers, so their numeric-target
conversions and range checks are unchanged.

Real-EVM Forge ground truth: `tests/forge-harness/bool-cast-of-comparison`.
`#eval`-confirmed booleans pinned with `#guard`.
-/

namespace SolidCore
namespace Solidity
namespace SolcAstImport
namespace BoolCastOfComparison

def importedSourceName : String :=
  "tests/forge-harness/bool-cast-of-comparison/src/BoolCastOfComparison.sol"

def importedContractDecl0 : ContractDecl :=
{ kind := ContractKind.contract
  name := "BoolCastOfComparisonTarget"
  abstract := false
  bases := []
  items := [(ContractItem.function
  { kind := FunctionKind.function,
    name := some "eqCast",
    visibility := some Visibility.external_,
    mutability := StateMutability.pure,
    params := [],
    returns := [{ name := none, ty := Ty.bool, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.call (Expr.typeName (Ty.bool)) [Arg.positional (Expr.binary BinaryOp.eq (Expr.literal (Literal.number "1")) (Expr.literal (Literal.number "2")))]))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "ltCast",
    visibility := some Visibility.external_,
    mutability := StateMutability.pure,
    params := [],
    returns := [{ name := none, ty := Ty.bool, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.call (Expr.typeName (Ty.bool)) [Arg.positional (Expr.binary BinaryOp.lt (Expr.literal (Literal.number "1")) (Expr.literal (Literal.number "2")))]))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "andCast",
    visibility := some Visibility.external_,
    mutability := StateMutability.pure,
    params := [],
    returns := [{ name := none, ty := Ty.bool, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.call (Expr.typeName (Ty.bool)) [Arg.positional (Expr.binary BinaryOp.boolAnd (Expr.binary BinaryOp.lt (Expr.literal (Literal.number "1")) (Expr.literal (Literal.number "2"))) (Expr.binary BinaryOp.lt (Expr.literal (Literal.number "2")) (Expr.literal (Literal.number "3"))))]))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "notCast",
    visibility := some Visibility.external_,
    mutability := StateMutability.pure,
    params := [],
    returns := [{ name := none, ty := Ty.bool, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.call (Expr.typeName (Ty.bool)) [Arg.positional (Expr.unary UnaryOp.logicalNot (Expr.binary BinaryOp.eq (Expr.literal (Literal.number "1")) (Expr.literal (Literal.number "2"))))]))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "arithCast",
    visibility := some Visibility.external_,
    mutability := StateMutability.pure,
    params := [],
    returns := [{ name := none, ty := Ty.uint 8, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.call (Expr.typeName (Ty.uint 8)) [Arg.positional (Expr.binary BinaryOp.add (Expr.literal (Literal.number "1")) (Expr.literal (Literal.number "2")))]))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "shiftCast",
    visibility := some Visibility.external_,
    mutability := StateMutability.pure,
    params := [],
    returns := [{ name := none, ty := Ty.uint 16, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.call (Expr.typeName (Ty.uint 16)) [Arg.positional (Expr.binary BinaryOp.shl (Expr.literal (Literal.number "1")) (Expr.literal (Literal.number "3")))]))]) })] }

def importedContract : ContractDecl :=
  importedContractDecl0

def importedContracts : List ContractDecl :=
  [importedContractDecl0]

def importedSourceUnit : SourceUnit :=
  { items := [SourceItem.pragma "solidity" "^0.8.35", SourceItem.contract importedContractDecl0] }

def importedContractAccepted : Bool :=
  TypeCheck.Result.isOk (TypeCheck.TypecheckedInput.checkedSourceUnit importedSourceUnit)

end BoolCastOfComparison
end SolcAstImport
end Solidity
end SolidCore

namespace SolidCore
namespace Solidity
namespace Witness
namespace BoolCastOfComparison

open SolidCore.Solidity.Source
open SolidCore.Solidity.TypeCheck

abbrev Fam := SolidCore.Solidity.SolcAstImport.BoolCastOfComparison.importedContract

-- The source unit type-checks (accepted) — the four bool-cast forms plus the
-- two arithmetic-literal casts all pass the acceptance predicate.
def accepted : Bool :=
  SolidCore.Solidity.SolcAstImport.BoolCastOfComparison.importedContractAccepted

-- Runtime values (bool: false = word 0, true = word 1).
def eqCast_is_false : Except TypeError Bool :=
  Examples.checkedOwnCallWordMatches 256 Fam "eqCast" State.empty [] 0

def ltCast_is_true : Except TypeError Bool :=
  Examples.checkedOwnCallWordMatches 256 Fam "ltCast" State.empty [] 1

def andCast_is_true : Except TypeError Bool :=
  Examples.checkedOwnCallWordMatches 256 Fam "andCast" State.empty [] 1

def notCast_is_true : Except TypeError Bool :=
  Examples.checkedOwnCallWordMatches 256 Fam "notCast" State.empty [] 1

def arithCast_is_3 : Except TypeError Bool :=
  Examples.checkedOwnCallWordMatches 256 Fam "arithCast" State.empty [] 3

def shiftCast_is_8 : Except TypeError Bool :=
  Examples.checkedOwnCallWordMatches 256 Fam "shiftCast" State.empty [] 8

-- Acceptance ISOLATION LADDER via the acceptance predicate. Single pure
-- function `f(uint a, uint b) returns (rt) { return e; }`.
private def lit (s : String) : Expr := Expr.literal (Literal.number s)

private def mkUnit (rt : Ty) (e : Expr) : SourceUnit :=
  let fn : ContractItem := ContractItem.function
    { kind := FunctionKind.function,
      name := some "f",
      visibility := some Visibility.public_,
      mutability := StateMutability.pure,
      params := [{ name := some "a", ty := Ty.uint 256, location := none },
                 { name := some "b", ty := Ty.uint 256, location := none }],
      returns := [{ name := none, ty := rt, location := none }],
      virtual := false, override? := none, modifiers := [],
      body := some (Stmt.block [Stmt.returnValues (some e)]) }
  let c : ContractDecl :=
    { kind := ContractKind.contract, name := "C", abstract := false,
      bases := [], items := [fn] }
  { items := [SourceItem.pragma "solidity" "^0.8.35", SourceItem.contract c] }

private def accepts (rt : Ty) (e : Expr) : Bool :=
  TypeCheck.Result.isOk (TypeCheck.TypecheckedInput.checkedSourceUnit (mkUnit rt e))

private def castTo (t : Ty) (e : Expr) : Expr :=
  Expr.call (Expr.typeName t) [Arg.positional e]

-- Must be ACCEPT (were over-rejected before the fix).
def acc_bool_eq : Bool :=
  accepts Ty.bool (castTo Ty.bool (Expr.binary BinaryOp.eq (lit "1") (lit "2")))
def acc_bool_lt : Bool :=
  accepts Ty.bool (castTo Ty.bool (Expr.binary BinaryOp.lt (lit "1") (lit "2")))
def acc_bool_and : Bool :=
  accepts Ty.bool (castTo Ty.bool (Expr.binary BinaryOp.boolAnd
    (Expr.binary BinaryOp.lt (lit "1") (lit "2"))
    (Expr.binary BinaryOp.lt (lit "2") (lit "3"))))
def acc_bool_not : Bool :=
  accepts Ty.bool (castTo Ty.bool
    (Expr.unary UnaryOp.logicalNot (Expr.binary BinaryOp.eq (lit "1") (lit "2"))))
-- Must stay ACCEPT: comparison of variable operands, arithmetic/bitwise casts.
def acc_bool_var_eq : Bool :=
  accepts Ty.bool (castTo Ty.bool (Expr.binary BinaryOp.eq (Expr.ident "a") (Expr.ident "b")))
def acc_uint8_add : Bool :=
  accepts (Ty.uint 8) (castTo (Ty.uint 8) (Expr.binary BinaryOp.add (lit "1") (lit "2")))
def acc_uint16_shl : Bool :=
  accepts (Ty.uint 16) (castTo (Ty.uint 16) (Expr.binary BinaryOp.shl (lit "1") (lit "3")))
def acc_int8_neg : Bool :=
  accepts (Ty.int 8) (castTo (Ty.int 8) (Expr.unary UnaryOp.neg (lit "1")))

-- Must stay REJECT (no over-accept traded in).
def rej_uint8_eq : Bool :=
  accepts (Ty.uint 8) (castTo (Ty.uint 8) (Expr.binary BinaryOp.eq (lit "1") (lit "2")))
def rej_uint8_lt : Bool :=
  accepts (Ty.uint 8) (castTo (Ty.uint 8) (Expr.binary BinaryOp.lt (lit "1") (lit "2")))
def rej_bool_num1 : Bool :=
  accepts Ty.bool (castTo Ty.bool (lit "1"))
def rej_bool_num0 : Bool :=
  accepts Ty.bool (castTo Ty.bool (lit "0"))
def rej_bool_add : Bool :=
  accepts Ty.bool (castTo Ty.bool (Expr.binary BinaryOp.add (lit "1") (lit "1")))

private def isOkTrue : Except TypeError Bool → Bool
  | Except.ok true => true
  | _ => false

#guard accepted
#guard isOkTrue eqCast_is_false
#guard isOkTrue ltCast_is_true
#guard isOkTrue andCast_is_true
#guard isOkTrue notCast_is_true
#guard isOkTrue arithCast_is_3
#guard isOkTrue shiftCast_is_8

#guard acc_bool_eq
#guard acc_bool_lt
#guard acc_bool_and
#guard acc_bool_not
#guard acc_bool_var_eq
#guard acc_uint8_add
#guard acc_uint16_shl
#guard acc_int8_neg

#guard !rej_uint8_eq
#guard !rej_uint8_lt
#guard !rej_bool_num1
#guard !rej_bool_num0
#guard !rej_bool_add

end BoolCastOfComparison
end Witness
end Solidity
end SolidCore

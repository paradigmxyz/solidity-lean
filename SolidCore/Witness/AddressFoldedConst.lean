import SolidCore.Solidity.Checked
import SolidCore.Witness.Checked

set_option maxHeartbeats 8000000

/-!
ADDRESS-FOLDED-CONST-CONVERSION (#170) — `address(<folded-const-expr>)`.

solc `RationalNumberType::isExplicitlyConvertibleTo` (Types.cpp:1050) decides an
explicit conversion to a nonpayable `address` on the ALREADY-FOLDED `m_value`:

  m_value == 0 ||
    (!isNegative() && !isFractional() && integerType() && numBits() <= 160)

Literal-ness is irrelevant, so a constant-folded arithmetic argument is
convertible exactly when it folds to a non-negative integer `< 2 ^ 160`. Pinned
solc 0.8.35 therefore ACCEPTS `address(1 + 1)` (= 2), `address(2 * 3)` (= 6),
`address(0x1234 + 1)` (= 0x1235), `address(1 - 1)` (folds to 0, the always-
allowed `m_value == 0` branch), and `address(2 ** 160 - 1)` (the accepted
boundary, `numBits() == 160`). It REJECTS `address(0 - 1)` (isNegative),
`address(2 ** 160)` (numBits() == 161), and `address(1 / 2)` (isFractional).

solidity-lean formerly lowered the nonpayable-address arm via
`Expr.toCoreAddressLiteral?`, which only matched literal NODES (`Literal.address`
/ `number` / `unitNumber`) and returned `none` for any non-literal argument, so a
constant-folded arithmetic argument was over-rejected — even though the integer
path (`uint160(1 + 1)` via `toCoreNumericLiteralAs?` → `untypedNumberLiteralRat?`)
already folded. The fix adds a folding fallback to `Expr.toCoreAddressLiteral?`
mirroring the integer path: fold the untyped number-literal EXPRESSION, and when
it is a non-negative integer `< 2 ^ 160` lower to that runtime word. Negatives
(`isNegative`), fractions (`exactInt?` = none / `isFractional`), and out-of-range
values (`addressLiteralFits`, i.e. `numBits() <= 160`) stay rejected. `payable`
is a separate node (`Expr.payableConversion` → `Expr.toCorePayableLiteral?`,
which already folds only to the allowed `m_value == 0`) and is untouched.

Real-EVM Forge ground truth: `tests/forge-harness/address-folded-const`.
`#eval`-confirmed runtime words pinned with `#guard`.
-/

namespace SolidCore
namespace Solidity
namespace SolcAstImport
namespace AddressFoldedConst

def importedSourceName : String :=
  "tests/forge-harness/address-folded-const/src/AddressFoldedConst.sol"

def importedContractDecl0 : ContractDecl :=
{ kind := ContractKind.contract
  name := "AddressFoldedConstTarget"
  abstract := false
  bases := []
  items := [(ContractItem.function
  { kind := FunctionKind.function,
    name := some "addCast",
    visibility := some Visibility.external_,
    mutability := StateMutability.pure,
    params := [],
    returns := [{ name := none, ty := Ty.address false, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.call (Expr.typeName (Ty.address false)) [Arg.positional (Expr.binary BinaryOp.add (Expr.literal (Literal.number "1")) (Expr.literal (Literal.number "1")))]))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "mulCast",
    visibility := some Visibility.external_,
    mutability := StateMutability.pure,
    params := [],
    returns := [{ name := none, ty := Ty.address false, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.call (Expr.typeName (Ty.address false)) [Arg.positional (Expr.binary BinaryOp.mul (Expr.literal (Literal.number "2")) (Expr.literal (Literal.number "3")))]))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "hexAddCast",
    visibility := some Visibility.external_,
    mutability := StateMutability.pure,
    params := [],
    returns := [{ name := none, ty := Ty.address false, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.call (Expr.typeName (Ty.address false)) [Arg.positional (Expr.binary BinaryOp.add (Expr.literal (Literal.number "0x1234")) (Expr.literal (Literal.number "1")))]))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "subZeroCast",
    visibility := some Visibility.external_,
    mutability := StateMutability.pure,
    params := [],
    returns := [{ name := none, ty := Ty.address false, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.call (Expr.typeName (Ty.address false)) [Arg.positional (Expr.binary BinaryOp.sub (Expr.literal (Literal.number "1")) (Expr.literal (Literal.number "1")))]))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "maxCast",
    visibility := some Visibility.external_,
    mutability := StateMutability.pure,
    params := [],
    returns := [{ name := none, ty := Ty.address false, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.call (Expr.typeName (Ty.address false)) [Arg.positional (Expr.binary BinaryOp.sub (Expr.binary BinaryOp.exp (Expr.literal (Literal.number "2")) (Expr.literal (Literal.number "160"))) (Expr.literal (Literal.number "1")))]))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "plainLit",
    visibility := some Visibility.external_,
    mutability := StateMutability.pure,
    params := [],
    returns := [{ name := none, ty := Ty.address false, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.call (Expr.typeName (Ty.address false)) [Arg.positional (Expr.literal (Literal.number "2"))]))]) })] }

def importedContract : ContractDecl :=
  importedContractDecl0

def importedContracts : List ContractDecl :=
  [importedContractDecl0]

def importedSourceUnit : SourceUnit :=
  { items := [SourceItem.pragma "solidity" "^0.8.35", SourceItem.contract importedContractDecl0] }

def importedContractAccepted : Bool :=
  TypeCheck.Result.isOk (TypeCheck.TypecheckedInput.checkedSourceUnit importedSourceUnit)

end AddressFoldedConst
end SolcAstImport
end Solidity
end SolidCore

namespace SolidCore
namespace Solidity
namespace Witness
namespace AddressFoldedConst

open SolidCore.Solidity.Source
open SolidCore.Solidity.TypeCheck

abbrev Fam := SolidCore.Solidity.SolcAstImport.AddressFoldedConst.importedContract

-- The imported contract type-checks (accepted): every folded-constant address
-- cast passes the acceptance predicate.
def accepted : Bool :=
  SolidCore.Solidity.SolcAstImport.AddressFoldedConst.importedContractAccepted

-- Runtime words (address values; all fold to non-negative integers < 2 ^ 160,
-- so no 160-bit masking is required).
def addCast_is_2 : Except TypeError Bool :=
  Examples.checkedOwnCallWordMatches 256 Fam "addCast" State.empty [] 2

def mulCast_is_6 : Except TypeError Bool :=
  Examples.checkedOwnCallWordMatches 256 Fam "mulCast" State.empty [] 6

def hexAddCast_is_4661 : Except TypeError Bool :=
  Examples.checkedOwnCallWordMatches 256 Fam "hexAddCast" State.empty [] 4661

def subZeroCast_is_0 : Except TypeError Bool :=
  Examples.checkedOwnCallWordMatches 256 Fam "subZeroCast" State.empty [] 0

def maxCast_is_2pow160m1 : Except TypeError Bool :=
  Examples.checkedOwnCallWordMatches 256 Fam "maxCast" State.empty [] (2 ^ 160 - 1)

def plainLit_is_2 : Except TypeError Bool :=
  Examples.checkedOwnCallWordMatches 256 Fam "plainLit" State.empty [] 2

-- Acceptance ISOLATION LADDER via the acceptance predicate. Single pure function
-- `f() returns (rt) { return e; }` (no params: all operands are constants).
private def lit (s : String) : Expr := Expr.literal (Literal.number s)

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

private def castTo (t : Ty) (e : Expr) : Expr :=
  Expr.call (Expr.typeName t) [Arg.positional e]

private def addr : Ty := Ty.address false

-- Must be ACCEPT (were over-rejected before the fix): folded non-negative
-- integers < 2 ^ 160.
def acc_addr_add : Bool :=
  accepts addr (castTo addr (Expr.binary BinaryOp.add (lit "1") (lit "1")))
def acc_addr_mul : Bool :=
  accepts addr (castTo addr (Expr.binary BinaryOp.mul (lit "2") (lit "3")))
def acc_addr_hex : Bool :=
  accepts addr (castTo addr (Expr.binary BinaryOp.add (lit "0x1234") (lit "1")))
def acc_addr_subZero : Bool :=
  accepts addr (castTo addr (Expr.binary BinaryOp.sub (lit "1") (lit "1")))
def acc_addr_max : Bool :=
  accepts addr (castTo addr
    (Expr.binary BinaryOp.sub (Expr.binary BinaryOp.exp (lit "2") (lit "160")) (lit "1")))
-- Must stay ACCEPT: plain literal, and the integer path that already folded.
def acc_addr_plain : Bool := accepts addr (castTo addr (lit "2"))
def acc_uint160_add : Bool :=
  accepts (Ty.uint 160) (castTo (Ty.uint 160) (Expr.binary BinaryOp.add (lit "1") (lit "1")))
def acc_addr_of_uint160_add : Bool :=
  accepts addr (castTo addr (castTo (Ty.uint 160) (Expr.binary BinaryOp.add (lit "1") (lit "1"))))

-- Must stay REJECT (no over-accept traded in): negative, out-of-range,
-- fractional.
def rej_addr_neg : Bool :=
  accepts addr (castTo addr (Expr.binary BinaryOp.sub (lit "0") (lit "1")))
def rej_addr_overflow : Bool :=
  accepts addr (castTo addr (Expr.binary BinaryOp.exp (lit "2") (lit "160")))
def rej_addr_frac : Bool :=
  accepts addr (castTo addr (Expr.binary BinaryOp.div (lit "1") (lit "2")))

private def isOkTrue : Except TypeError Bool → Bool
  | Except.ok true => true
  | _ => false

#guard accepted
#guard isOkTrue addCast_is_2
#guard isOkTrue mulCast_is_6
#guard isOkTrue hexAddCast_is_4661
#guard isOkTrue subZeroCast_is_0
#guard isOkTrue maxCast_is_2pow160m1
#guard isOkTrue plainLit_is_2

#guard acc_addr_add
#guard acc_addr_mul
#guard acc_addr_hex
#guard acc_addr_subZero
#guard acc_addr_max
#guard acc_addr_plain
#guard acc_uint160_add
#guard acc_addr_of_uint160_add

#guard !rej_addr_neg
#guard !rej_addr_overflow
#guard !rej_addr_frac

end AddressFoldedConst
end Witness
end Solidity
end SolidCore

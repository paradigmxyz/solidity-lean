import SolidCore.Solidity.Checked
import SolidCore.Witness.Checked

set_option maxHeartbeats 8000000

/-!
A binary whose one operand carries a nested internal call (`g() / 5`) and
whose other operand is call-free is lowered by hoisting the call and combining
the result with the pure operand in a residual binary. The pure operand must be
evaluated at its own Solidity width: `~uint8(p)` is the uint8 value
`255 - uint8(p)` and `p << 4` on a uint8 `p` wraps at 8 bits.

In a multi-value return such as `return ((g() / 5) - ~uint8(p), 1)` with
`p = 2^256 - 1`, solc computes `~uint8(p) = 0` and returns `(1, 1)`. The
hoisted lowering used the env-less lowering for the pure operand, which flips
all 256 bits for `~` (and does not wrap `<<`), so the checked subtraction
underflowed and the call reverted with Panic 0x11. The pure operand now goes
through the env-aware lowering, like the direct-call operand arms already did.

Controls: a direct call operand (`g() - ~uint8(p)`), narrow checked
arithmetic in the pure operand, and a genuine underflow (`p = 0`) keep their
semantics.

```solidity
contract C {
    function g() internal pure returns (uint8) { return 5; }
    function lhsNested(uint256 p) external pure returns (uint8, uint256) {
        return ((g() / 5) - ~uint8(p), 1);
    }
    function rhsNested(uint256 p) external pure returns (uint8, uint256) {
        return (~uint8(p) + (g() / 5), 1);
    }
    function shlNested(uint8 p) external pure returns (uint8, uint256) {
        return ((g() / 5) + (p << 4), 1);
    }
    function directCall(uint256 p) external pure returns (uint8, uint256) {
        return (g() - ~uint8(p), 1);
    }
    function arithNested(uint8 p) external pure returns (uint8, uint256) {
        return ((g() / 5) + p * 2, 1);
    }
}
```
-/

namespace SolidCore
namespace Solidity
namespace SolcAstImport
namespace HoistedBinaryPureOperandCleanupWitness

def importedSourceName : String := "HoistedBinaryPureOperandCleanup.sol"

def importedContractDecl0 : ContractDecl :=
{ kind := ContractKind.contract
  name := "C"
  abstract := false
  bases := []
  items := [(ContractItem.function
  { kind := FunctionKind.function,
    name := some "g",
    visibility := some Visibility.internal_,
    mutability := StateMutability.pure,
    params := [],
    returns := [{ name := none, ty := Ty.uint 8, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.literal (Literal.number "5")))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "lhsNested",
    visibility := some Visibility.external_,
    mutability := StateMutability.pure,
    params := [{ name := some "p", ty := Ty.uint 256, location := none }],
    returns := [{ name := none, ty := Ty.uint 8, location := none }, { name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.tuple [TupleItem.value (Expr.binary BinaryOp.sub (Expr.binary BinaryOp.div (Expr.call (Expr.ident "g") []) (Expr.literal (Literal.number "5"))) (Expr.unary UnaryOp.bitNot (Expr.call (Expr.typeName (Ty.uint 8)) [Arg.positional (Expr.ident "p")]))), TupleItem.value (Expr.literal (Literal.number "1"))]))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "rhsNested",
    visibility := some Visibility.external_,
    mutability := StateMutability.pure,
    params := [{ name := some "p", ty := Ty.uint 256, location := none }],
    returns := [{ name := none, ty := Ty.uint 8, location := none }, { name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.tuple [TupleItem.value (Expr.binary BinaryOp.add (Expr.unary UnaryOp.bitNot (Expr.call (Expr.typeName (Ty.uint 8)) [Arg.positional (Expr.ident "p")])) (Expr.binary BinaryOp.div (Expr.call (Expr.ident "g") []) (Expr.literal (Literal.number "5")))), TupleItem.value (Expr.literal (Literal.number "1"))]))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "shlNested",
    visibility := some Visibility.external_,
    mutability := StateMutability.pure,
    params := [{ name := some "p", ty := Ty.uint 8, location := none }],
    returns := [{ name := none, ty := Ty.uint 8, location := none }, { name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.tuple [TupleItem.value (Expr.binary BinaryOp.add (Expr.binary BinaryOp.div (Expr.call (Expr.ident "g") []) (Expr.literal (Literal.number "5"))) (Expr.binary BinaryOp.shl (Expr.ident "p") (Expr.literal (Literal.number "4")))), TupleItem.value (Expr.literal (Literal.number "1"))]))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "directCall",
    visibility := some Visibility.external_,
    mutability := StateMutability.pure,
    params := [{ name := some "p", ty := Ty.uint 256, location := none }],
    returns := [{ name := none, ty := Ty.uint 8, location := none }, { name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.tuple [TupleItem.value (Expr.binary BinaryOp.sub (Expr.call (Expr.ident "g") []) (Expr.unary UnaryOp.bitNot (Expr.call (Expr.typeName (Ty.uint 8)) [Arg.positional (Expr.ident "p")]))), TupleItem.value (Expr.literal (Literal.number "1"))]))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "arithNested",
    visibility := some Visibility.external_,
    mutability := StateMutability.pure,
    params := [{ name := some "p", ty := Ty.uint 8, location := none }],
    returns := [{ name := none, ty := Ty.uint 8, location := none }, { name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.tuple [TupleItem.value (Expr.binary BinaryOp.add (Expr.binary BinaryOp.div (Expr.call (Expr.ident "g") []) (Expr.literal (Literal.number "5"))) (Expr.binary BinaryOp.mul (Expr.ident "p") (Expr.literal (Literal.number "2")))), TupleItem.value (Expr.literal (Literal.number "1"))]))]) })] }

def importedContract : ContractDecl :=
  importedContractDecl0

def importedContracts : List ContractDecl :=
  [importedContractDecl0]

def importedSourceUnit : SourceUnit :=
  { items := [SourceItem.pragma "solidity" "^0.8.28", SourceItem.contract importedContractDecl0] }

def importedContractAccepted : Bool :=
  TypeCheck.Result.isOk (TypeCheck.TypecheckedInput.checkedSourceUnit importedSourceUnit)

end HoistedBinaryPureOperandCleanupWitness
end SolcAstImport
end Solidity
end SolidCore

namespace SolidCore
namespace Solidity
namespace Witness
namespace HoistedBinaryPureOperandCleanup

open SolidCore.Solidity.Source
open SolidCore.Solidity.TypeCheck

abbrev Fam :=
  SolidCore.Solidity.SolcAstImport.HoistedBinaryPureOperandCleanupWitness.importedContract

def accepted : Bool :=
  SolidCore.Solidity.SolcAstImport.HoistedBinaryPureOperandCleanupWitness.importedContractAccepted

private def maxWord : Nat := 2 ^ 256 - 1

-- (g() / 5) - ~uint8(max) = 1 - 0 = 1 (was Panic 0x11).
def lhs_nested_is_one : Except TypeError Bool :=
  Examples.checkedOwnCallWordPairMatches 512 Fam "lhsNested" State.empty
    [Value.word maxWord] 1 1

-- ~uint8(max) + (g() / 5) = 0 + 1 = 1 (was Panic 0x11).
def rhs_nested_is_one : Except TypeError Bool :=
  Examples.checkedOwnCallWordPairMatches 512 Fam "rhsNested" State.empty
    [Value.word maxWord] 1 1

-- (g() / 5) + (uint8(255) << 4) = 1 + 0xf0 = 241 (was Panic 0x11).
def shl_nested_wraps : Except TypeError Bool :=
  Examples.checkedOwnCallWordPairMatches 512 Fam "shlNested" State.empty
    [Value.word 255] 241 1

-- CONTROL: direct call operand already lowered the pure side env-aware.
def direct_call_is_five : Except TypeError Bool :=
  Examples.checkedOwnCallWordPairMatches 512 Fam "directCall" State.empty
    [Value.word maxWord] 5 1

-- CONTROL: a genuine uint8 underflow still panics: 1 - ~uint8(0) = 1 - 255.
def lhs_nested_underflow_panics : Except TypeError Bool :=
  Examples.checkedOwnCallPanicMatches 512 Fam "lhsNested" State.empty
    [Value.word 0] 17

-- CONTROL: narrow checked arithmetic in the pure operand still panics.
def arith_nested_panics : Except TypeError Bool :=
  Examples.checkedOwnCallPanicMatches 512 Fam "arithNested" State.empty
    [Value.word 200] 17

private def isOkTrue : Except TypeError Bool → Bool
  | Except.ok true => true
  | _ => false

#guard accepted
#guard isOkTrue lhs_nested_is_one
#guard isOkTrue rhs_nested_is_one
#guard isOkTrue shl_nested_wraps
#guard isOkTrue direct_call_is_five
#guard isOkTrue lhs_nested_underflow_panics
#guard isOkTrue arith_nested_panics

end HoistedBinaryPureOperandCleanup
end Witness
end Solidity
end SolidCore

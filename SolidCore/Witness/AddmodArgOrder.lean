import SolidCore.Solidity.Checked
import SolidCore.Witness.Checked

set_option maxHeartbeats 8000000

/-!
ADDMOD-ARG-ORDER (regression): `addmod`/`mulmod` evaluate their arguments
RIGHT to LEFT in solc 0.8.35 legacy codegen (`ExpressionCompiler.cpp`,
`Kind::AddMod`/`Kind::MulMod`): the modulus first, then a zero check
(`Panic(0x12)`), then the second operand, then the first.

```solidity
contract C {
    uint256 n;

    function bump() internal returns (uint256) {
        n += 1;
        return n;
    }

    function boom(uint256 x) internal pure returns (uint256) {
        return x + 200;
    }

    function f() external returns (uint256) {
        return addmod(bump(), n, 100);
    }

    function g() external returns (uint256) {
        return mulmod(bump(), n + 5, 100);
    }

    function h(uint256 x, uint256 m) external pure returns (uint256) {
        return addmod(x + 200, 1, m);
    }

    function k(uint256 x, uint256 m) external pure returns (uint256) {
        return mulmod(boom(x), 1, m);
    }

    function t() external returns (uint256, uint256) {
        return (7, addmod(bump(), n, 100));
    }

    function ctl() external returns (uint256) {
        return addmod(n, bump(), 100);
    }
}
```

The call hoisters ran `bump()` (the first operand) ahead of the residual
`addmod(_t, n, 100)`, so `n` was read after `bump()` incremented it; and the
interpreter checked the modulus for zero only after evaluating both operands,
so an overflowing operand reported `Panic(0x11)` instead of `Panic(0x12)`.
Both hoisters now bind the operands evaluated first (and the ANF hoister checks
a non-literal modulus for zero) ahead of the earlier operands' calls, and the
interpreter checks the modulus right after evaluating it.

Real solc 0.8.35 + EVM ground truth (from `n = 0`): `f() = 1`, `g() = 5`,
`h(2^256-101, 0)` and `k(2^256-101, 0)` revert `Panic(0x12)`, `t() = (7, 1)`,
`ctl() = 2`.
-/

namespace SolidCore
namespace Solidity
namespace SolcAstImport
namespace AddmodArgOrder

open SolidCore.Solidity.Source

def importedContractDecl0 : ContractDecl :=
{ kind := ContractKind.contract
  name := "C"
  abstract := false
  bases := []
  items := [(ContractItem.stateVar
  { name := "n",
    ty := Ty.uint 256,
    visibility := some Visibility.internal_,
    mutability := VarMutability.mutable,
    override? := none,
    init := none }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "bump",
    visibility := some Visibility.internal_,
    mutability := StateMutability.nonpayable,
    params := [],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.expr (Expr.assign (Expr.ident "n") AssignOp.addAssign (Expr.literal (Literal.number "1"))), Stmt.returnValues (some (Expr.ident "n"))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "boom",
    visibility := some Visibility.internal_,
    mutability := StateMutability.pure,
    params := [{ name := some "x", ty := Ty.uint 256, location := none }],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.binary BinaryOp.add (Expr.ident "x") (Expr.literal (Literal.number "200"))))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "f",
    visibility := some Visibility.external_,
    mutability := StateMutability.nonpayable,
    params := [],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.call (Expr.ident "addmod") [Arg.positional (Expr.call (Expr.ident "bump") []), Arg.positional (Expr.ident "n"), Arg.positional (Expr.literal (Literal.number "100"))]))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "g",
    visibility := some Visibility.external_,
    mutability := StateMutability.nonpayable,
    params := [],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.call (Expr.ident "mulmod") [Arg.positional (Expr.call (Expr.ident "bump") []), Arg.positional (Expr.binary BinaryOp.add (Expr.ident "n") (Expr.literal (Literal.number "5"))), Arg.positional (Expr.literal (Literal.number "100"))]))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "h",
    visibility := some Visibility.external_,
    mutability := StateMutability.pure,
    params := [{ name := some "x", ty := Ty.uint 256, location := none }, { name := some "m", ty := Ty.uint 256, location := none }],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.call (Expr.ident "addmod") [Arg.positional (Expr.binary BinaryOp.add (Expr.ident "x") (Expr.literal (Literal.number "200"))), Arg.positional (Expr.literal (Literal.number "1")), Arg.positional (Expr.ident "m")]))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "k",
    visibility := some Visibility.external_,
    mutability := StateMutability.pure,
    params := [{ name := some "x", ty := Ty.uint 256, location := none }, { name := some "m", ty := Ty.uint 256, location := none }],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.call (Expr.ident "mulmod") [Arg.positional (Expr.call (Expr.ident "boom") [Arg.positional (Expr.ident "x")]), Arg.positional (Expr.literal (Literal.number "1")), Arg.positional (Expr.ident "m")]))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "t",
    visibility := some Visibility.external_,
    mutability := StateMutability.nonpayable,
    params := [],
    returns := [{ name := none, ty := Ty.uint 256, location := none }, { name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.tuple [TupleItem.value (Expr.literal (Literal.number "7")), TupleItem.value (Expr.call (Expr.ident "addmod") [Arg.positional (Expr.call (Expr.ident "bump") []), Arg.positional (Expr.ident "n"), Arg.positional (Expr.literal (Literal.number "100"))])]))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "ctl",
    visibility := some Visibility.external_,
    mutability := StateMutability.nonpayable,
    params := [],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.call (Expr.ident "addmod") [Arg.positional (Expr.ident "n"), Arg.positional (Expr.call (Expr.ident "bump") []), Arg.positional (Expr.literal (Literal.number "100"))]))]) })] }

def importedContract : ContractDecl :=
  importedContractDecl0

def importedContracts : List ContractDecl :=
  [importedContractDecl0]

def importedSourceUnit : SourceUnit :=
  { items := [SourceItem.pragma "solidity" "^0.8.28", SourceItem.contract importedContractDecl0] }

def importedContractAccepted : Bool :=
  TypeCheck.Result.isOk (TypeCheck.TypecheckedInput.checkedSourceUnit importedSourceUnit)

end AddmodArgOrder
end SolcAstImport
end Solidity
end SolidCore

namespace SolidCore
namespace Solidity
namespace Witness
namespace AddmodArgOrder

open SolidCore.Solidity.Source
open SolidCore.Solidity.TypeCheck

abbrev Fam := SolidCore.Solidity.SolcAstImport.AddmodArgOrder.importedContract

def accepted : Bool :=
  SolidCore.Solidity.SolcAstImport.AddmodArgOrder.importedContractAccepted

private def isOkTrue : Except TypeError Bool → Bool
  | Except.ok true => true
  | _ => false

private def big : SolidCore.Solidity.Source.Value :=
  SolidCore.Solidity.Source.Value.word
    (115792089237316195423570985008687907853269984665640564039457584007913129639935 - 100)

private def zero : SolidCore.Solidity.Source.Value :=
  SolidCore.Solidity.Source.Value.word 0

-- `addmod(bump(), n, 100)`: `n` is read (0) before `bump()` runs.
def f_is_1 : Except TypeError Bool :=
  Examples.checkedOwnCallWordMatches 256 Fam "f" State.empty [] 1

-- `mulmod(bump(), n + 5, 100)`: `n + 5` is 5, `bump()` is 1.
def g_is_5 : Except TypeError Bool :=
  Examples.checkedOwnCallWordMatches 256 Fam "g" State.empty [] 5

-- The zero modulus is reported before the overflowing first operand.
def h_panics_0x12 : Except TypeError Bool :=
  Examples.checkedOwnCallPanicMatches 256 Fam "h" State.empty [big, zero] 0x12

-- ... and before a first-operand call that would itself overflow.
def k_panics_0x12 : Except TypeError Bool :=
  Examples.checkedOwnCallPanicMatches 256 Fam "k" State.empty [big, zero] 0x12

-- The same order inside a returned tuple (argument-position hoister).
def t_is_7_1 : Except TypeError Bool :=
  Examples.checkedOwnCallWordPairMatches 256 Fam "t" State.empty [] 7 1

-- Control: the call is the second operand, so it runs before `n` is read.
def ctl_is_2 : Except TypeError Bool :=
  Examples.checkedOwnCallWordMatches 256 Fam "ctl" State.empty [] 2

#guard accepted
#guard isOkTrue f_is_1
#guard isOkTrue g_is_5
#guard isOkTrue h_panics_0x12
#guard isOkTrue k_panics_0x12
#guard isOkTrue t_is_7_1
#guard isOkTrue ctl_is_2

end AddmodArgOrder
end Witness
end Solidity
end SolidCore

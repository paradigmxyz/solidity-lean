import SolidCore.Solidity.Checked
import SolidCore.Witness.Checked

set_option maxHeartbeats 8000000

/-!
ARRAY-LITERAL-CALL-ORDER (regression): solc evaluates inline-array elements
left to right (`ExpressionCompiler.cpp` `TupleExpression`), so in `[n, bump()]`
element 0 reads `n` before `bump()` increments it.

```solidity
contract C {
    uint256 n;
    uint8 small;

    function bump() internal returns (uint256) {
        n += 1;
        return n;
    }

    function bumpSmall() internal returns (uint8) {
        small += 1;
        return small;
    }

    function f() external returns (uint256) {
        uint256[2] memory m = [n, bump()];
        return m[0];
    }

    function g() external returns (uint256) {
        uint256[3] memory m = [n, bump(), n];
        return m[0] + m[2] * 10;
    }

    function h() external returns (uint256) {
        uint8[2] memory m = [small, bumpSmall()];
        return uint256(m[0]) * 10 + m[1];
    }

    function ctl() external returns (uint256) {
        uint256[2] memory m = [bump(), n];
        return m[0] * 10 + m[1];
    }
}
```

The ANF call hoister lifted `bump()` into a temp ahead of the declaration and
left the earlier element `n` in the residual array literal, so `n` was read
after the call. `Exprs.anfHoist` now materializes an earlier element between its
own prelude and a later element's call prelude, as `Args.anfHoist` already did
for call arguments.

Real solc 0.8.35 + EVM ground truth (from `n = small = 0`): `f() = 0`,
`g() = 10`, `h() = 1`, `ctl() = 11`.
-/

namespace SolidCore
namespace Solidity
namespace SolcAstImport
namespace ArrayLiteralCallOrder

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
    init := none }), (ContractItem.stateVar
  { name := "small",
    ty := Ty.uint 8,
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
    name := some "bumpSmall",
    visibility := some Visibility.internal_,
    mutability := StateMutability.nonpayable,
    params := [],
    returns := [{ name := none, ty := Ty.uint 8, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.expr (Expr.assign (Expr.ident "small") AssignOp.addAssign (Expr.literal (Literal.number "1"))), Stmt.returnValues (some (Expr.ident "small"))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "f",
    visibility := some Visibility.external_,
    mutability := StateMutability.nonpayable,
    params := [],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.varDecl [{ name := some "m", ty := Ty.array (Ty.uint 256) (some 2), location := some DataLocation.memory }] (some (Expr.array [Expr.ident "n", Expr.call (Expr.ident "bump") []])), Stmt.returnValues (some (Expr.index (Expr.ident "m") (Expr.literal (Literal.number "0"))))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "g",
    visibility := some Visibility.external_,
    mutability := StateMutability.nonpayable,
    params := [],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.varDecl [{ name := some "m", ty := Ty.array (Ty.uint 256) (some 3), location := some DataLocation.memory }] (some (Expr.array [Expr.ident "n", Expr.call (Expr.ident "bump") [], Expr.ident "n"])), Stmt.returnValues (some (Expr.binary BinaryOp.add (Expr.index (Expr.ident "m") (Expr.literal (Literal.number "0"))) (Expr.binary BinaryOp.mul (Expr.index (Expr.ident "m") (Expr.literal (Literal.number "2"))) (Expr.literal (Literal.number "10")))))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "h",
    visibility := some Visibility.external_,
    mutability := StateMutability.nonpayable,
    params := [],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.varDecl [{ name := some "m", ty := Ty.array (Ty.uint 8) (some 2), location := some DataLocation.memory }] (some (Expr.array [Expr.ident "small", Expr.call (Expr.ident "bumpSmall") []])), Stmt.returnValues (some (Expr.binary BinaryOp.add (Expr.binary BinaryOp.mul (Expr.call (Expr.typeName (Ty.uint 256)) [Arg.positional (Expr.index (Expr.ident "m") (Expr.literal (Literal.number "0")))]) (Expr.literal (Literal.number "10"))) (Expr.index (Expr.ident "m") (Expr.literal (Literal.number "1")))))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "ctl",
    visibility := some Visibility.external_,
    mutability := StateMutability.nonpayable,
    params := [],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.varDecl [{ name := some "m", ty := Ty.array (Ty.uint 256) (some 2), location := some DataLocation.memory }] (some (Expr.array [Expr.call (Expr.ident "bump") [], Expr.ident "n"])), Stmt.returnValues (some (Expr.binary BinaryOp.add (Expr.binary BinaryOp.mul (Expr.index (Expr.ident "m") (Expr.literal (Literal.number "0"))) (Expr.literal (Literal.number "10"))) (Expr.index (Expr.ident "m") (Expr.literal (Literal.number "1")))))]) })] }

def importedContract : ContractDecl :=
  importedContractDecl0

def importedContracts : List ContractDecl :=
  [importedContractDecl0]

def importedSourceUnit : SourceUnit :=
  { items := [SourceItem.pragma "solidity" "^0.8.28", SourceItem.contract importedContractDecl0] }

def importedContractAccepted : Bool :=
  TypeCheck.Result.isOk (TypeCheck.TypecheckedInput.checkedSourceUnit importedSourceUnit)

end ArrayLiteralCallOrder
end SolcAstImport
end Solidity
end SolidCore

namespace SolidCore
namespace Solidity
namespace Witness
namespace ArrayLiteralCallOrder

open SolidCore.Solidity.Source
open SolidCore.Solidity.TypeCheck

abbrev Fam := SolidCore.Solidity.SolcAstImport.ArrayLiteralCallOrder.importedContract

def accepted : Bool :=
  SolidCore.Solidity.SolcAstImport.ArrayLiteralCallOrder.importedContractAccepted

private def isOkTrue : Except TypeError Bool → Bool
  | Except.ok true => true
  | _ => false

-- `[n, bump()]`: element 0 is the old `n`.
def f_is_0 : Except TypeError Bool :=
  Examples.checkedOwnCallWordMatches 256 Fam "f" State.empty [] 0

-- `[n, bump(), n]`: elements read 0, 1, 1.
def g_is_10 : Except TypeError Bool :=
  Examples.checkedOwnCallWordMatches 256 Fam "g" State.empty [] 10

-- Narrow elements keep their order and type.
def h_is_1 : Except TypeError Bool :=
  Examples.checkedOwnCallWordMatches 256 Fam "h" State.empty [] 1

-- Control: the call is the first element.
def ctl_is_11 : Except TypeError Bool :=
  Examples.checkedOwnCallWordMatches 256 Fam "ctl" State.empty [] 11

#guard accepted
#guard isOkTrue f_is_0
#guard isOkTrue g_is_10
#guard isOkTrue h_is_1
#guard isOkTrue ctl_is_11

end ArrayLiteralCallOrder
end Witness
end Solidity
end SolidCore

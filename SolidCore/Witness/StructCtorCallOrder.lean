import SolidCore.Solidity.Checked
import SolidCore.Witness.Checked

set_option maxHeartbeats 8000000

/-!
STRUCT-CTOR-CALL-ORDER (regression): solc evaluates struct-constructor
arguments and tuple components left to right (`ExpressionCompiler.cpp`,
`StructConstructorCall` and `TupleExpression`), so in `S(n, bump())` field `a`
reads `n` before `bump()` increments it, and `S(arr[5], under())` reports the
out-of-bounds read (`Panic(0x32)`) before `under()` underflows.

```solidity
contract C {
    struct S { uint256 a; uint256 b; }
    uint256 n;

    function bump() internal returns (uint256) {
        n += 1;
        return n;
    }

    function under() internal returns (uint256) {
        n -= 1;
        return n;
    }

    function f() external returns (uint256) {
        S memory s = S(n, bump());
        return s.a;
    }

    function g() external returns (uint256) {
        uint256[] memory arr = new uint256[](1);
        S memory s = S(arr[5], under());
        return s.a;
    }

    function h() external returns (uint256) {
        (uint256 a, uint256 b) = (n, bump());
        return a * 10 + b;
    }

    function ctl() external returns (uint256) {
        S memory s = S(bump(), n);
        return s.a * 10 + s.b;
    }
}
```

A struct constructor resolves to a tuple of per-field casts, and the ANF call
hoister lifted a call in a later component into a temp ahead of the statement
while leaving earlier components in the residual tuple. `TupleItems.anfHoist`
now materializes an earlier component between its own prelude and a later
component's call prelude, as `Args.anfHoist` already did for call arguments.

Real solc 0.8.35 + EVM ground truth (from `n = 0`): `f() = 0`,
`g()` reverts `Panic(0x32)`, `h() = 1`, `ctl() = 11`.
-/

namespace SolidCore
namespace Solidity
namespace SolcAstImport
namespace StructCtorCallOrder

open SolidCore.Solidity.Source

def importedContractDecl0 : ContractDecl :=
{ kind := ContractKind.contract
  name := "C"
  abstract := false
  bases := []
  items := [(ContractItem.structDecl
  { name := "S",
    fields := [{ name := "a", ty := Ty.uint 256 }, { name := "b", ty := Ty.uint 256 }] }), (ContractItem.stateVar
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
    name := some "under",
    visibility := some Visibility.internal_,
    mutability := StateMutability.nonpayable,
    params := [],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.expr (Expr.assign (Expr.ident "n") AssignOp.subAssign (Expr.literal (Literal.number "1"))), Stmt.returnValues (some (Expr.ident "n"))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "f",
    visibility := some Visibility.external_,
    mutability := StateMutability.nonpayable,
    params := [],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.varDecl [{ name := some "s", ty := Ty.user ({ segments := ["S"] }), location := some DataLocation.memory }] (some (Expr.call (Expr.typeName (Ty.user ({ segments := ["S"] }))) [Arg.positional (Expr.ident "n"), Arg.positional (Expr.call (Expr.ident "bump") [])])), Stmt.returnValues (some (Expr.member (Expr.ident "s") "a"))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "g",
    visibility := some Visibility.external_,
    mutability := StateMutability.nonpayable,
    params := [],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.varDecl [{ name := some "arr", ty := Ty.array (Ty.uint 256) (none), location := some DataLocation.memory }] (some (Expr.newExpr (Ty.array (Ty.uint 256) (none)) [Arg.positional (Expr.literal (Literal.number "1"))])), Stmt.varDecl [{ name := some "s", ty := Ty.user ({ segments := ["S"] }), location := some DataLocation.memory }] (some (Expr.call (Expr.typeName (Ty.user ({ segments := ["S"] }))) [Arg.positional (Expr.index (Expr.ident "arr") (Expr.literal (Literal.number "5"))), Arg.positional (Expr.call (Expr.ident "under") [])])), Stmt.returnValues (some (Expr.member (Expr.ident "s") "a"))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "h",
    visibility := some Visibility.external_,
    mutability := StateMutability.nonpayable,
    params := [],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.varDecl [{ name := some "a", ty := Ty.uint 256, location := none }, { name := some "b", ty := Ty.uint 256, location := none }] (some (Expr.tuple [TupleItem.value (Expr.ident "n"), TupleItem.value (Expr.call (Expr.ident "bump") [])])), Stmt.returnValues (some (Expr.binary BinaryOp.add (Expr.binary BinaryOp.mul (Expr.ident "a") (Expr.literal (Literal.number "10"))) (Expr.ident "b")))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "ctl",
    visibility := some Visibility.external_,
    mutability := StateMutability.nonpayable,
    params := [],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.varDecl [{ name := some "s", ty := Ty.user ({ segments := ["S"] }), location := some DataLocation.memory }] (some (Expr.call (Expr.typeName (Ty.user ({ segments := ["S"] }))) [Arg.positional (Expr.call (Expr.ident "bump") []), Arg.positional (Expr.ident "n")])), Stmt.returnValues (some (Expr.binary BinaryOp.add (Expr.binary BinaryOp.mul (Expr.member (Expr.ident "s") "a") (Expr.literal (Literal.number "10"))) (Expr.member (Expr.ident "s") "b")))]) })] }

def importedContract : ContractDecl :=
  importedContractDecl0

def importedContracts : List ContractDecl :=
  [importedContractDecl0]

def importedSourceUnit : SourceUnit :=
  { items := [SourceItem.pragma "solidity" "^0.8.28", SourceItem.contract importedContractDecl0] }

def importedContractAccepted : Bool :=
  TypeCheck.Result.isOk (TypeCheck.TypecheckedInput.checkedSourceUnit importedSourceUnit)

end StructCtorCallOrder
end SolcAstImport
end Solidity
end SolidCore

namespace SolidCore
namespace Solidity
namespace Witness
namespace StructCtorCallOrder

open SolidCore.Solidity.Source
open SolidCore.Solidity.TypeCheck

abbrev Fam := SolidCore.Solidity.SolcAstImport.StructCtorCallOrder.importedContract

def accepted : Bool :=
  SolidCore.Solidity.SolcAstImport.StructCtorCallOrder.importedContractAccepted

private def isOkTrue : Except TypeError Bool → Bool
  | Except.ok true => true
  | _ => false

-- `S(n, bump())`: field `a` is the old `n`.
def f_is_0 : Except TypeError Bool :=
  Examples.checkedOwnCallWordMatches 256 Fam "f" State.empty [] 0

-- The first argument's out-of-bounds read is reported before the second
-- argument's underflow.
def g_panics_0x32 : Except TypeError Bool :=
  Examples.checkedOwnCallPanicMatches 256 Fam "g" State.empty [] 0x32

-- A tuple declaration reads its components in the same order.
def h_is_1 : Except TypeError Bool :=
  Examples.checkedOwnCallWordMatches 256 Fam "h" State.empty [] 1

-- Control: the call is the first argument.
def ctl_is_11 : Except TypeError Bool :=
  Examples.checkedOwnCallWordMatches 256 Fam "ctl" State.empty [] 11

#guard accepted
#guard isOkTrue f_is_0
#guard isOkTrue g_panics_0x32
#guard isOkTrue h_is_1
#guard isOkTrue ctl_is_11

end StructCtorCallOrder
end Witness
end Solidity
end SolidCore

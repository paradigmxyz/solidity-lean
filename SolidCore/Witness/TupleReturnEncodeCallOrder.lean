import SolidCore.Solidity.Checked
import SolidCore.Witness.Checked

set_option maxHeartbeats 8000000

/-!
TUPLE-RETURN-ENCODE-CALL-ORDER (regression): solc evaluates call arguments
and tuple components left to right (`ExpressionCompiler.cpp`), so in
`return (1, abi.encodePacked(n, bump()))` the argument `n` is read before
`bump()` increments it.

```solidity
contract C {
    uint256 n;

    function bump() internal returns (uint256) {
        n += 1;
        return n;
    }

    function id(uint256 x) internal pure returns (uint256) {
        return x;
    }

    function f() external returns (uint256, bytes memory) {
        return (1, abi.encodePacked(n, bump()));
    }

    function g() external returns (uint256, bytes memory) {
        return (2, abi.encode(n, bump()));
    }

    function h() external returns (uint256, uint256) {
        return (n, id(bump()));
    }

    function ctl() external returns (uint256, bytes memory) {
        return (3, abi.encodePacked(bump(), n));
    }
}
```

A returned tuple is lowered by the argument-position hoister, which peels the
nested call `bump()` into a temp ahead of the whole statement while leaving the
earlier sibling `n` in place, so `n` was read after the call (packing `1, 1`).
The hoister now parks such an earlier call-free value-typed sibling into its
own temp before peeling the later call.

Real solc 0.8.35 + EVM ground truth (from `n = 0`):
`f() = (1, encodePacked(0, 1))`, `g() = (2, encode(0, 1))`, `h() = (0, 1)`,
`ctl() = (3, encodePacked(1, 1))`.
-/

namespace SolidCore
namespace Solidity
namespace SolcAstImport
namespace TupleReturnEncodeCallOrder

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
    name := some "id",
    visibility := some Visibility.internal_,
    mutability := StateMutability.pure,
    params := [{ name := some "x", ty := Ty.uint 256, location := none }],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.ident "x"))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "f",
    visibility := some Visibility.external_,
    mutability := StateMutability.nonpayable,
    params := [],
    returns := [{ name := none, ty := Ty.uint 256, location := none }, { name := none, ty := Ty.bytes, location := some DataLocation.memory }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.tuple [TupleItem.value (Expr.literal (Literal.number "1")), TupleItem.value (Expr.call (Expr.member (Expr.ident "abi") "encodePacked") [Arg.positional (Expr.ident "n"), Arg.positional (Expr.call (Expr.ident "bump") [])])]))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "g",
    visibility := some Visibility.external_,
    mutability := StateMutability.nonpayable,
    params := [],
    returns := [{ name := none, ty := Ty.uint 256, location := none }, { name := none, ty := Ty.bytes, location := some DataLocation.memory }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.tuple [TupleItem.value (Expr.literal (Literal.number "2")), TupleItem.value (Expr.call (Expr.member (Expr.ident "abi") "encode") [Arg.positional (Expr.ident "n"), Arg.positional (Expr.call (Expr.ident "bump") [])])]))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "h",
    visibility := some Visibility.external_,
    mutability := StateMutability.nonpayable,
    params := [],
    returns := [{ name := none, ty := Ty.uint 256, location := none }, { name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.tuple [TupleItem.value (Expr.ident "n"), TupleItem.value (Expr.call (Expr.ident "id") [Arg.positional (Expr.call (Expr.ident "bump") [])])]))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "ctl",
    visibility := some Visibility.external_,
    mutability := StateMutability.nonpayable,
    params := [],
    returns := [{ name := none, ty := Ty.uint 256, location := none }, { name := none, ty := Ty.bytes, location := some DataLocation.memory }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.tuple [TupleItem.value (Expr.literal (Literal.number "3")), TupleItem.value (Expr.call (Expr.member (Expr.ident "abi") "encodePacked") [Arg.positional (Expr.call (Expr.ident "bump") []), Arg.positional (Expr.ident "n")])]))]) })] }

def importedContract : ContractDecl :=
  importedContractDecl0

def importedContracts : List ContractDecl :=
  [importedContractDecl0]

def importedSourceUnit : SourceUnit :=
  { items := [SourceItem.pragma "solidity" "^0.8.28", SourceItem.contract importedContractDecl0] }

def importedContractAccepted : Bool :=
  TypeCheck.Result.isOk (TypeCheck.TypecheckedInput.checkedSourceUnit importedSourceUnit)

end TupleReturnEncodeCallOrder
end SolcAstImport
end Solidity
end SolidCore

namespace SolidCore
namespace Solidity
namespace Witness
namespace TupleReturnEncodeCallOrder

open SolidCore.Solidity.Source
open SolidCore.Solidity.TypeCheck

abbrev Fam := SolidCore.Solidity.SolcAstImport.TupleReturnEncodeCallOrder.importedContract

def accepted : Bool :=
  SolidCore.Solidity.SolcAstImport.TupleReturnEncodeCallOrder.importedContractAccepted

private def isOkTrue : Except TypeError Bool → Bool
  | Except.ok true => true
  | _ => false

private def word32 (v : Nat) : List Nat :=
  (List.range 32).map (fun i => if i == 31 then v else 0)

private def wordBytesMatches (fn : Name) (a : Word) (expected : List Nat) :
    Except TypeError Bool := do
  let result ← CheckedInput.ownCall 256 Fam
    (SolidCore.Solidity.Source.CallTarget.name fn) State.empty []
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _
      [v, SolidCore.Solidity.Source.Value.bytes bs] =>
      match SolidCore.Solidity.Source.Value.asWord? v with
      | some w => Except.ok (SolidCore.Solidity.Source.wordEq w a && bs == expected)
      | none => Except.ok false
  | _ => Except.ok false

-- `abi.encodePacked(n, bump())` in a returned tuple packs `0` then `1`.
def f_packs_0_1 : Except TypeError Bool :=
  wordBytesMatches "f" 1 (word32 0 ++ word32 1)

-- `abi.encode(n, bump())` likewise.
def g_encodes_0_1 : Except TypeError Bool :=
  wordBytesMatches "g" 2 (word32 0 ++ word32 1)

-- A tuple component read before a later component's nested call.
def h_is_0_1 : Except TypeError Bool :=
  Examples.checkedOwnCallWordPairMatches 256 Fam "h" State.empty [] 0 1

-- Control: the call is the first argument, so `n` reads its new value.
def ctl_packs_1_1 : Except TypeError Bool :=
  wordBytesMatches "ctl" 3 (word32 1 ++ word32 1)

#guard accepted
#guard isOkTrue f_packs_0_1
#guard isOkTrue g_encodes_0_1
#guard isOkTrue h_is_0_1
#guard isOkTrue ctl_packs_1_1

end TupleReturnEncodeCallOrder
end Witness
end Solidity
end SolidCore

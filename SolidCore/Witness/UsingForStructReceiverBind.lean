import SolidCore.Solidity.Checked
import SolidCore.Witness.Checked

/-!
USINGFOR-STRUCT-RECEIVER-BIND — regression guard for the #158 (USINGFOR-WIDEN-BIND)
lowering fix.

#158 replaced the lowering-time using-for bind predicate `Ty.matchesShape` with the
DIRECTIONAL `Ty.canImplicitlyConvert` (in
`FunctionDecl.firstParamMatchesWithInternalFunctions?` and
`Parameter.matchesArgWithInternalFunctions?`) so a `uint8` receiver could widen-bind
`f(uint256 self)`. But `canImplicitlyConvert`'s struct/user arms are exact `==` only:
a STORAGE-STRUCT receiver whose reflected `abiTy` path is namespace-qualified
(`M.Box`, segments `["M","Box"]`) never `==`s the library parameter's resolved type
(`Box`, segments `["Box"]`), so `_b.getV()` / `_b.setV(x)` silently stopped binding.
This regressed the whole OpenZeppelin EnumerableMap flow (every `using ... for
<struct map type>` call), which lowered to default-zero reads (`contains`/`get`
returning `false`).

The fix ORs the pre-#158 nominal predicate back in
(`canImplicitlyConvert ‖ matchesShape`): the widening case still succeeds via
`canImplicitlyConvert`, and the nominal struct/user case binds again via
`Ty.matchesShape` → `Path.matchesNominal` (single-segment last-name match). Every
`canImplicitlyConvert` reject (narrowing, uint→bytes32, signedness) is ALSO a
`matchesShape` reject, so the #158 over-accept guards are preserved.

This witness is the FAST catch: it EXECUTES a using-for call on a storage-struct
receiver whose state-var path (`M.Box`) differs from the library first-parameter
path (`Box`) — the exact shape `canImplicitlyConvert`-alone could not bind — and
`#guard`s the round-tripped value. Under #158-without-the-fix the bind fails and the
read comes back 0.

```solidity
library M {
    struct Box { uint256 v; }
    function getV(Box storage self) internal view returns (uint256) { return self.v; }
    function setV(Box storage self, uint256 x) internal { self.v = x; }
}
contract C {
    using M for M.Box;
    M.Box _b;
    function set(uint256 x) external { _b.setV(x); }
    function get() external view returns (uint256) { return _b.getV(); }
}
```
-/

namespace SolidCore
namespace Solidity
namespace SolcAstImport
namespace UsingForStructReceiverBind

def importedLibrary : ContractDecl :=
{ kind := ContractKind.library
  name := "M"
  abstract := false
  bases := []
  items := [(ContractItem.structDecl
  { name := "Box",
    fields := [{ name := "v", ty := Ty.uint 256 }] }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "getV",
    visibility := some Visibility.internal_,
    mutability := StateMutability.view,
    params := [{ name := some "self", ty := Ty.user ({ segments := ["Box"] }), location := some DataLocation.storage }],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.member (Expr.ident "self") "v"))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "setV",
    visibility := some Visibility.internal_,
    mutability := StateMutability.nonpayable,
    params := [{ name := some "self", ty := Ty.user ({ segments := ["Box"] }), location := some DataLocation.storage }, { name := some "x", ty := Ty.uint 256, location := none }],
    returns := [],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.expr (Expr.assign (Expr.member (Expr.ident "self") "v") AssignOp.assign (Expr.ident "x"))]) })] }

def importedContract : ContractDecl :=
{ kind := ContractKind.contract
  name := "C"
  abstract := false
  bases := []
  items := [(ContractItem.usingDecl
  { library := { segments := ["M"] },
    functions := [],
    target := some (Ty.user ({ segments := ["M", "Box"] })),
    global := false }), (ContractItem.stateVar
  { name := "_b",
    ty := Ty.user ({ segments := ["M", "Box"] }),
    visibility := some Visibility.internal_,
    mutability := VarMutability.mutable,
    override? := none,
    init := none }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "set",
    visibility := some Visibility.external_,
    mutability := StateMutability.nonpayable,
    params := [{ name := some "x", ty := Ty.uint 256, location := none }],
    returns := [],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.expr (Expr.call (Expr.member (Expr.ident "_b") "setV") [Arg.positional (Expr.ident "x")])]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "get",
    visibility := some Visibility.external_,
    mutability := StateMutability.view,
    params := [],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.call (Expr.member (Expr.ident "_b") "getV") []))]) })] }

def importedSourceUnit : SourceUnit :=
  { items := [SourceItem.pragma "solidity" "^0.8.35",
      SourceItem.contract importedLibrary,
      SourceItem.contract importedContract] }

def importedContractAccepted : Bool :=
  TypeCheck.Result.isOk (TypeCheck.TypecheckedInput.checkedSourceUnit importedSourceUnit)

/-- Run `set(v)` (using-for `_b.setV(v)`) then `get()` (using-for `_b.getV()`),
    threading state between the calls, and return the read-back word. `none` on any
    lowering/execution failure — which is exactly what a broken using-for bind
    produces. -/
def setThenGet? (v : Nat) : Option SolidCore.Solidity.Source.Word :=
  match TypeCheck.CheckedInput.program (α := SourceUnit) importedSourceUnit with
  | Except.ok program =>
      match
          TypeCheck.CheckedProgram.callContract 1000 program "C"
            (SolidCore.Solidity.Source.CallTarget.name "set")
            SolidCore.Solidity.Source.State.empty
            [SolidCore.Solidity.Source.Value.word (v : SolidCore.Solidity.Source.Word)] with
      | Except.ok result1 =>
          match
              TypeCheck.CheckedProgram.callContract 1000 program "C"
                (SolidCore.Solidity.Source.CallTarget.name "get")
                result1.resultState [] with
          | Except.ok (SolidCore.Solidity.Source.CallResult.returned _
              [SolidCore.Solidity.Source.Value.word w]) => some w
          | _ => none
      | _ => none
  | _ => none

end UsingForStructReceiverBind
end SolcAstImport
end Solidity
end SolidCore

namespace SolidCore
namespace Solidity
namespace Witness
namespace UsingForStructReceiverBind

open SolidCore.Solidity.SolcAstImport.UsingForStructReceiverBind

/-- The using-for struct-receiver contract is ACCEPTED by the checker. -/
def accepted : Bool := importedContractAccepted

/-- `set(42)` binds `_b.setV(42)` (storage-struct receiver) and `get()` binds
    `_b.getV()`; the round-trip reads back 42. Under the #158 change WITHOUT the
    nominal fallback, the namespace-qualified struct receiver fails to bind and this
    comes back 0/none. -/
def structReceiverBindRoundtrips : Bool :=
  match setThenGet? 42 with
  | some w => SolidCore.Solidity.Source.wordEq w (42 : SolidCore.Solidity.Source.Word)
  | none => false

#guard accepted
#guard structReceiverBindRoundtrips

end UsingForStructReceiverBind
end Witness
end Solidity
end SolidCore

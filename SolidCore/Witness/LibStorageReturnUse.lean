import SolidCore.Solidity.Checked
import SolidCore.Witness.Checked

/-!
LIB-STORAGE-RETURN-USE (#156) — EXECUTING the storage reference a library
function value-returns.

Follow-up to #155 (the checker now ACCEPTS a library function returning a
storage reference). This witness closes the RUNTIME/lowering half: a contract
that calls an INTERNAL library function returning a `storage` struct reference
and then dereferences the returned pointer — `L.ref(s).x = v` (write) and
`return L.ref(s).x` (read) — now lowers and executes, resolving to the actual
storage slot of `s.x`.

Before #156 the type-checker accepted this program (post-#155) but the
interpreter/lowering failed: `L.ref(s).x` never became `L.ref(s)[0]` because the
struct-member→index rewrite cannot type a call result, and no lowering arm
consumed a member/index USE of a value-returned storage pointer — so the whole
contract was unlowerable (`toCoreContract? = none`, over-reject).

The fix (SolidCore/Solidity/Interface.lean):
  * the `expandUsing` surface pass rewrites `<call>.field` to `<call>[fieldIndex]`
    when the call's single return is a WHOLE `storage` struct reference
    (`Expr.callSingleStorageStructReturnDecl?`), so the existing index-assign arm
    lowers the WRITE; and
  * a new `Stmt.returnValues (Expr.index (call) i)` arm lowers the READ, capturing
    the returned pointer into the storage-ref temp the boundary already threads.
Both are gated on `FunctionDecl.returnsWholeStorageRefParam?` — the boundary
re-points a WHOLE storage-ref return (`return s;`) but not a nested sub-path
return (`return d.m;`, `return o.inner;`), which stays an over-reject.

This witness EXECUTES `set(42)` (write through the returned ref) then `get()`
(read through it) and `#guard`s the result is 42 — the lean-executing coverage
the #155 acceptance witness lacked. Real-EVM ground truth (write/read through the
returned struct/mapping ref => 42 / 99) lives in
`tests/forge-harness/lib-storage-return`, extended here with an internal-library
`storageReturnUse` case.

`#eval`-confirmed booleans pinned with `#guard` (the project avoids
`native_decide`).
-/

namespace SolidCore
namespace Solidity
namespace SolcAstImport
namespace LibStorageReturnUse

/-- Internal-library storage-return USE, minimal shape:
```solidity
library L {
    struct S { uint256 x; }
    function ref(S storage s) internal pure returns (S storage) { return s; }
}
contract C {
    L.S s;
    function set(uint256 v) external { L.ref(s).x = v; }          // write through
    function get() external view returns (uint256) { return L.ref(s).x; } // read through
}
```
Emitted by `scripts/solc_ast_to_lean_source.py` from pinned solc 0.8.35. -/
def importedLibrary : ContractDecl :=
{ kind := ContractKind.library
  name := "L"
  abstract := false
  bases := []
  items := [(ContractItem.structDecl
  { name := "S",
    fields := [{ name := "x", ty := Ty.uint 256 }] }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "ref",
    visibility := some Visibility.internal_,
    mutability := StateMutability.pure,
    params := [{ name := some "s", ty := Ty.user ({ segments := ["S"] }), location := some DataLocation.storage }],
    returns := [{ name := none, ty := Ty.user ({ segments := ["S"] }), location := some DataLocation.storage }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.ident "s"))]) })] }

def importedContract : ContractDecl :=
{ kind := ContractKind.contract
  name := "C"
  abstract := false
  bases := []
  items := [(ContractItem.stateVar
  { name := "s",
    ty := Ty.user ({ segments := ["L", "S"] }),
    visibility := some Visibility.internal_,
    mutability := VarMutability.mutable,
    override? := none,
    init := none }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "set",
    visibility := some Visibility.external_,
    mutability := StateMutability.nonpayable,
    params := [{ name := some "v", ty := Ty.uint 256, location := none }],
    returns := [],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.expr (Expr.assign (Expr.member (Expr.call (Expr.member (Expr.typeName (Ty.user ({ segments := ["L"] }))) "ref") [Arg.positional (Expr.ident "s")]) "x") AssignOp.assign (Expr.ident "v"))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "get",
    visibility := some Visibility.external_,
    mutability := StateMutability.view,
    params := [],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.member (Expr.call (Expr.member (Expr.typeName (Ty.user ({ segments := ["L"] }))) "ref") [Arg.positional (Expr.ident "s")]) "x"))]) })] }

def importedSourceUnit : SourceUnit :=
  { items := [SourceItem.pragma "solidity" "^0.8.35",
      SourceItem.contract importedLibrary,
      SourceItem.contract importedContract] }

def importedContractAccepted : Bool :=
  TypeCheck.Result.isOk (TypeCheck.TypecheckedInput.checkedSourceUnit importedSourceUnit)

/-- Run `set(v)` (write `v` through the returned storage ref) then `get()` (read
    it back), threading state between the two calls, and return the single word
    the reader produced. `none` on any lowering/execution failure. -/
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

end LibStorageReturnUse
end SolcAstImport
end Solidity
end SolidCore

namespace SolidCore
namespace Solidity
namespace Witness
namespace LibStorageReturnUse

open SolidCore.Solidity.SolcAstImport.LibStorageReturnUse

/-- The internal-library storage-return-USE contract is ACCEPTED by the checker
    (post-#155). -/
def accepted : Bool := importedContractAccepted

/-- Writing 42 through the returned storage ref (`L.ref(s).x = 42`) and reading it
    back (`return L.ref(s).x`) yields 42 — the real-EVM value. This EXECUTES the
    #156 storage-return use end-to-end in the interpreter. -/
def writeReadRoundtrips : Bool :=
  match setThenGet? 42 with
  | some w => SolidCore.Solidity.Source.wordEq w (42 : SolidCore.Solidity.Source.Word)
  | none => false

#guard accepted
#guard writeReadRoundtrips

end LibStorageReturnUse
end Witness
end Solidity
end SolidCore

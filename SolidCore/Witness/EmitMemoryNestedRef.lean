import SolidCore.Solidity.Checked
import SolidCore.Witness.Checked

set_option maxHeartbeats 8000000

/-!
EMIT-MEMORY-NESTED-REF (soundness, adjudicated) — an event argument NESTING
memory references (`uint256[][]`), i.e. a `Value.dynamicArray` whose element
rows are `Value.memoryRef`s.

```solidity
contract C {
    event N(uint256[][] rows);
    function run() external {
        uint256[][] memory rows = new uint256[][](2);
        rows[0] = new uint256[](1);
        rows[0][0] = 7;
        rows[1] = new uint256[](2);
        rows[1][0] = 8;
        rows[1][1] = 9;
        emit N(rows);
    }
}
```

solc+EVM emit `N` with the full ABI encoding of `[[7], [8, 9]]`.

solidity-lean formerly REVERTED with `Panic(0)`: `Stmt.emitEvent` evaluated its
arguments but did NOT deep-materialize them, so nested `Value.memoryRef` leaves
survived to the Runtime-free event encoder (`EventDecl.encodeFields?` /
`abiEncodeValues?`), which has no case for refs and returned `none` →
`RevertData.typeMismatch` = `Panic(0)`. This is DISTINCT from the earlier
bare-STORAGE emit-arg fix (#7): the static lowering rewrite materializes a bare
top-level storage identifier, but cannot reach refs created dynamically INSIDE
memory aggregates.

The fix routes `Stmt.emitEvent`'s evaluated argument values through
`Runtime.materializeForValueUseList` — the same deep, structurally recursive
materializer `abi.encode*` / `keccak256` / `bytes.concat` use — before the
encoder runs. The same materialization is applied to the custom-error revert
payload boundaries (`Stmt.revert` / `Stmt.requireCustom`), whose values are
encoded Runtime-free by `Contract.encodeRevertData?` (same class).

Real-EVM ground truth (forge lane `emit-memory-nested`): `run()` => success,
one log, topic0 = keccak256("N(uint256[][])"), data = abi.encode([[7],[8,9]]).
-/

namespace SolidCore
namespace Solidity
namespace SolcAstImport
namespace EmitMemoryNestedRef

private def lit (s : String) : Expr := Expr.literal (Literal.number s)

private def rowsTy : Ty := Ty.array (Ty.array (Ty.uint 256) none) none
private def rowTy : Ty := Ty.array (Ty.uint 256) none

private def declRows : Stmt :=
  Stmt.varDecl
    [{ name := some "rows", ty := rowsTy, location := some DataLocation.memory }]
    (some (Expr.newExpr rowsTy [Arg.positional (lit "2")]))

private def idx (base : Expr) (i : String) : Expr :=
  Expr.index base (lit i)

private def assign (lhs rhs : Expr) : Stmt :=
  Stmt.expr (Expr.assign lhs AssignOp.assign rhs)

private def runBody : Stmt :=
  Stmt.block
    [ declRows
    , assign (idx (Expr.ident "rows") "0")
        (Expr.newExpr rowTy [Arg.positional (lit "1")])
    , assign (idx (idx (Expr.ident "rows") "0") "0") (lit "7")
    , assign (idx (Expr.ident "rows") "1")
        (Expr.newExpr rowTy [Arg.positional (lit "2")])
    , assign (idx (idx (Expr.ident "rows") "1") "0") (lit "8")
    , assign (idx (idx (Expr.ident "rows") "1") "1") (lit "9")
    , Stmt.emitEvent
        (Expr.call (Expr.ident "N") [Arg.positional (Expr.ident "rows")]) ]

private def runFn : ContractItem :=
  ContractItem.function
    { kind := FunctionKind.function, name := some "run",
      visibility := some Visibility.external_,
      mutability := StateMutability.nonpayable,
      params := [], returns := [],
      virtual := false, override? := none, modifiers := [],
      body := some runBody }

def importedContractDecl0 : ContractDecl :=
  { kind := ContractKind.contract, name := "C",
    abstract := false, bases := [],
    items :=
      [ ContractItem.eventDecl
          { name := "N"
            params :=
              [{ name := some "rows", ty := rowsTy, indexed := false }] }
      , runFn ] }

def importedContract : ContractDecl := importedContractDecl0

def importedSourceUnit : SourceUnit :=
  { items := [SourceItem.pragma "solidity" "^0.8.35",
              SourceItem.contract importedContractDecl0] }

def importedContractAccepted : Bool :=
  TypeCheck.Result.isOk (TypeCheck.TypecheckedInput.checkedSourceUnit importedSourceUnit)

end EmitMemoryNestedRef
end SolcAstImport
end Solidity
end SolidCore

namespace SolidCore
namespace Solidity
namespace Witness
namespace EmitMemoryNestedRef

open SolidCore.Solidity.Source
open SolidCore.Solidity.TypeCheck

abbrev Fam := SolidCore.Solidity.SolcAstImport.EmitMemoryNestedRef.importedContract

def accepted : Bool :=
  SolidCore.Solidity.SolcAstImport.EmitMemoryNestedRef.importedContractAccepted

private def w (n : Nat) : List Byte :=
  SolidCore.Solidity.Source.wordToBytesBE 32 n

-- abi.encode([[7],[8,9]]): outer head offset 0x20; outer length 2; element
-- offsets 0x40 / 0x80 (relative to the outer payload start); row [7]
-- (length 1, value 7); row [8,9] (length 2, values 8, 9).
private def expectedDataBytes : List Byte :=
  w 32 ++ w 2 ++ w 64 ++ w 128 ++ w 1 ++ w 7 ++ w 2 ++ w 8 ++ w 9

-- The divergence witness: `run()` completes normally (pre-fix it REVERTED with
-- `Panic(0)`) and emits one `N` event with topic0 = keccak of the canonical
-- signature and data = the full nested ABI encoding, matching solc+EVM.
def run_emits_nested_array : Except TypeError Bool := do
  let result ←
    CheckedInput.ownCall 64 Fam
      (SolidCore.Solidity.Source.CallTarget.name "run")
      SolidCore.Solidity.Source.State.empty []
  match result with
  | SolidCore.Solidity.Source.CallResult.returned state [] =>
      match state.events with
      | [event] =>
          Except.ok
            (event.name == "N" &&
              event.topics ==
                [SolidCore.Solidity.Source.Keccak.digestWord "N(uint256[][])"] &&
              event.dataBytes == expectedDataBytes)
      | _ => Except.ok false
  | _ => Except.ok false

private def isOkTrue : Except TypeError Bool → Bool
  | Except.ok true => true
  | _ => false

#guard accepted
#guard isOkTrue run_emits_nested_array

end EmitMemoryNestedRef
end Witness
end Solidity
end SolidCore

import SolidCore.Solidity.Checked
import SolidCore.Witness.Checked

set_option maxHeartbeats 8000000

/-!
TERNARY-STORAGE-BYTES-KECCAK (#192 follow-up) — `keccak256` of a TERNARY over
two BARE STATE `bytes` variables.

```solidity
contract C {
    bytes bs;
    bytes bs2;
    function run() external returns (bytes32) {
        bs = hex"a1b2c3";
        bs2 = hex"ddeeff";
        bool c = true;
        return keccak256(c ? bs : bs2);
    }
}
```

solc+EVM selects the `bytes storage` pointer of the ternary and implicitly copies
it to memory at the `keccak256` value-use boundary, so it hashes the SELECTED
contents. With `c == true` the result is `keccak256(0xa1b2c3)` =
`0x90dd64b7…ee2d3286`.

solidity-lean formerly REVERTED with `Panic(0)`: the direct form `keccak256(bs)`
is rescued because `materializeStorageValueUseCore` rewrites a top-level
`Expr.storage key` → `Expr.storagePath key []` (full materializing read).
Wrapping the bare storage in a ternary defeated it — the lowered core is
`Expr.ternary cond (Expr.storage k1) (Expr.storage k2)`, and the materializer only
matched the TOP-LEVEL `Expr.storage`, so the ternary passed through UNREWRITTEN.
Each branch then evaluated to the storage HEADER word (the `.length` convention),
whose `asBytes?` is `none` → `RevertData.typeMismatch` = `Panic(0)`.

The fix extends `materializeStorageValueUseCore` to recurse into the ternary
branches (the boolean condition — not a value-use — is left untouched), so the
selected branch loads its full contents via `Expr.storagePath`.

Real-EVM ground truth (adjudicated divergence):
`run()` => `success|w:0x90dd64b7b65737922e06b10b3d994605524d919bed3b7025f3781f61ee2d3286`.
-/

namespace SolidCore
namespace Solidity
namespace SolcAstImport
namespace TernaryStorageBytesKeccak

open SolidCore.Solidity.Source

private def hexLit (s : String) : Expr := Expr.literal (Literal.hexString s)

-- `keccak256(c ? bs : bs2)`
private def keccakCall : Expr :=
  Expr.call (Expr.ident "keccak256")
    [Arg.positional (Expr.ternary (Expr.ident "c") (Expr.ident "bs") (Expr.ident "bs2"))]

-- `bs = hex"a1b2c3"; bs2 = hex"ddeeff"; bool c = true; return keccak256(c ? bs : bs2);`
private def runFn : ContractItem :=
  ContractItem.function
    { kind := FunctionKind.function, name := some "run",
      visibility := some Visibility.external_,
      mutability := StateMutability.nonpayable,
      params := [], returns := [{ name := none, ty := Ty.bytesN 32, location := none }],
      virtual := false, override? := none, modifiers := [],
      body := some (Stmt.block
        [ Stmt.expr (Expr.assign (Expr.ident "bs") AssignOp.assign (hexLit "a1b2c3"))
        , Stmt.expr (Expr.assign (Expr.ident "bs2") AssignOp.assign (hexLit "ddeeff"))
        , Stmt.varDecl [{ name := some "c", ty := Ty.bool, location := none }]
            (some (Expr.literal (Literal.bool true)))
        , Stmt.returnValues (some keccakCall) ]) }

def importedContractDecl0 : ContractDecl :=
  { kind := ContractKind.contract, name := "C",
    abstract := false, bases := [],
    items := [ ContractItem.stateVar { name := "bs", ty := Ty.bytes },
               ContractItem.stateVar { name := "bs2", ty := Ty.bytes },
               runFn ] }

def importedContract : ContractDecl := importedContractDecl0

def importedSourceUnit : SourceUnit :=
  { items := [SourceItem.pragma "solidity" "^0.8.35",
              SourceItem.contract importedContractDecl0] }

def importedContractAccepted : Bool :=
  TypeCheck.Result.isOk (TypeCheck.TypecheckedInput.checkedSourceUnit importedSourceUnit)

end TernaryStorageBytesKeccak
end SolcAstImport
end Solidity
end SolidCore

namespace SolidCore
namespace Solidity
namespace Witness
namespace TernaryStorageBytesKeccak

open SolidCore.Solidity.Source
open SolidCore.Solidity.TypeCheck

abbrev Fam := SolidCore.Solidity.SolcAstImport.TernaryStorageBytesKeccak.importedContract

def accepted : Bool :=
  SolidCore.Solidity.SolcAstImport.TernaryStorageBytesKeccak.importedContractAccepted

-- The divergence witness: `run()` returns `keccak256(0xa1b2c3)`, matching
-- solc+EVM (pre-fix this reverted with `Panic(0)` and yielded `false`).
def run_hashes_selected_branch : Except TypeError Bool :=
  Examples.checkedOwnCallWordMatches 4096 Fam "run" State.empty []
    0x90dd64b7b65737922e06b10b3d994605524d919bed3b7025f3781f61ee2d3286

private def isOkTrue : Except TypeError Bool → Bool
  | Except.ok true => true
  | _ => false

#guard accepted
#guard isOkTrue run_hashes_selected_branch

end TernaryStorageBytesKeccak
end Witness
end Solidity
end SolidCore

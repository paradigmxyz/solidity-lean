import SolidCore.Solidity.Checked
import SolidCore.Witness.Checked

set_option maxHeartbeats 8000000

/-!
EMIT-STORAGE-DYNAMIC-ARRAY (#192 follow-up) — a BARE STATE dynamic array
(`uint256[]`) passed as an EVENT argument.

```solidity
contract C {
    uint256[] arr;
    event E(uint256[] a);
    function run() external {
        arr.push(11);
        arr.push(22);
        emit E(arr);
    }
}
```

solc+EVM implicitly copies the storage array to memory before emitting, so `E`
carries the full ABI-encoded array `[11, 22]` (data = offset `0x20`, length `2`,
then the two elements).

solidity-lean formerly REVERTED with `Panic(0)`: an event argument is a
value-use boundary — `EventDecl.encodeFields?` ABI-encodes the argument CONTENTS
from the field types and cannot read storage — exactly like
`abi.encode*`/`keccak256`/`abi.decode`. But `Stmt.emitEvent`'s lowering passed
the lowered args through `Args.toCoreExprs?` UNMATERIALIZED. A bare state array
lowers to `Expr.storage key`, whose eval is the HEADER word (the `.length`
convention), so `abiEncodeValues?` for a `uint256[]` field on that `Value.word`
returned `none` → `RevertData.typeMismatch` = `Panic(0)`.

The fix mirrors the other value-use boundaries: both `Stmt.emitEvent` lowering
arms now rewrite their args with `materializeStorageValueUseCores`, so a
bare-storage argument loads its full contents (`Expr.storagePath key []`); every
other core shape (calldata/memory/scalar/refs) passes through untouched.

Real-EVM ground truth (adjudicated divergence): `run()` => `success`, emitting
`E` with data = ABI encoding of the array `[11, 22]`.
-/

namespace SolidCore
namespace Solidity
namespace SolcAstImport
namespace EmitStorageDynamicArray

open SolidCore.Solidity.Source

private def lit (s : String) : Expr := Expr.literal (Literal.number s)

private def uintArrayTy : Ty := Ty.array (Ty.uint 256) none

-- `arr.push(<n>);`
private def pushStmt (n : String) : Stmt :=
  Stmt.expr
    (Expr.call (Expr.member (Expr.ident "arr") "push") [Arg.positional (lit n)])

-- `emit E(arr);`
private def emitStmt : Stmt :=
  Stmt.emitEvent (Expr.call (Expr.ident "E") [Arg.positional (Expr.ident "arr")])

private def runFn : ContractItem :=
  ContractItem.function
    { kind := FunctionKind.function, name := some "run",
      visibility := some Visibility.external_,
      mutability := StateMutability.nonpayable,
      params := [], returns := [],
      virtual := false, override? := none, modifiers := [],
      body := some (Stmt.block [ pushStmt "11", pushStmt "22", emitStmt ]) }

def importedContractDecl0 : ContractDecl :=
  { kind := ContractKind.contract, name := "C",
    abstract := false, bases := [],
    items :=
      [ ContractItem.stateVar { name := "arr", ty := uintArrayTy }
      , ContractItem.eventDecl
          { name := "E"
            params := [{ name := some "a", ty := uintArrayTy, indexed := false }] }
      , runFn ] }

def importedContract : ContractDecl := importedContractDecl0

def importedSourceUnit : SourceUnit :=
  { items := [SourceItem.pragma "solidity" "^0.8.35",
              SourceItem.contract importedContractDecl0] }

def importedContractAccepted : Bool :=
  TypeCheck.Result.isOk (TypeCheck.TypecheckedInput.checkedSourceUnit importedSourceUnit)

end EmitStorageDynamicArray
end SolcAstImport
end Solidity
end SolidCore

namespace SolidCore
namespace Solidity
namespace Witness
namespace EmitStorageDynamicArray

open SolidCore.Solidity.Source
open SolidCore.Solidity.TypeCheck

abbrev Fam := SolidCore.Solidity.SolcAstImport.EmitStorageDynamicArray.importedContract

def accepted : Bool :=
  SolidCore.Solidity.SolcAstImport.EmitStorageDynamicArray.importedContractAccepted

-- Expected ABI-encoded event data for `E([11, 22])`: dynamic-array head offset
-- `0x20`, length `2`, then the two elements — four 32-byte big-endian words.
private def expectedDataBytes : List Byte :=
  SolidCore.Solidity.Source.wordToBytesBE 32 32 ++
  SolidCore.Solidity.Source.wordToBytesBE 32 2 ++
  SolidCore.Solidity.Source.wordToBytesBE 32 11 ++
  SolidCore.Solidity.Source.wordToBytesBE 32 22

-- The divergence witness: `run()` completes normally (pre-fix it REVERTED with
-- `Panic(0)`) and emits exactly one `E` event whose ABI-encoded data is the full
-- array `[11, 22]`, matching solc+EVM.
def run_emits_full_array : Except TypeError Bool := do
  let result ←
    CheckedInput.ownCall 64 Fam
      (SolidCore.Solidity.Source.CallTarget.name "run")
      SolidCore.Solidity.Source.State.empty []
  match result with
  | SolidCore.Solidity.Source.CallResult.returned state [] =>
      match state.events with
      | [event] =>
          Except.ok
            (event.name == "E" &&
              event.dataBytes == expectedDataBytes)
      | _ => Except.ok false
  | _ => Except.ok false

private def isOkTrue : Except TypeError Bool → Bool
  | Except.ok true => true
  | _ => false

#guard accepted
#guard isOkTrue run_emits_full_array

end EmitStorageDynamicArray
end Witness
end Solidity
end SolidCore

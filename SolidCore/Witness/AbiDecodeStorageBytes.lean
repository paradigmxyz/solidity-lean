import SolidCore.Solidity.Checked
import SolidCore.Witness.Checked

set_option maxHeartbeats 8000000

/-!
ABI-DECODE-STORAGE-BYTES (#192 follow-up) — `abi.decode` of a BARE STATE
`bytes`/`string` variable.

```solidity
contract C {
    bytes bs;
    function run() external returns (uint256) {
        bs = abi.encode(uint256(42));
        return abi.decode(bs, (uint256));
    }
}
```

solc+EVM implicitly copies the storage `bytes` to memory before `abi.decode`, so
it decodes the stored CONTENTS (the 32-byte word `42`) and `run()` returns `42`.

solidity-lean formerly REVERTED with `Panic(0)`: `abi.decode`'s DATA argument is
a value-use boundary (it consumes the byte CONTENTS), exactly like
`abi.encode*`/`keccak256`/`bytes.concat`, but `Expr.toAbiDecode?` passed the
lowered data core through UNMATERIALIZED. A bare state `bytes` lowers to
`Expr.storage key`, whose eval is the HEADER word (the `.length` convention =
`2*len+1` for the long-bytes layout), so `asBytes?` on that `Value.word` returned
`none` → `RevertData.typeMismatch` = `Panic(0)`.

The fix mirrors the other value-use boundaries: `Expr.toAbiDecode?` now rewrites
the data core with `materializeStorageValueUseCore`, so a bare-storage target
loads its full contents (`Expr.storagePath key []`); every other core shape
(calldata/memory bytes, locals) passes through untouched.

Real-EVM ground truth (adjudicated divergence): `run()` => `success|w:42`.
-/

namespace SolidCore
namespace Solidity
namespace SolcAstImport
namespace AbiDecodeStorageBytes

open SolidCore.Solidity.Source

private def lit (s : String) : Expr := Expr.literal (Literal.number s)
private def u256 (e : Expr) : Expr :=
  Expr.call (Expr.typeName (Ty.uint 256)) [Arg.positional e]

-- `abi.encode(uint256(42))`
private def encodeCall : Expr :=
  Expr.call (Expr.member (Expr.ident "abi") "encode")
    [Arg.positional (u256 (lit "42"))]

-- `abi.decode(bs, (uint256))`
private def decodeCall : Expr :=
  Expr.call (Expr.member (Expr.ident "abi") "decode")
    [ Arg.positional (Expr.ident "bs")
    , Arg.positional (Expr.tuple [TupleItem.value (Expr.typeName (Ty.uint 256))]) ]

-- `bs = abi.encode(uint256(42)); return abi.decode(bs, (uint256));`
private def runFn : ContractItem :=
  ContractItem.function
    { kind := FunctionKind.function, name := some "run",
      visibility := some Visibility.external_,
      mutability := StateMutability.nonpayable,
      params := [], returns := [{ name := none, ty := Ty.uint 256, location := none }],
      virtual := false, override? := none, modifiers := [],
      body := some (Stmt.block
        [ Stmt.expr (Expr.assign (Expr.ident "bs") AssignOp.assign encodeCall)
        , Stmt.returnValues (some decodeCall) ]) }

def importedContractDecl0 : ContractDecl :=
  { kind := ContractKind.contract, name := "C",
    abstract := false, bases := [],
    items := [ ContractItem.stateVar { name := "bs", ty := Ty.bytes }, runFn ] }

def importedContract : ContractDecl := importedContractDecl0

def importedSourceUnit : SourceUnit :=
  { items := [SourceItem.pragma "solidity" "^0.8.35",
              SourceItem.contract importedContractDecl0] }

def importedContractAccepted : Bool :=
  TypeCheck.Result.isOk (TypeCheck.TypecheckedInput.checkedSourceUnit importedSourceUnit)

end AbiDecodeStorageBytes
end SolcAstImport
end Solidity
end SolidCore

namespace SolidCore
namespace Solidity
namespace Witness
namespace AbiDecodeStorageBytes

open SolidCore.Solidity.Source
open SolidCore.Solidity.TypeCheck

abbrev Fam := SolidCore.Solidity.SolcAstImport.AbiDecodeStorageBytes.importedContract

def accepted : Bool :=
  SolidCore.Solidity.SolcAstImport.AbiDecodeStorageBytes.importedContractAccepted

-- The divergence witness: `run()` returns the DECODED contents `42`, matching
-- solc+EVM (pre-fix this reverted with `Panic(0)` and yielded `false`).
def run_returns_42 : Except TypeError Bool :=
  Examples.checkedOwnCallWordMatches 256 Fam "run" State.empty [] 42

private def isOkTrue : Except TypeError Bool → Bool
  | Except.ok true => true
  | _ => false

#guard accepted
#guard isOkTrue run_returns_42

end AbiDecodeStorageBytes
end Witness
end Solidity
end SolidCore

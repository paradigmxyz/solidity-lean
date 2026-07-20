import SolidCore.Solidity.Checked
import SolidCore.Witness.Checked

set_option maxHeartbeats 8000000

/-!
MAPPING-KEY-STORAGE-STRING (#192 family) — a `mapping(string => uint)` indexed
with a BARE STATE `string` variable as the key: `m[k]`.

```solidity
contract C {
    string k;
    mapping(string => uint256) m;
    function run() external returns (uint256) {
        k = "the-key";
        m[k] = 123;                 // write via storage-string key
        m["the-key"] = 123;         // write via literal key (same slot if materialized)
        return m[k] + m["the-key"]; // both read same slot -> 246 if correct
    }
}
```

A mapping value slot is `keccak256(keyContents . slot)`; for a `string`/`bytes`
key the hash reads the key's CONTENTS. solc+EVM copies the storage string to
memory at this value-use boundary, so `m[k]` and `m["the-key"]` derive the SAME
slot — both writes land there and `run()` returns `123 + 123 = 246`.

solidity-lean formerly REVERTED with `Panic(0)`: a bare state `string` lowers to
`Expr.storage key` (the storage HEADER word, the `.length` convention). As the
mapping index that word flowed into `mappingStorageSlotForKey` (key type
`bytesCalldata`), whose `key.asBytes?` is `none` for a word →
`RevertData.typeMismatch` = `Panic(0)`, thrown at the very first `m[k] = 123`
write. The literal-key statements never ran.

The fix materializes the lowered mapping-index core in the `storageIndex`
read/write lowering arms (`Expr.storage key` → `Expr.storagePath key []`, via
`materializeStorageValueUseCore`), so a bare storage `string`/`bytes`/array key
hashes its full contents. Scalar keys load identically through either form and
are unaffected.

Real-EVM ground truth (adjudicated divergence): `run()` => `success|w:246`.
-/

namespace SolidCore
namespace Solidity
namespace SolcAstImport
namespace MappingKeyStorageString

open SolidCore.Solidity.Source

private def strLit (s : String) : Expr := Expr.literal (Literal.string s)

-- `m[k]` and `m["the-key"]`
private def mAtK : Expr := Expr.index (Expr.ident "m") (Expr.ident "k")
private def mAtLit : Expr := Expr.index (Expr.ident "m") (strLit "the-key")

-- k = "the-key"; m[k] = 123; m["the-key"] = 123; return m[k] + m["the-key"];
private def runFn : ContractItem :=
  ContractItem.function
    { kind := FunctionKind.function, name := some "run",
      visibility := some Visibility.external_,
      mutability := StateMutability.nonpayable,
      params := [], returns := [{ name := none, ty := Ty.uint 256, location := none }],
      virtual := false, override? := none, modifiers := [],
      body := some (Stmt.block
        [ Stmt.expr (Expr.assign (Expr.ident "k") AssignOp.assign (strLit "the-key"))
        , Stmt.expr (Expr.assign mAtK AssignOp.assign (Expr.literal (Literal.number "123")))
        , Stmt.expr (Expr.assign mAtLit AssignOp.assign (Expr.literal (Literal.number "123")))
        , Stmt.returnValues (some (Expr.binary BinaryOp.add mAtK mAtLit)) ]) }

def importedContractDecl0 : ContractDecl :=
  { kind := ContractKind.contract, name := "C",
    abstract := false, bases := [],
    items := [ ContractItem.stateVar { name := "k", ty := Ty.string },
               ContractItem.stateVar
                 { name := "m", ty := Ty.mapping Ty.string (Ty.uint 256) },
               runFn ] }

def importedContract : ContractDecl := importedContractDecl0

def importedSourceUnit : SourceUnit :=
  { items := [SourceItem.pragma "solidity" "^0.8.35",
              SourceItem.contract importedContractDecl0] }

def importedContractAccepted : Bool :=
  TypeCheck.Result.isOk (TypeCheck.TypecheckedInput.checkedSourceUnit importedSourceUnit)

end MappingKeyStorageString
end SolcAstImport
end Solidity
end SolidCore

namespace SolidCore
namespace Solidity
namespace Witness
namespace MappingKeyStorageString

open SolidCore.Solidity.Source
open SolidCore.Solidity.TypeCheck

abbrev Fam := SolidCore.Solidity.SolcAstImport.MappingKeyStorageString.importedContract

def accepted : Bool :=
  SolidCore.Solidity.SolcAstImport.MappingKeyStorageString.importedContractAccepted

-- The divergence witness: `run()` returns `123 + 123 = 246`, matching solc+EVM
-- (pre-fix this reverted with `Panic(0)` at the first `m[k] = 123` write and
-- yielded `false`).
def run_bare_storage_key_is_246 : Except TypeError Bool :=
  Examples.checkedOwnCallWordMatches 4096 Fam "run" State.empty [] 246

private def isOkTrue : Except TypeError Bool → Bool
  | Except.ok true => true
  | _ => false

#guard accepted
#guard isOkTrue run_bare_storage_key_is_246

end MappingKeyStorageString
end Witness
end Solidity
end SolidCore

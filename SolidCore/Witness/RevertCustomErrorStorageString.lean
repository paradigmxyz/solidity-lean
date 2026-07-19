import SolidCore.Solidity.Checked
import SolidCore.Witness.Checked

set_option maxHeartbeats 8000000

/-!
REVERT-CUSTOM-ERROR-STORAGE-STRING (#192 follow-up) — `revert Bad(reason)` whose
argument is a BARE STATE `string` variable and `error Bad(string)`.

```solidity
contract C {
    string info;
    error Bad(string reason);
    function run() external {
        info = "insufficient balance for transfer";
        revert Bad(info);
    }
}
```

solc+EVM materializes the storage string into memory and reverts with the custom
error `Bad("insufficient balance for transfer")` (selector `0xc71b691d` +
ABI-encoded string).

solidity-lean formerly REVERTED with `Panic(0)`: a custom-error revert argument
is a value-use boundary — the argument CONTENTS are ABI-encoded into the revert
data, exactly like `abi.encode*`/`keccak256`/`emit`. But the custom-error revert
lowering passed the argument cores through UNMATERIALIZED. A bare state `string`
lowers to `Expr.storage key`, whose eval is the HEADER word (the `.length`
convention), so the error encoder's `asBytes?` on that `Value.word` returned
`none` → `RevertData.typeMismatch` = `Panic(0)`.

The fix mirrors the other value-use boundaries: the custom-error revert lowering
arms (bare-ident and member-qualified) now rewrite their arg cores with
`materializeStorageValueUseCores`, so a bare-storage argument loads its full
contents (`Expr.storagePath key []`); every other core shape (memory strings,
locals) passes through untouched.

Real-EVM ground truth (adjudicated divergence): `run()` =>
`revert|custom:Bad:b:insufficient balance for transfer`.
-/

namespace SolidCore
namespace Solidity
namespace SolcAstImport
namespace RevertCustomErrorStorageString

open SolidCore.Solidity.Source

-- `info = "insufficient balance for transfer"; revert Bad(info);`
private def runFn : ContractItem :=
  ContractItem.function
    { kind := FunctionKind.function, name := some "run",
      visibility := some Visibility.external_,
      mutability := StateMutability.nonpayable,
      params := [], returns := [],
      virtual := false, override? := none, modifiers := [],
      body := some (Stmt.block
        [ Stmt.expr
            (Expr.assign (Expr.ident "info") AssignOp.assign
              (Expr.literal (Literal.string "insufficient balance for transfer")))
        , Stmt.revertCall
            (Expr.call (Expr.ident "Bad")
              [ Arg.positional (Expr.ident "info") ]) ]) }

def importedContractDecl0 : ContractDecl :=
  { kind := ContractKind.contract, name := "C",
    abstract := false, bases := [],
    items :=
      [ ContractItem.stateVar { name := "info", ty := Ty.string }
      , ContractItem.errorDecl { name := "Bad", params := [{ ty := Ty.string }] }
      , runFn ] }

def importedContract : ContractDecl := importedContractDecl0

def importedSourceUnit : SourceUnit :=
  { items := [SourceItem.pragma "solidity" "^0.8.35",
              SourceItem.contract importedContractDecl0] }

def importedContractAccepted : Bool :=
  TypeCheck.Result.isOk (TypeCheck.TypecheckedInput.checkedSourceUnit importedSourceUnit)

end RevertCustomErrorStorageString
end SolcAstImport
end Solidity
end SolidCore

namespace SolidCore
namespace Solidity
namespace Witness
namespace RevertCustomErrorStorageString

open SolidCore.Solidity.Source
open SolidCore.Solidity.TypeCheck

abbrev Fam := SolidCore.Solidity.SolcAstImport.RevertCustomErrorStorageString.importedContract

def accepted : Bool :=
  SolidCore.Solidity.SolcAstImport.RevertCustomErrorStorageString.importedContractAccepted

-- `"insufficient balance for transfer"` as raw bytes (33 bytes).
private def reasonBytes : List SolidCore.Solidity.Source.Byte :=
  [105, 110, 115, 117, 102, 102, 105, 99, 105, 101, 110, 116, 32, 98, 97, 108,
    97, 110, 99, 101, 32, 102, 111, 114, 32, 116, 114, 97, 110, 115, 102, 101,
    114]

-- The divergence witness: `run()` reverts with the custom error `Bad` carrying
-- the storage string contents "insufficient balance for transfer", matching
-- solc+EVM (pre-fix this reverted with `Panic(0)`).
def run_reverts_custom_bad_string : Except TypeError Bool := do
  let result ←
    CheckedInput.ownCall 64 Fam
      (SolidCore.Solidity.Source.CallTarget.name "run")
      SolidCore.Solidity.Source.State.empty []
  match result with
  | SolidCore.Solidity.Source.CallResult.reverted _
      (SolidCore.Solidity.Source.RevertData.custom "Bad"
        [SolidCore.Solidity.Source.Value.bytes bs]) =>
      Except.ok (bs == reasonBytes)
  -- The raw ABI-encoded form (should the pipeline normalize to it) is also an
  -- acceptable `Bad(string)` observable: selector `0xc71b691d`, offset `0x20`,
  -- length `33`, then the 33 reason bytes.
  | SolidCore.Solidity.Source.CallResult.reverted _
      (SolidCore.Solidity.Source.RevertData.raw bytes) =>
      Except.ok
        (bytes.take 4 == [199, 27, 105, 29]           -- Bad(string) selector
          && bytes.length == 100                      -- 4 + 3*32
          && (bytes.drop 68).take 33 == reasonBytes)
  | _ => Except.ok false

private def isOkTrue : Except TypeError Bool → Bool
  | Except.ok true => true
  | _ => false

#guard accepted
#guard isOkTrue run_reverts_custom_bad_string

end RevertCustomErrorStorageString
end Witness
end Solidity
end SolidCore

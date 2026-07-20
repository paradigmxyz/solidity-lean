import SolidCore.Solidity.Checked
import SolidCore.Witness.Checked

set_option maxHeartbeats 8000000

/-!
REQUIRE-REASON-STORAGE-STRING (#192 follow-up) — `require(false, reason)` whose
REASON is a BARE STATE `string` variable.

```solidity
contract C {
    string reason;
    function run() external {
        reason = "not allowed here";
        require(false, reason);
    }
}
```

solc+EVM materializes the storage string into memory and reverts with
`Error("not allowed here")` (selector `0x08c379a0` + ABI-encoded string).

solidity-lean formerly REVERTED with `Panic(0)`: the reason of a
`require(cond, reason)` is a value-use boundary (it consumes the string
CONTENTS, ABI-encoded into `Error(string)` by `errorStringBytesRevert?`),
exactly like `abi.encode*`/`keccak256`/`abi.decode`. But the `require`
lowerings passed the reason core through UNMATERIALIZED. A bare state `string`
lowers to `Expr.storage key`, whose eval is the HEADER word (the `.length`
convention), so `asBytes?` on that `Value.word` returned `none` →
`RevertData.typeMismatch` = `Panic(0)`.

The fix mirrors the other value-use boundaries: the `requireErrorExpr`
lowerings now rewrite the reason core with `materializeStorageValueUseCore`, so
a bare-storage reason loads its full contents (`Expr.storagePath key []`);
every other core shape (memory strings, locals) passes through untouched.

Real-EVM ground truth (adjudicated divergence): `run()` =>
`revert|error:not allowed here`.
-/

namespace SolidCore
namespace Solidity
namespace SolcAstImport
namespace RequireReasonStorageString

open SolidCore.Solidity.Source

-- `reason = "not allowed here"; require(false, reason);`
private def runFn : ContractItem :=
  ContractItem.function
    { kind := FunctionKind.function, name := some "run",
      visibility := some Visibility.external_,
      mutability := StateMutability.nonpayable,
      params := [], returns := [],
      virtual := false, override? := none, modifiers := [],
      body := some (Stmt.block
        [ Stmt.expr
            (Expr.assign (Expr.ident "reason") AssignOp.assign
              (Expr.literal (Literal.string "not allowed here")))
        , Stmt.expr
            (Expr.call (Expr.ident "require")
              [ Arg.positional (Expr.literal (Literal.bool false))
              , Arg.positional (Expr.ident "reason") ]) ]) }

def importedContractDecl0 : ContractDecl :=
  { kind := ContractKind.contract, name := "C",
    abstract := false, bases := [],
    items := [ ContractItem.stateVar { name := "reason", ty := Ty.string }, runFn ] }

def importedContract : ContractDecl := importedContractDecl0

def importedSourceUnit : SourceUnit :=
  { items := [SourceItem.pragma "solidity" "^0.8.35",
              SourceItem.contract importedContractDecl0] }

def importedContractAccepted : Bool :=
  TypeCheck.Result.isOk (TypeCheck.TypecheckedInput.checkedSourceUnit importedSourceUnit)

end RequireReasonStorageString
end SolcAstImport
end Solidity
end SolidCore

namespace SolidCore
namespace Solidity
namespace Witness
namespace RequireReasonStorageString

open SolidCore.Solidity.Source
open SolidCore.Solidity.TypeCheck

abbrev Fam := SolidCore.Solidity.SolcAstImport.RequireReasonStorageString.importedContract

def accepted : Bool :=
  SolidCore.Solidity.SolcAstImport.RequireReasonStorageString.importedContractAccepted

-- `"not allowed here"` as raw bytes (16 bytes).
private def reasonBytes : List SolidCore.Solidity.Source.Byte :=
  [110, 111, 116, 32, 97, 108, 108, 111, 119, 101, 100, 32, 104, 101, 114, 101]

-- The divergence witness: `run()` reverts with the ABI-encoded `Error(string)`
-- carrying the storage string "not allowed here", matching solc+EVM (pre-fix
-- this reverted with `Panic(0)`).
def run_reverts_error_string : Except TypeError Bool := do
  let result ←
    CheckedInput.ownCall 64 Fam
      (SolidCore.Solidity.Source.CallTarget.name "run")
      SolidCore.Solidity.Source.State.empty []
  match result with
  | SolidCore.Solidity.Source.CallResult.reverted _
      (SolidCore.Solidity.Source.RevertData.raw bytes) =>
      Except.ok
        (bytes.take 4 == [8, 195, 121, 160]          -- Error(string) selector
          && bytes.length == 100                     -- 4 + 3*32
          && (bytes.drop 68).take 16 == reasonBytes)
  -- The direct `RevertData.error` form (should the pipeline normalize to it) is
  -- also an acceptable Error(string) observable.
  | SolidCore.Solidity.Source.CallResult.reverted _
      (SolidCore.Solidity.Source.RevertData.error reason) =>
      Except.ok (reason == "not allowed here")
  | _ => Except.ok false

private def isOkTrue : Except TypeError Bool → Bool
  | Except.ok true => true
  | _ => false

#guard accepted
#guard isOkTrue run_reverts_error_string

end RequireReasonStorageString
end Witness
end Solidity
end SolidCore

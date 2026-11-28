import SolidCore.Solidity.Checked
import SolidCore.Witness.Checked

set_option maxHeartbeats 8000000

/-!
STORAGE-PUSH-LENGTH-BOUND — `push` onto a storage array of `2^64` or more elements.

```solidity
contract C {
    uint256[] a;
    function grow() external returns (uint256) { a.push(); return a.length; }
}
```

solc 0.8.35's IR checks the old length before a storage push
(`storage_array_push_zero`): `if iszero(lt(oldLen, 18446744073709551616)) { panic_error_0x41() }`,
so a push onto an array of `2^64` or more elements reverts with Panic(0x41). solidity-lean
formerly failed only when the new length reached `2^256` (RevertData.overflow), so from a length
of `2^64` it pushed where solc panics.

Witnesses: from a length word of `2^64 - 1`, `grow()` returns `2^64`; from `2^64` it reverts with
Panic(0x41).
-/

namespace SolidCore
namespace Solidity
namespace SolcAstImport
namespace StoragePushLengthBound

open SolidCore.Solidity.Source

-- function grow() external returns (uint256) { a.push(); return a.length; }
private def growFn : ContractItem :=
  ContractItem.function
    { kind := FunctionKind.function, name := some "grow",
      visibility := some Visibility.external_,
      mutability := StateMutability.nonpayable,
      params := [],
      returns := [{ name := none, ty := Ty.uint 256, location := none }],
      virtual := false, override? := none, modifiers := [],
      body := some (Stmt.block
        [ Stmt.expr (Expr.call (Expr.member (Expr.ident "a") "push") [])
        , Stmt.returnValues (some (Expr.member (Expr.ident "a") "length")) ]) }

def importedContract : ContractDecl :=
  { kind := ContractKind.contract, name := "C",
    abstract := false, bases := [],
    items :=
      [ ContractItem.stateVar { name := "a", ty := Ty.array (Ty.uint 256) none }
      , growFn ] }

def importedSourceUnit : SourceUnit :=
  { items := [SourceItem.pragma "solidity" "^0.8.35",
              SourceItem.contract importedContract] }

def importedContractAccepted : Bool :=
  TypeCheck.Result.isOk (TypeCheck.TypecheckedInput.checkedSourceUnit importedSourceUnit)

end StoragePushLengthBound
end SolcAstImport
end Solidity
end SolidCore

namespace SolidCore
namespace Solidity
namespace Witness
namespace StoragePushLengthBound

open SolidCore.Solidity.Source
open SolidCore.Solidity.TypeCheck

abbrev Fam := SolidCore.Solidity.SolcAstImport.StoragePushLengthBound.importedContract

def accepted : Bool :=
  SolidCore.Solidity.SolcAstImport.StoragePushLengthBound.importedContractAccepted

/-- The state whose length word of `a` (slot 0) is `n`. -/
private def withLength (n : Nat) : State := State.empty.storeSlot 0 n

/-- From a length of `2^64 - 1`, the push succeeds and the length becomes `2^64`. -/
def grow_below_bound : Except TypeError Bool :=
  Examples.checkedOwnCallWordMatches 256 Fam "grow" (withLength (2 ^ 64 - 1)) [] (2 ^ 64)

/-- From a length of `2^64`, the push reverts with Panic(0x41), as solc's does. -/
def grow_at_bound_panics : Except TypeError Bool :=
  Examples.checkedOwnCallPanicMatches 256 Fam "grow" (withLength (2 ^ 64)) [] 0x41

private def isOkTrue : Except TypeError Bool -> Bool
  | Except.ok true => true
  | _ => false

#guard accepted
#guard isOkTrue grow_below_bound
#guard isOkTrue grow_at_bound_panics

end StoragePushLengthBound
end Witness
end Solidity
end SolidCore

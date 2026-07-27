import SolidCore.Solidity.Checked
import SolidCore.Witness.Checked

set_option maxHeartbeats 8000000

/-!
FIXED-STORAGE-ARRAY-LENGTH (soundness gap): the `.length` of a fixed-size STORAGE
array must return the compile-time constant `N` (solc folds `T[N].length` to `N`).

```solidity
contract T { uint256[3] a; function f() external returns (uint256 r) { r = a.length; } }
```

solc+EVM: `f()` => `3`.

solidity-lean formerly REVERTED with `Panic(0)`. A state-variable `.length`
lowers to `Expr.storage key` (the HEADER read — the `.length` convention: for a
dynamic array / `bytes` / `string` the slot value IS the length). But a
fixed-size array has NO length header slot, so the header read
(`loadStorageField`) MATERIALISED the whole array (`Value.fixedArray [0,0,0]`),
which then dead-ended in `RevertData.typeMismatch` when the scalar `.length`
consumer (`uint256 r = ...`) coerced it. A MEMORY fixed array was fine (its
`.length` folds through `Value.length?`).

Fix: header-mode reads route through `Runtime.loadStorageFieldHeader`, which
yields the constant size `N` for a `StorageLayout.fixedArray` and delegates to
the ordinary field read for every other layout. A whole-fixed-array value read
(a `ref`/`load`, not `header`) is unaffected.
-/

namespace SolidCore
namespace Solidity
namespace Witness
namespace FixedStorageArrayLength

open SolidCore.Solidity
open SolidCore.Solidity.Source
open SolidCore.Solidity.TypeCheck

private def u256 : Ty := Ty.uint 256

private def fixed3 : Ty := Ty.array (Ty.uint 256) (some 3)

private def fn (name : String) (rt : Ty) (body : List Stmt) : ContractItem :=
  ContractItem.function
    { kind := FunctionKind.function,
      name := some name,
      visibility := some Visibility.external_,
      mutability := StateMutability.nonpayable,
      params := [],
      returns := [{ name := some "r", ty := rt, location := none }],
      virtual := false, override? := none, modifiers := [],
      body := some (Stmt.block body) }

private def len (base : Expr) : Expr := Expr.member base "length"

-- The exact submission plus a two-element sibling to pin the fold to `N`.
def contract : ContractDecl :=
  { kind := ContractKind.contract, name := "T", abstract := false, bases := [],
    items :=
      [ ContractItem.stateVar { name := "a", ty := fixed3 }
      , ContractItem.stateVar { name := "b", ty := Ty.array (Ty.uint 256) (some 7) }
        -- `r = a.length;`
      , fn "f" u256
          [ Stmt.expr
              (Expr.assign (Expr.ident "r") AssignOp.assign (len (Expr.ident "a"))) ]
        -- `r = b.length;`  (a different constant N=7)
      , fn "g" u256
          [ Stmt.expr
              (Expr.assign (Expr.ident "r") AssignOp.assign (len (Expr.ident "b"))) ] ] }

def sourceUnit : SourceUnit :=
  { items := [SourceItem.pragma "solidity" "^0.8.35", SourceItem.contract contract] }

def accepted : Bool :=
  TypeCheck.Result.isOk (TypeCheck.TypecheckedInput.checkedSourceUnit sourceUnit)

private def isOkTrue : Except TypeError Bool → Bool
  | Except.ok true => true
  | _ => false

-- The submission: `uint256[3] a; a.length` == 3.
def f_len : Except TypeError Bool :=
  Examples.checkedOwnCallWordMatches 256 contract "f" State.empty [] 3
-- A distinct fixed size confirms the length is the layout constant, not a fold of 3.
def g_len : Except TypeError Bool :=
  Examples.checkedOwnCallWordMatches 256 contract "g" State.empty [] 7

#eval accepted
#eval f_len
#eval g_len

#guard accepted
#guard isOkTrue f_len
#guard isOkTrue g_len

end FixedStorageArrayLength
end Witness
end Solidity
end SolidCore

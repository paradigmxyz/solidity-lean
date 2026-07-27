import SolidCore.Solidity.Checked
import SolidCore.Witness.Checked

set_option maxHeartbeats 8000000

/-!
STORAGE-BYTESN-LENGTH (soundness gap): the `.length` of a STORAGE `bytesN`
state variable must return the compile-time constant width `N`
(solc folds `bytesN.length` to `N`).

```solidity
contract T { bytes3 b3; function f() external returns (uint256 r) { r = b3.length; } }
```

solc+EVM: `f()` => `3`.

solidity-lean returns `0`: a bare state-variable `.length` reads the HEADER of
the field. For a `bytesN` scalar layout the header read materialises the slot
WORD (default 0), and the `.length` consumer treats that word AS the length
(the dynamic-array / `bytes` / `string` convention), yielding the slot value 0
rather than the constant width N. A LOCAL / PARAM `bytesN` was already fixed
(`BytesNLengthMember`) because it materialises as `Value.fixedBytes size _`,
which folds through `Value.length?`; the storage header word never carried the
width tag.
-/

namespace SolidCore
namespace Solidity
namespace Witness
namespace StorageBytesNLength

open SolidCore.Solidity
open SolidCore.Solidity.Source
open SolidCore.Solidity.TypeCheck

private def u256 : Ty := Ty.uint 256

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

-- The exact submission plus a `bytes32` sibling to pin the fold to `N`.
def contract : ContractDecl :=
  { kind := ContractKind.contract, name := "T", abstract := false, bases := [],
    items :=
      [ ContractItem.stateVar { name := "b3", ty := Ty.bytesN 3 }
      , ContractItem.stateVar { name := "b32", ty := Ty.bytesN 32 }
        -- `r = b3.length;`
      , fn "f" u256
          [ Stmt.expr
              (Expr.assign (Expr.ident "r") AssignOp.assign (len (Expr.ident "b3"))) ]
        -- `r = b32.length;` (a different constant N=32)
      , fn "g" u256
          [ Stmt.expr
              (Expr.assign (Expr.ident "r") AssignOp.assign (len (Expr.ident "b32"))) ] ] }

def sourceUnit : SourceUnit :=
  { items := [SourceItem.pragma "solidity" "^0.8.35", SourceItem.contract contract] }

def accepted : Bool :=
  TypeCheck.Result.isOk (TypeCheck.TypecheckedInput.checkedSourceUnit sourceUnit)

private def isOkTrue : Except TypeError Bool → Bool
  | Except.ok true => true
  | _ => false

-- The submission: `bytes3 b3; b3.length` == 3.
def f_len : Except TypeError Bool :=
  Examples.checkedOwnCallWordMatches 256 contract "f" State.empty [] 3
-- A distinct width confirms the length is the type constant, not a fold of 3.
def g_len : Except TypeError Bool :=
  Examples.checkedOwnCallWordMatches 256 contract "g" State.empty [] 32

open SolidCore.Solidity.Source in
def rawResult : Except TypeError (CallResult) :=
  CheckedInput.ownCall 256 contract (CallTarget.name "f") State.empty []

open SolidCore.Solidity.Source in
def describe : String :=
  match rawResult with
  | Except.error _ => "typeerror"
  | Except.ok (CallResult.returned _ vs) => s!"returned {repr vs}"
  | Except.ok (CallResult.reverted _ w) => s!"reverted {repr w}"

#eval accepted
#eval f_len
#eval g_len
#eval describe

#guard accepted
#guard isOkTrue f_len
#guard isOkTrue g_len

end StorageBytesNLength
end Witness
end Solidity
end SolidCore

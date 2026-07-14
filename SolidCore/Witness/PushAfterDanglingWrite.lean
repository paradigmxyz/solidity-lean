import SolidCore.Solidity.Checked
import SolidCore.Witness.Checked

set_option maxHeartbeats 12000000

/-!
PUSH-AFTER-DANGLING-WRITE (regression): a storage pointer captures arr[1]'s
slot, `pop()` frees (and zero-clears) it, a write THROUGH the dangling pointer
lands 5 in the freed slot, then `push()` regrows the array. solc/EVM `push()`
only bumps the length word and relies on the pre-existing zero invariant — it
does NOT re-zero the regrown element. So the dangling 5 survives and
`arr[1].a` reads back 5 (real solc 0.8.35 + EVM ground truth).

The Lean engine used to DEEP-CLEAR the regrown element on `push()`, returning 0.
-/

namespace SolidCore
namespace Solidity
namespace Witness
namespace PushAfterDanglingWrite

open SolidCore.Solidity.Source
open SolidCore.Solidity.TypeCheck

def runContract : ContractDecl :=
{ kind := ContractKind.contract
  name := "C"
  abstract := false
  bases := []
  items :=
    [ ContractItem.structDecl
        { name := "S", fields := [{ name := "a", ty := Ty.uint 256 }] }
    , ContractItem.stateVar
        { name := "arr"
          ty := Ty.array (Ty.user ({ segments := ["S"] })) none
          visibility := some Visibility.internal_
          mutability := VarMutability.mutable
          override? := none
          init := none }
    , ContractItem.function
        { kind := FunctionKind.function
          name := some "run"
          visibility := some Visibility.external_
          mutability := StateMutability.nonpayable
          params := []
          returns := [{ name := none, ty := Ty.uint 256, location := none }]
          virtual := false
          override? := none
          modifiers := []
          body := some (Stmt.block
            [ Stmt.expr (Expr.call (Expr.member (Expr.ident "arr") "push") [])
            , Stmt.expr (Expr.call (Expr.member (Expr.ident "arr") "push") [])
            , Stmt.varDecl
                [{ name := some "p", ty := Ty.user ({ segments := ["S"] }),
                   location := some DataLocation.storage }]
                (some (Expr.index (Expr.ident "arr") (Expr.literal (Literal.number "1"))))
            , Stmt.expr (Expr.call (Expr.member (Expr.ident "arr") "pop") [])
            , Stmt.expr (Expr.assign (Expr.member (Expr.ident "p") "a")
                AssignOp.assign (Expr.literal (Literal.number "5")))
            , Stmt.expr (Expr.call (Expr.member (Expr.ident "arr") "push") [])
            , Stmt.returnValues
                (some (Expr.member
                  (Expr.index (Expr.ident "arr") (Expr.literal (Literal.number "1"))) "a")) ]) } ] }

def runSourceUnit : SourceUnit :=
  { items := [SourceItem.pragma "solidity" "^0.8.35", SourceItem.contract runContract] }

def accepted : Bool :=
  TypeCheck.Result.isOk (TypeCheck.TypecheckedInput.checkedSourceUnit runSourceUnit)

-- Real solc 0.8.35 + EVM ground truth: `run()` returns 5 (the dangling write
-- survives the `push()` regrow, which does not re-zero the element).
def run_push_after_dangling_write_is_5 : Except TypeError Bool :=
  Examples.checkedOwnCallWordMatches 512 runContract "run" State.empty [] 5

private def isOkTrue : Except TypeError Bool -> Bool
  | Except.ok true => true
  | _ => false

#guard accepted
#guard isOkTrue run_push_after_dangling_write_is_5

end PushAfterDanglingWrite
end Witness
end Solidity
end SolidCore

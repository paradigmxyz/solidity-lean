import SolidCore.Solidity.Checked
import SolidCore.Witness.Checked

set_option maxHeartbeats 8000000

/-!
PUSH-THROUGH-TERNARY-STORAGE-REF — `.push` directly on a ternary-SELECTED
storage array reference.

```solidity
contract C {
    uint256[] a;
    uint256[] b;
    function run() external returns (uint256) {
        bool cond = true;
        (cond ? b : a).push(77);
        return b.length * 100 + b[0];
    }
}
```

solc evaluates `(cond ? b : a)` to a storage-reference lvalue, then pushes on
the SELECTED array. With `cond == true` this pushes `77` onto `b`, so
`b.length == 1`, `b[0] == 77`, and `run()` returns `1 * 100 + 77 = 177`.

solidity-lean formerly REVERTED (empty). The statement-position push lowering
(`storageArrayPushPathCore?` / `storageArrayPushPathCoreWithEnv?` in
`SolidCore/Solidity/Interface.lean`) resolves its target with
`Expr.storagePathCore?`, which only names an `Expr.ident`/`Expr.index` path. A
ternary target returned `none`, so the push statement failed to lower and the
whole contract fell CLOSED to a revert.

The fix branches a ternary-selected push target into an `ifElse`:
`if cond { b.push(v) } else { a.push(v) }`. Only the taken branch runs, so `v`
is evaluated exactly once — the same on-chain effect as
select-the-reference-then-push. It recurses so either branch may itself be a
nested ternary or an index path.

Real-EVM ground truth (adjudicated divergence): `run()` => `success`, return
word `177`, storage `b.length = 1`, `b[0] = 77`.
-/

namespace SolidCore
namespace Solidity
namespace SolcAstImport
namespace PushThroughTernaryStorageRef

open SolidCore.Solidity.Source

private def lit (s : String) : Expr := Expr.literal (Literal.number s)

private def uintArrayTy : Ty := Ty.array (Ty.uint 256) none

-- `(cond ? <thenArr> : <elseArr>).push(77);`
private def ternaryPushStmt (thenArr elseArr : String) : Stmt :=
  Stmt.expr
    (Expr.call
      (Expr.member
        (Expr.ternary (Expr.ident "cond")
          (Expr.ident thenArr) (Expr.ident elseArr))
        "push")
      [Arg.positional (lit "77")])

-- `return <arr>.length * 100 + <arr>[0];`
private def returnLenElem (arr : String) : Stmt :=
  Stmt.returnValues
    (some
      (Expr.binary BinaryOp.add
        (Expr.binary BinaryOp.mul
          (Expr.member (Expr.ident arr) "length") (lit "100"))
        (Expr.index (Expr.ident arr) (lit "0"))))

-- `bool cond = <b>;`
private def condDecl (b : Bool) : Stmt :=
  Stmt.varDecl [{ name := some "cond", ty := Ty.bool, location := none }]
    (some (Expr.literal (Literal.bool b)))

-- run(): cond = true -> pushes onto `b`, reads `b`. Returns 177.
private def runFn : ContractItem :=
  ContractItem.function
    { kind := FunctionKind.function, name := some "run",
      visibility := some Visibility.external_,
      mutability := StateMutability.nonpayable,
      params := [],
      returns := [{ name := none, ty := Ty.uint 256, location := none }],
      virtual := false, override? := none, modifiers := [],
      body := some (Stmt.block
        [ condDecl true, ternaryPushStmt "b" "a", returnLenElem "b" ]) }

-- runElse(): cond = false -> pushes onto `a`, reads `a`. Exercises the ELSE
-- branch of the lowered `ifElse`. Also returns 177.
private def runElseFn : ContractItem :=
  ContractItem.function
    { kind := FunctionKind.function, name := some "runElse",
      visibility := some Visibility.external_,
      mutability := StateMutability.nonpayable,
      params := [],
      returns := [{ name := none, ty := Ty.uint 256, location := none }],
      virtual := false, override? := none, modifiers := [],
      body := some (Stmt.block
        [ condDecl false, ternaryPushStmt "b" "a", returnLenElem "a" ]) }

def importedContractDecl0 : ContractDecl :=
  { kind := ContractKind.contract, name := "C",
    abstract := false, bases := [],
    items :=
      [ ContractItem.stateVar { name := "a", ty := uintArrayTy }
      , ContractItem.stateVar { name := "b", ty := uintArrayTy }
      , runFn, runElseFn ] }

def importedContract : ContractDecl := importedContractDecl0

def importedSourceUnit : SourceUnit :=
  { items := [SourceItem.pragma "solidity" "^0.8.35",
              SourceItem.contract importedContractDecl0] }

def importedContractAccepted : Bool :=
  TypeCheck.Result.isOk (TypeCheck.TypecheckedInput.checkedSourceUnit importedSourceUnit)

end PushThroughTernaryStorageRef
end SolcAstImport
end Solidity
end SolidCore

namespace SolidCore
namespace Solidity
namespace Witness
namespace PushThroughTernaryStorageRef

open SolidCore.Solidity.Source
open SolidCore.Solidity.TypeCheck

abbrev Fam := SolidCore.Solidity.SolcAstImport.PushThroughTernaryStorageRef.importedContract

def accepted : Bool :=
  SolidCore.Solidity.SolcAstImport.PushThroughTernaryStorageRef.importedContractAccepted

private def callWord (fn : Name) (expected : Word) : Except TypeError Bool :=
  Examples.checkedOwnCallWordMatches 256 Fam fn State.empty [] expected

-- The divergence witness: `run()` (cond = true) pushes 77 onto `b` and returns
-- 1 * 100 + 77 = 177. Pre-fix it REVERTED (the ternary push failed to lower).
def run_is_177 : Except TypeError Bool := callWord "run" 177

-- ELSE branch: `runElse()` (cond = false) pushes 77 onto `a`, returns 177.
def runElse_is_177 : Except TypeError Bool := callWord "runElse" 177

private def isOkTrue : Except TypeError Bool -> Bool
  | Except.ok true => true
  | _ => false

#guard accepted
#guard isOkTrue run_is_177
#guard isOkTrue runElse_is_177

end PushThroughTernaryStorageRef
end Witness
end Solidity
end SolidCore

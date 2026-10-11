import SolidCore.Solidity.Checked
import SolidCore.Witness.Checked

set_option maxHeartbeats 8000000

/-!
POP-THROUGH-TERNARY-STORAGE-REF — `pop()` directly on a ternary-selected
storage array reference.

```solidity
contract C {
    uint256[] left;
    uint256[] right;
    function run(bool chooseLeft) external returns (uint256) {
        left.push();
        right.push();
        (chooseLeft ? left : right).pop();
        return left.length * 10 + right.length;
    }
}
```

Solidity selects a storage-reference lvalue and pops only that array. Before
this fix, statement lowering tried to turn the conditional receiver into a
single static storage path. That failed and the whole function fell closed to
an empty revert. The env-aware pop lowering now branches on the condition and
executes exactly one concrete pop.

Real-EVM ground truth for the contest witness: `run(true)` succeeds, returns
`1`, and leaves `left.length = 0`, `right.length = 1`.
-/

namespace SolidCore
namespace Solidity
namespace SolcAstImport
namespace PopThroughTernaryStorageRef

open SolidCore.Solidity.Source

private def lit (s : String) : Expr := Expr.literal (Literal.number s)

private def uintArrayTy : Ty := Ty.array (Ty.uint 256) none

private def emptyPush (arr : String) : Stmt :=
  Stmt.expr (Expr.call (Expr.member (Expr.ident arr) "push") [])

private def ternaryPop : Stmt :=
  Stmt.expr
    (Expr.call
      (Expr.member
        (Expr.ternary (Expr.ident "chooseLeft")
          (Expr.ident "left") (Expr.ident "right"))
        "pop")
      [])

private def returnLengths : Stmt :=
  Stmt.returnValues
    (some
      (Expr.binary BinaryOp.add
        (Expr.binary BinaryOp.mul
          (Expr.member (Expr.ident "left") "length") (lit "10"))
        (Expr.member (Expr.ident "right") "length")))

private def runFn : ContractItem :=
  ContractItem.function
    { kind := FunctionKind.function, name := some "run",
      visibility := some Visibility.external_,
      mutability := StateMutability.nonpayable,
      params := [{ name := some "chooseLeft", ty := Ty.bool, location := none }],
      returns := [{ name := none, ty := Ty.uint 256, location := none }],
      virtual := false, override? := none, modifiers := [],
      body := some (Stmt.block
        [emptyPush "left", emptyPush "right", ternaryPop, returnLengths]) }

def importedContractDecl0 : ContractDecl :=
  { kind := ContractKind.contract, name := "C",
    abstract := false, bases := [],
    items :=
      [ ContractItem.stateVar { name := "left", ty := uintArrayTy }
      , ContractItem.stateVar { name := "right", ty := uintArrayTy }
      , runFn ] }

def importedContract : ContractDecl := importedContractDecl0

def importedSourceUnit : SourceUnit :=
  { items := [SourceItem.pragma "solidity" "0.8.35",
              SourceItem.contract importedContractDecl0] }

def importedContractAccepted : Bool :=
  TypeCheck.Result.isOk
    (TypeCheck.TypecheckedInput.checkedSourceUnit importedSourceUnit)

end PopThroughTernaryStorageRef
end SolcAstImport
end Solidity
end SolidCore

namespace SolidCore
namespace Solidity
namespace Witness
namespace PopThroughTernaryStorageRef

open SolidCore.Solidity.Source
open SolidCore.Solidity.TypeCheck

abbrev Fam :=
  SolidCore.Solidity.SolcAstImport.PopThroughTernaryStorageRef.importedContract

def accepted : Bool :=
  SolidCore.Solidity.SolcAstImport.PopThroughTernaryStorageRef.importedContractAccepted

def chooseLeft_is_1 : Except TypeError Bool :=
  Examples.checkedOwnCallWordMatches
    256 Fam "run" State.empty [Value.word 1] 1

def chooseRight_is_10 : Except TypeError Bool :=
  Examples.checkedOwnCallWordMatches
    256 Fam "run" State.empty [Value.word 0] 10

private def isOkTrue : Except TypeError Bool -> Bool
  | Except.ok true => true
  | _ => false

#guard accepted
#guard isOkTrue chooseLeft_is_1
#guard isOkTrue chooseRight_is_10

end PopThroughTernaryStorageRef
end Witness
end Solidity
end SolidCore

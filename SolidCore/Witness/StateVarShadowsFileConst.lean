import SolidCore.Solidity.Checked
import SolidCore.Witness.Checked

set_option maxHeartbeats 8000000

/-!
STATE-VAR-SHADOWS-FILE-CONST — a contract-level *storage* state variable
shadows a same-name file-level `constant`; a function reads the state var.

```solidity
uint256 constant X = 5;          // file-level constant
contract B {
    uint256 internal X = 9;      // storage state var, shadows file-level X in B
    function run() external view returns (uint256) { return X; }
}
```

solc+EVM: within `B`, the storage variable `X` shadows the file-level constant,
so `run()` reads the storage slot (`X = 9`). Result `9` (adjudicated observable
`success|w:9`, storage `0:9`).

Pre-fix the interpreter inlined `B.run`'s body against a constant env that still
carried the file-level `X = 5` (a storage state var contributes no
`constantEntry?`, so nothing suppressed the file-level entry), so the bare
`X` was constant-folded to `5` and the storage read never happened — `run()`
yielded `5`.

Fix: the per-contract constant scope now drops any file-level/qualified constant
whose name is shadowed by a non-constant state variable in that contract's own
lexical scope (own + inherited, C3), so `X` stays a storage read.

Ground truth: pinned solc 0.8.35 + real EVM (adjudicated observable
`success|w:9`, `sto=0:9`).
-/

namespace SolidCore
namespace Solidity
namespace SolcAstImport
namespace StateVarShadowsFileConst

def contractB : ContractDecl :=
{ kind := ContractKind.contract
  name := "B"
  abstract := false
  bases := []
  items := [(ContractItem.stateVar
  { name := "X",
    ty := Ty.uint 256,
    visibility := some Visibility.internal_,
    mutability := VarMutability.mutable,
    override? := none,
    init := some (Expr.literal (Literal.number "9")) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "run",
    visibility := some Visibility.external_,
    mutability := StateMutability.view,
    params := [],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.ident "X"))]) })] }

def sourceUnit : SourceUnit :=
  { items := [SourceItem.pragma "solidity" "0.8.35", SourceItem.freeConstant
  { name := "X",
    ty := Ty.uint 256,
    visibility := none,
    mutability := VarMutability.constant,
    override? := none,
    init := some (Expr.literal (Literal.number "5")) }, SourceItem.contract contractB] }

def accepted : Bool :=
  TypeCheck.Result.isOk (TypeCheck.TypecheckedInput.checkedSourceUnit sourceUnit)

end StateVarShadowsFileConst
end SolcAstImport

namespace Witness
namespace StateVarShadowsFileConst

open SolidCore.Solidity.Source
open SolidCore.Solidity.TypeCheck

abbrev U := SolidCore.Solidity.SolcAstImport.StateVarShadowsFileConst.sourceUnit

def accepted : Bool :=
  SolidCore.Solidity.SolcAstImport.StateVarShadowsFileConst.accepted

private def isOkTrue : Except TypeError Bool → Bool
  | Except.ok true => true
  | _ => false

/-- Post-deploy storage: the inline initializer `X = 9` leaves storage slot 0 at
    `9` (the adjudicated `sto=0:9`). -/
def deployedState : CoreState := State.empty.storeSlot 0 9

/-- The divergence witness: reading `X` yields the storage slot (`9`), matching
    solc+EVM. Pre-fix the file-level constant `X = 5` was folded in, so `run()`
    yielded `5` regardless of storage. -/
def run_is_9 : Except TypeError Bool :=
  Examples.checkedCallWordMatches 4000 U "B" "run" deployedState [] 9

/-- Control: the pre-fix wrong value `5` (the folded file-level constant) must
    NOT be produced. -/
def run_not_5 : Except TypeError Bool :=
  (Examples.checkedCallWordMatches 4000 U "B" "run" deployedState [] 5).map not

#guard accepted
#guard isOkTrue run_is_9
#guard isOkTrue run_not_5

end StateVarShadowsFileConst
end Witness
end Solidity
end SolidCore

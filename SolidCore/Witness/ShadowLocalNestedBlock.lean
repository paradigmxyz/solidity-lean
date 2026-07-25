import SolidCore.Solidity.Checked
import SolidCore.Witness.Checked

set_option maxHeartbeats 8000000

/-!
SHADOW-LOCAL-IN-NESTED-BLOCK — a nested-block local shadows a same-name state
variable; the compound assignment inside the block must hit the LOCAL, and the
state variable must be unchanged.

```solidity
contract T {
    uint256 sv = 100;
    function run() public returns (uint256) {
        { uint256 sv = 5; sv += 1; }   // local sv: 5 -> 6, dies at block end
        return sv;                     // reads state sv = 100
    }
}
```

solc+EVM: the nested-block `uint256 sv` shadows the state variable only inside
the block, so `sv += 1` mutates the LOCAL (5 -> 6). At block end the local dies;
`return sv` reads the untouched state variable `100`, and storage slot 0 stays
`100`. Observable `success|w:100##STO##0:100`.

Pre-fix the source→core lowering resolved a bare identifier to a storage
reference whenever its name was a state-variable name (`sourceIdentCore` /
`Expr.toCore?` consult a fixed `storageNames` list that is never narrowed by
locally-declared names). So the shadowing local `sv` was ignored: `sv += 1`
lowered to a STORAGE read-modify-write (100 -> 101) and `return sv` read storage,
yielding the wrong observable `success|w:101##STO##0:101`.

Ground truth: pinned solc 0.8.35 + real EVM (adjudicated observable
`success|w:100`, storage `0:100`).
-/

namespace SolidCore
namespace Solidity
namespace SolcAstImport
namespace ShadowLocalNestedBlock

def contractT : ContractDecl :=
{ kind := ContractKind.contract
  name := "T"
  abstract := false
  bases := []
  items := [(ContractItem.stateVar
  { name := "sv",
    ty := Ty.uint 256,
    init := some (Expr.literal (Literal.number "100")) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "run",
    visibility := some Visibility.public_,
    mutability := StateMutability.nonpayable,
    params := [],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block
      [ Stmt.block
          [ Stmt.varDecl [{ name := some "sv", ty := Ty.uint 256, location := none }]
              (some (Expr.literal (Literal.number "5")))
          , Stmt.expr (Expr.assign (Expr.ident "sv") AssignOp.addAssign
              (Expr.literal (Literal.number "1"))) ]
      , Stmt.returnValues (some (Expr.ident "sv")) ]) })] }

def sourceUnit : SourceUnit :=
  { items := [SourceItem.pragma "solidity" "0.8.35", SourceItem.contract contractT] }

def accepted : Bool :=
  TypeCheck.Result.isOk (TypeCheck.TypecheckedInput.checkedSourceUnit sourceUnit)

end ShadowLocalNestedBlock
end SolcAstImport

namespace Witness
namespace ShadowLocalNestedBlock

open SolidCore.Solidity.Source
open SolidCore.Solidity.TypeCheck

abbrev U := SolidCore.Solidity.SolcAstImport.ShadowLocalNestedBlock.sourceUnit

def accepted : Bool :=
  SolidCore.Solidity.SolcAstImport.ShadowLocalNestedBlock.accepted

private def isOkTrue : Except TypeError Bool → Bool
  | Except.ok true => true
  | _ => false

/-- Deploy state: run the constructor so the state variable `sv` is initialized to
    `100` (its declared initializer runs at construction), exactly as the
    adjudicator deployed `T` before calling `run` (ground-truth storage `0:100`). -/
def deployedState : Except TypeError State :=
  Examples.checkedConstructState 4000 U "T" []

/-- The divergence witness: on the deployed state (`sv = 100`), `run()` returns
    `100` — the nested-block local `sv` (5 → 6) dies at block end and `return sv`
    reads the untouched state variable, matching solc+EVM. Pre-fix the lowering
    treated the block-local `sv` as the state variable, so `sv += 1` bumped
    storage (100 → 101) and `run()` yielded `101` (storage `0:101`). -/
def run_is_100 : Except TypeError Bool := do
  let st ← deployedState
  Examples.checkedCallWordMatches 4000 U "T" "run" st [] 100

/-- Control: the pre-fix wrong value `101` must NOT be produced. -/
def run_not_101 : Except TypeError Bool := do
  let st ← deployedState
  (Examples.checkedCallWordMatches 4000 U "T" "run" st [] 101).map not

/-- The same defect over the empty state (no constructor, `sv = 0`): `run()` must
    read the untouched `0`, never the pre-fix `1`. -/
def run_empty_is_0 : Except TypeError Bool :=
  Examples.checkedCallWordMatches 4000 U "T" "run" State.empty [] 0

#guard accepted
#guard isOkTrue run_is_100
#guard isOkTrue run_not_101
#guard isOkTrue run_empty_is_0

end ShadowLocalNestedBlock
end Witness
end Solidity
end SolidCore

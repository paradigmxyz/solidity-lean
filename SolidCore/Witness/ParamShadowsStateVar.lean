import SolidCore.Solidity.Checked
import SolidCore.Witness.Checked

set_option maxHeartbeats 8000000

/-!
PARAM-SHADOWS-STATEVAR — a function parameter shadows a same-name state
variable; the body must read the PARAMETER, not the storage slot.

```solidity
contract C {
    uint256 x = 100;                                   // storage slot 0
    function run(uint256 x) external view returns (uint256) {
        return x + 1;                                  // reads the PARAMETER
    }
}
```

solc+EVM: inside `run`, the parameter `x` shadows the state variable `x` (solc
resolves the nearest declaration), so `x + 1` reads the argument. Called with
`run(7)` the result is `8` (adjudicated observable `success|w:8`, storage
unchanged at `sto=0:100`).

Pre-fix the entrypoint lowering turned every bare state-variable-named identifier
into a storage read keyed by the contract's state-name set, WITHOUT removing the
names shadowed by the function's own parameters/named returns. So `run`'s `x`
lowered to an SLOAD of slot 0 and yielded `100 + 1 = 101`.

Fix: `FunctionDecl.toCore?` lowers the function body against the state-name set
with the function's parameter and named-return names removed
(`stateNamesExcludingBound`), so a shadowed bare read resolves to the local.

Ground truth: pinned solc 0.8.35 + real EVM (adjudicated observable
`success|w:8`, `sto=0:100`).
-/

namespace SolidCore
namespace Solidity
namespace SolcAstImport
namespace ParamShadowsStateVar

def contractC : ContractDecl :=
{ kind := ContractKind.contract
  name := "C"
  abstract := false
  bases := []
  items := [(ContractItem.stateVar
  { name := "x",
    ty := Ty.uint 256,
    visibility := none,
    mutability := VarMutability.mutable,
    override? := none,
    init := some (Expr.literal (Literal.number "100")) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "run",
    visibility := some Visibility.external_,
    mutability := StateMutability.view,
    params := [{ name := some "x", ty := Ty.uint 256, location := none }],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues
      (some (Expr.binary BinaryOp.add (Expr.ident "x")
        (Expr.literal (Literal.number "1"))))]) })] }

def sourceUnit : SourceUnit :=
  { items := [SourceItem.pragma "solidity" "0.8.35", SourceItem.contract contractC] }

def accepted : Bool :=
  TypeCheck.Result.isOk (TypeCheck.TypecheckedInput.checkedSourceUnit sourceUnit)

end ParamShadowsStateVar
end SolcAstImport

namespace Witness
namespace ParamShadowsStateVar

open SolidCore.Solidity.Source
open SolidCore.Solidity.TypeCheck

abbrev U := SolidCore.Solidity.SolcAstImport.ParamShadowsStateVar.sourceUnit

def accepted : Bool :=
  SolidCore.Solidity.SolcAstImport.ParamShadowsStateVar.accepted

private def isOkTrue : Except TypeError Bool → Bool
  | Except.ok true => true
  | _ => false

/-- Post-deploy storage: the inline initializer `x = 100` leaves storage slot 0
    at `100` (the adjudicated `sto=0:100`). -/
def deployedState : CoreState := State.empty.storeSlot 0 100

/-- The divergence witness: `run(7)` reads the PARAMETER (`7 + 1 = 8`), matching
    solc+EVM. Pre-fix the bare `x` read the storage slot and yielded `101`. -/
def run_is_8 : Except TypeError Bool :=
  Examples.checkedCallWordMatches 4000 U "C" "run" deployedState [Value.word 7] 8

/-- Control: the pre-fix wrong value `101` (the SLOAD of `x = 100`, plus one)
    must NOT be produced. -/
def run_not_101 : Except TypeError Bool :=
  (Examples.checkedCallWordMatches 4000 U "C" "run" deployedState
    [Value.word 7] 101).map not

#guard accepted
#guard isOkTrue run_is_8
#guard isOkTrue run_not_101

end ParamShadowsStateVar
end Witness
end Solidity
end SolidCore

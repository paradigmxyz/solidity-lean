import SolidCore.Solidity.Checked
import SolidCore.Witness.Checked

set_option maxHeartbeats 8000000

/-!
FIXED-BARE-STATE-UFIXED (coverage gap): a contract with a bare `ufixed` state
variable that is never read or written —

  contract T {
    ufixed y;
    function run() public returns (uint256) { return 1; }
  }

Real solc 0.8.35 accepts this in-scope program (bare `ufixed` is the alias for
`ufixed128x18`) and the EVM runs `run()` to success returning 1; the unused
fixed-point slot has no on-chain effect.

The bug lived in the solc-AST importer (`scripts/solc_ast_to_lean_source.py`):
`type_from_name` matched the explicit `ufixed<M>x<N>`/`fixed<M>x<N>` forms but
not the BARE `ufixed`/`fixed` aliases, which solc emits verbatim on the
elementary-type node (its typeString is `ufixed128x18`). The importer failed
closed (`unsupported Solidity elementary type 'ufixed'`) on a program solc
accepts. The Lean semantics already model `Ty.ufixed 128 18` state vars (cf.
`FixedPointBoundary.sol`'s `ufixed128x18 private plain;`); only the bare-alias
spelling was unmapped. The fix adds the two exact-name aliases so bare `ufixed`
lowers to `Ty.ufixed 128 18` (and `fixed` to `Ty.fixed 128 18`).

This witness pins the target Lean semantics for the imported program: the
contract is accepted and `run()` returns 1.
-/

namespace SolidCore
namespace Solidity
namespace Witness
namespace FixedBareStateUfixed

open SolidCore.Solidity.Source
open SolidCore.Solidity.TypeCheck

private def u256 : Ty := Ty.uint 256

private def runFn : FunctionDecl :=
  { kind := FunctionKind.function, name := some "run"
    visibility := some Visibility.public_, mutability := StateMutability.nonpayable
    params := [], returns := [{ name := none, ty := u256, location := none }]
    virtual := false, override? := none, modifiers := []
    body := some (Stmt.block
      [ Stmt.returnValues (some (Expr.literal (Literal.number "1"))) ]) }

def runContract : ContractDecl :=
{ kind := ContractKind.contract, name := "T", abstract := false, bases := []
  items :=
    [ ContractItem.stateVar
        { name := "y", ty := Ty.ufixed 128 18, visibility := some Visibility.internal_
          mutability := VarMutability.mutable, override? := none, init := none }
    , ContractItem.function runFn ] }

def runSourceUnit : SourceUnit :=
  { items := [SourceItem.pragma "solidity" "^0.8.35", SourceItem.contract runContract] }

def accepted : Bool :=
  TypeCheck.Result.isOk (TypeCheck.TypecheckedInput.checkedSourceUnit runSourceUnit)

def run_is_1 : Except TypeError Bool :=
  Examples.checkedOwnCallWordMatches 4096 runContract "run" State.empty [] 1

private def isOkTrue : Except TypeError Bool → Bool
  | Except.ok true => true
  | _ => false

#guard accepted
#guard isOkTrue run_is_1

end FixedBareStateUfixed
end Witness
end Solidity
end SolidCore

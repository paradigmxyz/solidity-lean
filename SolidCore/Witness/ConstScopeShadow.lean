import SolidCore.Solidity.Checked
import SolidCore.Witness.Checked

set_option maxHeartbeats 8000000

/-!
CONST-SCOPE-SHADOW — a file-level `constant` read by a BASE virtual, shadowed
by a same-name contract-level `constant` in the DERIVED contract.

```solidity
uint256 constant X = 5;                 // file-level
contract A {
    function g() internal virtual returns (uint256) { return X; }   // sees 5
}
contract B is A {
    uint256 internal constant X = 9;    // contract-level, shadows only in B
    function g() internal override returns (uint256) {
        return X * 100 + super.g();     // 9 * 100 + A.g() = 900 + 5
    }
    function run() external returns (uint256) { return g(); }
}
```

solc+EVM: `B.g` reads B's `X = 9`; the inherited `A.g` body resolves its
unqualified `X` in A's scope, where B's contract-level `X` is NOT visible, so it
reads the file-level `X = 5`. Result `9 * 100 + 5 = 905`.

Pre-fix the interpreter inlined EVERY contract's function body against a single
flattened, name-keyed constant env (`ContractDecls.contextualOrdinaryFunctions`
+ friends took one `constants : ConstantEnv`), in which B's `X = 9` (a
contract-level constant, ordered ahead of the file-level entry) captured the
inherited `A.g`'s `X` too — so `A.g` returned 9 and `run()` yielded the wrong
value `909`.

Fix: `ContractDecl.scopedConstantEntries` builds each contract's OWN unqualified
constant scope (own + inherited, C3 most-derived-first) and the contextual
function / modifier lowering inlines each contract's bodies against
`scopedConstantEntries ++ (file-level ++ qualified)` — so a derived constant no
longer leaks into an inherited base body, and the file-level constant remains
visible there.

Ground truth: pinned solc 0.8.35 + real EVM (adjudicated observable
`success|w:905`).
-/

namespace SolidCore
namespace Solidity
namespace SolcAstImport
namespace ConstScopeShadow

def contractA : ContractDecl :=
{ kind := ContractKind.contract
  name := "A"
  abstract := false
  bases := []
  items := [(ContractItem.function
  { kind := FunctionKind.function,
    name := some "g",
    visibility := some Visibility.internal_,
    mutability := StateMutability.nonpayable,
    params := [],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := true,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.ident "X"))]) })] }

def contractB : ContractDecl :=
{ kind := ContractKind.contract
  name := "B"
  abstract := false
  bases := [{ base := { segments := ["A"] }, args := [] }]
  items := [(ContractItem.stateVar
  { name := "X",
    ty := Ty.uint 256,
    visibility := some Visibility.internal_,
    mutability := VarMutability.constant,
    override? := none,
    init := some (Expr.literal (Literal.number "9")) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "g",
    visibility := some Visibility.internal_,
    mutability := StateMutability.nonpayable,
    params := [],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := some { bases := [] },
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.binary BinaryOp.add (Expr.binary BinaryOp.mul (Expr.ident "X") (Expr.literal (Literal.number "100"))) (Expr.call (Expr.member (Expr.ident "super") "g") [])))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "run",
    visibility := some Visibility.external_,
    mutability := StateMutability.nonpayable,
    params := [],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.call (Expr.ident "g") []))]) })] }

def sourceUnit : SourceUnit :=
  { items := [SourceItem.pragma "solidity" "0.8.35", SourceItem.freeConstant
  { name := "X",
    ty := Ty.uint 256,
    visibility := none,
    mutability := VarMutability.constant,
    override? := none,
    init := some (Expr.literal (Literal.number "5")) }, SourceItem.contract contractA, SourceItem.contract contractB] }

def accepted : Bool :=
  TypeCheck.Result.isOk (TypeCheck.TypecheckedInput.checkedSourceUnit sourceUnit)

end ConstScopeShadow
end SolcAstImport

namespace Witness
namespace ConstScopeShadow

open SolidCore.Solidity.Source
open SolidCore.Solidity.TypeCheck

abbrev U := SolidCore.Solidity.SolcAstImport.ConstScopeShadow.sourceUnit

def accepted : Bool :=
  SolidCore.Solidity.SolcAstImport.ConstScopeShadow.accepted

private def isOkTrue : Except TypeError Bool → Bool
  | Except.ok true => true
  | _ => false

/-- The divergence witness: `run()` returns `905` (`9*100 + 5`), matching
    solc+EVM. Pre-fix the inherited base `A.g` wrongly read B's `X = 9`, so
    `run()` yielded `909`. -/
def run_is_905 : Except TypeError Bool :=
  Examples.checkedCallWordMatches 4000 U "B" "run" State.empty [] 905

/-- Control: the pre-fix wrong value `909` must NOT be produced. -/
def run_not_909 : Except TypeError Bool :=
  (Examples.checkedCallWordMatches 4000 U "B" "run" State.empty [] 909).map not

#guard accepted
#guard isOkTrue run_is_905
#guard isOkTrue run_not_909

end ConstScopeShadow
end Witness
end Solidity
end SolidCore

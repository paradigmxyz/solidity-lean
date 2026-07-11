import SolidCore.Solidity.Checked
import SolidCore.Witness.Checked

/-!
NEW-CONTRACT-LOCAL-STRUCT-ARRAY (#163) — `new P[](n)` for a CONTRACT-LOCAL struct
`P` is now accepted and EXECUTES.

`contract C { struct P { uint256 x; } ... new P[](1) ... }` is accepted and run
by solc 0.8.35 (real EVM). The model's CHECKER rejected it: the `Ty.array _ none`
("new dynamic array") branch of the `Expr.newExpr` type-check returned the RAW
AST element type `["P"]`, whereas every TARGET type formed for a declared local,
return, or parameter qualifies a contract-local struct reference to `["C","P"]`
via `Ty.qualifyLocalUserTypes`. The unqualified `["P"]` never matched the
qualified target, so `expectAssignableTo` failed with
`TypeError.expectedType (array ["C","P"]) (array ["P"])` and
`importedContractAccepted = false` (over-reject, replay-reachable).

The fix (SolidCore/Solidity/TypeCheck.lean) runs the `new`-array RESULT element
type through the SAME current-scope qualification the surrounding target-type
code uses — `CheckEnv.qualifyCurrentLocalUserTypes` — which only qualifies to a
path that is actually KNOWN in the current/ancestor scope. A contract-local `P`
becomes `["C","P"]` and matches; an elementary element type or a file-level
struct (no in-scope `["C","P"]`) is left untouched, so those arrays behave
exactly as before, and a same-named struct in another contract is qualified only
to its own enclosing scope (no mirror over-accept).

Isolation ladder, pinned by execution below and by the Forge lane
`tests/forge-harness/new-contract-local-struct-array` (real solc 0.8.35 + EVM):
  * G  `localVarLen` — local var `P[] memory pa = new P[](3)`      => 3 (the fix)
  * G2 `returnArr`   — return-position `return new P[](1)`         => len 1 (the fix)
  * G3 `multiLen`    — MULTI-field local struct `Q[]`              => 2 (the fix)
  * G4 `arr2Len`     — array-of-array of the local struct `P[][]`  => 4 (the fix)
  * H  `uintLen`     — elementary element `uint256[]` (unchanged)  => 5

Emitted by `scripts/solc_ast_to_lean_source.py` from pinned solc 0.8.35.
`#eval`-confirmed booleans pinned with `#guard` (the project avoids
`native_decide`).
-/

namespace SolidCore
namespace Solidity
namespace SolcAstImport
namespace NewContractLocalStructArray

def importedContract : ContractDecl :=
{ kind := ContractKind.contract
  name := "NewContractLocalStructArrayHarness"
  abstract := false
  bases := []
  items := [(ContractItem.structDecl
  { name := "P",
    fields := [{ name := "x", ty := Ty.uint 256 }] }), (ContractItem.structDecl
  { name := "Q",
    fields := [{ name := "x", ty := Ty.uint 256 }, { name := "y", ty := Ty.address false }, { name := "z", ty := Ty.bool }] }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "localVarLen",
    visibility := some Visibility.external_,
    mutability := StateMutability.pure,
    params := [],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.varDecl [{ name := some "pa", ty := Ty.array (Ty.user ({ segments := ["P"] })) (none), location := some DataLocation.memory }] (some (Expr.newExpr (Ty.array (Ty.user ({ segments := ["P"] })) (none)) [Arg.positional (Expr.literal (Literal.number "3"))])), Stmt.returnValues (some (Expr.member (Expr.ident "pa") "length"))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "returnArr",
    visibility := some Visibility.external_,
    mutability := StateMutability.pure,
    params := [],
    returns := [{ name := none, ty := Ty.array (Ty.user ({ segments := ["P"] })) (none), location := some DataLocation.memory }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.newExpr (Ty.array (Ty.user ({ segments := ["P"] })) (none)) [Arg.positional (Expr.literal (Literal.number "1"))]))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "multiLen",
    visibility := some Visibility.external_,
    mutability := StateMutability.pure,
    params := [],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.varDecl [{ name := some "qa", ty := Ty.array (Ty.user ({ segments := ["Q"] })) (none), location := some DataLocation.memory }] (some (Expr.newExpr (Ty.array (Ty.user ({ segments := ["Q"] })) (none)) [Arg.positional (Expr.literal (Literal.number "2"))])), Stmt.returnValues (some (Expr.member (Expr.ident "qa") "length"))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "arr2Len",
    visibility := some Visibility.external_,
    mutability := StateMutability.pure,
    params := [],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.varDecl [{ name := some "aa", ty := Ty.array (Ty.array (Ty.user ({ segments := ["P"] })) (none)) (none), location := some DataLocation.memory }] (some (Expr.newExpr (Ty.array (Ty.array (Ty.user ({ segments := ["P"] })) (none)) (none)) [Arg.positional (Expr.literal (Literal.number "4"))])), Stmt.returnValues (some (Expr.member (Expr.ident "aa") "length"))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "uintLen",
    visibility := some Visibility.external_,
    mutability := StateMutability.pure,
    params := [],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.varDecl [{ name := some "ua", ty := Ty.array (Ty.uint 256) (none), location := some DataLocation.memory }] (some (Expr.newExpr (Ty.array (Ty.uint 256) (none)) [Arg.positional (Expr.literal (Literal.number "5"))])), Stmt.returnValues (some (Expr.member (Expr.ident "ua") "length"))]) })] }

def importedSourceUnit : SourceUnit :=
  { items := [SourceItem.pragma "solidity" "^0.8.35",
      SourceItem.contract importedContract] }

def importedContractAccepted : Bool :=
  TypeCheck.Result.isOk (TypeCheck.TypecheckedInput.checkedSourceUnit importedSourceUnit)

/-- Call external function `fn` (no args) on the harness against empty state and
    return the single word it produced; `none` on any lowering/execution
    failure. EXERCISES the `new P[](n)` lowering end-to-end. -/
def callWord? (fn : String) : Option SolidCore.Solidity.Source.Word :=
  match TypeCheck.CheckedInput.program (α := SourceUnit) importedSourceUnit with
  | Except.ok program =>
      match
          TypeCheck.CheckedProgram.callContract 1000 program
            "NewContractLocalStructArrayHarness"
            (SolidCore.Solidity.Source.CallTarget.name fn)
            SolidCore.Solidity.Source.State.empty [] with
      | Except.ok (SolidCore.Solidity.Source.CallResult.returned _
          [SolidCore.Solidity.Source.Value.word w]) => some w
      | _ => none
  | _ => none

end NewContractLocalStructArray
end SolcAstImport
end Solidity
end SolidCore

namespace SolidCore
namespace Solidity
namespace Witness
namespace NewContractLocalStructArray

open SolidCore.Solidity.SolcAstImport.NewContractLocalStructArray

/-- The harness (which declares and `new`-allocates contract-local struct arrays)
    is ACCEPTED by the checker — the #163 over-reject is closed. -/
def accepted : Bool := importedContractAccepted

/-- Does external function `fn` execute and return the expected word? -/
def returns (fn : String) (expected : Nat) : Bool :=
  match callWord? fn with
  | some w =>
      SolidCore.Solidity.Source.wordEq w (expected : SolidCore.Solidity.Source.Word)
  | none => false

/-- G: `P[] memory pa = new P[](3); return pa.length;` executes to 3. -/
def localVarLenExecutes : Bool := returns "localVarLen" 3

/-- G3: multi-field local struct array `Q[]` — `qa.length` is 2. -/
def multiLenExecutes : Bool := returns "multiLen" 2

/-- G4: array-of-array of the local struct `P[][]` — `aa.length` is 4. -/
def arr2LenExecutes : Bool := returns "arr2Len" 4

/-- H (isolation ladder): elementary element array stays working — length 5. -/
def uintLenExecutes : Bool := returns "uintLen" 5

#guard accepted
#guard localVarLenExecutes
#guard multiLenExecutes
#guard arr2LenExecutes
#guard uintLenExecutes

end NewContractLocalStructArray
end Witness
end Solidity
end SolidCore

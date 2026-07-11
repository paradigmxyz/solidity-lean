import SolidCore.Solidity.Checked
import SolidCore.Witness.Checked

/-!
RECURSIVE-STRUCT-MEM-CONSTRUCT (#160) — memory-constructing a SELF-REFERENTIAL
struct now lowers and EXECUTES.

`struct Node { uint256 v; Node[] kids; }` has a dynamic-array member whose
element type is the struct itself. solc 0.8.35 accepts and runs
`Node memory n = Node(1, new Node[](0)); return n.v;` (real EVM: 1). The model's
CHECKER accepted the program, but the executable lowering could not build the
memory construction: `Ty.resolveStructs` inlines a struct path into its field
list to a fixed fuel budget, and for a self-referential struct that expansion
never terminates. The constructor-argument cast (resolved as the surface pass
descends the expression tree) and the declared memory-variable type (resolved
from the top of the type) therefore bottomed out at DIFFERENT fuel-residual
depths, so the `Ty.tuple actualFields == Ty.struct _ expectedFields` check in the
Executable-side `Ty.canImplicitlyConvert` compared two structurally different
giant trees, reported a spurious mismatch, and the whole contract failed to
lower (`toCoreContract? = none`, over-reject).

The fix (SolidCore/Solidity/Interface.lean) compares the two `resolveStructs`
expansions with `Ty.sameNominalType`, a fuel-tolerant nominal equality that
matches struct/user nodes by PATH and STOPS at each struct boundary — sound
(the inlined fields are redundant given the path + struct env) and
fuel-independent (a residual `Ty.user p` matches a further-expanded
`Ty.struct p _`). Non-recursive structs resolve fully and still compare equal,
so their lowering is unchanged. Only the Executable/lowering predicate changed;
the acceptance predicate is untouched, so nothing becomes over-accepted.

Isolation ladder, all pinned by execution below and by the Forge lane
`tests/forge-harness/recursive-struct-mem-construct` (real solc 0.8.35 + EVM):
  * G3 `constructRecursive` — the self-referential memory construct => 1 (the fix)
  * H1 `constructFlat`      — dyn-array member of a value type      => 2 (already worked)
  * H2 `constructBox`       — dyn-array member of a DIFFERENT struct => 3 (already worked)
  * G1 `storageWrite`       — recursive struct in storage, no mem construct => 5 (already worked)

Emitted by `scripts/solc_ast_to_lean_source.py` from pinned solc 0.8.35.
`#eval`-confirmed booleans pinned with `#guard` (the project avoids
`native_decide`).
-/

namespace SolidCore
namespace Solidity
namespace SolcAstImport
namespace RecursiveStructMemConstruct

def importedContract : ContractDecl :=
{ kind := ContractKind.contract
  name := "RecursiveStructMemConstructHarness"
  abstract := false
  bases := []
  items := [(ContractItem.structDecl
  { name := "Node",
    fields := [{ name := "v", ty := Ty.uint 256 }, { name := "kids", ty := Ty.array (Ty.user ({ segments := ["Node"] })) (none) }] }), (ContractItem.structDecl
  { name := "Leaf",
    fields := [{ name := "v", ty := Ty.uint 256 }] }), (ContractItem.structDecl
  { name := "Box",
    fields := [{ name := "v", ty := Ty.uint 256 }, { name := "kids", ty := Ty.array (Ty.user ({ segments := ["Leaf"] })) (none) }] }), (ContractItem.structDecl
  { name := "Flat",
    fields := [{ name := "v", ty := Ty.uint 256 }, { name := "kids", ty := Ty.array (Ty.uint 256) (none) }] }), (ContractItem.stateVar
  { name := "stored",
    ty := Ty.user ({ segments := ["Node"] }),
    visibility := some Visibility.internal_,
    mutability := VarMutability.mutable,
    override? := none,
    init := none }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "constructRecursive",
    visibility := some Visibility.external_,
    mutability := StateMutability.pure,
    params := [],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.varDecl [{ name := some "n", ty := Ty.user ({ segments := ["Node"] }), location := some DataLocation.memory }] (some (Expr.call (Expr.typeName (Ty.user ({ segments := ["Node"] }))) [Arg.positional (Expr.literal (Literal.number "1")), Arg.positional (Expr.newExpr (Ty.array (Ty.user ({ segments := ["Node"] })) (none)) [Arg.positional (Expr.literal (Literal.number "0"))])])), Stmt.returnValues (some (Expr.member (Expr.ident "n") "v"))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "constructFlat",
    visibility := some Visibility.external_,
    mutability := StateMutability.pure,
    params := [],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.varDecl [{ name := some "n", ty := Ty.user ({ segments := ["Flat"] }), location := some DataLocation.memory }] (some (Expr.call (Expr.typeName (Ty.user ({ segments := ["Flat"] }))) [Arg.positional (Expr.literal (Literal.number "2")), Arg.positional (Expr.newExpr (Ty.array (Ty.uint 256) (none)) [Arg.positional (Expr.literal (Literal.number "0"))])])), Stmt.returnValues (some (Expr.member (Expr.ident "n") "v"))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "constructBox",
    visibility := some Visibility.external_,
    mutability := StateMutability.pure,
    params := [],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.varDecl [{ name := some "n", ty := Ty.user ({ segments := ["Box"] }), location := some DataLocation.memory }] (some (Expr.call (Expr.typeName (Ty.user ({ segments := ["Box"] }))) [Arg.positional (Expr.literal (Literal.number "3")), Arg.positional (Expr.newExpr (Ty.array (Ty.user ({ segments := ["Leaf"] })) (none)) [Arg.positional (Expr.literal (Literal.number "0"))])])), Stmt.returnValues (some (Expr.member (Expr.ident "n") "v"))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "storageWrite",
    visibility := some Visibility.external_,
    mutability := StateMutability.nonpayable,
    params := [],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.expr (Expr.assign (Expr.member (Expr.ident "stored") "v") AssignOp.assign (Expr.literal (Literal.number "5"))), Stmt.returnValues (some (Expr.member (Expr.ident "stored") "v"))]) })] }

def importedSourceUnit : SourceUnit :=
  { items := [SourceItem.pragma "solidity" "^0.8.35",
      SourceItem.contract importedContract] }

def importedContractAccepted : Bool :=
  TypeCheck.Result.isOk (TypeCheck.TypecheckedInput.checkedSourceUnit importedSourceUnit)

/-- Call external function `fn` (no args) on the harness against empty state and
    return the single word it produced; `none` on any lowering/execution
    failure. This EXERCISES the memory-construction lowering end-to-end. -/
def callWord? (fn : String) : Option SolidCore.Solidity.Source.Word :=
  match TypeCheck.CheckedInput.program (α := SourceUnit) importedSourceUnit with
  | Except.ok program =>
      match
          TypeCheck.CheckedProgram.callContract 1000 program
            "RecursiveStructMemConstructHarness"
            (SolidCore.Solidity.Source.CallTarget.name fn)
            SolidCore.Solidity.Source.State.empty [] with
      | Except.ok (SolidCore.Solidity.Source.CallResult.returned _
          [SolidCore.Solidity.Source.Value.word w]) => some w
      | _ => none
  | _ => none

end RecursiveStructMemConstruct
end SolcAstImport
end Solidity
end SolidCore

namespace SolidCore
namespace Solidity
namespace Witness
namespace RecursiveStructMemConstruct

open SolidCore.Solidity.SolcAstImport.RecursiveStructMemConstruct

/-- The harness (which declares and memory-constructs a self-referential struct)
    is ACCEPTED by the checker. -/
def accepted : Bool := importedContractAccepted

/-- Does external function `fn` execute and return the expected word? -/
def returns (fn : String) (expected : Nat) : Bool :=
  match callWord? fn with
  | some w =>
      SolidCore.Solidity.Source.wordEq w (expected : SolidCore.Solidity.Source.Word)
  | none => false

/-- G3: memory-constructing the self-referential `Node(1, new Node[](0))` and
    reading `n.v` executes to 1 — the real-EVM value, and the #160 fix. -/
def constructRecursiveExecutes : Bool := returns "constructRecursive" 1

/-- H1 (isolation ladder): a struct with a value-type dynamic-array member. -/
def constructFlatExecutes : Bool := returns "constructFlat" 2

/-- H2 (isolation ladder): a struct with a dynamic-array member of a DIFFERENT
    struct. -/
def constructBoxExecutes : Bool := returns "constructBox" 3

/-- G1 (isolation ladder): storage-field write on the recursive struct, no memory
    construction. -/
def storageWriteExecutes : Bool := returns "storageWrite" 5

#guard accepted
#guard constructRecursiveExecutes
#guard constructFlatExecutes
#guard constructBoxExecutes
#guard storageWriteExecutes

end RecursiveStructMemConstruct
end Witness
end Solidity
end SolidCore

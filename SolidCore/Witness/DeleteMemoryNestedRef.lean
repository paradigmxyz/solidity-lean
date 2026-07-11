import SolidCore.Solidity.Checked
import SolidCore.Witness.Checked

/-!
DELETE-MEMORY-NESTED-REF (#168) — `delete` on a MEMORY struct/array now zeroes the
whole object graph, detaching (and freshly re-allocating) every nested reference.

solc's `delete` on a memory lvalue allocates a brand-new, fully-zeroed object at
the free-memory pointer; a struct's dynamic-array member therefore becomes a NEW
empty (length-0) array, not an alias of the old one. The model's memory `delete`
paths zeroed via `Value.defaultLike`, which has no `Runtime` and so returned the
SAME inner `memoryRef` — `s.x` zeroed but `s.arr.length` stayed 3 (wrong value,
replay-reachable). The fix (SolidCore/Solidity/Interpreter.lean,
`Runtime.deleteZeroValue`) walks the value graph runtime-aware: dynamic array →
fresh empty, fixed array → same length each element zeroed, struct → each field
zeroed, value fields → zero word, and every inner `memoryRef` is dereferenced,
zeroed, and re-allocated as a FRESH cell so the deleted variable is fully
detached from the pre-delete cells (which surviving aliases keep observing).

Ground truth = pinned solc 0.8.35 (legacy) + real EVM (anvil/cast):
  * f          delete S{uint x; uint[] arr}, then (s.x, s.arr.length) => (0, 0)
  * freshAfter delete then a fresh `s.arr = new uint[](2)` works           => (2, 5)
  * g          delete `uint[][2] memory` (each inner len 3)                => (0, 0)
  * nested     delete `Outer{S inner; uint[] tail}`                        => (0, 0, 0)
  * aliasCase  `b = s.arr; delete s;` — b keeps the OLD array, s.arr fresh => (3, 42, 0)
  * valueStruct delete a value-only struct (unchanged)                     => (0, 0)
  * topArray   delete a top-level `uint[] memory` (unchanged)              => 0
  * scalarLocal delete a `uint` local (unchanged)                          => 0

Emitted by `scripts/solc_ast_to_lean_source.py` from pinned solc 0.8.35; executed
end-to-end through `TypeCheck.CheckedProgram.callContract`. `#eval`-confirmed
booleans pinned with `#guard` (the project avoids `native_decide`).
-/

namespace SolidCore
namespace Solidity
namespace SolcAstImport
namespace DeleteMemoryNestedRef

def importedContractDecl0 : ContractDecl :=
{ kind := ContractKind.contract
  name := "DeleteMemNestedRefHarness"
  abstract := false
  bases := []
  items := [(ContractItem.structDecl
  { name := "S",
    fields := [{ name := "x", ty := Ty.uint 256 }, { name := "arr", ty := Ty.array (Ty.uint 256) (none) }] }), (ContractItem.structDecl
  { name := "Outer",
    fields := [{ name := "inner", ty := Ty.user ({ segments := ["S"] }) }, { name := "tail", ty := Ty.array (Ty.uint 256) (none) }] }), (ContractItem.structDecl
  { name := "V",
    fields := [{ name := "a", ty := Ty.uint 256 }, { name := "b", ty := Ty.uint 256 }] }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "f",
    visibility := some Visibility.external_,
    mutability := StateMutability.pure,
    params := [],
    returns := [{ name := none, ty := Ty.uint 256, location := none }, { name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.varDecl [{ name := some "s", ty := Ty.user ({ segments := ["S"] }), location := some DataLocation.memory }] none, Stmt.expr (Expr.assign (Expr.member (Expr.ident "s") "x") AssignOp.assign (Expr.literal (Literal.number "7"))), Stmt.expr (Expr.assign (Expr.member (Expr.ident "s") "arr") AssignOp.assign (Expr.newExpr (Ty.array (Ty.uint 256) (none)) [Arg.positional (Expr.literal (Literal.number "3"))])), Stmt.expr (Expr.assign (Expr.index (Expr.member (Expr.ident "s") "arr") (Expr.literal (Literal.number "0"))) AssignOp.assign (Expr.literal (Literal.number "42"))), Stmt.expr (Expr.unary UnaryOp.delete (Expr.ident "s")), Stmt.returnValues (some (Expr.tuple [TupleItem.value (Expr.member (Expr.ident "s") "x"), TupleItem.value (Expr.member (Expr.member (Expr.ident "s") "arr") "length")]))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "freshAfter",
    visibility := some Visibility.external_,
    mutability := StateMutability.pure,
    params := [],
    returns := [{ name := none, ty := Ty.uint 256, location := none }, { name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.varDecl [{ name := some "s", ty := Ty.user ({ segments := ["S"] }), location := some DataLocation.memory }] none, Stmt.expr (Expr.assign (Expr.member (Expr.ident "s") "x") AssignOp.assign (Expr.literal (Literal.number "7"))), Stmt.expr (Expr.assign (Expr.member (Expr.ident "s") "arr") AssignOp.assign (Expr.newExpr (Ty.array (Ty.uint 256) (none)) [Arg.positional (Expr.literal (Literal.number "3"))])), Stmt.expr (Expr.assign (Expr.index (Expr.member (Expr.ident "s") "arr") (Expr.literal (Literal.number "0"))) AssignOp.assign (Expr.literal (Literal.number "42"))), Stmt.expr (Expr.unary UnaryOp.delete (Expr.ident "s")), Stmt.expr (Expr.assign (Expr.member (Expr.ident "s") "arr") AssignOp.assign (Expr.newExpr (Ty.array (Ty.uint 256) (none)) [Arg.positional (Expr.literal (Literal.number "2"))])), Stmt.expr (Expr.assign (Expr.index (Expr.member (Expr.ident "s") "arr") (Expr.literal (Literal.number "1"))) AssignOp.assign (Expr.literal (Literal.number "5"))), Stmt.returnValues (some (Expr.tuple [TupleItem.value (Expr.member (Expr.member (Expr.ident "s") "arr") "length"), TupleItem.value (Expr.index (Expr.member (Expr.ident "s") "arr") (Expr.literal (Literal.number "1")))]))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "g",
    visibility := some Visibility.external_,
    mutability := StateMutability.pure,
    params := [],
    returns := [{ name := none, ty := Ty.uint 256, location := none }, { name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.varDecl [{ name := some "m", ty := Ty.array (Ty.array (Ty.uint 256) (none)) (some 2), location := some DataLocation.memory }] none, Stmt.expr (Expr.assign (Expr.index (Expr.ident "m") (Expr.literal (Literal.number "0"))) AssignOp.assign (Expr.newExpr (Ty.array (Ty.uint 256) (none)) [Arg.positional (Expr.literal (Literal.number "3"))])), Stmt.expr (Expr.assign (Expr.index (Expr.ident "m") (Expr.literal (Literal.number "1"))) AssignOp.assign (Expr.newExpr (Ty.array (Ty.uint 256) (none)) [Arg.positional (Expr.literal (Literal.number "3"))])), Stmt.expr (Expr.unary UnaryOp.delete (Expr.ident "m")), Stmt.returnValues (some (Expr.tuple [TupleItem.value (Expr.member (Expr.index (Expr.ident "m") (Expr.literal (Literal.number "0"))) "length"), TupleItem.value (Expr.member (Expr.index (Expr.ident "m") (Expr.literal (Literal.number "1"))) "length")]))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "nested",
    visibility := some Visibility.external_,
    mutability := StateMutability.pure,
    params := [],
    returns := [{ name := none, ty := Ty.uint 256, location := none }, { name := none, ty := Ty.uint 256, location := none }, { name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.varDecl [{ name := some "o", ty := Ty.user ({ segments := ["Outer"] }), location := some DataLocation.memory }] none, Stmt.expr (Expr.assign (Expr.member (Expr.member (Expr.ident "o") "inner") "x") AssignOp.assign (Expr.literal (Literal.number "1"))), Stmt.expr (Expr.assign (Expr.member (Expr.member (Expr.ident "o") "inner") "arr") AssignOp.assign (Expr.newExpr (Ty.array (Ty.uint 256) (none)) [Arg.positional (Expr.literal (Literal.number "3"))])), Stmt.expr (Expr.assign (Expr.member (Expr.ident "o") "tail") AssignOp.assign (Expr.newExpr (Ty.array (Ty.uint 256) (none)) [Arg.positional (Expr.literal (Literal.number "4"))])), Stmt.expr (Expr.unary UnaryOp.delete (Expr.ident "o")), Stmt.returnValues (some (Expr.tuple [TupleItem.value (Expr.member (Expr.member (Expr.ident "o") "inner") "x"), TupleItem.value (Expr.member (Expr.member (Expr.member (Expr.ident "o") "inner") "arr") "length"), TupleItem.value (Expr.member (Expr.member (Expr.ident "o") "tail") "length")]))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "aliasCase",
    visibility := some Visibility.external_,
    mutability := StateMutability.pure,
    params := [],
    returns := [{ name := none, ty := Ty.uint 256, location := none }, { name := none, ty := Ty.uint 256, location := none }, { name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.varDecl [{ name := some "s", ty := Ty.user ({ segments := ["S"] }), location := some DataLocation.memory }] none, Stmt.expr (Expr.assign (Expr.member (Expr.ident "s") "arr") AssignOp.assign (Expr.newExpr (Ty.array (Ty.uint 256) (none)) [Arg.positional (Expr.literal (Literal.number "3"))])), Stmt.expr (Expr.assign (Expr.index (Expr.member (Expr.ident "s") "arr") (Expr.literal (Literal.number "0"))) AssignOp.assign (Expr.literal (Literal.number "42"))), Stmt.varDecl [{ name := some "b", ty := Ty.array (Ty.uint 256) (none), location := some DataLocation.memory }] (some (Expr.member (Expr.ident "s") "arr")), Stmt.expr (Expr.unary UnaryOp.delete (Expr.ident "s")), Stmt.returnValues (some (Expr.tuple [TupleItem.value (Expr.member (Expr.ident "b") "length"), TupleItem.value (Expr.index (Expr.ident "b") (Expr.literal (Literal.number "0"))), TupleItem.value (Expr.member (Expr.member (Expr.ident "s") "arr") "length")]))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "valueStruct",
    visibility := some Visibility.external_,
    mutability := StateMutability.pure,
    params := [],
    returns := [{ name := none, ty := Ty.uint 256, location := none }, { name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.varDecl [{ name := some "v", ty := Ty.user ({ segments := ["V"] }), location := some DataLocation.memory }] none, Stmt.expr (Expr.assign (Expr.member (Expr.ident "v") "a") AssignOp.assign (Expr.literal (Literal.number "3"))), Stmt.expr (Expr.assign (Expr.member (Expr.ident "v") "b") AssignOp.assign (Expr.literal (Literal.number "4"))), Stmt.expr (Expr.unary UnaryOp.delete (Expr.ident "v")), Stmt.returnValues (some (Expr.tuple [TupleItem.value (Expr.member (Expr.ident "v") "a"), TupleItem.value (Expr.member (Expr.ident "v") "b")]))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "topArray",
    visibility := some Visibility.external_,
    mutability := StateMutability.pure,
    params := [],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.varDecl [{ name := some "a", ty := Ty.array (Ty.uint 256) (none), location := some DataLocation.memory }] (some (Expr.newExpr (Ty.array (Ty.uint 256) (none)) [Arg.positional (Expr.literal (Literal.number "3"))])), Stmt.expr (Expr.assign (Expr.index (Expr.ident "a") (Expr.literal (Literal.number "0"))) AssignOp.assign (Expr.literal (Literal.number "9"))), Stmt.expr (Expr.unary UnaryOp.delete (Expr.ident "a")), Stmt.returnValues (some (Expr.member (Expr.ident "a") "length"))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "scalarLocal",
    visibility := some Visibility.external_,
    mutability := StateMutability.pure,
    params := [],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.varDecl [{ name := some "x", ty := Ty.uint 256, location := none }] (some (Expr.literal (Literal.number "7"))), Stmt.expr (Expr.unary UnaryOp.delete (Expr.ident "x")), Stmt.returnValues (some (Expr.ident "x"))]) })] }

def importedContract : ContractDecl :=
  importedContractDecl0

def importedContracts : List ContractDecl :=
  [importedContractDecl0]

def importedSourceUnit : SourceUnit :=
  { items := [SourceItem.pragma "solidity" "0.8.35", SourceItem.contract importedContractDecl0] }

def importedContractAccepted : Bool :=
  TypeCheck.Result.isOk (TypeCheck.TypecheckedInput.checkedSourceUnit importedSourceUnit)

/-- Call external function `fn` (no args) on the harness against empty state and
    return the list of words it produced; `none` on any lowering/execution
    failure. EXERCISES the memory `delete` object-graph zeroing end-to-end. -/
def callWords? (fn : String) : Option (List SolidCore.Solidity.Source.Word) :=
  match TypeCheck.CheckedInput.program (α := SourceUnit) importedSourceUnit with
  | Except.ok program =>
      match
          TypeCheck.CheckedProgram.callContract 1000 program
            "DeleteMemNestedRefHarness"
            (SolidCore.Solidity.Source.CallTarget.name fn)
            SolidCore.Solidity.Source.State.empty [] with
      | Except.ok (SolidCore.Solidity.Source.CallResult.returned _ values) =>
          values.mapM (fun v =>
            match v with
            | SolidCore.Solidity.Source.Value.word w => some w
            | _ => none)
      | _ => none
  | _ => none

end DeleteMemoryNestedRef
end SolcAstImport
end Solidity
end SolidCore

namespace SolidCore
namespace Solidity
namespace Witness
namespace DeleteMemoryNestedRef

open SolidCore.Solidity.SolcAstImport.DeleteMemoryNestedRef

/-- The harness is ACCEPTED by the checker. -/
def accepted : Bool := importedContractAccepted

/-- Does external function `fn` execute and return exactly `expected` (as words)? -/
def returns (fn : String) (expected : List Nat) : Bool :=
  match callWords? fn with
  | some ws =>
      ws.length == expected.length &&
        (ws.zip expected).all (fun (w, e) =>
          SolidCore.Solidity.Source.wordEq w (e : SolidCore.Solidity.Source.Word))
  | none => false

/-- The core fix: `delete s` fully zeroes the struct — `s.arr` becomes empty. -/
def fZeroesNestedArray : Bool := returns "f" [0, 0]

/-- After `delete s`, `s.arr` is a fresh array: a new `new uint[](2)` works. -/
def freshAfterDelete : Bool := returns "freshAfter" [2, 5]

/-- `delete` of a fixed array of dynamic arrays empties each inner array. -/
def gEmptiesFixedArrayOfDyn : Bool := returns "g" [0, 0]

/-- Nested struct: `delete Outer` zeroes every nested length. -/
def nestedAllZero : Bool := returns "nested" [0, 0, 0]

/-- Aliasing: a pre-delete alias `b` keeps the OLD array; `s.arr` is fresh empty. -/
def aliasKeepsOldArray : Bool := returns "aliasCase" [3, 42, 0]

/-- Unchanged: delete a value-only struct. -/
def valueStructUnchanged : Bool := returns "valueStruct" [0, 0]

/-- Unchanged: delete a top-level `uint[] memory`. -/
def topArrayUnchanged : Bool := returns "topArray" [0]

/-- Unchanged: delete a scalar local. -/
def scalarLocalUnchanged : Bool := returns "scalarLocal" [0]

#guard accepted
#guard fZeroesNestedArray
#guard freshAfterDelete
#guard gEmptiesFixedArrayOfDyn
#guard nestedAllZero
#guard aliasKeepsOldArray
#guard valueStructUnchanged
#guard topArrayUnchanged
#guard scalarLocalUnchanged

end DeleteMemoryNestedRef
end Witness
end Solidity
end SolidCore

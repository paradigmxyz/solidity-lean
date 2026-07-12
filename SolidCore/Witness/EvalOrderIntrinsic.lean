/-
R1 — INTRINSIC SIBLING-EVALUATION ORDER (rearch/eval-order-intrinsic).

Pins the construct-intrinsic sibling-evaluation orders against solc 0.8.35
legacy codegen (`libsolidity/codegen/ExpressionCompiler.cpp`):
  * argument / tuple / inline-array / abi.encode / custom-error lists and
    index base-vs-key run LEFT to RIGHT (710-711, 682-684, 1031, 400, 388);
  * binary operands run RIGHT then LEFT (614-615) — preserved;
  * assignment and compound assignment evaluate the RHS BEFORE the LHS
    reference (319, 331, 336-370) — preserved;
  * `emit` is TWO-PHASE (Kind::Event, 976-1043): indexed (topic) arguments
    evaluate in REVERSE source order first, then non-indexed (data) arguments
    FORWARD;
  * short-circuit `&&`/`||` stay left-first with a guarded right operand.

Real-EVM Forge ground truth: `tests/forge-harness/eval-order-intrinsic`
(14 tests pass under pinned solc 0.8.35). Every check below is enforced at
`lake build SolidCore` time by the trailing `#eval` (compiled evaluator; no
proof axioms).
-/
import SolidCore.Solidity.Checked
import SolidCore.Witness.Checked

namespace SolidCore
namespace Solidity
namespace SolcAstImport
namespace EvalOrderIntrinsic

def importedSourceName : String := "tests/forge-harness/eval-order-intrinsic/src/EvalOrderIntrinsic.sol"

def importedContractDecl0 : ContractDecl :=
{ kind := ContractKind.contract
  name := "EvalOrderIntrinsic"
  abstract := false
  bases := []
  items := [(ContractItem.stateVar
  { name := "i",
    ty := Ty.uint 256,
    visibility := some Visibility.public_,
    mutability := VarMutability.mutable,
    override? := none,
    init := none }), (ContractItem.stateVar
  { name := "s",
    ty := Ty.uint 256,
    visibility := some Visibility.public_,
    mutability := VarMutability.mutable,
    override? := none,
    init := none }), (ContractItem.stateVar
  { name := "m",
    ty := Ty.mapping (Ty.uint 256) (Ty.mapping (Ty.uint 256) (Ty.uint 256)),
    visibility := some Visibility.public_,
    mutability := VarMutability.mutable,
    override? := none,
    init := none }), (ContractItem.eventDecl
  { name := "Mixed",
    params := [{ name := some "a", ty := Ty.uint 256, indexed := true }, { name := some "b", ty := Ty.uint 256, indexed := false }, { name := some "c", ty := Ty.uint 256, indexed := true }, { name := some "d", ty := Ty.uint 256, indexed := false }],
    anonymous := false }), (ContractItem.eventDecl
  { name := "AllData",
    params := [{ name := some "a", ty := Ty.uint 256, indexed := false }, { name := some "b", ty := Ty.uint 256, indexed := false }, { name := some "c", ty := Ty.uint 256, indexed := false }],
    anonymous := false }), (ContractItem.errorDecl
  { name := "Err",
    params := [{ name := some "a", ty := Ty.uint 256, location := none }, { name := some "b", ty := Ty.uint 256, location := none }] }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "tupleRhs",
    visibility := some Visibility.public_,
    mutability := StateMutability.nonpayable,
    params := [],
    returns := [{ name := none, ty := Ty.uint 256, location := none }, { name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.expr (Expr.assign (Expr.ident "i") AssignOp.assign (Expr.literal (Literal.number "0"))), Stmt.varDecl [{ name := some "a", ty := Ty.uint 256, location := none }] none, Stmt.varDecl [{ name := some "b", ty := Ty.uint 256, location := none }] none, Stmt.expr (Expr.assign (Expr.tuple [TupleItem.value (Expr.ident "a"), TupleItem.value (Expr.ident "b")]) AssignOp.assign (Expr.tuple [TupleItem.value (Expr.unary UnaryOp.postIncrement (Expr.ident "i")), TupleItem.value (Expr.ident "i")])), Stmt.returnValues (some (Expr.tuple [TupleItem.value (Expr.ident "a"), TupleItem.value (Expr.ident "b")]))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "returnTuple",
    visibility := some Visibility.public_,
    mutability := StateMutability.nonpayable,
    params := [],
    returns := [{ name := none, ty := Ty.uint 256, location := none }, { name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.expr (Expr.assign (Expr.ident "i") AssignOp.assign (Expr.literal (Literal.number "0"))), Stmt.returnValues (some (Expr.tuple [TupleItem.value (Expr.unary UnaryOp.postIncrement (Expr.ident "i")), TupleItem.value (Expr.unary UnaryOp.postIncrement (Expr.ident "i"))]))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "callArgs",
    visibility := some Visibility.public_,
    mutability := StateMutability.nonpayable,
    params := [],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.expr (Expr.assign (Expr.ident "i") AssignOp.assign (Expr.literal (Literal.number "0"))), Stmt.returnValues (some (Expr.call (Expr.ident "sink") [Arg.positional (Expr.unary UnaryOp.postIncrement (Expr.ident "i")), Arg.positional (Expr.unary UnaryOp.postIncrement (Expr.ident "i")), Arg.positional (Expr.unary UnaryOp.postIncrement (Expr.ident "i"))]))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "sink",
    visibility := some Visibility.internal_,
    mutability := StateMutability.pure,
    params := [{ name := some "a", ty := Ty.uint 256, location := none }, { name := some "b", ty := Ty.uint 256, location := none }, { name := some "c", ty := Ty.uint 256, location := none }],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.binary BinaryOp.add (Expr.binary BinaryOp.add (Expr.binary BinaryOp.mul (Expr.ident "a") (Expr.literal (Literal.number "100"))) (Expr.binary BinaryOp.mul (Expr.ident "b") (Expr.literal (Literal.number "10")))) (Expr.ident "c")))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "abiEnc",
    visibility := some Visibility.public_,
    mutability := StateMutability.nonpayable,
    params := [],
    returns := [{ name := none, ty := Ty.bytes, location := some DataLocation.memory }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.expr (Expr.assign (Expr.ident "i") AssignOp.assign (Expr.literal (Literal.number "0"))), Stmt.returnValues (some (Expr.call (Expr.member (Expr.ident "abi") "encode") [Arg.positional (Expr.unary UnaryOp.postIncrement (Expr.ident "i")), Arg.positional (Expr.unary UnaryOp.postIncrement (Expr.ident "i"))]))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "indexLhs",
    visibility := some Visibility.public_,
    mutability := StateMutability.nonpayable,
    params := [],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.expr (Expr.assign (Expr.ident "i") AssignOp.assign (Expr.literal (Literal.number "0"))), Stmt.expr (Expr.assign (Expr.index (Expr.index (Expr.ident "m") (Expr.unary UnaryOp.postIncrement (Expr.ident "i"))) (Expr.unary UnaryOp.postIncrement (Expr.ident "i"))) AssignOp.assign (Expr.literal (Literal.number "99"))), Stmt.returnValues (some (Expr.index (Expr.index (Expr.ident "m") (Expr.literal (Literal.number "0"))) (Expr.literal (Literal.number "1"))))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "revertErr",
    visibility := some Visibility.public_,
    mutability := StateMutability.nonpayable,
    params := [],
    returns := [],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.expr (Expr.assign (Expr.ident "i") AssignOp.assign (Expr.literal (Literal.number "0"))), Stmt.revertCall (Expr.call (Expr.ident "Err") [Arg.positional (Expr.unary UnaryOp.postIncrement (Expr.ident "i")), Arg.positional (Expr.unary UnaryOp.postIncrement (Expr.ident "i"))])]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "emitAllData",
    visibility := some Visibility.public_,
    mutability := StateMutability.nonpayable,
    params := [],
    returns := [],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.expr (Expr.assign (Expr.ident "i") AssignOp.assign (Expr.literal (Literal.number "0"))), Stmt.emitEvent (Expr.call (Expr.ident "AllData") [Arg.positional (Expr.unary UnaryOp.postIncrement (Expr.ident "i")), Arg.positional (Expr.unary UnaryOp.postIncrement (Expr.ident "i")), Arg.positional (Expr.unary UnaryOp.postIncrement (Expr.ident "i"))])]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "emitMixed",
    visibility := some Visibility.public_,
    mutability := StateMutability.nonpayable,
    params := [],
    returns := [],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.expr (Expr.assign (Expr.ident "i") AssignOp.assign (Expr.literal (Literal.number "0"))), Stmt.emitEvent (Expr.call (Expr.ident "Mixed") [Arg.positional (Expr.unary UnaryOp.postIncrement (Expr.ident "i")), Arg.positional (Expr.unary UnaryOp.postIncrement (Expr.ident "i")), Arg.positional (Expr.unary UnaryOp.postIncrement (Expr.ident "i")), Arg.positional (Expr.unary UnaryOp.postIncrement (Expr.ident "i"))])]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "wr",
    visibility := some Visibility.internal_,
    mutability := StateMutability.nonpayable,
    params := [],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.expr (Expr.assign (Expr.ident "s") AssignOp.assign (Expr.literal (Literal.number "5"))), Stmt.returnValues (some (Expr.literal (Literal.number "0")))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "rd",
    visibility := some Visibility.internal_,
    mutability := StateMutability.view,
    params := [],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.ident "s"))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "binaryOrder",
    visibility := some Visibility.public_,
    mutability := StateMutability.nonpayable,
    params := [],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.expr (Expr.assign (Expr.ident "s") AssignOp.assign (Expr.literal (Literal.number "0"))), Stmt.returnValues (some (Expr.binary BinaryOp.add (Expr.call (Expr.ident "rd") []) (Expr.call (Expr.ident "wr") [])))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "arrAssign",
    visibility := some Visibility.public_,
    mutability := StateMutability.nonpayable,
    params := [],
    returns := [{ name := none, ty := Ty.uint 256, location := none }, { name := none, ty := Ty.uint 256, location := none }, { name := none, ty := Ty.uint 256, location := none }, { name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.expr (Expr.assign (Expr.ident "i") AssignOp.assign (Expr.literal (Literal.number "0"))), Stmt.varDecl [{ name := some "arr", ty := Ty.array (Ty.uint 256) (some 3), location := some DataLocation.memory }] (some (Expr.array [Expr.call (Expr.typeName (Ty.uint 256)) [Arg.positional (Expr.literal (Literal.number "7"))], Expr.literal (Literal.number "7"), Expr.literal (Literal.number "7")])), Stmt.expr (Expr.assign (Expr.index (Expr.ident "arr") (Expr.unary UnaryOp.postIncrement (Expr.ident "i"))) AssignOp.assign (Expr.unary UnaryOp.postIncrement (Expr.ident "i"))), Stmt.returnValues (some (Expr.tuple [TupleItem.value (Expr.index (Expr.ident "arr") (Expr.literal (Literal.number "0"))), TupleItem.value (Expr.index (Expr.ident "arr") (Expr.literal (Literal.number "1"))), TupleItem.value (Expr.index (Expr.ident "arr") (Expr.literal (Literal.number "2"))), TupleItem.value (Expr.ident "i")]))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "arrCompound",
    visibility := some Visibility.public_,
    mutability := StateMutability.nonpayable,
    params := [],
    returns := [{ name := none, ty := Ty.uint 256, location := none }, { name := none, ty := Ty.uint 256, location := none }, { name := none, ty := Ty.uint 256, location := none }, { name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.expr (Expr.assign (Expr.ident "i") AssignOp.assign (Expr.literal (Literal.number "0"))), Stmt.varDecl [{ name := some "arr", ty := Ty.array (Ty.uint 256) (some 3), location := some DataLocation.memory }] (some (Expr.array [Expr.call (Expr.typeName (Ty.uint 256)) [Arg.positional (Expr.literal (Literal.number "7"))], Expr.literal (Literal.number "7"), Expr.literal (Literal.number "7")])), Stmt.expr (Expr.assign (Expr.index (Expr.ident "arr") (Expr.unary UnaryOp.postIncrement (Expr.ident "i"))) AssignOp.addAssign (Expr.unary UnaryOp.postIncrement (Expr.ident "i"))), Stmt.returnValues (some (Expr.tuple [TupleItem.value (Expr.index (Expr.ident "arr") (Expr.literal (Literal.number "0"))), TupleItem.value (Expr.index (Expr.ident "arr") (Expr.literal (Literal.number "1"))), TupleItem.value (Expr.index (Expr.ident "arr") (Expr.literal (Literal.number "2"))), TupleItem.value (Expr.ident "i")]))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "scAnd",
    visibility := some Visibility.public_,
    mutability := StateMutability.nonpayable,
    params := [],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.expr (Expr.assign (Expr.ident "i") AssignOp.assign (Expr.literal (Literal.number "0"))), Stmt.varDecl [{ name := some "r", ty := Ty.bool, location := none }] (some (Expr.binary BinaryOp.boolAnd (Expr.binary BinaryOp.eq (Expr.unary UnaryOp.postIncrement (Expr.ident "i")) (Expr.literal (Literal.number "100"))) (Expr.binary BinaryOp.eq (Expr.unary UnaryOp.postIncrement (Expr.ident "i")) (Expr.literal (Literal.number "0"))))), Stmt.returnValues (some (Expr.ternary (Expr.ident "r") (Expr.binary BinaryOp.add (Expr.literal (Literal.number "1000")) (Expr.ident "i")) (Expr.ident "i")))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "scOr",
    visibility := some Visibility.public_,
    mutability := StateMutability.nonpayable,
    params := [],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.expr (Expr.assign (Expr.ident "i") AssignOp.assign (Expr.literal (Literal.number "0"))), Stmt.varDecl [{ name := some "r", ty := Ty.bool, location := none }] (some (Expr.binary BinaryOp.boolOr (Expr.binary BinaryOp.eq (Expr.unary UnaryOp.postIncrement (Expr.ident "i")) (Expr.literal (Literal.number "0"))) (Expr.binary BinaryOp.eq (Expr.unary UnaryOp.postIncrement (Expr.ident "i")) (Expr.literal (Literal.number "100"))))), Stmt.returnValues (some (Expr.ternary (Expr.ident "r") (Expr.binary BinaryOp.add (Expr.literal (Literal.number "1000")) (Expr.ident "i")) (Expr.ident "i")))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "dataDep",
    visibility := some Visibility.public_,
    mutability := StateMutability.nonpayable,
    params := [],
    returns := [{ name := none, ty := Ty.uint 256, location := none }, { name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.expr (Expr.assign (Expr.ident "i") AssignOp.assign (Expr.literal (Literal.number "0"))), Stmt.varDecl [{ name := some "a", ty := Ty.uint 256, location := none }, { name := some "b", ty := Ty.uint 256, location := none }] (some (Expr.tuple [TupleItem.value (Expr.assign (Expr.ident "i") AssignOp.assign (Expr.literal (Literal.number "5"))), TupleItem.value (Expr.binary BinaryOp.add (Expr.ident "i") (Expr.literal (Literal.number "1")))])), Stmt.returnValues (some (Expr.tuple [TupleItem.value (Expr.ident "a"), TupleItem.value (Expr.ident "b")]))]) })] }

def importedContractDecl1 : ContractDecl :=
{ kind := ContractKind.contract
  name := "EvalOrderInlineArray"
  abstract := false
  bases := []
  items := [(ContractItem.stateVar
  { name := "i",
    ty := Ty.uint 256,
    visibility := some Visibility.public_,
    mutability := VarMutability.mutable,
    override? := none,
    init := none }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "inlineArray",
    visibility := some Visibility.public_,
    mutability := StateMutability.nonpayable,
    params := [],
    returns := [{ name := none, ty := Ty.uint 256, location := none }, { name := none, ty := Ty.uint 256, location := none }, { name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.expr (Expr.assign (Expr.ident "i") AssignOp.assign (Expr.literal (Literal.number "0"))), Stmt.varDecl [{ name := some "arr", ty := Ty.array (Ty.uint 256) (some 3), location := some DataLocation.memory }] (some (Expr.array [Expr.unary UnaryOp.postIncrement (Expr.ident "i"), Expr.unary UnaryOp.postIncrement (Expr.ident "i"), Expr.unary UnaryOp.postIncrement (Expr.ident "i")])), Stmt.returnValues (some (Expr.tuple [TupleItem.value (Expr.index (Expr.ident "arr") (Expr.literal (Literal.number "0"))), TupleItem.value (Expr.index (Expr.ident "arr") (Expr.literal (Literal.number "1"))), TupleItem.value (Expr.index (Expr.ident "arr") (Expr.literal (Literal.number "2")))]))]) })] }

def importedContract : ContractDecl :=
  importedContractDecl0

def importedContracts : List ContractDecl :=
  [importedContractDecl0, importedContractDecl1]

def importedSourceUnit : SourceUnit :=
  { items := [SourceItem.pragma "solidity" "^0.8.35", SourceItem.contract importedContractDecl0, SourceItem.contract importedContractDecl1] }

def importedContractAccepted : Bool :=
  TypeCheck.Result.isOk (TypeCheck.TypecheckedInput.checkedSourceUnit importedSourceUnit)

end EvalOrderIntrinsic
end SolcAstImport
end Solidity
end SolidCore

namespace SolidCore
namespace Solidity
namespace Witness
namespace EvalOrderIntrinsic

open SolidCore.Solidity.Source
open SolidCore.Solidity.TypeCheck

abbrev C := SolidCore.Solidity.SolcAstImport.EvalOrderIntrinsic.importedContract

def accepted : Bool :=
  SolidCore.Solidity.SolcAstImport.EvalOrderIntrinsic.importedContractAccepted

private def call (fn : Name) :
    Except TypeError SolidCore.Solidity.Source.CallResult :=
  CheckedInput.ownCall 256 C
    (SolidCore.Solidity.Source.CallTarget.name fn)
    SolidCore.Solidity.Source.State.empty []

private def isOkTrue : Except TypeError Bool -> Bool
  | Except.ok true => true
  | _ => false

private def wordsMatch :
    List SolidCore.Solidity.Source.Value -> List Word -> Bool
  | [], [] => true
  | SolidCore.Solidity.Source.Value.word value :: values, expected :: rest =>
      SolidCore.Solidity.Source.wordEq value expected &&
        wordsMatch values rest
  | _, _ => false

private def returnedWords (fn : Name) (expected : List Word) :
    Except TypeError Bool := do
  let result ← call fn
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _ values =>
      Except.ok (wordsMatch values expected)
  | _ => Except.ok false

-- LEFT-to-RIGHT constructs (CHANGED by R1; previously right-to-left).

/-- Tuple RHS `(a, b) = (i++, i)` -> (0, 1). -/
def tupleRhs : Except TypeError Bool := returnedWords "tupleRhs" [0, 1]

/-- Return tuple `return (i++, i++)` -> (0, 1). -/
def returnTuple : Except TypeError Bool := returnedWords "returnTuple" [0, 1]

/-- Internal-call args `sink(i++, i++, i++)` -> 012. -/
def callArgs : Except TypeError Bool := returnedWords "callArgs" [12]

-- NOTE: the inline-array-literal probe (`[i++, i++, i++]` -> [0,1,2]) lives
-- in the Forge lane only (`EvalOrderInlineArray`): the importer does not yet
-- lower non-literal inline-array components. `Expr.fixedArray` components run
-- through the same left-to-right list evaluator pinned by tupleRhs/callArgs.

/-- Index lvalue base-then-key: `m[i++][i++] = 99` writes `m[0][1]`. -/
def indexLhs : Except TypeError Bool := returnedWords "indexLhs" [99]

/-- Data-dependent siblings `(i = 5, i + 1)` -> (5, 6). -/
def dataDep : Except TypeError Bool := returnedWords "dataDep" [5, 6]

/-- `abi.encode(i++, i++)` encodes (0, 1). -/
def abiEnc : Except TypeError Bool := do
  let result ← call "abiEnc"
  let expected? :=
    SolidCore.Solidity.Source.abiEncodeValues?
      [SolidCore.Solidity.Source.Ty.uint256,
        SolidCore.Solidity.Source.Ty.uint256]
      [SolidCore.Solidity.Source.Value.word 0,
        SolidCore.Solidity.Source.Value.word 1]
  match result, expected? with
  | SolidCore.Solidity.Source.CallResult.returned _
      [SolidCore.Solidity.Source.Value.bytes got], some expected =>
      Except.ok (got == expected)
  | _, _ => Except.ok false

/-- `revert Err(i++, i++)` -> `Err(0, 1)`. -/
def revertErr : Except TypeError Bool := do
  let result ← call "revertErr"
  match result with
  | SolidCore.Solidity.Source.CallResult.reverted _
      (SolidCore.Solidity.Source.RevertData.custom "Err"
        [SolidCore.Solidity.Source.Value.word a,
          SolidCore.Solidity.Source.Value.word b]) =>
      Except.ok
        (SolidCore.Solidity.Source.wordEq a 0 &&
          SolidCore.Solidity.Source.wordEq b 1)
  | _ => Except.ok false

-- emit: two-phase (indexed reverse first, then data forward).

/-- All-data event: `emit AllData(i++, i++, i++)` -> data (0, 1, 2). -/
def emitAllData : Except TypeError Bool := do
  let result ← call "emitAllData"
  match result with
  | SolidCore.Solidity.Source.CallResult.returned state [] =>
      match state.events with
      | [event] =>
          Except.ok
            (event.name == "AllData" &&
              event.topics ==
                [SolidCore.Solidity.Source.Keccak.digestWord
                  "AllData(uint256,uint256,uint256)"] &&
              wordsMatch event.data [0, 1, 2])
      | _ => Except.ok false
  | _ => Except.ok false

/-- Mixed event `Mixed(indexed a, b, indexed c, d)` with args
    `(i++, i++, i++, i++)`: TWO-PHASE evaluation — indexed args in REVERSE
    source order first (c = 0, then a = 1), then data args FORWARD
    (b = 2, d = 3). Topics carry a = 1, c = 0. -/
def emitMixedTwoPhase : Except TypeError Bool := do
  let result ← call "emitMixed"
  match result with
  | SolidCore.Solidity.Source.CallResult.returned state [] =>
      match state.events with
      | [event] =>
          Except.ok
            (event.name == "Mixed" &&
              event.topics ==
                [SolidCore.Solidity.Source.Keccak.digestWord
                  "Mixed(uint256,uint256,uint256,uint256)",
                  1, 0] &&
              wordsMatch event.indexed [1, 0] &&
              wordsMatch event.data [2, 3])
      | _ => Except.ok false
  | _ => Except.ok false

-- PRESERVED right-first controls (must NOT have changed).

/-- Binary operands RIGHT then LEFT: `rd() + wr()` -> 5. -/
def binaryOrder : Except TypeError Bool := returnedWords "binaryOrder" [5]

/-- Assignment RHS before LHS-ref: `arr[i++] = i++` -> arr = [7,0,7], i = 2. -/
def arrAssign : Except TypeError Bool :=
  returnedWords "arrAssign" [7, 0, 7, 2]

/-- Compound assign RHS before LHS-ref: `arr[i++] += i++` -> [7,7,7], i = 2. -/
def arrCompound : Except TypeError Bool :=
  returnedWords "arrCompound" [7, 7, 7, 2]

/-- Short-circuit `&&` left-first, right guarded. -/
def scAnd : Except TypeError Bool := returnedWords "scAnd" [1]

/-- Short-circuit `||` left-first, right guarded. -/
def scOr : Except TypeError Bool := returnedWords "scOr" [1001]

def checks : List (String × Bool) :=
  [ ("accepted", accepted)
  , ("tupleRhs", isOkTrue tupleRhs)
  , ("returnTuple", isOkTrue returnTuple)
  , ("callArgs", isOkTrue callArgs)
  , ("indexLhs", isOkTrue indexLhs)
  , ("dataDep", isOkTrue dataDep)
  , ("abiEnc", isOkTrue abiEnc)
  , ("revertErr", isOkTrue revertErr)
  , ("emitAllData", isOkTrue emitAllData)
  , ("emitMixedTwoPhase", isOkTrue emitMixedTwoPhase)
  , ("binaryOrder", isOkTrue binaryOrder)
  , ("arrAssign", isOkTrue arrAssign)
  , ("arrCompound", isOkTrue arrCompound)
  , ("scAnd", isOkTrue scAnd)
  , ("scOr", isOkTrue scOr) ]

def failing : List String :=
  (checks.filter (fun check => !check.2)).map (fun check => check.1)

end EvalOrderIntrinsic
end Witness
end Solidity
end SolidCore

/- Build-time machine-check: `lake build SolidCore` fails (this `#eval` throws)
    if any construct's intrinsic sibling-evaluation order regresses. -/
#eval
  match SolidCore.Solidity.Witness.EvalOrderIntrinsic.failing with
  | [] => (pure () : IO Unit)
  | bad =>
      throw (IO.userError
        (String.intercalate ", " bad ++
          ": eval-order-intrinsic witness regressed"))

import SolidCore.Solidity.Checked
import SolidCore.Witness.Checked

set_option maxHeartbeats 8000000

/-!
CALLDATA-SLICE-STOP-CALL (S, call-in-slice-stop-revert-vs-success) — a
value-returning internal call in a calldata-slice BOUND (`d[1 : f()]`,
`d[1 : f() + 1]`) must be peeled into a sibling temp before lowering, exactly as
a call in an index key / array element / `new` argument is. solidity-lean's
sibling-prefix call hoister (`Expr.findArgPosInnerCall?`) had no `Expr.slice`
arm, and the var-decl hoist dispatcher (`isTarget`) excluded slice
initializers, so the direct lowering kept the call INSIDE the Core slice bound.
Evaluating an internal call as a pure slice-bound sub-expression is unsupported,
so the slice threw `RevertData.typeMismatch` -> spurious `Panic(0)`.

The fix adds the `Expr.slice` arm to `findArgPosInnerCall?` (descend base,
start, stop in source L2R order) and lists `Expr.slice` as a hoist target, so
`bytes calldata s = d[1 : f() + 1]` lowers as
`uint256 t = f(); bytes calldata s = d[1 : t + 1];` — the call runs once, as a
statement, with its side effect ordered correctly.

Submission `run(0x0011223344556677)`: `f()` sets `trace = 1`, returns 1, so the
slice is `d[1:2]` (length 1) and the function returns `s.length + trace = 2`
with storage slot 0 = 1. solc+EVM succeeds with `w:2, sto=0:1`; solidity-lean
formerly reverted `Panic(0)`.
-/

namespace SolidCore
namespace Solidity
namespace SolcAstImport
namespace CalldataSliceStopCallFuelWitness

open SolidCore.Solidity.Source

private def lit (s : String) : Expr := Expr.literal (Literal.number s)
private def d : Expr := Expr.ident "d"
private def trace : Expr := Expr.ident "trace"
private def callF : Expr := Expr.call (Expr.ident "f") []

-- `trace = trace * 10 + n; return r;`
private def traceReturns (n r : String) : List Stmt :=
  [ Stmt.expr (Expr.assign trace AssignOp.assign
      (Expr.binary BinaryOp.add (Expr.binary BinaryOp.mul trace (lit "10")) (lit n)))
  , Stmt.returnValues (some (lit r)) ]

private def fFn : ContractItem := ContractItem.function
  { kind := FunctionKind.function, name := some "f",
    visibility := some Visibility.internal_, mutability := StateMutability.nonpayable,
    params := [], returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false, override? := none, modifiers := [],
    body := some (Stmt.block (traceReturns "1" "1")) }

-- run(bytes calldata d): `bytes calldata s = d[1 : f() + 1]; return s.length + trace;`
private def runBody (stop : Expr) : List Stmt :=
  [ Stmt.varDecl [{ name := some "s", ty := some Ty.bytes, location := some DataLocation.calldata }]
      (some (Expr.slice d (some (lit "1")) (some stop)))
  , Stmt.returnValues (some
      (Expr.binary BinaryOp.add (Expr.member (Expr.ident "s") "length") trace)) ]

private def runFn (nm : String) (stop : Expr) : ContractItem := ContractItem.function
  { kind := FunctionKind.function, name := some nm,
    visibility := some Visibility.public_, mutability := StateMutability.nonpayable,
    params := [{ name := some "d", ty := Ty.bytes, location := some DataLocation.calldata }],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false, override? := none, modifiers := [],
    body := some (Stmt.block (runBody stop)) }

-- The submission: `stop = f() + 1`.
private def runCallStop : ContractItem :=
  runFn "run" (Expr.binary BinaryOp.add callF (lit "1"))
-- CONTROL: literal `stop = 2` (no compound bound) — must also succeed.
private def runLitStop : ContractItem := runFn "runLit" (lit "2")

-- PROBE B: bare call stop `d[1 : f()]` (no +1).
private def runBareCall : ContractItem :=
  runFn "runBareCall" callF

-- PROBE C: stop is a non-call compound `d[1 : 1 + 1]`.
private def runLitAdd : ContractItem :=
  runFn "runLitAdd" (Expr.binary BinaryOp.add (lit "1") (lit "1"))

def importedContractDecl0 : ContractDecl :=
  { kind := ContractKind.contract, name := "T",
    abstract := false, bases := [],
    items := [ ContractItem.stateVar { name := "trace", ty := Ty.uint 256 },
               fFn, runCallStop, runLitStop, runBareCall, runLitAdd ] }

def importedContract : ContractDecl := importedContractDecl0
def importedContracts : List ContractDecl := [importedContractDecl0]

def importedSourceUnit : SourceUnit :=
  { items := [SourceItem.pragma "solidity" "^0.8.35",
              SourceItem.contract importedContractDecl0] }

def importedContractAccepted : Bool :=
  TypeCheck.Result.isOk (TypeCheck.TypecheckedInput.checkedSourceUnit importedSourceUnit)

end CalldataSliceStopCallFuelWitness
end SolcAstImport
end Solidity
end SolidCore

namespace SolidCore
namespace Solidity
namespace Witness
namespace CalldataSliceStopCallFuel

open SolidCore.Solidity.Source
open SolidCore.Solidity.TypeCheck

abbrev Fam := SolidCore.Solidity.SolcAstImport.CalldataSliceStopCallFuelWitness.importedContract

def accepted : Bool :=
  SolidCore.Solidity.SolcAstImport.CalldataSliceStopCallFuelWitness.importedContractAccepted

private def dArg : Value := Value.bytes [0x00, 0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x77]

-- Submission run(0x0011223344556677): slice d[1 : f()+1] = d[1:2], length 1,
-- trace = 1 -> returns 2, storage slot 0 = 1.
def run_returns_2_slot_1 : Except TypeError Bool :=
  Examples.checkedOwnCallWordAndSlotMatches 256 Fam "run" State.empty [dArg] 2 1

-- CONTROL: literal-stop slice d[1:2] (length 1, `f` never called so trace = 0)
-- returns s.length + trace = 1, storage slot 0 = 0. This simple slice already
-- worked pre-fix; it guards against a regression on the common path.
def runLit_returns_1_slot_0 : Except TypeError Bool :=
  Examples.checkedOwnCallWordAndSlotMatches 256 Fam "runLit" State.empty [dArg] 1 0

-- BARE-CALL bound d[1 : f()] = d[1:1] (f returns 1): length 0, trace 1 -> 1,
-- slot 0 = 1. A call also survived un-hoisted here pre-fix (Panic 0).
def runBareCall_returns_1_slot_1 : Except TypeError Bool :=
  Examples.checkedOwnCallWordAndSlotMatches 256 Fam "runBareCall" State.empty [dArg] 1 1

-- CALL-FREE compound bound d[1 : 1 + 1] = d[1:2]: length 1, trace 0 -> 1,
-- slot 0 = 0. Never needed hoisting; stays green (no regression).
def runLitAdd_returns_1_slot_0 : Except TypeError Bool :=
  Examples.checkedOwnCallWordAndSlotMatches 256 Fam "runLitAdd" State.empty [dArg] 1 0

private def isOkTrue : Except TypeError Bool → Bool
  | Except.ok true => true
  | _ => false

#guard accepted
#guard isOkTrue run_returns_2_slot_1
#guard isOkTrue runLit_returns_1_slot_0
#guard isOkTrue runBareCall_returns_1_slot_1
#guard isOkTrue runLitAdd_returns_1_slot_0

end CalldataSliceStopCallFuel
end Witness
end Solidity
end SolidCore

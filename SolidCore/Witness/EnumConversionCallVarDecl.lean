import SolidCore.Solidity.Checked
import SolidCore.Witness.Checked

set_option maxHeartbeats 8000000

/-!
ENUM-CONVERSION-CALL-VARDECL (S, call-in-enum-conversion-revert-vs-success) — a
value-returning internal call inside an enum conversion (`En e = E(f())`,
`E(uint8(f()))`) must be peeled into a sibling temp before lowering, exactly as
a call in an index key / array element / `new` argument / calldata-slice bound
is. solidity-lean's sibling-prefix call hoister (`Expr.findArgPosInnerCall?`)
had no `Expr.enumFromUInt` arm, and the var-decl hoist dispatcher (`isTarget`)
excluded enum-conversion initializers, so the direct lowering kept the call
INSIDE the Core `enumFromUInt`. Evaluating an internal call as a pure
enum-conversion sub-expression is unsupported, so it threw -> spurious
`Panic(0)`.

The fix adds the `Expr.enumFromUInt` arm to `findArgPosInnerCall?` (descend the
converted expression) and lists `Expr.enumFromUInt` as a hoist target, so
`En0 ev0 = En0(uint8(tk0()))` lowers as
`uint256 t = tk0(); En0 ev0 = En0(uint8(t));` — the call runs once, as a
statement, with its side effect ordered correctly.

Submission `run()`: `tk0()` sets `trace = 1`, returns 1, so `En0(uint8(1))` is
`En0.B` (in range) and `p0()` returns `uint256(uint8(ev0)) = 1`; `run()` returns
1 with storage slot 0 (`trace`) = 1. solc+EVM succeeds with `w:1, sto=0:1`;
solidity-lean formerly reverted `Panic(0)`.
-/

namespace SolidCore
namespace Solidity
namespace SolcAstImport
namespace EnumConversionCallVarDeclWitness

open SolidCore.Solidity.Source

private def lit (s : String) : Expr := Expr.literal (Literal.number s)
private def trace : Expr := Expr.ident "trace"
private def callTk0 : Expr := Expr.call (Expr.ident "tk0") []
private def enumTy : Ty := Ty.user ({ segments := ["En0"] })

private def uint8Of (e : Expr) : Expr :=
  Expr.call (Expr.typeName (Ty.uint 8)) [Arg.positional e]
private def uint256Of (e : Expr) : Expr :=
  Expr.call (Expr.typeName (Ty.uint 256)) [Arg.positional e]
private def enumConv (e : Expr) : Expr :=
  Expr.call (Expr.typeName enumTy) [Arg.positional e]

-- `trace = trace * 10 + 1; return 1;`
private def tk0Body : List Stmt :=
  [ Stmt.expr (Expr.assign trace AssignOp.assign
      (Expr.binary BinaryOp.add (Expr.binary BinaryOp.mul trace (lit "10")) (lit "1")))
  , Stmt.returnValues (some (lit "1")) ]

private def tk0Fn : ContractItem := ContractItem.function
  { kind := FunctionKind.function, name := some "tk0",
    visibility := some Visibility.internal_, mutability := StateMutability.nonpayable,
    params := [], returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false, override? := none, modifiers := [],
    body := some (Stmt.block tk0Body) }

-- `En0 ev0 = En0(uint8(arg)); return uint256(uint8(ev0));`
private def pBody (arg : Expr) : List Stmt :=
  [ Stmt.varDecl [{ name := some "ev0", ty := some enumTy, location := none }]
      (some (enumConv (uint8Of arg)))
  , Stmt.returnValues (some (uint256Of (uint8Of (Expr.ident "ev0")))) ]

private def pFn (nm : String) (arg : Expr) : ContractItem := ContractItem.function
  { kind := FunctionKind.function, name := some nm,
    visibility := some Visibility.internal_, mutability := StateMutability.nonpayable,
    params := [], returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false, override? := none, modifiers := [],
    body := some (Stmt.block (pBody arg)) }

-- The submission: the enum conversion argument nests the call `tk0()`.
private def p0Fn : ContractItem := pFn "p0" callTk0
-- CONTROL: call-free enum conversion `En0(uint8(1))` — already lowered.
private def pLitFn : ContractItem := pFn "pLit" (lit "1")

private def runFn (nm callee : String) : ContractItem := ContractItem.function
  { kind := FunctionKind.function, name := some nm,
    visibility := some Visibility.public_, mutability := StateMutability.nonpayable,
    params := [], returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false, override? := none, modifiers := [],
    body := some (Stmt.block
      [Stmt.returnValues (some (Expr.call (Expr.ident callee) []))]) }

private def runCall : ContractItem := runFn "run" "p0"
private def runLit : ContractItem := runFn "runLit" "pLit"

def importedContractDecl0 : ContractDecl :=
  { kind := ContractKind.contract, name := "T",
    abstract := false, bases := [],
    items := [ ContractItem.stateVar { name := "trace", ty := Ty.uint 256 },
               ContractItem.enumDecl { name := "En0", cases := ["A", "B", "C"] },
               tk0Fn, p0Fn, pLitFn, runCall, runLit ] }

def importedContract : ContractDecl := importedContractDecl0
def importedContracts : List ContractDecl := [importedContractDecl0]

def importedSourceUnit : SourceUnit :=
  { items := [SourceItem.pragma "solidity" "^0.8.35",
              SourceItem.contract importedContractDecl0] }

def importedContractAccepted : Bool :=
  TypeCheck.Result.isOk (TypeCheck.TypecheckedInput.checkedSourceUnit importedSourceUnit)

end EnumConversionCallVarDeclWitness
end SolcAstImport
end Solidity
end SolidCore

namespace SolidCore
namespace Solidity
namespace Witness
namespace EnumConversionCallVarDecl

open SolidCore.Solidity.Source
open SolidCore.Solidity.TypeCheck

abbrev Fam := SolidCore.Solidity.SolcAstImport.EnumConversionCallVarDeclWitness.importedContract

def accepted : Bool :=
  SolidCore.Solidity.SolcAstImport.EnumConversionCallVarDeclWitness.importedContractAccepted

-- Submission run(): tk0() sets trace = 1, returns 1; En0(uint8(1)) = En0.B (in
-- range), p0() returns uint256(uint8(ev0)) = 1; run returns 1, storage slot 0
-- (trace) = 1. Pre-fix the nested call survived inside the Core enumFromUInt and
-- reverted Panic(0).
def run_returns_1_slot_1 : Except TypeError Bool :=
  Examples.checkedOwnCallWordAndSlotMatches 256 Fam "run" State.empty [] 1 1

-- CONTROL: call-free conversion En0(uint8(1)) — tk0 never runs (trace = 0),
-- p0Lit returns 1, slot 0 = 0. This path lowered directly pre-fix; it guards
-- against a regression on the common (no-nested-call) enum conversion.
def runLit_returns_1_slot_0 : Except TypeError Bool :=
  Examples.checkedOwnCallWordAndSlotMatches 256 Fam "runLit" State.empty [] 1 0

private def isOkTrue : Except TypeError Bool → Bool
  | Except.ok true => true
  | _ => false

#guard accepted
#guard isOkTrue run_returns_1_slot_1
#guard isOkTrue runLit_returns_1_slot_0

end EnumConversionCallVarDecl
end Witness
end Solidity
end SolidCore

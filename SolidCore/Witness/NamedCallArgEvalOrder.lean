import SolidCore.Solidity.Checked
import SolidCore.Witness.Checked

set_option maxHeartbeats 8000000

/-!
NAMED-CALL-ARG-EVAL-ORDER (S, named-argument-call-evaluated-in-written-order) — a
call with NAMED arguments evaluates its argument expressions in the callee's
PARAMETER-DECLARATION order, not the order written at the call site. solc 0.8.35
legacy codegen (`ExpressionCompiler.cpp`) reorders named arguments to parameter
order and then evaluates the argument list left-to-right; the ANF call-hoister in
solidity-lean lifted the nested argument calls in WRITTEN order, so
`g({b: t(1), a: t(2)})` ran `t(1)` before `t(2)`.

Submission `f()`: `t` folds a digit onto `trace` (`trace = trace*10 + k`). With
declaration order `(a, b)` the `a` expression `t(2)` runs first, then `t(1)`, so
`trace == 21`; argument BINDING is correct on both engines (`a == 2, b == 1`, so
`g` returns 21). solc+EVM: `w:21, sto=0:21`. Pre-fix solidity-lean lifted the
written-first `t(1)` first -> `trace == 12` (`w:12, sto=0:12`).

The fix reorders an internal call's named arguments into parameter-declaration
order (as positional args) BEFORE the ANF hoister lifts their nested calls, so
the hoist temps evaluate in solc's order — the same reorder the emit / revert /
custom-error paths already perform on their own statement shapes.
-/

namespace SolidCore
namespace Solidity
namespace SolcAstImport
namespace NamedCallArgEvalOrderWitness

open SolidCore.Solidity.Source

private def lit (s : String) : Expr := Expr.literal (Literal.number s)
private def trace : Expr := Expr.ident "trace"

-- `t(k)`: `trace = trace * 10 + k; return k;`
private def tBody : List Stmt :=
  [ Stmt.expr (Expr.assign trace AssignOp.assign
      (Expr.binary BinaryOp.add
        (Expr.binary BinaryOp.mul trace (lit "10")) (Expr.ident "k")))
  , Stmt.returnValues (some (Expr.ident "k")) ]

private def tFn : ContractItem := ContractItem.function
  { kind := FunctionKind.function, name := some "t",
    visibility := some Visibility.internal_, mutability := StateMutability.nonpayable,
    params := [{ name := some "k", ty := Ty.uint 256, location := none }],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false, override? := none, modifiers := [],
    body := some (Stmt.block tBody) }

-- `g(a, b) pure`: `return a * 10 + b;`
private def gFn : ContractItem := ContractItem.function
  { kind := FunctionKind.function, name := some "g",
    visibility := some Visibility.internal_, mutability := StateMutability.pure,
    params := [{ name := some "a", ty := Ty.uint 256, location := none },
               { name := some "b", ty := Ty.uint 256, location := none }],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false, override? := none, modifiers := [],
    body := some (Stmt.block
      [ Stmt.returnValues (some (Expr.binary BinaryOp.add
          (Expr.binary BinaryOp.mul (Expr.ident "a") (lit "10")) (Expr.ident "b"))) ]) }

private def callT (k : String) : Expr :=
  Expr.call (Expr.ident "t") [Arg.positional (lit k)]

-- The submission call, written order (b, a); declaration order (a, b).
private def namedCall : Expr :=
  Expr.call (Expr.ident "g")
    [ Arg.named "b" (callT "1"), Arg.named "a" (callT "2") ]

-- `f()`: `uint256 v = g({b: t(1), a: t(2)}); require(v == 21, "..."); return trace;`
private def fBody : List Stmt :=
  [ Stmt.varDecl [{ name := some "v", ty := some (Ty.uint 256), location := none }]
      (some namedCall)
  , Stmt.expr (Expr.call (Expr.ident "require")
      [ Arg.positional (Expr.binary BinaryOp.eq (Expr.ident "v") (lit "21"))
      , Arg.positional (Expr.literal (Literal.string "binding agrees on both engines")) ])
  , Stmt.returnValues (some trace) ]

private def fFn : ContractItem := ContractItem.function
  { kind := FunctionKind.function, name := some "f",
    visibility := some Visibility.public_, mutability := StateMutability.nonpayable,
    params := [], returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false, override? := none, modifiers := [],
    body := some (Stmt.block fBody) }

def importedContractDecl0 : ContractDecl :=
  { kind := ContractKind.contract, name := "C",
    abstract := false, bases := [],
    items := [ ContractItem.stateVar { name := "trace", ty := Ty.uint 256 },
               tFn, gFn, fFn ] }

def importedContract : ContractDecl := importedContractDecl0
def importedContracts : List ContractDecl := [importedContractDecl0]

def importedSourceUnit : SourceUnit :=
  { items := [SourceItem.pragma "solidity" "^0.8.35",
              SourceItem.contract importedContractDecl0] }

def importedContractAccepted : Bool :=
  TypeCheck.Result.isOk (TypeCheck.TypecheckedInput.checkedSourceUnit importedSourceUnit)

end NamedCallArgEvalOrderWitness
end SolcAstImport
end Solidity
end SolidCore

namespace SolidCore
namespace Solidity
namespace Witness
namespace NamedCallArgEvalOrder

open SolidCore.Solidity.Source
open SolidCore.Solidity.TypeCheck

abbrev Fam := SolidCore.Solidity.SolcAstImport.NamedCallArgEvalOrderWitness.importedContract

def accepted : Bool :=
  SolidCore.Solidity.SolcAstImport.NamedCallArgEvalOrderWitness.importedContractAccepted

-- Submission f(): declaration order (a, b) runs t(2) first, then t(1), so
-- trace == 21; g returns a*10+b == 21, v == 21 (require passes); f returns 21,
-- storage slot 0 (trace) == 21. Pre-fix the hoister lifted t(1) first -> 12.
def f_returns_21_slot_21 : Except TypeError Bool :=
  Examples.checkedOwnCallWordAndSlotMatches 256 Fam "f" State.empty [] 21 21

private def isOkTrue : Except TypeError Bool → Bool
  | Except.ok true => true
  | _ => false

#guard accepted
#guard isOkTrue f_returns_21_slot_21

end NamedCallArgEvalOrder
end Witness
end Solidity
end SolidCore

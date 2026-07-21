import SolidCore.Solidity.Checked
import SolidCore.Witness.Checked

set_option maxHeartbeats 4000000

/-!
ITEM-5 (operator using-for, SOUND fallback) — hand-built source-AST witness.

The solc-AST importer resolves user-defined operator applications to direct
free-function calls (solc annotates each operator node with its bound
function), so the `expandUsing` operator rewrite
(`usingFreeFunctionOperands?`) is exercised by SOURCE-level `Expr.binary`/
`Expr.unary` on UDVT operands — the shape a hand-built (or other-frontend)
AST carries. The strict operand-shape gate declines whenever an operand
cannot be typed (`abiTy*` = none); the ITEM-5 fallback then binds the unique
free function whose parameters ALL equal the using-directive's target UDVT —
exactly solc's binding rule — instead of silently leaving the raw operator
to fail-close downstream.

Real-EVM ground truth for the semantics: Forge lane
`operator-udvt-resolution` (8 tests, pinned solc 0.8.35, all PASS).
-/

namespace SolidCore
namespace Solidity
namespace Witness
namespace OperatorUdvtFallback

open SolidCore.Solidity
open SolidCore.Solidity.Source (State)

private def ptTy : Ty := Ty.user { segments := ["Pt"] }
private def wrap (e : Expr) : Expr :=
  Expr.call (Expr.member (Expr.typeName ptTy) "wrap") [Arg.positional e]
private def unwrap (e : Expr) : Expr :=
  Expr.call (Expr.member (Expr.typeName ptTy) "unwrap") [Arg.positional e]
private def u128 (name : String) : Parameter :=
  { name := some name, ty := Ty.uint 128, location := none }
private def ptParam (name : String) : Parameter :=
  { name := some name, ty := ptTy, location := none }

private def ptAddDecl : FunctionDecl :=
  { kind := FunctionKind.function, name := some "ptAdd",
    visibility := none, mutability := StateMutability.pure,
    params := [ptParam "a", ptParam "b"],
    returns := [{ name := none, ty := ptTy, location := none }],
    virtual := false, override? := none, modifiers := [],
    body := some (Stmt.block
      [ Stmt.returnValues (some (wrap
          (Expr.binary BinaryOp.add
            (unwrap (Expr.ident "a")) (unwrap (Expr.ident "b"))))) ]) }

private def ptNegDecl : FunctionDecl :=
  { kind := FunctionKind.function, name := some "ptNeg",
    visibility := none, mutability := StateMutability.pure,
    params := [ptParam "a"],
    returns := [{ name := none, ty := ptTy, location := none }],
    virtual := false, override? := none, modifiers := [],
    body := some (Stmt.block
      [ Stmt.returnValues (some (wrap
          (Expr.binary BinaryOp.sub
            (Expr.literal (Literal.number "0"))
            (unwrap (Expr.ident "a"))))) ]) }

private def usingOps : UsingDecl :=
  { library := { segments := [] },
    functions :=
      [ { function := { segments := ["ptAdd"] },
          operator? := some (UsingOperator.binary BinaryOp.add) }
      , { function := { segments := ["ptNeg"] },
          operator? := some (UsingOperator.unary UnaryOp.neg) } ],
    target := some ptTy,
    global := true }

/-- `run(a, b) = Pt.unwrap(Pt.wrap(a) + Pt.wrap(b))` written as a source
    OPERATOR application (`Expr.binary add`) on UDVT operands. -/
private def opContract : ContractDecl :=
  { kind := ContractKind.contract, name := "OpFB",
    abstract := false, bases := [],
    items :=
      [ ContractItem.function
          { kind := FunctionKind.function, name := some "run",
            visibility := some Visibility.external_,
            mutability := StateMutability.pure,
            params := [u128 "a", u128 "b"],
            returns := [{ name := none, ty := Ty.uint 128, location := none }],
            virtual := false, override? := none, modifiers := [],
            body := some (Stmt.block
              [ Stmt.returnValues (some (unwrap
                  (Expr.binary BinaryOp.add
                    (wrap (Expr.ident "a")) (wrap (Expr.ident "b"))))) ]) }
      , ContractItem.function
          { kind := FunctionKind.function, name := some "runChain",
            visibility := some Visibility.external_,
            mutability := StateMutability.pure,
            params := [u128 "a", u128 "b", u128 "c"],
            returns := [{ name := none, ty := Ty.uint 128, location := none }],
            virtual := false, override? := none, modifiers := [],
            body := some (Stmt.block
              [ Stmt.returnValues (some (unwrap
                  (Expr.binary BinaryOp.add
                    (Expr.binary BinaryOp.add
                      (wrap (Expr.ident "a")) (wrap (Expr.ident "b")))
                    (wrap (Expr.ident "c"))))) ]) }
      , ContractItem.function
          { kind := FunctionKind.function, name := some "runNeg",
            visibility := some Visibility.external_,
            mutability := StateMutability.pure,
            params := [u128 "a", u128 "b"],
            returns := [{ name := none, ty := Ty.uint 128, location := none }],
            virtual := false, override? := none, modifiers := [],
            body := some (Stmt.block
              [ Stmt.returnValues (some (unwrap
                  (Expr.unary UnaryOp.neg
                    (Expr.binary BinaryOp.add
                      (wrap (Expr.ident "a")) (wrap (Expr.ident "b")))))) ]) } ] }

private def unit : SourceUnit :=
  { items :=
      [ SourceItem.pragma "solidity" "^0.8.35"
      , SourceItem.freeUserValueType { name := "Pt", underlying := Ty.uint 128 }
      , SourceItem.freeFunction ptAddDecl
      , SourceItem.freeFunction ptNegDecl
      , SourceItem.usingDecl usingOps
      , SourceItem.contract opContract ] }

def unitAccepted : Bool :=
  TypeCheck.Result.isOk (TypeCheck.TypecheckedInput.checkedSourceUnit unit)

private def isOkTrue : Except TypeCheck.TypeError Bool → Bool
  | Except.ok true => true
  | _ => false

private def callRun (fn : String) (args : List Source.Value)
    (expected : Word) : Bool :=
  isOkTrue
    (TypeCheck.Examples.checkedCallWordMatches 4096 unit "OpFB" fn
      Source.State.empty args expected)

-- Forge-pinned semantics (lane operator-udvt-resolution):
-- 3 + 4 = 7 dispatched through ptAdd.
#guard unitAccepted
#guard callRun "run" [Source.Value.word 3, Source.Value.word 4] 7
-- (3 + 4) + 5 = 12; the outer +'s left operand is a rewritten ptAdd call.
#guard callRun "runChain"
  [Source.Value.word 3, Source.Value.word 4, Source.Value.word 5] 12
-- -(0 + 0) = 0 through ptNeg over a rewritten ptAdd call.
#guard callRun "runNeg" [Source.Value.word 0, Source.Value.word 0] 0

end OperatorUdvtFallback
end Witness
end Solidity
end SolidCore

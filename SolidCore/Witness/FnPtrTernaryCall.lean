import SolidCore.Solidity.Checked
import SolidCore.Witness.Checked

set_option maxHeartbeats 12000000

/-!
FNPTR-TERNARY-CALL (regression): calling directly through a ternary that selects
between two internal function pointers, with a side-effecting condition —
`(tick() ? a1 : a2)(x)`. The callee is a parenthesized `Conditional` whose
branches are internal-function identifiers, so the FunctionCall callee is a
non-identifier internal function-pointer expression (`Expr.ternary`), the same
boundary shape as `arr[i](x)` in [[internal-call-name-keying]].

Two gaps were closed:
  * the solc-AST importer left `TupleExpression.argumentTypes.typeIdentifier` /
    `.typeString` UNCLASSIFIED — solc annotates the parenthesized callee node
    with `argumentTypes` (the call's argument types) exactly as it does for the
    `Identifier`/`IndexAccess`/`MemberAccess`/… callee shapes, but the
    `TupleExpression` case was omitted, so an in-scope, solc-accepted program
    failed closed at import; and
  * the executable lowering routes a call through a non-identifier
    function-pointer callee via `ptrBoundaryCallExprParts?`
    (`Expr.call callee args` arm), which already accepts an arbitrary callee
    expression, so the ternary callee elaborates once the importer stops
    fail-closing.

Real solc 0.8.35 + EVM ground truth for `run(3)` from `t = 0`:
  r1: `tick()` → t=1 (odd → true)  → `a1(3) = 3+1 = 4`
  r2: `tick()` → t=2 (even → false) → `a2(3) = 3*2 = 6`
  return `4*10000 + 6*100 + t = 40000 + 600 + 2 = 40602` (0x9e9a), final `t = 2`.
-/

namespace SolidCore
namespace Solidity
namespace Witness
namespace FnPtrTernaryCall

open SolidCore.Solidity.Source
open SolidCore.Solidity.TypeCheck

private def unaryFn (name : Name) (body : Stmt) : ContractItem :=
  ContractItem.function
    { kind := FunctionKind.function
      name := some name
      visibility := some Visibility.internal_
      mutability := StateMutability.pure
      params := [{ name := some "v", ty := Ty.uint 256, location := none }]
      returns := [{ name := none, ty := Ty.uint 256, location := none }]
      virtual := false
      override? := none
      modifiers := []
      body := some body }

def runContract : ContractDecl :=
{ kind := ContractKind.contract
  name := "C"
  abstract := false
  bases := []
  items :=
    [ ContractItem.stateVar
        { name := "t"
          ty := Ty.uint 256
          visibility := some Visibility.public_
          mutability := VarMutability.mutable
          override? := none
          init := none }
      -- a1(v) = v + 1
    , unaryFn "a1"
        (Stmt.block
          [Stmt.returnValues
            (some (Expr.binary BinaryOp.add (Expr.ident "v")
              (Expr.literal (Literal.number "1"))))])
      -- a2(v) = v * 2
    , unaryFn "a2"
        (Stmt.block
          [Stmt.returnValues
            (some (Expr.binary BinaryOp.mul (Expr.ident "v")
              (Expr.literal (Literal.number "2"))))])
      -- tick(): t += 1; return t % 2 == 1;
    , ContractItem.function
        { kind := FunctionKind.function
          name := some "tick"
          visibility := some Visibility.internal_
          mutability := StateMutability.nonpayable
          params := []
          returns := [{ name := none, ty := Ty.bool, location := none }]
          virtual := false
          override? := none
          modifiers := []
          body := some (Stmt.block
            [ Stmt.expr
                (Expr.assign (Expr.ident "t") AssignOp.addAssign
                  (Expr.literal (Literal.number "1")))
            , Stmt.returnValues
                (some (Expr.binary BinaryOp.eq
                  (Expr.binary BinaryOp.mod (Expr.ident "t")
                    (Expr.literal (Literal.number "2")))
                  (Expr.literal (Literal.number "1")))) ]) }
      -- run(x):
      --   r1 = (tick() ? a1 : a2)(x);
      --   r2 = (tick() ? a1 : a2)(x);
      --   return r1 * 10000 + r2 * 100 + t;
    , ContractItem.function
        { kind := FunctionKind.function
          name := some "run"
          visibility := some Visibility.external_
          mutability := StateMutability.nonpayable
          params := [{ name := some "x", ty := Ty.uint 256, location := none }]
          returns := [{ name := none, ty := Ty.uint 256, location := none }]
          virtual := false
          override? := none
          modifiers := []
          body := some (Stmt.block
            [ Stmt.varDecl
                [{ name := some "r1", ty := Ty.uint 256, location := none }]
                (some (Expr.call
                  (Expr.ternary (Expr.call (Expr.ident "tick") [])
                    (Expr.ident "a1") (Expr.ident "a2"))
                  [Arg.positional (Expr.ident "x")]))
            , Stmt.varDecl
                [{ name := some "r2", ty := Ty.uint 256, location := none }]
                (some (Expr.call
                  (Expr.ternary (Expr.call (Expr.ident "tick") [])
                    (Expr.ident "a1") (Expr.ident "a2"))
                  [Arg.positional (Expr.ident "x")]))
            , Stmt.returnValues
                (some (Expr.binary BinaryOp.add
                  (Expr.binary BinaryOp.add
                    (Expr.binary BinaryOp.mul (Expr.ident "r1")
                      (Expr.literal (Literal.number "10000")))
                    (Expr.binary BinaryOp.mul (Expr.ident "r2")
                      (Expr.literal (Literal.number "100"))))
                  (Expr.ident "t"))) ]) } ] }

def runSourceUnit : SourceUnit :=
  { items := [SourceItem.pragma "solidity" "^0.8.35", SourceItem.contract runContract] }

def accepted : Bool :=
  TypeCheck.Result.isOk (TypeCheck.TypecheckedInput.checkedSourceUnit runSourceUnit)

-- `run(3)` from `t=0`: r1=a1(3)=4, r2=a2(3)=6, t=2 → 4*10000+6*100+2 = 40602.
def run_3_is_40602 : Except TypeError Bool :=
  Examples.checkedOwnCallWordMatches 256 runContract "run" State.empty
    [Value.word 3] 40602

-- Final storage: `t = 2` after two `tick()`s.
def run_3_final_t : Except TypeError CoreState :=
  Examples.checkedOwnCallState 256 runContract "run" State.empty [Value.word 3]

-- `run(5)` from `t=0`: r1=a1(5)=6, r2=a2(5)=10, t=2 → 6*10000+10*100+2 = 61002.
def run_5_is_61002 : Except TypeError Bool :=
  Examples.checkedOwnCallWordMatches 256 runContract "run" State.empty
    [Value.word 5] 61002

private def isOkTrue : Except TypeError Bool -> Bool
  | Except.ok true => true
  | _ => false

private def finalTIs2 : Bool :=
  match run_3_final_t with
  | Except.ok state => SolidCore.Solidity.Source.wordEq (state.loadSlot 0) 2
  | _ => false

#guard accepted
#guard isOkTrue run_3_is_40602
#guard isOkTrue run_5_is_61002
#guard finalTIs2

end FnPtrTernaryCall
end Witness
end Solidity
end SolidCore

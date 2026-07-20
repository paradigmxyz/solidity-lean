import SolidCore.Solidity.Checked
import SolidCore.Witness.Checked

set_option maxHeartbeats 12000000

/-!
PACKED-SIGNED-ARRAY-MEM-ARITH (regression): a packed signed storage array
(`int8[]`) copied to memory and summed, then arithmetic against a literal fed
through an unsigned conversion —

  int8[] a;
  uint256 public out;
  function run() external returns (uint256) {
    a.push(-1); a.push(100); a.push(-128); a.push(0); a.push(127);
    int8[] memory m = a;
    int256 sum = 0;
    for (uint256 i = 0; i < m.length; i++) { sum += int256(m[i]); }
    out = uint256(sum + 1000);
    return out;
  }

Real solc 0.8.35 + EVM: the elements sum to -1+100-128+0+127 = 98, so
`sum + 1000 = 1098`, `run()` returns 1098 and slot 1 (`out`) = 1098. The packed
data slot holds the five sign-extended bytes 0xff,0x64,0x80,0x00,0x7f =
545469261055.

The bug: an unpacked signed element (`int256(m[i])` → `Value.int`) added to a
literal that the env-less `Expr.toCore?` lowers to `Expr.word` (the shape
produced inside `uint256(sum + 1000)`) reached `BinaryOp.apply` as
`Value.int + Value.word`. The arithmetic branch only handled `shl`/`shr`/`sar`/
`exp` for that operand pairing and Panic(0)'d (`typeMismatch`) on `add` — so the
whole call reverted `panic:0` instead of returning 1098. A `Value.int` operand
forces the operation signed (int/uint never mix in a well-typed program), so the
mixed pairing now dispatches to the signed path (`applySignedWord`), which also
matters for the overflow check (`-1 + 1000` overflows as unsigned but not
signed).
-/

namespace SolidCore
namespace Solidity
namespace Witness
namespace PackedSignedArrayMemArith

open SolidCore.Solidity.Source
open SolidCore.Solidity.TypeCheck

private def lit (s : String) : Expr := Expr.literal (Literal.number s)
private def negLit (s : String) : Expr := Expr.unary UnaryOp.neg (lit s)
private def push (name : String) (v : Expr) : Stmt :=
  Stmt.expr (Expr.call (Expr.member (Expr.ident name) "push") [Arg.positional v])
private def i256 (e : Expr) : Expr :=
  Expr.call (Expr.typeName (Ty.int 256)) [Arg.positional e]
private def u256 (e : Expr) : Expr :=
  Expr.call (Expr.typeName (Ty.uint 256)) [Arg.positional e]

def runContract : ContractDecl :=
{ kind := ContractKind.contract
  name := "C"
  abstract := false
  bases := []
  items :=
    [ ContractItem.stateVar
        { name := "a"
          ty := Ty.array (Ty.int 8) none
          visibility := some Visibility.internal_
          mutability := VarMutability.mutable
          override? := none
          init := none }
    , ContractItem.stateVar
        { name := "out"
          ty := Ty.uint 256
          visibility := some Visibility.public_
          mutability := VarMutability.mutable
          override? := none
          init := none }
    , ContractItem.function
        { kind := FunctionKind.function
          name := some "run"
          visibility := some Visibility.external_
          mutability := StateMutability.nonpayable
          params := []
          returns := [{ name := none, ty := Ty.uint 256, location := none }]
          virtual := false
          override? := none
          modifiers := []
          body := some (Stmt.block
            [ push "a" (negLit "1")
            , push "a" (lit "100")
            , push "a" (negLit "128")
            , push "a" (lit "0")
            , push "a" (lit "127")
            , Stmt.varDecl
                [{ name := some "m"
                   ty := some (Ty.array (Ty.int 8) none)
                   location := some DataLocation.memory }]
                (some (Expr.ident "a"))
            , Stmt.varDecl
                [{ name := some "sum"
                   ty := some (Ty.int 256)
                   location := none }]
                (some (lit "0"))
            , Stmt.forLoop
                (some (Stmt.varDecl
                  [{ name := some "i"
                     ty := some (Ty.uint 256)
                     location := none }]
                  (some (lit "0"))))
                (some (Expr.binary BinaryOp.lt (Expr.ident "i")
                  (Expr.member (Expr.ident "m") "length")))
                (some (Expr.unary UnaryOp.postIncrement (Expr.ident "i")))
                (Stmt.block
                  [ Stmt.expr (Expr.assign (Expr.ident "sum") AssignOp.addAssign
                      (i256 (Expr.index (Expr.ident "m") (Expr.ident "i")))) ])
            , Stmt.expr (Expr.assign (Expr.ident "out") AssignOp.assign
                (u256 (Expr.binary BinaryOp.add (Expr.ident "sum") (lit "1000"))))
            , Stmt.returnValues (some (Expr.ident "out")) ]) } ] }

def runSourceUnit : SourceUnit :=
  { items := [SourceItem.pragma "solidity" "^0.8.35", SourceItem.contract runContract] }

def accepted : Bool :=
  TypeCheck.Result.isOk (TypeCheck.TypecheckedInput.checkedSourceUnit runSourceUnit)

def deployedState : Except TypeError CoreState := do
  let result ← CheckedInput.ownConstruct 4096 runContract State.empty []
  match result with
  | SolidCore.Solidity.Source.CallResult.returned state _ => Except.ok state
  | _ => Except.error (executableFailure "constructor")

-- Real solc 0.8.35 + EVM ground truth: `run()` returns 1098.
def run_returns_1098 : Except TypeError Bool := do
  let state ← deployedState
  Examples.checkedOwnCallWordMatches 4096 runContract "run" state [] 1098

-- Final storage: slot 1 (`out`) = 1098; slot 0 (array length) = 5.
def storage_after : Except TypeError Bool := do
  let state ← deployedState
  let state ← Examples.checkedOwnCallState 4096 runContract "run" state []
  Except.ok
    (SolidCore.Solidity.Source.wordEq (state.loadSlot 1) 1098 &&
      SolidCore.Solidity.Source.wordEq (state.loadSlot 0) 5)

private def isOkTrue : Except TypeError Bool -> Bool
  | Except.ok true => true
  | _ => false

#guard accepted
#guard isOkTrue run_returns_1098
#guard isOkTrue storage_after

end PackedSignedArrayMemArith
end Witness
end Solidity
end SolidCore

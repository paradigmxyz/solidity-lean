import SolidCore.Solidity.Checked
import SolidCore.Witness.Checked

set_option maxHeartbeats 8000000

/-!
CALL-IN-ABI-ENCODE-NESTED (soundness gap): a variable DECLARATION whose
initializer is an ident-headed builtin call that TRANSITIVELY nests one or more
INTERNAL calls in an argument-like position —

  uint256 trace;
  function f() internal returns (uint256) { trace = trace*10+1; return 1; }
  function g() internal returns (uint256) { trace = trace*10+2; return 2; }
  function run() public returns (uint256) {
    bytes32 k = keccak256(bytes.concat(abi.encode(f(), g())));
    return uint256(k) % 7 + trace;
  }

Real solc 0.8.35 + EVM ground truth: f() and g() are evaluated left-to-right
(f: trace 0→1, g: 1→12), so `abi.encode(f(), g())` is the two words 1 and 2,
trace ends 12, keccak256 of that concat mod 7 is 6, and run() returns
6 + 12 = 18; storage slot 0 = 12.

The bug: the single-binding var-decl arm for an `Expr.call (Expr.ident name)`
initializer had no arm that reaches the two internal calls buried under
`keccak256`/`bytes.concat`/`abi.encode`. `internalSingleReturnCallCore?` fails
(keccak256 is a builtin), the abi one-call peel stalls on the SECOND call, and
the statement fell through to the env-less `Stmt.toCore?`, which cannot lower a
nested internal call — the declaration over-rejected, poisoning the contract's
executable lowering, and replay Panicked 0 instead of running.

The fix routes that fallback through the existing generic argument-position
hoister (`Expr.argPositionHoistPrefix?`) before the env-less lowering, exactly as
the direct-`abi.*` var-decl arm already does: it descends through the call
wrappers and peels BOTH f() and g() into ordered sibling prefix temps, then
re-lowers `bytes32 k = keccak256(bytes.concat(abi.encode((uint256)(t0), (uint256)(t1))))`
cleanly. It fires only when a nested call is actually found, so every previously
accepted initializer is byte-identical.
-/

namespace SolidCore
namespace Solidity
namespace Witness
namespace AbiEncodeCallArgConcatKeccak

open SolidCore.Solidity.Source
open SolidCore.Solidity.TypeCheck

private def u256 : Ty := Ty.uint 256
private def lit (s : String) : Expr := Expr.literal (Literal.number s)
private def call0 (fn : String) : Expr := Expr.call (Expr.ident fn) []

private def bumpTrace (k : String) : Stmt :=
  Stmt.expr (Expr.assign (Expr.ident "trace") AssignOp.assign
    (Expr.binary BinaryOp.add
      (Expr.binary BinaryOp.mul (Expr.ident "trace") (lit "10")) (lit k)))

private def fFn : FunctionDecl :=
  { kind := FunctionKind.function, name := some "f"
    visibility := some Visibility.internal_, mutability := StateMutability.nonpayable
    params := [], returns := [{ name := none, ty := u256, location := none }]
    virtual := false, override? := none, modifiers := []
    body := some (Stmt.block [ bumpTrace "1", Stmt.returnValues (some (lit "1")) ]) }

private def gFn : FunctionDecl :=
  { kind := FunctionKind.function, name := some "g"
    visibility := some Visibility.internal_, mutability := StateMutability.nonpayable
    params := [], returns := [{ name := none, ty := u256, location := none }]
    virtual := false, override? := none, modifiers := []
    body := some (Stmt.block [ bumpTrace "2", Stmt.returnValues (some (lit "2")) ]) }

-- bytes32 k = keccak256(bytes.concat(abi.encode(f(), g()))); return uint256(k) % 7 + trace;
private def abiEnc : Expr :=
  Expr.call (Expr.member (Expr.ident "abi") "encode")
    [Arg.positional (call0 "f"), Arg.positional (call0 "g")]
private def bytesConcat : Expr :=
  Expr.call (Expr.member (Expr.ident "bytes") "concat") [Arg.positional abiEnc]
private def kecCall : Expr :=
  Expr.call (Expr.ident "keccak256") [Arg.positional bytesConcat]

private def runFn : FunctionDecl :=
  { kind := FunctionKind.function, name := some "run"
    visibility := some Visibility.public_, mutability := StateMutability.nonpayable
    params := [], returns := [{ name := none, ty := u256, location := none }]
    virtual := false, override? := none, modifiers := []
    body := some (Stmt.block
      [ Stmt.varDecl
          [ { name := some "k", ty := some (Ty.fixedBytes 32), location := none } ]
          (some kecCall)
      , Stmt.returnValues (some (Expr.binary BinaryOp.add
          (Expr.binary BinaryOp.mod
            (Expr.call (Expr.typeName u256) [Arg.positional (Expr.ident "k")])
            (lit "7"))
          (Expr.ident "trace"))) ]) }

def runContract : ContractDecl :=
{ kind := ContractKind.contract, name := "T", abstract := false, bases := []
  items :=
    [ ContractItem.stateVar
        { name := "trace", ty := u256, visibility := some Visibility.internal_
          mutability := VarMutability.mutable, override? := none, init := none }
    , ContractItem.function fFn
    , ContractItem.function gFn
    , ContractItem.function runFn ] }

def runSourceUnit : SourceUnit :=
  { items := [SourceItem.pragma "solidity" "^0.8.35", SourceItem.contract runContract] }

def accepted : Bool :=
  TypeCheck.Result.isOk (TypeCheck.TypecheckedInput.checkedSourceUnit runSourceUnit)

def run_is_18 : Except TypeError Bool :=
  Examples.checkedOwnCallWordMatches 4096 runContract "run" State.empty [] 18

private def isOkTrue : Except TypeError Bool → Bool
  | Except.ok true => true
  | _ => false

#guard accepted
#guard isOkTrue run_is_18

end AbiEncodeCallArgConcatKeccak
end Witness
end Solidity
end SolidCore

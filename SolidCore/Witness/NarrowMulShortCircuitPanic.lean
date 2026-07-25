import SolidCore.Solidity.Checked
import SolidCore.Witness.Checked

set_option maxHeartbeats 8000000

/-!
NARROW-MUL-SHORT-CIRCUIT-PANIC (S, narrow-overflow-in-short-circuit) — a NARROW
(uint64) checked multiplication that overflows must Panic(0x11) even when it sits
inside the short-circuit RIGHT operand of `&&`.

`uint64(2^32) * uint64(2^32)` = 2^64 overflows uint64 (max 2^64-1). solc wraps it
in `checked_mul_t_uint64`, which reverts Panic(0x11). When the multiplication is
the right operand of a short-circuit `c && ((ma0*mb0) != 0)` with `c` true, solc
still evaluates the operand and panics. solidity-lean formerly dropped the narrow
overflow check on the short-circuit operand and returned success (1).
-/

namespace SolidCore
namespace Solidity
namespace SolcAstImport
namespace NarrowMulShortCircuitPanicWitness

open SolidCore.Solidity.Source

private def c : Expr := Expr.ident "c"
private def u64 (e : Expr) : Expr :=
  Expr.call (Expr.typeName (Ty.uint 64)) [Arg.positional e]
private def num (s : String) : Expr := Expr.literal (Literal.number s)
private def bin (op : BinaryOp) (x y : Expr) : Expr := Expr.binary op x y

-- The submission body: uint64 ma0/mb0 = 2^32; bool bb0 = c && ((ma0*mb0 << 0) != 0);
-- return bb0 ? 1 : 0;
private def bb0Init : Expr :=
  bin BinaryOp.boolAnd c
    (bin BinaryOp.ne
      (bin BinaryOp.shl
        (bin BinaryOp.mul (Expr.ident "ma0") (Expr.ident "mb0"))
        (num "0"))
      (num "0"))

private def fBody : Stmt := Stmt.block
  [ Stmt.varDecl [{ name := some "ma0", ty := some (Ty.uint 64), location := none }]
      (some (u64 (num "4294967296")))
  , Stmt.varDecl [{ name := some "mb0", ty := some (Ty.uint 64), location := none }]
      (some (u64 (num "4294967296")))
  , Stmt.varDecl [{ name := some "bb0", ty := some Ty.bool, location := none }]
      (some bb0Init)
  , Stmt.returnValues
      (some (Expr.ternary (Expr.ident "bb0") (num "1") (num "0"))) ]

private def fFn : ContractItem := ContractItem.function
  { kind := FunctionKind.function, name := some "f",
    visibility := some Visibility.external_, mutability := StateMutability.pure,
    params := [{ name := some "c", ty := Ty.bool, location := none }],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false, override? := none, modifiers := [],
    body := some fBody }

-- CONTROL: the same narrow overflow NOT in a short-circuit operand — a plain
-- var decl `uint64 r = ma0 * mb0;` must panic unconditionally.
private def gBody : Stmt := Stmt.block
  [ Stmt.varDecl [{ name := some "ma0", ty := some (Ty.uint 64), location := none }]
      (some (u64 (num "4294967296")))
  , Stmt.varDecl [{ name := some "mb0", ty := some (Ty.uint 64), location := none }]
      (some (u64 (num "4294967296")))
  , Stmt.varDecl [{ name := some "r", ty := some (Ty.uint 64), location := none }]
      (some (bin BinaryOp.mul (Expr.ident "ma0") (Expr.ident "mb0")))
  , Stmt.returnValues (some (num "1")) ]

private def gFn : ContractItem := ContractItem.function
  { kind := FunctionKind.function, name := some "g",
    visibility := some Visibility.external_, mutability := StateMutability.pure,
    params := [],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false, override? := none, modifiers := [],
    body := some gBody }

-- EXACT submission shape: left operand is a STATE VAR read `cflag`.
private def runBody : Stmt := Stmt.block
  [ Stmt.varDecl [{ name := some "ma0", ty := some (Ty.uint 64), location := none }]
      (some (u64 (num "4294967296")))
  , Stmt.varDecl [{ name := some "mb0", ty := some (Ty.uint 64), location := none }]
      (some (u64 (num "4294967296")))
  , Stmt.varDecl [{ name := some "bb0", ty := some Ty.bool, location := none }]
      (some (bin BinaryOp.boolAnd (Expr.ident "cflag")
        (bin BinaryOp.ne
          (bin BinaryOp.shl
            (bin BinaryOp.mul (Expr.ident "ma0") (Expr.ident "mb0"))
            (num "0"))
          (num "0"))))
  , Stmt.returnValues
      (some (Expr.ternary (Expr.ident "bb0") (num "1") (num "0"))) ]

private def runFn : ContractItem := ContractItem.function
  { kind := FunctionKind.function, name := some "run",
    visibility := some Visibility.external_, mutability := StateMutability.nonpayable,
    params := [],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false, override? := none, modifiers := [],
    body := some runBody }

-- VARIANT h: short-circuit operand WITHOUT the shift -> `c && ((ma0*mb0) != 0)`.
private def hBody : Stmt := Stmt.block
  [ Stmt.varDecl [{ name := some "ma0", ty := some (Ty.uint 64), location := none }]
      (some (u64 (num "4294967296")))
  , Stmt.varDecl [{ name := some "mb0", ty := some (Ty.uint 64), location := none }]
      (some (u64 (num "4294967296")))
  , Stmt.varDecl [{ name := some "bb0", ty := some Ty.bool, location := none }]
      (some (bin BinaryOp.boolAnd c
        (bin BinaryOp.ne (bin BinaryOp.mul (Expr.ident "ma0") (Expr.ident "mb0")) (num "0"))))
  , Stmt.returnValues (some (Expr.ternary (Expr.ident "bb0") (num "1") (num "0"))) ]

private def hFn : ContractItem := ContractItem.function
  { kind := FunctionKind.function, name := some "h",
    visibility := some Visibility.external_, mutability := StateMutability.pure,
    params := [{ name := some "c", ty := Ty.bool, location := none }],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false, override? := none, modifiers := [], body := some hBody }

-- VARIANT d: shift wrapper but NO short-circuit -> `return ((ma0*mb0)<<0) != 0;`.
private def dBody : Stmt := Stmt.block
  [ Stmt.varDecl [{ name := some "ma0", ty := some (Ty.uint 64), location := none }]
      (some (u64 (num "4294967296")))
  , Stmt.varDecl [{ name := some "mb0", ty := some (Ty.uint 64), location := none }]
      (some (u64 (num "4294967296")))
  , Stmt.returnValues (some (Expr.ternary
      (bin BinaryOp.ne
        (bin BinaryOp.shl (bin BinaryOp.mul (Expr.ident "ma0") (Expr.ident "mb0")) (num "0"))
        (num "0"))
      (num "1") (num "0"))) ]

private def dFn : ContractItem := ContractItem.function
  { kind := FunctionKind.function, name := some "d",
    visibility := some Visibility.external_, mutability := StateMutability.pure,
    params := [],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false, override? := none, modifiers := [], body := some dBody }

-- CONTROL okShift: a NON-overflowing narrow mul under a shift still computes the
-- right value through the new arm: `uint64 a=3,b=5; return ((a*b) << 2);` = 60.
private def okBody : Stmt := Stmt.block
  [ Stmt.varDecl [{ name := some "a", ty := some (Ty.uint 64), location := none }]
      (some (u64 (num "3")))
  , Stmt.varDecl [{ name := some "b", ty := some (Ty.uint 64), location := none }]
      (some (u64 (num "5")))
  , Stmt.returnValues (some
      (bin BinaryOp.shl (bin BinaryOp.mul (Expr.ident "a") (Expr.ident "b")) (num "2"))) ]

private def okFn : ContractItem := ContractItem.function
  { kind := FunctionKind.function, name := some "okShift",
    visibility := some Visibility.external_, mutability := StateMutability.pure,
    params := [],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false, override? := none, modifiers := [], body := some okBody }

def importedContractDecl0 : ContractDecl :=
  { kind := ContractKind.contract, name := "C",
    abstract := false, bases := [],
    items := [ContractItem.stateVar { name := "cflag", ty := Ty.bool, visibility := some Visibility.internal_ },
              ContractItem.stateVar { name := "trace", ty := Ty.uint 256, visibility := some Visibility.internal_ },
              fFn, gFn, hFn, dFn, okFn, runFn] }

def importedContract : ContractDecl := importedContractDecl0

def importedSourceUnit : SourceUnit :=
  { items := [SourceItem.pragma "solidity" "^0.8.35",
              SourceItem.contract importedContractDecl0] }

def importedContractAccepted : Bool :=
  TypeCheck.Result.isOk (TypeCheck.TypecheckedInput.checkedSourceUnit importedSourceUnit)

end NarrowMulShortCircuitPanicWitness
end SolcAstImport
end Solidity
end SolidCore

namespace SolidCore
namespace Solidity
namespace Witness
namespace NarrowMulShortCircuitPanic

open SolidCore.Solidity.Source
open SolidCore.Solidity.TypeCheck

abbrev Fam := SolidCore.Solidity.SolcAstImport.NarrowMulShortCircuitPanicWitness.importedContract

def accepted : Bool :=
  SolidCore.Solidity.SolcAstImport.NarrowMulShortCircuitPanicWitness.importedContractAccepted

-- EXACT SUBMISSION: run() with cflag=true (constructor). The `&&` operand is
-- evaluated; `(uint64(2^32)*uint64(2^32)) << 0` overflows uint64 -> Panic(0x11).
def run_cflag_true_panics : Except TypeError Bool :=
  Examples.checkedOwnCallPanicMatches 256 Fam "run" (State.empty.storeSlot 0 1) [] 17

-- run() with cflag=false: short-circuit skips the operand -> returns 0 (no panic).
def run_cflag_false_is_0 : Except TypeError Bool :=
  Examples.checkedOwnCallWordMatches 256 Fam "run" State.empty [] 0

-- f(true): param left operand true; short-circuit operand evaluated -> Panic(0x11).
def f_true_panics : Except TypeError Bool :=
  Examples.checkedOwnCallPanicMatches 256 Fam "f" State.empty [Value.word 1] 17

-- f(false): short-circuit skips the operand -> returns 0 (no panic).
def f_false_is_0 : Except TypeError Bool :=
  Examples.checkedOwnCallWordMatches 256 Fam "f" State.empty [Value.word 0] 0

-- ISOLATION h: `&&` operand WITHOUT the shift wrapper already panicked before the
-- fix -> the `&&` is NOT the trigger.
def h_true_panics : Except TypeError Bool :=
  Examples.checkedOwnCallPanicMatches 256 Fam "h" State.empty [Value.word 1] 17

-- ISOLATION d: the shift wrapper WITHOUT any `&&` -> the shift IS the trigger
-- (returned 0 before the fix, now Panic(0x11)).
def d_panics : Except TypeError Bool :=
  Examples.checkedOwnCallPanicMatches 256 Fam "d" State.empty [] 17

-- CONTROL g: narrow mul overflow with neither shift nor `&&` -> always Panic(0x11).
def g_panics : Except TypeError Bool :=
  Examples.checkedOwnCallPanicMatches 256 Fam "g" State.empty [] 17

-- CONTROL okShift: a non-overflowing narrow mul under a shift still returns 60,
-- confirming the new arm's cleanup is an idempotent mask when nothing overflows.
def okShift_is_60 : Except TypeError Bool :=
  Examples.checkedOwnCallWordMatches 256 Fam "okShift" State.empty [] 60

private def isOkTrue : Except TypeError Bool → Bool
  | Except.ok true => true
  | _ => false

#guard accepted
#guard isOkTrue run_cflag_true_panics
#guard isOkTrue run_cflag_false_is_0
#guard isOkTrue f_true_panics
#guard isOkTrue f_false_is_0
#guard isOkTrue h_true_panics
#guard isOkTrue d_panics
#guard isOkTrue g_panics
#guard isOkTrue okShift_is_60

end NarrowMulShortCircuitPanic
end Witness
end Solidity
end SolidCore

import SolidCore.Solidity.Checked
import SolidCore.Witness.Checked

set_option maxHeartbeats 8000000

/-!
NARROW-ADDMOD-FNPTR-PANIC (S, narrow-addmod-through-fnptr-arg) — a NARROW
(uint128) checked add that overflows, buried in the ARGUMENT of an internal
function-pointer call, must still Panic(0x11).

The submission's `p0()`:

```
uint128 am0 = uint128(type(uint128).max);  // 2^128 - 1
uint128 an0 = uint128(9);
function(uint128) internal pure returns (uint128) fp0 = fpt0;  // identity
return uint256(fp0(uint128(uint128(addmod(uint256(am0 + an0), 1, 7)))));
```

`am0 + an0` = (2^128 - 1) + 9 overflows uint128 → solc evaluates the checked
uint128 add and reverts Panic(0x11) BEFORE the `addmod`/cast/call ever run.
solidity-lean ran `am0 + an0` bare at 256 bits (= 2^128 + 8, no overflow); the
addmod then produced `(2^128 + 9) mod 7 = 6` and the call returned 6
successfully — a revert-vs-success soundness gap.

Root cause (NOT the function pointer — it is incidental obfuscation): the
`addmod`-argument reroute gate `Expr.abiArgNeedsEnvCleanup?` only peeled NARROW
casts to find overflow arithmetic, so it never saw the narrow `am0 + an0` under
the `uint256(...)` WIDE cast — the identical shape the return-position wide-cast
arm (#31) already handled. The bare `addmod(uint256(a + b), 1, 7)` return (`j`)
reproduced it without any fnptr; the submission additionally buries the addmod in
a `uint128(uint128(...))` cast tower (the arg shape a value returned through an
internal function pointer takes), which the cast-of-builtin lowering also failed
to peel. Fix: make the flag transparent to WORD- AND NARROW-int casts (recurse
through the cast to the flagged content), and broaden the cast-of-builtin arm to
lower any flagged argument env-aware so each cast layer peels inward until the
addmod's operand-width Panic 0x11 fires.
-/

namespace SolidCore
namespace Solidity
namespace Witness
namespace NarrowAddmodFnptrPanic

open SolidCore.Solidity.Source
open SolidCore.Solidity.TypeCheck

private def uintMax128 : String := "340282366920938463463374607431768211455"
private def num (s : String) : Expr := Expr.literal (Literal.number s)
private def castTo (n : Nat) (e : Expr) : Expr :=
  Expr.call (Expr.typeName (Ty.uint n)) [Arg.positional e]

private def fptTy : Ty :=
  Ty.function [Ty.uint 128] [Ty.uint 128] StateMutability.pure Visibility.internal_

-- fpt0(uint128 x) internal pure returns (uint128) { return x; }
private def fpt0Fn : ContractItem :=
  ContractItem.function
    { kind := FunctionKind.function
      name := some "fpt0"
      visibility := some Visibility.internal_
      mutability := StateMutability.pure
      params := [{ name := some "x", ty := Ty.uint 128, location := none }]
      returns := [{ name := none, ty := Ty.uint 128, location := none }]
      virtual := false
      override? := none
      modifiers := []
      body := some (Stmt.block [Stmt.returnValues (some (Expr.ident "x"))]) }

-- am0 + an0 : the narrow (uint128) checked add that overflows.
private def narrowAdd : Expr :=
  Expr.binary BinaryOp.add (Expr.ident "am0") (Expr.ident "an0")

-- addmod(uint256(am0 + an0), 1, 7)
private def addmodExpr : Expr :=
  Expr.call (Expr.ident "addmod")
    [ Arg.positional (castTo 256 narrowAdd)
    , Arg.positional (num "1")
    , Arg.positional (num "7") ]

-- the two uint128 var-decl inits, shared by both functions
private def decls : List Stmt :=
  [ Stmt.varDecl [{ name := some "am0", ty := some (Ty.uint 128), location := none }]
      (some (castTo 128 (num uintMax128)))
  , Stmt.varDecl [{ name := some "an0", ty := some (Ty.uint 128), location := none }]
      (some (castTo 128 (num "9"))) ]

-- f(): the submission shape — the overflowing add flows through the fp0 CALL arg.
--   return uint256(fp0(uint128(uint128(addmod(uint256(am0 + an0), 1, 7)))));
private def fBody : Stmt := Stmt.block
  (decls ++
    [ Stmt.varDecl
        [{ name := some "fp0", ty := some fptTy, location := none }]
        (some (Expr.ident "fpt0"))
    , Stmt.returnValues
        (some (castTo 256
          (Expr.call (Expr.ident "fp0")
            [Arg.positional (castTo 128 (castTo 128 addmodExpr))]))) ])

private def fFn : ContractItem :=
  ContractItem.function
    { kind := FunctionKind.function
      name := some "f"
      visibility := some Visibility.external_
      mutability := StateMutability.pure
      params := []
      returns := [{ name := none, ty := Ty.uint 256, location := none }]
      virtual := false
      override? := none
      modifiers := []
      body := some fBody }

-- CONTROL g(): same overflowing add through the SAME cast tower but WITHOUT the
-- fp0 call — `uint256(uint128(uint128(addmod(uint256(am0 + an0), 1, 7))))`.
-- This position already routed env-aware, so it must Panic(0x11) too (proves the
-- add itself overflows and isolates the fnptr-arg as the sole regression site).
private def gBody : Stmt := Stmt.block
  (decls ++
    [ Stmt.returnValues
        (some (castTo 256 (castTo 128 (castTo 128 addmodExpr)))) ])

private def gFn : ContractItem :=
  ContractItem.function
    { kind := FunctionKind.function
      name := some "g"
      visibility := some Visibility.external_
      mutability := StateMutability.pure
      params := []
      returns := [{ name := none, ty := Ty.uint 256, location := none }]
      virtual := false
      override? := none
      modifiers := []
      body := some gBody }

-- CONTROL h(): safe inputs (am0 = 1, an0 = 9) through the fp0 call arg — no
-- overflow, so `addmod((1+9), 1, 7) = 11 mod 7 = 4` returns 4 (proves the fnptr
-- call value path is otherwise byte-identical / non-panicking).
private def hDecls : List Stmt :=
  [ Stmt.varDecl [{ name := some "am0", ty := some (Ty.uint 128), location := none }]
      (some (castTo 128 (num "1")))
  , Stmt.varDecl [{ name := some "an0", ty := some (Ty.uint 128), location := none }]
      (some (castTo 128 (num "9"))) ]

private def hBody : Stmt := Stmt.block
  (hDecls ++
    [ Stmt.varDecl
        [{ name := some "fp0", ty := some fptTy, location := none }]
        (some (Expr.ident "fpt0"))
    , Stmt.returnValues
        (some (castTo 256
          (Expr.call (Expr.ident "fp0")
            [Arg.positional (castTo 128 (castTo 128 addmodExpr))]))) ])

private def hFn : ContractItem :=
  ContractItem.function
    { kind := FunctionKind.function
      name := some "h"
      visibility := some Visibility.external_
      mutability := StateMutability.pure
      params := []
      returns := [{ name := none, ty := Ty.uint 256, location := none }]
      virtual := false
      override? := none
      modifiers := []
      body := some hBody }

-- DIAGNOSTIC j(): plainest shape `return addmod(uint256(am0 + an0), 1, 7)`.
private def jBody : Stmt := Stmt.block
  (decls ++ [ Stmt.returnValues (some addmodExpr) ])
private def jFn : ContractItem :=
  ContractItem.function
    { kind := FunctionKind.function, name := some "j"
      visibility := some Visibility.external_, mutability := StateMutability.pure
      params := [], returns := [{ name := none, ty := Ty.uint 256, location := none }]
      virtual := false, override? := none, modifiers := []
      body := some jBody }

-- DIAGNOSTIC k(): baseline #31 shape `return uint256(am0 + an0)` (already panics).
private def kBody : Stmt := Stmt.block
  (decls ++ [ Stmt.returnValues (some (castTo 256 narrowAdd)) ])
private def kFn : ContractItem :=
  ContractItem.function
    { kind := FunctionKind.function, name := some "k"
      visibility := some Visibility.external_, mutability := StateMutability.pure
      params := [], returns := [{ name := none, ty := Ty.uint 256, location := none }]
      virtual := false, override? := none, modifiers := []
      body := some kBody }

-- DIAGNOSTIC m(): bare-add addmod `return addmod(am0 + an0, 1, 7)` (no wide cast).
private def mBody : Stmt := Stmt.block
  (decls ++ [ Stmt.returnValues (some (Expr.call (Expr.ident "addmod")
    [ Arg.positional narrowAdd, Arg.positional (num "1"), Arg.positional (num "7") ])) ])
private def mFn : ContractItem :=
  ContractItem.function
    { kind := FunctionKind.function, name := some "m"
      visibility := some Visibility.external_, mutability := StateMutability.pure
      params := [], returns := [{ name := none, ty := Ty.uint 256, location := none }]
      virtual := false, override? := none, modifiers := []
      body := some mBody }

def runContract : ContractDecl :=
{ kind := ContractKind.contract
  name := "T"
  abstract := false
  bases := []
  items := [fpt0Fn, fFn, gFn, hFn, jFn, kFn, mFn] }

def runSourceUnit : SourceUnit :=
  { items := [SourceItem.pragma "solidity" "^0.8.35", SourceItem.contract runContract] }

def accepted : Bool :=
  TypeCheck.Result.isOk (TypeCheck.TypecheckedInput.checkedSourceUnit runSourceUnit)

-- f(): overflowing narrow add through the fp0 call arg -> Panic(0x11) (was 6).
def f_panics : Except TypeError Bool :=
  Examples.checkedOwnCallPanicMatches 256 runContract "f" State.empty [] 17

-- g(): same overflow WITHOUT the fnptr call -> Panic(0x11) (already correct).
def g_panics : Except TypeError Bool :=
  Examples.checkedOwnCallPanicMatches 256 runContract "g" State.empty [] 17

-- h(): safe inputs through the fp0 call arg -> addmod(10,1,7) = 4, no panic.
def h_is_4 : Except TypeError Bool :=
  Examples.checkedOwnCallWordMatches 256 runContract "h" State.empty [] 4

-- j(): the MINIMAL trigger `return addmod(uint256(am0 + an0), 1, 7)` — the wide
-- cast over narrow arithmetic as an addmod arg. -> Panic(0x11) (was 6).
def j_panics : Except TypeError Bool :=
  Examples.checkedOwnCallPanicMatches 256 runContract "j" State.empty [] 17

-- k(): baseline #31 `return uint256(am0 + an0)` — already panicked (sanity check
-- that this fix leaves the direct wide-cast-return path intact).
def k_panics : Except TypeError Bool :=
  Examples.checkedOwnCallPanicMatches 256 runContract "k" State.empty [] 17

-- m(): bare-add addmod `return addmod(am0 + an0, 1, 7)` — the WS1 baseline
-- (narrow add directly, no wide cast); panics before and after this fix.
def m_panics : Except TypeError Bool :=
  Examples.checkedOwnCallPanicMatches 256 runContract "m" State.empty [] 17

private def isOkTrue : Except TypeError Bool -> Bool
  | Except.ok true => true
  | _ => false

#guard accepted
#guard isOkTrue f_panics   -- exact submission shape (overflow through the fp0 arg)
#guard isOkTrue g_panics   -- same overflow WITHOUT the fnptr (isolates the trigger)
#guard isOkTrue j_panics   -- minimal: addmod(uint256(a+b), …) wide-cast arg
#guard isOkTrue k_panics   -- #31 baseline still panics
#guard isOkTrue m_panics   -- WS1 bare-add baseline still panics
#guard isOkTrue h_is_4     -- safe inputs through the fp0 arg -> 4, no panic

end NarrowAddmodFnptrPanic
end Witness
end Solidity
end SolidCore

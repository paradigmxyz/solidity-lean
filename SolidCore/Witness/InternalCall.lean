/-
Stage-1 witnesses for the function-boundary refactor
(`docs/function-boundary-refactor-plan.md` §6 stage 1).

These pin the behaviour of the new `Stmt.internalCall` node + `FunctionTable` +
the in-monad `internalCall` evaluator arm, using HAND-BUILT core tables (not the
frozen corpus — elaboration does not emit the node until stage 2). Each `#guard`
fails the build if the behaviour regresses. They cover, per the plan:

  * direct recursion via a hand-built table (representable now; the acceptance
    gap the refactor closes);
  * frame isolation — a callee cannot read the caller's locals (R7), and the
    caller's locals survive a call;
  * state sharing — a callee's storage write is visible to the caller;
  * `broke` in a callee maps to `reverted typeMismatch` (R3; a callee cannot
    break the caller's loop);
  * `selfdestruct` in a callee propagates (halts the frame);
  * the recursion depth is bounded by the ordinary statement fuel, exhaustion
    reflecting as `outOfFuel` (R2).
-/
import SolidCore.Solidity.Interpreter

namespace SolidCore.Solidity.Source
namespace InternalCallWitness

/-- Fold a hand-built top-level statement under an empty world. -/
def foldTop (fuel : Nat) (table : FunctionTable) (context : Context)
    (state : State) (stmt : Stmt) : Except SolidityFailure Result :=
  SolI.run context
    (Stmt.eval fuel table context (Runtime.ofState state) stmt)

def runTop (fuel : Nat) (table : FunctionTable) (stmt : Stmt) : Option Result :=
  (foldTop fuel table Context.empty State.empty stmt).toOption

def returnedWordEq (expected : Word) : Option Result -> Bool
  | some (Result.returned _ [Value.word w]) => wordEq w expected
  | _ => false

-- `RevertData.typeMismatch` is `RevertData.panic 0` (a def, and `RevertData`
-- has no `BEq`), so match the constructor and compare the code.
def isRevertTypeMismatch : Option Result -> Bool
  | some (Result.reverted _ (RevertData.panic w)) => wordEq w 0
  | _ => false

def isReverted : Option Result -> Bool
  | some (Result.reverted _ _) => true
  | _ => false

def isSelfdestructed : Option Result -> Bool
  | some (Result.selfdestructed _) => true
  | _ => false

def isOutOfFuel : Except SolidityFailure Result -> Bool
  | .error SolidityFailure.outOfFuel => true
  | _ => false

def uintB (name : String) : BindingDecl := { name := name, ty := Ty.uint256 }

/-! ### Direct recursion: `factorial(5) = 120` -/

def factorialFn : InternalFunction :=
  { name := "factorial"
    params := [uintB "n"]
    returns := [uintB "out"]
    body :=
      Stmt.ifElse
        (Expr.binary BinaryOp.le (Expr.var "n") (Expr.word 1))
        (Stmt.returnValues [Expr.word 1])
        (Stmt.block
          [ Stmt.varDecl Ty.uint256 "t" none
          , Stmt.internalCall ["t"] "factorial"
              [Expr.binary BinaryOp.sub (Expr.var "n") (Expr.word 1)]
          , Stmt.returnValues
              [Expr.binary BinaryOp.mul (Expr.var "n") (Expr.var "t")] ]) }

def factorialTable : FunctionTable := [factorialFn]

def callFactorial (n : Word) : Stmt :=
  Stmt.block
    [ Stmt.varDecl Ty.uint256 "r" none
    , Stmt.internalCall ["r"] "factorial" [Expr.word n]
    , Stmt.returnValues [Expr.var "r"] ]

#guard returnedWordEq 120 (runTop 64 factorialTable (callFactorial 5))
#guard returnedWordEq 1 (runTop 64 factorialTable (callFactorial 1))
#guard returnedWordEq 6 (runTop 64 factorialTable (callFactorial 3))

/-! ### Frame isolation (R7): a callee cannot see the caller's locals -/

-- `leak` reads `secret`, which it never declared; only the caller has it.
def leakFn : InternalFunction :=
  { name := "leak", params := [], returns := [uintB "out"]
    body := Stmt.returnValues [Expr.var "secret"] }

def callLeak : Stmt :=
  Stmt.block
    [ Stmt.varDecl Ty.uint256 "secret" (some (Expr.word 99))
    , Stmt.varDecl Ty.uint256 "r" none
    , Stmt.internalCall ["r"] "leak" []
    , Stmt.returnValues [Expr.var "r"] ]

-- With locals REPLACED (not pushScope), `secret` is unbound in the callee, so
-- the read reverts instead of resolving to 99. This is the isolation
-- discriminator: a pushScope leak would return 99.
#guard isReverted (runTop 16 [leakFn] callLeak)

-- The caller's own locals survive a benign call unchanged.
def benignFn : InternalFunction :=
  { name := "benign", params := [], returns := [uintB "out"]
    body := Stmt.block
      [ Stmt.varDecl Ty.uint256 "secret" (some (Expr.word 7))
      , Stmt.returnValues [Expr.var "secret"] ] }

def callBenignKeepCaller : Stmt :=
  Stmt.block
    [ Stmt.varDecl Ty.uint256 "secret" (some (Expr.word 99))
    , Stmt.varDecl Ty.uint256 "r" none
    , Stmt.internalCall ["r"] "benign" []
    , Stmt.returnValues [Expr.var "secret"] ]

-- Returns the CALLER's `secret` (99), proving the callee's `secret := 7` did not
-- leak into and overwrite the restored caller frame; and `r` captured 7.
#guard returnedWordEq 99 (runTop 16 [benignFn] callBenignKeepCaller)

def callBenignCaptured : Stmt :=
  Stmt.block
    [ Stmt.varDecl Ty.uint256 "secret" (some (Expr.word 99))
    , Stmt.varDecl Ty.uint256 "r" none
    , Stmt.internalCall ["r"] "benign" []
    , Stmt.returnValues [Expr.var "r"] ]

#guard returnedWordEq 7 (runTop 16 [benignFn] callBenignCaptured)

/-! ### State sharing: a callee's storage write is visible to the caller -/

def storageContext : Context :=
  { Context.empty with storageFields := [{ name := "x", slot := 0 }] }

def storeFn : InternalFunction :=
  { name := "store", params := [], returns := []
    body := Stmt.assign (LValue.storage "x") (Expr.word 42) }

def callStore : Stmt :=
  Stmt.block
    [ Stmt.internalCall [] "store" []
    , Stmt.returnValues [Expr.storage "x"] ]

-- State (storage) is shared, not isolated: the caller reads back 42.
#guard
  (match (foldTop 16 [storeFn] storageContext State.empty callStore).toOption with
   | some (Result.returned _ [Value.word w]) => wordEq w 42
   | _ => false)

/-! ### `broke` in a callee -> `reverted typeMismatch` (R3) -/

def breakFn : InternalFunction :=
  { name := "brk", params := [], returns := []
    body := Stmt.break }

def callBreak : Stmt :=
  Stmt.block
    [ Stmt.internalCall [] "brk" []
    , Stmt.returnValues [Expr.word 1] ]

#guard isRevertTypeMismatch (runTop 16 [breakFn] callBreak)

/-! ### `selfdestruct` in a callee propagates (halts the frame) -/

def sdFn : InternalFunction :=
  { name := "sd", params := [], returns := []
    body := Stmt.selfdestruct (Expr.word 0xbeef) }

def callSd : Stmt :=
  Stmt.block
    [ Stmt.internalCall [] "sd" []
    , Stmt.returnValues [Expr.word 1] ]

#guard isSelfdestructed (runTop 16 [sdFn] callSd)

/-! ### Fuel bound (R2): deep recursion exhausts statement fuel -> `outOfFuel` -/

-- Same call, generous vs insufficient fuel: value at 64, `outOfFuel` at 3.
#guard returnedWordEq 120 (runTop 64 factorialTable (callFactorial 5))
#guard isOutOfFuel (foldTop 3 factorialTable Context.empty State.empty (callFactorial 5))
#guard (runTop 3 factorialTable (callFactorial 5)).isNone

/-! ### Reference-signature callees (function-boundary refactor, ref extension)

These pin the interpreter groundwork that lets storage/memory-reference
parameters and returns cross the internal-function boundary as pointer VALUES:
reference-preserving argument evaluation (`evalRefArg`),
reference-preserving parameter binding (`bindArgsRef?`), reference-preserving
return collection (`collectReturnBindingsRef`), and reference-aware return
assignment (`assignNamedValuesRef?`). -/

def storageRefContext : Context :=
  { Context.empty with
    storageFields :=
      [ { name := "x", slot := 0, ty? := some Ty.uint256 }
      , { name := "y", slot := 1, ty? := some Ty.uint256 } ] }

-- Callee takes a `T storage` parameter `_arg0` and reads THROUGH it. Under
-- reference-preserving binding, `_arg0` holds the caller's storage pointer, so
-- `Expr.var "_arg0"` loads the caller's slot.
def readThroughFn : InternalFunction :=
  { name := "readThrough", params := [uintB "_arg0"], returns := [uintB "out"]
    body := Stmt.returnValues [Expr.var "_arg0"] }

-- Caller: set storage x := 7, alias local `p` to x, pass `p` by reference.
def callReadThrough : Stmt :=
  Stmt.block
    [ Stmt.assign (LValue.storage "x") (Expr.word 7)
    , Stmt.storageAlias "p" "x"
    , Stmt.varDecl Ty.uint256 "r" none
    , Stmt.internalCall ["r"] "readThrough" [Expr.var "p"]
    , Stmt.returnValues [Expr.var "r"] ]

#guard
  (match (foldTop 16 [readThroughFn] storageRefContext State.empty
      callReadThrough).toOption with
   | some (Result.returned _ [Value.word w]) => wordEq w 7
   | _ => false)

-- A callee whose `_arg0` is passed a plain (non-reference) value still binds and
-- reads by value — the ref-preserving path is inert for value arguments.
def callReadThroughByValue : Stmt :=
  Stmt.block
    [ Stmt.varDecl Ty.uint256 "r" none
    , Stmt.internalCall ["r"] "readThrough" [Expr.word 55]
    , Stmt.returnValues [Expr.var "r"] ]

#guard returnedWordEq 55 (runTop 16 [readThroughFn] callReadThroughByValue)

-- Callee RETURNS a `T storage` pointer: it re-points its named storage return
-- `out` at slot `x`. `collectReturnBindingsRef` preserves the pointer and
-- `assignNamedValuesRef?` re-points the caller's alias target `r`.
def pickStorageFn : InternalFunction :=
  { name := "pickStorage", params := [], returns := [uintB "out"]
    body := Stmt.storageAlias "out" "x" }

-- Caller aliases `r` to y (value 5) first; after the call `r` must point at x
-- (value 7), proving the returned pointer flowed, not the initial aliasing.
def callPickStorage : Stmt :=
  Stmt.block
    [ Stmt.assign (LValue.storage "x") (Expr.word 7)
    , Stmt.assign (LValue.storage "y") (Expr.word 5)
    , Stmt.storageAlias "r" "y"
    , Stmt.internalCall ["r"] "pickStorage" []
    , Stmt.returnValues [Expr.var "r"] ]

#guard
  (match (foldTop 16 [pickStorageFn] storageRefContext State.empty
      callPickStorage).toOption with
   | some (Result.returned _ [Value.word w]) => wordEq w 7
   | _ => false)

-- Stage A (storage-ref RETURN via named return + frame binding): the callee's
-- named return is declared `isStorageRef := true`, so the frame binds it to a
-- storage POINTER (initially the reserved uninitialized target); the body
-- re-points it via `storageAliasAssign` from inside a nested block (proving the
-- assignment lands in the FRAME binding and survives the block's scope pop, the
-- failure mode of a declaration-based prologue), and the caller's alias temp is
-- re-pointed to the returned slot.
def namedStorageReturnFn : InternalFunction :=
  { name := "namedPick"
    params := []
    returns := [{ name := "out", ty := Ty.uint256, isStorageRef := true }]
    body := Stmt.block [Stmt.block [Stmt.storageAliasAssign "out" "x"]] }

def callNamedStorageReturn : Stmt :=
  Stmt.block
    [ Stmt.assign (LValue.storage "x") (Expr.word 13)
    , Stmt.assign (LValue.storage "y") (Expr.word 5)
    , Stmt.storageAlias "r" "y"
    , Stmt.internalCall ["r"] "namedPick" []
    , Stmt.returnValues [Expr.var "r"] ]

#guard
  (match (foldTop 16 [namedStorageReturnFn] storageRefContext State.empty
      callNamedStorageReturn).toOption with
   | some (Result.returned _ [Value.word w]) => wordEq w 13
   | _ => false)

/-! ### Stage C: internal function pointers (dispatch IDs)

Pins the `Stmt.internalCallPtr` arm + `Value.internalFunction` + the 64-bit
storage-read mask against solc via-IR's model
(`docs/refs-completion-solc-research.md` §2): a pointer is a small numeric ID,
call-through dispatches by ID, a miss (incl. the uninitialized 0) panics 0x51,
and a dirty storage word is masked to 64 bits at read with validity checked
only at call time. -/

def isPanic51 : Option Result -> Bool
  | some (Result.reverted _ (RevertData.panic w)) => wordEq w 0x51
  | _ => false

def dblFn : InternalFunction :=
  { name := "dbl", params := [uintB "x"], returns := [uintB "out"]
    body := Stmt.returnValues
      [Expr.binary BinaryOp.mul (Expr.var "x") (Expr.word 2)]
    id? := some 1 }

def tripFn : InternalFunction :=
  { name := "trip", params := [uintB "x"], returns := [uintB "out"]
    body := Stmt.returnValues
      [Expr.binary BinaryOp.mul (Expr.var "x") (Expr.word 3)]
    id? := some 2 }

def ptrTable : FunctionTable := [dblFn, tripFn]

def callPtr (id : Word) : Stmt :=
  Stmt.block
    [ Stmt.varDecl Ty.uint256 "r" none
    , Stmt.internalCallPtr ["r"] (Expr.internalFunction id) [Expr.word 21]
    , Stmt.returnValues [Expr.var "r"] ]

-- Dispatch by ID: 1 -> dbl (42), 2 -> trip (63).
#guard returnedWordEq 42 (runTop 16 ptrTable (callPtr 1))
#guard returnedWordEq 63 (runTop 16 ptrTable (callPtr 2))

-- Uninitialized pointer (ID 0) and unknown IDs panic 0x51 (dispatch default).
#guard isPanic51 (runTop 16 ptrTable (callPtr 0))
#guard isPanic51 (runTop 16 ptrTable (callPtr 7))

-- A pointer stored as a LOCAL value flows and dispatches.
def callPtrViaLocal : Stmt :=
  Stmt.block
    [ Stmt.varDecl Ty.internalFunction "fp"
        (some (Expr.internalFunction 2))
    , Stmt.varDecl Ty.uint256 "r" none
    , Stmt.internalCallPtr ["r"] (Expr.var "fp") [Expr.word 21]
    , Stmt.returnValues [Expr.var "r"] ]

#guard returnedWordEq 63 (runTop 16 ptrTable callPtrViaLocal)

-- Storage round-trip with a DIRTY word: the fn-pointer storage read masks to
-- 64 bits (no validity check at read); the masked ID then dispatches at call
-- time. Planted word = 2^64 * 5 + 2 -> masked ID 2 -> trip -> 63.
def fnPtrStorageContext : Context :=
  { Context.empty with
    storageFields := [{ name := "fp", slot := 0, ty? := some Ty.internalFunction }] }

def dirtyFnPtrState : State :=
  State.empty.storeSlot 0 (2 ^ 64 * 5 + 2)

def callPtrFromStorage : Stmt :=
  Stmt.block
    [ Stmt.varDecl Ty.uint256 "r" none
    , Stmt.internalCallPtr ["r"] (Expr.storage "fp") [Expr.word 21]
    , Stmt.returnValues [Expr.var "r"] ]

#guard
  (match (foldTop 16 ptrTable fnPtrStorageContext dirtyFnPtrState
      callPtrFromStorage).toOption with
   | some (Result.returned _ [Value.word w]) => wordEq w 63
   | _ => false)

-- A dirty word whose MASKED ID has no dispatch entry panics 0x51 at call time.
def dirtyMissState : State :=
  State.empty.storeSlot 0 (2 ^ 64 * 5 + 9)

#guard
  (match (foldTop 16 ptrTable fnPtrStorageContext dirtyMissState
      callPtrFromStorage).toOption with
   | some (Result.reverted _ (RevertData.panic w)) => wordEq w 0x51
   | _ => false)

-- Recursion THROUGH a pointer is bounded by the same statement fuel.
def factorialPtrFn : InternalFunction :=
  { name := "factorialPtr", params := [uintB "n"], returns := [uintB "out"]
    body :=
      Stmt.ifElse
        (Expr.binary BinaryOp.le (Expr.var "n") (Expr.word 1))
        (Stmt.returnValues [Expr.word 1])
        (Stmt.block
          [ Stmt.varDecl Ty.uint256 "t" none
          , Stmt.internalCallPtr ["t"] (Expr.internalFunction 1)
              [Expr.binary BinaryOp.sub (Expr.var "n") (Expr.word 1)]
          , Stmt.returnValues
              [Expr.binary BinaryOp.mul (Expr.var "n") (Expr.var "t")] ])
    id? := some 1 }

def callFactorialPtr (n : Word) : Stmt :=
  Stmt.block
    [ Stmt.varDecl Ty.uint256 "r" none
    , Stmt.internalCallPtr ["r"] (Expr.internalFunction 1) [Expr.word n]
    , Stmt.returnValues [Expr.var "r"] ]

#guard returnedWordEq 120 (runTop 64 [factorialPtrFn] (callFactorialPtr 5))
#guard isOutOfFuel
  (foldTop 3 [factorialPtrFn] Context.empty State.empty (callFactorialPtr 5))

/-! ### Missing callee -> defensive revert (total interpreter) -/

def callMissing : Stmt :=
  Stmt.block
    [ Stmt.varDecl Ty.uint256 "r" none
    , Stmt.internalCall ["r"] "doesNotExist" []
    , Stmt.returnValues [Expr.var "r"] ]

#guard isRevertTypeMismatch (runTop 16 [] callMissing)

end InternalCallWitness
end SolidCore.Solidity.Source

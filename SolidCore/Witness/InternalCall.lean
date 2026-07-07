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

/-! ### Missing callee -> defensive revert (total interpreter) -/

def callMissing : Stmt :=
  Stmt.block
    [ Stmt.varDecl Ty.uint256 "r" none
    , Stmt.internalCall ["r"] "doesNotExist" []
    , Stmt.returnValues [Expr.var "r"] ]

#guard isRevertTypeMismatch (runTop 16 [] callMissing)

end InternalCallWitness
end SolidCore.Solidity.Source

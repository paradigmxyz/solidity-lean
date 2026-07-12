/-
Witnesses for #186 EXTERNAL-SELF-CALL: closed-world self-dispatch of a call to
`address(this)`.

An external call to the executing contract's OWN address is closed-world — the
model has the contract's code — so it must NOT emit an open-world `Query.external`
to a responder; it must route the call through the contract's own external
dispatcher (`Contract.callCalldataAtFromWithContext?`) against the LIVE state, in
a proper sub-frame (`msg.sender := address(this)`, `msg.value` per options, storage
threaded, revert propagated per call semantics). The capability is a
`SelfDispatchFn` installed on the entry `Context` by the closed-world call entries
(`Contract.callSelfDispatch?` etc.) and consulted at the interpreter's
external-call emit sites when `target == context.self`.

These `#guard`s pin, against the real-EVM ground truth (deployed and checked with
pinned solc 0.8.35 + Forge; see `tests/forge-harness/external-self-call`):

  * value read: `this.getX()` returns storage `x` (5);
  * state mutation persists: `this.inc()` writes and the write survives (counter
    1, then 2);
  * `msg.sender` identity: inside the self-called fn `msg.sender == address(this)`;
  * revert routing: a reverting self-call routes to `try/catch` (42) and, via a
    low-level `(bool,bytes)` self-call, yields `success = false`;
  * a plain (non-try) reverting self-call PROPAGATES;
  * constructor guard: `this.f()` while under construction reverts empty
    (`extcodesize(this) == 0`) — deploy reverts;
  * opt-in: WITHOUT the hook a self-call still fails closed (open-world path
    unchanged — the control for the responder-scripted self-call witnesses);
  * bounded nested self-dispatch (mutual self-calls terminate; a zero-budget hook
    resolves to `none`);
  * control: a DIRECT own-call of the callee is unchanged.
-/
import SolidCore.Solidity.ABI

namespace SolidCore.Solidity.Source
namespace ExternalSelfCallWitness

open SolidCore.Solidity.Source.ABI

def uintB (name : String) : BindingDecl := { name := name, ty := Ty.uint256 }
def boolB (name : String) : BindingDecl := { name := name, ty := Ty.bool }

/-- Calldata for a zero-argument external function: just its 4-byte selector. -/
def sel (signature : String) : Expr :=
  Expr.byteArray (encodeSelector (selectorFromSignature signature))

/-- A high-level self-call `this.f()` returning one `uint`: a `tryExternalCall`
    to `Expr.self` (checkTargetCode = false, since it has a return value). -/
def selfCallUint (signature : String) (kind : LowLevelCallKind)
    (catchClauses : List TryCatchClause) : Stmt :=
  Stmt.tryExternalCall kind Expr.self (sel signature) (Expr.word 0) none false
    false [uintB "v"] [] (Stmt.returnValues [Expr.var "v"]) catchClauses

def getXFn : FunctionDef :=
  { name := "getX", selector? := some (selectorFromSignature "getX()")
    params := [], returns := [uintB "out"]
    body := Stmt.returnValues [Expr.storage "x"] }

def incFn : FunctionDef :=
  { name := "inc", selector? := some (selectorFromSignature "inc()")
    params := [], returns := [uintB "out"]
    body := Stmt.block
      [ Stmt.assign (LValue.storage "counter")
          (Expr.binary BinaryOp.add (Expr.storage "counter") (Expr.word 1))
      , Stmt.returnValues [Expr.storage "counter"] ] }

def whoamiFn : FunctionDef :=
  { name := "whoami", selector? := some (selectorFromSignature "whoami()")
    params := [], returns := [boolB "out"]
    body := Stmt.returnValues [Expr.binary BinaryOp.eq Expr.caller Expr.self] }

def boomFn : FunctionDef :=
  { name := "boom", selector? := some (selectorFromSignature "boom()")
    params := [], returns := [uintB "out"]
    body := Stmt.revertError (some "nope") }

def hFn : FunctionDef :=
  { name := "h", selector? := some (selectorFromSignature "h()")
    params := [], returns := [uintB "out"]
    body := selfCallUint "getX()" LowLevelCallKind.staticcall [] }

def doIncFn : FunctionDef :=
  { name := "doInc", selector? := some (selectorFromSignature "doInc()")
    params := [], returns := [uintB "out"]
    body := selfCallUint "inc()" LowLevelCallKind.call [] }

def senderCheckFn : FunctionDef :=
  { name := "senderCheck", selector? := some (selectorFromSignature "senderCheck()")
    params := [], returns := [boolB "out"]
    body := Stmt.tryExternalCall LowLevelCallKind.staticcall Expr.self
      (sel "whoami()") (Expr.word 0) none false false [boolB "v"] []
      (Stmt.returnValues [Expr.var "v"]) [] }

/-- `try this.boom() returns (uint v) { return v; } catch { return 42; }`. -/
def tryCatchFn : FunctionDef :=
  { name := "tryCatchBoom", selector? := some (selectorFromSignature "tryCatchBoom()")
    params := [], returns := [uintB "out"]
    body := selfCallUint "boom()" LowLevelCallKind.staticcall
      [TryCatchClause.clause none [] (Stmt.returnValues [Expr.word 42])] }

/-- A PLAIN (non-try) self-call to a reverting fn: no catch clause, so the revert
    propagates out of the caller. -/
def propBoomFn : FunctionDef :=
  { name := "propBoom", selector? := some (selectorFromSignature "propBoom()")
    params := [], returns := [uintB "out"]
    body := selfCallUint "boom()" LowLevelCallKind.staticcall [] }

/-- A low-level `(bool ok, ) = address(this).call(boom())` — the tuple's `ok`
    is `false` on a reverting self-call. -/
def lowLevelBoomFn : FunctionDef :=
  { name := "lowLevelBoom", selector? := some (selectorFromSignature "lowLevelBoom()")
    params := [], returns := [boolB "out"]
    body := Stmt.block
      [ Stmt.varDecl Ty.bool "ok" none
      , Stmt.assignTuple [some (LValue.var "ok"), none]
          (Expr.lowLevelCall LowLevelCallKind.call Expr.self (sel "boom()")
            (Expr.word 0) none false)
      , Stmt.returnValues [Expr.var "ok"] ] }

/-- Mutual/nested self-dispatch: `a()` self-calls `b()`, `b()` returns 7. -/
def bFn : FunctionDef :=
  { name := "b", selector? := some (selectorFromSignature "b()")
    params := [], returns := [uintB "out"]
    body := Stmt.returnValues [Expr.word 7] }

def aFn : FunctionDef :=
  { name := "a", selector? := some (selectorFromSignature "a()")
    params := [], returns := [uintB "out"]
    body := selfCallUint "b()" LowLevelCallKind.staticcall [] }

def selfCallContract : Contract :=
  { storageFields :=
      [ { name := "x", slot := 0 }, { name := "counter", slot := 1 } ]
    functions :=
      [ getXFn, incFn, whoamiFn, boomFn, hFn, doIncFn, senderCheckFn, tryCatchFn
      , propBoomFn, lowLevelBoomFn, aFn, bFn ] }

/-- Closed-world own-call WITH the self-dispatch hook installed. -/
def runCall (name : String) (state : State) : Option CallResult :=
  Contract.callSelfDispatch? 1000 selfCallContract (CallTarget.name name) state []

def returnedWord : Option CallResult -> Option Word
  | some (CallResult.returned _ [Value.word w]) => some w
  | _ => none

def returnedState : Option CallResult -> Option State
  | some (CallResult.returned state _) => some state
  | _ => none

def isRevertedEmpty : Option CallResult -> Bool
  | some (CallResult.reverted _ RevertData.empty) => true
  | _ => false

def isRevertedError : String -> Option CallResult -> Bool
  | msg, some (CallResult.reverted _ (RevertData.error m)) => m == msg
  | _, _ => false

/-! ### Value read: `this.getX()` returns storage `x` -/

def stateX5 : State := State.empty.storeSlot 0 5

-- Control: a DIRECT own-call of the callee returns storage `x`.
#guard returnedWord (runCall "getX" stateX5) == some 5
-- The self-call routes through the dispatcher and returns the same 5.
#guard returnedWord (runCall "h" stateX5) == some 5
-- With `x` unset (fresh state) it is 0 — the read is against LIVE storage.
#guard returnedWord (runCall "h" State.empty) == some 0

/-! ### State mutation persists across the self-call boundary -/

-- `this.inc()` returns 1 and the write to slot 1 (counter) survives.
#guard returnedWord (runCall "doInc" State.empty) == some 1
#guard
  (match returnedState (runCall "doInc" State.empty) with
   | some state => state.loadSlot 1 == 1
   | none => false)
-- Threading the mutated state, a second `this.inc()` yields 2.
#guard
  (match returnedState (runCall "doInc" State.empty) with
   | some state => returnedWord (runCall "doInc" state) == some 2
   | none => false)

/-! ### `msg.sender` identity: inside the self-call `msg.sender == address(this)` -/

#guard returnedWord (runCall "senderCheck" State.empty) == some (boolWord true)

/-! ### Revert routing -/

-- A reverting self-call wrapped in try/catch routes to the catch branch (42).
#guard returnedWord (runCall "tryCatchBoom" State.empty) == some 42
-- A PLAIN reverting self-call propagates the callee's revert to the caller as
-- the bubbled returndata: the ABI encoding of `Error("nope")` (selector
-- 0x08c379a0). This is the raw-bytes bubble a real CALL performs, matching EVM.
#guard
  (match runCall "propBoom" State.empty with
   | some (CallResult.reverted _ (RevertData.raw bytes)) =>
       bytes.take 4 == [8, 195, 121, 160] &&        -- Error(string) selector
         bytes.length == 100 &&                      -- 4 + 3*32
         (bytes.drop 68).take 4 == [110, 111, 112, 101]  -- "nope"
   | _ => false)
-- A low-level `(bool,) = address(this).call(boom())` yields `false`.
#guard returnedWord (runCall "lowLevelBoom" State.empty) == some (boolWord false)

/-! ### Opt-in: WITHOUT the hook a self-call still fails CLOSED (control for the
    open-world/responder self-call witnesses — behaviour there is unchanged). -/

-- `Contract.call?` installs NO self-dispatch hook and folds under the empty
-- responder, so the self-call's `Query.external` is unmatched -> `none`.
#guard (Contract.call? 1000 selfCallContract (CallTarget.name "h") stateX5 []).isNone
-- The identical target under the self-dispatch entry succeeds — the hook is
-- exactly what turns the open-world miss into a closed-world dispatch.
#guard returnedWord (runCall "h" stateX5) == some 5

/-! ### Bounded nested self-dispatch (mutual self-calls terminate) -/

-- `a()` self-calls `b()` (a second dispatch level); with ample budget it returns.
#guard returnedWord (runCall "a" State.empty) == some 7
-- A zero-budget hook resolves to `none` (fail-closed) — the nesting bound.
#guard (selfDispatchHook 0 selfCallContract 0 0 0
  (encodeSelector (selectorFromSignature "b()")) State.empty).isNone

/-! ### Constructor guard: `this.f()` under construction reverts empty
    (`extcodesize(this) == 0`) — deploy reverts. -/

def ctorContext : Context :=
  { selfCallContract.context with
    construction := true
    selfDispatch? := some (selfDispatchHook 1000 selfCallContract 0) }

#guard
  (match FunctionDef.call 1000 selfCallContract.table ctorContext hFn stateX5 [] with
   | some tree =>
       match SolI.runWith [] tree with
       | .ok result => isRevertedEmpty (some result)
       | .error _ => false
   | none => false)

-- Outside construction the same call self-dispatches and returns 5 (the guard is
-- construction-specific, not a blanket self-call block).
def liveContext : Context :=
  { selfCallContract.context with
    selfDispatch? := some (selfDispatchHook 1000 selfCallContract 0) }

#guard
  (match FunctionDef.call 1000 selfCallContract.table liveContext hFn stateX5 [] with
   | some tree =>
       match SolI.runWith [] tree with
       | .ok result => returnedWord (some result) == some 5
       | .error _ => false
   | none => false)

end ExternalSelfCallWitness
end SolidCore.Solidity.Source

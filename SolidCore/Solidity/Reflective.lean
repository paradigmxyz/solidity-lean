import SolidCore.Solidity.Checked

/-!
# Closed-world reflective responder (multi-contract execution)

The v2 seam documented in `contest/multi_contract.py`: instead of answering an external
call from a scripted row, *run the callee* in the same semantics. The world is an
`OpenWorld` (all accounts' storage and balances) plus a registry saying, for every
address that can be called, whether it is

* `code c`  — a Solidity contract executed here (its storage lives in the world);
* `actor s` — a scripted actor (the attacker side of a replay, which uses Foundry
  cheatcodes and is not executed): on its k-th invocation it performs its recorded
  child calls *through this responder* and returns its recorded output;
* `eoa`     — an externally owned account: value transfers succeed, no code runs.

Any other address fails closed. A call moves value in the world, adopts the world into
the callee (`adoptWorld`), runs the callee's call tree under this same responder one
level deeper, and snapshots the callee back into the world (`snapshotWorld`). The
round-trip law `snapshotWorld (adoptWorld w ..) = w` (`AdoptionLaws.lean`) is what makes
this composition faithful, including reentrancy: the snapshot a callee receives carries
the caller's own storage as of the call.

Out of scope (fail closed): contract creation, `gasleft`-dependent behaviour (resource
queries get the canonical default), static-call write protection (not enforced).
Everything is `partial`: this is an executable model, not (yet) a proved one.
-/

namespace SolidCore.Solidity.Source.Reflective

open SolidCore.Solidity.Source
open EvmCompiler.Simulation

/-- One recorded invocation of an actor: the calls it made, in order, and what it
    returned to its caller. -/
structure ActorInvocation where
  calls : List (Word × Word × List Nat)  -- target, value, calldata
  success : Bool := true
  output : List Nat := []
  deriving Repr, Inhabited

inductive Member where
  | code (contract : Contract)
  | actor (script : List ActorInvocation)
  | eoa
  deriving Inhabited

structure Registry where
  members : List (Word × Member)
  blockEnv : BlockEnv
  txEnv : TxEnv
  fuel : Nat := 4096

/-- Per-actor invocation cursors, threaded through the whole run. -/
abbrev Cursors := List (Word × Nat)

def Cursors.next (cs : Cursors) (a : Word) : Nat × Cursors :=
  let n := ((cs.find? (·.1 == a)).map (·.2)).getD 0
  (n, (a, n + 1) :: cs.filter (·.1 != a))

def Registry.find? (reg : Registry) (a : Word) : Option Member :=
  (reg.members.find? (·.1 == Shared.norm a)).map (·.2)

/-- Move `value` from `src` to `dst` in the world; `none` if `src` cannot pay. -/
def transferValue (world : Shared.OpenWorld) (src dst value : Word) :
    Option Shared.OpenWorld :=
  if value == 0 then some world else
  let sa := wordToAddress src
  let s := (world.accounts.find? sa).getD default
  let sb := u256ToWord s.balance
  if sb < value then none else
  let s' : OpenAccount := { s with balance := wordToU256 (sb - value) }
  let world := { world with accounts := world.accounts.insert sa s' }
  let da := wordToAddress dst
  let d := (world.accounts.find? da).getD default
  let d' : OpenAccount := { d with balance := wordToU256 (u256ToWord d.balance + value) }
  some { world with accounts := world.accounts.insert da d' }

def failed (world : Shared.OpenWorld) (req : CallRequest) : CallResponse :=
  { success := false, returnData := ByteArray.empty, postWorld := world,
    returnedGas := req.requestedGas }

mutual

/-- Fold a call tree, answering every external call reflectively. -/
partial def run {α : Type} (reg : Registry) (depth : Nat) (cs : Cursors) :
    SolI α → Except String (α × Cursors)
  | .done (.ok a) => .ok (a, cs)
  | .done (.error e) => .error ("solidity failure: " ++ reprStr e)
  | .request (.external world (.call req)) k => do
      let (resp, cs) ← answerCall reg depth cs world req
      run reg depth cs (k resp)
  | .request (.external _ (.create _)) _ =>
      .error "contract creation is not supported in the closed world"
  | .request (.resource r) k => run reg depth cs (k (Query.defaultAnswer (.resource r)))

/-- Answer one call request by executing the callee. -/
partial def answerCall (reg : Registry) (depth : Nat) (cs : Cursors)
    (world : Shared.OpenWorld) (req : CallRequest) : Except String (CallResponse × Cursors) := do
  if depth == 0 then return (failed world req, cs)
  if let some resp := precompileAnswerCall? world req then return (resp, cs)
  let caller := addressToWord req.caller
  let self := addressToWord req.recipient
  let target := addressToWord req.codeAddress
  let value := u256ToWord req.transferValue
  let calldata := byteArrayToBytes req.calldata
  let moves := req.kind == .call || req.kind == .callcode
  let some world1 := (if moves then transferValue world caller self value else some world)
    | return (failed world req, cs)
  match reg.find? target with
  | some (.code contract) =>
      let base : Context := { contract.context with blockEnv := reg.blockEnv, txEnv := reg.txEnv }
      let ctx := ABI.Contract.callContextAtWithBase contract base self caller
        (u256ToWord req.apparentValue) calldata
      let st0 := adoptWorld world1 ctx State.empty
      let (r, cs) ← dispatch reg (depth - 1) cs contract base st0 self caller
        (u256ToWord req.apparentValue) calldata
      let post := if r.success then snapshotWorld ctx r.state else world
      return ({ success := r.success, returnData := bytesToByteArray r.output,
                postWorld := post, returnedGas := req.requestedGas }, cs)
  | some (.actor script) =>
      let (n, cs) := cs.next target
      let some inv := script[n]? | .error s!"actor {target} called {n + 1} times, recorded {script.length}"
      let mut w := world1
      let mut cs := cs
      for (t, v, cd) in inv.calls do
        let sub : CallRequest :=
          { kind := .call, requestedGas := req.requestedGas, caller := wordToAddress target,
            recipient := wordToAddress t, codeAddress := wordToAddress t,
            transferValue := wordToU256 v, apparentValue := wordToU256 v,
            calldata := bytesToByteArray cd, permission := true }
        let (resp, cs') ← answerCall reg (depth - 1) cs w sub
        cs := cs'
        if resp.success then w := resp.postWorld
      let post := if inv.success then w else world
      return ({ success := inv.success, returnData := bytesToByteArray inv.output,
                postWorld := post, returnedGas := req.requestedGas }, cs)
  | some .eoa =>
      return ({ success := true, returnData := ByteArray.empty, postWorld := world1,
                returnedGas := req.requestedGas }, cs)
  | none => .error s!"call to unregistered address {target}"

/-- `ABI.Contract.callCalldataAtFromWithContext?`, but folding each function's call
    tree with `run` instead of the empty responder. -/
partial def dispatch (reg : Registry) (depth : Nat) (cs : Cursors) (contract : Contract)
    (base : Context) (state : State) (self sender value : Word) (calldata : List Nat) :
    Except String (ABI.AbiCallResult × Cursors) := do
  let callFn := fun (function : FunctionDef) (args : List Value) (cd : List Nat)
      (encode : List Value → Option (List Nat)) =>
    (do
      let ctx := ABI.Contract.callContextAtWithBase contract base self sender value cd
      if !function.acceptsValue value then
        let some r := ABI.Contract.rejectedValueCall? contract state | .error "encode"
        return (r, cs)
      let some tree := function.call reg.fuel contract.table ctx state args
        | .error "no call tree"
      let (res, cs) ← run reg depth cs tree
      match res with
      | .returned st' values =>
          let some output := encode values | .error "encode returns"
          return ({ success := true, output, state := st' }, cs)
      | .reverted st' revert =>
          let some output := ABI.Contract.encodeRevertData? contract revert | .error "encode revert"
          return ({ success := false, output, state := st' }, cs) : Except String _)
  let fallback : Except String (ABI.AbiCallResult × Cursors) :=
    match ABI.Contract.findFallback? contract with
    | some f =>
        match ABI.FunctionDef.fallbackArgs? f calldata with
        | some args => callFn f args calldata (ABI.FunctionDef.encodeFallbackOutput? f)
        | none => .error "fallback args"
    | none =>
        match ABI.Contract.missingFallbackCall? contract state with
        | some r => .ok (r, cs)
        | none => .error "missing fallback"
  let byFunction := fun (function : FunctionDef) =>
    let enc := ABI.encodeValues? (function.returns.map BindingDecl.ty)
    match ABI.decodeFunctionArgs? function (calldata.drop ABI.selectorBytes) with
    | Except.ok args => callFn function args calldata enc
    | Except.error revert =>
        match ABI.Contract.revertedCall? contract state revert with
        | some r => Except.ok (r, cs)
        | none => Except.error "decode revert"
  let byReceive := fun (f : FunctionDef) =>
    callFn f [] [] (ABI.encodeValues? (f.returns.map BindingDecl.ty))
  match ABI.readSelector? calldata with
  | some selector =>
      match contract.findFunctionBySelector? selector with
      | some function => byFunction function
      | none => fallback
  | none =>
      if calldata.isEmpty then
        match ABI.Contract.findReceive? contract with
        | some f => byReceive f
        | none => fallback
      else fallback

end

/-- Run a sequence of top-level calls (sender, target, value, calldata) from `world0`.
    Returns per-call success and the final world. -/
def runTop (reg : Registry) (world0 : Shared.OpenWorld)
    (calls : List (Word × Word × Word × List Nat)) :
    Except String (List Bool × Shared.OpenWorld) := do
  let mut w := world0
  let mut cs : Cursors := []
  let mut oks := []
  for (sender, target, value, cd) in calls do
    let req : CallRequest :=
      { kind := .call, requestedGas := wordToU256 30000000, caller := wordToAddress sender,
        recipient := wordToAddress target, codeAddress := wordToAddress target,
        transferValue := wordToU256 value, apparentValue := wordToU256 value,
        calldata := bytesToByteArray cd, permission := true }
    let (resp, cs') ← answerCall reg 1024 cs w req
    cs := cs'
    oks := oks ++ [resp.success]
    if resp.success then w := resp.postWorld
  return (oks, w)

/-- Build a world from (address, balance, storage) triples. Accounts the registry runs
    (`code`/`actor`) get a non-empty code marker: Solidity's high-level calls check
    `extcodesize(target) > 0` before calling, and the semantics reads it from the world. -/
def mkWorld (reg : Registry) (accounts : List (Word × Word × List (Word × Word))) :
    Shared.OpenWorld :=
  { accounts := accounts.foldl (fun acc (a, bal, slots) =>
      let hasCode := match reg.find? a with
        | some .eoa => false
        | some _ => true
        | none => false
      let account : OpenAccount :=
        { (default : OpenAccount) with
          balance := wordToU256 bal
          storage := slots.foldl (fun s kv => s.insert (wordToU256 kv.1) (wordToU256 kv.2))
            default
          codeBytes := if hasCode then bytesToByteArray [0xfe] else ByteArray.empty }
      acc.insert (wordToAddress a) account)
      default
    substate := default
    createdAccounts := default }

def loadSlot (world : Shared.OpenWorld) (a slot : Word) : Word :=
  match world.accounts.find? (wordToAddress a) with
  | some acc => u256ToWord ((acc.storage.find? (wordToU256 slot)).getD (wordToU256 0))
  | none => 0

def balanceOf (world : Shared.OpenWorld) (a : Word) : Word :=
  match world.accounts.find? (wordToAddress a) with
  | some acc => u256ToWord acc.balance
  | none => 0

end SolidCore.Solidity.Source.Reflective

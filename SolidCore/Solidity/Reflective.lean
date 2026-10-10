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
  /-- caller, target, value, calldata. The caller is normally the actor itself; a
      Foundry `vm.prank` in the recorded run makes it another address. -/
  calls : List (Word × Word × Word × List Nat)
  success : Bool := true
  output : List Nat := []
  deriving Repr, Inhabited

inductive Member where
  /-- `immutables`: (name, raw word) as deployed. Immutables live in code, not in the
      world's storage, so the registry carries them; each is coerced through the
      field's type exactly as the constructor's store would. -/
  | code (contract : Contract) (immutables : List (String × Word))
  | actor (script : List ActorInvocation)
  | eoa
  deriving Inhabited

structure Registry where
  members : List (Word × Member)
  blockEnv : BlockEnv
  txEnv : TxEnv
  fuel : Nat := 4096

/-- Per-actor invocation cursors, threaded through the whole run. -/
structure Cursors where
  pos : List (Word × Nat) := []
  /-- Every answered call, in order: caller, target, selector bytes, success. For
      diffing a closed-world run against the recorded EVM call sequence. -/
  log : Array (Word × Word × List Nat × Bool) := #[]
  /-- Why a call failed inside the responder itself (not a callee revert). -/
  notes : Array String := #[]
  /-- Block environment overrides from replayed Foundry `vm.warp` / `vm.roll`. -/
  timestamp? : Option Word := none
  number? : Option Word := none
  deriving Inhabited

/-- Foundry's cheatcode address: actor scripts keep their `vm.warp`/`vm.roll` calls. -/
def cheatAddress : Word := 0x7109709ECfa91a80626fF3989D68f67F5b1DD12D

def Cursors.blockEnv (cs : Cursors) (b : BlockEnv) : BlockEnv :=
  let b := match cs.timestamp? with | some t => { b with timestamp := t } | none => b
  match cs.number? with | some n => { b with number := n } | none => b

def Cursors.note (cs : Cursors) (s : String) : Cursors := { cs with notes := cs.notes.push s }

def Cursors.next (cs : Cursors) (a : Word) : Nat × Cursors :=
  let n := ((cs.pos.find? (·.1 == a)).map (·.2)).getD 0
  (n, { cs with pos := (a, n + 1) :: cs.pos.filter (·.1 != a) })

def Cursors.record (cs : Cursors) (caller target : Word) (calldata : List Nat) (ok : Bool) :
    Cursors :=
  { cs with log := cs.log.push (caller, target, calldata.take 4, ok) }

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

def balanceOfWorld (world : Shared.OpenWorld) (a : Word) : Word :=
  match world.accounts.find? (wordToAddress a) with
  | some acc => u256ToWord acc.balance
  | none => 0

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

/-- Answer one call request by executing the callee; logged in pre-order. -/
partial def answerCall (reg : Registry) (depth : Nat) (cs : Cursors)
    (world : Shared.OpenWorld) (req : CallRequest) : Except String (CallResponse × Cursors) := do
  let idx := cs.log.size
  let cs := cs.record (addressToWord req.caller) (addressToWord req.codeAddress)
    (byteArrayToBytes req.calldata) false
  let (resp, cs) ← answerCallInner reg depth cs world req
  let (c, t, sel, _) := cs.log[idx]!
  return (resp, { cs with log := cs.log.set! idx (c, t, sel, resp.success) })

partial def answerCallInner (reg : Registry) (depth : Nat) (cs : Cursors)
    (world : Shared.OpenWorld) (req : CallRequest) : Except String (CallResponse × Cursors) := do
  if depth == 0 then return (failed world req, cs.note "depth exhausted")
  if let some resp := precompileAnswerCall? world req then return (resp, cs)
  let caller := addressToWord req.caller
  let self := addressToWord req.recipient
  let target := addressToWord req.codeAddress
  let value := u256ToWord req.transferValue
  let calldata := byteArrayToBytes req.calldata
  if target == cheatAddress then
    -- Replayed Foundry cheatcodes from an actor script: `vm.warp(t)` (0xe5d6bf02),
    -- `vm.roll(n)` (0x1f7b4f30) update the block environment; `vm.store(a, slot, v)`
    -- (0x70ca10bb) and `vm.deal(a, wei)` (0xc88a5e6d) are out-of-band world edits
    -- (Forge's `deal(token, who, n)` ends in a `vm.store`).
    let word := fun (k : Nat) => (calldata.drop (4 + 32 * k)).take 32 |>.foldl (fun a b => a * 256 + b) 0
    let (world', cs) := match calldata.take 4 with
      | [0xe5, 0xd6, 0xbf, 0x02] => (world, { cs with timestamp? := some (word 0) })
      | [0x1f, 0x7b, 0x4f, 0x30] => (world, { cs with number? := some (word 0) })
      | [0x70, 0xca, 0x10, 0xbb] =>
          let a := wordToAddress (word 0)
          let acc := (world.accounts.find? a).getD default
          let acc' : OpenAccount := { acc with storage := acc.storage.insert (wordToU256 (word 1)) (wordToU256 (word 2)) }
          ({ world with accounts := world.accounts.insert a acc' }, cs)
      | [0xc8, 0x8a, 0x5e, 0x6d] =>
          let a := wordToAddress (word 0)
          let acc := (world.accounts.find? a).getD default
          let acc' : OpenAccount := { acc with balance := wordToU256 (word 1) }
          ({ world with accounts := world.accounts.insert a acc' }, cs)
      | _ => (world, cs.note s!"ignored cheatcode {calldata.take 4}")
    return ({ success := true, returnData := ByteArray.empty, postWorld := world',
              returnedGas := req.requestedGas }, cs)
  let moves := req.kind == .call || req.kind == .callcode
  let some world1 := (if moves then transferValue world caller self value else some world)
    | return (failed world req, cs.note
        s!"value {value} from {caller} to {self}: balance {balanceOfWorld world caller}")
  match reg.find? target with
  | some (.code contract immutables) =>
      -- A2 entry re-bases `selfBalance` from the Context seed `accountBalances` plus
      -- `msg.value` (`FunctionDef.call`), not from the adopted world. Seed it with the
      -- world balance minus the value the entry will add back, so the callee starts
      -- with exactly its post-transfer balance (call) / unchanged balance (delegatecall).
      let entrySeed := balanceOfWorld world1 self - u256ToWord req.apparentValue
      let base : Context := { contract.context with
        blockEnv := cs.blockEnv reg.blockEnv, txEnv := reg.txEnv,
        accountBalances := (self, entrySeed) :: contract.context.accountBalances }
      let ctx := ABI.Contract.callContextAtWithBase contract base self caller
        (u256ToWord req.apparentValue) calldata
      let st0 := immutables.foldl (fun (st : State) (nw : String × Word) =>
          match contract.immutableFields.find? (·.name == nw.1) with
          | some field =>
              match field.ty.coerceValue? (Value.word nw.2) with
              | some v => st.storeImmutable nw.1 v
              | none => st
          | none => st)
        (adoptWorld world1 ctx State.empty)
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
      for (c, t, v, cd) in inv.calls do
        let sub : CallRequest :=
          { kind := .call, requestedGas := req.requestedGas, caller := wordToAddress c,
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
  | none => .error s!"call to unregistered address {target} from {caller} (selector {calldata.take 4}, depth {depth})"

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
def runTopLog (reg : Registry) (world0 : Shared.OpenWorld)
    (calls : List (Word × Word × Word × List Nat)) :
    Except String (List Bool × Shared.OpenWorld × Array (Word × Word × List Nat × Bool) ×
      Array String) := do
  let mut w := world0
  let mut cs : Cursors := {}
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
  return (oks, w, cs.log, cs.notes)

def runTop (reg : Registry) (world0 : Shared.OpenWorld)
    (calls : List (Word × Word × Word × List Nat)) :
    Except String (List Bool × Shared.OpenWorld) := do
  let mut w := world0
  let mut cs : Cursors := {}
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

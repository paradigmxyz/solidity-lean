import SolidCore.Refinement.Compose
import SolarTV.Machine

/-!
# SolidCore's source semantics under a call oracle

`Source.run` folds every function body's interaction tree with the closed responder
(`SolI.runWith []`): an external call that is not a precompile has no answer, so the fold fails
and the call shows nothing (`none`). Its context also knows no other account's code, so a
high-level call (`IERC20(token).balanceOf(...)`) reverts at solc's `extcodesize` guard before it is made.
A contract that calls out (UniswapV2's pair reading `balanceOf` and transferring tokens) then has
no successful behaviour in SolidCore, and a triple about it holds vacuously.

This module runs the source semantics in a world `W : World`, the source side of the call oracle the
MIR and EVM IR stages run under (`SolarTV.Machine.Oracle`):

* `Ans`: given the exchanges so far and a query, its answer, or `none` for no answer;
  `foldAns` folds an interaction tree, answering each query by `ans` from its history;
* `World`: an answerer and the other accounts' code;
* `Source.runIn W fuel` and `solidCoreIn W fuel : Sem`: `Source.run` with the context's account code
  `W.codes` and every function body folded by `W.ans` (the dispatcher, constructor, decoding and
  encoding are `Source.run`'s);
* `World.closed`: the closed responder and the contract's own context, so that
  `Source.runIn World.closed = Source.run` (`runIn_closed`) and
  `solidCoreIn World.closed = solidCore` (`solidCoreIn_closed`): every theorem about `Source.run` is
  the closed-world instance;
* `World.Open`: a world of the open world, which answers every external call and creation and
  keeps SolidCore's in-semantics precompile answers and resource defaults;
* `CallsAgree o W`: the oracle hypothesis that connects `W` to a MIR oracle `o`.

`Verify/SourceOracle.lean` composes the stages to the bytecode under a world, with `CallsAgree o W`
a premise of the end-to-end theorem.
-/

namespace SolidCore.Refinement

open SolidCore.Solidity SolidCore.Solidity.Source EvmCompiler.Simulation

/-- A source call oracle: the answer to a query given the exchanges before it, or `none` when it
has no answer (the fold then fails). -/
abbrev Ans := List Interaction.Exchange → (q : Query) → Option (Answer q)

/-- Fold an interaction tree under `ans`, from the history `h`: `none` when a query has no answer
or the tree ends in a failure (a revert caught into a value never reaches here; out of fuel). -/
def foldAns {α : Type} (ans : Ans) : List Interaction.Exchange → SolI α → Option α
  | _, .done (.ok a) => some a
  | _, .done (.error _) => none
  | h, .request q k =>
    match ans h q with
    | some a => foldAns ans (h ++ [⟨q, a⟩]) (k a)
    | none => none

/-- The closed responder of `Source.run` (`SolI.runWith []`): precompile calls answered in the
semantics, resources by their default, no other external call or creation answered. -/
def closedAns : Ans := fun _ q =>
  match q with
  | .resource r => some (Query.defaultAnswer (.resource r))
  | .external world (.call request) => precompileAnswerCall? world request
  | .external _ (.create _) => none

theorem answerCall?_nil (world : SolidCore.Solidity.Shared.OpenWorld) (request : CallRequest) :
    ScriptedResponder.answerCall? [] world request = none := by
  simp [ScriptedResponder.answerCall?, ScriptedResponder.callRows]

theorem answerCreate?_nil (world : SolidCore.Solidity.Shared.OpenWorld) (request : CreateRequest) :
    ScriptedResponder.answerCreate? [] world request = none := by
  simp [ScriptedResponder.answerCreate?, ScriptedResponder.createRows]

/-- Folding under `closedAns` is `Source.run`'s fold under the empty responder. -/
theorem foldAns_closed {α : Type} (t : SolI α) : ∀ h,
    foldAns closedAns h t = (match SolI.runWith [] t with | .ok r => some r | .error _ => none) := by
  induction t with
  | done r =>
    intro h
    cases r <;> rfl
  | request q k ih =>
    intro h
    cases q with
    | resource r =>
      simp only [foldAns, closedAns, SolI.runWith]
      exact ih _ _
    | external world req =>
      cases req with
      | call request =>
        simp only [foldAns, closedAns, SolI.runWith, answerCall?_nil]
        cases hp : precompileAnswerCall? world request with
        | none => rfl
        | some a => exact ih _ _
      | create request =>
        simp only [foldAns, closedAns, SolI.runWith, answerCreate?_nil]

/-- The world a source call runs in: the call oracle `ans`, and the code of the other accounts
before the call (`codes`, which SolidCore's existence check before a high-level call reads, as
solc's `extcodesize` guard does); `none` keeps the contract's own context, which knows no other
account's code, so that every high-level call reverts before it reaches `ans`. -/
structure World where
  ans : Ans
  codes : Option ByteMap := none

/-- The closed world of `Source.run`. -/
def World.closed : World := { ans := closedAns }

namespace Source

/-- `FunctionDef.call?` with the body folded by `ans`. -/
def callAns (ans : Ans) (fuel : Nat) (table : FunctionTable) (context : Context)
    (function : FunctionDef) (state : State) (args : List Value) : Option CallResult :=
  (function.call fuel table context state args).bind fun tree => foldAns ans [] tree

theorem callAns_closed (fuel : Nat) (table : FunctionTable) (context : Context)
    (function : FunctionDef) (state : State) (args : List Value) :
    callAns closedAns fuel table context function state args =
      function.call? fuel table context state args := by
  unfold callAns FunctionDef.call?
  cases function.call fuel table context state args with
  | none => rfl
  | some tree =>
    simp only [Option.bind_some, foldAns_closed]
    cases SolI.runWith [] tree <;> rfl

end Source

namespace Source.ABI.Oracle

open SolidCore.Solidity.Source.ABI

/-- `ABI.Contract.callCalldataAtFromWithContext?` with the selected function's body folded by
`ans`. The fallback and receive paths are `Source.run`'s. -/
def callCalldata (ans : Ans) (fuel : Nat) (contract : Contract) (base : Context) (state : State)
    (self sender value : SolidCore.Solidity.Source.Word) (calldata : Bytes) : Option AbiCallResult := do
  match readSelector? calldata with
  | some selector =>
      match contract.findFunctionBySelector? selector with
      | some function =>
          match decodeFunctionArgs? function (calldata.drop ABI.selectorBytes) with
          | Except.ok args =>
              let context :=
                Contract.callContextAtWithBase contract base self sender value calldata
              if function.acceptsValue value then
                match Source.callAns ans fuel contract.table context function state args with
                | some (CallResult.returned state' values) => do
                    let output ← encodeValues? (function.returns.map BindingDecl.ty) values
                    some { success := true, output, state := state' }
                | some (CallResult.reverted state' revert) => do
                    let output ← Contract.encodeRevertData? contract revert
                    some { success := false, output, state := state' }
                | none => none
              else
                Contract.rejectedValueCall? contract state
          | Except.error revert => Contract.revertedCall? contract state revert
      | none =>
          Contract.callFallbackAtFromWithContext? fuel contract base state self sender value calldata
  | none =>
      Contract.callReceiveOrFallbackAtFromWithContext? fuel contract base state self sender value
        calldata

set_option linter.unusedSimpArgs false in
theorem callCalldata_closed (fuel : Nat) (contract : Contract) (base : Context) (state : State)
    (self sender value : SolidCore.Solidity.Source.Word) (calldata : Bytes) :
    callCalldata closedAns fuel contract base state self sender value calldata =
      Contract.callCalldataAtFromWithContext? fuel contract base state self sender value
        calldata := by
  unfold callCalldata Contract.callCalldataAtFromWithContext?
  simp only [Source.callAns_closed]
  cases readSelector? calldata with
  | none => rfl
  | some selector =>
    cases contract.findFunctionBySelector? selector with
    | none => rfl
    | some function =>
      cases decodeFunctionArgs? function (List.drop ABI.selectorBytes calldata) with
      | error revert => rfl
      | ok args =>
        by_cases hv : function.acceptsValue value = true
        · simp only [hv, ↓reduceIte]
          cases FunctionDef.call? fuel contract.table
            (Contract.callContextAtWithBase contract base self sender value calldata) function state
            args with
          | none => rfl
          | some r => cases r <;> rfl
        · simp only [hv]
          rfl

end Source.ABI.Oracle

namespace Source

/-- `Source.result?` in the world `W`: during the call the other accounts' code is `W.codes`, and
every function body is folded by `W.ans`. The contract was deployed before the call, as
`Source.result?` deploys it, in its own context. -/
def resultIn? (W : World) (fuel : Nat) (contract : TypeCheck.CheckedContract) (call : Call) :
    Option TypeCheck.CoreAbiCallResult :=
  let base := contract.core.context
  let deploy := { base with sender := callerAddress, self := selfAddress, value := call.callvalue }
  let context := { deploy with accountCodes := W.codes.getD base.accountCodes }
  match TypeCheck.CheckedContract.constructWithContext? fuel contract deploy
      State.empty selfAddress 0 [] with
  | some (CallResult.returned deployed _) =>
    let storage := call.storage.foldl
      (fun acc kv => StorageMap.insertLoop acc kv.1 kv.2) deployed.storage
    Source.ABI.Oracle.callCalldata W.ans fuel contract.core context
      { deployed with storage := storage } selfAddress callerAddress call.callvalue
      (call.calldata.data.toList.map (·.toNat))
  | _ => none

/-- Run `call` against `contract` in SolidCore with `fuel`, in the world `W`. -/
def runIn (W : World) (fuel : Nat) (contract : TypeCheck.CheckedContract) (call : Call) :
    Option Observable :=
  (resultIn? W fuel contract call).map (observe call)

theorem resultIn?_closed (fuel : Nat) (contract : TypeCheck.CheckedContract) (call : Call) :
    resultIn? World.closed fuel contract call = result? fuel contract call := by
  unfold resultIn? result?
  simp only [World.closed, Option.getD_none, Source.ABI.Oracle.callCalldata_closed]
  rfl

/-- **The closed world is `Source.run`.** -/
theorem runIn_closed : runIn World.closed = run := by
  funext fuel contract call
  simp only [runIn, run, resultIn?_closed]

end Source

/-- SolidCore in the world `W`, with statement fuel `fuel`. -/
def solidCoreIn (W : World) (fuel : Nat) : Sem :=
  { Prog := SolidCore.Solidity.TypeCheck.CheckedContract, run := Source.runIn W fuel }

theorem solidCoreIn_closed (fuel : Nat) : solidCoreIn World.closed fuel = solidCore fuel := by
  simp only [solidCoreIn, solidCore, Source.runIn_closed]

/-! ## The open world -/

/-- A world of the open world: it answers every external call and creation, keeps SolidCore's
in-semantics answers to precompile calls and its resource defaults, and gives the other accounts'
code. -/
structure World.Open (W : World) : Prop where
  calls : ∀ h world request, (W.ans h (.external world (.call request))).isSome
  creates : ∀ h world request, (W.ans h (.external world (.create request))).isSome
  precompiles : ∀ h world request a, precompileAnswerCall? world request = some a →
    W.ans h (.external world (.call request)) = some a
  resources : ∀ h r, W.ans h (.resource r) = some (Query.defaultAnswer (.resource r))
  codes : W.codes.isSome

/-! ## The world after a call

SolidCore adopts the world a call answers (`adoptWorld`): the caller's storage and transient storage
become its account's in the answered world, and every later read of another account's code reads
the answered world (`State.envAccountCode`). The oracle hypothesis says the MIR oracle shows the
same world after the call. -/

/-- The account at the address `a` in a world, as SolidCore reads it (absent: the empty account). -/
def accountIn (world : SolidCore.Solidity.Shared.OpenWorld) (a : Nat) :
    EvmCompiler.Simulation.OpenAccount :=
  (world.accounts.find? (wordToAddress a)).getD default

/-- The word at `slot` of the caller's storage in a world, as SolidCore adopts it. -/
def storageIn (world : SolidCore.Solidity.Shared.OpenWorld) (slot : Nat) : Nat :=
  (StorageMap.lookup? (storageToWordMap (accountIn world selfAddress).storage) slot).getD 0

/-- The word at `slot` of the caller's transient storage in a world, as SolidCore adopts it. -/
def transientIn (world : SolidCore.Solidity.Shared.OpenWorld) (slot : Nat) : Nat :=
  (StorageMap.lookup? (storageToWordMap (accountIn world selfAddress).transientStorage) slot).getD 0

/-- The code of the account `a` in a world, as SolidCore reads it after adopting the world. -/
def codeIn (world : SolidCore.Solidity.Shared.OpenWorld) (a : Nat) : List SolidCore.Solidity.Byte :=
  byteArrayToBytes (accountIn world a).codeBytes

/-- The code of the account `a` after the exchanges `h`, as SolidCore reads it: the world the
last call or creation answered (`State.envAccountCode` after an adoption), else `W.codes`. -/
def codeAfter (W : World) : List Interaction.Exchange → Nat → List SolidCore.Solidity.Byte
  | h, a =>
    match h.reverse.find? (fun e => match e.query with | .external _ _ => true | _ => false) with
    | some ⟨.external _ (.call _), r⟩ => codeIn r.postWorld a
    | some ⟨.external _ (.create _), r⟩ => codeIn r.postWorld a
    | _ => SolidCore.Solidity.Shared.Account.codeAt (W.codes.getD []) a

/-! ## The oracle hypothesis -/

/-- The MIR call kind of a source call. -/
def machineKind : CallKind → SolarTV.Machine.CallKind
  | .call => .call
  | .callcode => .callcode
  | .delegatecall => .delegatecall
  | .staticcall => .staticcall

/-- The source calls of a history: kind, callee, value and input bytes. -/
def sourceCalls : List Interaction.Exchange → List (SolarTV.Machine.CallKind × Nat × Nat × List Nat)
  | [] => []
  | ⟨.external _ (.call r), _⟩ :: rest =>
    (machineKind r.kind, addressToWord r.codeAddress, u256ToWord r.transferValue,
      byteArrayToBytes r.calldata) :: sourceCalls rest
  | _ :: rest => sourceCalls rest

/-- The calls of a MIR world: kind, callee, value (zero for `DELEGATECALL` and `STATICCALL`) and
input bytes. -/
def machineCalls : List SolarTV.Machine.Event → List (SolarTV.Machine.CallKind × Nat × Nat × List Nat)
  | [] => []
  | .call kind seen input _ _ :: rest =>
    (kind, (seen.getD 1 0).toNat % 2 ^ 160,
      (if kind = .call ∨ kind = .callcode then (seen.getD 2 0).toNat else 0),
      input.map BitVec.toNat) :: machineCalls rest
  | _ :: rest => machineCalls rest

/-- The MIR oracle's code test for every address in the world `w`: `extcodesize` is zero exactly
when `code` gives the address no code. -/
def CodesAgree (o : SolarTV.Machine.Oracle) (w : List SolarTV.Machine.Event)
    (code : Nat → List SolidCore.Solidity.Byte) : Prop :=
  ∀ a < 2 ^ 160, (o.env "extcodesize" w [BitVec.ofNat 256 a] = 0) ↔ (code a).isEmpty

/-- **The oracle hypothesis**: the world `W` and the MIR oracle `o` agree.

* `codes`: in every MIR world with no call yet, `o`'s `extcodesize` of an address is zero
  exactly when `W` gives it no code;
* `calls`: for every history and call request `W.ans` answers, and every MIR world that ends
  in a call, whose calls are the source's (`sourceCalls` of the history with the request, by kind,
  callee, value and input), whose storage and transient storage at the call are the caller's in
  the world sent with the request and whose code test before the call is that world's, `o` answers that call as `W.ans` does: the success flag; for
  a call that is not a `STATICCALL`, the storage and transient storage after it, the caller's in
  the answered world, which SolidCore adopts; and, in that world followed by events with no call
  (gas reads), the size of the return data (as a word), its bytes (at word indices), and every
  account's code (the answered
  world's, which SolidCore reads after adopting it);
* `static`: a `STATICCALL` answers a world in which the caller's storage and transient storage
  are those of the world sent with it, as the MIR frame keeps them.

The callee's answer may depend on the calls before it and on the caller's storage at the call,
never on what the source cannot see (the gas forwarded, memory offsets, gas reads). -/
structure CallsAgree (o : SolarTV.Machine.Oracle) (W : World) : Prop where
  codes : ∀ w, machineCalls w = [] →
    CodesAgree o w (SolidCore.Solidity.Shared.Account.codeAt (W.codes.getD []))
  calls : ∀ h world request a, W.ans h (.external world (.call request)) = some a →
    ∀ (w : List SolarTV.Machine.Event) k s i st tr,
      w.getLast? = some (.call k s i st tr) →
      machineCalls w = sourceCalls (h ++ [⟨.external world (.call request), a⟩]) →
      (∀ slot < 2 ^ 256, (st (BitVec.ofNat 256 slot)).toNat = storageIn world slot ∧
        (tr (BitVec.ofNat 256 slot)).toNat = transientIn world slot) →
      CodesAgree o w.dropLast (codeIn world) →
      ((SolarTV.Machine.callFlag o w = 1) ↔ a.success = true) ∧
      (request.kind ≠ .staticcall → ∀ slot < 2 ^ 256,
        (o.storageAfter w (BitVec.ofNat 256 slot)).toNat = storageIn a.postWorld slot ∧
        (o.transientAfter w (BitVec.ofNat 256 slot)).toNat = transientIn a.postWorld slot) ∧
      ∀ rest : List SolarTV.Machine.Event, machineCalls rest = [] →
        (SolarTV.Machine.returndataSize o (w ++ rest)).toNat = a.returnData.size % 2 ^ 256 ∧
        (∀ j < a.returnData.size, j < 2 ^ 256 →
          (SolarTV.Machine.returndataByte o (w ++ rest) j).toNat = (a.returnData.get! j).toNat) ∧
        CodesAgree o (w ++ rest) (codeAfter W (h ++ [⟨.external world (.call request), a⟩]))
  static : ∀ h world request a, W.ans h (.external world (.call request)) = some a →
    request.kind = .staticcall →
    ∀ slot, storageIn a.postWorld slot = storageIn world slot ∧
      transientIn a.postWorld slot = transientIn world slot

/-- info: 'SolidCore.Refinement.Source.runIn_closed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Source.runIn_closed

end SolidCore.Refinement

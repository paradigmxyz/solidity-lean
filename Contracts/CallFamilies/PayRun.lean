import Contracts.CallFamilies.PaySource

/-!
# pay's body in SolidCore, through its transfer call

pay_run: from a frame binding to and amount (to below 2^160), with Calls' token field, outside
construction and with a token other than the contract itself, SolidCore's pay body is exactly one
request node, the low-level CALL of transfer(to, amount) (payInput) from the sent world, and for
every answer with return data shorter than 2^256 bytes it continues to payRes: success (no return
data, or a word equal to 1), Error("TRANSFER_FAILED") (a failed call, or a word equal to 0), or the
empty revert of a short or non-bool return word, in a runtime whose state is the adopted world with
the call recorded (payState). Covers the memoryVarDecl of ret, the tuple assignment of the call's
result, and the short-circuit require with the bool decode.
-/

namespace SolidCore.Refinement.CallFamilies

open SolarTV SolidCore.Refinement SolidCore.Refinement.Generic SolidCore.Refinement.CallNode
open SolidCore.Solidity.Source EvmCompiler.Simulation

/-- The runtime after (ok, ret) = the call's result. -/
def wroteRt (R : Runtime) (w : Nat) (out : List Byte) (L : LocalEnv) : Runtime :=
  { state := R.state
    locals := [("__solidcore_low_level_return", Value.tuple [Value.word w, Value.bytes out]),
      ("ret", Value.memoryRef R.nextMemory), ("ok", Value.word w)] :: L
    memory := R.memory.insertLoop R.nextMemory (Value.bytes out)
    nextMemory := R.nextMemory + 1
    nextMemoryByte := R.nextMemoryByte + (Value.bytes out).memoryAllocationBytes }

theorem write_ok_ret (ctx : Context) (R : Runtime) (w : Nat) (out : List Byte) (id : Nat) (L : LocalEnv)
    (hl : R.locals = [("__solidcore_low_level_return", Value.tuple [Value.word w, Value.bytes out]),
        ("ret", Value.memoryRef id), ("ok", Value.word 0)] :: L) :
    LValues.writeTupleWithRuntime ctx R [some (LValue.var "ok"), some (LValue.var "ret")]
      [Value.word w, Value.bytes out] = EvmCompiler.Simulation.Interaction.done (.ok (wroteRt R w out L)) := by
  simp [LValues.writeTupleWithRuntime, LValues.resolveTupleWithRuntime, LValue.resolveWithRuntime, LValue.toExpr,
    Expr.resolveLValue, Expr.resolveLValueFuel, Runtime.lookupStorageBase?, Runtime.lookupLocal?, hl,
    LocalEnv.lookup?, Frame.lookup?, ResolvedLValue.freezeIndexedStoragePath, pure, bind, ipure_eq]
  simp only [ResolvedLValue.asStoragePath?, dbind]
  simp [LValues.writeResolvedRightToLeft, ResolvedLValue.write, Runtime.assignLocal?, Runtime.lookupLocal?, hl,
    LocalEnv.lookup?, Frame.lookup?, Value.isMemoryObject, Runtime.memoryStoredValue, Runtime.allocMemory,
    Runtime.assignLocalRaw?, LocalEnv.assign?, Frame.assign?, Value.coerceLike?, pure, bind, dbind, ipure_eq, wroteRt]
  simp only [liftM, monadLift, MonadLift.monadLift, SolI.ofExcept, dbind]
  simp [LocalEnv.lookup?, Frame.lookup?, Value.coerceLike?, LocalEnv.assign?, Frame.assign?, wroteRt]
  done

theorem throw_eq {α : Type} (e : SolidityFailure) :
    (throw e : SolI α) = EvmCompiler.Simulation.Interaction.done (.error e) := rfl

theorem tbind {α β : Type} (e : SolidityFailure) (f : α → SolI β) :
    EvmCompiler.Simulation.Interaction.bind (EvmCompiler.Simulation.Interaction.done (.error e) : SolI α) f =
      EvmCompiler.Simulation.Interaction.done (.error e) := rfl

theorem caught_revert {α : Type} (e : SolidCore.Solidity.Source.RevertData) :
    SolI.caught (EvmCompiler.Simulation.Interaction.done (.error (SolidityFailure.revert e)) : SolI α) =
      EvmCompiler.Simulation.Interaction.done (.ok (.error e)) := rfl

theorem headWords_bool :
    (if Ty.bool.isDynamicAbi = true then some 1 else Ty.bool.staticAbiHeadWords?) = some 1 := rfl

theorem decb_short (p : Nat) (bs : List Byte) (h : bs.length < 32) :
    abiDecodeValuesWithCleanupsAtExcept? p [Ty.bool] [AbiCleanup.none] bs = .error .empty := by
  simp [abiDecodeValuesWithCleanupsAtExcept?, Ty.listAbiHeadWords?, Ty.abiHeadWords?, abiDecodeOpt, bind,
    Except.bind, pure, Except.pure, wordBytes_eq, headWords_bool, h]

theorem decb_word (p : Nat) (bs : List Byte) (h : 32 ≤ bs.length) :
    abiDecodeValuesWithCleanupsAtExcept? p [Ty.bool] [AbiCleanup.none] bs =
      if bytesToWordBE ((bs.map normByte).take 32) ≤ 1 then
        .ok [.word (bytesToWordBE ((bs.map normByte).take 32))] else .error .empty := by
  have : ¬ bs.length < 32 := by omega
  simp [abiDecodeValuesWithCleanupsAtExcept?, Ty.listAbiHeadWords?, Ty.abiHeadWords?, abiDecodeOpt, bind,
    Except.bind, pure, Except.pure, abiDecodeValuesWithCleanupsAux?, abiDecodeValueAt?, wordBytes_eq, this,
    abiCheckTopLevelAllocationAt?, headWords_bool]
  rw [show Ty.bool.abiDecodeFuel = 1 from rfl]
  simp [abiDecodeValueAtWithFuel?, readWord?, readBytes?, wordBytes_eq, h, abiDecodeOpt, AbiCleanup.accepts]
  have hwlt : bytesToWordBE (List.take 32 (List.map normByte bs)) < 2 ^ 256 := Nat.mod_lt _ (by decide)
  generalize bytesToWordBE (List.take 32 (List.map normByte bs)) = w at hwlt ⊢
  simp only [bind, Except.bind]
  by_cases h0 : w = 0
  · subst h0; simp [wordEq]
  by_cases h1 : w = 1
  · subst h1; simp [wordEq]
  have h2 : ¬ w ≤ 1 := fun h => by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp h with h | h <;> contradiction
  have hn : SolidCore.Solidity.Shared.norm w = w := Nat.mod_eq_of_lt hwlt
  simp [wordEq, hn, h0, h1, h2, show SolidCore.Solidity.Shared.norm 0 = 0 from rfl,
    show SolidCore.Solidity.Shared.norm 1 = 1 from rfl]

/-- What pay's require condition evaluates to, by the call's success flag and return bytes. -/
def condRes (R : Runtime) (b : Bool) (out : List Byte) : SolI (Value × Runtime) :=
  if b then
    if out.length = 0 then .done (.ok (.word 1, R))
    else if out.length < 32 then .done (.error (.revert .empty))
    else if bytesToWordBE (((out.map normByte).map normByte).take 32) ≤ 1 then
      .done (.ok (.word (bytesToWordBE (((out.map normByte).map normByte).take 32)), R))
    else .done (.error (.revert .empty))
  else .done (.ok (.word 0, R))

theorem cond_eval (ctx : Context) (R : Runtime) (b : Bool) (out : List Byte) (id : Nat) (L : LocalEnv)
    (hl : R.locals = [("__solidcore_low_level_return", Value.tuple [Value.word (if b = true then 1 else 0),
        Value.bytes out]), ("ret", Value.memoryRef id), ("ok", Value.word (if b = true then 1 else 0))] :: L)
    (hm : R.memory[id]? = some (Value.bytes out)) (hlen : out.length < 2 ^ 256) :
    Expr.eval ctx R payCond = condRes R b out := by
  simp only [Expr.eval, payCond, Expr.orderFuel, Expr.listEvalFuel]
  simp only [Expr.evalFuel]
  cases b
  · simp [Runtime.lookupStorageBase?, Runtime.lookupLocal?, hl, LocalEnv.lookup?, Frame.lookup?,
      Runtime.derefMemoryValue, Value.expectWord, wordTruthy, liftM, monadLift, MonadLift.monadLift, SolI.ofExcept,
      bind_done_ok, pure, SolidCore.Solidity.Shared.norm, condRes]
    rfl
  · simp [Runtime.lookupStorageBase?, Runtime.lookupLocal?, hl, LocalEnv.lookup?, Frame.lookup?,
      Runtime.derefMemoryValue, Value.expectWord, wordTruthy, liftM, monadLift, MonadLift.monadLift, SolI.ofExcept,
      Runtime.loadMemory?, MemoryMap.lookup?, hm, bind_done_ok, pure, SolidCore.Solidity.Shared.norm, ipure_eq, wm,
      Value.length?, cleanup256, BinaryOp.apply, normWord]
    by_cases hz : out.length = 0
    · simp only [hz, cleanup256 _ 0 (by decide)]
      simp [Value.forceAbiLazy, BinaryOp.preservesFixedBytesWidth, bind_done_ok, ipure_eq, wm, wordEq, boolWord, bind,
        Except.bind, pure, Except.pure, condRes]
      intro h; exact absurd (List.length_eq_zero_iff.mp hz) h
    · simp only [cleanup256 _ _ hlen]
      simp [Value.forceAbiLazy, BinaryOp.preservesFixedBytesWidth, bind_done_ok, ipure_eq, wm, wordEq, boolWord, bind,
        Except.bind, pure, Except.pure, hz, Runtime.lookupStorageBase?, Runtime.lookupLocal?, hl, LocalEnv.lookup?,
        Frame.lookup?, Runtime.derefMemoryValue, Runtime.loadMemory?, MemoryMap.lookup?, hm, condRes]
      have hn' : SolidCore.Solidity.Shared.norm out.length = out.length := Nat.mod_eq_of_lt hlen
      have hz' : ¬ out = [] := fun h => hz (by rw [h]; rfl)
      by_cases hs : out.length < 32
      · simp [decb_short _ (out.map normByte) (by simpa using hs), hs, hn', hz, hz',
          show SolidCore.Solidity.Shared.norm 0 = 0 from rfl, Value.asBytes?]
        rfl
      · simp only [Value.asBytes?]
        rw [decb_word _ (out.map normByte) (by simp; omega)]
        simp only [List.map_map]
        have hwlt : bytesToWordBE ((out.map (normByte ∘ normByte)).take 32) < 2 ^ 256 := Nat.mod_lt _ (by decide)
        generalize bytesToWordBE ((out.map (normByte ∘ normByte)).take 32) = w at hwlt ⊢
        by_cases hw1 : w ≤ 1
        · have hn : w % 115792089237316195423570985008687907853269984665640564039457584007913129639936 = w :=
            Nat.mod_eq_of_lt hwlt
          rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hw1 with h | h <;> subst h <;>
            simp [hs, hn', hz, hz', show SolidCore.Solidity.Shared.norm 0 = 0 from rfl, Value.asBytes?, throw_eq,
              tbind, dbind] <;> rfl
        · simp [hw1, hs, hn', hz, hz', show SolidCore.Solidity.Shared.norm 0 = 0 from rfl, Value.asBytes?, throw_eq,
            tbind, dbind]
          done

/-- The state pay leaves once the transfer answered: the adopted world, with the call recorded. -/
def payState (ctx : Context) (st : State) (a : CallResponse) (D : LowLevelCallResult) : State :=
  { adoptWorld a.postWorld ctx st with
    externalInteractions := (adoptWorld a.postWorld ctx st).externalInteractions ++ [ExternalInteraction.lowLevelCall D] }

/-- pay's result, by the call's success flag and return bytes: success (no return data, or a true
word), Error("TRANSFER_FAILED") (a failed call or a false word), or the empty revert of a short or
non-bool return word. -/
def payRes (b : Bool) (out : List Byte) (R : Runtime) : Result :=
  let w := bytesToWordBE ((out.map (normByte ∘ normByte)).take 32)
  let r0 : Result :=
    if b then
      if out.length = 0 then .normal R
      else if out.length < 32 then .reverted R .empty
      else if w ≤ 1 then (if w = 0 then .reverted R (.error "TRANSFER_FAILED") else .normal R)
      else .reverted R .empty
    else .reverted R (.error "TRANSFER_FAILED")
  (r0.mapRuntime Runtime.popScope).mapRuntime Runtime.popScope

set_option maxHeartbeats 300000 in
theorem pay_run (n : Nat) (tbl : FunctionTable) (ctx : Context) (rt : Runtime) (dst amt : Nat)
    (hd : dst < 2 ^ 160) (ha : amt < 2 ^ 256)
    (hl : rt.locals = [[("to", .word dst), ("amount", .word amt)]])
    (hf : AddrFieldOk ctx "token" tokenField) (hw : rt.state.loadSlot tokenField.slot < Generic.wordSize)
    (hcons : ctx.construction = false)
    (hself : wordEq (SolidCore.Solidity.Shared.norm (fieldValue (rt.state.loadSlot tokenField.slot) tokenField.packedOffset 20)) ctx.self = false) :
    ∃ k, Stmt.eval (n + 3) tbl ctx rt payBody =
      .request (.external (snapshotWorld ctx rt.state)
        (.call (buildCallRequest ctx .call (SolidCore.Solidity.Shared.norm (fieldValue (rt.state.loadSlot tokenField.slot) tokenField.packedOffset 20))
          (List.map normByte (payInput dst amt)) (SolidCore.Solidity.Shared.norm 0) none))) k ∧
      ∀ a : CallResponse, a.returnData.size < 2 ^ 256 → ∃ R : Runtime,
        R.state = payState ctx rt.state a (decodeCallResponse a .call
          (SolidCore.Solidity.Shared.norm (fieldValue (rt.state.loadSlot tokenField.slot) tokenField.packedOffset 20))
          (List.map normByte (payInput dst amt)) (SolidCore.Solidity.Shared.norm 0) none) ∧
        k a = pure (payRes (decodeCallResponse a .call
          (SolidCore.Solidity.Shared.norm (fieldValue (rt.state.loadSlot tokenField.slot) tokenField.packedOffset 20))
          (List.map normByte (payInput dst amt)) (SolidCore.Solidity.Shared.norm 0) none).success
          (decodeCallResponse a .call
          (SolidCore.Solidity.Shared.norm (fieldValue (rt.state.loadSlot tokenField.slot) tokenField.packedOffset 20))
          (List.map normByte (payInput dst amt)) (SolidCore.Solidity.Shared.norm 0) none).output R) := by
  rw [payBody, eval_block, evalList_cons, show n + 2 = (n + 1) + 1 from rfl, eval_skip, sbind_pure]
  dsimp only
  rw [evalList_cons, pay_amount (n + 1) tbl ctx rt.pushScope dst amt ha (by simp [Runtime.pushScope, hl]), sbind_pure]
  dsimp only
  rw [evalList_cons, eval_block, payInner, evalList_cons, eval_varDecl_none, sbind_pure]
  dsimp only
  rw [evalList_cons, eval_memoryVarDecl_none, ret_decl]
  dsimp only
  rw [sbind_pure]
  dsimp only
  rw [evalList_cons, eval_varDecl_some]
  rw [Expr.eval, show payCallE.orderFuel + 1 = 13 + 1 from rfl, payCallE,
    eval_lowLevelCall 13 ctx _ _ _ _ false (tokF' 12 ctx _ rt hf ?hs hw) rfl (word0F 12 ctx _) rfl
      (payEnc 7 ctx _ dst amt hd ha ?b1 ?l1 ?b2 ?l2) rfl hcons hself]
  · simp only [caught_request, bind_request]
    refine ⟨_, rfl, fun a ha => ?_⟩
    simp only [lowLevelTail, caught_done_ok, bind_done_ok, pure]
    have hlen : (decodeCallResponse a LowLevelCallKind.call
          (SolidCore.Solidity.Shared.norm (fieldValue (rt.state.loadSlot tokenField.slot) tokenField.packedOffset 20))
          (List.map normByte (payInput dst amt)) (SolidCore.Solidity.Shared.norm 0) none).output.length < 2 ^ 256 := by
      simp only [decodeCallResponse, byteArrayToBytes_eq, List.length_map, List.length_range]; exact ha
    generalize decodeCallResponse a LowLevelCallKind.call _ _ _ none = D at hlen ⊢
    simp only [ipure_eq, caught_done_ok, bind_done_ok]
    generalize hR0 : retRt _ = R0
    have hR0l : R0.locals = [[("ret", Value.memoryRef rt.nextMemory), ("ok", Value.word 0)], [],
        [("to", Value.word dst), ("amount", Value.word amt)]] := by
      rw [← hR0]; simp [retRt, Runtime.declareLocal, Runtime.pushScope, LocalEnv.declare, Ty.defaultValue]
    have hR0m : R0.memory = rt.memory.insertLoop rt.nextMemory (Value.bytes []) := by
      rw [← hR0]; simp [retRt, Runtime.declareLocal, Runtime.pushScope]
    have hR0n : R0.nextMemory = rt.nextMemory + 1 := by
      rw [← hR0]; simp [retRt, Runtime.declareLocal, Runtime.pushScope]
    have hR0s : R0.state = rt.state := by
      rw [← hR0]; simp [retRt, Runtime.declareLocal, Runtime.pushScope]
    clear hR0
    simp only [Ty.coerceTupleValues?, Ty.coerceValue?, boolWord]
    have h01 : (wordEq (if D.success = true then 1 else 0) 0 ||
        wordEq (if D.success = true then 1 else 0) 1) = true := by
      cases D.success <;> simp [wordEq]
    simp only [h01, ↓reduceIte]
    dsimp only [bind, Option.bind]
    generalize hR1 : Runtime.declareLocal _ "__solidcore_low_level_return" _ = R1
    have hR1l : R1.locals = [[("__solidcore_low_level_return", Value.tuple [Value.word (if D.success = true then 1 else 0),
        Value.bytes D.output]), ("ret", Value.memoryRef rt.nextMemory), ("ok", Value.word 0)], [],
        [("to", Value.word dst), ("amount", Value.word amt)]] := by
      rw [← hR1]; simp [Runtime.declareLocal, Runtime.recordExternalInteraction, LocalEnv.declare, hR0l]
    have hR1s : R1.state = payState ctx rt.state a D := by
      rw [← hR1, ← hR0s]; rfl
    have hR1m : R1.memory = R0.memory := by
      rw [← hR1]; simp [Runtime.declareLocal, Runtime.recordExternalInteraction]
    have hR1n : R1.nextMemory = R0.nextMemory := by
      rw [← hR1]; simp [Runtime.declareLocal, Runtime.recordExternalInteraction]
    clear hR1
    rw [dbind]; dsimp only
    rw [evalList_cons, Stmt.eval]; dsimp only
    simp [Expr.eval, Expr.orderFuel, Expr.evalFuel, Runtime.lookupStorageBase?, Runtime.lookupLocal?, hR1l,
      LocalEnv.lookup?, Frame.lookup?, Runtime.derefMemoryValue]
    simp only [liftM, monadLift, MonadLift.monadLift, SolI.ofExcept, bind_done_ok, ipure_eq, caught_done_ok, pure]
    try simp only [dbind]
    rw [write_ok_ret ctx R1 _ D.output rt.nextMemory _ hR1l]
    try simp only [caught_done_ok, dbind]
    generalize hR2 : wroteRt R1 _ D.output _ = R2
    have hR2l : R2.locals = [("__solidcore_low_level_return", Value.tuple [Value.word (if D.success = true then 1 else 0),
        Value.bytes D.output]), ("ret", Value.memoryRef R1.nextMemory), ("ok", Value.word (if D.success = true then 1 else 0))] ::
        [[], [("to", Value.word dst), ("amount", Value.word amt)]] := by
      rw [← hR2]; rfl
    have hR2m : R2.memory = R1.memory.insertLoop R1.nextMemory (Value.bytes D.output) := by rw [← hR2]; rfl
    have hR2s : R2.state = R1.state := by rw [← hR2]; rfl
    clear hR2
    rw [bind_done_ok]; dsimp only
    rw [bind_done_ok]; dsimp only
    rw [evalList_cons, eval_require]
    have hm : R2.memory[R1.nextMemory]? = some (Value.bytes D.output) := by
      rw [hR2m]; simp [MemoryMap.insertLoop]
    rw [cond_eval ctx R2 D.success D.output R1.nextMemory _ hR2l hm hlen]
    refine ⟨R2, by rw [hR2s, hR1s], ?_⟩
    simp only [condRes, payRes]
    simp only [List.map_map]
    have hwm : SolidCore.Solidity.Shared.wordModulus = 2 ^ 256 := rfl
    have hwlt : bytesToWordBE (List.take 32 (List.map (normByte ∘ normByte) D.output)) < 2 ^ 256 :=
      Nat.mod_lt _ (by decide)
    have hwlt' : bytesToWordBE (List.take 32 (List.map (normByte ∘ normByte) D.output)) <
        115792089237316195423570985008687907853269984665640564039457584007913129639936 := hwlt
    split_ifs <;> simp [caught_done_ok, bind_done_ok, dbind, tbind, ipure_eq, Value.expectWord, wordTruthy,
      evalList_nil, pure, SolidCore.Solidity.Shared.norm, throw_eq, hwm, caught_revert, Nat.mod_eq_of_lt hwlt',
      Result.mapRuntime, *] <;> done
  · rfl
  all_goals simp [Runtime.lookupStorageBase?, Runtime.lookupLocal?, retRt, Runtime.declareLocal, Runtime.pushScope,
    LocalEnv.declare, LocalEnv.lookup?, Frame.lookup?]

/-- info: 'SolidCore.Refinement.CallFamilies.pay_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms pay_run

end SolidCore.Refinement.CallFamilies

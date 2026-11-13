import Contracts.CallFamilies.SyncSource

/-!
# The source half of `feeOn`

`feeOn_source`: SolidCore's run of `feeOn()` in a world `V` asks `V` the `STATICCALL` of
`feeTo()` the MIR makes, from the world the MIR sees, and shows `FeeOn.obsOf` of `V`'s answer
(`FeeOnSource`); `feeOn_stage_in` composes it with `mir_feeOn_agree` into the source stage of
`feeOn` under every oracle that agrees with `V`.
-/

namespace SolidCore.Refinement.CallFamilies

open SolarTV SolidCore.Refinement SolidCore.Refinement.Generic SolidCore.Refinement.CallNode
open SolidCore.Solidity.Source EvmCompiler.Simulation

/-- SolidCore's `feeOn()` of `Calls`, as the checker lowers it. -/
def feeOnFn : FunctionDef :=
{ name := "feeOn",
  selector? := some 1328766218,
  payable := false,
  params := [],
  paramAbiCleanups := [],
  returns := [{ name := "on", ty := Ty.bool, isStorageRef := false }],
  body := Stmt.block
            [Stmt.skip,
             Stmt.block
               [Stmt.varDecl (Ty.address) "_sol_hoist_1" (some (Expr.word 0)),
                Stmt.varDecl (Ty.address) "_sol_hoist_0" none,
                Stmt.tryExternalCall
                  (SolidCore.Solidity.Shared.Call.ExternalCallKind.staticcall)
                  (Expr.storageRead (StorageReadMode.ref) "factory" [])
                  (Expr.encode (EncodeKind.withSelector) (some (Expr.word 25067096)) [] [] [])
                  (Expr.word 0) none false false
                  [{ name := "__ext0", ty := Ty.address, isStorageRef := false }]
                  [AbiCleanup.none]
                  (Stmt.assign (LValue.var "_sol_hoist_0") (Expr.var "__ext0"))
                  [],
                Stmt.assign (LValue.var "on")
                  (Expr.binary (BinaryOp.ne) (Expr.var "_sol_hoist_0") (Expr.var "_sol_hoist_1")),
                Stmt.ifElse (Expr.var "on")
                  (Stmt.assign (LValue.storage "kLast") (Expr.word 1))
                  (Stmt.skip)]],
  dispatchId? := none }

theorem decode_addr (bs : List Byte) (h : 32 ≤ bs.length) :
    abiDecodeValuesExcept? [Ty.address] bs =
      if bytesToWordBE ((bs.map normByte).take 32) < 2 ^ 160 then
        .ok [.word (bytesToWordBE ((bs.map normByte).take 32))] else .error .empty := by
  have : ¬ bs.length < 32 := by omega
  simp [abiDecodeValuesExcept?, Ty.listAbiHeadWords?, Ty.abiHeadWords?, abiDecodeOpt, bind,
    Except.bind, pure, Except.pure, abiDecodeValuesAux?, abiDecodeValueAt?,
    wordBytes_eq, this]
  rw [show Ty.address.abiDecodeFuel = 1 from rfl]
  simp [abiDecodeValueAtWithFuel?, readWord?, readBytes?, wordBytes_eq, h, this, abiDecodeOpt,
    show (if Ty.address.isDynamicAbi = true then some 1 else Ty.address.staticAbiHeadWords?) = some 1 from rfl,
    abiAddressFits]
  have hv : bytesToWordBE (List.take 32 (List.map normByte bs)) < 2 ^ 256 := Nat.mod_lt _ (by decide)
  generalize bytesToWordBE (List.take 32 (List.map normByte bs)) = v at hv ⊢
  have hn : SolidCore.Solidity.Shared.norm v = v := Nat.mod_eq_of_lt hv
  by_cases hc : v < 2 ^ 160
  · have hc' : v < 1461501637330902918203684832716283019655932542976 := hc
    simp [hn, hc', bind, Except.bind]
  · have hc' : ¬ v < 1461501637330902918203684832716283019655932542976 := hc
    simp [hn, hc', bind, Except.bind]

theorem decode_short_addr (bs : List Byte) (h : bs.length < 32) :
    abiDecodeValuesExcept? [Ty.address] bs = .error .empty := by
  simp [abiDecodeValuesExcept?, Ty.listAbiHeadWords?, Ty.abiHeadWords?, abiDecodeOpt, bind,
    Except.bind, pure, Except.pure, wordBytes_eq, h,
    show (if Ty.address.isDynamicAbi = true then some 1 else Ty.address.staticAbiHeadWords?) = some 1 from rfl]

theorem deref_word (rt : Runtime) (w : Word) : rt.derefMemoryValueDeep (.word w) = .ok (.word w) := by
  unfold Runtime.derefMemoryValueDeep
  rw [Runtime.derefMemoryValueWithFuel]
  all_goals intros
  all_goals contradiction

theorem enc_feeTo (ctx : Context) (rt : Runtime) :
    (Expr.encode (EncodeKind.withSelector) (some (Expr.word 25067096)) [] [] []).evalWithRuntimeByContext
      ctx rt = .ok (.bytes [1, 126, 126, 88], rt) := by
  simp only [Expr.evalWithRuntimeByContext, Expr.eval, Expr.orderFuel, Expr.evalFuel,
    Expr.listEvalFuel, Expr.evalListFuel]
  simp [Runtime.materializeForValueUseList, mat_word, bind, pure, liftM, monadLift,
    MonadLift.monadLift, SolI.ofExcept, ipure_bind]
  rfl

theorem eval_varDecl_addr0 (n : Nat) (table : FunctionTable) (ctx : Context) (rt : Runtime)
    (x : String) :
    Stmt.eval (n + 1) table ctx rt (.varDecl Ty.address x (some (Expr.word 0))) =
      pure (Result.normal (rt.declareLocal x (.word 0))) := by
  rw [Stmt.eval]
  simp [Expr.eval, Expr.evalFuel, Expr.orderFuel]
  rfl

theorem eval_skip (n : Nat) (table : FunctionTable) (ctx : Context) (rt : Runtime) :
    Stmt.eval (n + 1) table ctx rt .skip = pure (Result.normal rt) := by
  rw [Stmt.eval]

/-- `Calls`'s `factory` field. -/
def factoryField : StorageField :=
  { name := "factory",
    slot := 0,
    ty? := some Ty.address,
    layout? := some (StorageLayout.scalar Ty.address),
    transient := false,
    packedOffset := 0,
    packedBytes := 20,
    packedSigned := false }

theorem fac_eval (ctx : Context) (rt : Runtime) (hf : AddrFieldOk ctx "factory" factoryField)
    (hw : rt.state.loadSlot factoryField.slot < Generic.wordSize) :
    (Expr.storageRead .ref "factory" []).evalWithRuntimeByContext ctx rt =
      .ok (.word (fieldValue (rt.state.loadSlot factoryField.slot) factoryField.packedOffset 20), rt) := by
  simp only [Expr.evalWithRuntimeByContext, Expr.eval, Expr.orderFuel, Expr.evalFuel,
    Expr.listEvalFuel]
  simp only [load_addrField hf hw]
  rfl

theorem feeOnCall_eq (σ : List (Nat × Nat)) :
    FeeOn.feeOnCall σ = Evm.Wide.callAt 1328766218 [] σ := rfl

theorem feeOn_source (k : Nat) (V : World) {c : SolidCore.Solidity.TypeCheck.CheckedContract}
    {d : SolidCore.Solidity.Source.State} (hd : Wide.DeployedAt (k + 5) c d [])
    (hfind : c.core.findFunctionBySelector? 1328766218 = some feeOnFn)
    (hfields : c.core.storageFields = callsFields)
    (hstatic : StaticKeeps V) (hdt : d.transient.toList = []) (hde : d.envWorld? = none)
    (hcb : c.core.context.accountBalances = []) (hch : c.core.context.accountCodehashes = [])
    (hcc : c.core.context.accountCodes = []) (hkeys : ∀ p ∈ V.codes.getD [], p.1 < 2 ^ 160)
    (hsize : ∀ h world request a, V.ans h (.external world (.call request)) = some a →
      a.returnData.size < 2 ^ 256) (σ : List (Nat × Nat))
    (hself : slotValue σ 0 % 2 ^ 160 ≠ selfAddress) : FeeOnSource (k + 5) c V σ := by
  have hlt := slotValue_lt σ
  intro obs hrun
  rw [feeOnCall_eq, runIn_eq_at V hd] at hrun
  simp only [Source.ABI.Oracle.callCalldata, Dirty.readSelector_calldata _ (by decide : 1328766218 < 2 ^ 32), hfind] at hrun
  simp only [show ABI.decodeFunctionArgs? feeOnFn (List.drop ABI.selectorBytes
      (List.map (fun x => x.toNat) (EthLib.Base.natToBytes 4 1328766218) ++
        Dirty.argBytes (List.map (fun x => BitVec.toNat x) []))) = .ok [] from rfl,
    show feeOnFn.acceptsValue 0 = true from rfl, ↓reduceIte] at hrun
  generalize hctx : ABI.Contract.callContextAtWithBase c.core (ctxIn V c) selfAddress callerAddress 0
    (List.map (fun x => x.toNat) (EthLib.Base.natToBytes 4 1328766218) ++
      Dirty.argBytes (List.map (fun x => BitVec.toNat x) [])) = ctx at hrun
  generalize hst : ({ d with storage := σ.foldl (fun acc kv => acc.insertLoop kv.1 kv.2) d.storage } :
    SolidCore.Solidity.Source.State) = st0 at hrun
  have hctxv : ctx.value = 0 := by subst hctx; rfl
  have hctxs : ctx.self = selfAddress := by subst hctx; rfl
  simp only [Source.callAns, FunctionDef.call, FunctionDef.evalBodyEntry, hctxv,
    show feeOnFn.acceptsValue 0 = true from rfl, ↓reduceIte,
    show feeOnFn.initialFrame? [] = some [("on", Value.word 0)] by
      simp [FunctionDef.initialFrame?, FunctionDef.returnDefaultBindings, BindingDecl.defaultBinding,
        BindingDecl.bindArgs?, feeOnFn, Ty.defaultValue], Option.map_some, Option.bind_some] at hrun
  generalize hrt0 : ({ state := { st0 with selfBalance := Solidity.Shared.addWord (Solidity.Shared.Account.balanceAt ctx.accountBalances ctx.self) 0, worldMutatedSinceAdoption := true }, locals := [[("on", Value.word 0)]] } : Runtime) = rt0 at hrun
  rw [show feeOnFn.body = Stmt.block
            [Stmt.skip,
             Stmt.block
               [Stmt.varDecl (Ty.address) "_sol_hoist_1" (some (Expr.word 0)),
                Stmt.varDecl (Ty.address) "_sol_hoist_0" none,
                Stmt.tryExternalCall
                  (SolidCore.Solidity.Shared.Call.ExternalCallKind.staticcall)
                  (Expr.storageRead (StorageReadMode.ref) "factory" [])
                  (Expr.encode (EncodeKind.withSelector) (some (Expr.word 25067096)) [] [] [])
                  (Expr.word 0) none false false
                  [{ name := "__ext0", ty := Ty.address, isStorageRef := false }]
                  [AbiCleanup.none]
                  (Stmt.assign (LValue.var "_sol_hoist_0") (Expr.var "__ext0"))
                  [],
                Stmt.assign (LValue.var "on")
                  (Expr.binary (BinaryOp.ne) (Expr.var "_sol_hoist_0") (Expr.var "_sol_hoist_1")),
                Stmt.ifElse (Expr.var "on")
                  (Stmt.assign (LValue.storage "kLast") (Expr.word 1))
                  (Stmt.skip)]] from rfl] at hrun
  simp only [eval_block, evalList_cons, eval_skip, sbind_pure, eval_varDecl_addr0, eval_varDecl_none] at hrun
  rw [show k + 3 = (k + 2) + 1 from rfl] at hrun
  have hctxf : ctx.storageFields = callsFields := by subst hctx; exact hfields
  have hfx : AddrFieldOk ctx "factory" factoryField :=
    ⟨by simp [Context.storageField?, hctxf, callsFields, factoryField, tokenField], rfl, rfl, rfl, by decide, by decide⟩
  have hload : ∀ k, k < Generic.wordSize → st0.loadSlot k = slotValue σ k := by
    intro k hk
    have := getD_storage_cover hd (σ := σ) (by intro kv hkv; simp at hkv) k
    subst hst
    simp only [State.loadSlot, StorageMap.lookup?]
    rw [← this]
    simp only [SolidCore.Solidity.Shared.norm, modulus_eq, Std.HashMap.get?_eq_getElem?]
    cases (List.foldl (fun acc kv => acc.insertLoop kv.1 kv.2) d.storage σ)[k % Generic.wordSize]? <;> rfl
  have hT : ((rt0.pushScope.pushScope.declareLocal "_sol_hoist_1" (Value.word 0)).declareLocal "_sol_hoist_0" Ty.address.defaultValue).state.loadSlot factoryField.slot = slotValue σ 0 := by
    subst hrt0; exact hload 0 (by decide)
  have ht := fac_eval ctx ((rt0.pushScope.pushScope.declareLocal "_sol_hoist_1" (Value.word 0)).declareLocal "_sol_hoist_0" Ty.address.defaultValue) hfx
    (by rw [hT]; exact hlt 0)
  rw [hT] at ht
  have hne : wordEq (SolidCore.Solidity.Shared.norm (fieldValue (slotValue σ 0) factoryField.packedOffset 20)) ctx.self = false := by
    rw [hctxs]
    simp only [wordEq, fieldValue, factoryField, SolidCore.Solidity.Shared.norm]
    simp
    have h1 : slotValue σ 0 % 1461501637330902918203684832716283019655932542976 < Solidity.Shared.wordModulus :=
      lt_of_lt_of_le (Nat.mod_lt _ (by decide)) (by decide)
    rw [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt (by decide : selfAddress < Solidity.Shared.wordModulus)]
    exact hself
  rw [eval_tryCall (k + 2) _ ctx _ _ _ _ _ false _ _ _ _ ht rfl (word0_eval ctx _) rfl (enc_feeTo ctx _) rfl hne] at hrun
  generalize hW : snapshotWorld ctx ((rt0.pushScope.pushScope.declareLocal "_sol_hoist_1" (Value.word 0)).declareLocal "_sol_hoist_0" Ty.address.defaultValue).state = world at hrun
  generalize hR : buildCallRequest ctx Solidity.Shared.Call.ExternalCallKind.staticcall
      (Solidity.Shared.norm (fieldValue (slotValue σ 0) factoryField.packedOffset 20))
      (List.map normByte [1, 126, 126, 88]) (Solidity.Shared.norm 0) none = request at hrun
  simp only [bind_request, map_request] at hrun
  rw [foldAns_request] at hrun
  cases hans : V.ans [] (Query.external world (ExternalRequest.call request)) with
  | none => simp [hans] at hrun
  | some a =>
    simp only [hans] at hrun
    have hworld : ∀ slot < 2 ^ 256, storageIn world slot = slotValue σ slot % 2 ^ 256 := by
      intro slot hslot
      have hmut : ((rt0.pushScope.pushScope.declareLocal "_sol_hoist_1" (Value.word 0)).declareLocal "_sol_hoist_0" Ty.address.defaultValue).state.worldMutatedSinceAdoption = true := by
        subst hrt0; rfl
      have hwf : StorageMap.WF ((rt0.pushScope.pushScope.declareLocal "_sol_hoist_1" (Value.word 0)).declareLocal "_sol_hoist_0" Ty.address.defaultValue).state.storage := by
        subst hrt0 hst
        exact wf_foldl σ _ (wf_of_toList_nil _ hd.storage)
      have hl := hload slot hslot
      have hsto : ((rt0.pushScope.pushScope.declareLocal "_sol_hoist_1" (Value.word 0)).declareLocal "_sol_hoist_0" Ty.address.defaultValue).state.storage = st0.storage := by
        subst hrt0; rfl
      subst hW
      unfold storageIn accountIn
      rw [show wordToAddress selfAddress = wordToAddress ctx.self by rw [hctxs],
        snapshotWorld_find_self ctx _ (Or.inr hmut)]
      simp only [Option.getD_some, snapshotSelfAccount]
      rw [lookup?_roundtrip _ hwf, hsto]
      unfold State.loadSlot at hl
      cases h : StorageMap.lookup? st0.storage slot with
      | none => rw [h] at hl; simp [← hl]
      | some v => rw [h] at hl; simp [← hl, SolidCore.Solidity.Shared.norm]; rfl
    refine ⟨world, request, a, ?_, ?_⟩
    · refine ⟨hans, by subst hR; rfl, ?_, by subst hR; rfl, ?_, ?_, ?_, ?_, ?_⟩
      · subst hR
        simp [buildCallRequest, addressToWord, wordToAddress, wordToU256, fieldValue, factoryField,
          EvmYul.AccountAddress.ofUInt256, SolidCore.Solidity.Shared.norm]
        have h1 : slotValue σ 0 % 1461501637330902918203684832716283019655932542976 <
            Solidity.Shared.wordModulus := lt_of_lt_of_le (Nat.mod_lt _ (by decide)) (by decide)
        rw [Nat.mod_eq_of_lt h1]
        simp [EvmYul.UInt256.ofNat, EvmYul.AccountAddress.size, Fin.ofNat, Id.run, EvmYul.UInt256.size]
      · subst hR
        show byteArrayToBytes (bytesToByteArray (List.map normByte [1, 126, 126, 88])) = List.map BitVec.toNat FeeOn.input
        simp only [byteArrayToBytes, toList_eq_data, bytesToByteArray]
        decide
      · exact hworld
      · intro slot hslot
        have hmut : ((rt0.pushScope.pushScope.declareLocal "_sol_hoist_1" (Value.word 0)).declareLocal "_sol_hoist_0" Ty.address.defaultValue).state.worldMutatedSinceAdoption = true := by
          subst hrt0; rfl
        have htr : ((rt0.pushScope.pushScope.declareLocal "_sol_hoist_1" (Value.word 0)).declareLocal "_sol_hoist_0" Ty.address.defaultValue).state.transient = d.transient := by
          subst hrt0 hst; rfl
        subst hW
        unfold transientIn accountIn
        rw [show wordToAddress selfAddress = wordToAddress ctx.self by rw [hctxs],
          snapshotWorld_find_self ctx _ (Or.inr hmut)]
        simp only [Option.getD_some, snapshotSelfAccount]
        rw [lookup?_roundtrip _ (by rw [htr]; exact wf_of_toList_nil _ hdt), htr]
        have hnone : StorageMap.lookup? d.transient slot = none := by
          unfold StorageMap.lookup?
          rw [Std.HashMap.get?_eq_getElem?]
          cases h : d.transient[SolidCore.Solidity.Shared.norm slot]? with
          | none => rfl
          | some v =>
            have := Std.HashMap.mem_toList_iff_getElem?_eq_some.mpr h
            rw [hdt] at this; cases this
        rw [hnone]; rfl
      · intro x hx
        have hacc : ctx.accountCodes = V.codes.getD [] := by
          subst hctx
          show V.codes.getD c.core.context.accountCodes = V.codes.getD []
          rw [hcc]
        rw [← hacc]
        subst hW
        apply codeIn_snapshot
        · subst hrt0 hst; exact hde
        · subst hctx; exact hcb
        · subst hctx; exact hch
        · rw [hacc]; exact hkeys
        · rw [hctxs]; decide
        · exact hx
      · exact hsize _ _ _ _ hans
    · simp only [tryTail, decodeCallResponse] at hrun
      cases hs : a.success
      · simp only [hs, Bool.false_eq_true, ↓reduceIte, findMatch_nil] at hrun
        simp only [sbind_pure, map_pure', foldAns_pure, Result.mapRuntime, FunctionDef.callBodyResult,
          RevertData.fromRawBytes, normByte_bytes] at hrun
        have hout : ∀ out, ABI.Contract.encodeRevertData? c.core
            (if (byteArrayToBytes a.returnData == []) = true then SolidCore.Solidity.Source.RevertData.empty
              else SolidCore.Solidity.Source.RevertData.raw (byteArrayToBytes a.returnData)).untagFixedBytes = some out →
            out = byteArrayToBytes a.returnData := by
          intro out h
          split at h
          · rename_i he
            simp only [beq_iff_eq] at he
            simp only [RevertData.untagFixedBytes, ABI.Contract.encodeRevertData?, Option.some.injEq] at h
            rw [← h, he]
          · simp only [RevertData.untagFixedBytes, ABI.Contract.encodeRevertData?, Option.some.injEq] at h
            rw [← h]
            exact normByte_bytes a.returnData
        simp only [Option.bind_eq_bind, Option.map_bind] at hrun
        obtain ⟨out, hout', hobs⟩ := Option.bind_eq_some_iff.mp hrun
        rw [hout out hout'] at hobs
        simp only [Function.comp, Option.map_some, Option.some.injEq] at hobs
        rw [← hobs]
        simp only [Source.observe, FeeOn.obsOf, hs, Bool.false_eq_true, ↓reduceIte, byteArrayToBytes_eq]
        rfl
      · simp only [hs, ↓reduceIte, normByte_bytes, List.map_cons, List.map_nil] at hrun
        by_cases hlen : (byteArrayToBytes a.returnData).length < 32
        · rw [decode_short_addr _ hlen] at hrun
          simp only [sbind_pure, map_pure', foldAns_pure, Result.mapRuntime, FunctionDef.callBodyResult,
            RevertData.untagFixedBytes, ABI.Contract.encodeRevertData?, Option.bind_eq_bind, Option.bind_some,
            Option.map_some, Option.some.injEq] at hrun
          have hsz : a.returnData.size < 32 := by
            rw [byteArrayToBytes_eq, List.length_map, List.length_range] at hlen; exact hlen
          rw [← hrun]
          simp only [Source.observe, FeeOn.obsOf, hs, ↓reduceIte, hsz, Bool.false_eq_true]
          rfl
        · rw [decode_addr _ (by omega)] at hrun
          simp only [normByte_bytes] at hrun
          generalize hw : bytesToWordBE (List.take 32 (byteArrayToBytes a.returnData)) = w at hrun
          have hwlt : w < 2 ^ 256 := by rw [← hw]; exact Nat.mod_lt _ (by decide)
          have hsz : 32 ≤ a.returnData.size := by
            rw [byteArrayToBytes_eq, List.length_map, List.length_range] at hlen; omega
          have hv : (Sync.retWord a).toNat = w := by rw [retWord_toNat a hsz, hw]
          by_cases hc : w < 2 ^ 160
          · rw [if_pos hc] at hrun
            have hbind : BindingDecl.bindArgs? [{ name := "__ext0", ty := Ty.address }] [Value.word w] =
                some [("__ext0", Value.word w)] := by
              simp [BindingDecl.bindArgs?, BindingDecl.bindArg?, Ty.coerceValue?, SolidCore.Solidity.Shared.norm,
                Nat.mod_eq_of_lt hwlt]
            simp only [show AbiCleanups.acceptOrUnspecified [AbiCleanup.none] [Value.word w] = true by
                simp [AbiCleanups.acceptOrUnspecified, AbiCleanups.accept, AbiCleanup.accepts],
              hbind, ↓reduceIte] at hrun
            let ρ : Val := ⟨[], slotValue σ, solHash⟩
            let E : EraseEnv := { fields := callsFields, events := ctx.eventDecls, tbl := c.core.table }
            let S1 : SymState := ⟨[[("__ext0", .lit w)], [("_sol_hoist_0", .lit 0), ("_sol_hoist_1", .lit 0)], [], [("on", .lit 0)]], [], []⟩
            have hrel1 : StmtRel ρ E ctx (((({ state := adoptWorld a.postWorld ctx ((rt0.pushScope.pushScope.declareLocal "_sol_hoist_1" (Value.word 0)).declareLocal "_sol_hoist_0" Ty.address.defaultValue).state, locals := ((rt0.pushScope.pushScope.declareLocal "_sol_hoist_1" (Value.word 0)).declareLocal "_sol_hoist_0" Ty.address.defaultValue).locals, memory := ((rt0.pushScope.pushScope.declareLocal "_sol_hoist_1" (Value.word 0)).declareLocal "_sol_hoist_0" Ty.address.defaultValue).memory, nextMemory := ((rt0.pushScope.pushScope.declareLocal "_sol_hoist_1" (Value.word 0)).declareLocal "_sol_hoist_0" Ty.address.defaultValue).nextMemory, nextMemoryByte := ((rt0.pushScope.pushScope.declareLocal "_sol_hoist_1" (Value.word 0)).declareLocal "_sol_hoist_0" Ty.address.defaultValue).nextMemoryByte } : Runtime).recordExternalInteraction (ExternalInteraction.lowLevelCall { kind := Solidity.Shared.Call.ExternalCallKind.staticcall, target := Solidity.Shared.norm (fieldValue (slotValue σ 0) factoryField.packedOffset 20), calldata := [normByte 1, normByte 126, normByte 126, normByte 88], value := Solidity.Shared.norm 0, success := true, output := byteArrayToBytes a.returnData })).withFrame [("__ext0", Value.word w)])) S1 :=
              { fields := hctxf
                events := rfl
                checked := by subst hctx; rfl
                sender := by subst hctx; rfl
                hash := rfl
                ok := slotValue_store σ
                frames := by
                  subst hrt0
                  simp [Runtime.withFrame, Runtime.recordExternalInteraction, Runtime.declareLocal,
                    Runtime.pushScope, frameOf, S1, WExpr.eval, Nat.mod_eq_of_lt hwlt]
                  simp [LocalEnv.declare, Ty.defaultValue]
                store := by
                  intro j hj
                  show (adoptWorld a.postWorld ctx
                    ((rt0.pushScope.pushScope.declareLocal "_sol_hoist_1" (Value.word 0)).declareLocal "_sol_hoist_0" Ty.address.defaultValue).state).loadSlot j = slotValue σ j
                  have hadopt : ∀ X, (adoptWorld a.postWorld ctx X).loadSlot j = storageIn a.postWorld j := by
                    intro X
                    simp only [adoptWorld, State.loadSlot, storageIn, accountIn, hctxs]
                    cases StorageMap.lookup? _ j <;> rfl
                  rw [hadopt, hstatic _ _ _ _ hans (by subst hR; rfl) j, hworld j hj, Nat.mod_eq_of_lt (hlt j)]
                logs := by
                  subst hrt0 hst
                  show List.map logOf d.events = List.map (Log.eval ρ) []
                  rw [hd.events]
                  rfl
                facts := by intro p hp; cases hp }
            obtain ⟨r1, hr1, hl1⟩ := eval_stmt ρ E ctx (k + 2) (Stmt.assign (LValue.var "_sol_hoist_0")
              (Expr.var "__ext0")) S1 _ rfl _ hrel1
            rw [hr1] at hrun
            let S1' : SymState := ⟨[[("__ext0", .lit w)], [("_sol_hoist_0", .lit w), ("_sol_hoist_1", .lit 0)], [], [("on", .lit 0)]], [], []⟩
            have hl1' : LeafRel ρ E ctx r1 (.normal S1') := hl1
            cases r1 with
            | normal rt1 =>
              have hrel2 : StmtRel ρ E ctx rt1.popScope S1'.pop := StmtRel.popScope hl1'
              obtain ⟨r2, hr2, hl2⟩ := eval_stmt ρ E ctx (k + 2 + 1) (Stmt.assign (LValue.var "on")
                (Expr.binary BinaryOp.ne (Expr.var "_sol_hoist_0") (Expr.var "_sol_hoist_1"))) S1'.pop _ rfl _ hrel2
              simp only [done_bind', Result.mapRuntime, sbind_pure] at hrun
              rw [hr2] at hrun
              let ON : WExpr := .un .iszero (.bin .eq (.lit w) (.lit 0))
              let S3 : SymState := ⟨[[("_sol_hoist_0", .lit w), ("_sol_hoist_1", .lit 0)], [], [("on", ON)]], [], []⟩
              have hl2' : LeafRel ρ E ctx r2 (.normal S3) := hl2
              cases r2 with
              | normal rt2 =>
                obtain ⟨r3, hr3, hl3⟩ := eval_stmt ρ E ctx (k + 2 + 1) (Stmt.ifElse (Expr.var "on")
                  (Stmt.assign (LValue.storage "kLast") (Expr.word 1)) Stmt.skip) S3 _ rfl _ hl2'
                simp only [done_bind', sbind_pure] at hrun
                rw [hr3] at hrun
                let S4 : SymState := ⟨S3.scopes, [(.lit 3, writeField (.init 3) (.lit 1) 0 32)], []⟩
                have hl3' : LeafRel ρ E ctx r3 (if ON.eval ρ = 0 then .normal S3 else .normal S4) := hl3
                have hON : ON.eval ρ = if w = 0 then 0 else 1 := by
                  have hwlt' : w < 115792089237316195423570985008687907853269984665640564039457584007913129639936 := hwlt
                  simp [ON, WExpr.eval, UnOp.eval, BinOp.eval, Generic.wordSize, Nat.mod_eq_of_lt hwlt']
                  by_cases hw0 : w = 0 <;> simp [hw0]
                have hsz' : ¬ a.returnData.size < 32 := by omega
                have hlo : ¬ 2 ^ 160 ≤ (Sync.retWord a).toNat := by rw [hv]; exact Nat.not_le_of_lt hc
                by_cases hw0 : w = 0
                · rw [hON, if_pos hw0, if_pos rfl] at hl3'
                  cases r3 with
                  | normal rt3 =>
                    have hrel3 : StmtRel ρ E ctx rt3 S3 := hl3'
                    simp only [done_bind', sbind_pure, evalList_nil, Result.mapRuntime, map_pure', foldAns_pure,
                      FunctionDef.callBodyResult] at hrun
                    have hloc : rt3.popScope.popScope.lookupLocal? "on" = some (Value.word 0) := by
                      simp [Runtime.popScope, Runtime.lookupLocal?, hrel3.frames, S3, S3, frameOf, LocalEnv.lookup?,
                        hON, hw0, Frame.lookup?]
                    have hcr : feeOnFn.collectReturns rt3.popScope.popScope = .ok [.word 0] := by
                      simp [FunctionDef.collectReturns, collectReturnBindings, collectReturnBindings.collect, feeOnFn, hloc,
                        deref_word, Ty.coerceValue?]
                      rfl
                    rw [hcr] at hrun
                    have henc : ABI.encodeValues? (List.map BindingDecl.ty feeOnFn.returns) [Value.word 0] =
                        some (FeeOn.wordBytes 0) := by decide
                    simp only [List.map_cons, List.map_nil, Value.untagFixedBytes, henc, Option.bind_eq_bind,
                      Option.bind_some, Option.map_some, Option.some.injEq] at hrun
                    have hev : rt3.state.events = [] := by
                      have := hrel3.logs
                      simp only [S3, S3, List.map_nil, List.map_eq_nil_iff] at this
                      exact this
                    rw [← hrun]
                    have hret : Sync.retWord a = 0 := BitVec.eq_of_toNat_eq (by rw [hv, hw0]; rfl)
                    simp only [Source.observe, FeeOn.obsOf, hs, ↓reduceIte, hsz', hlo, hret, Runtime.popScope,
                      State.logEntries, hev, List.map_nil]
                    rw [if_neg (by decide)]
                    congr 1
                    funext slot
                    rw [loadSlot_eq rt3.state S3.writes ρ (slotValue_store σ) hrel3.store slot]
                    simp only [S3, Writes.store, Machine.State.initial, BitVec.toNat_ofNat]
                    show slotValue σ slot = _
                    rw [← slotValue_store σ slot]
                    rfl
                  | _ => exact absurd hl3' id
                · rw [hON, if_neg hw0, if_neg (by decide)] at hl3'
                  cases r3 with
                  | normal rt3 =>
                    have hrel3 : StmtRel ρ E ctx rt3 S4 := hl3'
                    simp only [done_bind', sbind_pure, evalList_nil, Result.mapRuntime, map_pure', foldAns_pure,
                      FunctionDef.callBodyResult] at hrun
                    have hloc : rt3.popScope.popScope.lookupLocal? "on" = some (Value.word 1) := by
                      simp [Runtime.popScope, Runtime.lookupLocal?, hrel3.frames, S4, S3, frameOf, LocalEnv.lookup?,
                        hON, hw0, Frame.lookup?]
                    have hcr : feeOnFn.collectReturns rt3.popScope.popScope = .ok [.word 1] := by
                      simp [FunctionDef.collectReturns, collectReturnBindings, collectReturnBindings.collect, feeOnFn, hloc,
                        deref_word, Ty.coerceValue?]
                      rfl
                    rw [hcr] at hrun
                    have henc : ABI.encodeValues? (List.map BindingDecl.ty feeOnFn.returns) [Value.word 1] =
                        some (FeeOn.wordBytes 1) := by decide
                    simp only [List.map_cons, List.map_nil, Value.untagFixedBytes, henc, Option.bind_eq_bind,
                      Option.bind_some, Option.map_some, Option.some.injEq] at hrun
                    have hev : rt3.state.events = [] := by
                      have := hrel3.logs
                      simp only [S4, S3, List.map_nil, List.map_eq_nil_iff] at this
                      exact this
                    rw [← hrun]
                    have hret : ¬ Sync.retWord a = 0 := fun h => hw0 (by rw [← hv, h]; rfl)
                    simp only [Source.observe, FeeOn.obsOf, hs, ↓reduceIte, hsz', hlo, hret, Runtime.popScope,
                      State.logEntries, hev, List.map_nil]
                    congr 1
                    funext slot
                    rw [loadSlot_eq rt3.state S4.writes ρ (slotValue_store σ) hrel3.store slot]
                    simp only [S4, Writes.store, Machine.update, Machine.State.initial]
                    rw [writeField_eval ρ _ _ (by decide) (by decide)]
                    by_cases h2 : slot % 2 ^ 256 = 3
                    · have hb : BitVec.ofNat 256 slot = 3 := by
                        apply BitVec.eq_of_toNat_eq; simpa using h2
                      rw [if_pos hb]
                      have h2' : slot % 115792089237316195423570985008687907853269984665640564039457584007913129639936 = 3 := h2
                      simp [WExpr.eval, Generic.wordSize, h2', fieldWrite]
                    · have hb : BitVec.ofNat 256 slot ≠ 3 := by
                        intro h; apply h2; have := congrArg BitVec.toNat h; simpa using this
                      rw [if_neg hb]
                      have h2' : ¬ slot % 115792089237316195423570985008687907853269984665640564039457584007913129639936 = 3 := h2
                      have hne : ¬ ((WExpr.lit 3).eval ρ = slot % Generic.wordSize) := by
                        intro h; apply h2'; simpa [WExpr.eval, Generic.wordSize] using h.symm
                      rw [if_neg hne]
                      simp only [BitVec.toNat_ofNat]
                      show slotValue σ slot = _
                      rw [← slotValue_store σ slot]
                      rfl
                  | _ => exact absurd hl3' id
              | _ => exact absurd hl2' id
            | _ => exact absurd hl1' id
          · rw [if_neg hc] at hrun
            simp only [sbind_pure, map_pure', foldAns_pure, Result.mapRuntime, FunctionDef.callBodyResult,
              RevertData.untagFixedBytes, ABI.Contract.encodeRevertData?, Option.bind_eq_bind, Option.bind_some,
              Option.map_some, Option.some.injEq] at hrun
            rw [← hrun]
            have h1 : ¬ a.returnData.size < 32 := by omega
            have h2 : 2 ^ 160 ≤ (Sync.retWord a).toNat := by rw [hv]; exact Nat.le_of_not_lt hc
            simp only [Source.observe, FeeOn.obsOf, hs, ↓reduceIte, h1, h2, Bool.false_eq_true]
            rfl


/-- info: 'SolidCore.Refinement.CallFamilies.feeOn_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms feeOn_source

/-- **feeOn's source stage in the world V**: under every oracle that agrees with V
(CallsAgree o V), solar's stage0 runs feeOn() as SolidCore runs it in V, from every storage whose
factory is not the contract itself, with the hypotheses of sync_stage_in. -/
theorem feeOn_stage_in (k : Nat) (V : World) {c : SolidCore.Solidity.TypeCheck.CheckedContract}
    {d : SolidCore.Solidity.Source.State} (hd : Wide.DeployedAt (k + 5) c d [])
    (hfind : c.core.findFunctionBySelector? 1328766218 = some feeOnFn)
    (hfields : c.core.storageFields = callsFields)
    (hdt : d.transient.toList = []) (hde : d.envWorld? = none)
    (hcb : c.core.context.accountBalances = []) (hch : c.core.context.accountCodehashes = [])
    (hcc : c.core.context.accountCodes = []) (hkeys : ∀ p ∈ V.codes.getD [], p.1 < 2 ^ 160)
    (hsize : ∀ h world request a, V.ans h (.external world (.call request)) = some a →
      a.returnData.size < 2 ^ 256)
    (o : Machine.Oracle) (agree : CallsAgree o V) :
    Stage (solidCoreIn V (k + 5)) (MIR.Lowered.moduleSem o) c SolarTV.Export.Calls.stage0
      (fun call => ∃ σ, slotValue σ 0 % 2 ^ 160 ≠ selfAddress ∧ call = FeeOn.feeOnCall σ) :=
  feeOn_stage (k + 5) c V _ (fun σ hσ => feeOn_source k V hd hfind hfields
    (fun h w r a ha hk slot => (agree.static h w r a ha hk slot).1) hdt hde hcb hch hcc hkeys hsize σ hσ)
    o agree

/-- info: 'SolidCore.Refinement.CallFamilies.feeOn_stage_in' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms feeOn_stage_in

end SolidCore.Refinement.CallFamilies

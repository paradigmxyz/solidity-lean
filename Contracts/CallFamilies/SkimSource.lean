import Contracts.CallFamilies.PayRun
import Contracts.CallFamilies.SkimAgree
import Contracts.CallFamilies.Core

namespace SolidCore.Refinement.CallFamilies

open SolarTV SolidCore.Refinement SolidCore.Refinement.Generic SolidCore.Refinement.CallNode
open SolidCore.Solidity.Source EvmCompiler.Simulation

/-- The name of pay in Calls' function table. -/
def payName : String :=
  "__internal_pay(address,uint256)#[SolidCore.Solidity.Ty.address false, SolidCore.Solidity.Ty.uint 256]"

/-- pay, as the checker lowers it. -/
def payFn : InternalFunction :=
  { name := payName,
    params := [{ name := "to", ty := Ty.address, isStorageRef := false },
               { name := "amount", ty := Ty.uint256, isStorageRef := false }],
    returns := [],
    body := payBody }

/-- The checked sub of skim: balance - reserve. -/
def skimAmtE : Expr :=
  Expr.castOp CastKind.uintCleanup 256 (Expr.castOp CastKind.uintCleanup 256
    (Expr.binary BinaryOp.sub (Expr.castOp CastKind.uintCleanup 256 (Expr.var "_sol_hoist_0"))
      (Expr.castOp CastKind.uintCleanup 256 (Expr.var "_sol_hoist_1"))))

/-- skim's balance read. -/
def skimTryS : Stmt :=
  Stmt.tryExternalCall (SolidCore.Solidity.Shared.Call.ExternalCallKind.staticcall)
    (Expr.storageRead (StorageReadMode.ref) "token" [])
    (Expr.encode (EncodeKind.withSelector) (some (Expr.word 1889567281)) [] [Ty.address] [Expr.self])
    (Expr.word 0) none false false
    [{ name := "__ext0", ty := Ty.uint256, isStorageRef := false }]
    [AbiCleanup.uint 256]
    (Stmt.assign (LValue.var "_sol_hoist_0") (Expr.castOp (CastKind.uintCleanup) 256 (Expr.var "__ext0")))
    []

/-- skim's call of pay. -/
def skimPayS : List Stmt :=
  [Stmt.varDecl Ty.address "_ic_arg_0" (some (Expr.var "_sol_hoist_2")),
   Stmt.varDecl Ty.uint256 "_ic_arg_1" (some skimAmtE),
   Stmt.captureReturn [] (Stmt.internalCall [] payName [Expr.var "_ic_arg_0", Expr.var "_ic_arg_1"])]

/-- SolidCore's skim(address) of Calls, as the checker lowers it. -/
def skimFn : FunctionDef :=
{ name := "skim",
  selector? := some 3156594551,
  payable := false,
  params := [{ name := "to", ty := Ty.address, isStorageRef := false }],
  paramAbiCleanups := [AbiCleanup.none],
  returns := [],
  body := Stmt.block [Stmt.skip, Stmt.block
    [Stmt.varDecl Ty.address "_sol_hoist_2" (some (Expr.var "to")),
     Stmt.varDecl Ty.uint256 "_sol_hoist_1"
       (some (Expr.castOp CastKind.uintCleanup 256 (Expr.storageRead StorageReadMode.ref "reserve" []))),
     Stmt.varDecl Ty.uint256 "_sol_hoist_0" none,
     skimTryS,
     Stmt.block skimPayS]],
  dispatchId? := none }

/-- Calls's reserve field. -/
def reserveField : StorageField :=
  { name := "reserve", slot := 2, ty? := some Ty.uint256, layout? := some (StorageLayout.scalar Ty.uint256),
    transient := false, packedOffset := 0, packedBytes := 32, packedSigned := false }

theorem reserve_eval (ctx : Context) (rt : Runtime) (hf : FieldOk ctx "reserve" reserveField)
    (hw : rt.state.loadSlot reserveField.slot < Generic.wordSize) :
    Expr.eval ctx rt (Expr.castOp CastKind.uintCleanup 256 (Expr.storageRead StorageReadMode.ref "reserve" [])) =
      EvmCompiler.Simulation.Interaction.done (.ok (.word (fieldValue (rt.state.loadSlot reserveField.slot) 0 32), rt)) := by
  simp only [Expr.eval, Expr.orderFuel]
  rw [Expr.evalFuel]
  simp only [Expr.evalFuel, load_field hf hw]
  have hv : fieldValue (rt.state.loadSlot reserveField.slot) 0 32 < 2 ^ 256 := by
    simp only [fieldValue]; split <;> omega
  simp only [liftM, monadLift, MonadLift.monadLift, SolI.ofExcept, bind_done_ok,
    show reserveField.packedOffset = 0 from rfl, show reserveField.packedBytes = 32 from rfl]
  rw [sbind_pure]; dsimp only
  rw [cleanup256 _ _ hv]
  rfl

theorem varE (ctx : Context) (rt : Runtime) (x : String) (w : Nat)
    (hb : rt.lookupStorageBase? x = none) (hl : rt.lookupLocal? x = some (.word w)) :
    Expr.eval ctx rt (Expr.var x) = EvmCompiler.Simulation.Interaction.done (.ok (.word w, rt)) := by
  simp only [Expr.eval, Expr.orderFuel]
  exact varF 1 ctx rt x w hb hl

theorem assign_cast_var (n : Nat) (tbl : FunctionTable) (ctx : Context) (rt : Runtime) (x y : String) (w : Nat)
    (hw : w < 2 ^ 256) (L : LocalEnv)
    (hbx : rt.lookupStorageBase? x = none) (hmx : rt.lookupMemoryRef? x = none)
    (hlx : ∃ v, rt.lookupLocal? x = some (.word v))
    (hby : rt.lookupStorageBase? y = none) (hly : rt.lookupLocal? y = some (.word w))
    (hL : LocalEnv.assign? rt.locals x (.word w) = some L) :
    Stmt.eval (n + 1) tbl ctx rt (Stmt.assign (LValue.var x) (Expr.castOp CastKind.uintCleanup 256 (Expr.var y))) =
      pure (Result.normal { rt with locals := L }) := by
  obtain ⟨v, hv⟩ := hlx
  rw [Stmt.eval]; dsimp only
  simp only [LValue.wantsMemoryRefRhs, hmx, Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
  rw [castVar_eval ctx rt y w hw hby hly]
  rw [caught_done_ok, bind_done_ok]; dsimp only
  rw [resolve_var ctx rt x (.word v) hbx hv, caught_done_ok, bind_done_ok]; dsimp only
  simp [ResolvedLValue.write, Runtime.assignLocal?, hv, Value.coerceLike?, hL]
  done

theorem amt_eval (ctx : Context) (rt : Runtime) (w r : Nat) (hw : w < 2 ^ 256) (hr : r < 2 ^ 256)
    (hc : ctx.checked = true)
    (hb0 : rt.lookupStorageBase? "_sol_hoist_0" = none) (hl0 : rt.lookupLocal? "_sol_hoist_0" = some (.word w))
    (hb1 : rt.lookupStorageBase? "_sol_hoist_1" = none) (hl1 : rt.lookupLocal? "_sol_hoist_1" = some (.word r)) :
    Expr.eval ctx rt skimAmtE =
      if w < r then EvmCompiler.Simulation.Interaction.done (.error (.revert .overflow))
      else EvmCompiler.Simulation.Interaction.done (.ok (.word (w - r), rt)) := by
  simp only [Expr.eval, skimAmtE, Expr.orderFuel]
  simp only [Expr.evalFuel]
  simp [hb0, hl0, hb1, hl1, Runtime.derefMemoryValue, liftM, monadLift, MonadLift.monadLift, SolI.ofExcept,
    bind_done_ok, ipure_eq, cleanup256 _ _ hw, cleanup256 _ _ hr, BinaryOp.apply, hc, sbind_pure,
    Value.forceAbiLazy, BinaryOp.preservesFixedBytesWidth, BinaryOp.applyWord, checkedSub]
  have hnw : SolidCore.Solidity.Shared.norm w = w := Nat.mod_eq_of_lt hw
  have hnr : SolidCore.Solidity.Shared.norm r = r := Nat.mod_eq_of_lt hr
  by_cases hlt : w < r
  · simp [hnw, hnr, hlt, bind_done_ok, tbind, throw_eq, bind, Except.bind, pure, Except.pure]
    done
  · have hsub : SolidCore.Solidity.Shared.subWord w r = w - r := by
      rw [subWord_eq w r hw hr]
      have hge : r ≤ w := by omega
      have : w + (Generic.wordSize - r) = (w - r) + Generic.wordSize := by
        have : r < Generic.wordSize := hr
        omega
      rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by have : w < Generic.wordSize := hw; omega)]
    have hd : w - r < 2 ^ 256 := by omega
    simp [hnw, hnr, hlt, hsub, bind_done_ok, cleanup256 _ _ hd, sbind_pure, ipure_eq, bind, Except.bind, pure,
      Except.pure]
    done

theorem refArg_var (ctx : Context) (rt : Runtime) (x : String) (w : Nat)
    (hb : rt.lookupStorageBase? x = none) (hm : rt.lookupMemoryRef? x = none)
    (hl : rt.lookupLocal? x = some (.word w)) :
    Expr.evalRefArg ctx rt (Expr.var x) = EvmCompiler.Simulation.Interaction.done (.ok (.word w, rt)) := by
  simp only [Expr.evalRefArg, hb, hm]
  exact varE ctx rt x w hb hl

theorem refArgs2 (ctx : Context) (rt : Runtime) (x y : String) (v w : Nat)
    (hbx : rt.lookupStorageBase? x = none) (hmx : rt.lookupMemoryRef? x = none)
    (hlx : rt.lookupLocal? x = some (.word v))
    (hby : rt.lookupStorageBase? y = none) (hmy : rt.lookupMemoryRef? y = none)
    (hly : rt.lookupLocal? y = some (.word w)) :
    Expr.evalRefArgList ctx rt [Expr.var x, Expr.var y] =
      EvmCompiler.Simulation.Interaction.done (.ok ([.word v, .word w], rt)) := by
  simp only [Expr.evalRefArgList, Expr.listEvalFuel, Expr.orderFuel]
  simp only [Expr.evalRefArgListFuel, refArg_var ctx rt x v hbx hmx hlx, refArg_var ctx rt y w hby hmy hly,
    bind_done_ok]
  rfl

theorem pay_frame (v w : Nat) (hv : v < 2 ^ 160) (hw : w < 2 ^ 256) :
    payFn.initialFrame? [.word v, .word w] = some [("to", .word v), ("amount", .word w)] := by
  simp [InternalFunction.initialFrame?, payFn, BindingDecl.bindArgsRef?, BindingDecl.bindArgRef?,
    InternalFunction.returnDefaultBindings, BindingDecl.bindArg?, coerce_param (Or.inr rfl) v,
    coerce_param (Or.inl rfl) w]

theorem bytes_roundtrip (l : List Nat) : byteArrayToBytes (bytesToByteArray l) = l.map (· % 256) := by
  simp [byteArrayToBytes, bytesToByteArray, toList_eq_data]
  done

theorem srcBytesBE_eq : ∀ (n v : Nat),
    wordToBytesBE n v = (List.range n).map fun i => v / 256 ^ (n - 1 - i) % 256
  | 0, _ => rfl
  | n + 1, v => by
    rw [wordToBytesBE, srcBytesBE_eq n (v / 256), List.range_succ, List.map_append]
    congr 1
    · apply List.map_congr_left
      intro i hi
      simp only [List.mem_range] at hi
      rw [Nat.div_div_eq_div_mul, ← Nat.pow_succ', show (n - 1 - i).succ = n + 1 - 1 - i by omega]
    · simp [normByte, SolidCore.Solidity.Shared.Account.byte]

theorem input_eq (σ : List (Nat × Nat)) (dst : Nat) (a : CallResponse) (w : Nat)
    (hv : (Sync.retWord a).toNat = w) (hge : slotValue σ 2 ≤ w) :
    List.map (fun x => x % 256) (List.map normByte (payInput dst (w - slotValue σ 2))) =
      Skim.transferInput σ dst a := by
  have hr : slotValue σ 2 < 2 ^ 256 := slotValue_lt σ 2
  have hamt : (Skim.amtW σ a).toNat = w - slotValue σ 2 := by
    unfold Skim.amtW
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hr, hv]; exact hge),
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt hr, hv]
  rw [Skim.transferInput, hamt, payInput, srcBytesBE_eq, srcBytesBE_eq]
  simp [Skim.wordBE, normByte, SolidCore.Solidity.Shared.Account.byte, wordBytes_eq]
  congr 1 <;> apply List.map_congr_left <;> intro i _ <;> simp [Function.comp, normByte,
    SolidCore.Solidity.Shared.Account.byte, Nat.mod_mod]

/-- SolidCore's Error("TRANSFER_FAILED") bytes. -/
def errB : Option (List OByte) := errorBytes "TRANSFER_FAILED"

kernel_rfl errB_eq errB (some (Skim.errData.map OByte.lit)) using SolidCore.Verify.VC.Calls.selector_eq

theorem errB_eq' : errorBytes "TRANSFER_FAILED" = some (Skim.errData.map OByte.lit) := errB_eq

theorem skimCall_eq (σ : List (Nat × Nat)) (dst : Nat) :
    Skim.skimCall σ dst = Evm.Wide.callAt 3156594551 [BitVec.ofNat 256 dst] σ := rfl

set_option maxHeartbeats 4000000 in
theorem skim_source (k : Nat) (V : World) {c : SolidCore.Solidity.TypeCheck.CheckedContract}
    {d : SolidCore.Solidity.Source.State} (hd : Wide.DeployedAt (k + 8) c d [])
    (hfind : c.core.findFunctionBySelector? 3156594551 = some skimFn)
    (hpay : c.core.table.lookup? payName = some payFn)
    (hfields : c.core.storageFields = callsFields)
    (hstatic : StaticKeeps V)
    (hstaticT : ∀ h world request a, V.ans h (.external world (.call request)) = some a →
      request.kind = .staticcall → ∀ slot, transientIn a.postWorld slot = transientIn world slot) (hdt : d.transient.toList = []) (hde : d.envWorld? = none)
    (hcb : c.core.context.accountBalances = []) (hch : c.core.context.accountCodehashes = [])
    (hcc : c.core.context.accountCodes = []) (hkeys : ∀ p ∈ V.codes.getD [], p.1 < 2 ^ 160)
    (hsize : ∀ h world request a, V.ans h (.external world (.call request)) = some a →
      a.returnData.size < 2 ^ 256)
    (hsize64 : ∀ h world request a, V.ans h (.external world (.call request)) = some a →
      a.returnData.size < 2 ^ 64) (σ : List (Nat × Nat)) (dst : Nat) (hdst : dst < 2 ^ 160)
    (hself : slotValue σ 1 % 2 ^ 160 ≠ selfAddress) : Skim.SkimSource (k + 8) c V σ dst := by
  have hlt := slotValue_lt σ
  intro obs hrun
  rw [skimCall_eq, runIn_eq_at V hd] at hrun
  simp only [Source.ABI.Oracle.callCalldata, Dirty.readSelector_calldata _ (by decide : 3156594551 < 2 ^ 32), hfind] at hrun
  have hdst' : (BitVec.ofNat 256 dst).toNat = dst := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (lt_trans hdst (by decide))]
  simp only [List.map_cons, List.map_nil, hdst'] at hrun
  rw [show List.drop ABI.selectorBytes (List.map (fun x => x.toNat) (EthLib.Base.natToBytes 4 3156594551) ++
      Dirty.argBytes [dst]) = Dirty.argBytes [dst] by simp [ABI.selectorBytes, EthLib.Base.natToBytes_length],
    decode_args (ws := [160]) rfl [dst] rfl (by simp; exact lt_trans hdst (by decide))] at hrun
  have hcl : argsClean [160] [dst] = true := by simp [argsClean]; omega
  simp only [hcl, ↓reduceIte, show skimFn.acceptsValue 0 = true from rfl, List.map_cons, List.map_nil] at hrun
  generalize hctx : ABI.Contract.callContextAtWithBase c.core (ctxIn V c) selfAddress callerAddress 0
    (List.map (fun x => x.toNat) (EthLib.Base.natToBytes 4 3156594551) ++ Dirty.argBytes [dst]) = ctx at hrun
  generalize hst : ({ d with storage := σ.foldl (fun acc kv => acc.insertLoop kv.1 kv.2) d.storage } :
    SolidCore.Solidity.Source.State) = st0 at hrun
  have hctxv : ctx.value = 0 := by subst hctx; rfl
  have hctxs : ctx.self = selfAddress := by subst hctx; rfl
  have hframe : skimFn.initialFrame? [Value.word dst] = some [("to", Value.word dst)] := by
    simp [FunctionDef.initialFrame?, skimFn, BindingDecl.bindArgs?, BindingDecl.bindArg?,
      coerce_param (Or.inr rfl) dst, FunctionDef.returnDefaultBindings]
  simp only [Source.callAns, FunctionDef.call, FunctionDef.evalBodyEntry, hctxv,
    show skimFn.acceptsValue 0 = true from rfl, ↓reduceIte, hframe, Option.map_some, Option.bind_some] at hrun
  generalize hrt0 : ({ state := { st0 with selfBalance := Solidity.Shared.addWord (Solidity.Shared.Account.balanceAt ctx.accountBalances ctx.self) 0, worldMutatedSinceAdoption := true }, locals := [[("to", Value.word dst)]] } : Runtime) = rt0 at hrun
  have hrt0l : rt0.locals = [[("to", Value.word dst)]] := by rw [← hrt0]
  rw [show skimFn.body = Stmt.block [Stmt.skip, Stmt.block
    [Stmt.varDecl Ty.address "_sol_hoist_2" (some (Expr.var "to")),
     Stmt.varDecl Ty.uint256 "_sol_hoist_1"
       (some (Expr.castOp CastKind.uintCleanup 256 (Expr.storageRead StorageReadMode.ref "reserve" []))),
     Stmt.varDecl Ty.uint256 "_sol_hoist_0" none,
     skimTryS,
     Stmt.block skimPayS]] from rfl] at hrun
  rw [eval_block, evalList_cons, eval_skip, sbind_pure] at hrun
  dsimp only at hrun
  rw [evalList_cons, eval_block, evalList_cons, eval_varDecl_some,
    varE ctx _ "to" dst (by simp [Runtime.lookupStorageBase?, Runtime.lookupLocal?, Runtime.pushScope, hrt0l,
      LocalEnv.lookup?, Frame.lookup?]) (by simp [Runtime.lookupLocal?, Runtime.pushScope, hrt0l,
      LocalEnv.lookup?, Frame.lookup?]), caught_done_ok, bind_done_ok] at hrun
  dsimp only at hrun
  rw [coerce_param (Or.inr rfl) dst, sbind_pure] at hrun
  dsimp only at hrun
  have hctxf : ctx.storageFields = callsFields := by subst hctx; exact hfields
  have hfr : FieldOk ctx "reserve" reserveField :=
    ⟨by simp [Context.storageField?, hctxf, callsFields, reserveField, tokenField], rfl, rfl, by decide, by decide,
      by decide⟩
  have hfx : AddrFieldOk ctx "token" tokenField :=
    ⟨by simp [Context.storageField?, hctxf, callsFields, tokenField], rfl, rfl, rfl, by decide, by decide⟩
  have hload : ∀ k, k < Generic.wordSize → st0.loadSlot k = slotValue σ k := by
    intro k hk
    have := getD_storage_cover hd (σ := σ) (by intro kv hkv; simp at hkv) k
    subst hst
    simp only [State.loadSlot, StorageMap.lookup?]
    rw [← this]
    simp only [SolidCore.Solidity.Shared.norm, modulus_eq, Std.HashMap.get?_eq_getElem?]
    cases (List.foldl (fun acc kv => acc.insertLoop kv.1 kv.2) d.storage σ)[k % Generic.wordSize]? <;> rfl
  have hst0 : (rt0.pushScope.pushScope.declareLocal "_sol_hoist_2" (Value.word dst)).state.loadSlot 2 = slotValue σ 2 := by
    rw [← hrt0]; exact hload 2 (by decide)
  rw [evalList_cons, eval_varDecl_some, reserve_eval ctx _ hfr (by rw [show reserveField.slot = 2 from rfl, hst0]; exact hlt 2),
    caught_done_ok, bind_done_ok] at hrun
  dsimp only at hrun
  rw [coerce_param (Or.inl rfl), sbind_pure] at hrun
  dsimp only at hrun
  rw [evalList_cons, eval_varDecl_none, sbind_pure] at hrun
  dsimp only at hrun
  rw [evalList_cons, skimTryS] at hrun
  generalize hR : Runtime.declareLocal _ "_sol_hoist_0" _ = R at hrun
  have hRs : R.state = rt0.state := by rw [← hR]; rfl
  have hRl : R.locals = [[("_sol_hoist_0", Value.word 0),
      ("_sol_hoist_1", Value.word (fieldValue (slotValue σ 2) 0 32)), ("_sol_hoist_2", Value.word dst)], [],
      [("to", Value.word dst)]] := by
    rw [← hR, ← hst0]; simp [Runtime.declareLocal, Runtime.pushScope, LocalEnv.declare, hrt0l, Ty.defaultValue]; rfl
  clear hR
  have hT : R.state.loadSlot tokenField.slot = slotValue σ 1 := by
    rw [hRs, ← hrt0]; exact hload 1 (by decide)
  have ht := tok_eval ctx R hfx (by rw [hT]; exact hlt 1)
  rw [hT] at ht
  have hne : wordEq (SolidCore.Solidity.Shared.norm (fieldValue (slotValue σ 1) tokenField.packedOffset 20)) ctx.self = false := by
    rw [hctxs]
    simp only [wordEq, fieldValue, tokenField, SolidCore.Solidity.Shared.norm]
    simp
    have h1 : slotValue σ 1 % 1461501637330902918203684832716283019655932542976 < Solidity.Shared.wordModulus :=
      lt_of_lt_of_le (Nat.mod_lt _ (by decide)) (by decide)
    rw [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt (by decide : selfAddress < Solidity.Shared.wordModulus)]
    exact hself
  rw [show k + 6 = (k + 5) + 1 from rfl,
    eval_tryCall (k + 5) _ ctx _ _ _ _ _ false _ _ _ _ ht rfl (word0_eval ctx _) rfl (enc_eval ctx _ hctxs) rfl hne] at hrun
  generalize hW : snapshotWorld ctx R.state = world at hrun
  generalize hRq : buildCallRequest ctx Solidity.Shared.Call.ExternalCallKind.staticcall
      (Solidity.Shared.norm (fieldValue (slotValue σ 1) tokenField.packedOffset 20))
      (List.map normByte encSync) (Solidity.Shared.norm 0) none = request at hrun
  simp only [bind_request, map_request] at hrun
  rw [foldAns_request] at hrun
  have hmut : R.state.worldMutatedSinceAdoption = true := by rw [hRs, ← hrt0]
  have hwf : StorageMap.WF R.state.storage := by
    rw [hRs, ← hrt0, ← hst]; exact wf_foldl σ _ (wf_of_toList_nil _ hd.storage)
  have hworld : ∀ slot < 2 ^ 256, storageIn world slot = slotValue σ slot % 2 ^ 256 := by
    intro slot hslot
    have hl := hload slot hslot
    have hsto : R.state.storage = st0.storage := by rw [hRs, ← hrt0]
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
  have htrans : ∀ slot < 2 ^ 256, transientIn world slot = 0 := by
    intro slot hslot
    have htr : R.state.transient = d.transient := by rw [hRs, ← hrt0, ← hst]
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
  have hacc : ctx.accountCodes = V.codes.getD [] := by
    subst hctx
    show V.codes.getD c.core.context.accountCodes = V.codes.getD []
    rw [hcc]
  have hcodes : ∀ x < 2 ^ 160, (codeIn world x).isEmpty =
      (SolidCore.Solidity.Shared.Account.codeAt (V.codes.getD []) x).isEmpty := by
    intro x hx
    rw [← hacc]
    subst hW
    apply codeIn_snapshot
    · rw [hRs, ← hrt0, ← hst]; exact hde
    · subst hctx; exact hcb
    · subst hctx; exact hch
    · rw [hacc]; exact hkeys
    · rw [hctxs]; decide
    · exact hx
  cases hans : V.ans [] (Query.external world (ExternalRequest.call request)) with
  | none => simp [hans] at hrun
  | some a =>
  simp only [hans] at hrun
  have hask : Sync.SyncAsk σ V world request a := by
    refine ⟨hans, by subst hRq; rfl, ?_, by subst hRq; rfl, ?_, hworld, htrans, hcodes, hsize _ _ _ _ hans⟩
    · subst hRq
      simp [buildCallRequest, addressToWord, wordToAddress, wordToU256, fieldValue, tokenField,
        EvmYul.AccountAddress.ofUInt256, SolidCore.Solidity.Shared.norm]
      have h1 : slotValue σ 1 % 1461501637330902918203684832716283019655932542976 <
          Solidity.Shared.wordModulus := lt_of_lt_of_le (Nat.mod_lt _ (by decide)) (by decide)
      rw [Nat.mod_eq_of_lt h1]
      simp [EvmYul.UInt256.ofNat, EvmYul.AccountAddress.size, Fin.ofNat, Id.run, EvmYul.UInt256.size]
    · subst hRq
      show byteArrayToBytes (bytesToByteArray (List.map normByte encSync)) = List.map BitVec.toNat Sync.input
      simp only [byteArrayToBytes, toList_eq_data, bytesToByteArray]
      decide
  refine ⟨world, request, a, hask, ?_⟩
  simp only [tryTail, decodeCallResponse] at hrun
  cases hs : a.success
  · have hE : Skim.Early σ a := Or.inl hs
    refine ⟨fun _ => ?_, fun h => absurd hE h⟩
    simp only [hs, Bool.false_eq_true, ↓reduceIte, findMatch_nil] at hrun
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
    simp only [Source.observe, Skim.obsEarly, Skim.failObs, hs, Bool.false_eq_true, ↓reduceIte, byteArrayToBytes_eq]
    rfl
  · simp only [hs, ↓reduceIte, normByte_bytes, List.map_cons, List.map_nil] at hrun
    by_cases hlen : (byteArrayToBytes a.returnData).length < 32
    · have hsz : a.returnData.size < 32 := by
        rw [byteArrayToBytes_eq, List.length_map, List.length_range] at hlen; exact hlen
      have hE : Skim.Early σ a := Or.inr (Or.inl hsz)
      refine ⟨fun _ => ?_, fun h => absurd hE h⟩
      rw [decode_short _ hlen] at hrun
      simp only [sbind_pure, map_pure', foldAns_pure, Result.mapRuntime, FunctionDef.callBodyResult,
        RevertData.untagFixedBytes, ABI.Contract.encodeRevertData?, Option.bind_eq_bind, Option.bind_some,
        Option.map_some, Option.some.injEq] at hrun
      rw [← hrun]
      simp only [Source.observe, Skim.obsEarly, Skim.failObs, hs, ↓reduceIte, hsz]
      rfl
    · have hsz : 32 ≤ a.returnData.size := by
        rw [byteArrayToBytes_eq, List.length_map, List.length_range] at hlen; omega
      rw [decode_word _ (by omega)] at hrun
      simp only [normByte_bytes] at hrun
      have hv : (Sync.retWord a).toNat = bytesToWordBE (List.take 32 (byteArrayToBytes a.returnData)) :=
        retWord_toNat a hsz
      generalize hw : bytesToWordBE (List.take 32 (byteArrayToBytes a.returnData)) = w at hrun hv
      have hwlt : w < 2 ^ 256 := by rw [← hw]; exact Nat.mod_lt _ (by decide)
      simp only [AbiCleanups.acceptOrUnspecified] at hrun
      have hacc : AbiCleanups.accept [AbiCleanup.uint 256] [Value.word w] = true := by
        simp [AbiCleanups.accept, AbiCleanup.accepts, SolidCore.Solidity.Shared.norm]
        first
          | exact decide_eq_true (Nat.mod_lt w (by decide : 0 < Solidity.Shared.wordModulus))
          | exact Nat.mod_lt w (by decide : 0 < Solidity.Shared.wordModulus)
      have hbind : BindingDecl.bindArgs? [{ name := "__ext0", ty := Ty.uint256 }] [Value.word w] =
          some [("__ext0", Value.word w)] := by
        simp [BindingDecl.bindArgs?, BindingDecl.bindArg?, Ty.coerceValue?, SolidCore.Solidity.Shared.norm,
          Nat.mod_eq_of_lt hwlt]
      simp only [hacc, hbind, Bool.or_true, ↓reduceIte] at hrun
      generalize hQ : Runtime.withFrame _ [("__ext0", Value.word w)] = Q at hrun
      have hQl : Q.locals = [("__ext0", Value.word w)] :: R.locals := by rw [← hQ]; rfl
      rw [hRl] at hQl
      rw [show k + 5 = (k + 4) + 1 from rfl, assign_cast_var (k + 4) _ ctx Q "_sol_hoist_0" "__ext0" w hwlt
        [[("__ext0", Value.word w)], [("_sol_hoist_0", Value.word w),
          ("_sol_hoist_1", Value.word (fieldValue (slotValue σ 2) 0 32)), ("_sol_hoist_2", Value.word dst)], [],
          [("to", Value.word dst)]]
        (by simp [Runtime.lookupStorageBase?, Runtime.lookupLocal?, hQl, LocalEnv.lookup?, Frame.lookup?])
        (by simp [Runtime.lookupMemoryRef?, Runtime.lookupLocal?, hQl, LocalEnv.lookup?, Frame.lookup?])
        ⟨0, by simp [Runtime.lookupLocal?, hQl, LocalEnv.lookup?, Frame.lookup?]⟩
        (by simp [Runtime.lookupStorageBase?, Runtime.lookupLocal?, hQl, LocalEnv.lookup?, Frame.lookup?])
        (by simp [Runtime.lookupLocal?, hQl, LocalEnv.lookup?, Frame.lookup?])
        (by simp [hQl, LocalEnv.assign?, Frame.assign?])] at hrun
      simp only [sbind_pure, Result.mapRuntime] at hrun
      have hres : fieldValue (slotValue σ 2) 0 32 = slotValue σ 2 := by
        have := hlt 2; simp [fieldValue]; done
      rw [hres] at hrun
      generalize hT : Runtime.popScope _ = T at hrun
      have hTl : T.locals = [[("_sol_hoist_0", Value.word w), ("_sol_hoist_1", Value.word (slotValue σ 2)),
          ("_sol_hoist_2", Value.word dst)], [], [("to", Value.word dst)]] := by rw [← hT]; rfl
      rw [evalList_cons, eval_block, skimPayS, evalList_cons, eval_varDecl_some,
        varE ctx _ "_sol_hoist_2" dst (by simp [Runtime.lookupStorageBase?, Runtime.lookupLocal?, Runtime.pushScope, hTl,
          LocalEnv.lookup?, Frame.lookup?]) (by simp [Runtime.lookupLocal?, Runtime.pushScope, hTl,
          LocalEnv.lookup?, Frame.lookup?]), caught_done_ok, bind_done_ok] at hrun
      dsimp only at hrun
      rw [coerce_param (Or.inr rfl), sbind_pure] at hrun
      dsimp only at hrun
      have hctxc : ctx.checked = true := by subst hctx; rfl
      rw [evalList_cons, eval_varDecl_some, amt_eval ctx _ w (slotValue σ 2) hwlt (hlt 2) hctxc
        (by simp [Runtime.lookupStorageBase?, Runtime.lookupLocal?, Runtime.pushScope, Runtime.declareLocal, hTl,
          LocalEnv.declare, LocalEnv.lookup?, Frame.lookup?])
        (by simp [Runtime.lookupLocal?, Runtime.pushScope, Runtime.declareLocal, hTl, LocalEnv.declare,
          LocalEnv.lookup?, Frame.lookup?])
        (by simp [Runtime.lookupStorageBase?, Runtime.lookupLocal?, Runtime.pushScope, Runtime.declareLocal, hTl,
          LocalEnv.declare, LocalEnv.lookup?, Frame.lookup?])
        (by simp [Runtime.lookupLocal?, Runtime.pushScope, Runtime.declareLocal, hTl, LocalEnv.declare,
          LocalEnv.lookup?, Frame.lookup?])] at hrun
      by_cases hlw : w < slotValue σ 2
      · have hE : Skim.Early σ a := Or.inr (Or.inr (by rw [hv]; exact hlw))
        refine ⟨fun _ => ?_, fun h => absurd hE h⟩
        simp only [hlw, ↓reduceIte, caught_revert, bind_done_ok] at hrun
        simp only [sbind_pure, Result.mapRuntime, map_pure', foldAns_pure, FunctionDef.callBodyResult] at hrun
        have hpd : (panicBytes 17).map (OByte.eval ⟨[], fun _ => 0, solHash⟩) = Skim.panicData := by rfl
        simp only [RevertData.overflow, RevertData.untagFixedBytes, encode_panic ⟨[], fun _ => 0, solHash⟩, hpd, Option.bind_some,
          Option.map_some, Option.some.injEq] at hrun
        simp only [bind, Option.bind, Option.map, Option.some.injEq] at hrun
        subst hrun
        have hns : ¬ a.returnData.size < 32 := by omega
        simp only [Source.observe, Skim.obsEarly, Skim.failObs, hs, ↓reduceIte, hns]
        rfl
      have hnE : ¬ Skim.Early σ a := by
        rintro (h | h | h)
        · rw [hs] at h; cases h
        · omega
        · rw [hv] at h; exact hlw h
      refine ⟨fun h => absurd h hnE, fun _ => ?_⟩
      simp only [hlw, ↓reduceIte, caught_done_ok, bind_done_ok] at hrun
      try dsimp only at hrun
      rw [coerce_param (Or.inl rfl), sbind_pure] at hrun
      dsimp only at hrun
      rw [evalList_cons, eval_captureReturn_nil] at hrun
      generalize hU : Runtime.declareLocal _ "_ic_arg_1" _ = U at hrun
      have hUl : U.locals = [[("_ic_arg_1", Value.word (w - slotValue σ 2)), ("_ic_arg_0", Value.word dst)],
          [("_sol_hoist_0", Value.word w), ("_sol_hoist_1", Value.word (slotValue σ 2)),
          ("_sol_hoist_2", Value.word dst)], [], [("to", Value.word dst)]] := by
        rw [← hU]; simp [Runtime.declareLocal, Runtime.pushScope, LocalEnv.declare, hTl]
      have hamt : w - slotValue σ 2 < 2 ^ 256 := lt_of_le_of_lt (Nat.sub_le _ _) hwlt
      rw [show k + 4 = (k + 3) + 1 from rfl, eval_internalCall (k + 3) _ ctx U [] payName _ payFn _ U _
        (refArgs2 ctx U "_ic_arg_0" "_ic_arg_1" dst (w - slotValue σ 2)
          (by simp [Runtime.lookupStorageBase?, Runtime.lookupLocal?, hUl, LocalEnv.lookup?, Frame.lookup?])
          (by simp [Runtime.lookupMemoryRef?, Runtime.lookupLocal?, hUl, LocalEnv.lookup?, Frame.lookup?])
          (by simp [Runtime.lookupLocal?, hUl, LocalEnv.lookup?, Frame.lookup?])
          (by simp [Runtime.lookupStorageBase?, Runtime.lookupLocal?, hUl, LocalEnv.lookup?, Frame.lookup?])
          (by simp [Runtime.lookupMemoryRef?, Runtime.lookupLocal?, hUl, LocalEnv.lookup?, Frame.lookup?])
          (by simp [Runtime.lookupLocal?, hUl, LocalEnv.lookup?, Frame.lookup?]))
        hpay (pay_frame dst _ hdst hamt)] at hrun
      have hUs : U.state.storage = (adoptWorld a.postWorld ctx R.state).storage := by
        rw [← hU, ← hT, ← hQ]; rfl
      have hadopt : ∀ j, (adoptWorld a.postWorld ctx R.state).loadSlot j = storageIn a.postWorld j := by
        intro j
        simp only [adoptWorld, State.loadSlot, storageIn, accountIn, hctxs]
        cases StorageMap.lookup? _ j <;> rfl
      have hpost : ∀ j < 2 ^ 256, storageIn a.postWorld j = slotValue σ j := by
        intro j hj
        rw [hstatic _ _ _ _ hans (by subst hRq; rfl) j, hworld j hj, Nat.mod_eq_of_lt (hlt j)]
      have hU1 : U.state.loadSlot tokenField.slot = slotValue σ 1 := by
        rw [show U.state.loadSlot tokenField.slot = (adoptWorld a.postWorld ctx R.state).loadSlot 1 by
          unfold State.loadSlot; rw [hUs]; rfl, hadopt, hpost 1 (by decide)]
      have hfx' : AddrFieldOk { ctx with checked := true } "token" tokenField :=
        ⟨by simp [Context.storageField?, hctxf, callsFields, tokenField], rfl, rfl, rfl, by decide, by decide⟩
      generalize hP : (⟨U.state, _, U.memory, U.nextMemory, U.nextMemoryByte⟩ : Runtime) = P at hrun
      have hPs : P.state = U.state := by rw [← hP]
      have hPl : P.locals = [[("to", Value.word dst), ("amount", Value.word (w - slotValue σ 2))]] := by rw [← hP]
      obtain ⟨kk, hk, hkk⟩ := pay_run k _ { ctx with checked := true } P dst (w - slotValue σ 2) hdst hamt hPl hfx'
        (by rw [hPs, hU1]; exact hlt 1) (by subst hctx; rfl) (by rw [hPs, hU1]; exact hne)
      rw [show payFn.body = payBody from rfl, hk] at hrun
      simp only [bind_request, map_request] at hrun
      rw [foldAns_request] at hrun
      have hUenv : U.state.envWorld? = some a.postWorld := by rw [← hU, ← hT, ← hQ]; rfl
      have hUmut : U.state.worldMutatedSinceAdoption = false := by rw [← hU, ← hT, ← hQ]; rfl
      have hW2 : snapshotWorld { ctx with checked := true } P.state = a.postWorld := by
        rw [hPs]; simp [snapshotWorld, hUenv, hUmut]
      rw [hW2] at hrun
      generalize hRq2 : buildCallRequest { ctx with checked := true } LowLevelCallKind.call _ _ _ none = request2 at hrun
      cases hans2 : V.ans ([] ++ [{ query := Query.external world (ExternalRequest.call request), answer := a }])
          (Query.external a.postWorld (ExternalRequest.call request2)) with
      | none => rw [hans2] at hrun; simp at hrun
      | some a2 =>
      simp only [hans2] at hrun
      refine ⟨a.postWorld, request2, a2, ?_, ?_⟩
      · refine ⟨by rw [List.nil_append] at hans2; exact hans2, by subst hRq2; rfl, ?_, by subst hRq2; rfl, ?_, ?_, ?_, fun _ _ => rfl, ?_⟩
        · subst hRq2
          rw [hPs, hU1]
          simp [buildCallRequest, addressToWord, wordToAddress, wordToU256, fieldValue, tokenField,
            EvmYul.AccountAddress.ofUInt256, SolidCore.Solidity.Shared.norm]
          have h1 : slotValue σ 1 % 1461501637330902918203684832716283019655932542976 <
              Solidity.Shared.wordModulus := lt_of_lt_of_le (Nat.mod_lt _ (by decide)) (by decide)
          rw [Nat.mod_eq_of_lt h1]
          simp [EvmYul.UInt256.ofNat, EvmYul.AccountAddress.size, Fin.ofNat, Id.run, EvmYul.UInt256.size]
        · subst hRq2
          simp only [buildCallRequest, bytes_roundtrip]
          exact input_eq σ dst a w hv (Nat.le_of_not_lt hlw)
        · intro slot hslot
          rw [hstatic _ _ _ _ hans (by subst hRq; rfl) slot, hworld slot hslot]
        · intro slot hslot
          rw [hstaticT _ _ _ _ hans (by subst hRq; rfl) slot, htrans slot hslot]
        · exact hsize64 _ _ _ _ hans2
      · obtain ⟨R2, hR2s, hk2⟩ := hkk a2 (hsize _ _ _ _ hans2)
        simp only [hk2, sbind_pure] at hrun
        simp only [decodeCallResponse] at hrun hR2s
        have hl2 : (byteArrayToBytes a2.returnData).length = a2.returnData.size := by
          rw [byteArrayToBytes_eq, List.length_map, List.length_range]
        have hwq : 32 ≤ a2.returnData.size → bytesToWordBE (List.take 32 (List.map (normByte ∘ normByte)
            (byteArrayToBytes a2.returnData))) = (Sync.retWord a2).toNat := by
          intro h32
          rw [← List.map_map, normByte_bytes, normByte_bytes, retWord_toNat a2 h32]
        have hcr : ∀ r, skimFn.collectReturns r = .ok [] := fun _ => rfl
        have hst2 : ∀ j, R2.state.loadSlot j = storageIn a2.postWorld (j % 2 ^ 256) := by
          intro j
          rw [hR2s]
          simp only [payState, adoptWorld, State.loadSlot, storageIn, accountIn, hctxs]
          simp only [StorageMap.lookup?, SolidCore.Solidity.Shared.norm, Std.HashMap.get?_eq_getElem?]
          have hmm : j % 2 ^ 256 % SolidCore.Solidity.Shared.wordModulus = j % SolidCore.Solidity.Shared.wordModulus :=
            Nat.mod_mod j _
          rw [hmm]
          cases (storageToWordMap _)[j % SolidCore.Solidity.Shared.wordModulus]? <;> rfl
        have hev2 : R2.state.events = [] := by
          rw [hR2s]
          show P.state.events = []
          have hUe : U.state.events = R.state.events := by rw [← hU, ← hT, ← hQ]; rfl
          rw [hPs, hUe, hRs, ← hrt0, ← hst]
          exact hd.events
        have hemp : ABI.Contract.encodeRevertData? c.core RevertData.empty = some [] := by
          simp [ABI.Contract.encodeRevertData?]
        have he : ABI.Contract.encodeRevertData? c.core (RevertData.error "TRANSFER_FAILED") = some Skim.errData := by
          rw [encode_error ⟨[], fun _ => 0, solHash⟩ c.core errB_eq', List.map_map]
          decide
        simp only [payRes, hl2] at hrun
        split_ifs at hrun with h1 h2 h3 h4 h5
        all_goals simp only [Result.mapRuntime, finish_reverted, finish_normal_nil payFn rfl, sbind_pure,
          map_pure', foldAns_pure, FunctionDef.callBodyResult, evalList_nil] at hrun
        all_goals simp only [hcr, List.map_nil, show ABI.encodeValues? (List.map BindingDecl.ty skimFn.returns) [] = some [] from rfl,
          RevertData.untagFixedBytes, he, hemp, Option.bind_eq_bind, Option.bind_some,
          Option.map_some, Option.some.injEq] at hrun
        all_goals try subst hrun
        all_goals simp only [Source.observe, Skim.obsLate, Skim.failObs, Skim.okObs]
        · simp only [h1, h2, ↓reduceIte, if_true, Runtime.popScope, State.logEntries, hev2, List.map_nil]
          congr 1
          funext slot
          exact hst2 slot
        · simp only [h1, h2, h3, ↓reduceIte]
          rfl
        · have h32 : 32 ≤ a2.returnData.size := by omega
          rw [hwq h32] at h4 h5
          simp only [h1, h2, h3, ↓reduceIte, h5, show ¬ 1 < 0 by omega]
          rfl
        · have h32 : 32 ≤ a2.returnData.size := by omega
          rw [hwq h32] at h4 h5
          simp only [h1, h2, h3, ↓reduceIte, h5, Nat.not_lt.mpr h4, if_true,
            Runtime.popScope, State.logEntries, hev2, List.map_nil]
          congr 1
          funext slot
          exact hst2 slot
        · have h32 : 32 ≤ a2.returnData.size := by omega
          rw [hwq h32] at h4
          simp only [h1, h2, h3, ↓reduceIte, Nat.lt_of_not_le h4]
          rfl
        · simp only [h1, Bool.false_eq_true, ↓reduceIte]
          rfl

/-- info: 'SolidCore.Refinement.CallFamilies.skim_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms skim_source

/-- **skim's source stage in the world V**: under every oracle that agrees with V (CallsAgree o V),
solar's stage0 runs skim(dst) as SolidCore runs it in V, for every recipient below 2 ^ 160 and every
storage whose token is not the contract itself. Hypotheses: the checked contract's skim, pay and
fields are skimFn, payFn and callsFields, its constructor leaves no storage, transient storage,
adopted world or seeded accounts; V's seeded code is at addresses below 2 ^ 160 and its answers'
return data is shorter than 2 ^ 64 bytes. -/
theorem skim_stage_in (k : Nat) (V : World) {c : SolidCore.Solidity.TypeCheck.CheckedContract}
    {d : SolidCore.Solidity.Source.State} (hd : Wide.DeployedAt (k + 8) c d [])
    (hfind : c.core.findFunctionBySelector? 3156594551 = some skimFn)
    (hpay : c.core.table.lookup? payName = some payFn)
    (hfields : c.core.storageFields = callsFields)
    (hdt : d.transient.toList = []) (hde : d.envWorld? = none)
    (hcb : c.core.context.accountBalances = []) (hch : c.core.context.accountCodehashes = [])
    (hcc : c.core.context.accountCodes = []) (hkeys : ∀ p ∈ V.codes.getD [], p.1 < 2 ^ 160)
    (hsize64 : ∀ h world request a, V.ans h (.external world (.call request)) = some a →
      a.returnData.size < 2 ^ 64)
    (o : Machine.Oracle) (agree : CallsAgree o V) :
    Stage (solidCoreIn V (k + 8)) (MIR.Lowered.moduleSem o) c SolarTV.Export.Calls.stage0
      (fun call => ∃ σ dst, (dst < 2 ^ 160 ∧ slotValue σ 1 % 2 ^ 160 ≠ selfAddress) ∧ call = Skim.skimCall σ dst) :=
  Skim.skim_stage (k + 8) c V _ (fun _ _ h => h.1)
    (fun σ dst h => skim_source k V hd hfind hpay hfields
      (fun h w r a ha hk slot => (agree.static h w r a ha hk slot).1)
      (fun h w r a ha hk slot => (agree.static h w r a ha hk slot).2)
      hdt hde hcb hch hcc hkeys
      (fun h w r a ha => lt_trans (hsize64 h w r a ha) (by decide)) hsize64 σ dst h.1 h.2)
    o agree

/-- info: 'SolidCore.Refinement.CallFamilies.skim_stage_in' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms skim_stage_in

end SolidCore.Refinement.CallFamilies

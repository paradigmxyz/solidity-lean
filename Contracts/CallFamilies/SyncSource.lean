import Contracts.CallFamilies.StageOfSource
import SolidCore.Refinement.Generic.StageIn
import SolidCore.Refinement.Generic.CallNode
import SolidCore.Solidity.AdoptionLaws

namespace SolidCore.Refinement.CallFamilies

open SolarTV SolidCore.Refinement SolidCore.Refinement.Generic SolidCore.Refinement.CallNode
open SolidCore.Solidity.Source EvmCompiler.Simulation

/-- SolidCore's `sync()` of `Calls`, as the checker lowers it. -/
def syncFn : FunctionDef :=
{ name := "sync",
  selector? := some 4294363881,
  payable := false,
  params := [],
  paramAbiCleanups := [],
  returns := [],
  body := Stmt.block
            [Stmt.block
               [Stmt.varDecl (Ty.uint256) "_sol_hoist_0" none,
                Stmt.tryExternalCall
                  (SolidCore.Solidity.Shared.Call.ExternalCallKind.staticcall)
                  (Expr.storageRead (StorageReadMode.ref) "token" [])
                  (Expr.encode (EncodeKind.withSelector) (some (Expr.word 1889567281)) []
                    [Ty.address] [Expr.self])
                  (Expr.word 0) none false false
                  [{ name := "__ext0", ty := Ty.uint256, isStorageRef := false }]
                  [AbiCleanup.uint 256]
                  (Stmt.assign (LValue.var "_sol_hoist_0")
                    (Expr.castOp (CastKind.uintCleanup) 256 (Expr.var "__ext0")))
                  [],
                Stmt.assign (LValue.storage "reserve")
                  (Expr.castOp (CastKind.uintCleanup) 256 (Expr.var "_sol_hoist_0"))]],
  dispatchId? := none }




/-- The input of `balanceOf(address(this))`. -/
def encSync : List Nat := [112, 160, 130, 49] ++ List.replicate 30 0 ++ [16, 0]

theorem enc_eval (ctx : Context) (rt : Runtime) (h : ctx.self = selfAddress) :
    (Expr.encode (EncodeKind.withSelector) (some (Expr.word 1889567281)) [] [Ty.address]
      [Expr.self]).evalWithRuntimeByContext ctx rt = .ok (.bytes encSync, rt) := by
  simp only [Expr.evalWithRuntimeByContext, Expr.eval, Expr.orderFuel, Expr.evalFuel,
    Expr.listEvalFuel, Expr.evalListFuel, h]
  simp [Runtime.materializeForValueUseList, mat_word, bind, pure, liftM, monadLift,
    MonadLift.monadLift, SolI.ofExcept, ipure_bind]
  rfl

/-- `Calls`'s `token` field. -/
def tokenField : StorageField :=
  { name := "token",
    slot := 1,
    ty? := some Ty.address,
    layout? := some (StorageLayout.scalar Ty.address),
    transient := false,
    packedOffset := 0,
    packedBytes := 20,
    packedSigned := false }

theorem tok_eval (ctx : Context) (rt : Runtime) (hf : AddrFieldOk ctx "token" tokenField)
    (hw : rt.state.loadSlot tokenField.slot < Generic.wordSize) :
    (Expr.storageRead .ref "token" []).evalWithRuntimeByContext ctx rt =
      .ok (.word (fieldValue (rt.state.loadSlot tokenField.slot) tokenField.packedOffset 20), rt) := by
  simp only [Expr.evalWithRuntimeByContext, Expr.eval, Expr.orderFuel, Expr.evalFuel,
    Expr.listEvalFuel]
  simp only [load_addrField hf hw]
  rfl


theorem done_bind' {α β : Type} (a : α) (f : α → SolI β) :
    (Interaction.done (Except.ok a) >>= f : SolI β) = f a := rfl

/-- `Calls`'s storage fields. -/
def callsFields : List StorageField :=
  [{ name := "factory", slot := 0, ty? := some Ty.address,
     layout? := some (StorageLayout.scalar Ty.address), transient := false, packedOffset := 0,
     packedBytes := 20, packedSigned := false },
   tokenField,
   { name := "reserve", slot := 2, ty? := some Ty.uint256,
     layout? := some (StorageLayout.scalar Ty.uint256), transient := false, packedOffset := 0,
     packedBytes := 32, packedSigned := false },
   { name := "kLast", slot := 3, ty? := some Ty.uint256,
     layout? := some (StorageLayout.scalar Ty.uint256), transient := false, packedOffset := 0,
     packedBytes := 32, packedSigned := false }]

theorem fold_mod (M : Nat) (l : List Nat) (x : Nat) :
    (l.foldl (fun a b => a * 256 + b) (x % M)) % M =
      (l.foldl (fun a b => a * 256 + b) x) % M := by
  induction l generalizing x with
  | nil => simp
  | cons b l ih =>
    simp only [List.foldl_cons]
    have h : (x % M * 256 + b) % M = (x * 256 + b) % M := by
      simp [Nat.add_mod, Nat.mul_mod, Nat.mod_mod]
    rw [← ih (x % M * 256 + b), h, ih]

theorem step_or (acc : BitVec 256) (b : BitVec 8) :
    ((acc <<< 8) ||| b.setWidth 256).toNat = (acc.toNat * 256 + b.toNat) % 2 ^ 256 := by
  have hand : (acc <<< 8) &&& b.setWidth 256 = 0 := by
    ext i hi
    simp
    intro h1 h2
    exact BitVec.getLsbD_of_ge b i (by omega)
  rw [← BitVec.add_eq_or_of_and_eq_zero _ _ hand, BitVec.toNat_add, BitVec.toNat_shiftLeft,
    BitVec.toNat_setWidth]
  have hb := b.isLt
  rw [Nat.mod_eq_of_lt (by omega : b.toNat < 2 ^ 256), Nat.shiftLeft_eq]
  simp only [Nat.add_mod_mod, Nat.mod_add_mod]

theorem fold_bv (bs : List (BitVec 8)) (acc : BitVec 256) :
    (bs.foldl (fun (acc : BitVec 256) (b : BitVec 8) => (acc <<< 8) ||| b.setWidth 256) acc).toNat =
      ((bs.map BitVec.toNat).foldl (fun a b => a * 256 + b) acc.toNat) % 2 ^ 256 := by
  induction bs generalizing acc with
  | nil => simp [Nat.mod_eq_of_lt acc.isLt]
  | cons b bs ih =>
    simp only [List.foldl_cons, List.map_cons]
    rw [ih, step_or, fold_mod]

theorem retWord_toNat (a : CallResponse) (h : 32 ≤ a.returnData.size) :
    (Sync.retWord a).toNat = bytesToWordBE (List.take 32 (byteArrayToBytes a.returnData)) := by
  unfold Sync.retWord bytesToWordBE SolidCore.Solidity.Shared.norm
  rw [fold_bv, byteArrayToBytes_eq, ← List.map_take, List.take_range, Nat.min_eq_left h]
  simp only [List.map_map, BitVec.toNat_zero]
  rw [List.foldl_map, List.foldl_map]
  have : ∀ x : UInt8, (BitVec.ofNat 8 x.toNat).toNat = normByte x.toNat := by
    intro x
    simp [normByte, SolidCore.Solidity.Shared.Account.byte]
  simp only [Function.comp, this]
  rfl

theorem syncCall_eq (σ : List (Nat × Nat)) :
    Sync.syncCall σ = Evm.Wide.callAt 4294363881 [] σ := rfl

/-- The storage a call from `σ` starts with: `σ` written over the constructor's (empty) storage. -/
theorem load_deployed {fuel : Nat} {c : SolidCore.Solidity.TypeCheck.CheckedContract}
    {d : SolidCore.Solidity.Source.State} (hd : Wide.DeployedAt fuel c d []) (σ : List (Nat × Nat))
    (k : Nat) (hk : k < Generic.wordSize) :
    ({ d with storage := σ.foldl (fun acc kv => acc.insertLoop kv.1 kv.2) d.storage } :
      SolidCore.Solidity.Source.State).loadSlot k = slotValue σ k := by
  have := getD_storage_cover hd (σ := σ) (by intro kv hkv; simp at hkv) k
  simp only [State.loadSlot, StorageMap.lookup?]
  rw [← this]
  simp only [SolidCore.Solidity.Shared.norm, modulus_eq, Std.HashMap.get?_eq_getElem?]
  cases (List.foldl (fun acc kv => acc.insertLoop kv.1 kv.2) d.storage σ)[k % Generic.wordSize]? <;> rfl

/-- An address field holding `x` names another account than the contract's. -/
theorem callee_ne_self {x : Nat} (h : x % 2 ^ 160 ≠ selfAddress) :
    wordEq (SolidCore.Solidity.Shared.norm (fieldValue x 0 20)) selfAddress = false := by
  simp only [wordEq, fieldValue, SolidCore.Solidity.Shared.norm]
  simp
  have h1 : x % 1461501637330902918203684832716283019655932542976 < Solidity.Shared.wordModulus :=
    lt_of_lt_of_le (Nat.mod_lt _ (by decide)) (by decide)
  rw [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt (by decide : selfAddress < Solidity.Shared.wordModulus)]
  exact h

/-- The callee of a call of an address field holding `x`. -/
theorem callee_word (x : Nat) :
    addressToWord (wordToAddress (SolidCore.Solidity.Shared.norm (fieldValue x 0 20))) = x % 2 ^ 160 := by
  simp [addressToWord, wordToAddress, wordToU256, fieldValue, EvmYul.AccountAddress.ofUInt256,
    SolidCore.Solidity.Shared.norm]
  have h1 : x % 1461501637330902918203684832716283019655932542976 < Solidity.Shared.wordModulus :=
    lt_of_lt_of_le (Nat.mod_lt _ (by decide)) (by decide)
  rw [Nat.mod_eq_of_lt h1]
  simp [EvmYul.UInt256.ofNat, EvmYul.AccountAddress.size, Fin.ofNat, Id.run, EvmYul.UInt256.size]

/-- **The world a first call sends**: `σ`'s storage, no transient storage, and `V`'s code. `X` is the
state at the call, which still holds the deployed state with `σ` written. -/
theorem sent_world {fuel : Nat} {c : SolidCore.Solidity.TypeCheck.CheckedContract}
    {d : SolidCore.Solidity.Source.State} (hd : Wide.DeployedAt fuel c d []) (V : World)
    (σ : List (Nat × Nat)) (ctx : Context) (hctxs : ctx.self = selfAddress)
    (hacc : ctx.accountCodes = V.codes.getD []) (hcb : ctx.accountBalances = [])
    (hch : ctx.accountCodehashes = []) (hkeys : ∀ p ∈ V.codes.getD [], p.1 < 2 ^ 160)
    (hdt : d.transient.toList = []) (st0 : SolidCore.Solidity.Source.State)
    (hst : ({ d with storage := σ.foldl (fun acc kv => acc.insertLoop kv.1 kv.2) d.storage } :
      SolidCore.Solidity.Source.State) = st0)
    (X : SolidCore.Solidity.Source.State) (world : SolidCore.Solidity.Shared.OpenWorld)
    (hW : snapshotWorld ctx X = world) (hmut : X.worldMutatedSinceAdoption = true)
    (hsto : X.storage = st0.storage) (htr : X.transient = d.transient) (henv : X.envWorld? = none) :
    (∀ slot < 2 ^ 256, storageIn world slot = slotValue σ slot % 2 ^ 256) ∧
      (∀ slot < 2 ^ 256, transientIn world slot = 0) ∧
      ∀ x < 2 ^ 160, (codeIn world x).isEmpty =
        (SolidCore.Solidity.Shared.Account.codeAt (V.codes.getD []) x).isEmpty := by
  subst hW
  refine ⟨fun slot hslot => ?_, fun slot hslot => ?_, fun x hx => ?_⟩
  · have hl : st0.loadSlot slot = slotValue σ slot := by subst hst; exact load_deployed hd σ slot hslot
    have hwf : StorageMap.WF X.storage := by
      rw [hsto, ← hst]; exact wf_foldl σ _ (wf_of_toList_nil _ hd.storage)
    unfold storageIn accountIn
    rw [show wordToAddress selfAddress = wordToAddress ctx.self by rw [hctxs],
      snapshotWorld_find_self ctx _ (Or.inr hmut)]
    simp only [Option.getD_some, snapshotSelfAccount]
    rw [lookup?_roundtrip _ hwf, hsto]
    unfold State.loadSlot at hl
    cases h : StorageMap.lookup? st0.storage slot with
    | none => rw [h] at hl; simp [← hl]
    | some v => rw [h] at hl; simp [← hl, SolidCore.Solidity.Shared.norm]; rfl
  · unfold transientIn accountIn
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
  · rw [← hacc]
    exact codeIn_snapshot ctx X henv hcb hch (by rw [hacc]; exact hkeys) (by rw [hctxs]; decide) x hx

/-- A failed call's raw revert data are its return data. -/
theorem revert_raw (c : SolidCore.Solidity.TypeCheck.CheckedContract) (a : CallResponse) :
    ∀ out, ABI.Contract.encodeRevertData? c.core
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

/-- The world hypothesis a static call needs: its answer keeps the caller's storage. -/
def StaticKeeps (V : World) : Prop :=
  ∀ h world request a, V.ans h (.external world (.call request)) = some a →
    request.kind = .staticcall → ∀ slot, storageIn a.postWorld slot = storageIn world slot

theorem eval_skip (n : Nat) (table : FunctionTable) (ctx : Context) (rt : Runtime) :
    Stmt.eval (n + 1) table ctx rt .skip = pure (Result.normal rt) := by
  rw [Stmt.eval]

/-- Adopting the callee's world leaves the contract's slots as the world holds them. -/
theorem adopt_load {ctx : Context} (hctxs : ctx.self = selfAddress) (w : SolidCore.Solidity.Shared.OpenWorld)
    (X : SolidCore.Solidity.Source.State) (j : Nat) :
    (adoptWorld w ctx X).loadSlot j = storageIn w j := by
  simp only [adoptWorld, State.loadSlot, storageIn, accountIn, hctxs]
  cases StorageMap.lookup? _ j <;> rfl

/-- After a first static call, the callee's world still holds `σ`'s storage. -/
theorem static_post {V : World} (hstatic : StaticKeeps V) {σ : List (Nat × Nat)}
    {world : SolidCore.Solidity.Shared.OpenWorld} {request : CallRequest} {a : CallResponse}
    (hans : V.ans [] (.external world (.call request)) = some a) (hkind : request.kind = .staticcall)
    (hworld : ∀ slot < 2 ^ 256, storageIn world slot = slotValue σ slot % 2 ^ 256) :
    ∀ j < 2 ^ 256, storageIn a.postWorld j = slotValue σ j := fun j hj => by
  rw [hstatic _ _ _ _ hans hkind j, hworld j hj, Nat.mod_eq_of_lt (slotValue_lt σ j)]

/-- **The relation after a first static call**: the runtime that adopted the callee's world, with
no writes or logs yet, and locals `sc`. -/
theorem static_rel {fuel : Nat} {c : SolidCore.Solidity.TypeCheck.CheckedContract}
    {d : SolidCore.Solidity.Source.State} (hd : Wide.DeployedAt fuel c d []) {V : World}
    (hstatic : StaticKeeps V) {σ : List (Nat × Nat)} {ctx : Context} (hctxs : ctx.self = selfAddress)
    (hfields : ctx.storageFields = callsFields) (hchecked : ctx.checked = true)
    (hsender : ctx.sender = (WExpr.lit SolidCore.Refinement.Generic.callerWord).eval ⟨[], slotValue σ, solHash, SolidCore.Refinement.Generic.callerWord⟩)
    {world : SolidCore.Solidity.Shared.OpenWorld} {request : CallRequest} {a : CallResponse}
    (hans : V.ans [] (.external world (.call request)) = some a) (hkind : request.kind = .staticcall)
    (hworld : ∀ slot < 2 ^ 256, storageIn world slot = slotValue σ slot % 2 ^ 256)
    (X : SolidCore.Solidity.Source.State) (rt : Runtime)
    (hload : ∀ j, rt.state.loadSlot j = (adoptWorld a.postWorld ctx X).loadSlot j)
    (hev : rt.state.events = d.events) (sc : Scopes)
    (hframes : rt.locals = sc.map (frameOf ⟨[], slotValue σ, solHash, SolidCore.Refinement.Generic.callerWord⟩)) :
    StmtRel ⟨[], slotValue σ, solHash, SolidCore.Refinement.Generic.callerWord⟩
      { fields := callsFields, events := ctx.eventDecls, tbl := c.core.table } ctx rt
      ⟨sc, [], [], .lit SolidCore.Refinement.Generic.callerWord, []⟩ :=
  { fields := hfields
    events := rfl
    checked := hchecked
    sender := hsender
    hash := rfl
    ok := slotValue_store σ
    frames := hframes
    store := fun j hj => by
      rw [hload, adopt_load hctxs, static_post hstatic hans hkind hworld j hj]
      rfl
    logs := by rw [hev, hd.events]; rfl
    facts := by intro p hp; cases hp }

/-- The storage after one word write at slot `n`, as the symbolic writes give it. -/
theorem store_write (call : SolarTV.Call) (rc n w : Nat) (hn : n < 2 ^ 256) (x : BitVec 256)
    (hx : x.toNat = w) (slot : Nat) :
    (Machine.update (Machine.State.initial call).storage (BitVec.ofNat 256 n) x
        (BitVec.ofNat 256 slot)).toNat =
      Writes.store ⟨[], slotValue call.storage, solHash, rc⟩
        [(.lit n, writeField (.init n) (.lit w) 0 32)] slot := by
  have hn' : n % 115792089237316195423570985008687907853269984665640564039457584007913129639936 = n :=
    Nat.mod_eq_of_lt hn
  have hw' : w % 115792089237316195423570985008687907853269984665640564039457584007913129639936 = w :=
    Nat.mod_eq_of_lt (hx ▸ x.isLt)
  simp only [Writes.store, Machine.update]
  rw [writeField_eval _ _ _ (by decide) (by decide)]
  by_cases h2 : slot % 115792089237316195423570985008687907853269984665640564039457584007913129639936 = n
  · have hb : BitVec.ofNat 256 slot = BitVec.ofNat 256 n := by
      apply BitVec.eq_of_toNat_eq; simp [h2, hn']
    rw [if_pos hb, hx]
    simp [WExpr.eval, Generic.wordSize, h2, fieldWrite, hw', hn']
  · have hb : BitVec.ofNat 256 slot ≠ BitVec.ofNat 256 n := by
      intro h; apply h2; have := congrArg BitVec.toNat h; simpa [hn'] using this
    rw [if_neg hb]
    have hne : ¬ ((WExpr.lit n).eval ⟨[], slotValue call.storage, solHash, rc⟩ = slot % Generic.wordSize) := by
      intro h; apply h2; simpa [WExpr.eval, Generic.wordSize, hn'] using h.symm
    rw [if_neg hne]
    simp only [Machine.State.initial, BitVec.toNat_ofNat]
    exact slotValue_store call.storage slot

set_option maxHeartbeats 4000000 in
theorem sync_source (k : Nat) (V : World) {c : SolidCore.Solidity.TypeCheck.CheckedContract}
    {d : SolidCore.Solidity.Source.State} (hd : Wide.DeployedAt (k + 5) c d [])
    (hfind : c.core.findFunctionBySelector? 4294363881 = some syncFn)
    (hfields : c.core.storageFields = callsFields)
    (hstatic : StaticKeeps V) (hdt : d.transient.toList = []) (hde : d.envWorld? = none)
    (hcb : c.core.context.accountBalances = []) (hch : c.core.context.accountCodehashes = [])
    (hcc : c.core.context.accountCodes = []) (hkeys : ∀ p ∈ V.codes.getD [], p.1 < 2 ^ 160)
    (hsize : ∀ h world request a, V.ans h (.external world (.call request)) = some a →
      a.returnData.size < 2 ^ 256) (σ : List (Nat × Nat))
    (hself : slotValue σ 1 % 2 ^ 160 ≠ selfAddress) : SyncSource (k + 5) c V σ := by
  have hlt := slotValue_lt σ
  intro obs hrun
  rw [syncCall_eq, runIn_eq_at V hd] at hrun
  simp only [Source.ABI.Oracle.callCalldata, Dirty.readSelector_calldata _ (by decide : 4294363881 < 2 ^ 32), hfind] at hrun
  simp only [show ABI.decodeFunctionArgs? syncFn (List.drop ABI.selectorBytes
      (List.map (fun x => x.toNat) (EthLib.Base.natToBytes 4 4294363881) ++
        Dirty.argBytes (List.map (fun x => BitVec.toNat x) []))) = .ok [] from rfl,
    show syncFn.acceptsValue 0 = true from rfl, ↓reduceIte] at hrun
  generalize hctx : ABI.Contract.callContextAtWithBase c.core (ctxIn V c) selfAddress callerAddress 0
    (List.map (fun x => x.toNat) (EthLib.Base.natToBytes 4 4294363881) ++
      Dirty.argBytes (List.map (fun x => BitVec.toNat x) [])) = ctx at hrun
  generalize hst : ({ d with storage := σ.foldl (fun acc kv => acc.insertLoop kv.1 kv.2) d.storage } :
    SolidCore.Solidity.Source.State) = st0 at hrun
  have hctxv : ctx.value = 0 := by subst hctx; rfl
  have hctxs : ctx.self = selfAddress := by subst hctx; rfl
  simp only [Source.callAns, FunctionDef.call, FunctionDef.evalBodyEntry, hctxv,
    show syncFn.acceptsValue 0 = true from rfl, ↓reduceIte,
    show syncFn.initialFrame? [] = some [] from rfl, Option.map_some, Option.bind_some] at hrun
  generalize hrt0 : ({ state := { st0 with selfBalance := Solidity.Shared.addWord (Solidity.Shared.Account.balanceAt ctx.accountBalances ctx.self) 0, worldMutatedSinceAdoption := true }, locals := [[]] } : Runtime) = rt0 at hrun
  rw [show syncFn.body = Stmt.block [Stmt.block [Stmt.varDecl (Ty.uint256) "_sol_hoist_0" none,
                Stmt.tryExternalCall
                  (SolidCore.Solidity.Shared.Call.ExternalCallKind.staticcall)
                  (Expr.storageRead (StorageReadMode.ref) "token" [])
                  (Expr.encode (EncodeKind.withSelector) (some (Expr.word 1889567281)) []
                    [Ty.address] [Expr.self])
                  (Expr.word 0) none false false
                  [{ name := "__ext0", ty := Ty.uint256, isStorageRef := false }]
                  [AbiCleanup.uint 256]
                  (Stmt.assign (LValue.var "_sol_hoist_0")
                    (Expr.castOp (CastKind.uintCleanup) 256 (Expr.var "__ext0")))
                  [],
                Stmt.assign (LValue.storage "reserve")
                  (Expr.castOp (CastKind.uintCleanup) 256 (Expr.var "_sol_hoist_0"))]] from rfl] at hrun
  rw [eval_block, evalList_cons, eval_block, evalList_cons, eval_varDecl_none, sbind_pure] at hrun
  simp only [evalList_cons] at hrun
  have hctxf : ctx.storageFields = callsFields := by subst hctx; exact hfields
  have hfx : AddrFieldOk ctx "token" tokenField :=
    ⟨by simp [Context.storageField?, hctxf, callsFields, tokenField], rfl, rfl, rfl, by decide, by decide⟩
  have hT : (rt0.pushScope.pushScope.declareLocal "_sol_hoist_0" Ty.uint256.defaultValue).state.loadSlot tokenField.slot = slotValue σ 1 := by
    subst hrt0 hst; exact load_deployed hd σ 1 (by decide)
  have ht := tok_eval ctx (rt0.pushScope.pushScope.declareLocal "_sol_hoist_0" Ty.uint256.defaultValue) hfx
    (by rw [hT]; exact hlt 1)
  rw [hT] at ht
  have hne : wordEq (SolidCore.Solidity.Shared.norm (fieldValue (slotValue σ 1) tokenField.packedOffset 20)) ctx.self = false := by
    rw [hctxs]; exact callee_ne_self hself
  rw [eval_tryCall (k + 2) _ ctx _ _ _ _ _ false _ _ _ _ ht rfl (word0_eval ctx _) rfl (enc_eval ctx _ hctxs) rfl hne] at hrun
  generalize hW : snapshotWorld ctx (rt0.pushScope.pushScope.declareLocal "_sol_hoist_0" Ty.uint256.defaultValue).state = world at hrun
  generalize hR : buildCallRequest ctx Solidity.Shared.Call.ExternalCallKind.staticcall
      (Solidity.Shared.norm (fieldValue (slotValue σ 1) tokenField.packedOffset 20))
      (List.map normByte encSync) (Solidity.Shared.norm 0) none = request at hrun
  simp only [bind_request, map_request] at hrun
  rw [foldAns_request] at hrun
  obtain ⟨hworld, htrans, hcodes⟩ := sent_world hd V σ ctx hctxs
    (by subst hctx; show V.codes.getD c.core.context.accountCodes = V.codes.getD []; rw [hcc])
    (by subst hctx; exact hcb) (by subst hctx; exact hch) hkeys hdt st0 hst _ world hW
    (by subst hrt0; rfl) (by subst hrt0; rfl) (by subst hrt0 hst; rfl) (by subst hrt0 hst; exact hde)
  cases hans : V.ans [] (Query.external world (ExternalRequest.call request)) with
  | none => simp [hans] at hrun
  | some a =>
    simp only [hans] at hrun
    refine ⟨world, request, a, ⟨hans, by subst hR; rfl, by subst hR; exact callee_word _, by subst hR; rfl,
      ?_, hworld, htrans, hcodes, hsize _ _ _ _ hans⟩, ?_⟩
    · subst hR
      show byteArrayToBytes (bytesToByteArray (List.map normByte encSync)) = List.map BitVec.toNat Sync.input
      simp only [byteArrayToBytes, toList_eq_data, bytesToByteArray]
      decide
    · simp only [tryTail, decodeCallResponse] at hrun
      cases hs : a.success
      · simp only [hs, Bool.false_eq_true, ↓reduceIte, findMatch_nil] at hrun
        simp only [sbind_pure, map_pure', foldAns_pure, Result.mapRuntime, FunctionDef.callBodyResult,
          RevertData.fromRawBytes, normByte_bytes] at hrun
        simp only [Option.bind_eq_bind, Option.map_bind] at hrun
        obtain ⟨out, hout', hobs⟩ := Option.bind_eq_some_iff.mp hrun
        rw [revert_raw c a out hout'] at hobs
        simp only [Function.comp, Option.map_some, Option.some.injEq] at hobs
        rw [← hobs]
        simp only [Source.observe, Sync.obsOf, hs, Bool.false_eq_true, ↓reduceIte, byteArrayToBytes_eq]
        rfl
      · simp only [hs, ↓reduceIte, normByte_bytes, List.map_cons, List.map_nil] at hrun
        by_cases hlen : (byteArrayToBytes a.returnData).length < 32
        · rw [decode_short _ hlen] at hrun
          simp only [sbind_pure, map_pure', foldAns_pure, Result.mapRuntime, FunctionDef.callBodyResult,
            RevertData.untagFixedBytes, ABI.Contract.encodeRevertData?, Option.bind_eq_bind, Option.bind_some,
            Option.map_some, Option.some.injEq] at hrun
          have hsz : a.returnData.size < 32 := by
            rw [byteArrayToBytes_eq, List.length_map, List.length_range] at hlen; exact hlen
          rw [← hrun]
          simp only [Source.observe, Sync.obsOf, hs, ↓reduceIte, hsz, Bool.false_eq_true]
          rfl
        · rw [decode_word _ (by omega)] at hrun
          simp only [normByte_bytes] at hrun
          generalize hw : bytesToWordBE (List.take 32 (byteArrayToBytes a.returnData)) = w at hrun
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
          let ρ : Val := ⟨[], slotValue σ, solHash, SolidCore.Refinement.Generic.callerWord⟩
          let E : EraseEnv := { fields := callsFields, events := ctx.eventDecls, tbl := c.core.table }
          let S1 : SymState := ⟨[[("__ext0", .lit w)], [("_sol_hoist_0", .lit 0)], [], []], [], [], .lit SolidCore.Refinement.Generic.callerWord, []⟩
          have hrel1 : StmtRel ρ E ctx ((({ state := adoptWorld a.postWorld ctx (rt0.pushScope.pushScope.declareLocal "_sol_hoist_0" Ty.uint256.defaultValue).state, locals := (rt0.pushScope.pushScope.declareLocal "_sol_hoist_0" Ty.uint256.defaultValue).locals, memory := (rt0.pushScope.pushScope.declareLocal "_sol_hoist_0" Ty.uint256.defaultValue).memory, nextMemory := (rt0.pushScope.pushScope.declareLocal "_sol_hoist_0" Ty.uint256.defaultValue).nextMemory, nextMemoryByte := (rt0.pushScope.pushScope.declareLocal "_sol_hoist_0" Ty.uint256.defaultValue).nextMemoryByte } : Runtime).recordExternalInteraction (ExternalInteraction.lowLevelCall { kind := Solidity.Shared.Call.ExternalCallKind.staticcall, target := Solidity.Shared.norm (fieldValue (slotValue σ 1) tokenField.packedOffset 20), calldata := List.map normByte encSync, value := Solidity.Shared.norm 0, success := true, output := byteArrayToBytes a.returnData })).withFrame [("__ext0", Value.word w)]) S1 :=
            static_rel hd hstatic hctxs hctxf (by subst hctx; rfl) (by subst hctx; rfl) hans (by subst hR; rfl)
              hworld (rt0.pushScope.pushScope.declareLocal "_sol_hoist_0" Ty.uint256.defaultValue).state _
              (fun _ => by rfl) (by subst hrt0 hst; rfl) _ (by
                subst hrt0
                simp [Runtime.withFrame, Runtime.recordExternalInteraction, Runtime.declareLocal,
                  Runtime.pushScope, frameOf, S1, WExpr.eval, Nat.mod_eq_of_lt hwlt]
                simp [LocalEnv.declare, Ty.defaultValue])
          obtain ⟨r1, hr1, hl1⟩ := eval_stmt ρ E ctx (k + 2) (Stmt.assign (LValue.var "_sol_hoist_0")
            (Expr.castOp CastKind.uintCleanup 256 (Expr.var "__ext0"))) S1 _ rfl _ hrel1
          rw [hr1] at hrun
          let S1' : SymState := ⟨[[("__ext0", .lit w)], [("_sol_hoist_0", .lit w)], [], []], [], [], .lit SolidCore.Refinement.Generic.callerWord, []⟩
          have hl1' : LeafRel ρ E ctx r1 (.normal S1') := hl1
          cases r1 with
          | normal rt1 =>
            have hrel2 : StmtRel ρ E ctx rt1.popScope S1'.pop := StmtRel.popScope hl1'
            obtain ⟨r2, hr2, hl2⟩ := eval_stmt ρ E ctx (k + 3) (Stmt.assign (LValue.storage "reserve")
              (Expr.castOp CastKind.uintCleanup 256 (Expr.var "_sol_hoist_0"))) S1'.pop _ rfl _ hrel2
            simp only [done_bind', Result.mapRuntime, sbind_pure] at hrun
            rw [hr2] at hrun
            let S3 : SymState := ⟨[[("_sol_hoist_0", .lit w)], [], []],
              [(.lit 2, writeField (.init 2) (.lit w) 0 32)], [], .lit SolidCore.Refinement.Generic.callerWord, []⟩
            have hl2' : LeafRel ρ E ctx r2 (.normal S3) := hl2
            cases r2 with
            | normal rt2 =>
              have hrel3 : StmtRel ρ E ctx rt2 S3 := hl2'
              simp only [done_bind', sbind_pure, evalList_nil, Result.mapRuntime, map_pure', foldAns_pure,
                FunctionDef.callBodyResult] at hrun
              rw [show syncFn.collectReturns rt2.popScope.popScope = .ok [] from rfl] at hrun
              simp only [List.map_nil, show ABI.encodeValues? (List.map BindingDecl.ty syncFn.returns) [] = some [] from rfl,
                Option.bind_eq_bind, Option.bind_some, Option.map_some, Option.some.injEq] at hrun
              have hev : rt2.state.events = [] := by
                have := hrel3.logs
                simp only [S3, List.map_nil, List.map_eq_nil_iff] at this
                exact this
              have hsz : 32 ≤ a.returnData.size := by
                rw [byteArrayToBytes_eq, List.length_map, List.length_range] at hlen; omega
              rw [← hrun]
              simp only [Source.observe, Sync.obsOf, hs, ↓reduceIte, Runtime.popScope, State.logEntries, hev,
                List.map_nil, show ¬ a.returnData.size < 32 by omega]
              congr 1
              funext slot
              rw [loadSlot_eq rt2.state S3.writes ρ (slotValue_store σ) hrel3.store slot]
              exact (store_write (Sync.syncCall σ) _ 2 w (by decide) _ (by rw [retWord_toNat a hsz, hw]) slot).symm
            | _ => exact absurd hl2' id
          | _ => exact absurd hl1' id


/-- info: 'SolidCore.Refinement.CallFamilies.sync_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sync_source

/-- **sync's source stage in the world `V`**: under every oracle that agrees with `V`
(`CallsAgree o V`), solar's stage0 runs `sync()` as SolidCore runs it in `V`, from every storage
whose token is not the contract itself. Hypotheses: the checked contract's `sync` and fields are
`syncFn` and `callsFields`, its constructor leaves no storage, transient storage, adopted world or
seeded accounts; `V`'s seeded code is at addresses below `2 ^ 160` and its answers' return data is
shorter than `2 ^ 256` bytes. -/
theorem sync_stage_in (k : Nat) (V : World) {c : SolidCore.Solidity.TypeCheck.CheckedContract}
    {d : SolidCore.Solidity.Source.State} (hd : Wide.DeployedAt (k + 5) c d [])
    (hfind : c.core.findFunctionBySelector? 4294363881 = some syncFn)
    (hfields : c.core.storageFields = callsFields)
    (hdt : d.transient.toList = []) (hde : d.envWorld? = none)
    (hcb : c.core.context.accountBalances = []) (hch : c.core.context.accountCodehashes = [])
    (hcc : c.core.context.accountCodes = []) (hkeys : ∀ p ∈ V.codes.getD [], p.1 < 2 ^ 160)
    (hsize : ∀ h world request a, V.ans h (.external world (.call request)) = some a →
      a.returnData.size < 2 ^ 256)
    (o : Machine.Oracle) (agree : CallsAgree o V) :
    Stage (solidCoreIn V (k + 5)) (MIR.Lowered.moduleSem o) c SolarTV.Export.Calls.stage0
      (fun call => ∃ σ, slotValue σ 1 % 2 ^ 160 ≠ selfAddress ∧ call = Sync.syncCall σ) :=
  sync_stage (k + 5) c V _ (fun σ hσ => sync_source k V hd hfind hfields
    (fun h w r a ha hk slot => (agree.static h w r a ha hk slot).1) hdt hde hcb hch hcc hkeys hsize σ hσ)
    o agree

/-- info: 'SolidCore.Refinement.CallFamilies.sync_stage_in' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sync_stage_in

end SolidCore.Refinement.CallFamilies

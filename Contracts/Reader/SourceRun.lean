import Contracts.Reader.Agree
import Contracts.Reader.Fn
import SolidCore.Refinement.Generic.StageIn
import Contracts.CallFamilies.SkimSource

/-!
# The source half of `read`

`read_source`: SolidCore's run of `read(a)` in a world `V` that answers its call asks `V` the
`STATICCALL` of `price()` to `a` that the MIR makes, from the world the MIR sees, and shows
`obsOfS` of `V`'s answer, with the storage of the world the answer leaves.
-/

namespace SolidCore.Refinement.Reader

open SolarTV SolidCore.Refinement SolidCore.Refinement.Generic SolidCore.Refinement.CallNode
open SolidCore.Solidity.Source EvmCompiler.Simulation
open SolidCore.Refinement.CallFamilies

theorem readCall_eq (σ : List (Nat × Nat)) (a : Nat) (ha : a < 2 ^ 160) :
    readCall σ a = Evm.Wide.callAt 2693245054 [BitVec.ofNat 256 a] σ := by
  unfold readCall Evm.Wide.callAt
  rw [List.map_cons, List.map_nil, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (lt_trans ha (by decide : (2 : Nat) ^ 160 < 2 ^ 256))]

theorem var_evalR (ctx : Context) (rt : Runtime) (x : String) (w : Nat)
    (hb : rt.lookupStorageBase? x = none) (hl : rt.lookupLocal? x = some (.word w)) :
    (Expr.var x).evalWithRuntimeByContext ctx rt = .ok (.word w, rt) := by
  simp only [Expr.evalWithRuntimeByContext, varE ctx rt x w hb hl]
  rfl

theorem enc_price (ctx : Context) (rt : Runtime) :
    (Expr.encode (EncodeKind.withSelector) (some (Expr.word 2687873534)) [] [] []).evalWithRuntimeByContext
      ctx rt = .ok (.bytes [160, 53, 177, 254], rt) := by
  simp only [Expr.evalWithRuntimeByContext, Expr.eval, Expr.orderFuel, Expr.evalFuel,
    Expr.listEvalFuel, Expr.evalListFuel]
  simp [Runtime.materializeForValueUseList, mat_word, bind, pure, liftM, monadLift,
    MonadLift.monadLift, SolI.ofExcept, ipure_bind]
  rfl

theorem eval_varDecl_one (n : Nat) (table : FunctionTable) (ctx : Context) (rt : Runtime)
    (x : String) :
    Stmt.eval (n + 1) table ctx rt (.varDecl Ty.uint256 x (some (Expr.word 1))) =
      pure (Result.normal (rt.declareLocal x (.word 1))) := by
  rw [Stmt.eval]
  simp [Expr.eval, Expr.evalFuel, Expr.orderFuel]
  rfl

theorem callee_addr {a : Nat} (ha : a < 2 ^ 160) : addressToWord (wordToAddress a) = a := by
  have h := callee_word a
  have h1 : Solidity.Shared.norm (fieldValue a 0 20) = a := by
    have h0 : fieldValue a 0 20 = a := by simp [fieldValue]; omega
    rw [h0]; exact Nat.mod_eq_of_lt (lt_trans ha (by decide))
  rwa [h1, Nat.mod_eq_of_lt ha] at h

theorem ne_self {a : Nat} (ha : a < 2 ^ 160) (h : a ≠ selfAddress) : wordEq a selfAddress = false := by
  have := callee_ne_self (x := a) (by rwa [Nat.mod_eq_of_lt ha])
  have h1 : Solidity.Shared.norm (fieldValue a 0 20) = a := by
    have h0 : fieldValue a 0 20 = a := by simp [fieldValue]; omega
    rw [h0]; exact Nat.mod_eq_of_lt (lt_trans ha (by decide))
  rwa [h1] at this

theorem revert_raw_eq (c : SolidCore.Solidity.TypeCheck.CheckedContract) (a : CallResponse) :
    ABI.Contract.encodeRevertData? c.core
        (if (byteArrayToBytes a.returnData == []) = true then SolidCore.Solidity.Source.RevertData.empty
          else SolidCore.Solidity.Source.RevertData.raw (byteArrayToBytes a.returnData)).untagFixedBytes =
      some (byteArrayToBytes a.returnData) := by
  split
  · rename_i he
    simp only [beq_iff_eq] at he
    simp only [RevertData.untagFixedBytes, ABI.Contract.encodeRevertData?, he]
  · simp only [RevertData.untagFixedBytes, ABI.Contract.encodeRevertData?, Option.some.injEq]
    exact normByte_bytes a.returnData

theorem storageIn_mod (w : SolidCore.Solidity.Shared.OpenWorld) (k : Nat) :
    storageIn w (k % Generic.wordSize) = storageIn w k := by
  simp only [storageIn, StorageMap.lookup?, norm_mod, Nat.mod_mod]

theorem storageIn_lt (w : SolidCore.Solidity.Shared.OpenWorld) (k : Nat) : storageIn w k < Generic.wordSize := by
  unfold storageIn
  rw [lookup?_storageToWordMap]
  cases (accountIn w selfAddress).storage.find? (wordToU256 k) with
  | none => exact Nat.zero_lt_of_ne_zero (by decide)
  | some v => exact v.val.isLt

/-- The values of a world's slots, as a valuation's storage. -/
def postVal (w : SolidCore.Solidity.Shared.OpenWorld) : Val :=
  ⟨[], fun j => storageIn w j, solHash, SolidCore.Refinement.Generic.callerWord⟩

theorem postVal_ok (w : SolidCore.Solidity.Shared.OpenWorld) : (postVal w).Ok := fun k => by
  show storageIn w (k % Generic.wordSize) % Generic.wordSize = storageIn w k
  rw [storageIn_mod, Nat.mod_eq_of_lt (storageIn_lt w k)]

/-- **The relation after a call whose answered world is adopted**: the runtime holds the answered
world's slots, with no writes or logs yet, and locals `sc`. -/
theorem post_rel {fuel : Nat} {c : SolidCore.Solidity.TypeCheck.CheckedContract}
    {d : SolidCore.Solidity.Source.State} (hd : Wide.DeployedAt fuel c d []) {ctx : Context}
    (hctxs : ctx.self = selfAddress)
    {F : List StorageField} (hfields : ctx.storageFields = F) (hchecked : ctx.checked = true)
    {w : SolidCore.Solidity.Shared.OpenWorld}
    (hsender : ctx.sender = (WExpr.lit SolidCore.Refinement.Generic.callerWord).eval (postVal w))
    (X : SolidCore.Solidity.Source.State) (rt : Runtime)
    (hload : ∀ j, rt.state.loadSlot j = (adoptWorld w ctx X).loadSlot j)
    (hev : rt.state.events = d.events) (sc : Scopes)
    (hframes : rt.locals = sc.map (frameOf (postVal w))) :
    StmtRel (postVal w) { fields := F, events := ctx.eventDecls, tbl := c.core.table } ctx rt
      ⟨sc, [], [], .lit SolidCore.Refinement.Generic.callerWord, [], [], none⟩ :=
  { fields := hfields
    events := rfl
    checked := hchecked
    sender := hsender
    hash := rfl
    ok := postVal_ok w
    frames := hframes
    store := fun j _ => by rw [hload, adopt_load hctxs]; rfl
    logs := by rw [hev, hd.events]; rfl
    facts := by intro p hp; cases hp }

theorem guard_add_one (ρ : Val) (w : Nat) (hw : w < 2 ^ 256) :
    (WExpr.bin BinOp.lt (WExpr.bin BinOp.add (WExpr.lit w) (WExpr.lit 1)) (WExpr.lit w)).eval ρ =
      if w + 1 = 2 ^ 256 then 1 else 0 := by
  have h1 : (1 : Nat) % 2 ^ 256 = 1 := Nat.mod_eq_of_lt (Nat.one_lt_two_pow (by decide))
  have hw' : w % 2 ^ 256 = w := Nat.mod_eq_of_lt hw
  show (if ((w % 2 ^ 256 + 1 % 2 ^ 256) % 2 ^ 256) % 2 ^ 256 < w % 2 ^ 256 then 1 else 0) % 2 ^ 256 = _
  simp only [hw', h1, Nat.mod_mod]
  by_cases hov : w + 1 = 2 ^ 256
  · have hpos : 0 < w := Nat.pos_of_ne_zero (by rintro rfl; norm_num at hov)
    simp only [hov, Nat.mod_self, hpos, if_true, h1]
  · have hn : ¬ (w + 1 < w) := by omega
    simp only [Nat.mod_eq_of_lt (Nat.lt_of_le_of_ne hw hov), hn, hov, if_false, Nat.zero_mod]

theorem read_source (k : Nat) (V : World) {c : SolidCore.Solidity.TypeCheck.CheckedContract}
    {d : SolidCore.Solidity.Source.State} (hd : Wide.DeployedAt (k + 5) c d [])
    (hfind : c.core.findFunctionBySelector? 2693245054 = some readFn)
    (hfields : c.core.storageFields = [])
    (hdt : d.transient.toList = []) (hde : d.envWorld? = none)
    (hcb : c.core.context.accountBalances = []) (hch : c.core.context.accountCodehashes = [])
    (hcc : c.core.context.accountCodes = []) (hkeys : ∀ p ∈ V.codes.getD [], p.1 < 2 ^ 160)
    (σ : List (Nat × Nat)) (a : Nat) (ha : a < 2 ^ 160) (hself : a ≠ selfAddress)
    (hanswers : ∀ world request, (V.ans [] (.external world (.call request))).isSome)
    (hsize : ∀ world request r, V.ans [] (.external world (.call request)) = some r →
      request.kind = .staticcall → addressToWord request.codeAddress = a →
      u256ToWord request.transferValue = 0 → byteArrayToBytes request.calldata = [0xa0, 0x35, 0xb1, 0xfe] →
      r.returnData.size < 2 ^ 256) :
    ∃ world request r, ReadAsk σ a V world request r ∧
      Source.runIn V (k + 5) c (readCall σ a) = some (obsOfS σ r (fun slot => storageIn r.postWorld slot)) := by
  generalize hrun : Source.runIn V (k + 5) c (readCall σ a) = R
  rw [readCall_eq σ a ha, runIn_eq_at V hd] at hrun
  simp only [Source.ABI.Oracle.callCalldata, Dirty.readSelector_calldata _ (by decide : 2693245054 < 2 ^ 32), hfind] at hrun
  have ha' : (BitVec.ofNat 256 a).toNat = a := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (lt_trans ha (by decide))]
  simp only [List.map_cons, List.map_nil, ha'] at hrun
  rw [show List.drop ABI.selectorBytes (List.map (fun x => x.toNat) (EthLib.Base.natToBytes 4 2693245054) ++
      Dirty.argBytes [a]) = Dirty.argBytes [a] by simp [ABI.selectorBytes, EthLib.Base.natToBytes_length],
    decode_args (ws := [2 ^ 160 - 1]) rfl [a] rfl (by simp; exact lt_trans ha (by decide))] at hrun
  have hcl : argsClean [2 ^ 160 - 1] [a] = true := by
    show (argOk (2 ^ 160 - 1) a && true) = true
    rw [argOk_lt _ (by decide)]
    simpa using Nat.le_sub_one_of_lt ha
  simp only [hcl, ↓reduceIte, show readFn.acceptsValue 0 = true from rfl, List.map_cons, List.map_nil] at hrun
  generalize hctx : ABI.Contract.callContextAtWithBase c.core (ctxIn V c) selfAddress callerAddress 0
    (List.map (fun x => x.toNat) (EthLib.Base.natToBytes 4 2693245054) ++ Dirty.argBytes [a]) = ctx at hrun
  generalize hst : ({ d with storage := σ.foldl (fun acc kv => acc.insertLoop kv.1 kv.2) d.storage } :
    SolidCore.Solidity.Source.State) = st0 at hrun
  have hctxv : ctx.value = 0 := by subst hctx; rfl
  have hctxs : ctx.self = selfAddress := by subst hctx; rfl
  have hframe : readFn.initialFrame? [Value.word a] = some [("o", Value.word a), ("_ret0", Value.word 0)] := by
    simp [FunctionDef.initialFrame?, readFn, BindingDecl.bindArgs?, BindingDecl.bindArg?,
      coerce_param (Or.inr rfl) a, FunctionDef.returnDefaultBindings, BindingDecl.defaultBinding, Ty.defaultValue]
  simp only [Source.callAns, FunctionDef.call, FunctionDef.evalBodyEntry, hctxv,
    show readFn.acceptsValue 0 = true from rfl, ↓reduceIte, hframe, Option.map_some, Option.bind_some] at hrun
  generalize hrt0 : ({ state := { st0 with selfBalance := Solidity.Shared.addWord (Solidity.Shared.Account.balanceAt ctx.accountBalances ctx.self) 0, worldMutatedSinceAdoption := true }, locals := [[("o", Value.word a), ("_ret0", Value.word 0)]] } : Runtime) = rt0 at hrun
  have hrt0l : rt0.locals = [[("o", Value.word a), ("_ret0", Value.word 0)]] := by rw [← hrt0]
  rw [show readFn.body = Stmt.block
            [Stmt.skip,
             Stmt.skip,
             Stmt.block
               [Stmt.varDecl (Ty.uint256) "_sol_hoist_1" (some (Expr.word 1)),
                Stmt.varDecl (Ty.uint256) "_sol_hoist_0" none,
                Stmt.tryExternalCall
                  (SolidCore.Solidity.Shared.Call.ExternalCallKind.staticcall)
                  (Expr.var "o")
                  (Expr.encode (EncodeKind.withSelector) (some (Expr.word 2687873534)) [] [] [])
                  (Expr.word 0) none false false
                  [{ name := "__ext0", ty := Ty.uint256, isStorageRef := false }]
                  [AbiCleanup.uint 256]
                  (Stmt.assign (LValue.var "_sol_hoist_0")
                    (Expr.castOp (CastKind.uintCleanup) 256 (Expr.var "__ext0")))
                  [],
                Stmt.returnValues
                  [Expr.castOp (CastKind.uintCleanup) 256
                    (Expr.castOp (CastKind.uintCleanup) 256
                      (Expr.binary (BinaryOp.add)
                        (Expr.castOp (CastKind.uintCleanup) 256 (Expr.var "_sol_hoist_0"))
                        (Expr.castOp (CastKind.uintCleanup) 256 (Expr.var "_sol_hoist_1"))))]]] from rfl] at hrun
  rw [eval_block, evalList_cons, eval_skip, sbind_pure] at hrun
  dsimp only at hrun
  rw [evalList_cons, eval_skip, sbind_pure] at hrun
  dsimp only at hrun
  rw [evalList_cons, eval_block, evalList_cons, eval_varDecl_one, sbind_pure] at hrun
  dsimp only at hrun
  rw [evalList_cons, eval_varDecl_none, sbind_pure] at hrun
  dsimp only at hrun
  rw [evalList_cons] at hrun
  generalize hR : Runtime.declareLocal _ "_sol_hoist_0" _ = Rt at hrun
  have hRs : Rt.state = rt0.state := by rw [← hR]; rfl
  have hRl : Rt.locals = [[("_sol_hoist_0", Value.word 0), ("_sol_hoist_1", Value.word 1)], [],
      [("o", Value.word a), ("_ret0", Value.word 0)]] := by
    rw [← hR]; simp [Runtime.declareLocal, Runtime.pushScope, LocalEnv.declare, hrt0l, Ty.defaultValue]
  clear hR
  have ht := var_evalR ctx Rt "o" a
    (by simp [Runtime.lookupStorageBase?, Runtime.lookupLocal?, hRl, LocalEnv.lookup?, Frame.lookup?])
    (by simp [Runtime.lookupLocal?, hRl, LocalEnv.lookup?, Frame.lookup?])
  have hne : wordEq a ctx.self = false := by rw [hctxs]; exact ne_self ha hself
  have hna : Solidity.Shared.norm a = a := Nat.mod_eq_of_lt (lt_trans ha (by decide))
  have htw : (Value.word a).expectWord = .ok a := by simp [Value.expectWord, hna]
  rw [show k + 3 = (k + 2) + 1 from rfl,
    eval_tryCall (k + 2) _ ctx _ _ _ _ _ false _ _ _ _ ht htw (word0_eval ctx _) rfl (enc_price ctx _) rfl hne] at hrun
  generalize hW : snapshotWorld ctx Rt.state = world at hrun
  generalize hRq : buildCallRequest ctx Solidity.Shared.Call.ExternalCallKind.staticcall a
      (List.map normByte [160, 53, 177, 254]) (Solidity.Shared.norm 0) none = request at hrun
  simp only [bind_request, map_request] at hrun
  rw [foldAns_request] at hrun
  obtain ⟨hworld, htrans, hcodes⟩ := sent_world hd V σ ctx hctxs
    (by subst hctx; show V.codes.getD c.core.context.accountCodes = V.codes.getD []; rw [hcc])
    (by subst hctx; exact hcb) (by subst hctx; exact hch) hkeys hdt st0 hst _ world hW
    (by rw [hRs, ← hrt0]) (by rw [hRs, ← hrt0]) (by rw [hRs, ← hrt0, ← hst]) (by rw [hRs, ← hrt0, ← hst]; exact hde)
  have hkind : request.kind = .staticcall := by subst hRq; rfl
  have hcallee : addressToWord request.codeAddress = a := by subst hRq; exact callee_addr ha
  have hvalue : u256ToWord request.transferValue = 0 := by subst hRq; rfl
  have hinput : byteArrayToBytes request.calldata = [0xa0, 0x35, 0xb1, 0xfe] := by
    subst hRq
    show byteArrayToBytes (bytesToByteArray (List.map normByte [160, 53, 177, 254])) = _
    simp only [byteArrayToBytes, toList_eq_data, bytesToByteArray]
    decide
  obtain ⟨r, hans⟩ := Option.isSome_iff_exists.mp (hanswers world request)
  have hask : ReadAsk σ a V world request r :=
    ⟨hans, hkind, hcallee, hvalue, by rw [hinput, input_eq], hworld, htrans, hcodes,
      hsize world request r hans hkind hcallee hvalue hinput⟩
  refine ⟨world, request, r, hask, ?_⟩
  simp only [hans] at hrun
  simp only [tryTail, decodeCallResponse] at hrun
  cases hs : r.success
  · simp only [hs, Bool.false_eq_true, ↓reduceIte, findMatch_nil] at hrun
    simp only [sbind_pure, map_pure', foldAns_pure, Result.mapRuntime, FunctionDef.callBodyResult,
      RevertData.fromRawBytes, normByte_bytes] at hrun
    simp only [Option.bind_eq_bind, revert_raw_eq c r, Option.bind_some, Option.map_some] at hrun
    rw [← hrun]
    simp only [Source.observe, obsOfS, hs, Bool.false_eq_true, ↓reduceIte, byteArrayToBytes_eq]
    rfl
  · simp only [hs, ↓reduceIte, normByte_bytes, List.map_cons, List.map_nil] at hrun
    by_cases hlen : (byteArrayToBytes r.returnData).length < 32
    · rw [decode_short _ hlen] at hrun
      simp only [sbind_pure, map_pure', foldAns_pure, Result.mapRuntime, FunctionDef.callBodyResult,
        RevertData.untagFixedBytes, ABI.Contract.encodeRevertData?, Option.bind_eq_bind, Option.bind_some,
        Option.map_some] at hrun
      have hsz : r.returnData.size < 32 := by
        rw [byteArrayToBytes_eq, List.length_map, List.length_range] at hlen; exact hlen
      rw [← hrun]
      simp only [Source.observe, obsOfS, hs, ↓reduceIte, hsz, Bool.false_eq_true]
      rfl
    · rw [decode_word _ (by omega)] at hrun
      simp only [normByte_bytes] at hrun
      have hsz : 32 ≤ r.returnData.size := by
        rw [byteArrayToBytes_eq, List.length_map, List.length_range] at hlen; omega
      have hv : (Sync.retWord r).toNat = bytesToWordBE (List.take 32 (byteArrayToBytes r.returnData)) :=
        retWord_toNat r hsz
      generalize hw : bytesToWordBE (List.take 32 (byteArrayToBytes r.returnData)) = w at hrun hv
      have hwlt : w < 2 ^ 256 := by rw [← hw]; exact Nat.mod_lt _ (by decide)
      simp only [AbiCleanups.acceptOrUnspecified] at hrun
      have hacc : AbiCleanups.accept [AbiCleanup.uint 256] [Value.word w] = true := by
        simp [AbiCleanups.accept, AbiCleanup.accepts, SolidCore.Solidity.Shared.norm]
        exact decide_eq_true (Nat.mod_lt w (by decide : 0 < Solidity.Shared.wordModulus))
      have hbind : BindingDecl.bindArgs? [{ name := "__ext0", ty := Ty.uint256 }] [Value.word w] =
          some [("__ext0", Value.word w)] := by
        simp [BindingDecl.bindArgs?, BindingDecl.bindArg?, Ty.coerceValue?, SolidCore.Solidity.Shared.norm,
          Nat.mod_eq_of_lt hwlt]
      simp only [hacc, hbind, Bool.or_true, ↓reduceIte] at hrun
      generalize hQ : Runtime.withFrame _ [("__ext0", Value.word w)] = Q at hrun
      let ρ : Val := postVal r.postWorld
      let E : EraseEnv := { fields := [], events := ctx.eventDecls, tbl := c.core.table }
      let S1 : SymState := ⟨[[("__ext0", .lit w)], [("_sol_hoist_0", .lit 0), ("_sol_hoist_1", .lit 1)], [],
        [("o", .lit a), ("_ret0", .lit 0)]], [], [], .lit SolidCore.Refinement.Generic.callerWord, [], [], none⟩
      have hctxf : ctx.storageFields = [] := by subst hctx; exact hfields
      have hQl : Q.locals = [[("__ext0", Value.word w)], [("_sol_hoist_0", Value.word 0), ("_sol_hoist_1", Value.word 1)], [],
          [("o", Value.word a), ("_ret0", Value.word 0)]] := by
        rw [← hQ]; simp [Runtime.withFrame, Runtime.recordExternalInteraction, hRl]
      have hwW : w < Generic.wordSize := hwlt
      have haW : a < Generic.wordSize := lt_trans ha (by decide)
      have hrel1 : StmtRel ρ E ctx Q S1 :=
        post_rel hd hctxs hctxf (by subst hctx; rfl) (by subst hctx; rfl) Rt.state Q (fun _ => by rw [← hQ]; rfl) (by rw [← hQ]; show Rt.state.events = _; rw [hRs, ← hrt0, ← hst])
          S1.scopes (by
            rw [hQl]
            simp [frameOf, S1, WExpr.eval, Nat.mod_eq_of_lt hwW, Nat.mod_eq_of_lt haW])
      obtain ⟨r1, hr1, hl1⟩ := eval_stmt ρ E ctx (k + 2) (Stmt.assign (LValue.var "_sol_hoist_0")
        (Expr.castOp CastKind.uintCleanup 256 (Expr.var "__ext0"))) S1 _ rfl _ hrel1
      rw [hr1] at hrun
      let S1' : SymState := ⟨[[("__ext0", .lit w)], [("_sol_hoist_0", .lit w), ("_sol_hoist_1", .lit 1)], [],
        [("o", .lit a), ("_ret0", .lit 0)]], [], [], .lit SolidCore.Refinement.Generic.callerWord, [], [], none⟩
      have hl1' : LeafRel ρ E ctx r1 (.normal S1') := hl1
      cases r1 with
      | normal rt1 =>
        have hrel2 : StmtRel ρ E ctx rt1.popScope S1'.pop := StmtRel.popScope hl1'
        obtain ⟨r2, hr2, hl2⟩ := eval_stmt ρ E ctx (k + 2 + 1) (Stmt.returnValues
                  [Expr.castOp (CastKind.uintCleanup) 256
                    (Expr.castOp (CastKind.uintCleanup) 256
                      (Expr.binary (BinaryOp.add)
                        (Expr.castOp (CastKind.uintCleanup) 256 (Expr.var "_sol_hoist_0"))
                        (Expr.castOp (CastKind.uintCleanup) 256 (Expr.var "_sol_hoist_1"))))]) S1'.pop _ rfl _ hrel2
        simp only [done_bind', Result.mapRuntime, sbind_pure, evalList_cons] at hrun
        rw [hr2] at hrun
        simp only [Br.eval, guards, List.foldr, ordered_nil, codeOf_lt, List.nil_append, List.append_nil,
          List.cons_append] at hl2
        have hg : (WExpr.bin BinOp.lt (WExpr.bin BinOp.add (WExpr.lit w) (WExpr.lit 1)) (WExpr.lit w)).eval ρ =
            if w + 1 = 2 ^ 256 then 1 else 0 := by
          exact guard_add_one ρ w hwlt
        rw [hg] at hl2
        by_cases hov : w + 1 = 2 ^ 256
        · rw [if_pos hov, if_neg (by decide)] at hl2
          cases r2 with
          | reverted rt2 data =>
            have hdata : data = .panic 17 := hl2
            subst hdata
            simp only [done_bind', sbind_pure, Result.mapRuntime, map_pure', foldAns_pure,
              FunctionDef.callBodyResult] at hrun
            have hpd : (panicBytes 17).map (OByte.eval ρ) = Skim.panicData := by rfl
            simp only [RevertData.untagFixedBytes, encode_panic ρ, hpd, Option.bind_eq_bind, Option.bind_some,
              Option.map_some] at hrun
            rw [← hrun]
            have hns : ¬ r.returnData.size < 32 := by omega
            have hovr : (Sync.retWord r).toNat + 1 = 2 ^ 256 := by rw [hv]; exact hov
            simp only [Source.observe, obsOfS, hs, ↓reduceIte, hns, hovr, Bool.false_eq_true]
            rfl
          | _ => exact absurd hl2 id
        · rw [if_neg hov, if_pos rfl] at hl2
          cases r2 with
          | returned rt2 vs =>
            obtain ⟨hrel3, hvs⟩ := hl2
            simp only [done_bind', sbind_pure, Result.mapRuntime, map_pure', foldAns_pure,
              FunctionDef.callBodyResult] at hrun
            have hw1 : w + 1 < 2 ^ 256 := Nat.lt_of_le_of_ne hwlt hov
            have hv1 : WExpr.eval ρ (.bin .add (.lit w) (.lit 1)) = w + 1 := by
              simp [WExpr.eval, BinOp.eval, Generic.wordSize, Nat.mod_eq_of_lt hwlt, Nat.mod_eq_of_lt hw1]
              exact hw1
            subst hvs
            simp only [retVals_nil, List.map_cons, List.map_nil, hv1] at hrun
            have hco : readFn.coerceReturnValues rt2.popScope.popScope [Value.word (w + 1)] = .ok [Value.word (w + 1)] := by
              simp [FunctionDef.coerceReturnValues, readFn, coerceReturnBindings, coerceReturnBindings.coerce,
                deref_word', coerce_param (Or.inl rfl) (w + 1), bind, Except.bind, pure, Except.pure]
            have henc : ABI.encodeValues? (List.map BindingDecl.ty readFn.returns) [Value.word (w + 1)] =
                some (ABI.encodeWord (w + 1)) := by
              simp [readFn, ABI.encodeValues?, ABI.Ty.listAbiHeadWords?, ABI.Ty.abiHeadWords?, ABI.Ty.isDynamicAbi,
                ABI.Ty.staticAbiHeadWords?, ABI.encodeValuesAux?, ABI.encodeStaticValue?, bind, Option.bind]
            simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte, hco, List.map_cons, List.map_nil,
              Value.untagFixedBytes, henc, Option.bind_eq_bind, Option.bind_some, Option.map_some] at hrun
            have hev : rt2.state.events = [] := by
              have := hrel3.logs
              simp only [S1', SymState.pop, List.map_nil, List.map_eq_nil_iff] at this
              exact this
            rw [← hrun]
            have hnov : ¬ (Sync.retWord r).toNat + 1 = 2 ^ 256 := by rw [hv]; exact hov
            simp only [Source.observe, obsOfS, hs, ↓reduceIte, show ¬ r.returnData.size < 32 by omega, hnov,
              Runtime.popScope, State.logEntries, hev, List.map_nil, hv, encodeWord_eq, hov]
            have hst2 : (fun slot => rt2.state.loadSlot slot) = fun slot => storageIn r.postWorld slot := by
              funext slot
              rw [loadSlot_eq rt2.state S1'.pop.writes ρ (postVal_ok _) hrel3.store slot]
              rfl
            rw [hst2]
            rfl
          | _ => exact absurd hl2 id
      | _ => exact absurd hl1' id


/-- info: 'SolidCore.Refinement.Reader.read_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms read_source

end SolidCore.Refinement.Reader

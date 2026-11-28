import SolidCore.Refinement.Generic.CallSource
import SolidCore.Refinement.Generic.StageIn
import Contracts.CallFamilies.SkimSource
import Contracts.CallFamilies.SyncSource

/-!
# SolidCore runs a function with one external call as its call tree

`source_runC`: in an open world, SolidCore runs a call of a function of the call fragment as its
call tree, with the world's answer to the call's request as the callee's answer, read after the
call's argument words.
-/

namespace SolidCore.Refinement.Generic
open SolidCore.Solidity.Source SolidCore.Refinement SolidCore.Refinement.CallNode EvmCompiler.Simulation

/-! ## Pieces of the evaluation -/

theorem eval_localStmt (f : Nat) (tbl : FunctionTable) (ctx : Context) (rt : Runtime) :
    ∀ s : Stmt, localStmt s = true →
      ∃ rt', Stmt.eval (f + 1) tbl ctx rt s = .done (.ok (.normal rt')) ∧ rt'.state = rt.state
  | .skip, _ => ⟨rt, by rw [Stmt.eval]; rfl, rfl⟩
  | .varDecl ty x none, _ => ⟨rt.declareLocal x ty.defaultValue, by rw [eval_varDecl_none]; rfl, rfl⟩
  | .varDecl ty x (some (.word w)), hs => by
    simp only [localStmt] at hs
    refine ⟨rt.declareLocal x (.word (normWord w)), ?_, rfl⟩
    rw [Stmt.eval]
    simp [Expr.eval, Expr.evalFuel]
    rw [show ((pure (Value.word (normWord w), rt) : SolI (Value × Runtime))).caught =
      .done (.ok (.ok (Value.word (normWord w), rt))) from rfl]
    simp [bind_done_ok, (wordTy_coerce hs _).1]
    rfl


theorem encode_sel_eval (ctx : Context) (rt : Runtime) (sel : Nat) :
    (Expr.encode (EncodeKind.withSelector) (some (Expr.word sel)) [] [] []).evalWithRuntimeByContext ctx rt =
      .ok (.bytes (wordToBytesBE selectorBytes (SolidCore.Solidity.Shared.norm (normWord sel))), rt) := by
  simp only [Expr.evalWithRuntimeByContext, Expr.eval, Expr.orderFuel, Expr.evalFuel,
    Expr.listEvalFuel, Expr.evalListFuel]
  simp [Runtime.materializeForValueUseList, bind, pure, liftM, monadLift,
    MonadLift.monadLift, SolI.ofExcept, ipure_bind, Value.expectWord, abiEncodeValues?, SolI.foldExpr,
    Ty.listAbiHeadWords?, abiEncodeValuesAux?]
  rfl

theorem foldExpr_done {α : Type} (fuel : Nat) (ctx : Context) (a : α) :
    SolI.foldExpr (fuel + 1) ctx (.done (.ok a)) = .ok a := by
  simp [SolI.foldExpr, SolI.runFromContext]

theorem callStmt?_spec {s : Stmt} {tgt : Expr} {sel : Nat} {x : String} {succ : Stmt}
    (h : callStmt? s = some (tgt, sel, x, succ)) :
    s = .tryExternalCall .staticcall tgt (.encode .withSelector (some (.word sel)) [] [] []) (.word 0) none
      false false [⟨x, .uint256, false⟩] [.uint 256] succ [] := by
  unfold callStmt? at h
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl, rfl⟩ := h
    rfl
  · simp at h

theorem addressToWord_wordToAddress (x : Nat) : addressToWord (wordToAddress x) = x % 2 ^ 160 := by
  simp [addressToWord, wordToAddress, wordToU256, EvmYul.AccountAddress.ofUInt256]
  simp [EvmYul.UInt256.ofNat, EvmYul.AccountAddress.size, Fin.ofNat, Id.run, EvmYul.UInt256.size]


theorem input_selBytes (ρ : Val) (sel : Nat) (hsel : sel < 2 ^ 32) :
    byteArrayToBytes (bytesToByteArray ((wordToBytesBE selectorBytes
      (SolidCore.Solidity.Shared.norm (normWord sel))).map normByte)) = (selBytes sel).map (OByte.eval ρ) := by
  have hn : SolidCore.Solidity.Shared.norm (normWord sel) = sel := by
    simp only [SolidCore.Solidity.Shared.norm, normWord]
    rw [Nat.mod_mod, Nat.mod_eq_of_lt (lt_trans hsel (by decide))]
  rw [hn]
  simp [selectorBytes, wordToBytesBE, selBytes, litBytes, List.range_succ, OByte.eval, normByte,
    SolidCore.Solidity.Shared.Account.byte, byteArrayToBytes, bytesToByteArray,
    Nat.div_div_eq_div_mul]

theorem wordAt_zero (data : List Nat) (hb : ∀ x ∈ data, x < 256) (h : 32 ≤ data.length) :
    wordAt data 0 = bytesToWordBE ((data.map normByte).take 32) := by
  unfold wordAt dataMem SolarTV.Machine.Mem.load SolarTV.Machine.Mem.read
  rw [SolidCore.Refinement.CallFamilies.fold_bv]
  unfold bytesToWordBE SolidCore.Solidity.Shared.norm
  simp only [List.map_map, Nat.zero_add]
  rw [List.foldl_map]
  have hl : (List.map normByte data).take 32 = (List.range 32).map (fun i => data.getD i 0) := by
    apply List.ext_getElem
    · simp; omega
    · intro j h1 h2
      simp only [List.getElem_take, List.getElem_map, List.getElem_range, List.getD_eq_getElem?_getD]
      simp at h2
      rw [List.getElem?_eq_getElem (by simp at h1; omega)]
      simp [normByte, SolidCore.Solidity.Shared.Account.byte]
      exact hb _ (List.getElem_mem _)
  rw [hl, List.foldl_map]
  have hm : SolidCore.Solidity.Shared.wordModulus = 2 ^ 256 := rfl
  rw [hm]
  simp only [Function.comp, BitVec.toNat_ofNat, normByte, SolidCore.Solidity.Shared.Account.byte]
  rfl

theorem bytes_lt (rd : ByteArray) : ∀ x ∈ byteArrayToBytes rd, x < 256 := by
  intro x hx
  simp only [byteArrayToBytes, List.mem_map] at hx
  obtain ⟨b, _, rfl⟩ := hx
  exact b.toNat_lt

/-! ## The run of a computation with one external call -/

/-- The request SolidCore sends for a call node's request: a `STATICCALL` of the target with no
value and the input bytes. -/
structure ReqOK (ρ : Val) (r : CReq) (request : CallRequest) : Prop where
  kind : request.kind = .staticcall
  callee : addressToWord request.codeAddress = r.target.eval ρ % 2 ^ 160
  value : u256ToWord request.transferValue = 0
  input : byteArrayToBytes request.calldata = r.input.map (OByte.eval ρ)

/-- The answer to a call as the callee's answer of the call tree. -/
def toCAns (resp : CallResponse) : CAns := ⟨resp.success, byteArrayToBytes resp.returnData⟩

/-- An answer the stage admits for the valuation `ρ` and the world `world` sent: a static call's
answer keeps the caller's storage, its return data is shorter than `2 ^ 256` bytes, and the
valuation reads its words after the `n` argument words. -/
structure RespOK (ρ : Val) (n : Nat) (world : SolidCore.Solidity.Shared.OpenWorld) (resp : CallResponse) : Prop where
  static : ∀ slot, storageIn resp.postWorld slot = storageIn world slot
  size : resp.returnData.size < 2 ^ 256
  val : ρ.withAns n (toCAns resp) = ρ

/-- **How a computation with one external call runs**: it asks the call of `world` with a request
the call node describes, and every answer the stage admits finishes it: a success with a result
the branch tree `k` describes, a failure with a revert of the callee's return data. -/
def CallRun (ρ : Val) (E : EraseEnv) (ctx : Context) (world : SolidCore.Solidity.Shared.OpenWorld) (n : Nat)
    (r : CReq) (k : Br) (t : SolI Result) : Prop :=
  ∃ request kont, t = .request (.external world (.call request)) kont ∧ ReqOK ρ r request ∧
    ∀ resp, RespOK ρ n world resp →
      (resp.success = true → ∃ res, kont resp = .done (.ok res) ∧ LeafRel ρ E ctx res (k.eval ρ)) ∧
      (resp.success = false → ∃ rt', kont resp =
        .done (.ok (.reverted rt' (RevertData.fromRawBytes (byteArrayToBytes resp.returnData)))))

theorem RespOK.arg_size {ρ : Val} {n : Nat} {world : SolidCore.Solidity.Shared.OpenWorld} {resp : CallResponse}
    (h : RespOK ρ n world resp) : (WExpr.arg n).eval ρ = resp.returnData.size := by
  have e := withAns_size ρ n (toCAns resp)
  rw [h.val] at e
  have hlen : (toCAns resp).data.length = resp.returnData.size := by
    simp [toCAns, byteArrayToBytes_eq]
  simp only [WExpr.eval, e, hlen, Nat.mod_eq_of_lt h.size]

theorem RespOK.arg_word {ρ : Val} {n : Nat} {world : SolidCore.Solidity.Shared.OpenWorld} {resp : CallResponse}
    (h : RespOK ρ n world resp) (h32 : 32 ≤ resp.returnData.size) :
    (WExpr.arg (n + 1)).eval ρ = bytesToWordBE ((byteArrayToBytes resp.returnData).map normByte |>.take 32) := by
  have hlen : (toCAns resp).data.length = resp.returnData.size := by
    simp [toCAns, byteArrayToBytes_eq]
  have e := withAns_word ρ n (toCAns resp) (k := 0) (by rw [hlen]; omega)
  rw [h.val] at e
  simp only [Nat.add_zero, Nat.mul_zero] at e
  simp only [WExpr.eval, e, toCAns]
  rw [wordAt_zero _ (bytes_lt _) (by simp [toCAns, byteArrayToBytes_eq]; omega)]
  exact Nat.mod_eq_of_lt (Nat.mod_lt _ (by decide))


/-! ## The call statement -/

theorem norm_word_lt {v : Nat} (h : v < wordSize) : SolidCore.Solidity.Shared.norm v = v :=
  Nat.mod_eq_of_lt h

/-- **The call statement runs as its call node.** -/
theorem callRun_callStmt (ρ : Val) (E : EraseEnv) (ctx : Context) (n f : Nat) {s : Stmt} {S : SymState}
    {r : CReq} {k : Br} (h : eraseCallStmt E n f s S = some (r, k)) (rt : Runtime)
    (hrel : StmtRel ρ E ctx rt S) (hctxs : ctx.self = selfAddress)
    (hself : r.target.eval ρ ≠ selfAddress)
    (hW0 : ∀ slot < 2 ^ 256, storageIn (snapshotWorld ctx rt.state) slot = ρ.store slot) :
    CallRun ρ E ctx (snapshotWorld ctx rt.state) n r k (Stmt.eval (f + 1) E.tbl ctx rt s) := by
  unfold eraseCallStmt at h
  split at h
  · simp at h
  rename_i tgt sel x succ hcs
  have hs := callStmt?_spec hcs
  subst hs
  split at h
  case isFalse => simp at h
  rename_i hcond
  obtain ⟨hw, hl, hsel, htag⟩ := hcond
  split at h
  · rename_i t het
    split at h
    · rename_i b hb
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have heval := eval_eq ρ E.fields ctx rt S hrel.expr het
      have ht : tgt.evalWithRuntimeByContext ctx rt = .ok (.word (t.eval ρ), rt) := by
        simp only [Expr.evalWithRuntimeByContext, heval, exprResult, List.any_nil, Bool.false_eq_true,
          ↓reduceIte]
        exact foldExpr_done _ _ _
      have htw : (Value.word (t.eval ρ)).expectWord = .ok (t.eval ρ) := by
        simp [Value.expectWord, norm_word_lt (t.eval_lt ρ)]
      have hne : wordEq (t.eval ρ) ctx.self = false := by
        rw [hctxs]
        simp only [wordEq, norm_word_lt (t.eval_lt ρ),
          norm_word_lt (show selfAddress < wordSize by decide), beq_eq_false_iff_ne, ne_eq]
        exact hself
      rw [eval_tryCall f E.tbl ctx rt .staticcall tgt _ (.word 0) false _ _ succ [] ht htw (word0_eval ctx rt)
        rfl (encode_sel_eval ctx rt sel) rfl hne]
      refine ⟨_, _, rfl, ⟨rfl, ?_, ?_, ?_⟩, ?_⟩
      · simp [buildCallRequest, addressToWord_wordToAddress]
      · simp [buildCallRequest, u256ToWord, wordToU256]; rfl
      · exact input_selBytes ρ sel hsel
      · intro resp hresp
        have hsz := hresp.arg_size
        refine ⟨fun hsucc => ?_, fun hfail => ?_⟩
        · simp only [tryTail, decodeCallResponse, hsucc, ↓reduceIte, normByte_bytes, List.map_cons, List.map_nil]
          by_cases hlen : resp.returnData.size < 32
          · have hlen' : (byteArrayToBytes resp.returnData).length < 32 := by
              rw [byteArrayToBytes_eq, List.length_map, List.length_range]; exact hlen
            rw [decode_short _ hlen']
            refine ⟨_, rfl, ?_⟩
            have hc : (WExpr.bin .lt (.arg n) (.lit 32)).eval ρ ≠ 0 := by
              show (if (WExpr.arg n).eval ρ < (32 : Nat) % wordSize then 1 else 0) % wordSize ≠ 0
              rw [hsz, if_pos (by rw [Nat.mod_eq_of_lt (by decide)]; exact hlen)]
              decide
            simp only [Br.eval, hc, ↓reduceIte]
            rfl
          · have h32 : 32 ≤ resp.returnData.size := by omega
            have hlen' : 32 ≤ (byteArrayToBytes resp.returnData).length := by
              rw [byteArrayToBytes_eq, List.length_map, List.length_range]; exact h32
            rw [decode_word _ hlen']
            simp only [normByte_bytes]
            have hw1 := hresp.arg_word h32
            simp only [normByte_bytes] at hw1
            generalize hwd : bytesToWordBE (List.take 32 (byteArrayToBytes resp.returnData)) = w at hw1 ⊢
            have hwlt : w < 2 ^ 256 := by rw [← hwd]; exact Nat.mod_lt _ (by decide)
            have hacc : AbiCleanups.acceptOrUnspecified [AbiCleanup.uint 256] [Value.word w] = true := by
              have : AbiCleanups.accept [AbiCleanup.uint 256] [Value.word w] = true := by
                simp [AbiCleanups.accept, AbiCleanup.accepts, SolidCore.Solidity.Shared.norm]
                exact decide_eq_true (Nat.mod_lt w (by decide : 0 < Solidity.Shared.wordModulus))
              simp [AbiCleanups.acceptOrUnspecified, this]
            have hbind : BindingDecl.bindArgs? [{ name := x, ty := Ty.uint256 }] [Value.word w] =
                some [(x, Value.word w)] := by
              simp [BindingDecl.bindArgs?, BindingDecl.bindArg?, Ty.coerceValue?, SolidCore.Solidity.Shared.norm,
                Nat.mod_eq_of_lt hwlt]
            simp only [hacc, hbind, ↓reduceIte]
            have hrel' : StmtRel ρ E ctx
                (({ rt with state := adoptWorld resp.postWorld ctx rt.state }.recordExternalInteraction
                  (ExternalInteraction.lowLevelCall
                    { kind := LowLevelCallKind.staticcall, target := WExpr.eval ρ t,
                      calldata := List.map normByte (wordToBytesBE selectorBytes (Solidity.Shared.norm (normWord sel))),
                      value := Solidity.Shared.norm 0, success := true,
                      output := byteArrayToBytes resp.returnData })).withFrame [(x, Value.word w)])
                { S with scopes := [(x, .arg (n + 1))] :: S.scopes } :=
              { fields := hrel.fields, events := hrel.events, checked := hrel.checked, sender := hrel.sender,
                hash := hrel.hash, ok := hrel.ok, facts := hrel.facts
                frames := by
                  simp only [Runtime.withFrame, Runtime.recordExternalInteraction, hrel.frames, List.map_cons,
                    frameOfT, htag, Tag.val_word, List.map_nil, hw1]
                store := fun j hj => by
                  show (adoptWorld resp.postWorld ctx rt.state).loadSlot j = _
                  rw [SolidCore.Refinement.CallFamilies.adopt_load hctxs, hresp.static, hW0 j hj, hw]
                  rfl
                logs := by
                  simp only [Runtime.withFrame, Runtime.recordExternalInteraction, adoptWorld]
                  exact hrel.logs
                mem := hrel.mem
                next := hrel.next }
            obtain ⟨res, hres, hleaf⟩ := eval_stmt ρ E ctx f succ _ b hb _ hrel'
            rw [hres]
            refine ⟨res.mapRuntime Runtime.popScope, rfl, ?_⟩
            have hc : (WExpr.bin .lt (.arg n) (.lit 32)).eval ρ = 0 := by
              show (if (WExpr.arg n).eval ρ < (32 : Nat) % wordSize then 1 else 0) % wordSize = 0
              rw [hsz, if_neg (by rw [Nat.mod_eq_of_lt (by decide)]; omega)]
              rfl
            simp only [Br.eval, hc, ↓reduceIte, Br.eval_mapS]
            exact hleaf.popScope
        · simp only [tryTail, decodeCallResponse, hfail, Bool.false_eq_true, ↓reduceIte, findMatch_nil,
            normByte_bytes]
          exact ⟨_, rfl⟩
    · simp at h
  · simp at h


/-! ## Blocks and statement lists -/

theorem CallRun.bind {ρ : Val} {E : EraseEnv} {ctx : Context} {world : SolidCore.Solidity.Shared.OpenWorld}
    {n : Nat} {r : CReq} {k k' : Br} {t : SolI Result} (h : CallRun ρ E ctx world n r k t)
    (g : Result → SolI Result)
    (hg : ∀ res, LeafRel ρ E ctx res (k.eval ρ) → ∃ res', g res = .done (.ok res') ∧ LeafRel ρ E ctx res' (k'.eval ρ))
    (hrev : ∀ rt' d, ∃ rt'', g (.reverted rt' d) = .done (.ok (.reverted rt'' d))) :
    CallRun ρ E ctx world n r k' (t >>= g) := by
  obtain ⟨request, kont, rfl, hreq, hans⟩ := h
  refine ⟨request, fun a => kont a >>= g, by rw [bind_request], hreq, fun resp hresp => ⟨fun hs => ?_, fun hf => ?_⟩⟩
  · obtain ⟨res, hres, hleaf⟩ := (hans resp hresp).1 hs
    obtain ⟨res', hg1, hg2⟩ := hg res hleaf
    exact ⟨res', by simp only [hres]; exact hg1, hg2⟩
  · obtain ⟨rt', hres⟩ := (hans resp hresp).2 hf
    obtain ⟨rt'', hg1⟩ := hrev rt' _
    exact ⟨rt'', by simp only [hres]; exact hg1⟩

/-- **A statement list that reaches the external call runs as its call node.** -/
theorem callRun_seq (ρ : Val) (E : EraseEnv) (ctx : Context) (n f : Nat)
    (world : SolidCore.Solidity.Shared.OpenWorld) (X0 : SolidCore.Solidity.Source.State)
    {fC : Stmt → SymState → Option (CReq × Br)}
    (hC : ∀ s S r k, fC s S = some (r, k) → r.target.eval ρ ≠ selfAddress → ∀ rt, StmtRel ρ E ctx rt S →
      rt.state = X0 → CallRun ρ E ctx world n r k (Stmt.eval f E.tbl ctx rt s)) :
    ∀ ss S r k, eraseSeqC fC (eraseStmt E f) ss S = some (r, k) → r.target.eval ρ ≠ selfAddress →
      ∀ rt, StmtRel ρ E ctx rt S → rt.state = X0 → CallRun ρ E ctx world n r k (Stmt.evalList f E.tbl ctx rt ss)
  | [], S, r, k, h, _, _, _, _ => by simp [eraseSeqC] at h
  | s :: rest, S, r, k, h, hself, rt, hrel, hX => by
    simp only [eraseSeqC] at h
    rw [evalList_cons]
    split at h
    · -- a local declaration
      rename_i hloc
      split at h
      · rename_i S' hb
        obtain ⟨res, hres, hleaf⟩ := eval_stmt ρ E ctx f s S _ hb rt hrel
        cases f with
        | zero => simp [eraseStmt] at hb
        | succ f =>
          obtain ⟨rt', hrt', hst⟩ := eval_localStmt f E.tbl ctx rt s hloc
          rw [hrt'] at hres
          cases hres
          rw [hrt']
          simp only [Br.eval] at hleaf
          exact callRun_seq ρ E ctx n (f + 1) world X0 hC rest S' r k h hself rt' hleaf (by rw [hst, hX])
      · simp at h
    · -- the statement with the call
      split at h
      · rename_i r0 k0 hc
        split at h
        · rename_i k' hk
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          refine (hC s S r0 k0 hc hself rt hrel hX).bind _ ?_ ?_
          · intro res hleaf
            have hb := Br.bind_eval ρ hk
            generalize hl : k0.eval ρ = l at hb hleaf
            cases l with
            | normal S1 =>
              obtain ⟨c, hc1, hc2⟩ := hb
              cases res <;> simp only [LeafRel] at hleaf
              rename_i rt1
              obtain ⟨res', hres', hleaf'⟩ := eval_seq_of ρ E ctx f
                (fun s S b h rt hrel => eval_stmt ρ E ctx f s S b h rt hrel) rest S1 c hc1 rt1 hleaf
              exact ⟨res', hres', by rw [hc2]; exact hleaf'⟩
            | returned S1 vs =>
              cases res <;> simp only [LeafRel] at hleaf
              exact ⟨_, rfl, by rw [hb]; exact hleaf⟩
            | reverted p =>
              cases res <;> simp only [LeafRel] at hleaf
              exact ⟨_, rfl, by rw [hb]; exact hleaf⟩
          · intro rt' d
            exact ⟨rt', rfl⟩
        · simp at h
      · simp at h

theorem eraseStmtC_other (E : EraseEnv) (n f : Nat) {s : Stmt} (hs : ∀ ss, s ≠ .block ss) (S : SymState) :
    eraseStmtC E n (f + 1) s S = eraseCallStmt E n f s S := by
  cases s <;> first | rfl | exact absurd rfl (hs _)

/-- **A statement with the external call, at the top of nested blocks, runs as its call node.** -/
theorem callRun_stmt (ρ : Val) (E : EraseEnv) (ctx : Context) (n : Nat)
    (X0 : SolidCore.Solidity.Source.State) (hctxs : ctx.self = selfAddress)
    (hW0 : ∀ slot < 2 ^ 256, storageIn (snapshotWorld ctx X0) slot = ρ.store slot) :
    ∀ f s S r k, eraseStmtC E n f s S = some (r, k) → r.target.eval ρ ≠ selfAddress →
      ∀ rt, StmtRel ρ E ctx rt S → rt.state = X0 →
        CallRun ρ E ctx (snapshotWorld ctx X0) n r k (Stmt.eval f E.tbl ctx rt s)
  | 0, s, S, r, k, h, _, _, _, _ => by simp [eraseStmtC] at h
  | f + 1, s, S, r, k, h, hself, rt, hrel, hX => by
    by_cases hb : ∃ ss, s = .block ss
    · obtain ⟨ss, rfl⟩ := hb
      simp only [eraseStmtC] at h
      split at h
      · rename_i r0 k0 hseq
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        rw [eval_block]
        refine (callRun_seq ρ E ctx n f (snapshotWorld ctx X0) X0
          (fun s S r k h hs rt hrel hX => callRun_stmt ρ E ctx n X0 hctxs hW0 f s S r k h hs rt hrel hX)
          ss S.push r0 k0 hseq hself rt.pushScope hrel.pushScope hX).bind _ ?_ ?_
        · intro res hleaf
          exact ⟨_, rfl, by rw [Br.eval_mapS]; exact hleaf.popScope⟩
        · intro rt' d
          exact ⟨rt'.popScope, rfl⟩
      · simp at h
    · rw [eraseStmtC_other E n f (fun ss hs => hb ⟨ss, hs⟩) S] at h
      rw [← hX]
      exact callRun_callStmt ρ E ctx n f h rt hrel hctxs hself (by rw [hX]; exact hW0)


/-! ## The function -/

/-- How the ABI dispatcher finishes a call of ¤fn¤ from its result, as ¤callCalldata¤ does. -/
def finishCall (core : Contract) (fn : FunctionDef) : Option CallResult → Option ABI.AbiCallResult
  | some (CallResult.returned state' values) => do
    let output ← ABI.encodeValues? (fn.returns.map BindingDecl.ty) values
    some { success := true, output, state := state' }
  | some (CallResult.reverted state' revert) => do
    let output ← ABI.Contract.encodeRevertData? core revert
    some { success := false, output, state := state' }
  | none => none

/-- **A body that ends as the leaf of a branch tree finishes the call as the leaf's tree.** -/
theorem finish_leaf {c : SolidCore.Solidity.TypeCheck.CheckedContract} {fn : FunctionDef} {ρ : Val} {K : Facts}
    (hK : K.Hold ρ) (hρok : ρ.Ok) {σ : List (Nat × Nat)} (hρ : ρ.store = slotValue σ) {ctx : Context}
    {st0 : SolidCore.Solidity.Source.State} {r : Result} {l : Leaf} {T' : Tree}
    (hleaf : LeafRel ρ { envOf c.core with facts := K } ctx r l) (hT' : leafTree fn K l = some T')
    (call : Call) (hcs : call.storage = σ) :
    Option.map (Source.observe call) (finishCall c.core fn (some (fn.callBodyResult st0 r))) =
      some (T'.eval ρ).obs := by
  simp only [finishCall]
  cases l with
  | normal S =>
    cases r <;> simp only [LeafRel] at hleaf
    rename_i rt
    simp only [leafTree, Option.bind_eq_bind, Option.bind_eq_some_iff] at hT'
    obtain ⟨ws, hws, hT'⟩ := hT'
    split at hT'
    case isFalse => simp at hT'
    rename_i hok
    simp only [Option.some.injEq] at hT'
    subst hT'
    simp only [FunctionDef.callBodyResult, FunctionDef.collectReturns, collectReturnBindings,
      collect_vals ρ rt S hK hleaf fn.returns ws hok hws, untag_vals ρ _ ws hK hok,
      encode_vals ρ hK fn.returns _ ws hok, bind, Option.bind, Option.map_some]
    simp only [Source.observe, Tree.eval, Res.obs, ↓reduceIte, logEntries_map,
      hleaf.logs, Option.some.injEq, Observable.mk.injEq, true_and]
    funext slot
    exact loadSlot_eq _ S.writes ρ hρok hleaf.store slot
  | returned S vs ts =>
    cases r <;> simp only [LeafRel] at hleaf
    rename_i rt vals
    obtain ⟨hst', rfl⟩ := hleaf
    by_cases hv : vs = []
    · subst hv
      simp only [retVals_nil_vals]
      simp only [leafTree, if_true, Option.bind_eq_bind, Option.bind_eq_some_iff] at hT'
      obtain ⟨ws, hws, hT'⟩ := hT'
      split at hT'
      case isFalse => simp at hT'
      rename_i hok
      simp only [Option.some.injEq] at hT'
      subst hT'
      simp only [FunctionDef.callBodyResult, List.map_nil, List.isEmpty_nil, if_true,
        FunctionDef.collectReturns, collectReturnBindings,
        collect_vals ρ rt S hK hst' fn.returns ws hok hws, untag_vals ρ _ ws hK hok,
        encode_vals ρ hK fn.returns _ ws hok, bind, Option.bind, Option.map_some]
      simp only [Source.observe, Tree.eval, Res.obs, ↓reduceIte, logEntries_map,
        hst'.logs, Option.some.injEq, Observable.mk.injEq, true_and]
      funext slot
      exact loadSlot_eq _ S.writes ρ hρok hst'.store slot
    · simp only [leafTree, hv, if_false] at hT'
      split at hT'
      case isFalse => simp at hT'
      rename_i hok
      simp only [Option.some.injEq] at hT'
      subst hT'
      have hne : (retVals ρ ts vs).isEmpty = false := by
        cases vs with
        | nil => exact absurd rfl hv
        | cons _ _ => cases ts <;> rfl
      simp only [FunctionDef.callBodyResult, hne, Bool.false_eq_true, if_false,
        FunctionDef.coerceReturnValues, coerceReturnBindings,
        coerce_vals ρ rt hK fn.returns ts vs hok, untag_vals ρ ts vs hK hok,
        encode_vals ρ hK fn.returns ts vs hok, bind, Option.bind, Option.map_some]
      simp only [Source.observe, Tree.eval, Res.obs, ↓reduceIte, logEntries_map,
        hst'.logs, Option.some.injEq, Observable.mk.injEq, true_and]
      funext slot
      exact loadSlot_eq _ S.writes ρ hρok hst'.store slot
  | reverted p =>
    cases r <;> simp only [LeafRel] at hleaf
    subst hleaf
    cases p with
    | empty =>
      simp only [leafTree, Option.some.injEq] at hT'
      subst hT'
      simp [FunctionDef.callBodyResult, RevertData.untagFixedBytes, Fail.data,
        ABI.Contract.encodeRevertData?, Source.observe, Tree.eval, Res.obs, hρ, hcs]
    | panic c =>
      simp only [leafTree, Option.some.injEq] at hT'
      subst hT'
      simp [FunctionDef.callBodyResult, RevertData.untagFixedBytes, Fail.data, encode_panic ρ,
        Source.observe, Tree.eval, Res.obs, hρ, hcs]
    | error m =>
      simp only [leafTree, Option.map_eq_some_iff] at hT'
      obtain ⟨bs, hbs, rfl⟩ := hT'
      simp [FunctionDef.callBodyResult, RevertData.untagFixedBytes, Fail.data, encode_error ρ _ hbs,
        Source.observe, Tree.eval, Res.obs, hρ, hcs]

theorem revert_raw_bytes (core : Contract) (a : CallResponse) :
    ABI.Contract.encodeRevertData? core (RevertData.fromRawBytes (byteArrayToBytes a.returnData)).untagFixedBytes =
      some (byteArrayToBytes a.returnData) := by
  unfold RevertData.fromRawBytes
  split
  · rename_i he
    simp only [beq_iff_eq, normByte_bytes] at he
    simp only [RevertData.untagFixedBytes, ABI.Contract.encodeRevertData?, he]
  · simp only [RevertData.untagFixedBytes, ABI.Contract.encodeRevertData?, Option.some.injEq]
    exact normByte_bytes a.returnData

/-- **A failed call that bubbles finishes the call with the callee's return data.** -/
theorem finish_bubble (core : Contract) (fn : FunctionDef) {ρ : Val} {σ : List (Nat × Nat)}
    (hρ : ρ.store = slotValue σ) (st0 : SolidCore.Solidity.Source.State) (rt' : Runtime) (resp : CallResponse)
    (call : Call) (hcs : call.storage = σ) :
    Option.map (Source.observe call) (finishCall core fn (some (fn.callBodyResult st0
      (.reverted rt' (RevertData.fromRawBytes (byteArrayToBytes resp.returnData)))))) =
      some (bubbleRes ρ (toCAns resp)).obs := by
  simp only [finishCall, FunctionDef.callBodyResult, revert_raw_bytes, bind, Option.bind, Option.map_some]
  simp [Source.observe, bubbleRes, Res.obs, toCAns, hρ, hcs]


/-! ## The valuation with the answer's words -/

theorem frameOf_congr {ρ ρ' : Val} : ∀ (L : Locals), (∀ p ∈ L, p.2.eval ρ = p.2.eval ρ') →
    frameOf ρ L = frameOf ρ' L
  | [], _ => rfl
  | p :: L, h => by
    simp only [frameOf, List.map_cons, List.cons.injEq] at *
    refine ⟨by rw [h p List.mem_cons_self], ?_⟩
    have := frameOf_congr L (fun q hq => h q (List.mem_cons_of_mem _ hq))
    simpa [frameOf] using this

theorem frameOfT_congr {ρ ρ' : Val} (T : Tags) : ∀ (L : Locals), (∀ p ∈ L, p.2.eval ρ = p.2.eval ρ') →
    frameOfT ρ T L = frameOfT ρ' T L
  | [], _ => rfl
  | p :: L, h => by
    simp only [frameOfT, List.map_cons, List.cons.injEq] at *
    refine ⟨by rw [h p List.mem_cons_self], ?_⟩
    have := frameOfT_congr T L (fun q hq => h q (List.mem_cons_of_mem _ hq))
    simpa [frameOfT] using this

theorem paramLocals_arg : ∀ (ps : List BindingDecl) (i : Nat), ∀ p ∈ paramLocals ps i,
    ∃ j, p.2 = .arg j ∧ i ≤ j ∧ j < i + ps.length
  | [], _, p, hp => by simp [paramLocals] at hp
  | q :: ps, i, p, hp => by
    simp only [paramLocals, List.mem_cons] at hp
    rcases hp with rfl | hp
    · exact ⟨i, rfl, le_refl _, by simp⟩
    · obtain ⟨j, hj, h1, h2⟩ := paramLocals_arg ps (i + 1) p hp
      exact ⟨j, hj, by omega, by simp; omega⟩

theorem argsClean_append : ∀ (ws args extra : List Nat), ws.length = args.length →
    argsClean ws (args ++ extra) = argsClean ws args
  | [], _, _, _ => by cases ‹List Nat› <;> simp [argsClean] <;> cases ‹List Nat› <;> rfl
  | w :: ws, [], extra, h => by simp at h
  | w :: ws, a :: as, extra, h => by
    simp only [List.cons_append, argsClean]
    rw [argsClean_append ws as extra (by simpa using h)]

theorem ansWords_lt (a : CAns) : ∀ x ∈ ansWords a, x < wordSize := by
  intro x hx
  simp only [ansWords, List.mem_cons, List.mem_map, List.mem_range] at hx
  rcases hx with rfl | ⟨k, _, rfl⟩
  · exact Nat.mod_lt _ (by decide)
  · exact ((dataMem a.data).load (32 * k)).isLt

theorem withAns_append (args : List Nat) (st : Nat → Nat) (hs : Nat → Nat → Nat) (c : Nat) (a : CAns) :
    (⟨args ++ ansWords a, st, hs, c⟩ : Val).withAns args.length a = ⟨args ++ ansWords a, st, hs, c⟩ := by
  simp only [Val.withAns, Val.mk.injEq, and_true]
  congr 1
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [List.length_map, List.length_range] at h1
    simp only [List.getElem_map, List.getElem_range]
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_left h1, List.getElem?_eq_getElem h1]
    rfl

theorem arg_append (args extra : List Nat) (st : Nat → Nat) (hs : Nat → Nat → Nat) (c : Nat) {j : Nat}
    (hj : j < args.length) :
    (WExpr.arg j).eval (⟨args ++ extra, st, hs, c⟩ : Val) = (WExpr.arg j).eval ⟨args, st, hs, c⟩ := by
  simp only [WExpr.eval, List.getD_eq_getElem?_getD, List.getElem?_append_left hj]

/-- The relation at the start of a call, with the answer's words after the argument words. -/
theorem StmtRel.extend {args extra : List Nat} {st : Nat → Nat} {c : Nat} {E : EraseEnv}
    {ctx : Context} {rt : Runtime} {fn : FunctionDef} {cw : Nat}
    (hlen : args.length = fn.params.length)
    (h : StmtRel ⟨args, st, solHash, c⟩ E ctx rt { initState fn with caller := .lit cw })
    (hK : E.facts.Hold ⟨args ++ extra, st, solHash, c⟩) :
    StmtRel ⟨args ++ extra, st, solHash, c⟩ E ctx rt { initState fn with caller := .lit cw } where
  fields := h.fields
  events := h.events
  checked := h.checked
  sender := h.sender
  hash := h.hash
  ok := h.ok
  facts := hK
  store := h.store
  logs := h.logs
  mem := fun _ _ hl => by simp [initState] at hl
  next := h.next
  frames := by
    rw [h.frames]
    simp only [initState, List.map_cons, List.map_nil, List.cons.injEq, and_true]
    apply frameOfT_congr
    intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · obtain ⟨j, hj, _, hj2⟩ := paramLocals_arg fn.params 0 p hp
      rw [hj, arg_append _ _ _ _ _ (by omega)]
    · simp only [List.mem_map] at hp
      obtain ⟨r, _, rfl⟩ := hp
      rfl


/-! ## The run in a world -/

/-- `call_entry` with the state the body starts from: the deployed state with the call's storage,
marked mutated. -/
theorem call_entry_state {c : SolidCore.Solidity.TypeCheck.CheckedContract} {fn : FunctionDef} {ws : List Nat}
    (hw : widthsOf fn.params fn.paramAbiCleanups = some ws)
    (hret : fn.returns.all wordBinding = true) (fuel : Nat) (base : SolidCore.Solidity.Source.Context) (a : Nat)
    (bytes : List Nat) {st0 : SolidCore.Solidity.Source.State} {σ : List (Nat × Nat)}
    (hstore : ∀ k, (st0.storage[k % 2 ^ 256]?).getD 0 = slotValue σ k) (hev : st0.events = [])
    {K : Facts} {args : List Nat} {rc : Nat} (cw : WExpr)
    (hlen : args.length = fn.params.length) (hargs : ∀ a ∈ args, a < 2 ^ 256)
    (hclean : argsClean ws args = true)
    (hK : K.Hold ⟨args, slotValue σ, solHash, rc⟩)
    (hcw : SolidCore.Solidity.Shared.norm a = cw.eval ⟨args, slotValue σ, solHash, rc⟩) :
    ∃ rt, StmtRel ⟨args, slotValue σ, solHash, rc⟩ { envOf c.core with facts := K }
        (ABI.Contract.callContextAtWithBase c.core base selfAddress a 0 bytes) rt
        { initState fn with caller := cw } ∧
      fn.call fuel c.core.table (ABI.Contract.callContextAtWithBase c.core base selfAddress a 0 bytes)
        st0 (args.map .word) =
        some (fn.callBodyResult st0 <$> Stmt.eval fuel c.core.table
          (ABI.Contract.callContextAtWithBase c.core base selfAddress a 0 bytes) rt fn.body) ∧
      rt.state.storage = st0.storage ∧ rt.state.transient = st0.transient ∧
      rt.state.envWorld? = st0.envWorld? ∧ rt.state.worldMutatedSinceAdoption = true := by
  set ctx := ABI.Contract.callContextAtWithBase c.core base selfAddress a 0 bytes with hctx
  set ρ : Val := ⟨args, slotValue σ, solHash, rc⟩ with hρ
  have hr : ∀ r ∈ fn.returns, RetTy r.ty ∧ r.isStorageRef = false :=
    fun r hr => wordBinding_ty (List.all_eq_true.mp hret r hr)
  have hframe : fn.initialFrame? (args.map .word) =
      some (frameOf ρ (paramLocals fn.params 0 ++ fn.returns.map fun r => (r.name, .lit 0))) := by
    have h0 : BindingDecl.bindArgs? fn.params (args.map .word) =
        some (frameOf ρ (paramLocals fn.params 0)) := by
      have h := bindArgs_clean ρ hargs [] fn.params fn.paramAbiCleanups ws 0 (widthsOf_T hw).1
        (by simpa [hρ] using hclean) (by simp [hρ, hlen])
        (fun p hp => by rw [(widthsOf_T hw).2 p hp]; rfl)
      rwa [show ρ.args.drop 0 = args from rfl, argVals_words' (fun ty hty => by
        obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hty
        exact (widthsOf_T hw).2 p hp) (by simpa using hlen)] at h
    simp only [FunctionDef.initialFrame?, h0, FunctionDef.returnDefaultBindings,
      defaults_words ρ fn.returns hr, frameOf, List.map_append]
  have hacc : fn.acceptsValue ctx.value = true := by
    simp [hctx, ABI.Contract.callContextAtWithBase, SolidCore.Solidity.Shared.norm,
      FunctionDef.acceptsValue, wordEq]
  refine ⟨{ state := { st0 with
              selfBalance := SolidCore.Solidity.Shared.addWord
                (SolidCore.Solidity.Shared.Account.balanceAt ctx.accountBalances ctx.self) ctx.value
              worldMutatedSinceAdoption := true }
            locals := [frameOf ρ (paramLocals fn.params 0 ++ fn.returns.map fun r => (r.name, .lit 0))] },
    { fields := rfl, events := rfl, checked := rfl, sender := hcw, hash := rfl,
      ok := slotValue_store σ, frames := by simp [initState, fnTags, paramTags_words (words_of_widths hw hret)],
      facts := hK
      store := fun k _ => by
        simp only [SolidCore.Solidity.Source.State.loadSlot, StorageMap.lookup?, initState, Writes.store, hρ, ← hstore k,
          SolidCore.Solidity.Shared.norm, modulus_eq, Std.HashMap.get?_eq_getElem?]
        cases st0.storage[k % wordSize]? <;> rfl
      logs := by simp [hev, initState]
      mem := fun _ _ hl => by simp [initState] at hl
      next := fun k hk => by
        simp only [initState, Option.some.injEq] at hk
        subst hk
        rfl }, ?_, rfl, rfl, rfl, rfl⟩
  simp only [FunctionDef.call, FunctionDef.evalBodyEntry, hacc, hframe, if_true, Option.map_some]

theorem widthsOf_length : ∀ {ps : List BindingDecl} {cs : List AbiCleanup} {ws : List Nat},
    widthsOf ps cs = some ws → ws.length = ps.length
  | [], [], ws, h => by simp [widthsOf] at h; subst h; rfl
  | p :: ps, c :: cs, ws, h => by
    simp only [widthsOf, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨w, _, ws', hws', rfl⟩ := h
    simp [widthsOf_length hws']
  | [], _ :: _, _, h => by simp [widthsOf] at h
  | _ :: _, [], _, h => by simp [widthsOf] at h

/-- The valuation of a call of argument words `args` from the storage `σ` whose external call
answers `a`: the argument words, then the answer's words. -/
def callVal (args : List Nat) (σ : List (Nat × Nat)) (a : CAns) : Val :=
  ⟨args ++ ansWords a, slotValue σ, solHash, callerWord⟩

theorem callCalldata_finish (ans : Ans) {fuel : Nat} {core : Contract} {base : SolidCore.Solidity.Source.Context}
    {st0 : SolidCore.Solidity.Source.State} {a : Nat} {sel : Nat} (hsel : sel < 2 ^ 32) {fn : FunctionDef}
    (hfind : core.findFunctionBySelector? sel = some fn) {args : List Nat}
    (hdec : ABI.decodeFunctionArgs? fn (Dirty.argBytes args) = .ok (args.map .word)) :
    Source.ABI.Oracle.callCalldata ans fuel core base st0 selfAddress a 0
        ((EthLib.Base.natToBytes 4 sel).map (·.toNat) ++ Dirty.argBytes args) =
      finishCall core fn (Source.callAns ans fuel core.table (ABI.Contract.callContextAtWithBase core base
        selfAddress a 0 ((EthLib.Base.natToBytes 4 sel).map (·.toNat) ++ Dirty.argBytes args)) fn st0
        (args.map .word)) := by
  have hdrop : ((EthLib.Base.natToBytes 4 sel).map (·.toNat) ++ Dirty.argBytes args).drop
      ABI.selectorBytes = Dirty.argBytes args := by
    simp [ABI.selectorBytes, EthLib.Base.natToBytes_length]
  have hacc : fn.acceptsValue 0 = true := by simp [FunctionDef.acceptsValue, wordEq]
  simp only [Source.ABI.Oracle.callCalldata, Dirty.readSelector_calldata _ hsel, hfind, hdrop, hdec, hacc,
    if_true]
  rfl

/-- **SolidCore runs a call of a function of the call fragment as its call node, in a world.** In an
open world whose static calls keep the caller's storage and whose answers to static calls to code
are shorter than `2 ^ 256` bytes, a call on clean argument words of a function whose call tree is
the call node `.call r [] n t` asks the world the call's request (a static call of the target, no
value, the selector's bytes, sent with the deployed storage written by `σ`, no transient storage
and the world's code) and shows the call tree's result with the world's answer, read after the
argument words. The target is argument `j`, which is not the contract itself nor a precompile. -/
theorem source_runC (W : World) (hW : W.Open)
    (hstatic : ∀ h world request a, W.ans h (.external world (.call request)) = some a →
      request.kind = .staticcall → ∀ slot, storageIn a.postWorld slot = storageIn world slot)
    (hfit : ∀ world request a, W.ans [] (.external world (.call request)) = some a →
      request.kind = .staticcall →
      SolidCore.Solidity.Shared.Precompile.kindOfAddress? (addressToWord request.codeAddress) = none →
      a.returnData.size < 2 ^ 256)
    (hkeys : ∀ p ∈ W.codes.getD [], p.1 < 2 ^ 160)
    {fuel : Nat} {c : SolidCore.Solidity.TypeCheck.CheckedContract} {d : SolidCore.Solidity.Source.State}
    (hd : SolidCore.Refinement.Wide.DeployedAt fuel c d [])
    (hcc : c.core.context.accountCodes = []) (hcb : c.core.context.accountBalances = [])
    (hch : c.core.context.accountCodehashes = []) (hdt : d.transient.toList = []) (hde : d.envWorld? = none)
    {sel : Nat} (hsel : sel < 2 ^ 32) {fn : FunctionDef}
    (hfind : c.core.findFunctionBySelector? sel = some fn) {ws : List Nat}
    (hw : widthsOf fn.params fn.paramAbiCleanups = some ws) (hret : fn.returns.all wordBinding = true)
    {r : CReq} {k : Br}
    (hrk : eraseStmtC { envOf c.core with facts := argFacts ws 0 } fn.params.length fuel fn.body
      (initState fn) = some (r, k))
    {t : Tree} (ht : brTree fn (argFacts ws 0) k = some t)
    {j : Nat} (hj : j < fn.params.length) (htgt : r.target = .arg j)
    (args : List Nat) (hlen : args.length = fn.params.length) (hargs : ∀ a ∈ args, a < 2 ^ 256)
    (hclean : argsClean ws args = true)
    (hnself : args.getD j 0 ≠ selfAddress)
    (hnpre : SolidCore.Solidity.Shared.Precompile.kindOfAddress? (args.getD j 0 % 2 ^ 160) = none)
    (σ : List (Nat × Nat)) :
    ∃ world request resp, W.ans [] (.external world (.call request)) = some resp ∧
      ReqOK (callVal args σ (toCAns resp)) r request ∧
      (∀ slot < 2 ^ 256, storageIn world slot = slotValue σ slot % 2 ^ 256) ∧
      (∀ slot < 2 ^ 256, transientIn world slot = 0) ∧
      (∀ x < 2 ^ 160, (codeIn world x).isEmpty =
        (SolidCore.Solidity.Shared.Account.codeAt (W.codes.getD []) x).isEmpty) ∧
      resp.returnData.size < 2 ^ 256 ∧
      Source.runIn W fuel c { calldata := Abi.calldata sel args, callvalue := 0, storage := σ } =
        some ((CTree.call r [] fn.params.length t).eval (callVal args σ (toCAns resp))
          (fun _ _ => toCAns resp)).obs := by
  rw [SolidCore.Refinement.Wide.callAt_of_args sel args hargs σ, runIn_eq_at W hd,
    SolidCore.Refinement.Wide.map_ofNat_toNat args hargs]
  have hdec : ABI.decodeFunctionArgs? fn (Dirty.argBytes args) = .ok (args.map .word) := by
    have := decode_args hw args hlen hargs
    rw [if_pos hclean] at this
    exact this
  rw [callCalldata_finish W.ans hsel hfind hdec]
  set ctx := ABI.Contract.callContextAtWithBase c.core (ctxIn W c) selfAddress callerAddress 0
    ((EthLib.Base.natToBytes 4 sel).map (·.toNat) ++ Dirty.argBytes args) with hctx
  set st0 : SolidCore.Solidity.Source.State :=
    { d with storage := σ.foldl (fun acc kv => StorageMap.insertLoop acc kv.1 kv.2) d.storage } with hst0
  set E : EraseEnv := { envOf c.core with facts := argFacts ws 0 } with hE
  have hK0 : (argFacts ws 0).Hold ⟨args, slotValue σ, solHash, callerWord⟩ :=
    argFacts_hold ⟨args, slotValue σ, solHash, callerWord⟩ hargs ws 0 (by simpa using hclean)
  obtain ⟨rt, hrel0, hcall, hsto, htr, henv, hmut⟩ := call_entry_state (c := c) hw hret fuel (ctxIn W c)
    callerAddress ((EthLib.Base.natToBytes 4 sel).map (·.toNat) ++ Dirty.argBytes args) (st0 := st0)
    (getD_storage_cover hd (fun _ h => absurd h List.not_mem_nil)) hd.events (.lit callerWord) hlen hargs hclean hK0 rfl
  have hctxs : ctx.self = selfAddress := rfl
  have hacc : ctx.accountCodes = W.codes.getD [] := by
    show W.codes.getD c.core.context.accountCodes = _
    rw [hcc]
  obtain ⟨hwst, hwtr, hwcodes⟩ := SolidCore.Refinement.CallFamilies.sent_world hd W σ ctx hctxs hacc hcb hch
    hkeys hdt st0 rfl rt.state (snapshotWorld ctx rt.state) rfl hmut hsto htr (by rw [henv]; exact hde)
  have hW0 : ∀ ρ : Val, ρ.store = slotValue σ → ∀ slot < 2 ^ 256,
      storageIn (snapshotWorld ctx rt.state) slot = ρ.store slot := by
    intro ρ h slot hs
    rw [hwst slot hs, h, Nat.mod_eq_of_lt (slotValue_lt σ slot)]
  have hargj : args.getD j 0 < 2 ^ 256 := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
    exact hargs _ (List.getElem_mem _)
  have hself : ∀ extra : List Nat,
      r.target.eval ⟨args ++ extra, slotValue σ, solHash, callerWord⟩ ≠ selfAddress := by
    intro extra
    rw [htgt, arg_append _ _ _ _ _ (by omega)]
    simp only [WExpr.eval, Nat.mod_eq_of_lt hargj]
    exact hnself
  obtain ⟨request, kont, hbody, -, -⟩ := callRun_stmt ⟨args, slotValue σ, solHash, callerWord⟩ E ctx
    fn.params.length rt.state hctxs (hW0 _ rfl) fuel fn.body (initState fn) r k hrk
    (by simpa using hself []) rt hrel0 rfl
  obtain ⟨resp, hresp⟩ := Option.isSome_iff_exists.mp (hW.calls [] (snapshotWorld ctx rt.state) request)
  have hwsl : ws.length = args.length := by rw [hlen]; exact widthsOf_length hw
  have hK1 : (argFacts ws 0).Hold (callVal args σ (toCAns resp)) :=
    argFacts_hold (callVal args σ (toCAns resp))
      (by
        intro a ha
        rcases List.mem_append.mp ha with h | h
        · exact hargs a h
        · exact ansWords_lt _ a h)
      ws 0 (by simp only [callVal, List.drop_zero, argsClean_append ws args _ hwsl]; exact hclean)
  have hrel1 := StmtRel.extend (extra := ansWords (toCAns resp)) hlen hrel0 hK1
  obtain ⟨request', kont', hbody', hreq, hans⟩ := callRun_stmt (callVal args σ (toCAns resp)) E ctx
    fn.params.length rt.state hctxs (hW0 _ rfl) fuel fn.body (initState fn) r k hrk
    (hself _) rt hrel1 rfl
  rw [hbody] at hbody'
  injection hbody' with hq1 hq2
  injection hq1 with _ hq3
  injection hq3 with hq4
  subst hq4
  subst hq2
  have hRespOK : RespOK (callVal args σ (toCAns resp)) fn.params.length (snapshotWorld ctx rt.state) resp :=
    { static := hstatic [] _ request resp hresp hreq.kind
      size := hfit _ request resp hresp hreq.kind (by
        rw [hreq.callee, htgt]
        simp only [callVal, WExpr.eval, List.getD_eq_getElem?_getD, List.getElem?_append_left (show j < args.length by omega)]
        rw [← List.getD_eq_getElem?_getD, Nat.mod_eq_of_lt hargj]
        exact hnpre)
      val := by
        unfold callVal
        rw [← hlen]
        exact withAns_append args _ _ _ _ }
  refine ⟨_, request, resp, hresp, hreq, fun slot hs => hwst slot hs, hwtr, hwcodes, hRespOK.size, ?_⟩
  rw [← hctx] at hcall
  have hcallAns : Source.callAns W.ans fuel c.core.table ctx fn st0 (args.map .word) =
      foldAns W.ans [] (fn.callBodyResult st0 <$> Stmt.eval fuel c.core.table ctx rt fn.body) := by
    simp only [Source.callAns, hcall, Option.bind_some]
  have hbody2 : Stmt.eval fuel c.core.table ctx rt fn.body = _ := hbody
  rw [hcallAns, hbody2, map_request, foldAns_request, hresp]
  simp only [CTree.eval]
  cases hs : resp.success
  · obtain ⟨rt', hk⟩ := (hans resp hRespOK).2 hs
    rw [hk]
    have hok : (toCAns resp).ok = false := hs
    simp only [hok, Bool.false_eq_true, ↓reduceIte]
    exact finish_bubble c.core fn (σ := σ) rfl st0 rt' resp _ rfl
  · obtain ⟨res, hk, hleaf⟩ := (hans resp hRespOK).1 hs
    rw [hk]
    have hok : (toCAns resp).ok = true := hs
    simp only [hok, ↓reduceIte]
    rw [hRespOK.val]
    obtain ⟨T', hT', hTe⟩ := brTree_eval fn (argFacts ws 0) (callVal args σ (toCAns resp)) k t ht
    rw [← hTe]
    exact finish_leaf hK1 (slotValue_store σ) rfl hleaf hT' _ rfl

end SolidCore.Refinement.Generic


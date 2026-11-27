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
  obtain ⟨hw, hl, hsel⟩ := hcond
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
                    frameOf, List.map_nil, hw1]
                store := fun j hj => by
                  show (adoptWorld resp.postWorld ctx rt.state).loadSlot j = _
                  rw [SolidCore.Refinement.CallFamilies.adopt_load hctxs, hresp.static, hW0 j hj, hw]
                  rfl
                logs := by
                  simp only [Runtime.withFrame, Runtime.recordExternalInteraction, adoptWorld]
                  exact hrel.logs }
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

end SolidCore.Refinement.Generic


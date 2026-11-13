import SolidCore.Refinement.Generic.SourceCall
import Verify.Run
import SolidCore.Refinement.Dirty.Source

/-!
# SolidCore runs an external call of a function of the fragment as its tree

`source_run` is the source half of the generic source stage: on a call of the function `fn` with
selector `sel` (call data `Abi.calldata sel args`, any argument words below `2 ^ 256`, no value,
initial storage `σ`) to a contract whose constructor leaves the storage entries `s` and no logs,
when `σ` writes every slot `s` does (`Covers s σ`), SolidCore's `Source.run` shows
`(T.eval ⟨args, slotValue σ, solHash⟩).obs`, where `T` is the erasure `eraseFn` of `fn` in the
contract's `EraseEnv` (`envOf`: its storage fields, events and function table): the call's
argument words, its storage, and SolidCore's slot hash `solHash`.

The proof follows SolidCore's ABI dispatcher. The decoder reads each argument word, rejecting an
`address` word at or above `2 ^ 160` with empty data, then applies the `uint b` cleanups, which
reject a word at or above `2 ^ b` with empty data (`decode_args`): so a call with an argument word
dirty for its parameter's width reverts with empty data (`run_rejected`), as the tree's argument
checks do (`paramGuards_eval`). Otherwise the selector reads back (`readSelector_calldata`), the
parameters decode to their words, the frame binds each parameter to its word and each return to
zero (`bindArgs_words`, `defaults_words`), the body runs as its branch tree (`eval_stmt`, from a
runtime that `StmtRel` relates to `initState`: the context's caller is `callerWord` and its events
are the contract's), and the end of the body is encoded as the leaf of the tree says: the returned
words (`collect_words`, `coerce_words`, `encode_words`) or the revert data (`encode_panic`). A
success keeps the body's storage, which `loadSlot_eq` reads as the tree's writes over `σ`, and its
events, which `logEntries_map` reads as the tree's logs; a failure keeps `σ` and logs nothing.
The call's storage reads as `slotValue σ` in every slot, the constructor's entries included,
because `σ` writes each of them (`getD_storage_cover`).
-/

namespace SolidCore.Refinement.Generic
open SolidCore.Solidity SolidCore.Solidity.Source SolidCore.Refinement

/-- The erasure environment of a contract: its storage fields, its events and its function
table. -/
def envOf (core : Contract) : EraseEnv :=
  { fields := core.storageFields, events := core.eventDecls, tbl := core.table }

/-! ## The shape of the parameters -/

theorem paramWidth_spec {p : BindingDecl} {c : AbiCleanup} {w : Nat} (h : paramWidth p c = some w) :
    p.isStorageRef = false ∧
      ((p.ty = .uint256 ∧ c = .uint w ∧ 0 < w ∧ w ≤ 256) ∨ (p.ty = .address ∧ c = .none ∧ w = 160)) := by
  unfold paramWidth at h
  split at h
  · simp at h
  rename_i hs
  refine ⟨by simpa using hs, ?_⟩
  split at h
  · split at h
    · rename_i hb
      simp only [Option.some.injEq] at h
      subst h
      exact .inl ⟨by assumption, rfl, hb⟩
    · simp at h
  · simp only [Option.some.injEq] at h
    exact .inr ⟨by assumption, rfl, h.symm⟩
  · simp at h

theorem widthsOf_spec : ∀ {ps : List BindingDecl} {cs : List AbiCleanup} {ws : List Nat},
    widthsOf ps cs = some ws →
      cs.length = ps.length ∧ ws.length = ps.length ∧
      (∀ p ∈ ps, (p.ty = .uint256 ∨ p.ty = .address) ∧ p.isStorageRef = false) ∧
      (∀ c ∈ cs, c = .none ∨ ∃ b, c = .uint b ∧ 0 < b ∧ b ≤ 256)
  | [], [], ws, h => by
    simp only [widthsOf, Option.some.injEq] at h
    subst h
    simp
  | p :: ps, c :: cs, ws, h => by
    simp only [widthsOf, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨w, hw, ws', hws', rfl⟩ := h
    obtain ⟨h1, h2, h3, h4⟩ := widthsOf_spec hws'
    obtain ⟨hs, hk⟩ := paramWidth_spec hw
    refine ⟨by simp [h1], by simp [h2], ?_, ?_⟩
    · intro q hq
      rcases List.mem_cons.mp hq with rfl | hq
      · rcases hk with ⟨ht, -⟩ | ⟨ht, -⟩
        · exact ⟨.inl ht, hs⟩
        · exact ⟨.inr ht, hs⟩
      · exact h3 q hq
    · intro d hd
      rcases List.mem_cons.mp hd with rfl | hd
      · rcases hk with ⟨-, hc, hb⟩ | ⟨-, hc, -⟩
        · exact .inr ⟨w, hc, hb⟩
        · exact .inl hc
      · exact h4 d hd
  | [], _ :: _, _, h | _ :: _, [], _, h => by simp [widthsOf] at h

/-! ## Decoding the argument words -/

/-- Whether SolidCore's decoder accepts the word `a` for the type `ty`: an `address` word must be
below `2 ^ 160`. -/
def decodeClean : Source.Ty → Nat → Bool
  | .address, a => decide (a < 2 ^ 160)
  | _, _ => true

/-- Whether SolidCore's decoder accepts every argument word for its parameter's type. -/
def decodeCleanAll : List Source.Ty → List Nat → Bool
  | ty :: tys, a :: as => decodeClean ty a && decodeCleanAll tys as
  | _, _ => true

/-- Whether the word `a` passes the ABI cleanup `c`. -/
def cleanArg : AbiCleanup → Nat → Bool
  | .uint b, a => decide (a < 2 ^ b)
  | _, _ => true

/-- Whether every argument word passes its parameter's ABI cleanup. -/
def cleanupsClean : List AbiCleanup → List Nat → Bool
  | c :: cs, a :: as => cleanArg c a && cleanupsClean cs as
  | _, _ => true

/-- Whether every argument word fits its parameter's width. -/
def argsClean : List Nat → List Nat → Bool
  | w :: ws, a :: as => decide (a < 2 ^ w) && argsClean ws as
  | _, _ => true

theorem headWords_word {ty : Source.Ty} (h : ty = .uint256 ∨ ty = .address) :
    ABI.Ty.abiHeadWords? ty = some 1 := by
  rcases h with rfl | rfl <;>
    simp [ABI.Ty.abiHeadWords?, ABI.Ty.isDynamicAbi, ABI.Ty.staticAbiHeadWords?]

theorem listHeadWords_words : ∀ (tys : List Source.Ty), (∀ t ∈ tys, t = .uint256 ∨ t = .address) →
    ABI.Ty.listAbiHeadWords? tys = some tys.length
  | [], _ => rfl
  | t :: ts, h => by
    simp [ABI.Ty.listAbiHeadWords?, headWords_word (h t List.mem_cons_self),
      listHeadWords_words ts (fun u hu => h u (List.mem_cons_of_mem _ hu)), Nat.add_comm]

theorem decodeAux_words (args : List Nat) (hargs : ∀ a ∈ args, a < wordSize) :
    ∀ (ps : List (Bool × Source.Ty)) (idx : Nat), (∀ p ∈ ps, p.2 = .uint256 ∨ p.2 = .address) →
      idx + ps.length = args.length →
      ABI.decodeArgsAux? (Dirty.argBytes args) ps idx =
        if decodeCleanAll (ps.map Prod.snd) (args.drop idx) then .ok ((args.drop idx).map .word)
        else .error .empty
  | [], idx, _, hlen => by
    simp only [List.length_nil, Nat.add_zero] at hlen
    subst hlen
    simp [ABI.decodeArgsAux?, decodeCleanAll]
  | (lazy, ty) :: ps, idx, hps, hlen => by
    have hi : idx < args.length := by simp at hlen; omega
    have hr := Dirty.readWord_argBytes args hargs idx hi
    have ih := decodeAux_words args hargs ps (idx + 1)
      (fun p hp => hps p (List.mem_cons_of_mem _ hp)) (by simp at hlen; omega)
    have hty : ty = .uint256 ∨ ty = .address := hps _ List.mem_cons_self
    have ha := hargs _ (List.getElem_mem hi)
    rw [List.drop_eq_getElem_cons hi]
    rcases hty with rfl | rfl
    · simp only [ABI.decodeArgsAux?, ABI.decodeValueAt?, ABI.Ty.abiDecodeFuel,
        ABI.decodeValueAtWithFuel?, ABI.wordBytes, hr, ABI.abiArgOpt,
        headWords_word (Or.inl rfl), bind, Except.bind, pure, Except.pure, ih, List.map_cons,
        decodeCleanAll, decodeClean, Bool.true_and]
      by_cases hc : decodeCleanAll (List.map Prod.snd ps) (List.drop (idx + 1) args) = true <;>
        simp [hc]
    · simp only [ABI.decodeArgsAux?, ABI.decodeValueAt?, ABI.Ty.abiDecodeFuel,
        ABI.decodeValueAtWithFuel?, ABI.wordBytes, hr, ABI.abiArgOpt, ABI.addressFits, norm_lt ha,
        headWords_word (Or.inr rfl), bind, Except.bind, pure, Except.pure, ih, List.map_cons,
        decodeCleanAll, decodeClean]
      by_cases h1 : args[idx] < 2 ^ 160
      · simp only [h1, decide_true, Bool.true_and, ↓reduceIte]
        by_cases hc : decodeCleanAll (List.map Prod.snd ps) (List.drop (idx + 1) args) = true <;>
          simp [hc]
      · simp only [h1, decide_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte]

theorem lazyParamValues_words : ∀ (cs : List AbiCleanup) (args : List Nat),
    (∀ c ∈ cs, c = .none ∨ ∃ b, c = .uint b ∧ 0 < b ∧ b ≤ 256) → cs.length = args.length →
    (∀ a ∈ args, a < wordSize) →
    AbiCleanups.lazyParamValues cs (args.map .word) =
      if cleanupsClean cs args then some (args.map .word) else none
  | [], [], _, _, _ => rfl
  | c :: cs, a :: args, hc, hl, ha => by
    have ih := lazyParamValues_words cs args (fun d hd => hc d (List.mem_cons_of_mem _ hd))
      (by simpa using hl) (fun b hb => ha b (List.mem_cons_of_mem _ hb))
    have hlt := ha a List.mem_cons_self
    rcases hc c List.mem_cons_self with rfl | ⟨b, rfl, hb0, hb⟩
    · simp only [List.map_cons, AbiCleanups.lazyParamValues, AbiCleanup.lazyParamValue, ih,
        cleanupsClean, cleanArg, Bool.true_and, bind, Option.bind]
      by_cases hc : cleanupsClean cs args = true <;> simp [hc]
    · by_cases h : a < 2 ^ b
      · simp only [List.map_cons, AbiCleanups.lazyParamValues, ih, cleanupsClean, cleanArg, h,
          decide_true, Bool.true_and]
        by_cases hc : cleanupsClean cs args = true <;>
          simp [AbiCleanup.lazyParamValue, AbiCleanup.accepts, norm_lt hlt, h, hb0, hb, bind,
            Option.bind, hc]
      · simp [AbiCleanups.lazyParamValues, AbiCleanup.lazyParamValue, AbiCleanup.accepts,
          norm_lt hlt, h, hb0, hb, bind, Option.bind, cleanupsClean, cleanArg]
  | [], _ :: _, _, hl, _ | _ :: _, [], _, hl, _ => by simp at hl

theorem argsClean_widths : ∀ {ps : List BindingDecl} {cs : List AbiCleanup} {ws : List Nat}
    (args : List Nat), widthsOf ps cs = some ws → args.length = ps.length →
    argsClean ws args = (decodeCleanAll (ps.map BindingDecl.ty) args && cleanupsClean cs args)
  | [], [], ws, [], h, _ => by
    simp only [widthsOf, Option.some.injEq] at h
    subst h
    rfl
  | p :: ps, c :: cs, ws, a :: args, h, hl => by
    simp only [widthsOf, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨w, hw, ws', hws', rfl⟩ := h
    have ih := argsClean_widths args hws' (by simpa using hl)
    obtain ⟨-, hk⟩ := paramWidth_spec hw
    simp only [argsClean, ih, List.map_cons, decodeCleanAll, cleanupsClean]
    rcases hk with ⟨ht, rfl, -⟩ | ⟨ht, rfl, rfl⟩
    · simp only [ht, decodeClean, cleanArg, Bool.true_and]
      cases decide (a < 2 ^ w) <;> cases decodeCleanAll (ps.map BindingDecl.ty) args <;>
        cases cleanupsClean cs args <;> rfl
    · simp only [ht, decodeClean, cleanArg, Bool.and_true]
      cases decide (a < 2 ^ 160) <;> cases decodeCleanAll (ps.map BindingDecl.ty) args <;>
        cases cleanupsClean cs args <;> rfl
  | [], [], _, _ :: _, _, hl | _ :: _, _ :: _, _, [], _, hl => by simp at hl
  | [], _ :: _, _, _, h, _ | _ :: _, [], _, _, h, _ => by simp [widthsOf] at h

/-- **SolidCore decodes the argument words of a function of the fragment** to themselves when
each fits its parameter's width, and otherwise reverts with empty data. -/
theorem decode_args {fn : FunctionDef} {ws : List Nat}
    (hw : widthsOf fn.params fn.paramAbiCleanups = some ws) (args : List Nat)
    (hlen : args.length = fn.params.length) (hargs : ∀ a ∈ args, a < wordSize) :
    ABI.decodeFunctionArgs? fn (Dirty.argBytes args) =
      if argsClean ws args then .ok (args.map .word) else .error .empty := by
  obtain ⟨hcl, -, hp, hc⟩ := widthsOf_spec hw
  have hflags : (fn.paramAbiCleanups.length == (fn.params.map BindingDecl.ty).length) = true := by
    simp [hcl]
  have hps : ∀ p ∈ (fn.paramAbiCleanups.map ABI.AbiCleanup.decodeLazy).zip
      (fn.params.map BindingDecl.ty), p.2 = .uint256 ∨ p.2 = .address := by
    intro p hp'
    have := List.of_mem_zip hp'
    obtain ⟨b, hb, he⟩ := List.mem_map.mp this.2
    rw [← he]; exact (hp b hb).1
  have hzl : ((fn.paramAbiCleanups.map ABI.AbiCleanup.decodeLazy).zip
      (fn.params.map BindingDecl.ty)).length = args.length := by
    simp [hcl, hlen]
  have hsnd : ((fn.paramAbiCleanups.map ABI.AbiCleanup.decodeLazy).zip
      (fn.params.map BindingDecl.ty)).map Prod.snd = fn.params.map BindingDecl.ty :=
    List.map_snd_zip (by simp [hcl])
  have hhw : ABI.Ty.listAbiHeadWords? (fn.params.map BindingDecl.ty) = some args.length := by
    rw [listHeadWords_words _ (fun t ht => by
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ht
      exact (hp b hb).1)]
    simp [hlen]
  have hdec := decodeAux_words args hargs _ 0 hps (by omega)
  simp only [List.drop_zero, hsnd] at hdec
  rw [argsClean_widths args hw hlen]
  unfold ABI.decodeFunctionArgs? ABI.decodeArgsWith?
  simp only [hflags, ↓reduceIte, hsnd, hhw, ABI.abiArgOpt, Dirty.length_argBytes,
    ABI.wordBytes, Nat.lt_irrefl, bind, Except.bind, pure, Except.pure, hdec]
  by_cases hd : decodeCleanAll (fn.params.map BindingDecl.ty) args = true
  · simp only [hd, ↓reduceIte, Bool.true_and]
    rw [lazyParamValues_words _ _ hc (by omega) hargs]
    split
    · rename_i hnil
      have : args = [] := by
        rw [List.isEmpty_iff] at hnil
        rw [hnil] at hcl
        simp at hcl
        exact List.eq_nil_of_length_eq_zero (by omega)
      subst this
      cases fn.paramAbiCleanups <;> rfl
    · by_cases hcc : cleanupsClean fn.paramAbiCleanups args = true <;> simp [hcc]
  · simp only [hd, Bool.false_eq_true, ↓reduceIte, Bool.false_and]

/-! ## The frame a call starts with -/

theorem coerce_word (v : Nat) : Source.Ty.uint256.coerceValue? (.word v) = some (.word v) := by
  simp [Source.Ty.coerceValue?]

theorem coerce_param {ty : Source.Ty} (h : ty = .uint256 ∨ ty = .address) (v : Nat) :
    ty.coerceValue? (.word v) = some (.word v) :=
  (wordTy_coerce (by rcases h with rfl | rfl <;> rfl) v).1

/-- The parameters bind to the argument words, as `paramLocals` says. -/
theorem bindArgs_words (ρ : Val) (hρ : ∀ a ∈ ρ.args, a < wordSize) :
    ∀ (ps : List BindingDecl) (i : Nat),
      (∀ p ∈ ps, (p.ty = .uint256 ∨ p.ty = .address) ∧ p.isStorageRef = false) →
      i + ps.length = ρ.args.length →
      BindingDecl.bindArgs? ps ((ρ.args.drop i).map .word) = some (frameOf ρ (paramLocals ps i))
  | [], i, _, h => by
    simp only [List.length_nil, Nat.add_zero] at h
    subst h
    simp [BindingDecl.bindArgs?, paramLocals, frameOf]
  | p :: ps, i, hps, h => by
    have hi : i < ρ.args.length := by simp at h; omega
    have ih := bindArgs_words ρ hρ ps (i + 1) (fun q hq => hps q (List.mem_cons_of_mem _ hq))
      (by simp at h; omega)
    have hty := (hps p List.mem_cons_self).1
    have hlt := hρ _ (List.getElem_mem hi)
    rw [List.drop_eq_getElem_cons hi]
    simp only [List.map_cons, BindingDecl.bindArgs?, BindingDecl.bindArg?, coerce_param hty, ih,
      bind, Option.bind, paramLocals, frameOf, List.map_cons, WExpr.eval, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem hi, Option.getD_some, Nat.mod_eq_of_lt hlt]

/-- A return the fragment encodes: a `uint256`, `address` or `bool`. -/
abbrev RetTy (ty : Source.Ty) : Prop := ty = .uint256 ∨ ty = .address ∨ ty = .bool

theorem defaults_words (ρ : Val) (rs : List BindingDecl)
    (hrs : ∀ r ∈ rs, RetTy r.ty ∧ r.isStorageRef = false) :
    rs.map BindingDecl.defaultBinding = frameOf ρ (rs.map fun r => (r.name, WExpr.lit 0)) := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    have h := hrs r List.mem_cons_self
    simp only [List.map_cons, frameOf] at ih ⊢
    rw [ih (fun q hq => hrs q (List.mem_cons_of_mem _ hq))]
    rcases h.1 with h1 | h1 | h1 <;>
    simp [BindingDecl.defaultBinding, h1, h.2, Source.Ty.defaultValue, WExpr.eval]

/-- A word `retOk` accepts is one SolidCore coerces to its return's type and encodes as its
32-byte word. -/
theorem retOk_spec {ρ : Val} {K : Facts} (hK : K.Hold ρ) {ty : Source.Ty} {w : WExpr}
    (h : retOk K ty w = true) :
    ty.coerceValue? (.word (w.eval ρ)) = some (.word (w.eval ρ)) ∧
      ABI.Ty.isDynamicAbi ty = false ∧ ABI.Ty.staticAbiHeadWords? ty = some 1 ∧
      ABI.encodeStaticValue? ty (.word (w.eval ρ)) = some (ABI.encodeWord (w.eval ρ)) := by
  have hlt := w.eval_lt ρ
  unfold retOk at h
  split at h
  · exact ⟨by simp [Source.Ty.coerceValue?], rfl, rfl, rfl⟩
  · simp only [decide_eq_true_eq] at h
    have hn : w.eval ρ < 1461501637330902918203684832716283019655932542976 :=
      Nat.lt_of_le_of_lt (bound_sound hK w) h
    exact ⟨by simp [Source.Ty.coerceValue?], rfl, rfl,
      by simp [ABI.encodeStaticValue?, ABI.addressFits, norm_lt hlt, hn]⟩
  · simp only [decide_eq_true_eq] at h
    have hn : w.eval ρ ≤ 1 := Nat.le_trans (bound_sound hK w) h
    have hv : w.eval ρ = 0 ∨ w.eval ρ = 1 := by omega
    rcases hv with hv | hv <;>
    exact ⟨by simp [Source.Ty.coerceValue?, wordEq, hv], rfl, rfl,
      by simp [ABI.encodeStaticValue?, wordEq, hv]⟩
  · simp at h

theorem retsOk_length {K : Facts} : ∀ {rs : List BindingDecl} {ws : List WExpr},
    retsOk K rs ws = true → ws.length = rs.length
  | [], [], _ => rfl
  | _ :: rs, _ :: ws, h => by
    simp only [retsOk, Bool.and_eq_true] at h
    simp [retsOk_length h.2]
  | [], _ :: _, h | _ :: _, [], h => by simp [retsOk] at h

/-! ## Reading the returned words -/

theorem deref_word (rt : Runtime) (v : Nat) : rt.derefMemoryValueDeep (.word v) = .ok (.word v) := by
  simp [Runtime.derefMemoryValueDeep, Runtime.derefMemoryValueWithFuel]

theorem collect_words (ρ : Val) (rt : Runtime) (S : SymState) {K : Facts} (hK : K.Hold ρ)
    (hl : ∀ x e, Scopes.get? S.scopes x = some e → rt.lookupLocal? x = some (.word (e.eval ρ))) :
    ∀ (rs : List BindingDecl) (ws : List WExpr), retsOk K rs ws = true →
      rs.mapM (fun r => Scopes.get? S.scopes r.name) = some ws →
      collectReturnBindings.collect rt rs = .ok (ws.map fun e => .word (e.eval ρ))
  | [], ws, _, h => by
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h
    subst h; rfl
  | r :: rs, ws, hrs, h => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨e, he, ws', hws', rfl⟩ := h
    simp only [retsOk, Bool.and_eq_true] at hrs
    have ih := collect_words ρ rt S hK hl rs ws' hrs.2 hws'
    simp [collectReturnBindings.collect, hl _ _ he, deref_word, (retOk_spec hK hrs.1).1, ih, bind,
      Except.bind, pure, Except.pure]

theorem coerce_words (ρ : Val) (rt : Runtime) {K : Facts} (hK : K.Hold ρ) :
    ∀ (rs : List BindingDecl) (ws : List WExpr), retsOk K rs ws = true →
      coerceReturnBindings.coerce rt rs (ws.map fun e => .word (e.eval ρ)) =
        .ok (ws.map fun e => .word (e.eval ρ))
  | [], [], _ => rfl
  | r :: rs, e :: ws, hrs => by
    simp only [retsOk, Bool.and_eq_true] at hrs
    have ih := coerce_words ρ rt hK rs ws hrs.2
    simp only [List.map_cons] at ih ⊢
    simp [coerceReturnBindings.coerce, deref_word, (retOk_spec hK hrs.1).1, ih,
      bind, Except.bind, pure, Except.pure]
  | [], _ :: _, h | _ :: _, [], h => by simp [retsOk] at h

/-! ## Encoding the output -/

theorem wordToBytesBE_eq : ∀ (n v : Nat),
    ABI.wordToBytesBE n v = (List.range n).map fun i => v / 256 ^ (n - 1 - i) % 256
  | 0, _ => rfl
  | n + 1, v => by
    rw [ABI.wordToBytesBE, wordToBytesBE_eq n (v / 256), List.range_succ, List.map_append]
    congr 1
    · apply List.map_congr_left
      intro i hi
      simp only [List.mem_range] at hi
      rw [Nat.div_div_eq_div_mul, ← Nat.pow_succ', show (n - 1 - i).succ = n + 1 - 1 - i by omega]
    · simp [normByte, SolidCore.Solidity.Shared.Account.byte]

theorem div_pow_mod (v k : Nat) (hk : k < 32) : v % wordSize / 256 ^ k % 256 = v / 256 ^ k % 256 := by
  have hw : wordSize = 256 ^ k * 256 ^ (32 - k) := by
    rw [← Nat.pow_add, show k + (32 - k) = 32 by omega]
  rw [hw, Nat.mod_mul_right_div_self, Nat.mod_mod_of_dvd]
  have := Nat.pow_dvd_pow 256 (show 1 ≤ 32 - k by omega)
  simpa using this

theorem encodeWord_eq (v : Nat) :
    ABI.encodeWord v = (List.range 32).map fun i => v / 256 ^ (31 - i) % 256 := by
  rw [ABI.encodeWord, ABI.wordBytes, wordToBytesBE_eq]
  apply List.map_congr_left
  intro i hi
  simp only [List.mem_range] at hi
  simp only [SolidCore.Solidity.Shared.norm, modulus_eq, show 32 - 1 - i = 31 - i by omega]
  exact div_pow_mod v _ (by omega)

theorem encodeWord_eval (ρ : Val) (e : WExpr) :
    ABI.encodeWord (e.eval ρ) = (wordOBytes e).map (OByte.eval ρ) := by
  rw [encodeWord_eq, wordOBytes, List.map_map]
  rfl

theorem litBytes_eval (ρ : Val) (n : Nat) :
    (litBytes 32 n).map (OByte.eval ρ) = ABI.encodeWord n := by
  rw [encodeWord_eq, litBytes, List.map_map]
  apply List.map_congr_left
  intro i hi
  simp [OByte.eval, show 32 - 1 - i = 31 - i by omega]

theorem encodeAux_words (ρ : Val) {K : Facts} (hK : K.Hold ρ) :
    ∀ (rs : List BindingDecl) (ws : List WExpr) (off : Nat), retsOk K rs ws = true →
      ABI.encodeValuesAux? (rs.map BindingDecl.ty) (ws.map fun e => .word (e.eval ρ)) off =
        some ((ws.flatMap wordOBytes).map (OByte.eval ρ), [], off)
  | [], [], _, _ => rfl
  | r :: rs, e :: ws, off, hrs => by
    simp only [retsOk, Bool.and_eq_true] at hrs
    have ih := encodeAux_words ρ hK rs ws off hrs.2
    obtain ⟨-, hd, -, he⟩ := retOk_spec hK hrs.1
    simp only [List.map_cons, ABI.encodeValuesAux?, hd, he, ih, Bool.false_eq_true, ↓reduceIte,
      List.flatMap_cons, List.map_append, encodeWord_eval]
  | [], _ :: _, _, h | _ :: _, [], _, h => by simp [retsOk] at h

theorem encode_words (ρ : Val) {K : Facts} (hK : K.Hold ρ) (rs : List BindingDecl) (ws : List WExpr)
    (hrs : retsOk K rs ws = true) :
    ABI.encodeValues? (rs.map BindingDecl.ty) (ws.map fun e => .word (e.eval ρ)) =
      some ((ws.flatMap wordOBytes).map (OByte.eval ρ)) := by
  have hhw : ∀ (rs : List BindingDecl) (ws : List WExpr), retsOk K rs ws = true →
      ABI.Ty.listAbiHeadWords? (rs.map BindingDecl.ty) = some rs.length := by
    intro rs
    induction rs with
    | nil => intro ws _; rfl
    | cons r rs ih =>
      intro ws h
      cases ws with
      | nil => simp [retsOk] at h
      | cons w ws =>
        simp only [retsOk, Bool.and_eq_true] at h
        obtain ⟨-, hd, hw, -⟩ := retOk_spec (ρ := ρ) hK h.1
        simp [ABI.Ty.listAbiHeadWords?, ABI.Ty.abiHeadWords?, hd, hw, ih ws h.2, Nat.add_comm]
  simp [ABI.encodeValues?, hhw rs ws hrs, encodeAux_words ρ hK rs ws _ hrs, bind, Option.bind]

theorem encode_panic (ρ : Val) (core : Contract) (c : Nat) :
    ABI.Contract.encodeRevertData? core (.panic c) = some ((panicBytes c).map (OByte.eval ρ)) := by
  have h2 : ABI.encodeValues? [Source.Ty.uint256] [Value.word c] =
      some ((litBytes 32 c).map (OByte.eval ρ)) := by
    rw [litBytes_eval]
    simp [ABI.encodeValues?, ABI.Ty.listAbiHeadWords?, ABI.Ty.abiHeadWords?, ABI.Ty.isDynamicAbi,
      ABI.Ty.staticAbiHeadWords?, ABI.encodeValuesAux?, ABI.encodeStaticValue?, bind, Option.bind]
  simp only [ABI.Contract.encodeRevertData?, h2, panicBytes, List.map_append]
  congr 2

/-- SolidCore's `Error(msg)` revert data are `errorBytes msg`. -/
theorem encode_error (ρ : Val) (core : Contract) {m : String} {bs : List OByte}
    (h : errorBytes m = some bs) :
    ABI.Contract.encodeRevertData? core (.error m) = some (bs.map (OByte.eval ρ)) := by
  unfold errorBytes at h
  split at h
  · rename_i p hp
    dsimp only at h
    split at h
    · rename_i hall
      simp only [Option.some.injEq] at h
      subst h
      simp only [ABI.Contract.encodeRevertData?, hp, List.map_map, Option.some.injEq]
      symm
      have hid : ∀ b ∈ ABI.encodeSelector ABI.errorSelector ++ p, (OByte.eval ρ ∘ OByte.lit) b = id b :=
        fun b hb => by
          simp only [Function.comp, OByte.eval, id]
          exact Nat.mod_eq_of_lt (by simpa using List.all_eq_true.mp hall b hb)
      rw [List.map_congr_left hid, List.map_id]
    · simp at h
  · simp at h

/-! ## The call -/

theorem brTree_eval (fn : FunctionDef) (K : Facts) (ρ : Val) :
    ∀ (b : Br) (T : Tree), brTree fn K b = some T →
      ∃ T', leafTree fn K (b.eval ρ) = some T' ∧ T'.eval ρ = T.eval ρ
  | .leaf l, T, h => ⟨T, h, rfl⟩
  | .ite c t e, T, h => by
    simp only [brTree, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨t', ht, e', he, rfl⟩ := h
    simp only [Br.eval, Tree.eval]
    split
    · exact brTree_eval fn K ρ e e' he
    · exact brTree_eval fn K ρ t t' ht

theorem slotValue_lt (σ : List (Nat × Nat)) (k : Nat) : slotValue σ k < wordSize := by
  unfold slotValue
  have key : ∀ a, a < wordSize → σ.foldl (fun acc kv => if kv.1 % 2 ^ 256 = k % 2 ^ 256 then
      kv.2 % 2 ^ 256 else acc) a < wordSize := by
    induction σ with
    | nil => intro a h; exact h
    | cons kv σ ih =>
      intro a h
      simp only [List.foldl_cons]
      apply ih
      split
      · exact Nat.mod_lt _ (by decide)
      · exact h
  exact key 0 (by decide)

theorem slotValue_mod (σ : List (Nat × Nat)) (k : Nat) : slotValue σ (k % wordSize) = slotValue σ k := by
  simp only [slotValue, Nat.mod_mod]

theorem length_of_mapM {α β : Type} (f : α → Option β) :
    ∀ (l : List α) (ws : List β), l.mapM f = some ws → ws.length = l.length
  | [], ws, h => by simp at h; subst h; rfl
  | a :: l, ws, h => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨b, -, ws', h', rfl⟩ := h
    simp [length_of_mapM f l ws' h']

theorem slotValue_store (σ : List (Nat × Nat)) (k : Nat) :
    slotValue σ (k % wordSize) % wordSize = slotValue σ k := by
  rw [slotValue_mod, Nat.mod_eq_of_lt (slotValue_lt σ k)]

/-- A storage that holds, in every slot below `2 ^ 256`, the word the writes leave there reads so
in every slot. -/
theorem loadSlot_eq (st : State) (ws : Writes) (ρ : Val) (hρ : ρ.Ok)
    (h : ∀ k, k < wordSize → st.loadSlot k = Writes.store ρ ws k) (slot : Nat) :
    st.loadSlot slot = Writes.store ρ ws slot := by
  rw [← loadSlot_mod, h _ (Nat.mod_lt _ (by decide)), Writes.store_mod ρ hρ]

/-- What SolidCore's state shows of its events as logs. -/
theorem logEntries_map (st : State) (self : Nat) :
    (st.logEntries self).map (fun e => (e.topics, e.data)) = st.events.map logOf := by
  simp [State.logEntries, Event.toLogEntry, logOf]

theorem untag_words (ρ : Val) (ws : List WExpr) :
    (ws.map fun e => Value.word (e.eval ρ)).map Value.untagFixedBytes =
      ws.map fun e => Value.word (e.eval ρ) := by
  simp [Value.untagFixedBytes]

/-! ## The deployed storage -/

/-- The call's storage `σ` writes every slot the constructor's entries `s` write. -/
def Covers (s σ : List (Nat × Nat)) : Prop := ∀ kv ∈ s, ∃ kv' ∈ σ, kv'.1 % wordSize = kv.1 % wordSize

theorem getD_foldl_cover (k : Nat) : ∀ (σ : List (Nat × Nat)) (a : Option Nat) (b : Nat),
    (a.getD 0 = b ∨ ∃ kv ∈ σ, kv.1 % wordSize = k % wordSize) →
    (σ.foldl (fun acc kv => if SolidCore.Solidity.Shared.norm kv.1 = k % 2 ^ 256 then
        some (SolidCore.Solidity.Shared.norm kv.2) else acc) a).getD 0 =
      σ.foldl (fun acc kv => if kv.1 % 2 ^ 256 = k % 2 ^ 256 then kv.2 % 2 ^ 256 else acc) b
  | [], a, b, h => by
    rcases h with h | ⟨_, h, _⟩
    · simpa using h
    · simp at h
  | kv :: σ, a, b, h => by
    simp only [List.foldl_cons]
    apply getD_foldl_cover k σ
    by_cases hk : kv.1 % wordSize = k % wordSize
    · left
      have hk' : SolidCore.Solidity.Shared.norm kv.1 = k % 2 ^ 256 := hk
      rw [if_pos hk', if_pos hk]
      rfl
    · have hk' : ¬ SolidCore.Solidity.Shared.norm kv.1 = k % 2 ^ 256 := hk
      rw [if_neg hk', if_neg hk]
      rcases h with h | ⟨kv', hm, he⟩
      · exact Or.inl h
      · rcases List.mem_cons.mp hm with rfl | hm
        · exact absurd he hk
        · exact Or.inr ⟨kv', hm, he⟩

/-- A slot of the storage a call writes over the deployed storage reads as `slotValue`, when
the call's storage writes every slot of the deployed one. -/
theorem getD_storage_cover {fuel : Nat} {c : TypeCheck.CheckedContract} {d : Source.State}
    {s : List (Nat × Nat)} (hd : Wide.DeployedAt fuel c d s) {σ : List (Nat × Nat)}
    (hcov : Covers s σ) (k : Nat) :
    ((σ.foldl (fun acc kv => acc.insertLoop kv.1 kv.2) d.storage)[k % 2 ^ 256]?).getD 0 =
      slotValue σ k := by
  rw [Verify.getElem?_foldl_insertLoop]
  apply getD_foldl_cover k σ _ 0
  cases h : d.storage[k % 2 ^ 256]? with
  | none => exact Or.inl rfl
  | some v =>
    right
    have hm : (k % 2 ^ 256, v) ∈ s := hd.storage ▸ Std.HashMap.mem_toList_iff_getElem?_eq_some.mpr h
    obtain ⟨kv', hkv', he⟩ := hcov _ hm
    exact ⟨kv', hkv', by rw [he]; exact Nat.mod_mod _ _⟩

theorem deployedStorage_of {fuel : Nat} {c : TypeCheck.CheckedContract} {d : Source.State}
    {s : List (Nat × Nat)} (hd : Wide.DeployedAt fuel c d s) :
    ∃ s0, Abi.deployedStorage fuel c = some s0 := by
  obtain ⟨vs, hc⟩ := hd.cons
  unfold Abi.deployedStorage
  have hc' : TypeCheck.CheckedContract.constructWithContext? fuel c
      { c.core.context with sender := callerAddress, self := selfAddress, value := 0 } State.empty
      selfAddress 0 [] = some (CallResult.returned d vs) := hc
  simp only [hc']
  exact ⟨_, rfl⟩


/-! ## Dirty argument words -/

/-- The tree of a call with argument checks: their revert when an argument word is dirty for its
width, else the tree they guard. -/
theorem paramGuards_eval (ρ : Val) (t : Tree) (hρ : ∀ a ∈ ρ.args, a < wordSize) :
    ∀ (ws : List Nat) (i : Nat),
      (paramGuards ws i t).eval ρ =
        if argsClean ws (ρ.args.drop i) then t.eval ρ
        else { success := false, output := [], logs := [], store := ρ.store }
  | [], i => by simp [paramGuards, argsClean]
  | w :: ws, i => by
    have ih := paramGuards_eval ρ t hρ ws (i + 1)
    cases hdrop : ρ.args.drop i with
    | nil =>
      have hge : ρ.args.length ≤ i := by simpa using hdrop
      have hd1 : ρ.args.drop (i + 1) = [] := by simp; omega
      have harg : (WExpr.arg i).eval ρ = 0 := by
        simp [WExpr.eval, List.getD_eq_getElem?_getD, List.getElem?_eq_none hge]
      rw [hd1] at ih
      simp only [argsClean] at ih ⊢
      simp only [paramGuards]
      split
      · simp only [Tree.eval, ih, ite_true]
        rw [if_pos]
        simp only [eval_bin, harg, eval_lit, BinOp.eval]
        simp
      · simpa using ih
    | cons a as =>
      have hi : i < ρ.args.length := by
        have := congrArg List.length hdrop; simp at this; omega
      have ha : ρ.args.getD i 0 = a := by
        rw [List.getD_eq_getElem?_getD, ← List.head?_drop, hdrop]; rfl
      have hd1 : ρ.args.drop (i + 1) = as := by
        rw [← List.drop_drop, hdrop]; rfl
      have halt : a < wordSize := by
        rw [← ha, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
        exact hρ _ (List.getElem_mem hi)
      rw [hd1] at ih
      simp only [argsClean, paramGuards]
      split
      · rename_i hw256
        have hpos := Nat.two_pow_pos w
        have hm : (2 ^ w - 1) % wordSize = 2 ^ w - 1 :=
          Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.sub_lt hpos (by decide))
            (Nat.pow_le_pow_right (by decide) (by omega)))
        simp only [Tree.eval, ih, eval_bin, eval_lit, WExpr.eval, ha, Nat.mod_eq_of_lt halt, hm,
          BinOp.eval]
        by_cases hc2 : a < 2 ^ w
        · have : ¬ 2 ^ w - 1 < a := by omega
          simp [this, hc2]
        · have : 2 ^ w - 1 < a := by omega
          simp [this, hc2]
      · rename_i hw256
        have : a < 2 ^ w := Nat.lt_of_lt_of_le halt (Nat.pow_le_pow_right (by decide) (by omega))
        simp [ih, this]

/-- Past the argument checks, the facts they leave hold. -/
theorem argFacts_hold (ρ : Val) (hρ : ∀ a ∈ ρ.args, a < wordSize) :
    ∀ (ws : List Nat) (i : Nat), argsClean ws (ρ.args.drop i) = true → (argFacts ws i).Hold ρ
  | [], _, _ => by simp [argFacts, Facts.Hold]
  | w :: ws, i, h => by
    have key : ∀ a, (WExpr.arg i).eval ρ = a → a < 2 ^ w → argsClean ws (ρ.args.drop (i + 1)) = true →
        (argFacts (w :: ws) i).Hold ρ := by
      intro a ha haw hrest
      have ih := argFacts_hold ρ hρ ws (i + 1) hrest
      simp only [argFacts]
      split
      · rename_i hw256
        refine Facts.Hold.cons ih ?_
        have hpos := Nat.two_pow_pos w
        have hm : (2 ^ w - 1) % wordSize = 2 ^ w - 1 :=
          Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.sub_lt hpos (by decide))
            (Nat.pow_le_pow_right (by decide) (by omega)))
        have : ¬ 2 ^ w - 1 < a := by omega
        simp only [eval_bin, eval_lit, ha, hm, BinOp.eval]
        simp [this]
      · exact ih
    cases hdrop : ρ.args.drop i with
    | nil =>
      have hge : ρ.args.length ≤ i := by simpa using hdrop
      have hd1 : ρ.args.drop (i + 1) = [] := by simp; omega
      have harg : (WExpr.arg i).eval ρ = 0 := by
        simp [WExpr.eval, List.getD_eq_getElem?_getD, List.getElem?_eq_none hge]
      refine key 0 harg (Nat.two_pow_pos w) ?_
      rw [hd1]; cases ws <;> rfl
    | cons a as =>
      have hi : i < ρ.args.length := by
        have := congrArg List.length hdrop; simp at this; omega
      have ha : ρ.args.getD i 0 = a := by
        rw [List.getD_eq_getElem?_getD, ← List.head?_drop, hdrop]; rfl
      have hd1 : ρ.args.drop (i + 1) = as := by
        rw [← List.drop_drop, hdrop]; rfl
      have halt : a < wordSize := by
        rw [← ha, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
        exact hρ _ (List.getElem_mem hi)
      rw [hdrop] at h
      simp only [argsClean, Bool.and_eq_true, decide_eq_true_eq] at h
      refine key a ?_ h.1 (by rw [hd1]; exact h.2)
      have ha' : ρ.args[i]?.getD 0 = a := by rw [← List.getD_eq_getElem?_getD]; exact ha
      simp [WExpr.eval, ha', Nat.mod_eq_of_lt halt]

/-- **SolidCore rejects dirty argument words**: a call whose argument words SolidCore's decoder
rejects with empty data reverts with empty output and keeps the call's storage. -/
theorem run_rejected {fuel : Nat} {c : TypeCheck.CheckedContract} {d : Source.State}
    {s : List (Nat × Nat)} (hd : Wide.DeployedAt fuel c d s) {sel : Nat} (hsel : sel < 2 ^ 32)
    {fn : FunctionDef} (hfind : c.core.findFunctionBySelector? sel = some fn) (args : List Nat)
    (hdec : ABI.decodeFunctionArgs? fn (Dirty.argBytes args) = .error .empty)
    (σ : List (Nat × Nat)) :
    Source.run fuel c { calldata := Abi.calldata sel args, callvalue := 0, storage := σ } =
      some (Abi.rejected σ) := by
  obtain ⟨s0, hdep⟩ := deployedStorage_of hd
  unfold Abi.deployedStorage at hdep
  dsimp only at hdep
  split at hdep
  case h_2 => simp at hdep
  rename_i deployed st hcons
  simp only [Source.run, Source.result?, hcons,
    TypeCheck.CheckedContract.callCalldataAtFromWithContext?,
    ABI.Contract.callCalldataAtFromWithContext?, Dirty.bytes_calldata,
    Dirty.readSelector_calldata _ hsel, hfind]
  rw [show ((EthLib.Base.natToBytes 4 sel).map (·.toNat) ++ Dirty.argBytes args).drop
      ABI.selectorBytes = Dirty.argBytes args by
    simp [ABI.selectorBytes, EthLib.Base.natToBytes_length], hdec]
  simp only [ABI.Contract.revertedCall?, ABI.Contract.encodeRevertData?, bind, Option.bind,
    Option.map_some, Source.observe, Abi.rejected]
  simp

/-! ## The call -/

theorem wordBinding_ty {b : BindingDecl} (h : wordBinding b = true) :
    RetTy b.ty ∧ b.isStorageRef = false := by
  unfold wordBinding at h
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
  refine ⟨?_, h.2⟩
  have := h.1
  split at this
  · rename_i h'; exact .inl h'
  · rename_i h'; exact .inr (.inl h')
  · rename_i h'; exact .inr (.inr h')
  · simp at this

/-- The parameter widths of a function the erasure accepts. -/
theorem eraseFn_widths {E : EraseEnv} {fuel : Nat} {fn : FunctionDef} {T : Tree}
    (h : eraseFn E fuel fn = some T) : ∃ ws, widthsOf fn.params fn.paramAbiCleanups = some ws := by
  unfold eraseFn at h
  split at h
  · simp at h
  · rename_i ws hw
    exact ⟨ws, hw⟩

/-- SolidCore runs a call of a function of the fragment on clean argument words as its body's
tree. -/
theorem source_run_clean {fuel : Nat} {c : TypeCheck.CheckedContract} {d : Source.State}
    {s : List (Nat × Nat)} (hd : Wide.DeployedAt fuel c d s) {σ : List (Nat × Nat)}
    (hcov : Covers s σ) {sel : Nat} (hsel : sel < 2 ^ 32) {fn : FunctionDef}
    (hfind : c.core.findFunctionBySelector? sel = some fn) {ws : List Nat}
    (hw : widthsOf fn.params fn.paramAbiCleanups = some ws)
    (hret : fn.returns.all wordBinding = true) {b : Br}
    (hb : eraseStmt { envOf c.core with facts := argFacts ws 0 } fuel fn.body (initState fn) = some b)
    {T : Tree} (hT : brTree fn (argFacts ws 0) b = some T) (args : List Nat)
    (hlen : args.length = fn.params.length) (hargs : ∀ a ∈ args, a < 2 ^ 256)
    (hclean : argsClean ws args = true)
    (hdec : ABI.decodeFunctionArgs? fn (Dirty.argBytes args) = .ok (args.map .word)) :
    Source.run fuel c { calldata := Abi.calldata sel args, callvalue := 0, storage := σ } =
      some (T.eval ⟨args, slotValue σ, solHash⟩).obs := by
  rw [SolidCore.Refinement.Wide.callAt_of_args sel args hargs σ,
    SolidCore.Refinement.Wide.run_eq_at hd, SolidCore.Refinement.Wide.map_ofNat_toNat args hargs]
  have hdrop : ((EthLib.Base.natToBytes 4 sel).map (·.toNat) ++ Dirty.argBytes args).drop
      ABI.selectorBytes = Dirty.argBytes args := by
    simp [ABI.selectorBytes, EthLib.Base.natToBytes_length]
  simp only [ABI.Contract.callCalldataAtFromWithContext?, Dirty.readSelector_calldata _ hsel, hfind,
    hdrop, hdec]
  have hp := (widthsOf_spec hw).2.2.1
  have hr : ∀ r ∈ fn.returns, RetTy r.ty ∧ r.isStorageRef = false :=
    fun r hr => wordBinding_ty (List.all_eq_true.mp hret r hr)
  generalize hctx : ABI.Contract.callContextAtWithBase c.core (Wide.ctxOf c) selfAddress callerAddress 0
    ((EthLib.Base.natToBytes 4 sel).map (·.toNat) ++ Dirty.argBytes args) = ctx
  generalize hst : ({ d with storage := σ.foldl (fun acc kv => acc.insertLoop kv.1 kv.2) d.storage } :
    Source.State) = st0
  have hacc : fn.acceptsValue 0 = true := by
    simp [FunctionDef.acceptsValue, wordEq]
  have hctxv : ctx.value = 0 := by
    subst hctx; simp [ABI.Contract.callContextAtWithBase, SolidCore.Solidity.Shared.norm]
  set ρ : Val := ⟨args, slotValue σ, solHash⟩ with hρ
  have hρok : ρ.Ok := slotValue_store σ
  set K := argFacts ws 0 with hK
  have hKρ : K.Hold ρ := argFacts_hold ρ hargs ws 0 (by simpa [hρ] using hclean)
  set E : EraseEnv := { envOf c.core with facts := K } with hE
  have hframe : fn.initialFrame? (args.map .word) =
      some (frameOf ρ (paramLocals fn.params 0 ++ fn.returns.map fun r => (r.name, .lit 0))) := by
    have h0 : BindingDecl.bindArgs? fn.params (args.map .word) =
        some (frameOf ρ (paramLocals fn.params 0)) :=
      bindArgs_words ρ hargs fn.params 0 hp (by simp [hρ, hlen])
    simp only [FunctionDef.initialFrame?, h0, FunctionDef.returnDefaultBindings,
      defaults_words ρ fn.returns hr, frameOf, List.map_append]
  have hrel : StmtRel ρ E ctx
      { state := { st0 with
          selfBalance := SolidCore.Solidity.Shared.addWord
            (SolidCore.Solidity.Shared.Account.balanceAt ctx.accountBalances ctx.self) ctx.value
          worldMutatedSinceAdoption := true },
        locals := [frameOf ρ (paramLocals fn.params 0 ++ fn.returns.map fun r => (r.name, .lit 0))] }
      (initState fn) :=
    { fields := by subst hctx; rfl
      events := by subst hctx; rfl
      checked := by subst hctx; rfl
      sender := by subst hctx; rfl
      hash := rfl
      ok := hρok
      frames := rfl
      store := by
        intro k hk
        have := getD_storage_cover hd hcov k
        subst hst
        simp only [State.loadSlot, StorageMap.lookup?, initState, Writes.store, hρ]
        rw [← this]
        simp only [SolidCore.Solidity.Shared.norm, modulus_eq, Std.HashMap.get?_eq_getElem?]
        cases (List.foldl (fun acc kv => acc.insertLoop kv.1 kv.2) d.storage σ)[k % wordSize]? <;> rfl
      logs := by subst hst; simp [hd.events, initState]
      facts := hKρ }
  obtain ⟨r, hrun, hleaf⟩ := eval_stmt ρ E ctx fuel fn.body (initState fn) b hb _ hrel
  have hcall : fn.call? fuel c.core.table ctx st0 (args.map .word) =
      some (fn.callBodyResult st0 r) := by
    have hacc' : fn.acceptsValue ctx.value = true := hctxv ▸ hacc
    simp only [FunctionDef.call?, FunctionDef.call, FunctionDef.evalBodyEntry, hacc', hframe,
      if_true, Option.map_some, Option.bind_some]
    rw [show c.core.table = E.tbl from rfl, hrun]
    rfl
  obtain ⟨T', hT', hTe⟩ := brTree_eval fn K ρ b T hT
  rw [hacc, if_pos rfl, hcall, ← hTe]
  generalize b.eval ρ = l at hT' hleaf
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
      collect_words ρ rt S hKρ hleaf.expr.locals fn.returns ws hok hws, untag_words,
      encode_words ρ hKρ fn.returns ws hok, bind, Option.bind, Option.map_some]
    simp only [Source.observe, Tree.eval, Res.obs, if_true, ↓reduceIte, logEntries_map,
      hleaf.logs, Option.some.injEq, Observable.mk.injEq, true_and]
    funext slot
    exact loadSlot_eq _ S.writes ρ hρok hleaf.store slot
  | returned S vs =>
    cases r <;> simp only [LeafRel] at hleaf
    rename_i rt vals
    obtain ⟨hst', rfl⟩ := hleaf
    by_cases hv : vs = []
    · subst hv
      simp only [leafTree, if_true, Option.bind_eq_bind, Option.bind_eq_some_iff] at hT'
      obtain ⟨ws, hws, hT'⟩ := hT'
      split at hT'
      case isFalse => simp at hT'
      rename_i hok
      simp only [Option.some.injEq] at hT'
      subst hT'
      simp only [FunctionDef.callBodyResult, List.map_nil, List.isEmpty_nil, if_true,
        FunctionDef.collectReturns, collectReturnBindings,
        collect_words ρ rt S hKρ hst'.expr.locals fn.returns ws hok hws, untag_words,
        encode_words ρ hKρ fn.returns ws hok, bind, Option.bind, Option.map_some]
      simp only [Source.observe, Tree.eval, Res.obs, if_true, ↓reduceIte, logEntries_map,
        hst'.logs, Option.some.injEq, Observable.mk.injEq, true_and]
      funext slot
      exact loadSlot_eq _ S.writes ρ hρok hst'.store slot
    · simp only [leafTree, hv, if_false] at hT'
      split at hT'
      case isFalse => simp at hT'
      rename_i hok
      simp only [Option.some.injEq] at hT'
      subst hT'
      have hne : (vs.map fun e => Value.word (e.eval ρ)).isEmpty = false := by
        cases vs with
        | nil => exact absurd rfl hv
        | cons _ _ => rfl
      simp only [FunctionDef.callBodyResult, hne, Bool.false_eq_true, if_false,
        FunctionDef.coerceReturnValues, coerceReturnBindings,
        coerce_words ρ rt hKρ fn.returns vs hok, untag_words,
        encode_words ρ hKρ fn.returns vs hok, bind, Option.bind, Option.map_some]
      simp only [Source.observe, Tree.eval, Res.obs, if_true, ↓reduceIte, logEntries_map,
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
        ABI.Contract.encodeRevertData?, Source.observe, Tree.eval, Res.obs, hρ,
        SolidCore.Refinement.Evm.Wide.callAt]
    | panic c =>
      simp only [leafTree, Option.some.injEq] at hT'
      subst hT'
      simp [FunctionDef.callBodyResult, RevertData.untagFixedBytes, Fail.data, encode_panic ρ,
        Source.observe, Tree.eval, Res.obs, hρ, SolidCore.Refinement.Evm.Wide.callAt]
    | error m =>
      simp only [leafTree, Option.map_eq_some_iff] at hT'
      obtain ⟨bs, hbs, rfl⟩ := hT'
      simp [FunctionDef.callBodyResult, RevertData.untagFixedBytes, Fail.data, encode_error ρ _ hbs,
        Source.observe, Tree.eval, Res.obs, hρ, SolidCore.Refinement.Evm.Wide.callAt]

/-- **SolidCore runs a call of a function of the fragment as its erased tree**, from any storage
`σ` that writes every slot the constructor's entries `s` write, on any argument words below
`2 ^ 256`, clean or dirty. -/
theorem source_run {fuel : Nat} {c : TypeCheck.CheckedContract} {d : Source.State}
    {s : List (Nat × Nat)} (hd : Wide.DeployedAt fuel c d s) {σ : List (Nat × Nat)}
    (hcov : Covers s σ) {sel : Nat} (hsel : sel < 2 ^ 32) {fn : FunctionDef}
    (hfind : c.core.findFunctionBySelector? sel = some fn) {T : Tree}
    (hT : eraseFn (envOf c.core) fuel fn = some T) (args : List Nat)
    (hlen : args.length = fn.params.length) (hargs : ∀ a ∈ args, a < 2 ^ 256) :
    Source.run fuel c { calldata := Abi.calldata sel args, callvalue := 0, storage := σ } =
      some (T.eval ⟨args, slotValue σ, solHash⟩).obs := by
  unfold eraseFn at hT
  split at hT
  · simp at hT
  rename_i ws hw
  split at hT
  case isFalse => simp at hT
  rename_i hret
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hT
  obtain ⟨b, hb, t, ht, rfl⟩ := hT
  rw [paramGuards_eval ⟨args, slotValue σ, solHash⟩ t hargs ws 0, List.drop_zero]
  have hdec := decode_args hw args hlen hargs
  by_cases hclean : argsClean ws args = true
  · rw [if_pos hclean]
    rw [if_pos hclean] at hdec
    exact source_run_clean hd hcov hsel hfind hw hret hb ht args hlen hargs hclean hdec
  · rw [if_neg hclean]
    rw [if_neg hclean] at hdec
    rw [run_rejected hd hsel hfind args hdec σ]
    rfl

end SolidCore.Refinement.Generic

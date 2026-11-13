import SolidCore.Refinement.SourceOracle
import SolidCore.Solidity.AdoptionLaws

/-!
# The call node of SolidCore's source semantics

`eval_tryCall`: a `tryExternalCall` statement whose target is not the contract itself (no
self-dispatch), with no gas option and no `extcodesize` guard (solc skips it for a call that
expects return data), evaluates to one request node: the query of an external call of the
sent world (`snapshotWorld`), continued by the interpreter's own continuation (`tryTail`) on the
decoded response and the adopted world.
-/

namespace SolidCore.Refinement.CallNode

open SolidCore.Solidity.Source EvmCompiler.Simulation

/-- The interpreter's continuation of a `tryExternalCall` after the call answered. -/
def tryTail (fuel : Nat) (table : FunctionTable) (context : Context) (runtime''' : Runtime)
    (returns : List BindingDecl) (returnAbiCleanups : List AbiCleanup) (successBody : Stmt)
    (catchClauses : List TryCatchClause) (callResult : LowLevelCallResult) (adoptedState : State) :
    SolI Result :=
  let runtimeWithInteraction :=
    { runtime''' with state := adoptedState }.recordExternalInteraction
      (ExternalInteraction.lowLevelCall callResult)
  let success := callResult.success
  let output := callResult.output.map normByte
  if success then
    match abiDecodeValuesExcept? (returns.map BindingDecl.ty) output with
    | Except.ok decoded =>
      if AbiCleanups.acceptOrUnspecified returnAbiCleanups decoded then
        match BindingDecl.bindArgs? returns decoded with
        | some frame => do
          let result ← Stmt.eval fuel table context (runtimeWithInteraction.withFrame frame)
            successBody
          pure (result.mapRuntime Runtime.popScope)
        | none => pure (Result.reverted runtimeWithInteraction RevertData.typeMismatch)
      else pure (Result.reverted runtimeWithInteraction RevertData.empty)
    | Except.error revertData => pure (Result.reverted runtimeWithInteraction revertData)
  else
    match TryCatchClause.findMatch? output catchClauses with
    | some (frame, body) => do
      let result ← Stmt.eval fuel table context (runtimeWithInteraction.withFrame frame) body
      pure (result.mapRuntime Runtime.popScope)
    | none => pure (Result.reverted runtimeWithInteraction (RevertData.fromRawBytes output))

/-- **The call node**: a `tryExternalCall` of a target other than the contract itself, with no gas
option and no code guard, asks the external call of the sent world and continues with `tryTail`. -/
theorem eval_tryCall (n : Nat) (table : FunctionTable) (context : Context) (rt : Runtime)
    (kind : LowLevelCallKind) (tgt cdE valE : Expr) (gasFirst : Bool) (returns : List BindingDecl)
    (cleanups : List AbiCleanup) (succ : Stmt) (catches : List TryCatchClause)
    {tv vv cdv : Value} {rt1 rt2 rt3 : Runtime} {t v : Word} {cd : List Byte}
    (ht : tgt.evalWithRuntimeByContext context rt = .ok (tv, rt1)) (htw : tv.expectWord = .ok t)
    (hv : valE.evalWithRuntimeByContext context rt1 = .ok (vv, rt2)) (hvw : vv.expectWord = .ok v)
    (hc : cdE.evalWithRuntimeByContext context rt2 = .ok (cdv, rt3)) (hcb : cdv.asBytes? = some cd)
    (hself : wordEq t context.self = false) :
    Stmt.eval (n + 1) table context rt
        (.tryExternalCall kind tgt cdE valE none gasFirst false returns cleanups succ catches) =
      .request (.external (snapshotWorld context rt3.state)
          (.call (buildCallRequest context kind t cd v none)))
        (fun resp => tryTail n table context rt3 returns cleanups succ catches
          (decodeCallResponse resp kind t cd v none) (adoptWorld resp.postWorld context rt3.state)) := by
  rw [Stmt.eval]
  simp only [ht, htw, hv, hvw, hc, hcb, hself, Bool.and_false, Bool.false_and, Bool.or_false,
    Bool.not_false, Bool.true_and, Bool.and_self, Bool.false_eq_true, if_false]
  simp only [selfDispatchCall, hself, Bool.and_false, Bool.false_eq_true, if_false, emitLowLevelCall]
  rfl


theorem eval_block (n : Nat) (table : FunctionTable) (context : Context) (rt : Runtime)
    (ss : List Stmt) :
    Stmt.eval (n + 1) table context rt (.block ss) =
      (Stmt.evalList n table context rt.pushScope ss >>= fun r =>
        pure (r.mapRuntime Runtime.popScope)) := by
  rw [Stmt.eval]

theorem eval_varDecl_none (n : Nat) (table : FunctionTable) (context : Context) (rt : Runtime)
    (ty : Ty) (x : String) :
    Stmt.eval (n + 1) table context rt (.varDecl ty x none) =
      pure (Result.normal (rt.declareLocal x ty.defaultValue)) := by
  rw [Stmt.eval]

theorem evalList_nil (n : Nat) (table : FunctionTable) (context : Context) (rt : Runtime) :
    Stmt.evalList n table context rt [] = pure (Result.normal rt) := by
  rw [Stmt.evalList]

theorem evalList_cons (n : Nat) (table : FunctionTable) (context : Context) (rt : Runtime)
    (s : Stmt) (ss : List Stmt) :
    Stmt.evalList n table context rt (s :: ss) =
      (Stmt.eval n table context rt s >>= fun r =>
        match r with
        | Result.normal rt' => Stmt.evalList n table context rt' ss
        | r => pure r) := by
  rw [Stmt.evalList]
  rfl

theorem bind_request {α β : Type} (q : Query) (k : Answer q → SolI α) (f : α → SolI β) :
    (Interaction.request q k >>= f) = Interaction.request q (fun a => k a >>= f) := rfl

theorem sbind_pure {α β : Type} (a : α) (f : α → SolI β) : ((pure a : SolI α) >>= f) = f a := rfl

theorem map_request {α β : Type} (q : Query) (k : Answer q → SolI α) (f : α → β) :
    (f <$> Interaction.request q k : SolI β) = Interaction.request q (fun a => f <$> k a) := rfl

theorem foldAns_request {α : Type} (ans : Ans) (h : List Interaction.Exchange) (q : Query)
    (k : Answer q → SolI α) :
    foldAns ans h (.request q k) =
      match ans h q with
      | some a => foldAns ans (h ++ [⟨q, a⟩]) (k a)
      | none => none := by
  rw [foldAns]
  cases ans h q <;> rfl

theorem foldAns_pure {α : Type} (ans : Ans) (h : List Interaction.Exchange) (a : α) :
    foldAns ans h (pure a : SolI α) = some a := rfl


/-! ## Pieces of a call's evaluation -/

theorem ipure_bind {ε α β : Type} (a : α) (f : α → Interaction ε β) :
    (Interaction.pure a).bind f = f a := rfl

theorem mat_word (ctx : Context) (rt : Runtime) (w : Word) :
    rt.materializeForValueUse ctx (.word w) = .ok (.word w) := by
  unfold Runtime.materializeForValueUse
  rw [Runtime.materializeForValueUseFuel]
  all_goals intros
  all_goals contradiction

theorem word0_eval (ctx : Context) (rt : Runtime) :
    (Expr.word 0).evalWithRuntimeByContext ctx rt = .ok (.word 0, rt) := rfl

theorem headWords_uint256 :
    (if Ty.uint256.isDynamicAbi = true then some 1 else Ty.uint256.staticAbiHeadWords?) = some 1 :=
  rfl

theorem wordBytes_eq : SolidCore.Solidity.Source.wordBytes = 32 := rfl

/-- A one-word return shorter than a word fails to decode, with empty revert data. -/
theorem decode_short (bs : List Byte) (h : bs.length < 32) :
    abiDecodeValuesExcept? [Ty.uint256] bs = .error .empty := by
  simp [abiDecodeValuesExcept?, Ty.listAbiHeadWords?, Ty.abiHeadWords?, abiDecodeOpt, bind,
    Except.bind, pure, Except.pure, headWords_uint256, wordBytes_eq, h]

/-- A one-word return of at least a word decodes to its first word, big-endian. -/
theorem decode_word (bs : List Byte) (h : 32 ≤ bs.length) :
    abiDecodeValuesExcept? [Ty.uint256] bs =
      .ok [.word (bytesToWordBE ((bs.map normByte).take 32))] := by
  have : ¬ bs.length < 32 := by omega
  simp [abiDecodeValuesExcept?, Ty.listAbiHeadWords?, Ty.abiHeadWords?, abiDecodeOpt, bind,
    Except.bind, pure, Except.pure, abiDecodeValuesAux?, abiDecodeValueAt?, headWords_uint256,
    wordBytes_eq, this]
  rw [show Ty.uint256.abiDecodeFuel = 1 from rfl]
  simp [abiDecodeValueAtWithFuel?, readWord?, readBytes?, wordBytes_eq, h, this, abiDecodeOpt]
  rfl

/-- With no catch clause, a failed call matches none. -/
theorem findMatch_nil (raw : List Byte) : TryCatchClause.findMatch? raw [] = none := by
  unfold TryCatchClause.findMatch?
  cases revertClassify raw <;> rfl


theorem toList_loop (bs : ByteArray) : ∀ n i r, bs.size - i = n →
    ByteArray.toList.loop bs i r = r.reverse ++ (List.range' i n).map bs.get! := by
  intro n
  induction n with
  | zero =>
    intro i r h
    rw [ByteArray.toList.loop]
    rw [if_neg (by omega)]
    simp
  | succ n ih =>
    intro i r h
    rw [ByteArray.toList.loop, if_pos (by omega), ih (i + 1) _ (by omega)]
    simp [List.range'_succ]

theorem byteArrayToBytes_eq (rd : ByteArray) :
    byteArrayToBytes rd = (List.range rd.size).map (fun j => (rd.get! j).toNat) := by
  unfold byteArrayToBytes ByteArray.toList
  rw [toList_loop rd rd.size 0 [] (by omega), List.range_eq_range']
  simp

theorem normByte_bytes (rd : ByteArray) : (byteArrayToBytes rd).map normByte = byteArrayToBytes rd := by
  unfold byteArrayToBytes
  simp only [List.map_map]
  apply List.map_congr_left
  intro x _
  simp [normByte, SolidCore.Solidity.Shared.Account.byte, Nat.mod_eq_of_lt (UInt8.toNat_lt x)]

theorem map_pure' {α β : Type} (a : α) (f : α → β) : (f <$> (pure a : SolI α)) = pure (f a) := rfl


theorem toList_eq_data (bs : ByteArray) : bs.toList = bs.data.toList := by
  unfold ByteArray.toList
  rw [toList_loop bs bs.size 0 [] (by omega)]
  obtain ⟨arr⟩ := bs
  apply List.ext_getElem
  · simp only [List.reverse_nil, List.nil_append, List.length_map, List.length_range',
      Array.length_toList]
    rfl
  · intro i h1 h2
    simp only [List.reverse_nil, List.nil_append, List.getElem_map, List.getElem_range',
      Array.getElem_toList, ByteArray.get!]
    have : i < arr.size := by simpa using h2
    rw [getElem!_pos arr (0 + 1 * i) (by omega)]
    simp


theorem norm_norm (x : Word) :
    SolidCore.Solidity.Shared.norm (SolidCore.Solidity.Shared.norm x) =
      SolidCore.Solidity.Shared.norm x := by
  simp [SolidCore.Solidity.Shared.norm]

theorem wf_insertLoop (m : StorageMap) (hm : StorageMap.WF m) (k v : Word) :
    StorageMap.WF (m.insertLoop k v) := by
  intro p hp
  unfold StorageMap.insertLoop at hp
  rw [Std.HashMap.mem_toList_iff_getElem?_eq_some, Std.HashMap.getElem?_insert] at hp
  split at hp
  · rename_i he
    simp only [beq_iff_eq] at he
    simp only [Option.some.injEq] at hp
    rw [← he, ← hp]
    exact ⟨norm_norm k, norm_norm v⟩
  · exact hm p (Std.HashMap.mem_toList_iff_getElem?_eq_some.mpr hp)

theorem wf_foldl : ∀ (σ : List (Nat × Nat)) (m : StorageMap), StorageMap.WF m →
    StorageMap.WF (σ.foldl (fun acc kv => acc.insertLoop kv.1 kv.2) m)
  | [], _, hm => hm
  | kv :: σ, m, hm => wf_foldl σ _ (wf_insertLoop m hm kv.1 kv.2)

theorem wf_of_toList_nil (m : StorageMap) (h : m.toList = []) : StorageMap.WF m := by
  intro p hp
  rw [h] at hp
  cases hp

/-! ## The code a sent world shows -/

theorem addr_val (x : Word) (hx : x < 2 ^ 160) : (wordToAddress x).val = x := by
  simp [wordToAddress, wordToU256, EvmYul.AccountAddress.ofUInt256, EvmYul.UInt256.ofNat, Id.run,
    EvmYul.UInt256.size, Fin.ofNat, EvmYul.AccountAddress.size]
  omega

theorem addr_eq {x y : Word} (hx : x < 2 ^ 160) (hy : y < 2 ^ 160) :
    compare (wordToAddress x) (wordToAddress y) = .eq ↔ x = y := by
  rw [Std.LawfulEqCmp.compare_eq_iff_eq]
  constructor
  · intro h
    have := congrArg Fin.val h
    rwa [addr_val x hx, addr_val y hy] at this
  · intro h; rw [h]

theorem find_fold (mk : Word → OpenAccount) (x : Word) (hx : x < 2 ^ 160) :
    ∀ (cs : List (Word × OpenAccount)) (M : EvmYul.AddrMap OpenAccount),
      (∀ e ∈ cs, e.1 < 2 ^ 160 ∧ e.2 = mk e.1) →
      (cs.foldl (fun (acc : EvmYul.AddrMap OpenAccount) entry => acc.insert (wordToAddress entry.1) entry.2)
        M).find? (wordToAddress x) = if x ∈ cs.map Prod.fst then some (mk x) else M.find? (wordToAddress x)
  | [], M, _ => by simp
  | e :: cs, M, hcs => by
    simp only [List.foldl_cons, List.map_cons, List.mem_cons]
    rw [find_fold mk x hx cs _ (fun e he => hcs e (List.mem_cons_of_mem _ he))]
    obtain ⟨he1, he2⟩ := hcs e (List.mem_cons_self ..)
    by_cases hin : x ∈ cs.map Prod.fst
    · simp [hin]
    · simp only [hin, or_false, if_false]
      rw [RBTree.RBMap.find?_insert]
      by_cases hxe : x = e.1
      · rw [if_pos ((addr_eq hx he1).mpr hxe), if_pos hxe, he2, hxe]
      · rw [if_neg (fun h => hxe ((addr_eq hx he1).mp h)), if_neg hxe]

theorem mem_dedup (x : Word) : ∀ (l acc : List Word),
    x ∈ l.foldl (fun acc a => if acc.contains a then acc else acc ++ [a]) acc ↔ x ∈ acc ∨ x ∈ l
  | [], acc => by simp
  | a :: l, acc => by
    simp only [List.foldl_cons]
    rw [mem_dedup x l]
    split
    · rename_i h
      have : a ∈ acc := by simpa using h
      constructor
      · rintro (h1 | h1)
        · exact Or.inl h1
        · exact Or.inr (List.mem_cons_of_mem _ h1)
      · rintro (h1 | h1)
        · exact Or.inl h1
        · rcases List.mem_cons.mp h1 with h2 | h2
          · exact Or.inl (h2 ▸ this)
          · exact Or.inr h2
    · simp only [List.mem_append, List.mem_singleton, List.mem_cons]
      tauto

theorem wm : SolidCore.Solidity.Shared.wordModulus = 2 ^ 256 := rfl

theorem lookupBytes_none (x : Word) (hx : x < 2 ^ 160) : ∀ (cs : List (Word × List Nat)),
    (∀ p ∈ cs, p.1 < 2 ^ 160) → x ∉ cs.map Prod.fst →
    SolidCore.Solidity.Shared.Account.lookupBytes? cs x = none
  | [], _, _ => rfl
  | p :: cs, hk, hn => by
    have hp := hk p (List.mem_cons_self ..)
    have hne : p.1 ≠ x := fun h => hn (by simp [← h])
    simp only [SolidCore.Solidity.Shared.Account.lookupBytes?]
    rw [if_neg]
    · exact lookupBytes_none x hx cs (fun q hq => hk q (List.mem_cons_of_mem _ hq))
        (fun h => hn (List.mem_cons_of_mem _ h))
    · simp only [SolidCore.Solidity.Shared.Account.wordEq, SolidCore.Solidity.Shared.norm, beq_iff_eq]
      rw [Nat.mod_eq_of_lt (lt_trans hp (by decide)), Nat.mod_eq_of_lt (lt_trans hx (by decide))]
      exact hne

theorem isEmpty_bytes (l : List Nat) : (byteArrayToBytes (bytesToByteArray l)).isEmpty = l.isEmpty := by
  simp [byteArrayToBytes, toList_eq_data, bytesToByteArray]

theorem codeIn_snapshot (ctx : Context) (st : State) (henv : st.envWorld? = none)
    (hb : ctx.accountBalances = []) (hh : ctx.accountCodehashes = [])
    (hk : ∀ p ∈ ctx.accountCodes, p.1 < 2 ^ 160) (hself : ctx.self < 2 ^ 160)
    (x : Word) (hx : x < 2 ^ 160) :
    (codeIn (snapshotWorld ctx st) x).isEmpty =
      (SolidCore.Solidity.Shared.Account.codeAt ctx.accountCodes x).isEmpty := by
  unfold codeIn accountIn snapshotWorld
  rw [henv]
  simp only [snapshotWorldSeed]
  rw [RBTree.RBMap.find?_insert]
  by_cases hxs : x = ctx.self
  · rw [if_pos ((addr_eq hx hself).mpr hxs)]
    simp only [Option.getD_some, snapshotSelfAccount, henv, isEmpty_bytes, hxs]
  · rw [if_neg (fun h => hxs ((addr_eq hx hself).mp h))]
    have hnorm : ∀ p ∈ ctx.accountCodes, SolidCore.Solidity.Shared.norm p.1 = p.1 := by
      intro p hp
      have := hk p hp
      simp only [SolidCore.Solidity.Shared.norm]
      exact Nat.mod_eq_of_lt (lt_trans this (by decide))
    have hmem : ∀ a, a ∈ (snapshotOtherAccounts ctx).map Prod.fst ↔
        (a ∈ ctx.accountCodes.map Prod.fst ∧ ¬ wordEq a ctx.self = true) := by
      intro a
      simp only [snapshotOtherAccounts, hb, hh, List.map_nil, List.nil_append, List.append_nil,
        List.map_map, List.mem_map, List.mem_filter, Function.comp]
      constructor
      · rintro ⟨b, ⟨hb1, hb2⟩, rfl⟩
        rw [mem_dedup] at hb1
        simp only [List.not_mem_nil, false_or, List.mem_map] at hb1
        obtain ⟨p, hp, rfl⟩ := hb1
        refine ⟨⟨p, hp, (hnorm p hp).symm⟩, by simpa using hb2⟩
      · rintro ⟨⟨p, hp, rfl⟩, h2⟩
        refine ⟨p.1, ⟨?_, by simpa using h2⟩, rfl⟩
        rw [mem_dedup]
        simp only [List.not_mem_nil, false_or, List.mem_map]
        exact ⟨p, hp, hnorm p hp⟩
    rw [find_fold (fun a => { nonce := wordToU256 0, balance := wordToU256 (SolidCore.Solidity.Shared.Account.balanceAt ctx.accountBalances a), storage := default, transientStorage := default, codeBytes := bytesToByteArray (SolidCore.Solidity.Shared.Account.codeAt ctx.accountCodes a) })
      x hx]
    · have hwe : wordEq x ctx.self = false := by
        simp only [wordEq, SolidCore.Solidity.Shared.norm, beq_eq_false_iff_ne]
        rw [Nat.mod_eq_of_lt (lt_trans hx (by decide)), Nat.mod_eq_of_lt (lt_trans hself (by decide))]
        exact hxs
      by_cases hin : x ∈ List.map Prod.fst (snapshotOtherAccounts ctx)
      · rw [if_pos hin]
        simp only [Option.getD_some, isEmpty_bytes]
      · rw [if_neg hin]
        have hnk : x ∉ ctx.accountCodes.map Prod.fst := fun h => hin ((hmem x).mpr ⟨h, by simp [hwe]⟩)
        have hcode : SolidCore.Solidity.Shared.Account.codeAt ctx.accountCodes x = [] := by
          simp only [SolidCore.Solidity.Shared.Account.codeAt, lookupBytes_none x hx _ hk hnk, Option.getD_none]
        rw [hcode, show RBTree.RBMap.find? (default : EvmYul.AddrMap OpenAccount) (wordToAddress x) = none from rfl]
        simp [byteArrayToBytes, toList_eq_data]
        rfl
    · intro e he
      have he1 : e.1 ∈ List.map Prod.fst (snapshotOtherAccounts ctx) := List.mem_map_of_mem he
      obtain ⟨hk1, -⟩ := (hmem e.1).mp he1
      obtain ⟨q, hq, hqe⟩ := List.mem_map.mp hk1
      refine ⟨hqe ▸ hk q hq, ?_⟩
      simp only [snapshotOtherAccounts, List.mem_map, List.mem_filter] at he
      obtain ⟨a, -, rfl⟩ := he
      rfl

end SolidCore.Refinement.CallNode

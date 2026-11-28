import SolidCore.Refinement.Generic.SourceCall
import Verify.Run
import SolidCore.Refinement.Dirty.Source
import SolidCore.Refinement.AbiStatic

/-!
# SolidCore runs an external call of a function of the fragment as its tree

`source_run` is the source half of the generic source stage: on a call of the function `fn` with
selector `sel` (call data `Abi.calldata sel args`, any argument words below `2 ^ 256`, no value,
initial storage `σ`) to a contract whose constructor leaves the storage entries `s` and no logs,
when `σ` writes every slot `s` does (`Covers s σ`), SolidCore's `Source.run` shows
`(T.eval ⟨args, slotValue σ, solHash, callerWord⟩).obs`, where `T` is the erasure `eraseFn` of `fn` in the
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

/-- A parameter type of the fragment: a word, a signed word or a `bytes32`. -/
abbrev ParamTy (ty : Source.Ty) : Prop :=
  ty = .uint256 ∨ ty = .address ∨ ty = .bool ∨ ty = .int256 ∨ ty = .fixedBytes 32 ∨
    ty = .tuple [.uint256]

/-- An ABI cleanup of a parameter of the fragment. -/
abbrev ParamCleanup (c : AbiCleanup) : Prop :=
  c = .none ∨ (∃ b, c = .uint b ∧ 0 < b ∧ b ≤ 256) ∨ (∃ m, c = .enum m ∧ m < wordSize) ∨ c = .int 256 ∨
    (∃ b, c = .int b ∧ 0 < b ∧ b < 256) ∨ c = .tuple [.uint 256]

theorem paramWidth_spec {p : BindingDecl} {c : AbiCleanup} {w : Nat} (h : paramWidthT p c = some w) :
    p.isStorageRef = false ∧ ((w < wordSize ∧
      ((p.ty = .uint256 ∧ ∃ b, c = .uint b ∧ 0 < b ∧ b ≤ 256 ∧ w = 2 ^ b - 1) ∨
        (p.ty = .uint256 ∧ c = .enum w) ∨
        (p.ty = .address ∧ c = .none ∧ w = 2 ^ 160 - 1) ∨
        (p.ty = .bool ∧ c = .none ∧ w = 1) ∨
        (p.ty = .int256 ∧ c = .int 256 ∧ w = 2 ^ 256 - 1) ∨
        (p.ty = .fixedBytes 32 ∧ c = .none ∧ w = 2 ^ 256 - 1) ∨
        (p.ty = .tuple [.uint256] ∧ c = .tuple [.uint 256] ∧ w = 2 ^ 256 - 1))) ∨
      (p.ty = .int256 ∧ ∃ b, c = .int b ∧ 0 < b ∧ b < 256 ∧ w = wordSize + b)) := by
  unfold paramWidthT at h
  split at h
  · simp at h
  rename_i hs
  have hs' : p.isStorageRef = false := by simpa using hs
  split at h
  · rename_i b ht
    split at h
    · rename_i hb
      simp only [Option.some.injEq] at h
      subst h
      refine ⟨hs', .inl ⟨Nat.sub_lt (Nat.two_pow_pos _) (by decide) |>.trans_le
        (Nat.pow_le_pow_right (by decide) hb.2), .inl ⟨ht, _, rfl, hb.1, hb.2, rfl⟩⟩⟩
    · simp at h
  · rename_i m ht
    split at h
    · rename_i hm
      simp only [Option.some.injEq] at h
      subst h
      exact ⟨hs', .inl ⟨hm, .inr (.inl ⟨ht, rfl⟩)⟩⟩
    · simp at h
  · rename_i ht
    simp only [Option.some.injEq] at h
    subst h
    exact ⟨hs', .inl ⟨by decide, .inr (.inr (.inl ⟨ht, rfl, rfl⟩))⟩⟩
  · rename_i ht
    simp only [Option.some.injEq] at h
    subst h
    exact ⟨hs', .inl ⟨by decide, .inr (.inr (.inr (.inl ⟨ht, rfl, rfl⟩)))⟩⟩
  · rename_i ht
    simp only [Option.some.injEq] at h
    subst h
    exact ⟨hs', .inl ⟨by decide, .inr (.inr (.inr (.inr (.inl ⟨ht, rfl, rfl⟩))))⟩⟩
  · split at h
    · rename_i hb
      simp only [Option.some.injEq] at h
      subst h
      exact ⟨hs', .inr ⟨by assumption, _, rfl, hb.1, hb.2, rfl⟩⟩
    · simp at h
  · rename_i ht
    simp only [Option.some.injEq] at h
    subst h
    exact ⟨hs', .inl ⟨by decide, .inr (.inr (.inr (.inr (.inr (.inl ⟨ht, rfl, rfl⟩)))))⟩⟩
  · rename_i ht
    simp only [Option.some.injEq] at h
    subst h
    exact ⟨hs', .inl ⟨by decide, .inr (.inr (.inr (.inr (.inr (.inr ⟨ht, rfl, rfl⟩)))))⟩⟩
  · simp at h

theorem paramWidth_ty {p : BindingDecl} {c : AbiCleanup} {w : Nat} (h : paramWidthT p c = some w) :
    ParamTy p.ty := by
  rcases (paramWidth_spec h).2 with ⟨-, hk⟩ | ⟨ht, -⟩
  swap
  · exact .inr (.inr (.inr (.inl ht)))
  rcases hk with ⟨ht, -⟩ | ⟨ht, -⟩ | ⟨ht, -⟩ | ⟨ht, -⟩ | ⟨ht, -⟩ | ⟨ht, -⟩ | ⟨ht, -⟩
  · exact .inl ht
  · exact .inl ht
  · exact .inr (.inl ht)
  · exact .inr (.inr (.inl ht))
  · exact .inr (.inr (.inr (.inl ht)))
  · exact .inr (.inr (.inr (.inr (.inl ht))))
  · exact .inr (.inr (.inr (.inr (.inr ht))))

theorem paramWidth_cleanup {p : BindingDecl} {c : AbiCleanup} {w : Nat} (h : paramWidthT p c = some w) :
    ParamCleanup c := by
  rcases (paramWidth_spec h).2 with ⟨hw, hk⟩ | ⟨-, b, hc, hb0, hb, -⟩
  swap
  · exact .inr (.inr (.inr (.inr (.inl ⟨b, hc, hb0, hb⟩))))
  rcases hk with ⟨-, b, hc, hb0, hb, -⟩ | ⟨-, hc⟩ | ⟨-, hc, -⟩ | ⟨-, hc, -⟩ |
      ⟨-, hc, -⟩ | ⟨-, hc, -⟩ | ⟨-, hc, -⟩
  · exact .inr (.inl ⟨b, hc, hb0, hb⟩)
  · exact .inr (.inr (.inl ⟨w, hc, hw⟩))
  · exact .inl hc
  · exact .inl hc
  · exact .inr (.inr (.inr (.inl hc)))
  · exact .inl hc
  · exact .inr (.inr (.inr (.inr (.inr hc))))

theorem widthsOf_spec : ∀ {ps : List BindingDecl} {cs : List AbiCleanup} {ws : List Nat},
    widthsOfT ps cs = some ws →
      cs.length = ps.length ∧ ws.length = ps.length ∧
      (∀ p ∈ ps, ParamTy p.ty ∧ p.isStorageRef = false) ∧
      (∀ c ∈ cs, ParamCleanup c) ∧ (∀ w ∈ ws, w < wordSize + 256)
  | [], [], ws, h => by
    simp only [widthsOfT, Option.some.injEq] at h
    subst h
    simp
  | p :: ps, c :: cs, ws, h => by
    simp only [widthsOfT, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨w, hw, ws', hws', rfl⟩ := h
    obtain ⟨h1, h2, h3, h4, h5⟩ := widthsOf_spec hws'
    obtain ⟨hs, hk⟩ := paramWidth_spec hw
    have hwl : w < wordSize + 256 := by
      rcases hk with ⟨hw', -⟩ | ⟨-, b, -, -, hb, rfl⟩ <;> omega
    refine ⟨by simp [h1], by simp [h2], ?_, ?_, ?_⟩
    · intro q hq
      rcases List.mem_cons.mp hq with rfl | hq
      · exact ⟨paramWidth_ty hw, hs⟩
      · exact h3 q hq
    · intro d hd
      rcases List.mem_cons.mp hd with rfl | hd
      · exact paramWidth_cleanup hw
      · exact h4 d hd
    · intro v hv
      rcases List.mem_cons.mp hv with rfl | hv
      · exact hwl
      · exact h5 v hv
  | [], _ :: _, _, h | _ :: _, [], _, h => by simp [widthsOfT] at h

/-- SolidCore's values of argument words, each by its parameter type's tag. -/
def tyVals : List Source.Ty → List Nat → List Value
  | ty :: tys, a :: as => (tagOf ty).val a :: tyVals tys as
  | _, _ => []

theorem tyVals_length : ∀ (tys : List Source.Ty) (as : List Nat), tys.length = as.length →
    (tyVals tys as).length = as.length
  | [], [], _ => rfl
  | _ :: tys, _ :: as, h => by simp [tyVals, tyVals_length tys as (by simpa using h)]
  | [], _ :: _, h | _ :: _, [], h => by simp at h

/-- SolidCore's decoder's value of an argument word, before the lazy cleanups: a calldata struct
of one word is the tuple of that word. -/
def rawVal (ty : Source.Ty) (a : Nat) : Value :=
  if tagOf ty = .tup1 then .tuple [.word a] else (tagOf ty).val a

/-- SolidCore's decoder's values of argument words, before the lazy cleanups. -/
def tyValsRaw : List Source.Ty → List Nat → List Value
  | ty :: tys, a :: as => rawVal ty a :: tyValsRaw tys as
  | _, _ => []

/-- The value a call's parameter binds as its word does: the word, or for a calldata struct of one
word, its lazily checked tuple (which no word coerces to). -/
def argVal (ty : Source.Ty) (a : Nat) : Value :=
  if tagOf ty = .tup1 then Tag.tup1.val a else .word a

/-- The values the parameters bind as their words do. -/
def argVals : List Source.Ty → List Nat → List Value
  | ty :: tys, a :: as => argVal ty a :: argVals tys as
  | _, _ => []

theorem argVals_words : ∀ {tys : List Source.Ty} {as : List Nat}, (∀ ty ∈ tys, tagOf ty = .word) →
    argVals tys as = (as.take tys.length).map .word
  | [], _, _ => by simp [argVals]
  | _ :: _, [], _ => by simp [argVals]
  | ty :: tys, a :: as, h => by
    simp only [argVals, argVal, h ty List.mem_cons_self, reduceCtorEq, ↓reduceIte, List.length_cons,
      List.take_succ_cons, List.map_cons, argVals_words (fun t ht => h t (List.mem_cons_of_mem _ ht))]

theorem argVals_words' {tys : List Source.Ty} {as : List Nat} (h : ∀ ty ∈ tys, tagOf ty = .word)
    (hl : as.length = tys.length) : argVals tys as = as.map .word := by
  rw [argVals_words h, ← hl, List.take_length]

theorem paramWidth_T {p : BindingDecl} {c : AbiCleanup} {w : Nat} (h : paramWidth p c = some w) :
    paramWidthT p c = some w ∧ tagOf p.ty = .word := by
  unfold paramWidth at h
  split at h
  · exact ⟨h, by assumption⟩
  · simp at h

/-- Bounds of word parameters are bounds of the generic stage, and every parameter is a word. -/
theorem widthsOf_T : ∀ {ps : List BindingDecl} {cs : List AbiCleanup} {ws : List Nat},
    widthsOf ps cs = some ws → widthsOfT ps cs = some ws ∧ ∀ p ∈ ps, tagOf p.ty = .word
  | [], [], ws, h => by simp only [widthsOf, Option.some.injEq] at h; subst h; simp [widthsOfT]
  | p :: ps, c :: cs, ws, h => by
    simp only [widthsOf, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨w, hw, ws', hws', rfl⟩ := h
    obtain ⟨h1, h2⟩ := paramWidth_T hw
    obtain ⟨h3, h4⟩ := widthsOf_T hws'
    refine ⟨by simp [widthsOfT, h1, h3], ?_⟩
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact h2
    · exact h4 q hq
  | [], _ :: _, _, h | _ :: _, [], _, h => by simp [widthsOf] at h

theorem paramTags_words : ∀ {ps : List BindingDecl}, (∀ p ∈ ps, tagOf p.ty = .word) → paramTags ps = []
  | [], _ => rfl
  | p :: ps, h => by
    simp only [paramTags, h p List.mem_cons_self, ↓reduceIte]
    exact paramTags_words (fun q hq => h q (List.mem_cons_of_mem _ hq))

/-- A function whose parameters are all words has consistent tags. -/
theorem tagsOk_of_words {fn : FunctionDef} (h : ∀ p ∈ fn.params ++ fn.returns, tagOf p.ty = .word) :
    tagsOk fn = true := by
  simp only [tagsOk, fnTags, paramTags_words h, Tags.get_nil, List.all_eq_true, beq_iff_eq]
  exact fun p hp => (h p hp).symm

theorem tyVals_words : ∀ {tys : List Source.Ty} {as : List Nat}, (∀ ty ∈ tys, tagOf ty = .word) →
    as.length = tys.length → tyVals tys as = as.map .word
  | [], [], _, _ => rfl
  | ty :: tys, a :: as, h, hl => by
    simp only [tyVals, h ty List.mem_cons_self, Tag.val, List.map_cons,
      tyVals_words (fun t ht => h t (List.mem_cons_of_mem _ ht)) (by simpa using hl)]
  | [], _ :: _, _, hl | _ :: _, [], _, hl => by simp at hl

/-- The decoded values of a function whose parameters are all words are its argument words. -/
theorem tyVals_params {fn : FunctionDef} {ws : List Nat}
    (hw : widthsOf fn.params fn.paramAbiCleanups = some ws) {args : List Nat}
    (hlen : args.length = fn.params.length) :
    tyVals (fn.params.map BindingDecl.ty) args = args.map .word :=
  tyVals_words (fun ty hty => by
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hty
    exact (widthsOf_T hw).2 p hp) (by simpa using hlen)

/-! ## Decoding the argument words -/

/-- Whether SolidCore's decoder accepts the word `a` for the type `ty`: an `address` word must be
below `2 ^ 160` and a `bool` word at most 1. -/
def decodeClean : Source.Ty → Nat → Bool
  | .address, a => decide (a < 2 ^ 160)
  | .bool, a => decide (a ≤ 1)
  | _, _ => true

/-- Whether SolidCore's decoder accepts every argument word for its parameter's type. -/
def decodeCleanAll : List Source.Ty → List Nat → Bool
  | ty :: tys, a :: as => decodeClean ty a && decodeCleanAll tys as
  | _, _ => true

/-- Whether the word `a` passes the ABI cleanup `c`. -/
def cleanArg : AbiCleanup → Nat → Bool
  | .uint b, a => decide (a < 2 ^ b)
  | .enum m, a => decide (a ≤ m)
  | .int b, a => if 0 < b ∧ b < 256 then decide (sextNat b a = a) else true
  | _, _ => true

/-- Whether every argument word passes its parameter's ABI cleanup. -/
def cleanupsClean : List AbiCleanup → List Nat → Bool
  | c :: cs, a :: as => cleanArg c a && cleanupsClean cs as
  | _, _ => true

/-- Whether the argument word `a` passes its parameter's check `w` (`paramWidthT`): at most `w` for
a bound below `wordSize`, and its own sign extension from `w - wordSize` bits otherwise. -/
def argOk (w a : Nat) : Bool :=
  if w < 2 ^ 256 then decide (a ≤ w)
  else if 0 < w - 2 ^ 256 ∧ w - 2 ^ 256 < 256 then decide (sextNat (w - 2 ^ 256) a = a)
  else true

theorem argOk_eq (w a : Nat) : argOk w a = if w < wordSize then decide (a ≤ w)
    else if 0 < w - wordSize ∧ w - wordSize < 256 then decide (sextNat (w - wordSize) a = a)
    else true := rfl

theorem argOk_zero (w : Nat) : argOk w 0 = true := by
  rw [argOk_eq]
  split
  · simp
  · split
    · simp [sextNat, Nat.two_pow_pos]
    · rfl

theorem argOk_lt {w : Nat} (a : Nat) (h : w < wordSize) : argOk w a = decide (a ≤ w) := by
  simp [argOk_eq, h]

theorem argOk_sext (a b : Nat) (hb : 0 < b ∧ b < 256) :
    argOk (wordSize + b) a = decide (sextNat b a = a) := by
  simp [argOk_eq, hb]

/-- Whether every argument word passes its parameter's check. -/
def argsClean : List Nat → List Nat → Bool
  | w :: ws, a :: as => argOk w a && argsClean ws as
  | _, _ => true

theorem headWords_word {ty : Source.Ty} (h : ParamTy ty) :
    ABI.Ty.abiHeadWords? ty = some 1 := by
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [ABI.Ty.abiHeadWords?, ABI.Ty.isDynamicAbi, ABI.Ty.staticAbiHeadWords?,
      ABI.Ty.listHasDynamicAbi, ABI.Ty.listStaticAbiHeadWords?]

/-- SolidCore decodes a calldata struct of one word at a head word as the tuple of that word. -/
theorem decode_tuple1 (args : List Nat) (hargs : ∀ a ∈ args, a < wordSize) {i : Nat}
    (hi : i < args.length) (lazy : Bool) :
    ABI.decodeValueAt? lazy (Dirty.argBytes args) i (.tuple [.uint256]) =
      .ok (.tuple [.word args[i]]) := by
  have hr := Dirty.readWord_argBytes args hargs i hi
  have hb := Abi.readBytes_argBytes args i hi
  simp [ABI.decodeValueAt?, ABI.Ty.abiDecodeFuel, ABI.Ty.listAbiDecodeFuel, ABI.decodeValueAtWithFuel?,
    ABI.Ty.listHasDynamicAbi, ABI.Ty.isDynamicAbi, ABI.Ty.listAbiHeadWords?, ABI.Ty.abiHeadWords?,
    ABI.Ty.staticAbiHeadWords?, ABI.decodeValueList?, ABI.wordBytes, hr, hb, ABI.abiArgOpt, bind,
    Except.bind, pure, Except.pure]

theorem listHeadWords_words : ∀ (tys : List Source.Ty), (∀ t ∈ tys, ParamTy t) →
    ABI.Ty.listAbiHeadWords? tys = some tys.length
  | [], _ => rfl
  | t :: ts, h => by
    simp [ABI.Ty.listAbiHeadWords?, headWords_word (h t List.mem_cons_self),
      listHeadWords_words ts (fun u hu => h u (List.mem_cons_of_mem _ hu)), Nat.add_comm]

theorem decodeAux_words (args : List Nat) (hargs : ∀ a ∈ args, a < wordSize) :
    ∀ (ps : List (Bool × Source.Ty)) (idx : Nat), (∀ p ∈ ps, ParamTy p.2) →
      idx + ps.length = args.length →
      ABI.decodeArgsAux? (Dirty.argBytes args) ps idx =
        if decodeCleanAll (ps.map Prod.snd) (args.drop idx) then
          .ok (tyValsRaw (ps.map Prod.snd) (args.drop idx))
        else .error .empty
  | [], idx, _, hlen => by
    simp only [List.length_nil, Nat.add_zero] at hlen
    subst hlen
    simp [ABI.decodeArgsAux?, decodeCleanAll, tyValsRaw]
  | (lazy, ty) :: ps, idx, hps, hlen => by
    have hi : idx < args.length := by simp at hlen; omega
    have hr := Dirty.readWord_argBytes args hargs idx hi
    have ih := decodeAux_words args hargs ps (idx + 1)
      (fun p hp => hps p (List.mem_cons_of_mem _ hp)) (by simp at hlen; omega)
    have hty : ParamTy ty := hps _ List.mem_cons_self
    have ha := hargs _ (List.getElem_mem hi)
    rw [List.drop_eq_getElem_cons hi]
    rcases hty with rfl | rfl | rfl | rfl | rfl | rfl
    · simp only [ABI.decodeArgsAux?, ABI.decodeValueAt?, ABI.Ty.abiDecodeFuel,
        ABI.decodeValueAtWithFuel?, ABI.wordBytes, hr, ABI.abiArgOpt,
        headWords_word (Or.inl rfl), bind, Except.bind, pure, Except.pure, ih, List.map_cons,
        decodeCleanAll, decodeClean, Bool.true_and, tyValsRaw, rawVal, tagOf, Tag.val, reduceCtorEq, ↓reduceIte]
      by_cases hc : decodeCleanAll (List.map Prod.snd ps) (List.drop (idx + 1) args) = true <;>
        simp [hc]
    · simp only [ABI.decodeArgsAux?, ABI.decodeValueAt?, ABI.Ty.abiDecodeFuel,
        ABI.decodeValueAtWithFuel?, ABI.wordBytes, hr, ABI.abiArgOpt, ABI.addressFits, norm_lt ha,
        headWords_word (Or.inr (Or.inl rfl)), bind, Except.bind, pure, Except.pure, ih, List.map_cons,
        decodeCleanAll, decodeClean, tyValsRaw, rawVal, tagOf, Tag.val, reduceCtorEq, ↓reduceIte]
      by_cases h1 : args[idx] < 2 ^ 160
      · simp only [h1, decide_true, Bool.true_and, ↓reduceIte]
        by_cases hc : decodeCleanAll (List.map Prod.snd ps) (List.drop (idx + 1) args) = true <;>
          simp [hc]
      · simp only [h1, decide_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
    · have hb : (wordEq args[idx] 0 || wordEq args[idx] 1) = decide (args[idx] ≤ 1) := by
        have key : ∀ v : Nat, v < wordSize → (wordEq v 0 || wordEq v 1) = decide (v ≤ 1) := by
          intro v hv
          have ham : SolidCore.Solidity.Shared.norm v = v := Nat.mod_eq_of_lt hv
          simp only [wordEq, ham, show SolidCore.Solidity.Shared.norm 0 = 0 from rfl,
            show SolidCore.Solidity.Shared.norm 1 = 1 from rfl]
          rcases Nat.lt_or_ge v 2 with h | h
          · rcases (show v = 0 ∨ v = 1 by omega) with rfl | rfl <;> rfl
          · have h0 : (v == 0) = false := by simp; omega
            have h1 : (v == 1) = false := by simp; omega
            have h2 : decide (v ≤ 1) = false := by simp; omega
            rw [h0, h1, h2]; rfl
        exact key _ ha
      simp only [ABI.decodeArgsAux?, ABI.decodeValueAt?, ABI.Ty.abiDecodeFuel,
        ABI.decodeValueAtWithFuel?, ABI.wordBytes, hr, ABI.abiArgOpt, hb,
        headWords_word (Or.inr (Or.inr (Or.inl rfl))), bind, Except.bind, pure, Except.pure, ih,
        List.map_cons, decodeCleanAll, decodeClean, tyValsRaw, rawVal, tagOf, Tag.val, reduceCtorEq, ↓reduceIte]
      by_cases h1 : args[idx] ≤ 1
      · simp only [h1, decide_true, Bool.true_and, ↓reduceIte]
        by_cases hc : decodeCleanAll (List.map Prod.snd ps) (List.drop (idx + 1) args) = true <;>
          simp [hc]
      · simp only [h1, decide_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
    · simp only [ABI.decodeArgsAux?, ABI.decodeValueAt?, ABI.Ty.abiDecodeFuel,
        ABI.decodeValueAtWithFuel?, ABI.wordBytes, hr, ABI.abiArgOpt,
        headWords_word (Or.inr (Or.inr (Or.inr (Or.inl rfl)))), bind, Except.bind, pure,
        Except.pure, ih, List.map_cons, decodeCleanAll, decodeClean, Bool.true_and, tyValsRaw, rawVal, tagOf,
        Tag.val, reduceCtorEq, ↓reduceIte]
      by_cases hc : decodeCleanAll (List.map Prod.snd ps) (List.drop (idx + 1) args) = true <;>
        simp [hc]
    · have hd : ABI.decodeValueAt? lazy (Dirty.argBytes args) idx (.fixedBytes 32) =
          .ok (.fixedBytes 32 args[idx]) := Abi.decode_bytes32 args hargs hi 0 lazy
      simp only [ABI.decodeArgsAux?, hd, ABI.abiArgOpt,
        headWords_word (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))), bind, Except.bind, pure,
        Except.pure, ih, List.map_cons, decodeCleanAll, decodeClean, Bool.true_and, tyValsRaw, rawVal, tagOf,
        Tag.val, reduceCtorEq, ↓reduceIte]
      by_cases hc : decodeCleanAll (List.map Prod.snd ps) (List.drop (idx + 1) args) = true <;>
        simp [hc]

    · have hd : ABI.decodeValueAt? lazy (Dirty.argBytes args) idx (.tuple [.uint256]) =
          .ok (.tuple [.word args[idx]]) := decode_tuple1 args hargs hi lazy
      simp only [ABI.decodeArgsAux?, hd, ABI.abiArgOpt,
        headWords_word (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))), bind, Except.bind, pure,
        Except.pure, ih, List.map_cons, decodeCleanAll, decodeClean, Bool.true_and, tyValsRaw,
        rawVal, tagOf, ↓reduceIte]
      by_cases hc : decodeCleanAll (List.map Prod.snd ps) (List.drop (idx + 1) args) = true <;>
        simp [hc]

theorem accepts_int256 (a : Nat) (ha : a < wordSize) : AbiCleanup.accepts (.int 256) (.int a) = true := by
  have hn : SolidCore.Solidity.Shared.norm a = a := norm_lt ha
  simp only [AbiCleanup.accepts, hn, show (0 < 256 && 256 ≤ 256) = true from rfl, ↓reduceIte,
    Nat.mod_eq_of_lt ha, wordEq, Nat.sub_self, show SolidCore.Solidity.Shared.wordModulus = 2 ^ 256 from rfl]
  have h0 : wordModulus -
      115792089237316195423570985008687907853269984665640564039457584007913129639936 = 0 := rfl
  have h1 : (wordModulus -
      115792089237316195423570985008687907853269984665640564039457584007913129639936 + a) %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 = a := by
    rw [h0, Nat.zero_add]; exact Nat.mod_eq_of_lt ha
  split <;> simp [SolidCore.Solidity.Shared.norm, Nat.mod_eq_of_lt ha, Nat.zero_add, h1,
    show SolidCore.Solidity.Shared.wordModulus = 2 ^ 256 from rfl]

/-- The full-width bound of a word argument, which the generated modules write as a numeral,
passes every word below `2 ^ 256`. -/
theorem argOk_max (a : Nat) :
    argOk 115792089237316195423570985008687907853269984665640564039457584007913129639935 a =
      decide (a ≤ 115792089237316195423570985008687907853269984665640564039457584007913129639935) :=
  argOk_lt a (by decide)

theorem argsClean_cons (w : Nat) (ws : List Nat) (a : Nat) (as : List Nat) :
    argsClean (w :: ws) (a :: as) = (argOk w a && argsClean ws as) := rfl

theorem accepts_intb (a b : Nat) (ha : a < wordSize) (hb : 0 < b ∧ b < 256) :
    AbiCleanup.accepts (.int b) (.int a) = decide (sextNat b a = a) := by
  have hn : SolidCore.Solidity.Shared.norm a = a := norm_lt ha
  have hb' : (0 < b && b ≤ 256) = true := by simp; omega
  obtain ⟨hP, hPW, -, hh⟩ := pow_facts hb
  have hy := Nat.mod_lt a (Nat.two_pow_pos b)
  have hWM : SolidCore.Solidity.Source.wordModulus = wordSize := rfl
  have hWM' : SolidCore.Solidity.Shared.wordModulus = wordSize := rfl
  simp only [AbiCleanup.accepts, hn, hb', ↓reduceIte, wordEq, hWM, hWM']
  unfold sextNat
  generalize 2 ^ (b - 1) = h at *
  generalize 2 ^ b = P at *
  by_cases hc : h ≤ a % P
  · have h1 : wordSize - P + a % P < wordSize := by
      have := Nat.add_lt_add_left hy (wordSize - P)
      rwa [Nat.sub_add_cancel (Nat.le_of_lt hPW)] at this
    have h2 : SolidCore.Solidity.Shared.norm (wordSize - P + a % P) = a % P + (wordSize - P) := by
      rw [norm_lt h1, Nat.add_comm]
    have h3 : SolidCore.Solidity.Shared.norm (a % P + (wordSize - P)) = a % P + (wordSize - P) := by
      rw [Nat.add_comm]; exact norm_lt h1
    simp only [hc, ↓reduceIte, h2, h3]
    by_cases e : a % P + (wordSize - P) = a <;> simp [e, hn]
  · have h2 := norm_lt (Nat.lt_trans hy hPW)
    simp only [hc, ↓reduceIte, h2]
    by_cases e : a % P = a <;> simp [e, hn]

theorem lazyParamValues_vals : ∀ (ps : List BindingDecl) (cs : List AbiCleanup) (ws : List Nat)
    (args : List Nat), widthsOfT ps cs = some ws → args.length = ps.length →
    (∀ a ∈ args, a < wordSize) →
    AbiCleanups.lazyParamValues cs (tyValsRaw (ps.map BindingDecl.ty) args) =
      if cleanupsClean cs args then some (tyVals (ps.map BindingDecl.ty) args) else none
  | [], [], _, [], _, _, _ => rfl
  | p :: ps, c :: cs, ws, a :: args, hw, hl, ha => by
    simp only [widthsOfT, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hw
    obtain ⟨w, hw1, ws', hws', rfl⟩ := hw
    have ih := lazyParamValues_vals ps cs ws' args hws' (by simpa using hl)
      (fun b hb => ha b (List.mem_cons_of_mem _ hb))
    have hlt := ha a List.mem_cons_self
    obtain ⟨-, hk⟩ := paramWidth_spec hw1
    rcases hk with ⟨hm, hk⟩ | ⟨ht, b, rfl, hb0, hb, -⟩
    swap
    · have hbb : 0 < b ∧ b < 256 := ⟨hb0, hb⟩
      simp only [List.map_cons, tyVals, tyValsRaw, rawVal, ht, tagOf, Tag.val, reduceCtorEq, ↓reduceIte, AbiCleanups.lazyParamValues, ih,
        AbiCleanup.lazyParamValue, cleanupsClean, cleanArg, hbb, and_self, ↓reduceIte, bind,
        Option.bind, accepts_intb a b hlt hbb]
      by_cases h : sextNat b a = a
      · by_cases hc : cleanupsClean cs args = true <;> simp [h, hc]
      · simp [h]
    rcases hk with ⟨ht, b, rfl, hb0, hb, -⟩ | ⟨ht, rfl⟩ | ⟨ht, rfl, -⟩ | ⟨ht, rfl, -⟩ |
        ⟨ht, rfl, -⟩ | ⟨ht, rfl, -⟩ | ⟨ht, rfl, -⟩
    · by_cases h : a < 2 ^ b
      · simp only [List.map_cons, tyVals, tyValsRaw, rawVal, ht, tagOf, Tag.val, reduceCtorEq, ↓reduceIte, AbiCleanups.lazyParamValues, ih,
          cleanupsClean, cleanArg, h, decide_true, Bool.true_and]
        by_cases hc : cleanupsClean cs args = true <;>
          simp [AbiCleanup.lazyParamValue, AbiCleanup.accepts, norm_lt hlt, h, hb0, hb, bind,
            Option.bind, hc]
      · simp [List.map_cons, tyVals, tyValsRaw, rawVal, ht, tagOf, Tag.val, reduceCtorEq, ↓reduceIte, AbiCleanups.lazyParamValues,
          AbiCleanup.lazyParamValue, AbiCleanup.accepts, norm_lt hlt, h, hb0, hb, bind,
          Option.bind, cleanupsClean, cleanArg]
    · by_cases h : a ≤ w
      · simp only [List.map_cons, tyVals, tyValsRaw, rawVal, ht, tagOf, Tag.val, reduceCtorEq, ↓reduceIte, AbiCleanups.lazyParamValues, ih,
          cleanupsClean, cleanArg, h, decide_true, Bool.true_and]
        by_cases hc : cleanupsClean cs args = true <;>
          simp [AbiCleanup.lazyParamValue, AbiCleanup.accepts, norm_lt hlt, norm_lt hm, h, bind,
            Option.bind, hc]
      · simp [List.map_cons, tyVals, tyValsRaw, rawVal, ht, tagOf, Tag.val, reduceCtorEq, ↓reduceIte, AbiCleanups.lazyParamValues,
          AbiCleanup.lazyParamValue, AbiCleanup.accepts, norm_lt hlt, norm_lt hm, h, bind,
          Option.bind, cleanupsClean, cleanArg]
    all_goals first
      | (simp only [List.map_cons, tyVals, tyValsRaw, rawVal, ht, tagOf, Tag.val, reduceCtorEq,
          ↓reduceIte, AbiCleanups.lazyParamValues, ih, AbiCleanup.lazyParamValue, cleanupsClean, cleanArg,
          Bool.true_and, bind, Option.bind, accepts_int256 a hlt]
         by_cases hc : cleanupsClean cs args = true <;> simp [hc]
         done)
      | (simp only [List.map_cons, tyVals, tyValsRaw, rawVal, ht, tagOf, Tag.val, ↓reduceIte,
          AbiCleanups.lazyParamValues, ih, AbiCleanup.lazyParamValue, AbiCleanups.lazyValues,
          AbiCleanup.lazyValue, cleanupsClean, cleanArg, Bool.true_and, bind, Option.bind]
         by_cases hc : cleanupsClean cs args = true <;> simp [hc])
  | [], _ :: _, _, _, hw, _, _ | _ :: _, [], _, _, hw, _, _ => by simp [widthsOfT] at hw
  | [], [], _, _ :: _, _, hl, _ | _ :: _, _ :: _, _, [], _, hl, _ => by simp at hl

theorem argsClean_widths : ∀ {ps : List BindingDecl} {cs : List AbiCleanup} {ws : List Nat}
    (args : List Nat), widthsOfT ps cs = some ws → args.length = ps.length → (∀ a ∈ args, a < wordSize) →
    argsClean ws args = (decodeCleanAll (ps.map BindingDecl.ty) args && cleanupsClean cs args)
  | [], [], ws, [], h, _, _ => by
    simp only [widthsOfT, Option.some.injEq] at h
    subst h
    rfl
  | p :: ps, c :: cs, ws, a :: args, h, hl, ha => by
    simp only [widthsOfT, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨w, hw, ws', hws', rfl⟩ := h
    have ih := argsClean_widths args hws' (by simpa using hl)
      (fun b hb => ha b (List.mem_cons_of_mem _ hb))
    have hlt : a < wordSize := ha a List.mem_cons_self
    obtain ⟨-, hk⟩ := paramWidth_spec hw
    simp only [argsClean_cons, ih, List.map_cons, decodeCleanAll, cleanupsClean]
    have key : argOk w a = (decodeClean p.ty a && cleanArg c a) := by
      rcases hk with ⟨hwlt, hk⟩ | ⟨ht, b, rfl, hb0, hb, rfl⟩
      swap
      · simp [argOk_sext a b ⟨hb0, hb⟩, ht, decodeClean, cleanArg, hb0, hb]
      rw [argOk_lt a hwlt]
      rcases hk with ⟨ht, b, rfl, hb0, -, rfl⟩ | ⟨ht, rfl⟩ | ⟨ht, rfl, rfl⟩ | ⟨ht, rfl, rfl⟩ |
          ⟨ht, rfl, rfl⟩ | ⟨ht, rfl, rfl⟩ | ⟨ht, rfl, rfl⟩
      · have := Nat.two_pow_pos b
        simp only [ht, decodeClean, cleanArg, Bool.true_and]
        exact decide_eq_decide.mpr (by omega)
      · simp [ht, decodeClean, cleanArg]
      · have : (0 : Nat) < 2 ^ 160 := Nat.two_pow_pos _
        simp only [ht, decodeClean, cleanArg, Bool.and_true]
        exact decide_eq_decide.mpr (by omega)
      · simp [ht, decodeClean, cleanArg]
      · simp only [ht, decodeClean, cleanArg, Bool.and_true]
        exact decide_eq_true (Nat.le_sub_one_of_lt hlt)
      · simp only [ht, decodeClean, cleanArg, Bool.and_true]
        exact decide_eq_true (Nat.le_sub_one_of_lt hlt)
      · simp only [ht, decodeClean, cleanArg, Bool.and_true]
        exact decide_eq_true (Nat.le_sub_one_of_lt hlt)
    rw [key]
    cases decodeClean p.ty a <;> cases cleanArg c a <;>
      cases decodeCleanAll (ps.map BindingDecl.ty) args <;> cases cleanupsClean cs args <;> rfl
  | [], [], _, _ :: _, _, hl, _ | _ :: _, _ :: _, _, [], _, hl, _ => by simp at hl
  | [], _ :: _, _, _, h, _, _ | _ :: _, [], _, _, h, _, _ => by simp [widthsOfT] at h

/-- **SolidCore decodes the argument words of a function of the fragment** to themselves when
each is at most its parameter's bound, and otherwise reverts with empty data. -/
theorem decode_argsT {fn : FunctionDef} {ws : List Nat}
    (hw : widthsOfT fn.params fn.paramAbiCleanups = some ws) (args : List Nat)
    (hlen : args.length = fn.params.length) (hargs : ∀ a ∈ args, a < wordSize) :
    ABI.decodeFunctionArgs? fn (Dirty.argBytes args) =
      if argsClean ws args then .ok (tyVals (fn.params.map BindingDecl.ty) args) else .error .empty := by
  obtain ⟨hcl, -, hp, hc, -⟩ := widthsOf_spec hw
  have hflags : (fn.paramAbiCleanups.length == (fn.params.map BindingDecl.ty).length) = true := by
    simp [hcl]
  have hps : ∀ p ∈ (fn.paramAbiCleanups.map ABI.AbiCleanup.decodeLazy).zip
      (fn.params.map BindingDecl.ty), ParamTy p.2 := by
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
  rw [argsClean_widths args hw hlen hargs]
  unfold ABI.decodeFunctionArgs? ABI.decodeArgsWith?
  simp only [hflags, ↓reduceIte, hsnd, hhw, ABI.abiArgOpt, Dirty.length_argBytes,
    ABI.wordBytes, Nat.lt_irrefl, bind, Except.bind, pure, Except.pure, hdec]
  by_cases hd : decodeCleanAll (fn.params.map BindingDecl.ty) args = true
  · simp only [hd, ↓reduceIte, Bool.true_and]
    rw [lazyParamValues_vals fn.params _ ws args hw hlen hargs]
    split
    · rename_i hnil
      have : args = [] := by
        rw [List.isEmpty_iff] at hnil
        rw [hnil] at hcl
        simp at hcl
        exact List.eq_nil_of_length_eq_zero (by omega)
      subst this
      have h1 : ∀ tys, tyValsRaw tys [] = [] := fun tys => by cases tys <;> rfl
      have h2 : ∀ tys, tyVals tys [] = [] := fun tys => by cases tys <;> rfl
      cases fn.paramAbiCleanups <;> simp [h1, h2, cleanupsClean]
    · by_cases hcc : cleanupsClean fn.paramAbiCleanups args = true <;> simp [hcc]
  · simp only [hd, Bool.false_eq_true, ↓reduceIte, Bool.false_and]

/-- **SolidCore decodes the argument words of a function whose parameters are all words** to
themselves when each is at most its parameter's bound, and otherwise reverts with empty data. -/
theorem decode_args {fn : FunctionDef} {ws : List Nat}
    (hw : widthsOf fn.params fn.paramAbiCleanups = some ws) (args : List Nat)
    (hlen : args.length = fn.params.length) (hargs : ∀ a ∈ args, a < wordSize) :
    ABI.decodeFunctionArgs? fn (Dirty.argBytes args) =
      if argsClean ws args then .ok (args.map .word) else .error .empty := by
  rw [decode_argsT (widthsOf_T hw).1 args hlen hargs, tyVals_params hw hlen]

/-! ## The frame a call starts with -/

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

theorem coerce_param_clean {ty : Source.Ty} (h : ParamTy ty) {v : Nat} (hv : decodeClean ty v = true)
    (hlt : v < wordSize) : ty.coerceValue? (argVal ty v) = some ((tagOf ty).val v) := by
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl
  · rfl
  · rfl
  · simp only [decodeClean, decide_eq_true_eq] at hv
    have h' : v = 0 ∨ v = 1 := by omega
    rcases h' with rfl | rfl <;> rfl
  · rfl
  · rfl
  · simp [argVal, tagOf, Tag.val, Source.Ty.coerceValue?, Source.Ty.coerceTupleValues?]

/-- SolidCore coerces a parameter's decoded value as it coerces its word. -/
theorem coerce_tyVal {ty : Source.Ty} (h : ParamTy ty) {v : Nat} (hlt : v < wordSize) :
    ty.coerceValue? ((tagOf ty).val v) = ty.coerceValue? (argVal ty v) := by
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · simp [argVal, tagOf, Tag.val, Source.Ty.coerceValue?, normWord, SolidCore.Solidity.Shared.norm,
      Nat.mod_eq_of_lt hlt, show SolidCore.Solidity.Shared.wordModulus = wordSize from rfl]
  · rfl

/-- The parameters bind their decoded values as they bind their words. -/
theorem bindArgs_tyVals : ∀ (ps : List BindingDecl) (as : List Nat),
    (∀ p ∈ ps, ParamTy p.ty ∧ p.isStorageRef = false) → (∀ a ∈ as, a < wordSize) →
    as.length = ps.length →
    BindingDecl.bindArgs? ps (tyVals (ps.map BindingDecl.ty) as) =
      BindingDecl.bindArgs? ps (argVals (ps.map BindingDecl.ty) as)
  | [], [], _, _, _ => rfl
  | [], _ :: _, _, _, hl | _ :: _, [], _, _, hl => by simp at hl
  | p :: ps, a :: as, hp, ha, hl => by
    have ih := bindArgs_tyVals ps as (fun q hq => hp q (List.mem_cons_of_mem _ hq))
      (fun b hb => ha b (List.mem_cons_of_mem _ hb)) (by simpa using hl)
    simp only [List.map_cons, tyVals, argVals, BindingDecl.bindArgs?, BindingDecl.bindArg?,
      coerce_tyVal (hp p List.mem_cons_self).1 (ha a List.mem_cons_self), ih]

/-- A call of a function of the fragment on its decoded values runs as on its argument words. -/
theorem call_tyVals {fn : FunctionDef} {ws : List Nat}
    (hw : widthsOfT fn.params fn.paramAbiCleanups = some ws) {args : List Nat}
    (hlen : args.length = fn.params.length) (hargs : ∀ a ∈ args, a < wordSize) (fuel : Nat)
    (tbl : FunctionTable) (ctx : Context) (st0 : Source.State) :
    fn.call fuel tbl ctx st0 (tyVals (fn.params.map BindingDecl.ty) args) =
      fn.call fuel tbl ctx st0 (argVals (fn.params.map BindingDecl.ty) args) := by
  simp only [FunctionDef.call, FunctionDef.evalBodyEntry, FunctionDef.initialFrame?,
    bindArgs_tyVals fn.params args (widthsOf_spec hw).2.2.1 hargs hlen]

/-- A scope whose every local is a word shows as words. -/
theorem frameOfT_words (ρ : Val) (T : Tags) : ∀ (L : Locals), (∀ p ∈ L, T.get p.1 = .word) →
    frameOfT ρ T L = frameOf ρ L
  | [], _ => rfl
  | p :: L, h => by
    simp only [frameOfT, frameOf, List.map_cons, h p List.mem_cons_self, Tag.val_word]
    have := frameOfT_words ρ T L (fun q hq => h q (List.mem_cons_of_mem _ hq))
    simp only [frameOfT, frameOf] at this
    rw [this]

theorem tagsOk_spec {fn : FunctionDef} (h : tagsOk fn = true) :
    (∀ p ∈ fn.params, (fnTags fn).get p.name = tagOf p.ty) ∧
      (∀ r ∈ fn.returns, (fnTags fn).get r.name = tagOf r.ty) := by
  simp only [tagsOk, List.all_eq_true, beq_iff_eq] at h
  exact ⟨fun p hp => h p (List.mem_append_left _ hp), fun r hr => h r (List.mem_append_right _ hr)⟩

/-- **The parameters bind to the argument words, as `paramLocals` says**, each by its type's tag,
on argument words each at most its parameter's bound (a `bool` word is 0 or 1). -/
theorem bindArgs_clean (ρ : Val) (hρ : ∀ a ∈ ρ.args, a < wordSize) (T : Tags) :
    ∀ (ps : List BindingDecl) (cs : List AbiCleanup) (ws : List Nat) (i : Nat),
      widthsOfT ps cs = some ws → argsClean ws (ρ.args.drop i) = true →
      i + ps.length = ρ.args.length → (∀ p ∈ ps, T.get p.name = tagOf p.ty) →
      BindingDecl.bindArgs? ps (argVals (ps.map BindingDecl.ty) (ρ.args.drop i)) =
        some (frameOfT ρ T (paramLocals ps i))
  | [], _, _, i, _, _, h, _ => by
    simp only [List.length_nil, Nat.add_zero] at h
    subst h
    simp [BindingDecl.bindArgs?, paramLocals, frameOfT, argVals]
  | p :: ps, c :: cs, ws, i, hw, hcl, h, hT => by
    simp only [widthsOfT, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hw
    obtain ⟨w, hw1, ws', hws', rfl⟩ := hw
    have hi : i < ρ.args.length := by simp at h; omega
    have hlt := hρ _ (List.getElem_mem hi)
    have hdi : ρ.args.drop i = ρ.args[i] :: ρ.args.drop (i + 1) := List.drop_eq_getElem_cons hi
    rw [hdi] at hcl
    simp only [argsClean_cons, Bool.and_eq_true] at hcl
    have ih := bindArgs_clean ρ hρ T ps cs ws' (i + 1) hws' hcl.2 (by simp at h; omega)
      (fun q hq => hT q (List.mem_cons_of_mem _ hq))
    obtain ⟨hs, hk⟩ := paramWidth_spec hw1
    have hty : ParamTy p.ty := paramWidth_ty hw1
    have hdc : decodeClean p.ty ρ.args[i] = true := by
      rcases hk with ⟨hwlt, hk⟩ | ⟨ht, -⟩
      swap
      · simp [ht, decodeClean]
      have hcl1 := hcl.1
      rw [argOk_lt _ hwlt, decide_eq_true_eq] at hcl1
      rcases hk with ⟨ht, -⟩ | ⟨ht, -⟩ | ⟨ht, -, rfl⟩ | ⟨ht, -, rfl⟩ | ⟨ht, -⟩ | ⟨ht, -⟩ | ⟨ht, -⟩
      · simp [ht, decodeClean]
      · simp [ht, decodeClean]
      · simp only [ht, decodeClean, decide_eq_true_eq]
        exact Nat.lt_of_le_of_lt hcl1 (by decide)
      · simpa [ht, decodeClean] using hcl1
      · simp [ht, decodeClean]
      · simp [ht, decodeClean]
      · simp [ht, decodeClean]
    rw [hdi]
    simp only [List.map_cons, argVals, BindingDecl.bindArgs?, BindingDecl.bindArg?,
      coerce_param_clean hty hdc hlt, ih,
      bind, Option.bind, paramLocals, frameOfT, List.map_cons, WExpr.eval, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem hi, Option.getD_some, Nat.mod_eq_of_lt hlt, hT p List.mem_cons_self]
  | _ :: _, [], _, _, hw, _, _, _ => by simp [widthsOfT] at hw

/-- A return the fragment encodes: a `uint256`, `address` or `bool`. -/
abbrev RetTy (ty : Source.Ty) : Prop := ty = .uint256 ∨ ty = .address ∨ ty = .bool

theorem retBinding_ty {b : BindingDecl} (h : retBinding b = true) :
    (RetTy b.ty ∨ b.ty = .int256 ∨ b.ty = .fixedBytes 32) ∧ b.isStorageRef = false := by
  unfold retBinding at h
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
  refine ⟨?_, h.2⟩
  have := h.1
  split at this
  · rename_i h'; exact .inl (.inl h')
  · rename_i h'; exact .inl (.inr (.inl h'))
  · rename_i h'; exact .inl (.inr (.inr h'))
  · rename_i h'; exact .inr (.inl h')
  · rename_i h'; exact .inr (.inr h')
  · simp at this

/-- The returns start at zero, each by its type's tag. -/
theorem defaults_typed (ρ : Val) (T : Tags) (rs : List BindingDecl)
    (hrs : ∀ r ∈ rs, retBinding r = true) (hT : ∀ r ∈ rs, T.get r.name = tagOf r.ty) :
    rs.map BindingDecl.defaultBinding = frameOfT ρ T (rs.map fun r => (r.name, WExpr.lit 0)) := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    have h := retBinding_ty (hrs r List.mem_cons_self)
    have ht := hT r List.mem_cons_self
    simp only [List.map_cons, frameOfT] at ih ⊢
    rw [ih (fun q hq => hrs q (List.mem_cons_of_mem _ hq)) (fun q hq => hT q (List.mem_cons_of_mem _ hq)), ht]
    rcases h.1 with (h1 | h1 | h1) | h1 | h1 <;>
    simp [BindingDecl.defaultBinding, h1, h.2, Source.Ty.defaultValue, WExpr.eval, tagOf, Tag.val]

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

theorem collect_words (ρ : Val) (rt : Runtime) (S : SymState) {K : Facts} (hK : K.Hold ρ)
    (hl : ∀ x e, S.word? x = some e → rt.lookupLocal? x = some (.word (e.eval ρ))) :
    ∀ (rs : List BindingDecl) (ws : List WExpr), retsOk K rs ws = true →
      rs.mapM (fun r => S.word? r.name) = some ws →
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
    simp [collectReturnBindings.collect, hl _ _ he, deref_word', (retOk_spec hK hrs.1).1, ih, bind,
      Except.bind, pure, Except.pure]

/-- A named return's lookup in a typed scope, by its tag. -/
theorem lookup_retW {ρ : Val} {rt : Runtime} {S : SymState}
    (hfr : rt.locals = S.scopes.map (frameOfT ρ S.tags)) {x : String} {e : WExpr}
    (he : S.retW? x = some e) : rt.lookupLocal? x = some ((S.tags.get x).val (e.eval ρ)) := by
  unfold SymState.retW? at he
  split at he
  · simp [Runtime.lookupLocal?, hfr, envT_lookup, he]
  · simp at he

theorem coerce_words (ρ : Val) (rt : Runtime) {K : Facts} (hK : K.Hold ρ) :
    ∀ (rs : List BindingDecl) (ws : List WExpr), retsOk K rs ws = true →
      coerceReturnBindings.coerce rt rs (ws.map fun e => .word (e.eval ρ)) =
        .ok (ws.map fun e => .word (e.eval ρ))
  | [], [], _ => rfl
  | r :: rs, e :: ws, hrs => by
    simp only [retsOk, Bool.and_eq_true] at hrs
    have ih := coerce_words ρ rt hK rs ws hrs.2
    simp only [List.map_cons] at ih ⊢
    simp [coerceReturnBindings.coerce, deref_word', (retOk_spec hK hrs.1).1, ih,
      bind, Except.bind, pure, Except.pure]
  | [], _ :: _, h | _ :: _, [], h => by simp [retsOk] at h

/-- The value SolidCore's ABI boundary returns for a word of tag `t`: a `bytes32` drops its width
(`Value.untagFixedBytes`), every other tag keeps its value. -/
def Tag.out : Tag → Nat → Value
  | .bytes32, v => .word v
  | t, v => t.val v

/-- SolidCore's returned values of the words `ws` past its ABI boundary, each by its tag. -/
def retValsO (ρ : Val) : List Tag → List WExpr → List Value
  | t :: ts, w :: ws => t.out (w.eval ρ) :: retValsO ρ ts ws
  | [], ws => ws.map fun e => Value.word (e.eval ρ)
  | _ :: _, [] => []

@[simp] theorem retValsO_nil (ρ : Val) (ws : List WExpr) :
    retValsO ρ [] ws = ws.map fun e => Value.word (e.eval ρ) := by
  cases ws <;> rfl

theorem retOkT_spec {ρ : Val} {K : Facts} (hK : K.Hold ρ) {ty : Source.Ty} {t : Tag} {w : WExpr}
    (h : retOkT K ty t w = true) :
    ty.coerceValue? (t.val (w.eval ρ)) = some (t.val (w.eval ρ)) ∧
      ABI.Ty.isDynamicAbi ty = false ∧ ABI.Ty.staticAbiHeadWords? ty = some 1 ∧
      ABI.encodeStaticValue? ty (t.out (w.eval ρ)) = some (ABI.encodeWord (w.eval ρ)) ∧
      (∀ rt : Runtime, rt.derefMemoryValueDeep (t.val (w.eval ρ)) = .ok (t.val (w.eval ρ))) ∧
      (t.val (w.eval ρ)).untagFixedBytes = t.out (w.eval ρ) := by
  cases t with
  | word =>
    obtain ⟨h1, h2, h3, h4⟩ := retOk_spec hK h
    exact ⟨h1, h2, h3, h4, fun rt => deref_word' rt _, by simp [Tag.val, Tag.out, Value.untagFixedBytes]⟩
  | int =>
    cases ty <;> simp [retOkT] at h
    refine ⟨rfl, rfl, rfl, rfl, fun rt => ?_, ?_⟩
    · simp [Tag.val, Runtime.derefMemoryValueDeep, Runtime.derefMemoryValueWithFuel]
    · simp [Tag.val, Tag.out, Value.untagFixedBytes]
  | bytes32 =>
    have hlt := w.eval_lt ρ
    obtain rfl : ty = .fixedBytes 32 := by
      simp only [retOkT] at h
      split at h
      · rfl
      · simp at h
    refine ⟨?_, rfl, rfl, ?_, fun rt => ?_, ?_⟩
    · simp [Tag.val, Source.Ty.coerceValue?, normWord, norm_lt hlt]
    · have hlt' : WExpr.eval ρ w <
          115792089237316195423570985008687907853269984665640564039457584007913129639936 := hlt
      simp [Tag.out, ABI.encodeStaticValue?, ABI.fixedBytesFits, ABI.encodeWord, ABI.wordBytes,
        norm_lt hlt, hlt']
    · simp [Tag.val, Runtime.derefMemoryValueDeep, Runtime.derefMemoryValueWithFuel]
    · simp [Tag.val, Tag.out, Value.untagFixedBytes]
  | sref _ => simp [retOkT] at h
  | sptr _ => simp [retOkT] at h
  | mref => simp [retOkT] at h
  | tup1 => simp [retOkT] at h

theorem retsOkT_length {K : Facts} : ∀ {rs : List BindingDecl} {ts : List Tag} {ws : List WExpr},
    retsOkT K rs ts ws = true → ws.length = rs.length
  | rs, [], ws, h => retsOk_length (by simpa [retsOkT] using h)
  | r :: rs, t :: ts, w :: ws, h => by
    simp only [retsOkT, Bool.and_eq_true] at h
    simp [retsOkT_length h.2]
  | [], _ :: _, _, h | _ :: _, _ :: _, [], h => by simp [retsOkT] at h

theorem coerce_vals (ρ : Val) (rt : Runtime) {K : Facts} (hK : K.Hold ρ) :
    ∀ (rs : List BindingDecl) (ts : List Tag) (ws : List WExpr), retsOkT K rs ts ws = true →
      coerceReturnBindings.coerce rt rs (retVals ρ ts ws) = .ok (retVals ρ ts ws)
  | rs, [], ws, h => by
    simp only [retVals_nil]
    exact coerce_words ρ rt hK rs ws (by simpa [retsOkT] using h)
  | r :: rs, t :: ts, w :: ws, h => by
    simp only [retsOkT, Bool.and_eq_true] at h
    have ih := coerce_vals ρ rt hK rs ts ws h.2
    obtain ⟨h1, -, -, -, h5, -⟩ := retOkT_spec hK h.1
    simp only [retVals] at ih ⊢
    simp [coerceReturnBindings.coerce, h5 rt, h1, ih, bind, Except.bind, pure, Except.pure]
  | [], _ :: _, _, h | _ :: _, _ :: _, [], h => by simp [retsOkT] at h

theorem untag_vals (ρ : Val) : ∀ (ts : List Tag) (ws : List WExpr) {K : Facts} {rs : List BindingDecl},
    K.Hold ρ → retsOkT K rs ts ws = true →
    (retVals ρ ts ws).map Value.untagFixedBytes = retValsO ρ ts ws
  | [], ws, _, _, _, _ => by simp [Value.untagFixedBytes]
  | t :: ts, w :: ws, K, r :: rs, hK, h => by
    simp only [retsOkT, Bool.and_eq_true] at h
    obtain ⟨-, -, -, -, -, h6⟩ := retOkT_spec hK h.1
    simp only [retVals, retValsO, List.map_cons, h6, untag_vals ρ ts ws hK h.2]
  | _ :: _, [], _, _, _, _ => rfl
  | _ :: _, _ :: _, _, [], _, h => by simp [retsOkT] at h

/-- SolidCore collects the named returns as their values by their tags. -/
theorem collect_vals (ρ : Val) (rt : Runtime) (S : SymState) {E : EraseEnv} {ctx : Context}
    {K : Facts} (hK : K.Hold ρ) (hrel : StmtRel ρ E ctx rt S) :
    ∀ (rs : List BindingDecl) (ws : List WExpr),
      retsOkT K rs (rs.map fun r => S.tags.get r.name) ws = true →
      rs.mapM (fun r => S.retW? r.name) = some ws →
      collectReturnBindings.collect rt rs = .ok (retVals ρ (rs.map fun r => S.tags.get r.name) ws)
  | [], ws, _, h => by
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h
    subst h; rfl
  | r :: rs, ws, hrs, h => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨e, he, ws', hws', rfl⟩ := h
    simp only [List.map_cons, retsOkT, Bool.and_eq_true] at hrs
    have ih := collect_vals ρ rt S hK hrel rs ws' hrs.2 hws'
    obtain ⟨h1, -, -, -, h5, -⟩ := retOkT_spec hK hrs.1
    simp [collectReturnBindings.collect, lookup_retW hrel.frames he, h5 rt, h1, ih, retVals, bind,
      Except.bind, pure, Except.pure]

/-! ## Encoding the output -/

theorem wordToBytesBE_eq : ∀ (n v : Nat),
    ABI.wordToBytesBE n v = (List.range n).map fun i => v / 256 ^ (n - 1 - i) % 256 :=
  bytesBE_eq_range _ (fun _ => rfl) fun _ _ => rfl

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

theorem encodeAux_vals (ρ : Val) {K : Facts} (hK : K.Hold ρ) :
    ∀ (rs : List BindingDecl) (ts : List Tag) (ws : List WExpr) (off : Nat), retsOkT K rs ts ws = true →
      ABI.encodeValuesAux? (rs.map BindingDecl.ty) (retValsO ρ ts ws) off =
        some ((ws.flatMap wordOBytes).map (OByte.eval ρ), [], off)
  | rs, [], ws, off, h => by
    simp only [retValsO_nil]
    exact encodeAux_words ρ hK rs ws off (by simpa [retsOkT] using h)
  | r :: rs, t :: ts, w :: ws, off, h => by
    simp only [retsOkT, Bool.and_eq_true] at h
    have ih := encodeAux_vals ρ hK rs ts ws off h.2
    obtain ⟨-, hd, -, he, -, -⟩ := retOkT_spec hK h.1
    simp only [retValsO, List.map_cons, ABI.encodeValuesAux?, hd, he, ih, Bool.false_eq_true, ↓reduceIte,
      List.flatMap_cons, List.map_append, encodeWord_eval]
  | [], _ :: _, _, _, h | _ :: _, _ :: _, [], _, h => by simp [retsOkT] at h

theorem headWords_vals (ρ : Val) {K : Facts} (hK : K.Hold ρ) :
    ∀ (rs : List BindingDecl) (ts : List Tag) (ws : List WExpr), retsOkT K rs ts ws = true →
      ABI.Ty.listAbiHeadWords? (rs.map BindingDecl.ty) = some rs.length
  | [], _, _, _ => rfl
  | r :: rs, [], ws, h => by
    cases ws with
    | nil => simp [retsOkT, retsOk] at h
    | cons w ws =>
      simp only [retsOkT, retsOk, Bool.and_eq_true] at h
      obtain ⟨-, hd, hw, -⟩ := retOk_spec (ρ := ρ) hK h.1
      have ih := headWords_vals ρ hK rs [] ws (by simpa [retsOkT] using h.2)
      simp [ABI.Ty.listAbiHeadWords?, ABI.Ty.abiHeadWords?, hd, hw, ih, Nat.add_comm]
  | r :: rs, t :: ts, ws, h => by
    cases ws with
    | nil => simp [retsOkT] at h
    | cons w ws =>
      simp only [retsOkT, Bool.and_eq_true] at h
      obtain ⟨-, hd, hw, -, -, -⟩ := retOkT_spec hK h.1
      have ih := headWords_vals ρ hK rs ts ws h.2
      simp [ABI.Ty.listAbiHeadWords?, ABI.Ty.abiHeadWords?, hd, hw, ih, Nat.add_comm]

theorem encode_vals (ρ : Val) {K : Facts} (hK : K.Hold ρ) (rs : List BindingDecl) (ts : List Tag)
    (ws : List WExpr) (hrs : retsOkT K rs ts ws = true) :
    ABI.encodeValues? (rs.map BindingDecl.ty) (retValsO ρ ts ws) =
      some ((ws.flatMap wordOBytes).map (OByte.eval ρ)) := by
  simp [ABI.encodeValues?, headWords_vals ρ hK rs ts ws hrs, encodeAux_vals ρ hK rs ts ws _ hrs, bind,
    Option.bind]

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

theorem slotValue_lt (σ : List (Nat × Nat)) (k : Nat) : slotValue σ k < wordSize :=
  Evm.Wide.slotValue_lt σ k

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

/-- Comparing a word with a bound `m` below `2 ^ 256`. -/
theorem eval_gt_bound (ρ : Val) (e : WExpr) {m : Nat} (hm : m < wordSize) :
    (WExpr.bin .gt e (.lit m)).eval ρ = if e.eval ρ ≤ m then 0 else 1 := by
  simp only [eval_bin, eval_lit, Nat.mod_eq_of_lt hm, BinOp.eval]
  by_cases h : e.eval ρ ≤ m
  · simp [show ¬ m < e.eval ρ by omega, h]
  · simp [show m < e.eval ρ by omega, h, Nat.mod_eq_of_lt (show 1 < wordSize by decide)]

/-- The argument words from `i` on are at most the bounds `w :: ws` when word `i` is at most `w`
and the words after it at most `ws`; a missing word reads as zero. -/
theorem argsClean_drop (ρ : Val) (hρ : ∀ a ∈ ρ.args, a < wordSize) (w : Nat) (ws : List Nat)
    (i : Nat) : argsClean (w :: ws) (ρ.args.drop i) =
      (argOk w ((WExpr.arg i).eval ρ) && argsClean ws (ρ.args.drop (i + 1))) := by
  cases hdrop : ρ.args.drop i with
  | nil =>
    have hge : ρ.args.length ≤ i := by simpa using hdrop
    have hd1 : ρ.args.drop (i + 1) = [] := by simp; omega
    have hws : argsClean ws [] = true := by cases ws <;> rfl
    simp [hd1, hws, argsClean, WExpr.eval, List.getD_eq_getElem?_getD, List.getElem?_eq_none hge,
      argOk_zero]
  | cons a as =>
    have hi : i < ρ.args.length := by
      have := congrArg List.length hdrop; simp at this; omega
    have ha : ρ.args[i] = a := by
      have := congrArg List.head? hdrop
      rwa [List.head?_drop, List.getElem?_eq_getElem hi, List.head?_cons, Option.some.injEq] at this
    have hd1 : ρ.args.drop (i + 1) = as := by
      rw [← List.drop_drop, hdrop]; rfl
    have halt : a < wordSize := ha ▸ hρ _ (List.getElem_mem hi)
    simp [argsClean_cons, hd1, WExpr.eval, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, ha,
      Nat.mod_eq_of_lt halt]

/-- The tree of a call with argument checks: their revert when an argument word is above its
bound, else the tree they guard. -/
theorem paramGuards_eval (ρ : Val) (t : Tree) (hρ : ∀ a ∈ ρ.args, a < wordSize) :
    ∀ (ws : List Nat) (i : Nat),
      (paramGuards ws i t).eval ρ =
        if argsClean ws (ρ.args.drop i) then t.eval ρ
        else { success := false, output := [], logs := [], store := ρ.store }
  | [], i => by simp [paramGuards, argsClean]
  | w :: ws, i => by
    rw [argsClean_drop ρ hρ, paramGuards]
    have ih := paramGuards_eval ρ t hρ ws (i + 1)
    split
    · rename_i hw
      simp only [Tree.eval, eval_gt_bound ρ _ (show w < wordSize by omega), ih,
        argOk_lt _ (show w < wordSize by omega)]
      by_cases h : (WExpr.arg i).eval ρ ≤ w <;> simp [h]
    · rename_i hw
      split
      · rename_i hb
        simp only [Tree.eval, ih, argOk_eq, show ¬ w < wordSize by omega, ↓reduceIte, hb, and_self]
        by_cases h : sextNat (w - wordSize) ((WExpr.arg i).eval ρ) = (WExpr.arg i).eval ρ
        · simp [h, (eval_sextGuard ρ hb (.arg i)).mpr h]
        · have h0 : ¬ (sextGuard (w - wordSize) (.arg i)).eval ρ = 0 :=
            fun h' => h ((eval_sextGuard ρ hb _).mp h')
          simp [h, h0]
      · rename_i hb
        have hok : argOk w ((WExpr.arg i).eval ρ) = true := by
          have := WExpr.eval_lt ρ (.arg i)
          rw [argOk_eq]
          split
          · simp; omega
          · simp [hb]
        simp [ih, hok]

/-- Past the argument checks, the facts they leave hold. -/
theorem argFacts_hold (ρ : Val) (hρ : ∀ a ∈ ρ.args, a < wordSize) :
    ∀ (ws : List Nat) (i : Nat), argsClean ws (ρ.args.drop i) = true → (argFacts ws i).Hold ρ
  | [], _, _ => by simp [argFacts, Facts.Hold]
  | w :: ws, i, h => by
    rw [argsClean_drop ρ hρ, Bool.and_eq_true] at h
    have ih := argFacts_hold ρ hρ ws (i + 1) h.2
    simp only [argFacts]
    split
    · rename_i hw
      refine Facts.Hold.cons ih ?_
      have h1 := h.1
      rw [argOk_lt _ (show w < wordSize by omega), decide_eq_true_eq] at h1
      simp [eval_gt_bound ρ _ (show w < wordSize by omega), h1]
    · exact ih

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

/-- A function of the loop routes: word parameters and word returns, all tagged as words. -/
theorem words_of_widths {fn : FunctionDef} {ws : List Nat}
    (hw : widthsOf fn.params fn.paramAbiCleanups = some ws) (hret : fn.returns.all wordBinding = true) :
    ∀ p ∈ fn.params ++ fn.returns, tagOf p.ty = .word := by
  intro p hp
  rcases List.mem_append.mp hp with hp | hp
  · exact (widthsOf_T hw).2 p hp
  · rcases (wordBinding_ty (List.all_eq_true.mp hret p hp)).1 with h | h | h <;> simp [h, tagOf]

theorem retBinding_of_word {fn : FunctionDef} (h : fn.returns.all wordBinding = true) :
    fn.returns.all retBinding = true := by
  rw [List.all_eq_true] at h ⊢
  intro r hr
  have := h r hr
  unfold wordBinding at this
  unfold retBinding
  revert this
  cases r.ty <;> simp

/-- The parameter widths of a function the erasure accepts. -/
theorem eraseFn_widths {E : EraseEnv} {fuel : Nat} {fn : FunctionDef} {T : Tree}
    (h : eraseFn E fuel fn = some T) : ∃ ws, widthsOfT fn.params fn.paramAbiCleanups = some ws := by
  unfold eraseFn at h
  split at h
  · simp at h
  · rename_i ws hw
    exact ⟨ws, hw⟩

/-- **The entry of a call on clean argument words**: from any base context, sender `a` and state
`st0` whose slots hold `slotValue σ` and which has no logs, a function of the fragment starts its
body from a runtime related to its first symbolic state with the caller `cw`, the sender's word,
and the call is the body's run turned into the call's result. -/
theorem call_entry {c : TypeCheck.CheckedContract} {fn : FunctionDef} {ws : List Nat}
    (hw : widthsOfT fn.params fn.paramAbiCleanups = some ws)
    (hret : fn.returns.all retBinding = true) (htags : tagsOk fn = true) (fuel : Nat)
    (base : Source.Context) (a : Nat)
    (bytes : List Nat) {st0 : Source.State} {σ : List (Nat × Nat)}
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
        st0 (argVals (fn.params.map BindingDecl.ty) args) =
        some (fn.callBodyResult st0 <$> Stmt.eval fuel c.core.table
          (ABI.Contract.callContextAtWithBase c.core base selfAddress a 0 bytes) rt fn.body) := by
  set ctx := ABI.Contract.callContextAtWithBase c.core base selfAddress a 0 bytes with hctx
  set ρ : Val := ⟨args, slotValue σ, solHash, rc⟩ with hρ
  have hr : ∀ r ∈ fn.returns, retBinding r = true := fun r hr => List.all_eq_true.mp hret r hr
  have htg := tagsOk_spec htags
  have hframe : fn.initialFrame? (argVals (fn.params.map BindingDecl.ty) args) =
      some (frameOfT ρ (fnTags fn)
        (paramLocals fn.params 0 ++ fn.returns.map fun r => (r.name, .lit 0))) := by
    have h0 : BindingDecl.bindArgs? fn.params (argVals (fn.params.map BindingDecl.ty) args) =
        some (frameOfT ρ (fnTags fn) (paramLocals fn.params 0)) :=
      bindArgs_clean ρ hargs (fnTags fn) fn.params fn.paramAbiCleanups ws 0 hw
        (by simpa [hρ] using hclean) (by simp [hρ, hlen]) htg.1
    have hd : fn.returns.map BindingDecl.defaultBinding =
        frameOfT ρ (fnTags fn) (fn.returns.map fun r => (r.name, WExpr.lit 0)) := by
      exact defaults_typed ρ (fnTags fn) fn.returns hr htg.2
    have happ : ∀ (A B : Locals), frameOfT ρ (fnTags fn) (A ++ B) =
        frameOfT ρ (fnTags fn) A ++ frameOfT ρ (fnTags fn) B := by
      intro A B; simp [frameOfT, List.map_append]
    simp only [FunctionDef.initialFrame?, h0, FunctionDef.returnDefaultBindings, ← hd, happ]
  have hacc : fn.acceptsValue ctx.value = true := by
    simp [hctx, ABI.Contract.callContextAtWithBase, SolidCore.Solidity.Shared.norm,
      FunctionDef.acceptsValue, wordEq]
  refine ⟨{ state := { st0 with
              selfBalance := SolidCore.Solidity.Shared.addWord
                (SolidCore.Solidity.Shared.Account.balanceAt ctx.accountBalances ctx.self) ctx.value
              worldMutatedSinceAdoption := true }
            locals := [frameOfT ρ (fnTags fn)
              (paramLocals fn.params 0 ++ fn.returns.map fun r => (r.name, .lit 0))] },
    { fields := rfl, events := rfl, checked := rfl, sender := hcw, hash := rfl,
      ok := slotValue_store σ, frames := rfl, facts := hK
      store := fun k _ => by
        simp only [State.loadSlot, StorageMap.lookup?, initState, Writes.store, hρ, ← hstore k,
          SolidCore.Solidity.Shared.norm, modulus_eq, Std.HashMap.get?_eq_getElem?]
        cases st0.storage[k % wordSize]? <;> rfl
      logs := by simp [hev, initState]
      mem := fun _ _ hl => by simp [initState] at hl
      next := fun k hk => by
        simp only [initState, Option.some.injEq] at hk
        subst hk
        rfl }, ?_⟩
  simp only [FunctionDef.call, FunctionDef.evalBodyEntry, hacc, hframe, if_true, Option.map_some]

/-- **A call on clean argument words shows its body's tree**: from any base context, sender and
state as in `call_entry`, a body that runs from every related runtime to the leaf of `b` the
call's words select makes the call a finished one, and the ABI dispatcher shows the tree `brTree`
makes of `b`. -/
theorem abi_clean {c : TypeCheck.CheckedContract} {sel : Nat} (hsel : sel < 2 ^ 32)
    {fn : FunctionDef} (hfind : c.core.findFunctionBySelector? sel = some fn) {ws : List Nat}
    (hw : widthsOfT fn.params fn.paramAbiCleanups = some ws)
    (hret : fn.returns.all retBinding = true) (fuel : Nat) (base : Source.Context) (a : Nat)
    {st0 : Source.State} {σ : List (Nat × Nat)}
    (hstore : ∀ k, (st0.storage[k % 2 ^ 256]?).getD 0 = slotValue σ k) (hev : st0.events = [])
    {K : Facts} {args : List Nat} {rc : Nat} (cw : WExpr)
    (hlen : args.length = fn.params.length) (hargs : ∀ a ∈ args, a < 2 ^ 256)
    (hK : K.Hold ⟨args, slotValue σ, solHash, rc⟩)
    (hcw : SolidCore.Solidity.Shared.norm a = cw.eval ⟨args, slotValue σ, solHash, rc⟩)
    (htags : tagsOk fn = true)
    (hdec : ABI.decodeFunctionArgs? fn (Dirty.argBytes args) =
      .ok (tyVals (fn.params.map BindingDecl.ty) args))
    {b : Br} {T : Tree} (hT : brTree fn K b = some T)
    (hb : ∀ rt, StmtRel ⟨args, slotValue σ, solHash, rc⟩ { envOf c.core with facts := K }
        (ABI.Contract.callContextAtWithBase c.core base selfAddress a 0
          ((EthLib.Base.natToBytes 4 sel).map (·.toNat) ++ Dirty.argBytes args)) rt
        { initState fn with caller := cw } →
      ∃ r, Stmt.eval fuel c.core.table (ABI.Contract.callContextAtWithBase c.core base selfAddress a 0
          ((EthLib.Base.natToBytes 4 sel).map (·.toNat) ++ Dirty.argBytes args)) rt fn.body =
          .done (.ok r) ∧
        LeafRel ⟨args, slotValue σ, solHash, rc⟩ { envOf c.core with facts := K }
          (ABI.Contract.callContextAtWithBase c.core base selfAddress a 0
            ((EthLib.Base.natToBytes 4 sel).map (·.toNat) ++ Dirty.argBytes args)) r
          (b.eval ⟨args, slotValue σ, solHash, rc⟩))
    (call : Call) (hcs : call.storage = σ) :
    (∃ R, fn.call fuel c.core.table (ABI.Contract.callContextAtWithBase c.core base selfAddress a 0
        ((EthLib.Base.natToBytes 4 sel).map (·.toNat) ++ Dirty.argBytes args)) st0 (argVals (fn.params.map BindingDecl.ty) args) =
        some (.done (.ok R))) ∧
      Option.map (Source.observe call) (ABI.Contract.callCalldataAtFromWithContext? fuel c.core base
        st0 selfAddress a 0 ((EthLib.Base.natToBytes 4 sel).map (·.toNat) ++ Dirty.argBytes args)) =
        some (T.eval ⟨args, slotValue σ, solHash, rc⟩).obs := by
  set ρ : Val := ⟨args, slotValue σ, solHash, rc⟩ with hρ
  have hρok : ρ.Ok := slotValue_store σ
  have hclean : argsClean ws args = true := by
    have hd := decode_argsT hw args hlen hargs
    rw [hdec] at hd
    by_contra hn
    rw [if_neg hn] at hd
    exact absurd hd (by simp)
  obtain ⟨rt, hrel, hcall⟩ := call_entry (c := c) hw hret htags fuel base a
    ((EthLib.Base.natToBytes 4 sel).map (·.toNat) ++ Dirty.argBytes args) hstore hev cw hlen hargs
    hclean hK hcw
  have hbind : BindingDecl.bindArgs? fn.params (tyVals (fn.params.map BindingDecl.ty) args) =
      BindingDecl.bindArgs? fn.params (argVals (fn.params.map BindingDecl.ty) args) :=
    bindArgs_tyVals fn.params args (widthsOf_spec hw).2.2.1 hargs hlen
  obtain ⟨r, hrun, hleaf⟩ := hb rt hrel
  rw [hrun] at hcall
  refine ⟨⟨_, hcall⟩, ?_⟩
  have hdrop : ((EthLib.Base.natToBytes 4 sel).map (·.toNat) ++ Dirty.argBytes args).drop
      ABI.selectorBytes = Dirty.argBytes args := by
    simp [ABI.selectorBytes, EthLib.Base.natToBytes_length]
  simp only [ABI.Contract.callCalldataAtFromWithContext?, Dirty.readSelector_calldata _ hsel, hfind,
    hdrop, hdec]
  have hacc : fn.acceptsValue 0 = true := by simp [FunctionDef.acceptsValue, wordEq]
  have hcall' : fn.call? fuel c.core.table (ABI.Contract.callContextAtWithBase c.core base
      selfAddress a 0 ((EthLib.Base.natToBytes 4 sel).map (·.toNat) ++ Dirty.argBytes args)) st0
      (argVals (fn.params.map BindingDecl.ty) args) = some (fn.callBodyResult st0 r) := by
    simp only [FunctionDef.call?, hcall]
    rfl
  have hcallT : fn.call? fuel c.core.table (ABI.Contract.callContextAtWithBase c.core base
      selfAddress a 0 ((EthLib.Base.natToBytes 4 sel).map (·.toNat) ++ Dirty.argBytes args)) st0
      (tyVals (fn.params.map BindingDecl.ty) args) = some (fn.callBodyResult st0 r) := by
    rw [← hcall']
    simp only [FunctionDef.call?, FunctionDef.call, FunctionDef.evalBodyEntry,
      FunctionDef.initialFrame?, hbind]
  obtain ⟨T', hT', hTe⟩ := brTree_eval fn K ρ b T hT
  rw [hacc, if_pos rfl, hcallT, ← hTe]
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
      some (T.eval ⟨args, slotValue σ, solHash, callerWord⟩).obs := by
  unfold eraseFn at hT
  split at hT
  · simp at hT
  rename_i ws hw
  split at hT
  case isFalse => simp at hT
  rename_i hret'
  obtain ⟨hret, htags⟩ := Bool.and_eq_true _ _ ▸ hret'
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hT
  obtain ⟨b, hb, t, ht, rfl⟩ := hT
  rw [paramGuards_eval ⟨args, slotValue σ, solHash, callerWord⟩ t hargs ws 0, List.drop_zero]
  have hdec := decode_argsT hw args hlen hargs
  by_cases hclean : argsClean ws args = true
  · rw [if_pos hclean]
    rw [if_pos hclean] at hdec
    rw [Wide.callAt_of_args sel args hargs σ, Wide.run_eq_at hd, Wide.map_ofNat_toNat args hargs]
    exact (abi_clean hsel hfind hw hret fuel _ callerAddress
      (st0 := { d with storage := σ.foldl (fun acc kv => acc.insertLoop kv.1 kv.2) d.storage })
      (getD_storage_cover hd hcov) hd.events
      (.lit callerWord) hlen hargs (argFacts_hold _ hargs ws 0 (by simpa using hclean)) rfl htags
      hdec ht (fun rt hrel => eval_stmt _ _ _ fuel fn.body _ b hb rt hrel) _ rfl).2
  · rw [if_neg hclean]
    rw [if_neg hclean] at hdec
    rw [run_rejected hd hsel hfind args hdec σ]
    rfl

end SolidCore.Refinement.Generic

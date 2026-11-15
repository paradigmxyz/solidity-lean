import SolidCore.Refinement.Dirty.Source
import SolidCore.Refinement.Dyn.Abi

/-!
# SolidCore rejects malformed call data

SolidCore's ABI decoder reads the call data after the selector as a list of byte
values. For a function whose parameters are the lowering of `Dyn.DParam`s
(`dfnShapeOk`: `bytes calldata` as `Ty.bytesCalldata`, `T[] calldata` as
`Ty.dynamicArray` of a word type, a struct as `Ty.tuple` of word types, a word as in
`Dirty.paramFits`), every decoding failure is the empty revert (`decode_error`), and
the decoder accepts no call data that `Malformed` describes:

* it first checks that the heads are present (`decodeArgsWith?`);
* a `bytes` argument reads its offset word `o`, its length word at `o`, and needs the
  `o + 32 + length` bytes; an array needs `o + 32 + 32 * length` (`tail_of_ok`).

`run_malformed` lifts it to `Source.run`: the call shows `Abi.rejected`.
-/

namespace SolidCore.Refinement.Dyn

open EthLib.Base EthLib.Execution.Evm SolidCore.Refinement.Abi
open SolidCore.Solidity SolidCore.Solidity.Source

/-! ## The shape of a function -/

/-- Whether SolidCore's parameter type `ty` and cleanup `c` are the lowering of `p`. -/
def dparamFits : DParam → Source.Ty → AbiCleanup → Bool
  | .word p, ty, c => Dirty.paramFits p ty c
  | .bytes _, .bytesCalldata, .none => true
  | .array p _, .dynamicArray ty, .dynamicArray c => Dirty.paramFits p ty c
  | .struct ps, .tuple tys, .tuple cs => Dirty.fitsAll ps tys cs
  | _, _, _ => false

/-- Whether the parameter types and cleanups of a function are the lowering of `ps`. -/
def dfitsAll : List DParam → List Source.Ty → List AbiCleanup → Bool
  | p :: ps, ty :: tys, c :: cs => dparamFits p ty c && dfitsAll ps tys cs
  | [], [], [] => true
  | _, _, _ => false

/-- Whether the checked contract dispatches the selector of `fn` to a function whose
parameters are the lowering of `fn`'s. -/
def dfnShapeOk (c : TypeCheck.CheckedContract) (fn : DFn) : Bool :=
  decide (fn.sel < 2 ^ 32) &&
    match c.core.findFunctionBySelector? fn.sel with
    | some f => dfitsAll fn.params (f.params.map BindingDecl.ty) f.paramAbiCleanups
    | none => false

/-! ## Reading words -/

/-- The call data after the selector, as SolidCore reads it. -/
def srcBytes (data : ByteArray) : List Nat := data.data.toList.map (·.toNat)

theorem length_srcBytes (data : ByteArray) : (srcBytes data).length = data.size := by
  simp only [srcBytes, List.length_map, Array.length_toList]
  rfl

/-- SolidCore reads big-endian bytes as EthLib does, modulo `2 ^ 256`. -/
theorem bytesToWordBE_map (l : List UInt8) :
    ABI.bytesToWordBE (ABI.normalizeBytes (l.map (·.toNat))) = bytesToNat l % 2 ^ 256 := by
  have hbyte : ∀ b : UInt8, normByte (Shared.External.byte b.toNat) = b.toNat := by
    intro b
    have := b.toNat_lt
    simp [normByte, Shared.Account.byte, Shared.External.byte, Nat.mod_eq_of_lt this]
  unfold ABI.bytesToWordBE ABI.normalizeBytes Shared.External.normalizeBytes
  rw [List.map_map, List.foldl_map]
  simp only [Function.comp_def, hbyte]
  rfl

theorem bufferRead_eq_take (data : ByteArray) (p n : Nat) (h : p + n ≤ data.size) :
    bufferRead data p n = (data.data.toList.drop p).take n := by
  have hs : data.data.toList.length = data.size := by
    simp only [Array.length_toList]; rfl
  apply List.ext_getElem
  · rw [bufferRead_length, List.length_take, List.length_drop]; omega
  · intro i h1 h2
    rw [bufferRead_length] at h1
    simp only [bufferRead, List.getElem_map, List.getElem_range, List.getElem_take,
      List.getElem_drop, byteAt]
    have : p + i < data.size := by omega
    rw [dif_pos this]
    rfl

/-- A word SolidCore reads is the word CALLDATALOAD reads, and lies within the call data. -/
theorem readWord_srcBytes {data : ByteArray} {p w : Nat}
    (h : ABI.readWord? (srcBytes data) p = some w) :
    p + 32 ≤ data.size ∧ w = wordAt data p := by
  simp only [ABI.readWord?, ABI.readBytes?] at h
  by_cases hle : ABI.wordBytes ≤ (List.drop p (srcBytes data)).length
  · rw [if_pos hle] at h
    simp only [Option.some.injEq] at h
    subst h
    have hl : p + 32 ≤ data.size := by
      rw [List.length_drop, length_srcBytes] at hle; simp only [ABI.wordBytes] at hle; omega
    refine ⟨hl, ?_⟩
    simp only [wordAt, loadWord, BitVec.toNat_ofNat, bufferRead_eq_take data p 32 hl]
    rw [← bytesToWordBE_map]
    simp only [srcBytes, List.map_take, List.map_drop, ABI.wordBytes]
  · rw [if_neg hle] at h
    simp at h

theorem readBytes_some {bs : List Nat} {p n : Nat} {v : ABI.Bytes}
    (h : ABI.readBytes? bs p n = some v) : n ≤ bs.length - p := by
  simp only [ABI.readBytes?] at h
  by_cases hle : n ≤ (List.drop p bs).length
  · rw [List.length_drop] at hle; exact hle
  · rw [if_neg hle] at h; simp at h

/-! ## Decoding one argument -/

open ABI in
theorem types_of_fits {p : Param} {ty : Source.Ty} {c : AbiCleanup}
    (h : Dirty.paramFits p ty c = true) :
    ty = .uint256 ∨ ty = .int256 ∨ ty = .bool := by
  unfold Dirty.paramFits at h
  split at h <;> simp_all

/-- A word argument fails to decode only with the empty revert. -/
theorem word_error {p : Param} {ty : Source.Ty} {c : AbiCleanup}
    (h : Dirty.paramFits p ty c = true) {lazy : Bool} {bs : List Nat} {idx : Nat}
    {e : RevertData} (he : ABI.decodeValueAt? lazy bs idx ty = .error e) : e = .empty := by
  rcases types_of_fits h with rfl | rfl | rfl <;>
    simp only [ABI.decodeValueAt?, ABI.Ty.abiDecodeFuel, ABI.decodeValueAtWithFuel?, bind,
      Except.bind, pure, Except.pure] at he <;>
    cases hr : ABI.readWord? bs (ABI.wordBytes * idx) <;>
    simp only [hr, ABI.abiArgOpt, Except.error.injEq, reduceCtorEq] at he
  · exact he.symm
  · exact he.symm
  · exact he.symm
  · split at he
    · simp at he
    · simpa using he.symm

/-- A `bytes calldata` argument decodes only when its tail lies within the call data, and
fails only with the empty revert. -/
theorem bytes_decode (data : ByteArray) (idx : Nat) :
    (∀ v, ABI.decodeValueAt? true (srcBytes data) idx .bytesCalldata = .ok v →
      ¬ TailPastEnd data (32 * idx) 1) ∧
    (∀ e, ABI.decodeValueAt? true (srcBytes data) idx .bytesCalldata = .error e → e = .empty) := by
  simp only [ABI.decodeValueAt?, ABI.Ty.abiDecodeFuel, ABI.decodeValueAtWithFuel?]
  cases h1 : ABI.readWord? (srcBytes data) (ABI.wordBytes * idx) with
  | none => simp [ABI.abiArgOpt, bind, Except.bind]
  | some o =>
    cases h2 : ABI.readWord? (srcBytes data) o with
    | none => simp [h2, ABI.abiArgOpt, bind, Except.bind]
    | some n =>
      cases h3 : ABI.readBytes? (srcBytes data) (o + ABI.wordBytes) n with
      | none => simp [h2, h3, ABI.abiArgOpt, bind, Except.bind, pure, Except.pure]
      | some bs =>
        obtain ⟨-, rfl⟩ := readWord_srcBytes h1
        obtain ⟨h5, rfl⟩ := readWord_srcBytes h2
        have h4 := readBytes_some h3
        rw [length_srcBytes] at h4
        refine ⟨fun _ _ => ?_, fun e he => by simp [h2, h3, ABI.abiArgOpt, bind, Except.bind, pure,
          Except.pure] at he⟩
        simp only [TailPastEnd, ABI.wordBytes] at h4 h5 ⊢
        omega

/-- Values decoded in a row fail only with the empty revert, when each one does. -/
theorem seq_error {f : Nat → Except RevertData Value} {step : Option Nat}
    (hf : ∀ i e, f i = .error e → e = .empty) :
    ∀ n i e, ABI.decodeValueSeq? f step n i = .error e → e = .empty
  | 0, i, e, h => by simp [ABI.decodeValueSeq?] at h
  | n + 1, i, e, h => by
    simp only [ABI.decodeValueSeq?, bind, Except.bind, pure, Except.pure] at h
    cases h1 : f i with
    | error e' => rw [h1] at h; simp at h; subst h; exact hf i e' h1
    | ok v =>
      rw [h1] at h
      cases step with
      | none => simp [ABI.abiArgOpt] at h; exact h.symm
      | some k =>
        simp only [ABI.abiArgOpt] at h
        cases h2 : ABI.decodeValueSeq? f (some k) n (i + k) with
        | error e' => rw [h2] at h; simp at h; subst h; exact seq_error hf n _ _ h2
        | ok vs => rw [h2] at h; simp at h

/-- A `T[] calldata` argument of a word type decodes only when its tail lies within the
call data, and fails only with the empty revert. -/
theorem array_decode {ty : Source.Ty} (hty : ty = .uint256 ∨ ty = .int256 ∨ ty = .bool)
    (data : ByteArray) (idx : Nat) :
    (∀ v, ABI.decodeValueAt? true (srcBytes data) idx (.dynamicArray ty) = .ok v →
      ¬ TailPastEnd data (32 * idx) 32) ∧
    (∀ e, ABI.decodeValueAt? true (srcBytes data) idx (.dynamicArray ty) = .error e →
      e = .empty) := by
  have hw : ABI.Ty.abiHeadWords? ty = some 1 := by
    rcases hty with rfl | rfl | rfl <;> rfl
  rcases hty with rfl | rfl | rfl <;>
  simp only [ABI.decodeValueAt?, ABI.Ty.abiDecodeFuel, ABI.decodeValueAtWithFuel?] <;>
  simp only [hw] at * <;>
  cases h1 : ABI.readWord? (srcBytes data) (ABI.wordBytes * idx) <;>
    simp [ABI.abiArgOpt, bind, Except.bind, pure, Except.pure]
  all_goals
    rename_i o
    cases h2 : ABI.readWord? (srcBytes data) o with
    | none => simp [h2]
    | some n =>
      obtain ⟨-, rfl⟩ := readWord_srcBytes h1
      obtain ⟨h5, rfl⟩ := readWord_srcBytes h2
      simp only [h2]
      by_cases hb : ABI.readBytes? (List.drop (wordAt data (ABI.wordBytes * idx) + ABI.wordBytes)
          (srcBytes data)) 0 (wordAt data (wordAt data (ABI.wordBytes * idx)) * ABI.wordBytes) = none
      · simp [hb]
      · simp only [hb, ite_false]
        obtain ⟨bs, hbs⟩ := Option.ne_none_iff_exists'.mp hb
        have h4 := readBytes_some hbs
        rw [List.length_drop, length_srcBytes] at h4
        refine ⟨fun _ _ => ?_, fun e he => ?_⟩
        · simp only [TailPastEnd, ABI.wordBytes] at h4 h5 ⊢
          omega
        · split at he
          · rename_i e' he'
            simp only [Except.error.injEq] at he
            subst he
            exact seq_error (fun i e h => by split at h <;> simp at h) _ _ _ he'
          · simp at he

/-- Values of a list of types decoded in a row fail only with the empty revert, when each
one does. -/
theorem list_error {f : Source.Ty → Nat → Except RevertData Value}
    (hf : ∀ ty i e, f ty i = .error e → e = .empty) :
    ∀ tys i e, ABI.decodeValueList? f tys i = .error e → e = .empty
  | [], i, e, h => by simp [ABI.decodeValueList?] at h
  | ty :: tys, i, e, h => by
    simp only [ABI.decodeValueList?, bind, Except.bind, pure, Except.pure] at h
    cases h1 : f ty i with
    | error e' => rw [h1] at h; simp at h; subst h; exact hf ty i e' h1
    | ok v =>
      rw [h1] at h
      simp only [ABI.abiArgOpt] at h
      cases hw : ABI.Ty.abiHeadWords? ty with
      | none => rw [hw] at h; simp at h; exact h.symm
      | some k =>
        rw [hw] at h
        simp only at h
        cases h2 : ABI.decodeValueList? f tys (i + k) with
        | error e' => rw [h2] at h; simp at h; subst h; exact list_error hf tys _ _ h2
        | ok vs => rw [h2] at h; simp at h

theorem listHeadWords_of_fitsAll' : ∀ {ps : List Param} {tys : List Source.Ty}
    {cs : List AbiCleanup}, Dirty.fitsAll ps tys cs = true →
    ABI.Ty.listHasDynamicAbi tys = false ∧ ABI.Ty.listStaticAbiHeadWords? tys = some ps.length
  | [], [], [], _ => ⟨rfl, rfl⟩
  | _ :: _, _ :: _, _ :: _, h => by
    simp only [Dirty.fitsAll, Bool.and_eq_true] at h
    have ih := listHeadWords_of_fitsAll' h.2
    rcases types_of_fits h.1 with rfl | rfl | rfl <;>
      simp [ABI.Ty.listHasDynamicAbi, ABI.Ty.isDynamicAbi, ABI.Ty.listStaticAbiHeadWords?,
        ABI.Ty.staticAbiHeadWords?, ih.1, ih.2, Nat.add_comm]
  | [], _ :: _, _, h | [], [], _ :: _, h | _ :: _, [], _, h | _ :: _, _ :: _, [], h => by
    simp [Dirty.fitsAll] at h

/-- A struct argument of word types fails only with the empty revert. -/
theorem struct_error {ps : List Param} {tys : List Source.Ty} {cs : List AbiCleanup}
    (h : Dirty.fitsAll ps tys cs = true) (bs : List Nat) (idx : Nat) (e : RevertData)
    (he : ABI.decodeValueAt? true bs idx (.tuple tys) = .error e) : e = .empty := by
  obtain ⟨hd, hw⟩ := listHeadWords_of_fitsAll' h
  have hw' : ABI.Ty.listAbiHeadWords? tys = some ps.length := by
    rw [Dirty.listHeadWords_of_fitsAll h, (Dirty.length_of_fitsAll h).1]
  simp only [ABI.decodeValueAt?, ABI.Ty.abiDecodeFuel, ABI.decodeValueAtWithFuel?, hd,
    hw', ABI.abiArgOpt, bind, Except.bind, Bool.false_eq_true, ite_false, Bool.true_and] at he
  split at he
  · simp at he; exact he.symm
  · split at he
    · rename_i e' he'
      simp only [Except.error.injEq] at he
      subst he
      exact list_error (fun ty i e h => by split at h <;> simp at h) _ _ _ he'
    · simp at he

theorem decodeLazy_of_fits {p : Param} {ty : Source.Ty} {c : AbiCleanup}
    (h : Dirty.paramFits p ty c = true) : ABI.AbiCleanup.decodeLazy c = true := by
  unfold Dirty.paramFits at h
  split at h <;> first | (simp at h; done) | rfl

/-- One argument of the shape: decoded on the calldata path, it takes its head words, it
decodes only when its tail lies within the call data, and it fails only with the empty
revert. -/
theorem param_decode {p : DParam} {ty : Source.Ty} {c : AbiCleanup}
    (h : dparamFits p ty c = true) (data : ByteArray) (idx : Nat) :
    ABI.AbiCleanup.decodeLazy c = true ∧ ABI.Ty.abiHeadWords? ty = some p.headWords ∧
    (∀ v, ABI.decodeValueAt? true (srcBytes data) idx ty = .ok v →
      ∀ k, p.stride? = some k → ¬ TailPastEnd data (32 * idx) k) ∧
    (∀ e, ABI.decodeValueAt? true (srcBytes data) idx ty = .error e → e = .empty) := by
  unfold dparamFits at h
  split at h
  · rename_i q ty c
    exact ⟨decodeLazy_of_fits h, Dirty.headWords_of_fits h, fun _ _ k hk => by
      simp [DParam.stride?] at hk, fun e he => word_error h he⟩
  · have hb := bytes_decode data idx
    refine ⟨rfl, rfl, fun v hv k hk => ?_, hb.2⟩
    simp only [DParam.stride?, Option.some.injEq] at hk
    subst hk
    exact hb.1 v hv
  · rename_i q n ty c
    have ha := array_decode (types_of_fits h) data idx
    refine ⟨rfl, rfl, fun v hv k hk => ?_, ha.2⟩
    simp only [DParam.stride?, Option.some.injEq] at hk
    subst hk
    exact ha.1 v hv
  · rename_i ps tys cs
    obtain ⟨hd, hw⟩ := listHeadWords_of_fitsAll' h
    refine ⟨rfl, ?_, fun _ _ k hk => by simp [DParam.stride?] at hk,
      fun e he => struct_error h _ _ e he⟩
    simp [ABI.Ty.abiHeadWords?, ABI.Ty.isDynamicAbi, ABI.Ty.staticAbiHeadWords?, hd, hw,
      DParam.headWords]
  · simp at h

/-! ## Decoding the argument list -/

theorem dfitsAll_cons {p : DParam} {ps : List DParam} {ty : Source.Ty} {tys : List Source.Ty}
    {c : AbiCleanup} {cs : List AbiCleanup} (h : dfitsAll (p :: ps) (ty :: tys) (c :: cs) = true) :
    dparamFits p ty c = true ∧ dfitsAll ps tys cs = true := by
  simpa [dfitsAll] using h

theorem lengths_of_dfitsAll : ∀ {ps : List DParam} {tys : List Source.Ty}
    {cs : List AbiCleanup}, dfitsAll ps tys cs = true →
    tys.length = ps.length ∧ cs.length = ps.length
  | [], [], [], _ => ⟨rfl, rfl⟩
  | _ :: _, _ :: _, _ :: _, h => by
    have := lengths_of_dfitsAll (dfitsAll_cons h).2
    simp [this.1, this.2]
  | [], _ :: _, _, h | [], [], _ :: _, h | _ :: _, [], _, h | _ :: _, _ :: _, [], h => by
    simp [dfitsAll] at h

theorem listHeadWords_of_dfitsAll : ∀ {ps : List DParam} {tys : List Source.Ty}
    {cs : List AbiCleanup}, dfitsAll ps tys cs = true →
    ABI.Ty.listAbiHeadWords? tys = some (headWords ps)
  | [], [], [], _ => rfl
  | _ :: _, _ :: _, _ :: _, h => by
    have h1 := (param_decode (dfitsAll_cons h).1 .empty 0).2.1
    simp [ABI.Ty.listAbiHeadWords?, h1, listHeadWords_of_dfitsAll (dfitsAll_cons h).2, headWords]
  | [], _ :: _, _, h | [], [], _ :: _, h | _ :: _, [], _, h | _ :: _, _ :: _, [], h => by
    simp [dfitsAll] at h

theorem lazy_of_dfitsAll : ∀ {ps : List DParam} {tys : List Source.Ty}
    {cs : List AbiCleanup}, dfitsAll ps tys cs = true →
    cs.map ABI.AbiCleanup.decodeLazy = cs.map fun _ => true
  | [], [], [], _ => rfl
  | _ :: _, _ :: _, _ :: _, h => by
    have h1 := (param_decode (dfitsAll_cons h).1 .empty 0).1
    simp [h1, lazy_of_dfitsAll (dfitsAll_cons h).2]
  | [], _ :: _, _, h | [], [], _ :: _, h | _ :: _, [], _, h | _ :: _, _ :: _, [], h => by
    simp [dfitsAll] at h

/-- Under the shape, the decoder of the argument list fails only with the empty revert, and
decodes only when every dynamic argument's tail lies within the call data. -/
theorem aux_decode (data : ByteArray) : ∀ (ps : List DParam) (tys : List Source.Ty)
    (cs : List AbiCleanup) (idx : Nat), dfitsAll ps tys cs = true →
    (∀ vs, ABI.decodeArgsAux? (srcBytes data) ((cs.map fun _ => true).zip tys) idx = .ok vs →
      ∀ e ∈ dynHeads ps (32 * idx), ¬ TailPastEnd data e.1 e.2) ∧
    (∀ e, ABI.decodeArgsAux? (srcBytes data) ((cs.map fun _ => true).zip tys) idx = .error e →
      e = .empty)
  | [], [], [], _, _ => by simp [ABI.decodeArgsAux?, dynHeads]
  | p :: ps, ty :: tys, c :: cs, idx, h => by
    obtain ⟨h1, h2⟩ := dfitsAll_cons h
    obtain ⟨-, hw, hok, herr⟩ := param_decode h1 data idx
    have ih := aux_decode data ps tys cs (idx + p.headWords) h2
    simp only [List.map_cons, List.zip_cons_cons, ABI.decodeArgsAux?, bind, Except.bind, hw,
      ABI.abiArgOpt, pure, Except.pure]
    cases hv : ABI.decodeValueAt? true (srcBytes data) idx ty with
    | error e' => simp only; exact ⟨fun _ h => by simp at h, fun e he => by
        simp at he; subst he; exact herr e' hv⟩
    | ok v =>
      simp only
      cases hr : ABI.decodeArgsAux? (srcBytes data) ((cs.map fun _ => true).zip tys)
          (idx + p.headWords) with
      | error e' => simp only; exact ⟨fun _ h => by simp at h, fun e he => by
          simp at he; subst he; exact ih.2 e' hr⟩
      | ok vs =>
        simp only
        refine ⟨fun _ _ e he => ?_, fun e he => by simp at he⟩
        simp only [dynHeads, List.mem_append] at he
        rcases he with he | he
        · split at he
          · rename_i k hk
            simp only [List.mem_singleton] at he
            subst he
            exact hok v hv k hk
          · simp at he
        · rw [show 32 * idx + 32 * p.headWords = 32 * (idx + p.headWords) by omega] at he
          exact ih.1 vs hr e he
  | [], _ :: _, _, _, h | [], [], _ :: _, _, h | _ :: _, [], _, _, h
  | _ :: _, _ :: _, [], _, h => by simp [dfitsAll] at h

/-- A function of the shape decodes every malformed call data to the empty revert. -/
theorem decode_malformed (f : FunctionDef) (ps : List DParam)
    (hfit : dfitsAll ps (f.params.map BindingDecl.ty) f.paramAbiCleanups = true)
    (data : ByteArray) (hm : Malformed ps data) :
    ABI.decodeFunctionArgs? f (srcBytes data) = .error .empty := by
  obtain ⟨htl, hcl⟩ := lengths_of_dfitsAll hfit
  have hlazy := lazy_of_dfitsAll hfit
  have hz : List.map Prod.snd ((f.paramAbiCleanups.map fun _ => true).zip
      (f.params.map BindingDecl.ty)) = f.params.map BindingDecl.ty :=
    List.map_snd_zip (by simp [htl, hcl])
  have hh := aux_decode data ps _ _ 0 hfit
  unfold ABI.decodeFunctionArgs? ABI.decodeArgsWith?
  simp only [htl, hcl, beq_self_eq_true, ite_true, hlazy, hz, listHeadWords_of_dfitsAll hfit,
    ABI.abiArgOpt, bind, Except.bind, pure, Except.pure, length_srcBytes, ABI.wordBytes,
    Nat.mul_zero]
  simp only [Nat.mul_zero] at hh
  rcases hm with hm | ⟨e, he, ht⟩
  · simp [hm]
  · split
    · rename_i err heq
      split at heq
      · simp at heq; rw [← heq]
      · rw [hh.2 err heq]
    · rename_i vs heq
      split at heq
      · simp at heq
      · exact absurd ht (hh.1 vs heq e he)

/-! ## The call -/

theorem bytes_callOn (sel : Nat) (data : ByteArray) :
    (Evm.selectorOf sel ++ data).data.toList.map (·.toNat) =
      (natToBytes 4 sel).map (·.toNat) ++ srcBytes data := by
  simp [Evm.selectorOf, srcBytes]

theorem readSelector_append (sel : Nat) (hsel : sel < 2 ^ 32) (rest : List Nat) :
    ABI.readSelector? ((natToBytes 4 sel).map (·.toNat) ++ rest) = some sel := by
  have hlen : ((natToBytes 4 sel).map (·.toNat)).length = 4 := by simp [natToBytes_length]
  simp only [ABI.readSelector?, ABI.readBytes?, ABI.selectorBytes, List.drop_zero,
    List.length_append, hlen]
  rw [ite_eq_left (by omega), List.take_append_of_le_length (by omega),
    List.take_of_length_le (by omega)]
  simp only [Dirty.bytesToWordBE_natToBytes 4 sel (by simpa using hsel) (by decide)]

/-- SolidCore's run of a call of a function of the shape, from any storage, on malformed call
data: the empty revert, which keeps the call's storage. -/
theorem run_malformed {fuel : Nat} {c : TypeCheck.CheckedContract} {s0 : List (Nat × Nat)}
    (hdep : deployedStorage fuel c = some s0) (fn : DFn) (hshape : dfnShapeOk c fn = true)
    (σ : List (Nat × Nat)) (data : ByteArray) (hm : Malformed fn.params data) :
    Source.run fuel c (callOn fn.sel data σ) = some (rejected σ) := by
  simp only [dfnShapeOk, Bool.and_eq_true, decide_eq_true_eq] at hshape
  obtain ⟨hsel, hshape⟩ := hshape
  split at hshape
  case h_2 => simp at hshape
  rename_i f hf
  unfold deployedStorage at hdep
  dsimp only at hdep
  split at hdep
  case h_2 => simp at hdep
  rename_i deployed st hcons
  simp only [callOn, Source.run, Source.result?, hcons,
    TypeCheck.CheckedContract.callCalldataAtFromWithContext?,
    ABI.Contract.callCalldataAtFromWithContext?, bytes_callOn, readSelector_append _ hsel, hf]
  rw [show ((natToBytes 4 fn.sel).map (·.toNat) ++ srcBytes data).drop ABI.selectorBytes =
      srcBytes data by simp [ABI.selectorBytes, natToBytes_length],
    decode_malformed f fn.params hshape data hm]
  simp only [ABI.Contract.revertedCall?, ABI.Contract.encodeRevertData?, bind, Option.bind,
    Option.map_some, Source.observe, rejected]
  simp

end SolidCore.Refinement.Dyn

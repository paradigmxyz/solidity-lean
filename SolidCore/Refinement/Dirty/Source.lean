import SolidCore.Refinement.Evm.Calldata

/-!
# SolidCore rejects dirty argument words

SolidCore lowers a narrow ABI parameter to a `uint256`, `int256` or `bool`
word with an `AbiCleanup` (`uint b`, `int b`, `none`, `enum (n - 1)`). Its
decoder reads every word first, then applies the cleanups, and every failure on
the way is the empty revert. `decode_dirty` shows that a function of that shape,
`fitsAll`, decodes any argument list with a dirty word to `RevertData.empty`,
and `run_dirty` lifts it to `Source.run`: the call shows `Abi.rejected`.

`fnShapeOk` checks the shape of one function of a checked contract as a `Bool`,
so a proof about a contract establishes it with `native_decide`.

`refines_full` joins the two halves of a contract's proof: the refinement on the
clean calls `Abi.calls` (checked by evaluation) and EthLib's rejection of dirty
calls (`TargetDirty`, proved symbolically by `dirty_symex`) give the refinement
on `Abi.fullScope`, every call on any argument words below `2 ^ 256`. The
`Abi` section at the top shows that a clean argument list is one of
`Abi.calls` (`mem_calls`).
-/

namespace SolidCore.Refinement.Abi

/-! ## Membership of clean calls -/

/-- A clean word of a parameter is one of its values. -/
theorem mem_values {p : Param} {v : Nat} (hv : v < 2 ^ 256) (h : p.clean v = true) :
    v ∈ p.values := by
  cases p with
  | uint b => simpa [Param.clean, Param.values] using h
  | int b =>
    simp only [Param.clean, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
    simp only [Param.values, List.mem_append, List.mem_map, List.mem_range]
    generalize 2 ^ (b - 1) = Q at *
    rcases h with h | ⟨h1, -⟩
    · exact Or.inr h
    · left
      refine ⟨v - (2 ^ 256 - Q), by omega, by omega⟩
  | bool =>
    simp only [Param.clean, decide_eq_true_eq] at h
    simp only [Param.values, List.mem_cons, List.not_mem_nil, or_false]
    omega
  | enum n => simpa [Param.clean, Param.values] using h

/-- A list of clean words for the parameters is one of their tuples. -/
theorem mem_tuples : ∀ {ps : List Param} {args : List Nat}, args.length = ps.length →
    (∀ a ∈ args, a < 2 ^ 256) →
    (∀ i (hp : i < ps.length) (ha : i < args.length), ps[i].clean args[i] = true) →
    args ∈ tuples ps
  | [], [], _, _, _ => by simp [tuples]
  | p :: ps, a :: args, hlen, hargs, hc => by
    simp only [tuples, List.mem_flatMap, List.mem_map]
    refine ⟨a, mem_values (hargs a List.mem_cons_self) (hc 0 (by simp) (by simp)), args,
      mem_tuples (by simpa using hlen) (fun b hb => hargs b (List.mem_cons_of_mem _ hb))
        (fun i hp ha => hc (i + 1) (by simpa using hp) (by simpa using ha)), rfl⟩
  | [], _ :: _, hlen, _, _ | _ :: _, [], hlen, _, _ => by simp at hlen

/-- A call of a function of `fns` on clean words, from `s`, is one of `calls fns [s]`. -/
theorem mem_calls {fns : List Fn} {fn : Fn} (hfn : fn ∈ fns) {s : List (Nat × Nat)}
    {args : List Nat} (hlen : args.length = fn.params.length) (hargs : ∀ a ∈ args, a < 2 ^ 256)
    (hc : ∀ i (hp : i < fn.params.length) (ha : i < args.length),
      fn.params[i].clean args[i] = true) :
    { calldata := calldata fn.sel args, callvalue := 0, storage := s } ∈ calls fns [s] := by
  simp only [calls, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_flatMap,
    List.mem_map]
  exact ⟨fn, hfn, args, mem_tuples hlen hargs hc, rfl⟩

/-- Every call of a function of `fns` on any argument words below `2 ^ 256`, clean or not,
with no value, from the storage `s`. -/
def fullScope (fns : List Fn) (s : List (Nat × Nat)) (call : Call) : Prop :=
  ∃ fn ∈ fns, ∃ args : List Nat, args.length = fn.params.length ∧ (∀ a ∈ args, a < 2 ^ 256) ∧
    call = { calldata := calldata fn.sel args, callvalue := 0, storage := s }

end SolidCore.Refinement.Abi

namespace SolidCore.Refinement.Dirty

open EthLib.Base SolidCore.Refinement.Abi
open SolidCore.Solidity SolidCore.Solidity.Source

/-! ## The shape of a function -/

/-- Whether SolidCore's parameter type `ty` and cleanup `c` are the lowering of the ABI
parameter `p`. -/
def paramFits : Param → Source.Ty → AbiCleanup → Bool
  | .uint b, .uint256, .uint b' => b == b' && 0 < b && b ≤ 256
  | .int b, .int256, .int b' => b == b' && 0 < b && b ≤ 256
  | .bool, .bool, .none => true
  | .enum n, .uint256, .enum m => m + 1 == n && m < 2 ^ 256
  | _, _, _ => false

/-- Whether the parameter types and cleanups of a function are the lowering of `ps`. -/
def fitsAll : List Param → List Source.Ty → List AbiCleanup → Bool
  | p :: ps, ty :: tys, c :: cs => paramFits p ty c && fitsAll ps tys cs
  | [], [], [] => true
  | _, _, _ => false

/-- Whether the checked contract dispatches the selector of `fn` to a function whose
parameters are the lowering of `fn`'s. -/
def fnShapeOk (c : TypeCheck.CheckedContract) (fn : Fn) : Bool :=
  decide (fn.sel < 2 ^ 32) &&
    match c.core.findFunctionBySelector? fn.sel with
    | some f => fitsAll fn.params (f.params.map BindingDecl.ty) f.paramAbiCleanups
    | none => false

/-! ## Reading the argument words -/

/-- The bytes SolidCore reads after the selector. -/
def argBytes (args : List Nat) : List Nat := args.flatMap fun a => (natToBytes 32 a).map (·.toNat)

theorem norm_of_lt {a : Nat} (h : a < 2 ^ 256) : Shared.norm a = a := by
  simp only [Shared.norm, Shared.wordModulus]
  exact Nat.mod_eq_of_lt h

/-- SolidCore reads `n` big-endian bytes of `a` back as `a`. -/
theorem bytesToWordBE_natToBytes (n a : Nat) (ha : a < 256 ^ n) (hn : n ≤ 32) :
    ABI.bytesToWordBE (ABI.normalizeBytes ((natToBytes n a).map (·.toNat))) = a := by
  have h256 : 256 ^ n ≤ 2 ^ 256 := by
    rw [show (256 : Nat) = 2 ^ 8 by rfl, ← Nat.pow_mul]
    exact Nat.pow_le_pow_right (by decide) (by omega)
  have hbyte : ∀ b : UInt8, normByte (Shared.External.byte b.toNat) = b.toNat := by
    intro b
    have := b.toNat_lt
    simp [normByte, Shared.Account.byte, Shared.External.byte, Nat.mod_eq_of_lt this]
  unfold ABI.bytesToWordBE ABI.normalizeBytes Shared.External.normalizeBytes
  rw [List.map_map, List.foldl_map]
  simp only [Function.comp_def, hbyte]
  change Shared.norm (bytesToNat (natToBytes n a)) = _
  rw [EthLib.Base.bytesToNat_natToBytes_of_lt ha, norm_of_lt (by omega)]

theorem length_argBytes (args : List Nat) : (argBytes args).length = 32 * args.length := by
  induction args with
  | nil => rfl
  | cons a rest ih =>
    simp only [argBytes, List.flatMap_cons, List.length_append, List.length_map,
      natToBytes_length] at ih ⊢
    rw [ih, List.length_cons]; omega

/-- The word at index `i` of the argument bytes is argument `i`. -/
theorem readWord_argBytes (args : List Nat) (hargs : ∀ a ∈ args, a < 2 ^ 256) (i : Nat)
    (hi : i < args.length) : ABI.readWord? (argBytes args) (32 * i) = some args[i] := by
  induction args generalizing i with
  | nil => simp at hi
  | cons a rest ih =>
    have hchunk : ((natToBytes 32 a).map (·.toNat)).length = 32 := by
      simp [natToBytes_length]
    have hsplit : argBytes (a :: rest) = (natToBytes 32 a).map (·.toNat) ++ argBytes rest := by
      simp [argBytes]
    cases i with
    | zero =>
      have ha : a < 256 ^ 32 := by
        have := hargs a List.mem_cons_self
        rwa [show (2 : Nat) ^ 256 = 256 ^ 32 by decide] at this
      simp only [ABI.readWord?, ABI.readBytes?, ABI.wordBytes, Nat.mul_zero, List.drop_zero,
        hsplit, List.length_append, hchunk]
      rw [ite_eq_left (by omega), List.take_append_of_le_length (by omega),
        List.take_of_length_le (by omega)]
      simp only [bytesToWordBE_natToBytes 32 a ha (by decide), List.getElem_cons_zero]
    | succ i =>
      have := ih (fun b hb => hargs b (List.mem_cons_of_mem _ hb)) i (by simp at hi; omega)
      have hd : ((natToBytes 32 a).map (·.toNat) ++ argBytes rest).drop (32 + 32 * i) =
          (argBytes rest).drop (32 * i) := by
        rw [List.drop_append, List.drop_eq_nil_of_le (by omega), hchunk, List.nil_append]
        congr 1; omega
      rw [hsplit, show 32 * (i + 1) = 32 + 32 * i by omega]
      simp only [ABI.readWord?, ABI.readBytes?, List.getElem_cons_succ] at this ⊢
      rw [hd]
      exact this

/-! ## Decoding one word -/

/-- The value SolidCore decodes from the word `a` of type `ty`, before its cleanup. -/
def wordValue : Source.Ty → Nat → Value
  | .int256, a => .int a
  | _, a => .word a

theorem headWords_of_fits {p : Param} {ty : Source.Ty} {c : AbiCleanup}
    (h : paramFits p ty c = true) : ABI.Ty.abiHeadWords? ty = some 1 := by
  unfold paramFits at h
  split at h <;> first | (simp at h; done) | rfl

/-- A parameter of the shape decodes its word, or fails with the empty revert. -/
theorem decode_of_fits {p : Param} {ty : Source.Ty} {c : AbiCleanup}
    (h : paramFits p ty c = true) {lazy : Bool} {data : List Nat} {idx a : Nat}
    (hr : ABI.readWord? data (ABI.wordBytes * idx) = some a) :
    ABI.decodeValueAt? lazy data idx ty = .error .empty ∨
      ABI.decodeValueAt? lazy data idx ty = .ok (wordValue ty a) := by
  unfold paramFits at h
  split at h <;> first | (simp at h; done) | skip
  all_goals simp only [ABI.decodeValueAt?, ABI.Ty.abiDecodeFuel, ABI.decodeValueAtWithFuel?, hr,
    ABI.abiArgOpt, bind, Except.bind, pure, Except.pure, wordValue]
  all_goals first | (right; rfl) | simp | (split <;> simp)

/-- The empty revert, or the decoded word's cleanup rejecting it, when the word is dirty. -/
theorem rejects_of_fits {p : Param} {ty : Source.Ty} {c : AbiCleanup}
    (h : paramFits p ty c = true) {lazy : Bool} {data : List Nat} {idx a : Nat}
    (hr : ABI.readWord? data (ABI.wordBytes * idx) = some a) (ha : a < 2 ^ 256)
    (hd : p.clean a = false) :
    ABI.decodeValueAt? lazy data idx ty = .error .empty ∨
      c.lazyParamValue (wordValue ty a) = none := by
  have hn := norm_of_lt ha
  unfold paramFits at h
  split at h <;> first | (simp at h; done) | skip
  · -- uintN
    right
    rename_i b b'
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
    obtain ⟨⟨rfl, -⟩, -⟩ := h
    simp only [Param.clean, decide_eq_false_iff_not, Nat.not_lt] at hd
    simp [wordValue, AbiCleanup.lazyParamValue, AbiCleanup.accepts, hn]
    intros; omega
  · -- intN
    right
    rename_i b b'
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
    obtain ⟨⟨rfl, hb0⟩, hb⟩ := h
    simp only [Param.clean, Bool.or_eq_false_iff, decide_eq_false_iff_not, Nat.not_lt,
      Bool.and_eq_false_iff] at hd
    have hq : 0 < 2 ^ (b - 1) := Nat.two_pow_pos _
    have hpq : 2 ^ b = 2 * 2 ^ (b - 1) := by
      conv_lhs => rw [show b = (b - 1) + 1 by omega]
      rw [Nat.pow_succ]; omega
    have hp : 2 ^ b ≤ 2 ^ 256 := Nat.pow_le_pow_right (by decide) hb
    have hlow : a % 2 ^ b < 2 ^ b := Nat.mod_lt _ (Nat.two_pow_pos _)
    have hlow' : a % 2 ^ b ≤ a := Nat.mod_le _ _
    simp only [wordValue, AbiCleanup.lazyParamValue, AbiCleanup.accepts, hb0, hb, decide_true,
      Bool.and_self, ite_true]
    rw [ite_eq_right_iff]
    intro heq
    exfalso
    have hW : wordModulus = 2 ^ 256 := rfl
    simp only [wordEq, beq_iff_eq, Shared.norm, Shared.wordModulus, EvmYul.UInt256.size, hW]
      at heq hn
    generalize 2 ^ (b - 1) = Q at *
    generalize 2 ^ b = P at *
    have hQle : Q ≤ 2 ^ 256 := by omega
    have hS := Nat.sub_add_cancel hQle
    generalize 2 ^ 256 - Q = R at *
    rw [hn] at heq
    split at heq
    · rename_i hs
      have hT := Nat.sub_add_cancel hp
      generalize 2 ^ 256 - P = T at *
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at heq
      have h1 : T + a % P = a := heq
      have h2 : Q ≤ a % P := hs
      omega
    · rename_i hs
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at heq
      have h1 : a % P = a := heq
      have h2 : ¬ Q ≤ a % P := hs
      omega
  · -- bool
    left
    simp only [Param.clean, decide_eq_false_iff_not, Nat.not_lt] at hd
    simp only [ABI.decodeValueAt?, ABI.Ty.abiDecodeFuel, ABI.decodeValueAtWithFuel?, hr,
      ABI.abiArgOpt, bind, Except.bind, pure, Except.pure]
    simp [wordEq, hn, norm_of_lt (show (0 : Nat) < 2 ^ 256 by decide),
      norm_of_lt (show (1 : Nat) < 2 ^ 256 by decide)]
    exact ⟨by rintro rfl; exact absurd hd (by decide), by rintro rfl; exact absurd hd (by decide)⟩
  · -- enum
    right
    rename_i n m
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
    obtain ⟨rfl, hm⟩ := h
    simp only [Param.clean, decide_eq_false_iff_not, Nat.not_lt] at hd
    simp [wordValue, AbiCleanup.lazyParamValue, AbiCleanup.accepts, hn, norm_of_lt hm]
    exact hd

/-! ## Decoding the argument list -/

/-- Under the shape, every decoding failure is the empty revert, and an argument list with
a dirty word that decodes has a cleanup that rejects it. -/
theorem decodeAux_of_fits (data : List Nat) : ∀ (ps : List Param) (tys : List Source.Ty)
    (cs : List AbiCleanup) (flags : List Bool) (args : List Nat) (idx : Nat),
    fitsAll ps tys cs = true → flags.length = tys.length → args.length = ps.length →
    (∀ a ∈ args, a < 2 ^ 256) →
    (∀ i (h : i < args.length), ABI.readWord? data (ABI.wordBytes * (idx + i)) = some args[i]) →
    (∀ e, ABI.decodeArgsAux? data (flags.zip tys) idx = .error e → e = .empty) ∧
    (Dirty ps args → ∀ vs, ABI.decodeArgsAux? data (flags.zip tys) idx = .ok vs →
      AbiCleanups.lazyParamValues cs vs = none)
  | [], [], [], [], [], _, _, _, _, _, _ => by
    refine ⟨fun e h => by simp [ABI.decodeArgsAux?] at h, fun ⟨i, hp, _, _⟩ => by simp at hp⟩
  | p :: ps, ty :: tys, c :: cs, f :: flags, a :: args, idx, hfit, hfl, hlen, hargs, hread => by
    simp only [fitsAll, Bool.and_eq_true] at hfit
    obtain ⟨hp, hfit⟩ := hfit
    have ih := decodeAux_of_fits data ps tys cs flags args (idx + 1) hfit
      (by simpa using hfl) (by simpa using hlen)
      (fun b hb => hargs b (List.mem_cons_of_mem _ hb))
      (fun i h => by
        rw [show idx + 1 + i = idx + (i + 1) by omega]
        exact hread (i + 1) (by simp; omega))
    have hr0 : ABI.readWord? data (ABI.wordBytes * idx) = some a := by
      have := hread 0 (by simp)
      rw [Nat.add_zero] at this
      exact this
    have hw := headWords_of_fits hp
    have hdec := decode_of_fits (lazy := f) hp hr0
    simp only [List.zip_cons_cons, ABI.decodeArgsAux?, hw, ABI.abiArgOpt, bind, Except.bind,
      pure, Except.pure]
    refine ⟨fun e h => ?_, fun hd vs h => ?_⟩
    · rcases hdec with hdec | hdec <;> rw [hdec] at h
      · simpa using h.symm
      · simp only at h
        split at h
        · rename_i err herr
          obtain rfl : err = e := by simpa using h
          exact ih.1 _ herr
        · simp at h
    · rcases hdec with hdec | hdec <;> rw [hdec] at h
      · simp at h
      simp only at h
      split at h
      · simp at h
      rename_i vs' hvs'
      simp only [Except.ok.injEq] at h
      subst h
      obtain ⟨i, hip, hia, hcl⟩ := hd
      simp only [AbiCleanups.lazyParamValues, bind, Option.bind]
      cases i with
      | zero =>
        have := rejects_of_fits (lazy := f) hp hr0 (hargs a List.mem_cons_self) (by simpa using hcl)
        rw [hdec] at this
        rcases this with h' | h'
        · simp at h'
        · rw [h']
      | succ i =>
        have := ih.2 ⟨i, by simpa using hip, by simpa using hia, by simpa using hcl⟩ vs' hvs'
        split
        · rfl
        · rw [this]
  | [], [], [], _ :: _, _, _, _, hfl, _, _, _ => by simp at hfl
  | [], [], [], [], _ :: _, _, _, _, hlen, _, _ => by simp at hlen
  | p :: ps, ty :: tys, c :: cs, [], _, _, _, hfl, _, _, _ => by simp at hfl
  | p :: ps, ty :: tys, c :: cs, _ :: _, [], _, _, _, hlen, _, _ => by simp at hlen
  | [], _ :: _, _, _, _, _, hfit, _, _, _, _ => by simp [fitsAll] at hfit
  | [], [], _ :: _, _, _, _, hfit, _, _, _, _ => by simp [fitsAll] at hfit
  | _ :: _, [], _, _, _, _, hfit, _, _, _, _ => by simp [fitsAll] at hfit
  | _ :: _, _ :: _, [], _, _, _, hfit, _, _, _, _ => by simp [fitsAll] at hfit

theorem length_of_fitsAll : ∀ {ps : List Param} {tys : List Source.Ty} {cs : List AbiCleanup},
    fitsAll ps tys cs = true → tys.length = ps.length ∧ cs.length = ps.length
  | [], [], [], _ => ⟨rfl, rfl⟩
  | _ :: _, _ :: _, _ :: _, h => by
    simp only [fitsAll, Bool.and_eq_true] at h
    have := length_of_fitsAll h.2
    simp [this.1, this.2]
  | [], _ :: _, _, h | [], [], _ :: _, h | _ :: _, [], _, h | _ :: _, _ :: _, [], h => by
    simp [fitsAll] at h

theorem listHeadWords_of_fitsAll : ∀ {ps : List Param} {tys : List Source.Ty}
    {cs : List AbiCleanup}, fitsAll ps tys cs = true →
    ABI.Ty.listAbiHeadWords? tys = some tys.length
  | [], [], [], _ => rfl
  | _ :: _, _ :: _, _ :: _, h => by
    simp only [fitsAll, Bool.and_eq_true] at h
    simp [ABI.Ty.listAbiHeadWords?, headWords_of_fits h.1, listHeadWords_of_fitsAll h.2,
      Nat.add_comm]
  | [], _ :: _, _, h | [], [], _ :: _, h | _ :: _, [], _, h | _ :: _, _ :: _, [], h => by
    simp [fitsAll] at h

/-- A function of the shape decodes every argument list with a dirty word to the empty
revert. -/
theorem decode_dirty (fn : FunctionDef) (ps : List Param)
    (hfit : fitsAll ps (fn.params.map BindingDecl.ty) fn.paramAbiCleanups = true)
    (args : List Nat) (hlen : args.length = ps.length) (hargs : ∀ a ∈ args, a < 2 ^ 256)
    (hd : Dirty ps args) : ABI.decodeFunctionArgs? fn (argBytes args) = .error .empty := by
  obtain ⟨htl, hcl⟩ := length_of_fitsAll hfit
  have hne : fn.paramAbiCleanups.isEmpty = false := by
    obtain ⟨i, hip, -, -⟩ := hd
    cases h : fn.paramAbiCleanups with
    | nil => rw [h] at hcl; simp at hcl; omega
    | cons _ _ => rfl
  have hflags : (fn.paramAbiCleanups.map ABI.AbiCleanup.decodeLazy).length =
      (fn.params.map BindingDecl.ty).length := by simp [htl, hcl]
  have hread : ∀ i (h : i < args.length),
      ABI.readWord? (argBytes args) (ABI.wordBytes * (0 + i)) = some args[i] := by
    intro i h
    simpa [ABI.wordBytes] using readWord_argBytes args hargs i h
  have hh := decodeAux_of_fits (argBytes args) ps _ _ _ args 0 hfit hflags hlen hargs hread
  have hz : List.map Prod.snd ((fn.paramAbiCleanups.map ABI.AbiCleanup.decodeLazy).zip
      (fn.params.map BindingDecl.ty)) = fn.params.map BindingDecl.ty :=
    List.map_snd_zip (le_of_eq hflags.symm)
  unfold ABI.decodeFunctionArgs? ABI.decodeArgsWith?
  simp only [hz, listHeadWords_of_fitsAll hfit, ABI.abiArgOpt,
    length_argBytes, htl, hcl, hlen, beq_self_eq_true, ite_true, hne, bind, Except.bind, pure,
    Except.pure, ABI.wordBytes, Nat.lt_irrefl, ite_false]
  split
  · rename_i e he
    rw [hh.1 e he]
  · rename_i vs hvs
    simp [hh.2 hd vs hvs]

/-! ## The call -/

/-- The call data of `Abi.calldata`, byte by byte as SolidCore reads it. -/
theorem bytes_calldata (sel : Nat) (args : List Nat) :
    (calldata sel args).data.toList.map (·.toNat) =
      (natToBytes 4 sel).map (·.toNat) ++ argBytes args := by
  simp [calldata, argBytes, List.map_flatMap]

theorem readSelector_calldata (sel : Nat) (hsel : sel < 2 ^ 32) (args : List Nat) :
    ABI.readSelector? ((natToBytes 4 sel).map (·.toNat) ++ argBytes args) = some sel := by
  have hlen : ((natToBytes 4 sel).map (·.toNat)).length = 4 := by simp [natToBytes_length]
  simp only [ABI.readSelector?, ABI.readBytes?, ABI.selectorBytes, List.drop_zero,
    List.length_append, hlen]
  rw [ite_eq_left (by omega), List.take_append_of_le_length (by omega),
    List.take_of_length_le (by omega)]
  simp only [bytesToWordBE_natToBytes 4 sel (by simpa using hsel) (by decide)]

/-- SolidCore's run of a call of a function of the shape, from any storage, on argument
words with a dirty one: the empty revert, which keeps the call's storage. -/
theorem run_dirty {fuel : Nat} {c : TypeCheck.CheckedContract} {s0 : List (Nat × Nat)}
    (hdep : deployedStorage fuel c = some s0) (fn : Fn) (hshape : fnShapeOk c fn = true)
    (σ : List (Nat × Nat)) (args : List Nat) (hlen : args.length = fn.params.length)
    (hargs : ∀ a ∈ args, a < 2 ^ 256) (hd : Dirty fn.params args) :
    Source.run fuel c { calldata := calldata fn.sel args, callvalue := 0, storage := σ } =
      some (rejected σ) := by
  simp only [fnShapeOk, Bool.and_eq_true, decide_eq_true_eq] at hshape
  obtain ⟨hsel, hshape⟩ := hshape
  split at hshape
  case h_2 => simp at hshape
  rename_i f hf
  unfold deployedStorage at hdep
  dsimp only at hdep
  split at hdep
  case h_2 => simp at hdep
  rename_i deployed st hcons
  simp only [Source.run, Source.result?, hcons, TypeCheck.CheckedContract.callCalldataAtFromWithContext?,
    ABI.Contract.callCalldataAtFromWithContext?, bytes_calldata, readSelector_calldata _ hsel, hf]
  rw [show ((natToBytes 4 fn.sel).map (·.toNat) ++ argBytes args).drop ABI.selectorBytes =
      argBytes args by simp [ABI.selectorBytes, natToBytes_length],
    decode_dirty f fn.params hshape args hlen hargs hd]
  simp only [ABI.Contract.revertedCall?, ABI.Contract.encodeRevertData?, bind, Option.bind,
    Option.map_some, Source.observe, rejected]
  simp

/-! ## The full scope -/

/-- EthLib rejects every call of a function of `fns` with a dirty argument word, from any
storage: the per-contract fact `dirty_symex` proves. -/
def TargetDirty (code : ByteArray) (fns : List Fn) : Prop :=
  ∀ fn ∈ fns, ∀ (σ : List (Nat × Nat)) (args : List Nat), args.length = fn.params.length →
    (∀ a ∈ args, a < 2 ^ 256) → Dirty fn.params args →
    Target.run code { calldata := calldata fn.sel args, callvalue := 0, storage := σ } =
      some (rejected σ)

/-- The refinement on clean calls, the shape of every function and EthLib's rejection of
dirty calls give the refinement on every argument word. -/
theorem refines_full {fuel : Nat} {c : TypeCheck.CheckedContract} {code : ByteArray}
    {s : List (Nat × Nat)} {fns : List Fn} (hdep : deployedStorage fuel c = some s)
    (hclean : Refines fuel c code (· ∈ calls fns [s])) (hshape : fns.all (fnShapeOk c) = true)
    (htgt : TargetDirty code fns) : Refines fuel c code (fullScope fns s) := by
  rintro _ ⟨fn, hfn, args, hlen, hargs, rfl⟩
  by_cases hd : Dirty fn.params args
  · exact ⟨_, run_dirty hdep fn (List.all_eq_true.mp hshape fn hfn) s args hlen hargs hd,
      htgt fn hfn s args hlen hargs hd⟩
  · refine hclean _ (mem_calls hfn hlen hargs fun i hp ha => ?_)
    cases h : fn.params[i].clean args[i]
    · exact absurd ⟨i, hp, ha, h⟩ hd
    · rfl

end SolidCore.Refinement.Dirty















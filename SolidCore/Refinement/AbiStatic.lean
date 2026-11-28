import SolidCore.Refinement.Dirty.Source

/-!
# Static ABI parameters: their head words, and SolidCore's decoder and encoder on them

`Abi.Param` is one argument word. A static ABI parameter is a run of such words in the head of
the call data: a word type, a `bytesN` (one word, its `n` bytes on the left), a fixed-size array
`T[k]` of a static `T` (`k` runs of `T`'s words) or a struct of static members (their runs in
order). `Static` describes these, and `Static.flat` lists their words in calldata order.
`Static.params?` gives the `Abi.Param` of every word when each has one, which is the list the
generic route's `Fn` holds: every word type, and `bytes32`, whose clean words are every word
below `2 ^ 256`, exactly `.uint 256`'s (`Word.clean_param?`). A `bytesN` below 32 bytes has
none (its clean words are those whose low `32 - n` bytes are zero), so `params?` refuses it.

SolidCore's side, on its interpreter types (`Static.ofTy?` reads a static one):

* `headWords_ofTy`: a type `ofTy?` reads is not dynamic and takes `Static.headWords` words of the
  head, as SolidCore's own `staticAbiHeadWords?` counts them; `ofTy?_dynamic`: `ofTy?` reads no
  dynamic type, so `bytes`, `string`, `T[]` and every aggregate holding one stay outside.
* `decode_fixedBytes`: SolidCore decodes the argument word of a `bytesN` parameter to the
  `Value.fixedBytes` of its top `n` bytes when the word is clean, and otherwise reverts with empty
  data; `decode_bytes32`: every word is clean for `bytes32` and decodes to itself.
* `decode_fixedArray_words`, `decode_tuple_words`: a static array or struct of `uint256` words
  decodes from its run of head words to those words, for a `calldata` and a `memory` parameter.
* `encode_fixedBytes`: SolidCore encodes a `bytesN` value as one left-aligned word, `encodeWord`
  of the value shifted up by `32 - n` bytes; `encode_bytes32`: a `bytes32` value, tagged or not,
  encodes as `encodeWord` of its word, the bytes a `uint256` of that word gives.
* `encode_fixedArray`, `encode_tuple`: a static array or struct encodes as its members' encodings
  in order (`encode_fixedArray_words`: one of `uint256` words as those words).
* `encode_bytes`: SolidCore encodes one `bytes` or `string` value as the offset word 32, the length
  word, and the bytes padded with zeros to a whole word.
-/

namespace SolidCore.Refinement.Abi

open SolidCore.Solidity SolidCore.Solidity.Source

/-! ## The model -/

/-- One head word of a static ABI parameter: the word of an `Abi.Param`, or the word of a
`bytesN`, its `n` bytes on the left. -/
inductive Word where
  /-- The word of an `Abi.Param`. -/
  | param (p : Param)
  /-- The word of a `bytesN`, `0 < n ≤ 32`. -/
  | bytesN (n : Nat)
  deriving Repr, DecidableEq

/-- Whether `v` is a word the ABI encoding of the head word can give: for a `bytesN`, a word
below `2 ^ 256` whose low `32 - n` bytes are zero. -/
def Word.clean : Word → Nat → Bool
  | .param p, v => p.clean v
  | .bytesN n, v =>
    decide (0 < n) && decide (n ≤ 32) && decide (v < 2 ^ 256) && v % 2 ^ (8 * (32 - n)) == 0

/-- The `Abi.Param` whose clean words are the word's, when there is one: a word type's own, and
`.uint 256` for `bytes32`. -/
def Word.param? : Word → Option Param
  | .param p => some p
  | .bytesN n => if n = 32 then some (.uint 256) else none

/-- A word and its `Abi.Param` have the same clean words. -/
theorem Word.clean_param? {w : Word} {p : Param} (h : w.param? = some p) (v : Nat) :
    w.clean v = p.clean v := by
  cases w with
  | param q =>
    simp only [Word.param?, Option.some.injEq] at h
    subst h; rfl
  | bytesN n =>
    simp only [Word.param?] at h
    split at h
    · rename_i hn
      subst hn
      simp only [Option.some.injEq] at h
      subst h
      simp [Word.clean, Param.clean, Nat.mod_one]
    · simp at h

/-- `bytes32`'s clean words are `uint256`'s: every word below `2 ^ 256`. -/
theorem Word.clean_bytes32 (v : Nat) : (Word.bytesN 32).clean v = (Param.uint 256).clean v :=
  Word.clean_param? (by simp [Word.param?]) v

/-- A static ABI type: one word, a fixed-size array of `k` values of a static type, or a struct
of static members. -/
inductive Static where
  /-- One head word. -/
  | word (w : Word)
  /-- `T[k]`. -/
  | array (t : Static) (k : Nat)
  /-- A struct, its members in order. -/
  | tuple (ts : List Static)
  deriving Repr

mutual

/-- The head words of a static type, in calldata order. -/
def Static.flat : Static → List Word
  | .word w => [w]
  | .array t k => (List.replicate k (Static.flat t)).flatten
  | .tuple ts => Static.flatList ts

/-- The head words of static types, one after another. -/
def Static.flatList : List Static → List Word
  | [] => []
  | t :: ts => Static.flat t ++ Static.flatList ts

end

/-- The number of head words a static type takes. -/
def Static.headWords (t : Static) : Nat := t.flat.length

/-- Whether the words `vs` are a clean encoding of the static type: one clean word per head word. -/
def Static.clean (t : Static) (vs : List Nat) : Bool :=
  vs.length == t.headWords && (t.flat.zip vs).all fun p => p.1.clean p.2

/-- The `Abi.Param` of every head word of the parameters `ts`, in order, when each has one: the
list the generic route's `Fn` holds. -/
def Static.params? (ts : List Static) : Option (List Param) :=
  (Static.flatList ts).mapM Word.param?

theorem Static.headWords_array (t : Static) (k : Nat) :
    (Static.array t k).headWords = k * t.headWords := by
  simp [Static.headWords, Static.flat, List.length_flatten, List.map_replicate, List.sum_replicate]

theorem Static.headWords_tuple_cons (t : Static) (ts : List Static) :
    (Static.tuple (t :: ts)).headWords = t.headWords + (Static.tuple ts).headWords := by
  simp [Static.headWords, Static.flat, Static.flatList]

/-- `params?` keeps one `Abi.Param` per head word, each with that word's clean words. -/
theorem Static.params?_spec {ts : List Static} {ps : List Param} (h : Static.params? ts = some ps) :
    ps.length = (Static.flatList ts).length ∧
      ∀ i (hi : i < ps.length) (hj : i < (Static.flatList ts).length),
        ((Static.flatList ts)[i]).clean = (ps[i]).clean := by
  unfold Static.params? at h
  generalize Static.flatList ts = ws at h ⊢
  induction ws generalizing ps with
  | nil => simp at h; subst h; simp
  | cons w ws ih =>
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨p, hp, qs, hqs, rfl⟩ := h
    obtain ⟨hl, hc⟩ := ih hqs
    refine ⟨by simp [hl], fun i hi hj => ?_⟩
    cases i with
    | zero => exact funext (Word.clean_param? hp)
    | succ i => exact hc i (by simpa using hi) (by simpa using hj)

/-! ## SolidCore's interpreter types -/

mutual

/-- The static type of a SolidCore parameter type: its word types, `bytesN` for `0 < n ≤ 32`,
and fixed-size arrays and structs of static types; none for every other type, dynamic ones
included. -/
def Static.ofTy? : Source.Ty → Option Static
  | .uint256 => some (.word (.param (.uint 256)))
  | .address => some (.word (.param (.uint 160)))
  | .bool => some (.word (.param .bool))
  | .int256 => some (.word (.param (.int 256)))
  | .fixedBytes n => if 0 < n ∧ n ≤ 32 then some (.word (.bytesN n)) else none
  | .fixedArray k t => (Static.ofTy? t).map fun s => .array s k
  | .tuple ts => (Static.ofTyList? ts).map .tuple
  | _ => none

/-- The static types of a list of SolidCore types, when each has one. -/
def Static.ofTyList? : List Source.Ty → Option (List Static)
  | [] => some []
  | t :: ts =>
    match Static.ofTy? t, Static.ofTyList? ts with
    | some s, some ss => some (s :: ss)
    | _, _ => none

end

mutual

/-- A type `ofTy?` reads is not dynamic, and SolidCore's `staticAbiHeadWords?` counts the head
words `Static.headWords` does. -/
theorem headWords_ofTy : ∀ {ty : Source.Ty} {s : Static}, Static.ofTy? ty = some s →
    ABI.Ty.isDynamicAbi ty = false ∧ ABI.Ty.staticAbiHeadWords? ty = some s.headWords
  | .uint256, s, h | .address, s, h | .bool, s, h | .int256, s, h => by
    simp only [Static.ofTy?, Option.some.injEq] at h
    subst h
    simp [ABI.Ty.isDynamicAbi, ABI.Ty.staticAbiHeadWords?, Static.headWords, Static.flat]
  | .fixedBytes n, s, h => by
    simp only [Static.ofTy?] at h
    split at h
    · simp only [Option.some.injEq] at h
      subst h
      simp [ABI.Ty.isDynamicAbi, ABI.Ty.staticAbiHeadWords?, Static.headWords, Static.flat]
    · simp at h
  | .fixedArray k t, s, h => by
    simp only [Static.ofTy?, Option.map_eq_some_iff] at h
    obtain ⟨u, hu, rfl⟩ := h
    obtain ⟨hd, hw⟩ := headWords_ofTy hu
    refine ⟨by simp [ABI.Ty.isDynamicAbi, hd], ?_⟩
    simp [ABI.Ty.staticAbiHeadWords?, hd, hw, Static.headWords_array]
  | .tuple ts, s, h => by
    simp only [Static.ofTy?, Option.map_eq_some_iff] at h
    obtain ⟨us, hus, rfl⟩ := h
    obtain ⟨hd, hw⟩ := headWords_ofTyList hus
    refine ⟨by simp [ABI.Ty.isDynamicAbi, hd], ?_⟩
    simp [ABI.Ty.staticAbiHeadWords?, hd, hw, Static.headWords, Static.flat]
  | .bytesCalldata, s, h | .externalFunction, s, h | .internalFunction, s, h
  | .dynamicArray _, s, h => by simp [Static.ofTy?] at h
  | .enumStorage _, s, h => by simp [Static.ofTy?] at h

/-- Types `ofTyList?` reads hold no dynamic type, and take the head words of their static types,
one after another. -/
theorem headWords_ofTyList : ∀ {tys : List Source.Ty} {ss : List Static},
    Static.ofTyList? tys = some ss →
    ABI.Ty.listHasDynamicAbi tys = false ∧
      ABI.Ty.listStaticAbiHeadWords? tys = some (Static.flatList ss).length
  | [], ss, h => by
    simp only [Static.ofTyList?, Option.some.injEq] at h
    subst h
    simp [ABI.Ty.listHasDynamicAbi, ABI.Ty.listStaticAbiHeadWords?, Static.flatList]
  | t :: ts, ss, h => by
    simp only [Static.ofTyList?] at h
    split at h
    · rename_i s ss' hs hss
      simp only [Option.some.injEq] at h
      subst h
      obtain ⟨hd, hw⟩ := headWords_ofTy hs
      obtain ⟨hds, hws⟩ := headWords_ofTyList hss
      refine ⟨by simp [ABI.Ty.listHasDynamicAbi, hd, hds], ?_⟩
      simp [ABI.Ty.listStaticAbiHeadWords?, hw, hws, Static.flatList, Static.headWords]
    · simp at h

end

/-- `ofTy?` reads no dynamic type: `bytes`, `string`, `T[]` and every aggregate holding one stay
outside the static model. -/
theorem ofTy?_dynamic {ty : Source.Ty} (h : ABI.Ty.isDynamicAbi ty = true) : Static.ofTy? ty = none := by
  cases hs : Static.ofTy? ty with
  | none => rfl
  | some s => simp [(headWords_ofTy hs).1] at h

/-! ## SolidCore's decoder on a `bytesN` argument word -/

section Bytes

open EthLib.Base

theorem normalizeBytes_toNat (l : List UInt8) :
    ABI.normalizeBytes (l.map (·.toNat)) = l.map (·.toNat) := by
  unfold ABI.normalizeBytes Shared.External.normalizeBytes
  rw [List.map_map]
  apply List.map_congr_left
  intro b _
  have h : b.toNat < 256 := b.toNat_lt
  simp only [Function.comp, Shared.External.byte]
  exact Nat.mod_eq_of_lt h

/-- The argument bytes from word `i` on: word `i`'s 32 bytes, then the words after it. -/
theorem drop_argBytes (args : List Nat) (i : Nat) (hi : i < args.length) :
    (Dirty.argBytes args).drop (32 * i) =
      (natToBytes 32 args[i]).map (·.toNat) ++ Dirty.argBytes (args.drop (i + 1)) := by
  induction args generalizing i with
  | nil => simp at hi
  | cons a rest ih =>
    have hsplit : Dirty.argBytes (a :: rest) =
        (natToBytes 32 a).map (·.toNat) ++ Dirty.argBytes rest := by
      simp [Dirty.argBytes]
    have hchunk : ((natToBytes 32 a).map (·.toNat)).length = 32 := by simp [natToBytes_length]
    cases i with
    | zero => simp [hsplit]
    | succ i =>
      rw [hsplit, show 32 * (i + 1) = 32 + 32 * i by omega, List.drop_append,
        List.drop_eq_nil_of_le (by omega), hchunk, List.nil_append,
        show 32 + 32 * i - 32 = 32 * i by omega]
      simpa using ih i (by simp at hi; omega)

/-- The 32 bytes of argument word `i`, as SolidCore reads them. -/
theorem readBytes_argBytes (args : List Nat) (i : Nat) (hi : i < args.length) :
    ABI.readBytes? (Dirty.argBytes args) (32 * i) 32 = some ((natToBytes 32 args[i]).map (·.toNat)) := by
  have hchunk : ((natToBytes 32 args[i]).map (·.toNat)).length = 32 := by simp [natToBytes_length]
  simp only [ABI.readBytes?, drop_argBytes args i hi, List.length_append, hchunk]
  rw [ite_eq_left_of_eq_true _ _ (eq_true (by omega)), List.take_append_of_le_length (by omega),
    List.take_of_length_le (by omega), normalizeBytes_toNat]

theorem readBytes_left {A B : List UInt8} {k : Nat} (hk : A.length = k) :
    ABI.readBytes? (A.map (·.toNat) ++ B.map (·.toNat)) 0 k = some (A.map (·.toNat)) := by
  subst hk
  simp only [ABI.readBytes?, List.drop_zero, List.length_append, List.length_map]
  rw [ite_eq_left_of_eq_true _ _ (eq_true (by omega)), List.take_append_of_le_length (by simp),
    List.take_of_length_le (by simp), normalizeBytes_toNat]

theorem readBytes_right {A B : List UInt8} {k m : Nat} (hk : A.length = k) (hm : B.length = m) :
    ABI.readBytes? (A.map (·.toNat) ++ B.map (·.toNat)) k m = some (B.map (·.toNat)) := by
  subst hk hm
  have hd : (A.map (·.toNat) ++ B.map (·.toNat)).drop A.length = B.map (·.toNat) := by
    rw [List.drop_append, List.drop_eq_nil_of_le (by simp), List.nil_append, List.length_map,
      Nat.sub_self, List.drop_zero]
  simp only [ABI.readBytes?, hd, List.length_map]
  rw [ite_eq_left_of_eq_true _ _ (eq_true (Nat.le_refl _)), List.take_of_length_le (by simp),
    normalizeBytes_toNat]

theorem allZeroBytes_append (a b : List Nat) :
    ABI.allZeroBytes (a ++ b) = (ABI.allZeroBytes a && ABI.allZeroBytes b) := by
  induction a with
  | nil => simp [ABI.allZeroBytes]
  | cons x a ih => simp [ABI.allZeroBytes, ih, Bool.and_assoc]

/-- The low `m` bytes of `a` are all zero exactly when `256 ^ m` divides `a`. -/
theorem allZeroBytes_natToBytes (a : Nat) : ∀ m : Nat,
    ABI.allZeroBytes ((natToBytes m a).map (·.toNat)) = (a % 256 ^ m == 0)
  | 0 => by simp [natToBytes_zero, ABI.allZeroBytes, Nat.mod_one]
  | m + 1 => by
    have ih := allZeroBytes_natToBytes (a / 256) m
    have hm : a % 256 ^ (m + 1) = a % 256 + 256 * (a / 256 % 256 ^ m) := by
      rw [Nat.pow_succ', Nat.mod_mul]
    have hb : (UInt8.ofNat (a % 256)).toNat = a % 256 := by simp
    rw [natToBytes_succ, List.map_append, allZeroBytes_append, ih]
    simp only [List.map_cons, List.map_nil, ABI.allZeroBytes, hb, normByte, Shared.Account.byte,
      Nat.mod_mod, Bool.and_true, hm]
    rw [Bool.eq_iff_iff]
    simp only [Bool.and_eq_true, beq_iff_eq]
    clear hm hb ih
    generalize a / 256 % 256 ^ m = x
    rw [Nat.add_eq_zero_iff, Nat.mul_eq_zero]
    simp only [OfNat.ofNat_ne_zero, false_or]
    exact and_comm

theorem two_pow_bytes (k : Nat) : 2 ^ (8 * k) = 256 ^ k := by
  rw [Nat.pow_mul]

/-- **SolidCore decodes a `bytesN` argument word** to the `Value.fixedBytes` of its top `n` bytes
when the word is clean (its low `32 - n` bytes zero), and otherwise reverts with empty data, for a
`calldata` parameter and a `memory` one alike. -/
theorem decode_fixedBytes (args : List Nat) (hargs : ∀ a ∈ args, a < 2 ^ 256) {i : Nat}
    (hi : i < args.length) {n : Nat} (hn0 : 0 < n) (hn : n ≤ 32) (fuel : Nat) (lazy : Bool) :
    ABI.decodeValueAtWithFuel? (fuel + 1) lazy (Dirty.argBytes args) i (.fixedBytes n) =
      if (Word.bytesN n).clean args[i] then .ok (.fixedBytes n (args[i] / 2 ^ (8 * (32 - n))))
      else .error .empty := by
  have ha : args[i] < 2 ^ 256 := hargs _ (List.getElem_mem hi)
  have hsplit : natToBytes 32 args[i] =
      natToBytes n (args[i] / 256 ^ (32 - n)) ++ natToBytes (32 - n) args[i] := by
    have := natToBytes_add n (32 - n) args[i]
    rwa [show n + (32 - n) = 32 by omega] at this
  have hq : args[i] / 256 ^ (32 - n) < 256 ^ n := by
    rw [Nat.div_lt_iff_lt_mul (Nat.pow_pos (by decide)), ← Nat.pow_add,
      show n + (32 - n) = 32 by omega]
    exact ha
  have hword := SolidCore.Refinement.Dirty.bytesToWordBE_natToBytes n _ hq hn
  rw [normalizeBytes_toNat] at hword
  have hz := allZeroBytes_natToBytes args[i] (32 - n)
  simp only [ABI.decodeValueAtWithFuel?, ABI.wordBytes, readBytes_argBytes args i hi, hsplit,
    List.map_append, ABI.abiArgOpt,
    readBytes_left (B := natToBytes (32 - n) args[i]) (natToBytes_length n _),
    readBytes_right (natToBytes_length n _) (natToBytes_length (32 - n) _),
    bind, Except.bind, hword, hz, Word.clean, two_pow_bytes, hn0, hn, ha, decide_true,
    Bool.true_and]
  by_cases h : args[i] % 256 ^ (32 - n) = 0 <;> simp [h]

/-- **SolidCore decodes a `bytes32` argument word** to itself: every word is clean. -/
theorem decode_bytes32 (args : List Nat) (hargs : ∀ a ∈ args, a < 2 ^ 256) {i : Nat}
    (hi : i < args.length) (fuel : Nat) (lazy : Bool) :
    ABI.decodeValueAtWithFuel? (fuel + 1) lazy (Dirty.argBytes args) i (.fixedBytes 32) =
      .ok (.fixedBytes 32 args[i]) := by
  rw [decode_fixedBytes args hargs hi (by decide) (Nat.le_refl _)]
  simpa [Word.clean, Nat.mod_one] using hargs _ (List.getElem_mem hi)

/-! ## SolidCore's encoder on static values -/

/-- A word shifted up by `k` bytes is its bytes followed by `k` zero bytes. -/
theorem wordToBytesBE_shift (n v : Nat) : ∀ k : Nat,
    ABI.wordToBytesBE (n + k) (v * 256 ^ k) = ABI.wordToBytesBE n v ++ List.replicate k 0
  | 0 => by simp
  | k + 1 => by
    have ih := wordToBytesBE_shift n v k
    rw [← Nat.add_assoc, ABI.wordToBytesBE, Nat.pow_succ, ← Nat.mul_assoc,
      Nat.mul_div_cancel _ (by decide), ih, List.replicate_succ', List.append_assoc]
    simp [normByte, Shared.Account.byte, Nat.mul_mod_left]

/-- **SolidCore encodes a `bytesN` value** as one word, its `n` bytes on the left: the bytes of
`encodeWord` of the value shifted up by `32 - n` bytes. -/
theorem encode_fixedBytes (m : Nat) {n v : Nat} (hn0 : 0 < n) (hn : n ≤ 32)
    (hv : v < 2 ^ (8 * n)) :
    ABI.encodeStaticValue? (.fixedBytes n) (.fixedBytes m v) =
      some (ABI.encodeWord (v * 2 ^ (8 * (32 - n)))) := by
  have h256 : 2 ^ (8 * n) ≤ 2 ^ 256 := Nat.pow_le_pow_right (by decide) (by omega)
  have hlt : v * 2 ^ (8 * (32 - n)) < 2 ^ 256 := by
    calc v * 2 ^ (8 * (32 - n)) < 2 ^ (8 * n) * 2 ^ (8 * (32 - n)) :=
          Nat.mul_lt_mul_of_pos_right hv (Nat.pow_pos (by decide))
      _ = 2 ^ 256 := by rw [← Nat.pow_add]; congr 1; omega
  have hshift := wordToBytesBE_shift n v (32 - n)
  rw [show n + (32 - n) = 32 by omega] at hshift
  have hvn := Dirty.norm_of_lt (Nat.lt_of_lt_of_le hv h256)
  have hln := Dirty.norm_of_lt hlt
  rw [two_pow_bytes] at hv hln
  simp only [ABI.encodeStaticValue?, ABI.fixedBytesFits, ABI.encodeWord, ABI.wordBytes, hvn, hln,
    hv, hn0, hn, decide_true, Bool.and_true, ↓reduceIte, two_pow_bytes, hshift]

/-- **SolidCore encodes a `bytes32` value**, width-tagged or a bare word, as `encodeWord` of its
word: the bytes it gives a `uint256` of the same word. -/
theorem encode_bytes32 (m : Nat) {v : Nat} (hv : v < 2 ^ 256) :
    ABI.encodeStaticValue? (.fixedBytes 32) (.fixedBytes m v) = some (ABI.encodeWord v) ∧
      ABI.encodeStaticValue? (.fixedBytes 32) (.word v) = some (ABI.encodeWord v) ∧
      ABI.encodeStaticValue? .uint256 (.word v) = some (ABI.encodeWord v) := by
  refine ⟨?_, ?_, rfl⟩
  · rw [encode_fixedBytes m (by decide) (Nat.le_refl _) hv]; simp
  · have h := Dirty.norm_of_lt hv
    simp only [ABI.encodeStaticValue?, ABI.fixedBytesFits, ABI.encodeWord, ABI.wordBytes, h]
    simp only [show v < 2 ^ (8 * 32) from hv, decide_true, Bool.and_true, Nat.sub_self,
      List.replicate_zero, List.append_nil]
    rfl

theorem encodeArrayValues_eq (ty : Source.Ty) : ∀ (vs : List Value) (es : List ABI.Bytes),
    vs.mapM (ABI.encodeStaticValue? ty) = some es →
    ABI.encodeStaticValue?.encodeArrayValues? ty vs = some es.flatten
  | [], es, h => by
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h
    subst h
    simp [ABI.encodeStaticValue?.encodeArrayValues?]
  | v :: vs, es, h => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨e, he, es', hes, rfl⟩ := h
    simp [ABI.encodeStaticValue?.encodeArrayValues?, he, encodeArrayValues_eq ty vs es' hes]

/-- **SolidCore encodes a static fixed-size array** as its elements' encodings in order. -/
theorem encode_fixedArray {ty : Source.Ty} {vs : List Value} {es : List ABI.Bytes}
    (hd : ABI.Ty.isDynamicAbi ty = false) (h : vs.mapM (ABI.encodeStaticValue? ty) = some es) :
    ABI.encodeStaticValue? (.fixedArray vs.length ty) (.fixedArray vs) = some es.flatten := by
  simp [ABI.encodeStaticValue?, hd, encodeArrayValues_eq ty vs es h]

/-- A fixed-size array of `uint256` words encodes as those words. -/
theorem encode_fixedArray_words (ws : List Nat) :
    ABI.encodeStaticValue? (.fixedArray ws.length .uint256) (.fixedArray (ws.map .word)) =
      some (ws.flatMap ABI.encodeWord) := by
  have h : (ws.map Value.word).mapM (ABI.encodeStaticValue? .uint256) = some (ws.map ABI.encodeWord) := by
    induction ws with
    | nil => rfl
    | cons w ws ih => simp [List.mapM_cons, ABI.encodeStaticValue?, ih]
  have := encode_fixedArray (ty := .uint256) (by simp [ABI.Ty.isDynamicAbi]) h
  simpa [List.flatMap, List.length_map] using this

theorem encodeTupleValues_eq : ∀ (tys : List Source.Ty) (vs : List Value) (es : List ABI.Bytes),
    tys.length = vs.length → (tys.zip vs).mapM (fun p => ABI.encodeStaticValue? p.1 p.2) = some es →
    ABI.encodeStaticValue?.encodeTupleValues? tys vs = some es.flatten
  | [], [], es, _, h => by
    simp only [List.zip_nil_left, List.mapM_nil, Option.pure_def, Option.some.injEq] at h
    subst h
    simp [ABI.encodeStaticValue?.encodeTupleValues?]
  | ty :: tys, v :: vs, es, hl, h => by
    simp only [List.zip_cons_cons, List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.pure_def, Option.some.injEq] at h
    obtain ⟨e, he, es', hes, rfl⟩ := h
    simp [ABI.encodeStaticValue?.encodeTupleValues?, he,
      encodeTupleValues_eq tys vs es' (by simpa using hl) hes]
  | [], _ :: _, _, hl, _ | _ :: _, [], _, hl, _ => by simp at hl

/-- **SolidCore encodes a static struct** as its members' encodings in order. -/
theorem encode_tuple {tys : List Source.Ty} {vs : List Value} {es : List ABI.Bytes}
    (hd : ABI.Ty.listHasDynamicAbi tys = false) (hl : tys.length = vs.length)
    (h : (tys.zip vs).mapM (fun p => ABI.encodeStaticValue? p.1 p.2) = some es) :
    ABI.encodeStaticValue? (.tuple tys) (.tuple vs) = some es.flatten := by
  simp [ABI.encodeStaticValue?, hd, hl, encodeTupleValues_eq tys vs es hl h]

/-- **SolidCore encodes one `bytes` or `string` value** as the offset word 32, the length word, and
the bytes padded with zeros to a whole word. -/
theorem encode_bytes (bs : List Nat) :
    ABI.encodeValues? [.bytesCalldata] [.bytes bs] =
      some (ABI.encodeWord 32 ++ (ABI.encodeWord bs.length ++ ABI.padRightWord bs)) := by
  simp [ABI.encodeValues?, ABI.Ty.listAbiHeadWords?, ABI.Ty.abiHeadWords?, ABI.Ty.isDynamicAbi,
    ABI.encodeValuesAux?, ABI.encodeDynamicPayload?, ABI.wordBytes]

/-! ## SolidCore's decoder on static arrays and structs of words -/

/-- SolidCore decodes a `uint256` argument word to itself. -/
theorem decode_uint256 (args : List Nat) (hargs : ∀ a ∈ args, a < 2 ^ 256) {i : Nat}
    (hi : i < args.length) (fuel : Nat) (lazy : Bool) :
    ABI.decodeValueAtWithFuel? (fuel + 1) lazy (Dirty.argBytes args) i .uint256 =
      .ok (.word args[i]) := by
  simp [ABI.decodeValueAtWithFuel?, ABI.wordBytes, Dirty.readWord_argBytes args hargs i hi,
    ABI.abiArgOpt, bind, Except.bind]

/-- Decoding `k` values one word apart, each of which decodes to `g` of its word, gives those
values. -/
theorem decodeValueSeq_words (args : List Nat) (g : Nat → Value)
    (decode : Nat → Except RevertData Value)
    (hd : ∀ j (hj : j < args.length), decode j = .ok (g args[j])) :
    ∀ k i : Nat, i + k ≤ args.length →
      ABI.decodeValueSeq? decode (some 1) k i = .ok (((args.drop i).take k).map g)
  | 0, i, _ => by simp [ABI.decodeValueSeq?]
  | k + 1, i, h => by
    have hi : i < args.length := by omega
    have ih := decodeValueSeq_words args g decode hd k (i + 1) (by omega)
    simp only [ABI.decodeValueSeq?, hd i hi, ih, ABI.abiArgOpt, bind, Except.bind]
    rw [List.drop_eq_getElem_cons hi]
    rfl

/-- Decoding the members of a struct of `uint256` words, each of which decodes to itself. -/
theorem decodeValueList_words (args : List Nat)
    (decode : Source.Ty → Nat → Except RevertData Value)
    (hd : ∀ j (hj : j < args.length), decode .uint256 j = .ok (.word args[j])) :
    ∀ (k i : Nat), i + k ≤ args.length →
      ABI.decodeValueList? decode (List.replicate k .uint256) i =
        .ok (((args.drop i).take k).map .word)
  | 0, i, _ => by simp [ABI.decodeValueList?]
  | k + 1, i, h => by
    have hi : i < args.length := by omega
    have ih := decodeValueList_words args decode hd k (i + 1) (by omega)
    simp only [List.replicate_succ, ABI.decodeValueList?, hd i hi, ih, ABI.abiArgOpt,
      ABI.Ty.abiHeadWords?, ABI.Ty.isDynamicAbi, ABI.Ty.staticAbiHeadWords?, bind, Except.bind,
      Bool.false_eq_true, ↓reduceIte]
    rw [List.drop_eq_getElem_cons hi]
    rfl

theorem readBytes_isNone_argBytes (args : List Nat) {i n : Nat} (h : 32 * i + n ≤ 32 * args.length) :
    (ABI.readBytes? (Dirty.argBytes args) (32 * i) n).isNone = false := by
  simp only [ABI.readBytes?, List.length_drop, Dirty.length_argBytes]
  split
  · rfl
  · omega

/-- **SolidCore decodes a static array `uint256[k]`** from `k` argument words in the head, from
word `i` on, to those words, for a `calldata` parameter and a `memory` one alike. -/
theorem decode_fixedArray_words (args : List Nat) (hargs : ∀ a ∈ args, a < 2 ^ 256) {i k : Nat}
    (h : i + k ≤ args.length) (fuel : Nat) (lazy : Bool) :
    ABI.decodeValueAtWithFuel? (fuel + 2) lazy (Dirty.argBytes args) i (.fixedArray k .uint256) =
      .ok (.fixedArray (((args.drop i).take k).map .word)) := by
  have hb := readBytes_isNone_argBytes args (i := i) (n := k * 1 * 32) (by omega)
  simp only [ABI.decodeValueAtWithFuel?, ABI.Ty.isDynamicAbi, ABI.Ty.abiHeadWords?,
    ABI.Ty.staticAbiHeadWords?, ABI.wordBytes, ABI.abiArgOpt, Bool.false_eq_true, ↓reduceIte,
    bind, Except.bind, hb, Bool.and_false]
  rw [decodeValueSeq_words args Value.word _ ?_ k i h]
  intro j hj
  simp [Dirty.readWord_argBytes args hargs j hj]

theorem listHasDynamicAbi_words : ∀ k : Nat,
    ABI.Ty.listHasDynamicAbi (List.replicate k .uint256) = false
  | 0 => rfl
  | k + 1 => by
    simp [List.replicate_succ, ABI.Ty.listHasDynamicAbi, ABI.Ty.isDynamicAbi,
      listHasDynamicAbi_words k]

theorem listAbiHeadWords_words : ∀ k : Nat,
    ABI.Ty.listAbiHeadWords? (List.replicate k .uint256) = some k
  | 0 => rfl
  | k + 1 => by
    simp [List.replicate_succ, ABI.Ty.listAbiHeadWords?, ABI.Ty.abiHeadWords?, ABI.Ty.isDynamicAbi,
      ABI.Ty.staticAbiHeadWords?, listAbiHeadWords_words k, Nat.add_comm]

/-- **SolidCore decodes a static struct of `k` `uint256` members** from `k` argument words in the
head, from word `i` on, to those words, for a `calldata` parameter and a `memory` one alike. -/
theorem decode_tuple_words (args : List Nat) (hargs : ∀ a ∈ args, a < 2 ^ 256) {i k : Nat}
    (h : i + k ≤ args.length) (fuel : Nat) (lazy : Bool) :
    ABI.decodeValueAtWithFuel? (fuel + 2) lazy (Dirty.argBytes args) i
        (.tuple (List.replicate k .uint256)) =
      .ok (.tuple (((args.drop i).take k).map .word)) := by
  have hdyn := listHasDynamicAbi_words k
  have hhw := listAbiHeadWords_words k
  have hb := readBytes_isNone_argBytes args (i := i) (n := k * 32) (by omega)
  simp only [ABI.decodeValueAtWithFuel?, hdyn, hhw, ABI.wordBytes, ABI.abiArgOpt,
    Bool.false_eq_true, ↓reduceIte, bind, Except.bind, hb, Bool.and_false]
  rw [decodeValueList_words args _ ?_ k i h]
  intro j hj
  simp [decode_uint256 args hargs hj]

end Bytes

end SolidCore.Refinement.Abi

import SolidCore.Refinement.Generic.Source
import SolidCore.Refinement.Generic.Simp

/-!
# Events of the fragment: SolidCore's encoding of a log

A log of the fragment has a non-anonymous event's signature topic, then its indexed fields'
words as topics, and its other fields' words, ABI-encoded, as data. Each field is a `uint256`
word, or an `address` word that fits in 160 bits on every path the facts `K` hold on (`evOk K`:
its upper bound `bound K w` is below `2 ^ 160`, as for a constant such as `msg.sender`'s
`callerWord`, an `address` parameter, whose argument check `K` records, or a masked storage
read; SolidCore reverts on an address that does not fit, which the fragment leaves out). `encode_ok` and `encodeValues_ok`
compute SolidCore's `EventDecl.encodeFields?` on such words: the topics are the indexed words
(`evTopics`), the data the 32-byte big-endian encodings of the others (`evData`).
-/

namespace SolidCore.Refinement.Generic
open SolidCore.Solidity.Source

theorem fold_wordToBytesBE : ∀ (n v a : Nat),
    (wordToBytesBE n v).foldl (fun acc b => acc * 256 + normByte b) a = a * 256 ^ n + v % 256 ^ n
  | 0, v, a => by simp [wordToBytesBE, Nat.mod_one]
  | n + 1, v, a => by
    rw [wordToBytesBE, List.foldl_append, fold_wordToBytesBE n (v / 256) a]
    simp only [List.foldl_cons, List.foldl_nil, normByte, SolidCore.Solidity.Shared.Account.byte,
      Nat.mod_mod, Nat.pow_succ]
    have h1 : v % (256 ^ n * 256) = v % 256 + 256 * (v / 256 % 256 ^ n) := by
      rw [Nat.mul_comm, Nat.mod_mul]
    rw [h1, Nat.add_mul, Nat.mul_assoc, Nat.mul_comm (v / 256 % 256 ^ n) 256, Nat.add_assoc,
      Nat.add_comm (256 * (v / 256 % 256 ^ n))]

theorem bytesToWord_wordToBytes {v : Nat} (hv : v < wordSize) :
    bytesToWordBE (wordToBytesBE wordBytes v) = v := by
  simp only [bytesToWordBE, fold_wordToBytesBE, Nat.zero_mul, Nat.zero_add,
    show (256 : Nat) ^ wordBytes = wordSize from rfl, Nat.mod_eq_of_lt hv, norm_mod]

theorem evWordToBytesBE_eq : ∀ (n v : Nat),
    wordToBytesBE n v = (List.range n).map fun i => v / 256 ^ (n - 1 - i) % 256
  | 0, _ => rfl
  | n + 1, v => by
    rw [wordToBytesBE, evWordToBytesBE_eq n (v / 256), List.range_succ, List.map_append]
    congr 1
    · apply List.map_congr_left
      intro i hi
      simp only [List.mem_range] at hi
      rw [Nat.div_div_eq_div_mul, ← Nat.pow_succ', show (n - 1 - i).succ = n + 1 - 1 - i by omega]
    · simp [normByte, SolidCore.Solidity.Shared.Account.byte]

theorem wordBytes_eval (ρ : Val) (e : WExpr) :
    wordToBytesBE wordBytes (e.eval ρ) = (wordOBytes e).map (OByte.eval ρ) := by
  rw [evWordToBytesBE_eq, wordOBytes, List.map_map]
  apply List.map_congr_left
  intro i hi
  simp only [List.mem_range] at hi
  simp [OByte.eval, wordBytes, show 32 - 1 - i = 31 - i by omega]

/-- A field the fragment logs, with its word: any `uint256` word, or an `address` word whose bound
on the facts `K` fits in 160 bits. -/
def evFieldOk (K : Facts) (f : EventField) (w : WExpr) : Bool :=
  match f.ty with
  | .uint256 => true
  | .address => decide (bound K w < 2 ^ 160)
  | _ => false

/-- Whether every field is one the fragment logs, with its word. -/
def evOk (K : Facts) : List EventField → List WExpr → Bool
  | [], [] => true
  | f :: fs, w :: ws => evFieldOk K f w && evOk K fs ws
  | _, _ => false

/-- The words of the indexed fields: the log's topics after the signature's. -/
def evTopics : List EventField → List WExpr → List WExpr
  | f :: fs, w :: ws => if f.indexed then w :: evTopics fs ws else evTopics fs ws
  | _, _ => []

/-- The words of the other fields: the log's data, ABI-encoded. -/
def evData : List EventField → List WExpr → List WExpr
  | f :: fs, w :: ws => if f.indexed then evData fs ws else w :: evData fs ws
  | _, _ => []

/-- The types of the other fields. -/
def evDataTys : List EventField → List WExpr → List Ty
  | f :: fs, _ :: ws => if f.indexed then evDataTys fs ws else f.ty :: evDataTys fs ws
  | _, _ => []

theorem evFieldOk_static (ρ : Val) {K : Facts} (hK : K.Hold ρ) {f : EventField} {w : WExpr}
    (h : evFieldOk K f w = true) :
    abiStaticBytes? f.ty (.word (w.eval ρ)) = some (wordToBytesBE wordBytes (w.eval ρ)) ∧
      abiEncodeStaticValue? f.ty (.word (w.eval ρ)) = some (wordToBytesBE wordBytes (w.eval ρ)) ∧
      Ty.isHashedEventIndexed f.ty = false ∧ Ty.isDynamicAbi f.ty = false ∧
      Ty.staticAbiHeadWords? f.ty = some 1 := by
  unfold evFieldOk at h
  split at h
  · rename_i hty
    rw [hty]
    exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  · rename_i hty
    simp only [decide_eq_true_eq] at h
    have hn : w.eval ρ < 1461501637330902918203684832716283019655932542976 :=
      Nat.lt_of_le_of_lt (bound_sound hK w) h
    rw [hty]
    have hb : abiStaticBytes? Ty.address (.word (w.eval ρ)) =
        some (wordToBytesBE wordBytes (w.eval ρ)) := by
      simp [abiStaticBytes?, abiAddressFits, norm_mod, Nat.mod_eq_of_lt (w.eval_lt ρ), hn]
    exact ⟨hb, hb, rfl, rfl, rfl⟩
  · simp at h

theorem encode_ok (ρ : Val) {K : Facts} (hK : K.Hold ρ) :
    ∀ (fs : List EventField) (ws : List WExpr), evOk K fs ws = true →
    ∃ a b, EventDecl.encodeFields?.encode fs (ws.map fun e => Value.word (e.eval ρ)) =
      some ((evTopics fs ws).map (WExpr.eval ρ), evDataTys fs ws,
        (evData fs ws).map (fun e => Value.word (e.eval ρ)), a, b)
  | [], [], _ => ⟨[], [], rfl⟩
  | f :: fs, w :: ws, h => by
    simp only [evOk, Bool.and_eq_true] at h
    obtain ⟨a, b, ih⟩ := encode_ok ρ hK fs ws h.2
    obtain ⟨hs, -, hh, -, -⟩ := evFieldOk_static ρ hK h.1
    simp only [List.map_cons, EventDecl.encodeFields?.encode, ih, bind, Option.bind]
    by_cases hi : f.indexed = true
    · simp only [hi, ↓reduceIte, evTopics, evDataTys, evData, abiEventTopic?, hh,
        Bool.false_eq_true, hs, bytesToWord_wordToBytes (w.eval_lt ρ), List.map_cons]
      exact ⟨_, _, rfl⟩
    · simp only [hi, Bool.false_eq_true, ↓reduceIte, evTopics, evDataTys, evData, List.map_cons]
      exact ⟨_, _, rfl⟩
  | [], _ :: _, h | _ :: _, [], h => by simp [evOk] at h

theorem evData_ok {K : Facts} : ∀ (fs : List EventField) (ws : List WExpr), evOk K fs ws = true →
    ∀ (ρ : Val), K.Hold ρ → ∀ (off : Nat),
      Ty.listAbiHeadWords? (evDataTys fs ws) = some (evData fs ws).length ∧
      abiEncodeValuesAux? (evDataTys fs ws) ((evData fs ws).map fun e => Value.word (e.eval ρ)) off =
        some (((evData fs ws).flatMap wordOBytes).map (OByte.eval ρ), [], off)
  | [], [], _, _, _, _ => ⟨rfl, rfl⟩
  | f :: fs, w :: ws, h, ρ, hK, off => by
    simp only [evOk, Bool.and_eq_true] at h
    obtain ⟨ih1, ih2⟩ := evData_ok fs ws h.2 ρ hK off
    obtain ⟨-, hs, -, hd, hw⟩ := evFieldOk_static ρ hK h.1
    by_cases hi : f.indexed = true
    · simp only [evDataTys, evData, hi, ↓reduceIte]
      exact ⟨ih1, ih2⟩
    · simp only [evDataTys, evData, hi, Bool.false_eq_true, ↓reduceIte, List.map_cons,
        List.length_cons, List.flatMap_cons, List.map_append]
      refine ⟨?_, ?_⟩
      · simp [Ty.listAbiHeadWords?, Ty.abiHeadWords?, hd, hw, ih1, bind, Option.bind, Nat.add_comm]
      · simp only [abiEncodeValuesAux?, hd, Bool.false_eq_true, ↓reduceIte, hs, ih2, wordBytes_eval]
  | [], _ :: _, h, _, _, _ | _ :: _, [], h, _, _, _ => by simp [evOk] at h

theorem encodeValues_ok (ρ : Val) {K : Facts} (hK : K.Hold ρ) (fs : List EventField)
    (ws : List WExpr) (h : evOk K fs ws = true) :
    abiEncodeValues? (evDataTys fs ws) ((evData fs ws).map fun e => Value.word (e.eval ρ)) =
      some (((evData fs ws).flatMap wordOBytes).map (OByte.eval ρ)) := by
  obtain ⟨h1, h2⟩ := evData_ok fs ws h ρ hK (wordBytes * (evData fs ws).length)
  simp [abiEncodeValues?, h1, h2, bind, Option.bind]

end SolidCore.Refinement.Generic

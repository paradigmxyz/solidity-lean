import SolidCore.Solidity.Checked
import SolidCore.Refinement.Generic.Tree
import SolidCore.Refinement.Generic.Packed

/-!
# Expressions of the fragment: erasure and simulation

`eraseExpr` erases a SolidCore expression of the fragment (word literals, locals, unsigned
cleanups `uintCleanup b` and truncating casts `uintCast b` for `0 < b ≤ 256`, the latter to
`and v (2 ^ b - 1)`, checked `+`, `-`, `*`, the bitwise `&`, `|`, `^`, the comparisons `<`,
`>`, `==`, and reads of unsigned storage fields, alone in their slot or packed with others) to
its overflow conditions and its word, over a symbolic state of locals and storage writes
(`SymState`). Each overflow condition is a word whose being nonzero makes
SolidCore revert with `Panic(0x11)`: solar's check of a checked `uint256` operation
(`overflow`), or a narrow cleanup's range check `gt v (2 ^ b - 1)`. A field of `bytes` bytes
at byte offset `off` of its slot reads as `readField` (a shift and a mask) and is written by
`writeField` (the slot's other bits kept by `clearMask`, the value masked and shifted in).
`eval_erase` proves that SolidCore's interpreter evaluates the expression to `exprResult`:
the panic when a condition holds, else the word, whenever the runtime holds the symbolic state
(`ExprRel`).
-/

namespace SolidCore.Refinement.Generic
open SolidCore.Solidity.Source

/-- A storage field the fragment reads and writes: an unsigned scalar (`uint256` in SolidCore's
core) of `packedBytes` bytes at byte offset `packedOffset` of its slot, not transient. -/
def fieldOk (f : StorageField) : Bool :=
  (match f.layout? with | some (.scalar .uint256) => true | _ => false) && !f.transient &&
    decide (0 < f.packedBytes) && decide (f.packedOffset + f.packedBytes ≤ 32) &&
    decide (f.slot < wordSize)

/-- A mapping the fragment reads and writes: from `address` or `uint256` keys to `uint256`
words, not transient. -/
def mapOk (f : StorageField) : Bool :=
  (match f.layout? with
    | some (.mapping .address (.scalar .uint256)) => true
    | some (.mapping .uint256 (.scalar .uint256)) => true
    | _ => false) && !f.transient && decide (f.slot < wordSize)

/-- The slot of the mapping `x`, when the fragment reads and writes it. -/
def mapOf? (fields : List StorageField) (x : String) : Option Nat :=
  match fields.find? (fun f => f.name == x) with
  | some f => if mapOk f then some f.slot else none
  | none => none

/-- The slot, byte offset and size of the storage field `x`, when the fragment reads and
writes it. -/
def fieldOf? (fields : List StorageField) (x : String) : Option (Nat × Nat × Nat) :=
  match fields.find? (fun f => f.name == x) with
  | some f => if fieldOk f then some (f.slot, f.packedOffset, f.packedBytes) else none
  | none => none

/-- The mask of a field of `bytes` bytes. -/
def fieldMask (bytes : Nat) : Nat := 2 ^ (bytes * 8) - 1

/-- The field at byte offset `off` of `bytes` bytes of the slot word `w`: the word itself
when the field fills its slot, else `and (shr (off * 8) w) mask` (no shift at offset 0). -/
def readField (w : WExpr) (off bytes : Nat) : WExpr :=
  if off = 0 ∧ bytes = 32 then w
  else if off = 0 then .bin .and w (.lit (fieldMask bytes))
  else .bin .and (.bin .shr (.lit (off * 8)) w) (.lit (fieldMask bytes))

/-- The slot word `old` with the field at byte offset `off` of `bytes` bytes set to `v`:
`v` itself when the field fills its slot, else
`or (and old (clearMask (off * 8) (bytes * 8))) (shl (off * 8) (and v mask))`. -/
def writeField (old v : WExpr) (off bytes : Nat) : WExpr :=
  if off = 0 ∧ bytes = 32 then v
  else
    let val := WExpr.bin .and v (.lit (fieldMask bytes))
    .bin .or (.bin .and old (.lit (clearMask (off * 8) (bytes * 8))))
      (if off = 0 then val else .bin .shl (.lit (off * 8)) val)

/-- What SolidCore reads from the field in the slot word `w`. -/
def fieldValue (w off bytes : Nat) : Nat :=
  if off = 0 ∧ bytes = 32 then w else w / 2 ^ (off * 8) % 2 ^ (bytes * 8)

/-- What SolidCore leaves in the slot word `cur` when it writes `v` to the field. -/
def fieldWrite (cur v off bytes : Nat) : Nat :=
  if off = 0 ∧ bytes = 32 then v
  else (cur &&& clearMask (off * 8) (bytes * 8)) ||| ((v % 2 ^ (bytes * 8)) <<< (off * 8))

/-- A local the fragment knows: its name and its word. -/
abbrev Locals := List (String × WExpr)

def Locals.get? : Locals → String → Option WExpr
  | [], _ => none
  | (y, e) :: rest, x => if y = x then some e else Locals.get? rest x

/-- The locals of a function body by scope, the innermost first and the function's frame last,
as SolidCore's `LocalEnv` holds them. -/
abbrev Scopes := List Locals

/-- The word of the local `x`, from the innermost scope that has it. -/
def Scopes.get? : Scopes → String → Option WExpr
  | [], _ => none
  | L :: rest, x =>
    match L.get? x with
    | some e => some e
    | none => Scopes.get? rest x

/-- The symbolic state of a function body: its locals by scope, its storage writes so far and
the logs it emitted, the oldest first. -/
structure SymState where
  scopes : Scopes
  writes : Writes
  logs : List Log
  deriving DecidableEq, Repr

/-- SolidCore's slot of a mapping's entry: Keccak-256 of the key's word and the mapping's slot,
as `mappingStorageSlot slot key` computes it. -/
def solHash (key slot : Nat) : Nat := keccakWord (storageWordBytes key ++ storageWordBytes slot)

theorem mappingStorageSlot_eq (slot key : Nat) : mappingStorageSlot slot key = solHash key slot := rfl

/-- The overflow condition of a checked unsigned operation, as solar lowers it. -/
def overflow : BinOp → WExpr → WExpr → Option WExpr
  | .add, l, r => some (.bin .lt (.bin .add l r) l)
  | .sub, l, r => some (.bin .lt l r)
  | .mul, l, r => some (.un .iszero (.bin .or (.un .iszero r) (.bin .eq (.bin .div (.bin .mul l r) r) l)))
  | _, _, _ => none

/-- The fragment's binary operators: SolidCore's operator and the word operation. -/
def binOf : BinaryOp → Option BinOp
  | .add => some .add
  | .sub => some .sub
  | .mul => some .mul
  | .lt => some .lt
  | .gt => some .gt
  | .eq => some .eq
  | .bitAnd => some .and
  | .bitOr => some .or
  | .bitXor => some .xor
  | _ => none

/-- The erasure of an expression of the fragment: the overflow conditions it checks, each
reverting with `Panic(0x11)` when not zero, and its word. -/
def eraseExpr (fields : List StorageField) (S : SymState) : Expr → Option (List WExpr × WExpr)
  | .word n => some ([], .lit n)
  | .var x => (Scopes.get? S.scopes x).map fun e => ([], e)
  | .caller => some ([], .lit callerWord)
  | .castOp .uintCleanup b e => do
    let (gs, v) ← eraseExpr fields S e
    if b = 256 then some (gs, v)
    else if 0 < b ∧ b < 256 then some (gs ++ [.bin .gt v (.lit (2 ^ b - 1))], v)
    else none
  | .castOp .uintCast b e => do
    let (gs, v) ← eraseExpr fields S e
    if b = 256 then some (gs, v)
    else if 0 < b ∧ b < 256 then some (gs, .bin .and v (.lit (2 ^ b - 1)))
    else none
  | .binary op l r => do
    let o ← binOf op
    let (gl, vl) ← eraseExpr fields S l
    let (gr, vr) ← eraseExpr fields S r
    match overflow o vl vr with
    | some g => some (gl ++ gr ++ [g], .bin o vl vr)
    | none => some (gl ++ gr, .bin o vl vr)
  | .storageRead .header x [] =>
    (fieldOf? fields x).map fun (k, off, bytes) => ([], readField (S.writes.read (.lit k)) off bytes)
  | .storageRead .ref x [] =>
    (fieldOf? fields x).map fun (k, off, bytes) => ([], readField (S.writes.read (.lit k)) off bytes)
  | .storageRead .element x [idx] => do
    let k ← mapOf? fields x
    let (gs, v) ← eraseExpr fields S idx
    some (gs, S.writes.read (.hash v (.lit k)))
  | _ => none


/-! ## Words: SolidCore's word operations on words below `2 ^ 256` -/

theorem norm_lt {a : Nat} (h : a < wordSize) : SolidCore.Solidity.Shared.norm a = a := by
  simp only [SolidCore.Solidity.Shared.norm, SolidCore.Solidity.Shared.wordModulus]
  exact Nat.mod_eq_of_lt h

theorem size_eq : EvmYul.UInt256.size = wordSize := rfl
theorem modulus_eq : SolidCore.Solidity.Shared.wordModulus = wordSize := rfl

theorem toNat_ofNat_u256 (n : Nat) : (EvmYul.UInt256.ofNat n).toNat = n % wordSize :=
  Fin.val_ofNat _ _
theorem toNat_add_u256 (x y : EvmYul.UInt256) : (x.add y).toNat = (x.toNat + y.toNat) % wordSize :=
  Fin.val_add _ _
theorem toNat_sub_u256 (x y : EvmYul.UInt256) :
    (x.sub y).toNat = (wordSize - y.toNat + x.toNat) % wordSize :=
  Fin.val_sub _ _
theorem toNat_mul_u256 (x y : EvmYul.UInt256) : (x.mul y).toNat = (x.toNat * y.toNat) % wordSize :=
  Fin.val_mul _ _

open SolidCore.Solidity.Shared in
theorem addWord_eq (a b : Nat) : addWord a b = (a + b) % wordSize := by
  simp only [addWord, liftEvmBinary, ofEvmWord, toEvmWord, norm, modulus_eq, toNat_add_u256,
    toNat_ofNat_u256, Nat.mod_mod, Nat.add_mod_mod, Nat.mod_add_mod]

open SolidCore.Solidity.Shared in
theorem subWord_eq (a b : Nat) (ha : a < wordSize) (hb : b < wordSize) :
    subWord a b = (a + (wordSize - b)) % wordSize := by
  simp only [subWord, liftEvmBinary, ofEvmWord, toEvmWord, norm, modulus_eq, toNat_sub_u256,
    toNat_ofNat_u256, Nat.mod_mod, Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt ha]
  rw [Nat.add_comm]

open SolidCore.Solidity.Shared in
theorem mulWord_eq (a b : Nat) : mulWord a b = (a * b) % wordSize := by
  simp only [mulWord, liftEvmBinary, ofEvmWord, toEvmWord, norm, modulus_eq, toNat_mul_u256,
    toNat_ofNat_u256, Nat.mod_mod, Nat.mul_mod_mod, Nat.mod_mul_mod]

open SolidCore.Solidity.Shared in
theorem ltWord_eq (a b : Nat) : ltWord a b = if a % wordSize < b % wordSize then 1 else 0 := by
  have key : (EvmYul.UInt256.ofNat (norm a) < EvmYul.UInt256.ofNat (norm b)) ↔
      a % wordSize < b % wordSize := by
    show (EvmYul.UInt256.ofNat (norm a)).toNat < (EvmYul.UInt256.ofNat (norm b)).toNat ↔ _
    rw [toNat_ofNat_u256, toNat_ofNat_u256]
    simp [norm, modulus_eq]
  unfold ltWord liftEvmBinary ofEvmWord toEvmWord EvmYul.UInt256.lt EvmYul.UInt256.fromBool
    Bool.toUInt256
  by_cases h : a % wordSize < b % wordSize
  · rw [ite_eq_left_of_eq_true _ _ (eq_true (decide_eq_true (key.mpr h))), ite_eq_left_of_eq_true _ _ (eq_true h)]; rfl
  · rw [ite_eq_right_of_eq_false _ _ (eq_false (by simpa using fun h' => h (key.mp h'))), ite_eq_right_of_eq_false _ _ (eq_false h)]; rfl

open SolidCore.Solidity.Shared in
theorem gtWord_eq (a b : Nat) : gtWord a b = if b % wordSize < a % wordSize then 1 else 0 := by
  rw [← ltWord_eq]; rfl

theorem apply_add (a b : Nat) (ha : a < wordSize) (hb : b < wordSize) :
    BinaryOp.apply true .add (.word a) (.word b) =
      if wordSize ≤ a + b then .error (.panic 0x11) else .ok (.word ((a + b) % wordSize)) := by
  by_cases h : wordSize ≤ a + b <;>
  simp [BinaryOp.apply, Value.forceAbiLazy, BinaryOp.applyWord, checkedAdd, norm_lt ha, norm_lt hb,
    bind, Except.bind, Functor.map, Except.map, wordModulus, RevertData.overflow, addWord_eq, h,
    size_eq, modulus_eq]

theorem apply_sub (a b : Nat) (ha : a < wordSize) (hb : b < wordSize) :
    BinaryOp.apply true .sub (.word a) (.word b) =
      if a < b then .error (.panic 0x11) else .ok (.word ((a + (wordSize - b)) % wordSize)) := by
  by_cases h : a < b <;>
  simp [BinaryOp.apply, Value.forceAbiLazy, BinaryOp.applyWord, checkedSub, norm_lt ha, norm_lt hb,
    bind, Except.bind, Functor.map, Except.map, RevertData.overflow, subWord_eq a b ha hb, h]

theorem apply_mul (a b : Nat) (ha : a < wordSize) (hb : b < wordSize) :
    BinaryOp.apply true .mul (.word a) (.word b) =
      if wordSize ≤ a * b then .error (.panic 0x11) else .ok (.word ((a * b) % wordSize)) := by
  by_cases h : wordSize ≤ a * b <;>
  simp [BinaryOp.apply, Value.forceAbiLazy, BinaryOp.applyWord, checkedMul, norm_lt ha, norm_lt hb,
    bind, Except.bind, Functor.map, Except.map, wordModulus, RevertData.overflow, mulWord_eq, h,
    modulus_eq]

theorem apply_lt (a b : Nat) (ha : a < wordSize) (hb : b < wordSize) :
    BinaryOp.apply true .lt (.word a) (.word b) = .ok (.word (if a < b then 1 else 0)) := by
  simp [BinaryOp.apply, Value.forceAbiLazy, BinaryOp.applyWord, bind, Except.bind, Functor.map,
    Except.map, ltWord_eq, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]

theorem apply_gt (a b : Nat) (ha : a < wordSize) (hb : b < wordSize) :
    BinaryOp.apply true .gt (.word a) (.word b) = .ok (.word (if b < a then 1 else 0)) := by
  simp [BinaryOp.apply, Value.forceAbiLazy, BinaryOp.applyWord, bind, Except.bind, Functor.map,
    Except.map, gtWord_eq, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]

theorem apply_eq (a b : Nat) (ha : a < wordSize) (hb : b < wordSize) :
    BinaryOp.apply true .eq (.word a) (.word b) = .ok (.word (if a = b then 1 else 0)) := by
  simp [BinaryOp.apply, Value.forceAbiLazy, bind, Except.bind, Functor.map, Except.map, boolWord, wordEq,
    norm_lt ha, norm_lt hb]

theorem fieldOk_spec {f : StorageField} (h : fieldOk f = true) :
    f.layout? = some (.scalar .uint256) ∧ f.transient = false ∧ 0 < f.packedBytes ∧
      f.packedOffset + f.packedBytes ≤ 32 ∧ f.slot < wordSize := by
  unfold fieldOk at h
  simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨hl, ht⟩, hb⟩, ho⟩, hs⟩ := h
  refine ⟨?_, ht, hb, ho, hs⟩
  split at hl
  · rename_i h; exact h
  · simp at hl

/-- What the fragment knows of a field it reads and writes. -/
structure FieldOk (ctx : Context) (x : String) (f : StorageField) : Prop where
  find : ctx.storageField? x = some f
  layout : f.layout? = some (.scalar .uint256)
  transient : f.transient = false
  bytes : 0 < f.packedBytes
  fits : f.packedOffset + f.packedBytes ≤ 32
  slot : f.slot < wordSize

theorem fieldOf?_spec {fields : List StorageField} {ctx : Context} (hf : ctx.storageFields = fields)
    {x : String} {k off bytes : Nat} (h : fieldOf? fields x = some (k, off, bytes)) :
    ∃ f, FieldOk ctx x f ∧ f.slot = k ∧ f.packedOffset = off ∧ f.packedBytes = bytes := by
  unfold fieldOf? at h
  split at h
  · rename_i f hfind
    split at h
    · rename_i hs
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      obtain ⟨h1, h2, h3, h4, h5⟩ := fieldOk_spec hs
      exact ⟨f, ⟨by simp [Context.storageField?, hf, hfind], h1, h2, h3, h4, h5⟩, rfl, rfl, rfl⟩
    · simp at h
  · simp at h

theorem toNat_land_u256 (x y : EvmYul.UInt256) :
    (x.land y).toNat = (x.toNat &&& y.toNat) % wordSize := rfl
theorem toNat_lor_u256 (x y : EvmYul.UInt256) :
    (x.lor y).toNat = (x.toNat ||| y.toNat) % wordSize := rfl
theorem toNat_xor_u256 (x y : EvmYul.UInt256) :
    (x.xor y).toNat = (x.toNat ^^^ y.toNat) % wordSize := rfl

theorem apply_bitAnd (a b : Nat) (ha : a < wordSize) (hb : b < wordSize) :
    BinaryOp.apply true .bitAnd (.word a) (.word b) = .ok (.word ((a &&& b) % wordSize)) := by
  simp [BinaryOp.apply, Value.forceAbiLazy, BinaryOp.applyWord, bind, Except.bind, Functor.map,
    Except.map, SolidCore.Solidity.Shared.andWord, SolidCore.Solidity.Shared.liftEvmBinary,
    SolidCore.Solidity.Shared.ofEvmWord, SolidCore.Solidity.Shared.toEvmWord, toNat_land_u256,
    toNat_ofNat_u256, norm_lt ha, norm_lt hb, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb,
    SolidCore.Solidity.Shared.norm, modulus_eq, Nat.mod_mod]

theorem apply_bitOr (a b : Nat) (ha : a < wordSize) (hb : b < wordSize) :
    BinaryOp.apply true .bitOr (.word a) (.word b) = .ok (.word ((a ||| b) % wordSize)) := by
  simp [BinaryOp.apply, Value.forceAbiLazy, BinaryOp.applyWord, bind, Except.bind, Functor.map,
    Except.map, SolidCore.Solidity.Shared.orWord, SolidCore.Solidity.Shared.liftEvmBinary,
    SolidCore.Solidity.Shared.ofEvmWord, SolidCore.Solidity.Shared.toEvmWord, toNat_lor_u256,
    toNat_ofNat_u256, norm_lt ha, norm_lt hb, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb,
    SolidCore.Solidity.Shared.norm, modulus_eq, Nat.mod_mod]

theorem apply_bitXor (a b : Nat) (ha : a < wordSize) (hb : b < wordSize) :
    BinaryOp.apply true .bitXor (.word a) (.word b) = .ok (.word ((a ^^^ b) % wordSize)) := by
  simp [BinaryOp.apply, Value.forceAbiLazy, BinaryOp.applyWord, bind, Except.bind, Functor.map,
    Except.map, SolidCore.Solidity.Shared.xorWord, SolidCore.Solidity.Shared.liftEvmBinary,
    SolidCore.Solidity.Shared.ofEvmWord, SolidCore.Solidity.Shared.toEvmWord, toNat_xor_u256,
    toNat_ofNat_u256, norm_lt ha, norm_lt hb, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb,
    SolidCore.Solidity.Shared.norm, modulus_eq, Nat.mod_mod]

/-- SolidCore's checked cleanup to `b` bits keeps a word below `2 ^ b` and panics on any other. -/
theorem uintCleanup_lt (w b : Nat) (hw : w < wordSize) (hb0 : 0 < b) (hb : b ≤ 256) :
    uintCleanup? true b (.word w) = if w < 2 ^ b then .ok (.word w) else .error (.panic 0x11) := by
  simp [uintCleanup?, Value.forceAbiLazy, Value.asStorageWord?, norm_lt hw, uintCast?, bind,
    Except.bind, hb0, hb, RevertData.overflow]
  by_cases h : w < 2 ^ b
  · simp [h, Nat.mod_eq_of_lt h, Nat.not_le.mpr h]
  · simp [h, Nat.le_of_not_lt h]

theorem fieldMask_lt {bytes : Nat} (h : bytes ≤ 32) : fieldMask bytes < wordSize := by
  unfold fieldMask
  have := Nat.pow_le_pow_right (show 0 < 2 by decide) (show bytes * 8 ≤ 256 by omega)
  have := Nat.two_pow_pos (bytes * 8)
  simp only [wordSize]; omega

theorem eval_and_mask (ρ : Val) (e : WExpr) {bytes : Nat} (h : bytes ≤ 32) :
    (WExpr.bin .and e (.lit (fieldMask bytes))).eval ρ = e.eval ρ % 2 ^ (bytes * 8) := by
  simp only [WExpr.eval, BinOp.eval, Nat.mod_eq_of_lt (fieldMask_lt h)]
  rw [fieldMask, Nat.and_two_pow_sub_one_eq_mod]
  exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos _))
    (Nat.pow_le_pow_right (by decide) (by omega)))

theorem readField_eval (ρ : Val) (e : WExpr) {off bytes : Nat} (h : off + bytes ≤ 32)
    (hb : 0 < bytes) : (readField e off bytes).eval ρ = fieldValue (e.eval ρ) off bytes := by
  unfold readField fieldValue
  by_cases h1 : off = 0 ∧ bytes = 32
  · simp only [h1, and_self, ↓reduceIte]
  · simp only [h1, ↓reduceIte]
    by_cases h0 : off = 0
    · subst h0
      simp only [↓reduceIte, eval_and_mask ρ e (show bytes ≤ 32 by omega), Nat.zero_mul,
        Nat.pow_zero, Nat.div_one]
    · simp only [h0, ↓reduceIte, eval_and_mask ρ _ (show bytes ≤ 32 by omega)]
      have hs : off * 8 < 256 := by omega
      simp only [WExpr.eval, BinOp.eval, Nat.mod_eq_of_lt (show off * 8 < wordSize from
        Nat.lt_of_lt_of_le hs (by decide)), hs, ↓reduceIte]
      rw [Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (e.eval_lt ρ))]

theorem writeField_eval (ρ : Val) (old v : WExpr) {off bytes : Nat} (h : off + bytes ≤ 32)
    (hb : 0 < bytes) :
    (writeField old v off bytes).eval ρ = fieldWrite (old.eval ρ) (v.eval ρ) off bytes := by
  unfold writeField fieldWrite
  by_cases h1 : off = 0 ∧ bytes = 32
  · simp only [h1, and_self, ↓reduceIte]
  · simp only [h1, ↓reduceIte]
    have hob8 : off * 8 + bytes * 8 ≤ 256 := by omega
    have hcl := clearMask_lt (off * 8) (bytes * 8) hob8
    have hlt := replace_lt (old.eval_lt ρ) (v.eval ρ) _ _ hob8
    have hshl : (v.eval ρ % 2 ^ (bytes * 8)) <<< (off * 8) < wordSize := by
      exact Nat.lt_of_le_of_lt Nat.right_le_or hlt
    have hval : (if off = 0 then WExpr.bin .and v (.lit (fieldMask bytes))
        else .bin .shl (.lit (off * 8)) (.bin .and v (.lit (fieldMask bytes)))).eval ρ =
        (v.eval ρ % 2 ^ (bytes * 8)) <<< (off * 8) := by
      split
      · rename_i h0
        subst h0
        rw [eval_and_mask ρ v (by omega)]
        simp
      · rename_i h0
        have hs : off * 8 < 256 := by omega
        rw [eval_bin, eval_and_mask ρ v (by omega), eval_lit, Nat.mod_eq_of_lt (show off * 8 < wordSize from
          Nat.lt_of_lt_of_le hs (by decide))]
        simp only [BinOp.eval, hs, ↓reduceIte]
        rw [Nat.shiftLeft_eq] at hshl ⊢
        rw [Nat.mod_mod, Nat.mod_eq_of_lt hshl]
    rw [eval_bin, hval, eval_bin, eval_lit, Nat.mod_eq_of_lt hcl]
    simp only [BinOp.eval]
    rw [Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt Nat.and_le_left (old.eval_lt ρ)), Nat.mod_eq_of_lt hlt]

/-- What SolidCore's runtime holds of a symbolic state, for an expression: the context's
storage fields are the contract's, arithmetic is checked, every local the state knows holds
its word, and every slot holds the word the writes leave there. -/
structure ExprRel (ρ : Val) (fields : List StorageField) (ctx : Context) (rt : Runtime)
    (S : SymState) : Prop where
  fields : ctx.storageFields = fields
  checked : ctx.checked = true
  sender : ctx.sender = callerWord
  hash : ρ.hash = solHash
  ok : ρ.Ok
  locals : ∀ x e, Scopes.get? S.scopes x = some e → rt.lookupLocal? x = some (.word (e.eval ρ))
  store : ∀ k, k < wordSize → rt.state.loadSlot k = Writes.store ρ S.writes k

/-- What SolidCore's evaluation of an erased expression gives: `Panic(0x11)` when one of its
overflow conditions holds, and otherwise its word, with the runtime unchanged. -/
def exprResult (ρ : Val) (gs : List WExpr) (v : WExpr) (rt : Runtime) : SolI (Value × Runtime) :=
  if gs.any (fun g => g.eval ρ != 0) then .done (.error (.revert (.panic 0x11)))
  else .done (.ok (.word (v.eval ρ), rt))

theorem load_field {ctx : Context} {rt : Runtime} {x : String} {f : StorageField}
    (hf : FieldOk ctx x f) (hw : rt.state.loadSlot f.slot < wordSize) :
    rt.loadStorageField ctx x =
      .ok (.word (fieldValue (rt.state.loadSlot f.slot) f.packedOffset f.packedBytes)) := by
  have := hf.bytes
  have := hf.fits
  simp [Runtime.loadStorageField, hf.find, hf.layout, StorageField.storageValueFromWord?,
    Ty.storageValueFromWord?, State.loadFieldWord, StorageField.isPacked,
    SolidCore.Solidity.Source.wordBytes, State.loadFieldSlot, hf.transient, fieldValue, wordBitRange,
    StorageField.packedBitWidth, StorageField.packedBitOffset, norm_lt hw]
  by_cases h : f.packedOffset = 0 ∧ f.packedBytes = 32
  · simp [h]
  · have hlt : rt.state.loadSlot f.slot / 2 ^ (f.packedOffset * 8) % 2 ^ (f.packedBytes * 8) <
        wordSize :=
      Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos _))
        (Nat.pow_le_pow_right (by decide) (by omega))
    rw [if_pos (by omega), if_neg h, if_neg (by omega), norm_lt hlt]

theorem loadHeader_field {ctx : Context} {rt : Runtime} {x : String} {f : StorageField}
    (hf : FieldOk ctx x f) (hw : rt.state.loadSlot f.slot < wordSize) :
    rt.loadStorageFieldHeader ctx x =
      .ok (.word (fieldValue (rt.state.loadSlot f.slot) f.packedOffset f.packedBytes)) := by
  simp only [Runtime.loadStorageFieldHeader, hf.find, hf.layout]
  exact load_field hf hw

theorem guard_add (ρ : Val) (l r : WExpr) :
    ((WExpr.bin .lt (.bin .add l r) l).eval ρ != 0) = decide (wordSize ≤ l.eval ρ + r.eval ρ) := by
  have hl := l.eval_lt ρ
  have hr := r.eval_lt ρ
  simp only [WExpr.eval, BinOp.eval, Nat.mod_mod]
  by_cases h : wordSize ≤ l.eval ρ + r.eval ρ
  · have : (l.eval ρ + r.eval ρ) % wordSize < l.eval ρ := by
      rw [Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (by omega)]; omega
    simp [this, h]
  · have : ¬ (l.eval ρ + r.eval ρ) % wordSize < l.eval ρ := by
      rw [Nat.mod_eq_of_lt (by omega)]; omega
    simp [this, h]

theorem guard_sub (ρ : Val) (l r : WExpr) :
    ((WExpr.bin .lt l r).eval ρ != 0) = decide (l.eval ρ < r.eval ρ) := by
  simp only [WExpr.eval, BinOp.eval]
  by_cases h : l.eval ρ < r.eval ρ <;> simp [h]

theorem guard_mul (ρ : Val) (l r : WExpr) :
    ((WExpr.un .iszero (.bin .or (.un .iszero r) (.bin .eq (.bin .div (.bin .mul l r) r) l))).eval ρ
      != 0) = decide (wordSize ≤ l.eval ρ * r.eval ρ) := by
  have hl := l.eval_lt ρ
  have hr := r.eval_lt ρ
  simp only [WExpr.eval]
  generalize l.eval ρ = a at *
  generalize r.eval ρ = b at *
  by_cases hb0 : b = 0
  · subst hb0
    by_cases ha0 : a = 0
    · subst ha0; simp [UnOp.eval, BinOp.eval]
    · have : (0 = a) = False := propext ⟨fun h => ha0 h.symm, False.elim⟩
      simp [UnOp.eval, BinOp.eval, this]
  · have key : (a * b % wordSize) / b = a ↔ a * b < wordSize := by
      constructor
      · intro h
        by_contra h'
        have h1 : a * b % wordSize < wordSize := Nat.mod_lt _ (by decide)
        have h2 : (a * b % wordSize) / b * b ≤ a * b % wordSize := Nat.div_mul_le_self _ _
        rw [h] at h2
        omega
      · intro h
        rw [Nat.mod_eq_of_lt h, Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hb0)]
    have hdiv : a * b % wordSize / b < wordSize :=
      Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (Nat.mod_lt _ (by decide))
    simp only [UnOp.eval, BinOp.eval, hb0, ↓reduceIte, Nat.mod_mod, Nat.mod_eq_of_lt hdiv,
      Nat.zero_mod, Nat.zero_or]
    by_cases h : a * b % wordSize / b = a
    · have := key.mp h
      simp [h, Nat.not_le.mpr this]
    · have : wordSize ≤ a * b := Nat.not_lt.mp (fun h' => h (key.mpr h'))
      simp [h, this]

theorem bind_exprResult {α : Type} (ρ : Val) (gs : List WExpr) (v : WExpr) (rt : Runtime)
    (k : Value × Runtime → SolI α) :
    (exprResult ρ gs v rt >>= k) =
      if gs.any (fun g => g.eval ρ != 0) then .done (.error (.revert (.panic 0x11)))
      else k (.word (v.eval ρ), rt) := by
  unfold exprResult
  split <;> rfl


theorem add_wrap_lt {a b : Nat} (ha : a < wordSize) (hb : b < wordSize) (h : wordSize ≤ a + b) :
    (a + b) % wordSize < a := by
  rw [Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (by omega)]; omega

theorem add_nowrap_le {a b : Nat} (h : a + b < wordSize) : a ≤ (a + b) % wordSize := by
  rw [Nat.mod_eq_of_lt h]; omega

theorem any_append (p : WExpr → Bool) (a b : List WExpr) :
    (a ++ b).any p = (a.any p || b.any p) := List.any_append

theorem uintCleanup_256 (w : Nat) (hw : w < wordSize) :
    uintCleanup? true 256 (.word w) = .ok (.word w) := by
  simp [uintCleanup?, Value.forceAbiLazy, Value.asStorageWord?, norm_lt hw, uintCast?, bind,
    Except.bind, Nat.mod_eq_of_lt hw]
  exact hw

/-- SolidCore's truncating cast to `b` bits keeps the word's low `b` bits. -/
theorem uintCast_word (w b : Nat) (hw : w < wordSize) (hb0 : 0 < b) (hb : b ≤ 256) :
    uintCast? b (.word w) = .ok (.word (w % 2 ^ b)) := by
  simp [uintCast?, Value.forceAbiLazy, Value.asStorageWord?, norm_lt hw, bind, Except.bind, hb0, hb]

/-- The word `and e (2 ^ b - 1)` is `e`'s low `b` bits. -/
theorem eval_and_pow (ρ : Val) (e : WExpr) {b : Nat} (hb : b ≤ 256) :
    (WExpr.bin .and e (.lit (2 ^ b - 1))).eval ρ = e.eval ρ % 2 ^ b := by
  have hle : 2 ^ b ≤ wordSize := Nat.pow_le_pow_right (by decide) hb
  have hlt : 2 ^ b - 1 < wordSize :=
    Nat.lt_of_lt_of_le (Nat.sub_lt (Nat.two_pow_pos b) (by decide)) hle
  simp only [WExpr.eval, BinOp.eval, Nat.mod_eq_of_lt hlt]
  rw [Nat.and_two_pow_sub_one_eq_mod]
  exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos _)) hle)

/-- The word a constant slot holds is the writes' read of it. -/
theorem slot_read {ρ : Val} {fields : List StorageField} {ctx : Context} {rt : Runtime} {S : SymState}
    (hrel : ExprRel ρ fields ctx rt S) {k : Nat} (hk : k < wordSize) :
    rt.state.loadSlot k = (S.writes.read (.lit k)).eval ρ := by
  rw [Writes.eval_read hrel.ok, hrel.store k hk]
  simp only [WExpr.eval, Nat.mod_eq_of_lt hk]

theorem norm_mod (n : Nat) : SolidCore.Solidity.Shared.norm n = n % wordSize := rfl

theorem loadSlot_mod (st : State) (k : Nat) : st.loadSlot (k % wordSize) = st.loadSlot k := by
  simp only [State.loadSlot, StorageMap.lookup?, norm_mod, Nat.mod_mod]

/-- What the fragment knows of a mapping it reads and writes. -/
structure MapOk (ctx : Context) (x : String) (f : StorageField) : Prop where
  find : ctx.storageField? x = some f
  layout : f.layout? = some (.mapping .address (.scalar .uint256)) ∨
    f.layout? = some (.mapping .uint256 (.scalar .uint256))
  transient : f.transient = false
  slot : f.slot < wordSize

theorem mapOf?_spec {fields : List StorageField} {ctx : Context} (hf : ctx.storageFields = fields)
    {x : String} {k : Nat} (h : mapOf? fields x = some k) :
    ∃ f, MapOk ctx x f ∧ f.slot = k := by
  unfold mapOf? at h
  split at h
  · rename_i f hfind
    split at h
    · rename_i hs
      simp only [Option.some.injEq] at h
      subst h
      unfold mapOk at hs
      simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hs
      obtain ⟨⟨hl, ht⟩, hsl⟩ := hs
      refine ⟨f, ⟨by simp [Context.storageField?, hf, hfind], ?_, ht, hsl⟩, rfl⟩
      split at hl
      · rename_i h; exact .inl h
      · rename_i h; exact .inr h
      · simp at hl
    · simp at h
  · simp at h

/-- SolidCore reads the entry of a mapping at a key word as the writes' read of the slot word
`hash key slot`. -/
theorem loadIndex_map {ρ : Val} {fields : List StorageField} {ctx : Context} {rt : Runtime}
    {S : SymState} (hrel : ExprRel ρ fields ctx rt S) {x : String} {k : Nat}
    (hk : mapOf? fields x = some k) {w : Nat} (hw : w < wordSize) :
    rt.loadStorageIndex ctx x (.word w) =
      .ok (.word (Writes.store ρ S.writes (solHash w k % wordSize))) := by
  obtain ⟨f, hf, rfl⟩ := mapOf?_spec hrel.fields hk
  have hsl : rt.state.loadSlot (solHash w f.slot) = Writes.store ρ S.writes (solHash w f.slot % wordSize) := by
    rw [← loadSlot_mod, hrel.store _ (Nat.mod_lt _ (by decide))]
  rcases hf.layout with hl | hl <;>
  simp [Runtime.loadStorageIndex, hf.find, hl, mappingStorageSlotForKey, coerceMappingKeyWordAs,
    Value.forceAbiLazy, Ty.coerceValue?, Value.asStorageWord?, norm_lt hw, bind, Except.bind,
    State.loadStorageLayoutAt, State.loadStorageLayoutAtFuel, loadStorageWordAs,
    Ty.storageValueFromWord?, mappingStorageSlot_eq, hsl, pure, Except.pure, StorageLayout.depth]

theorem eval_erase (ρ : Val) (fields : List StorageField) (ctx : Context) (rt : Runtime)
    (S : SymState) (hrel : ExprRel ρ fields ctx rt S) (e : Expr) :
    ∀ (gs : List WExpr) (v : WExpr) (fuel : Nat), eraseExpr fields S e = some (gs, v) →
      Expr.orderFuel e < fuel → Expr.evalFuel fuel ctx rt e = exprResult ρ gs v rt := by
  intro gs v fuel h hf
  obtain ⟨n, rfl⟩ : ∃ n, fuel = n + 1 := ⟨fuel - 1, by omega⟩
  cases e with
  | word w =>
    simp only [eraseExpr, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp [Expr.evalFuel, exprResult, WExpr.eval, normWord, SolidCore.Solidity.Shared.norm, modulus_eq]
    rfl
  | var x =>
    simp only [eraseExpr, Option.map_eq_some_iff, Prod.mk.injEq] at h
    obtain ⟨e, he, rfl, rfl⟩ := h
    have hl := hrel.locals x e he
    simp [Expr.evalFuel, exprResult, Runtime.lookupStorageBase?, hl, Runtime.derefMemoryValue]
    rfl
  | castOp k b e =>
    cases k
    case uintCleanup =>
      cases he : eraseExpr fields S e with
      | none => simp [eraseExpr, he] at h
      | some p =>
      obtain ⟨gs0, v0⟩ := p
      have ih := eval_erase ρ fields ctx rt S hrel e gs0 v0 n he
        (by simp [Expr.orderFuel] at hf; omega)
      have hv0 := v0.eval_lt ρ
      by_cases hb : b = 256
      · subst hb
        simp only [eraseExpr, he, Option.bind_eq_bind, Option.bind_some, ↓reduceIte,
          Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        simp only [Expr.evalFuel, ih, hrel.checked]
        unfold exprResult
        split
        · rfl
        · simp only [bind, EvmCompiler.Simulation.Interaction.bind, liftM, monadLift,
            MonadLift.monadLift, uintCleanup_256 _ hv0, SolI.ofExcept]
          rfl
      · by_cases hb2 : 0 < b ∧ b < 256
        · simp only [eraseExpr, he, Option.bind_eq_bind, Option.bind_some, hb, hb2, and_self,
            ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          simp only [Expr.evalFuel, ih, hrel.checked]
          unfold exprResult
          simp only [any_append, List.any_cons, List.any_nil, Bool.or_false]
          by_cases hg : gs0.any (fun g => g.eval ρ != 0) = true
          · simp only [hg, Bool.true_or, ↓reduceIte]
            rfl
          · simp only [hg, Bool.false_or, Bool.false_eq_true, ↓reduceIte]
            simp only [bind, EvmCompiler.Simulation.Interaction.bind, liftM, monadLift,
              MonadLift.monadLift, uintCleanup_lt _ _ hv0 hb2.1 (by omega), SolI.ofExcept]
            have hpos := Nat.two_pow_pos b
            have hm : (2 ^ b - 1) % wordSize = 2 ^ b - 1 :=
              Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.sub_lt hpos (by decide))
                (Nat.pow_le_pow_right (by decide) (by omega)))
            by_cases hc : v0.eval ρ < 2 ^ b
            · have hc' : ¬ 2 ^ b - 1 < v0.eval ρ := by omega
              simp [hc, WExpr.eval, BinOp.eval, hm, hc']
              try rfl
            · have hc' : 2 ^ b - 1 < v0.eval ρ := by omega
              simp [hc, WExpr.eval, BinOp.eval, hm, hc']
              try rfl
        · simp [eraseExpr, he, hb, hb2] at h
    case uintCast =>
      cases he : eraseExpr fields S e with
      | none => simp [eraseExpr, he] at h
      | some p =>
      obtain ⟨gs0, v0⟩ := p
      have ih := eval_erase ρ fields ctx rt S hrel e gs0 v0 n he
        (by simp [Expr.orderFuel] at hf; omega)
      have hv0 := v0.eval_lt ρ
      by_cases hb : b = 256
      · subst hb
        simp only [eraseExpr, he, Option.bind_eq_bind, Option.bind_some, ↓reduceIte,
          Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        simp only [Expr.evalFuel, ih]
        unfold exprResult
        split
        · rfl
        · simp only [bind, EvmCompiler.Simulation.Interaction.bind, liftM, monadLift,
            MonadLift.monadLift, uintCast_word _ _ hv0 (by decide) (Nat.le_refl _),
            Nat.mod_eq_of_lt hv0, SolI.ofExcept]
          rfl
      · by_cases hb2 : 0 < b ∧ b < 256
        · simp only [eraseExpr, he, Option.bind_eq_bind, Option.bind_some, hb, hb2, and_self,
            ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          simp only [Expr.evalFuel, ih]
          unfold exprResult
          split
          · rfl
          · simp only [bind, EvmCompiler.Simulation.Interaction.bind, liftM, monadLift,
              MonadLift.monadLift, uintCast_word _ _ hv0 hb2.1 (by omega), SolI.ofExcept,
              eval_and_pow ρ v0 (show b ≤ 256 by omega)]
            rfl
        · simp [eraseExpr, he, hb, hb2] at h
    all_goals simp [eraseExpr] at h
  | binary op l r =>
    cases hl : eraseExpr fields S l with
    | none => cases op <;> simp [eraseExpr, hl, binOf] at h
    | some pl =>
    cases hr : eraseExpr fields S r with
    | none => cases op <;> simp [eraseExpr, hl, hr, binOf] at h
    | some pr =>
    obtain ⟨gl, vl⟩ := pl
    obtain ⟨gr, vr⟩ := pr
    have hfl : Expr.orderFuel l < n := by simp [Expr.orderFuel] at hf; omega
    have hfr : Expr.orderFuel r < n := by simp [Expr.orderFuel] at hf; omega
    have ihl := eval_erase ρ fields ctx rt S hrel l gl vl n hl hfl
    have ihr := eval_erase ρ fields ctx rt S hrel r gr vr n hr hfr
    have hal := vl.eval_lt ρ
    have har := vr.eval_lt ρ
    cases op <;> simp only [eraseExpr, hl, hr, binOf, overflow, Option.bind_eq_bind,
      Option.bind_some, Option.some.injEq, Prod.mk.injEq, reduceCtorEq, Option.bind_none] at h
    all_goals first
      | (simp at h; done)
      | skip
    all_goals
      obtain ⟨rfl, rfl⟩ := h
      simp only [Expr.evalFuel, ihr, bind_exprResult, hrel.checked]
      unfold exprResult
      by_cases hgr : gr.any (fun g => g.eval ρ != 0) = true
      · simp [hgr, any_append]
      · simp only [hgr, Bool.false_eq_true, ↓reduceIte, ihl, bind_exprResult]
        by_cases hgl : gl.any (fun g => g.eval ρ != 0) = true
        · simp [hgl, any_append]
        · simp only [hgl, Bool.false_eq_true, ↓reduceIte]
          simp only [any_append, hgl, hgr, Bool.false_or, List.any_cons, List.any_nil,
            Bool.or_false, guard_add, guard_sub, guard_mul]
          simp only [pure, EvmCompiler.Simulation.Interaction.pure, bind,
            EvmCompiler.Simulation.Interaction.bind, liftM, monadLift, MonadLift.monadLift,
            apply_add _ _ hal har, apply_sub _ _ hal har, apply_mul _ _ hal har, apply_lt _ _ hal har,
            apply_gt _ _ hal har, apply_eq _ _ hal har, apply_bitAnd _ _ hal har,
            apply_bitOr _ _ hal har, apply_bitXor _ _ hal har]
          split <;> simp_all [SolI.ofExcept, WExpr.eval, BinOp.eval, Nat.mod_mod]
          all_goals first
            | exact add_wrap_lt hal har (by assumption)
            | exact add_nowrap_le (by assumption)
            | (split <;> simp_all <;> omega)
  | caller =>
    simp only [eraseExpr, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp only [Expr.evalFuel, exprResult, List.any_nil, Bool.false_eq_true, ↓reduceIte, WExpr.eval,
      hrel.sender, callerWord]
    rfl
  | storageRead m x idx =>
    cases m
    case element =>
      match idx, h with
      | [i], h =>
        simp only [eraseExpr, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq,
          Prod.mk.injEq] at h
        obtain ⟨k, hk, ⟨gs0, v0⟩, hi, rfl, rfl⟩ := h
        have ih := eval_erase ρ fields ctx rt S hrel i gs0 v0 n hi
          (by simp [Expr.orderFuel, Expr.listEvalFuel] at hf; omega)
        simp only [Expr.evalFuel, ih, bind_exprResult]
        unfold exprResult
        split
        · rfl
        · obtain ⟨f, hf, rfl⟩ := mapOf?_spec hrel.fields hk
          rw [loadIndex_map hrel hk (v0.eval_lt ρ), Writes.eval_read hrel.ok]
          simp only [WExpr.eval, hrel.hash, Nat.mod_eq_of_lt hf.slot]
          rfl
    all_goals
      cases idx <;> simp only [eraseExpr, Option.map_eq_some_iff, Prod.mk.injEq] at h
    all_goals first
      | (simp at h; done)
      | skip
    all_goals
      obtain ⟨⟨k, off, bytes⟩, hk, rfl, rfl⟩ := h
      obtain ⟨f, hfx, rfl, rfl, rfl⟩ := fieldOf?_spec hrel.fields hk
      have hsl := slot_read hrel hfx.slot
      have hw : rt.state.loadSlot f.slot < wordSize := by
        rw [hsl]; exact WExpr.eval_lt _ _
      simp only [Expr.evalFuel, loadHeader_field hfx hw, load_field hfx hw, bind,
        EvmCompiler.Simulation.Interaction.bind, liftM, monadLift, MonadLift.monadLift, SolI.ofExcept,
        exprResult, List.any_nil, Bool.false_eq_true, ↓reduceIte, hsl,
        readField_eval ρ _ hfx.fits hfx.bytes]
      try rfl
  | _ => simp [eraseExpr] at h

end SolidCore.Refinement.Generic


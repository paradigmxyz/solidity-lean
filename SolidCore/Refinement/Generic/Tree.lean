import SolarTV.Sem

/-!
# Symbolic outcomes of a call: the interface of the generic source stage

The generic source stage (`Generic.Stage`) relates SolidCore and solar's first lowered MIR
through one object both sides compute for a function of the fragment: a `Tree`, the outcome
of one external call as a function of its argument words, the callee's storage before the
call and the hash of two words.

* `WExpr` is a word over the call: a literal, an argument word, the initial value of a
  storage slot (`init` at a constant slot, `sinit` at a computed one), an EVM word operation of
  others, a select (`sel c a b` is `a` when `c` is not zero, else `b`), or the Keccak-256 hash
  of the 64 bytes of two words (`hash a b`, a mapping's slot `keccak256(abi.encode(key, slot))`),
  which is the call's `Val.hash`: each side says what it is (SolidCore's Keccak-256, the MIR
  oracle's). Every word is below `2 ^ 256` by construction (`WExpr.eval_lt`).
* `OByte` is one byte of output: a literal byte, or byte `i` (big-endian) of a word.
* `Tree` branches on words (`ite c t e` takes `t` when `c` is not zero) and ends in a
  `halt`: success or failure, the output bytes, the storage writes and the logs; a failure
  rolls its writes and logs back.

Storage writes (`Writes`) are (slot word, value word) pairs, the newest that writes a slot
first: a slot holds the value of the first pair whose slot word is it (`Writes.store`).
`Writes.set` drops the pairs of the same slot word and inserts the new pair, after the pairs of
smaller constant slots when its slot is constant, so that a list of constant slots is sorted
with one entry per slot. `Writes.read` is the word a slot holds after the writes: the value of a
pair of the same slot word, past pairs of other constant slots, and a select on the equality of
the slot words otherwise, since a computed slot may be any slot (`Writes.eval_read`).

`Tree.eval` gives the `Res` of a call: success, output, logs and the storage after it. The
source side (`Generic.Source`) proves that SolidCore's interpreter runs a function of the
fragment as the tree its erasure computes; the target side (`Generic.Mir`) proves that the
lowered MIR runs as the tree its symbolic execution computes. The two trees are compared by
`Tree.canon` (Simp.lean, after `Tree.norm` here) and `Tree.beq`, equality as a `Bool`, which the
kernel evaluates.
-/

namespace SolidCore.Refinement.Generic

/-- The number of 256-bit words. -/
abbrev wordSize : Nat := 2 ^ 256

/-- The account that sends every call, as both sides of the stage take it: SolidCore's
`callerAddress`, and the MIR oracle's caller under `CallerOk`. -/
def callerWord : Nat := 0x2000

/-- The binary word operations of the fragment. -/
inductive BinOp where
  | add | sub | mul | div | lt | gt | eq | and | or | xor | shl | shr | byte
  deriving DecidableEq, Repr

/-- The unary word operations of the fragment. -/
inductive UnOp where
  | iszero | not
  deriving DecidableEq, Repr

/-- A binary operation on words below `2 ^ 256`, as the EVM computes it: `shl s v`, `shr s v`
and `byte i v` take the shift or the byte index first. -/
def BinOp.eval : BinOp → Nat → Nat → Nat
  | .add, a, b => (a + b) % wordSize
  | .sub, a, b => (a + (wordSize - b)) % wordSize
  | .mul, a, b => (a * b) % wordSize
  | .div, a, b => if b = 0 then 0 else a / b
  | .lt, a, b => if a < b then 1 else 0
  | .gt, a, b => if b < a then 1 else 0
  | .eq, a, b => if a = b then 1 else 0
  | .and, a, b => a &&& b
  | .or, a, b => a ||| b
  | .xor, a, b => a ^^^ b
  | .shl, a, b => if a < 256 then b * 2 ^ a % wordSize else 0
  | .shr, a, b => if a < 256 then b / 2 ^ a else 0
  | .byte, a, b => if a < 32 then b / 256 ^ (31 - a) % 256 else 0

/-- A unary operation on a word below `2 ^ 256`. -/
def UnOp.eval : UnOp → Nat → Nat
  | .iszero, a => if a = 0 then 1 else 0
  | .not, a => wordSize - 1 - a

/-- A word of the call. -/
inductive WExpr where
  | lit (n : Nat)
  | arg (i : Nat)
  | init (slot : Nat)
  | un (op : UnOp) (a : WExpr)
  | bin (op : BinOp) (a b : WExpr)
  /-- The initial value of the slot the word names. -/
  | sinit (k : WExpr)
  /-- The second word when the first is not zero, else the third. -/
  | sel (c a b : WExpr)
  /-- The hash of the 64 bytes of the two words, big-endian (`Val.hash`). -/
  | hash (a b : WExpr)
  /-- The account that sent the call (`msg.sender`), symbolic: `Val.caller`. -/
  | caller
  deriving DecidableEq, Repr

/-- What a call reads: its argument words, the callee's storage before it, and the hash of two
words, `keccak256(abi.encode(a, b))` (SolidCore's on the source side, the oracle's on the target
side, which agree under `HashOk`). -/
structure Val where
  args : List Nat
  store : Nat → Nat
  hash : Nat → Nat → Nat
  /-- The caller's address, the value of `WExpr.caller`. -/
  caller : Nat

/-- The value of a word of the call, below `2 ^ 256`. -/
def WExpr.eval (ρ : Val) : WExpr → Nat
  | .lit n => n % wordSize
  | .arg i => ρ.args.getD i 0 % wordSize
  | .init k => ρ.store k % wordSize
  | .un op a => op.eval (a.eval ρ) % wordSize
  | .bin op a b => op.eval (a.eval ρ) (b.eval ρ) % wordSize
  | .sinit k => ρ.store (k.eval ρ) % wordSize
  | .sel c a b => if c.eval ρ = 0 then b.eval ρ else a.eval ρ
  | .hash a b => ρ.hash (a.eval ρ) (b.eval ρ) % wordSize
  | .caller => ρ.caller % wordSize

theorem WExpr.eval_lt (ρ : Val) : ∀ e : WExpr, e.eval ρ < wordSize
  | .sel c a b => by
    simp only [WExpr.eval]
    split
    · exact WExpr.eval_lt ρ b
    · exact WExpr.eval_lt ρ a
  | .lit _ | .arg _ | .init _ | .un _ _ | .bin _ _ _ | .sinit _ | .hash _ _ | .caller =>
    Nat.mod_lt _ (by decide)

theorem eval_bin (ρ : Val) (op : BinOp) (a b : WExpr) :
    (WExpr.bin op a b).eval ρ = op.eval (a.eval ρ) (b.eval ρ) % wordSize := rfl

theorem eval_lit (ρ : Val) (n : Nat) : (WExpr.lit n).eval ρ = n % wordSize := rfl

/-- The storage a call starts from reads every slot modulo `2 ^ 256` as a word. -/
def Val.Ok (ρ : Val) : Prop := ∀ k, ρ.store (k % wordSize) % wordSize = ρ.store k

theorem Val.Ok.word {ρ : Val} (h : ρ.Ok) (k : Nat) : ρ.store k < wordSize := by
  rw [← h k]; exact Nat.mod_lt _ (by decide)

theorem Val.Ok.mod {ρ : Val} (h : ρ.Ok) (k : Nat) : ρ.store (k % wordSize) = ρ.store k := by
  rw [← h k, Nat.mod_eq_of_lt (h.word _)]

/-! ## Storage writes -/

/-- Storage writes: (slot word, value word) pairs, the newest of a slot first. -/
abbrev Writes := List (WExpr × WExpr)

/-- Two slot words that are constants, the first below the second. -/
def litLt : WExpr → WExpr → Bool
  | .lit a, .lit b => decide (a % wordSize < b % wordSize)
  | _, _ => false

/-- Two slot words that are different constants. -/
def litNe : WExpr → WExpr → Bool
  | .lit a, .lit b => decide (a % wordSize ≠ b % wordSize)
  | _, _ => false

theorem litLt_ne (ρ : Val) {a b : WExpr} (h : litLt a b = true) : a.eval ρ ≠ b.eval ρ := by
  unfold litLt at h
  split at h
  · simp only [decide_eq_true_eq] at h
    simp only [WExpr.eval]
    omega
  · simp at h

theorem litNe_ne (ρ : Val) {a b : WExpr} (h : litNe a b = true) : a.eval ρ ≠ b.eval ρ := by
  unfold litNe at h
  split at h
  · simp only [decide_eq_true_eq] at h
    simpa [WExpr.eval] using h
  · simp at h

/-- Insert the newest write of slot `k` among writes of other slots: after the writes of smaller
constant slots. -/
def Writes.ins : Writes → WExpr → WExpr → Writes
  | [], k, e => [(k, e)]
  | (k', e') :: rest, k, e =>
    if litLt k' k then (k', e') :: Writes.ins rest k e else (k, e) :: (k', e') :: rest

/-- Write `e` to the slot `k` names. -/
def Writes.set (ws : Writes) (k e : WExpr) : Writes :=
  Writes.ins (ws.filter fun p => p.1 != k) k e

/-- The storage after the writes, over the storage `ρ.store` before them; slots are words, so
slot `n` is slot `n % 2 ^ 256`. -/
def Writes.store (ρ : Val) : Writes → Nat → Nat
  | [], n => ρ.store n
  | (k, e) :: rest, n => if k.eval ρ = n % wordSize then e.eval ρ else Writes.store ρ rest n

/-- The word the slot `k` names holds after the writes. -/
def Writes.read : Writes → WExpr → WExpr
  | [], .lit n => .init (n % wordSize)
  | [], k => .sinit k
  | (k', e') :: rest, k =>
    if k' = k then e'
    else if litNe k' k then Writes.read rest k
    else .sel (.bin .eq k k') e' (Writes.read rest k)

theorem Writes.store_ins (ρ : Val) (k e : WExpr) (n : Nat) : ∀ ws : Writes,
    Writes.store ρ (ws.ins k e) n =
      if k.eval ρ = n % wordSize then e.eval ρ else Writes.store ρ ws n
  | [] => rfl
  | (k', e') :: rest => by
    simp only [Writes.ins]
    split
    · rename_i hlt
      have hne := litLt_ne ρ hlt
      simp only [Writes.store, Writes.store_ins ρ k e n rest]
      by_cases h1 : k'.eval ρ = n % wordSize
      · have : ¬ k.eval ρ = n % wordSize := fun h2 => hne (h1.trans h2.symm)
        simp [h1, this]
      · simp [h1]
    · rfl

theorem Writes.store_filter (ρ : Val) (k : WExpr) (n : Nat) (hn : ¬ k.eval ρ = n % wordSize) :
    ∀ ws : Writes, Writes.store ρ (ws.filter fun p => p.1 != k) n = Writes.store ρ ws n
  | [] => rfl
  | (k', e') :: rest => by
    simp only [List.filter_cons]
    split
    · simp only [Writes.store, Writes.store_filter ρ k n hn rest]
    · rename_i h
      simp only [bne_iff_ne, ne_eq, Decidable.not_not] at h
      subst h
      simp only [Writes.store, hn, ↓reduceIte, Writes.store_filter ρ k' n hn rest]

theorem Writes.store_set (ρ : Val) (ws : Writes) (k e : WExpr) (n : Nat) :
    Writes.store ρ (ws.set k e) n =
      if k.eval ρ = n % wordSize then e.eval ρ else Writes.store ρ ws n := by
  unfold Writes.set
  rw [Writes.store_ins]
  split
  · rfl
  · rename_i h
    exact Writes.store_filter ρ k n h ws

theorem Writes.store_word {ρ : Val} (hρ : ρ.Ok) (n : Nat) : ∀ ws : Writes,
    Writes.store ρ ws n < wordSize
  | [] => hρ.word n
  | (k, e) :: rest => by
    simp only [Writes.store]
    split
    · exact e.eval_lt ρ
    · exact Writes.store_word hρ n rest

theorem Writes.store_mod (ρ : Val) (hρ : ρ.Ok) (n : Nat) : ∀ ws : Writes,
    Writes.store ρ ws (n % wordSize) = Writes.store ρ ws n
  | [] => hρ.mod n
  | (k, e) :: rest => by
    simp only [Writes.store, Nat.mod_mod, Writes.store_mod ρ hρ n rest]

theorem Writes.eval_read {ρ : Val} (hρ : ρ.Ok) (k : WExpr) : ∀ ws : Writes,
    (ws.read k).eval ρ = Writes.store ρ ws (k.eval ρ)
  | [] => by cases k <;> exact Nat.mod_eq_of_lt (hρ.word _)
  | (k', e') :: rest => by
    have hk := k.eval_lt ρ
    simp only [Writes.read, Writes.store, Nat.mod_eq_of_lt hk]
    split
    · rename_i h; subst h; simp
    · split
      · rename_i _ hne
        have := litNe_ne ρ hne
        rw [if_neg this, Writes.eval_read hρ k rest]
      · simp only [WExpr.eval, BinOp.eval, Writes.eval_read hρ k rest]
        by_cases h : k.eval ρ = k'.eval ρ
        · simp [h]
        · simp [h, Ne.symm h]

/-! ## Output and logs -/

/-- One byte of output. -/
inductive OByte where
  | lit (b : Nat)
  | byteOf (e : WExpr) (i : Nat)
  deriving DecidableEq, Repr

/-- The value of a byte of output: byte `i` of a word counts from the most significant. -/
def OByte.eval (ρ : Val) : OByte → Nat
  | .lit b => b % 256
  | .byteOf e i => e.eval ρ / 256 ^ (31 - i) % 256

/-- The 32 bytes of a word, big-endian. -/
def wordOBytes (e : WExpr) : List OByte := (List.range 32).map (OByte.byteOf e)

/-- The 32 bytes of a literal word, big-endian. -/
def litBytes (len n : Nat) : List OByte :=
  (List.range len).map fun i => OByte.lit (n / 256 ^ (len - 1 - i) % 256)

/-- The revert data of `Panic(code)`: its selector and the code as a word. -/
def panicBytes (code : Nat) : List OByte := litBytes 4 0x4e487b71 ++ litBytes 32 code

/-- A log: its topics and its data. -/
structure Log where
  topics : List WExpr
  data : List OByte
  deriving DecidableEq, Repr

/-- What a log shows: its topics' words and its data bytes. -/
def Log.eval (ρ : Val) (l : Log) : List Nat × List Nat :=
  (l.topics.map (WExpr.eval ρ), l.data.map (OByte.eval ρ))

/-- The outcome of a call of a function of the fragment. -/
inductive Tree where
  | halt (success : Bool) (out : List OByte) (writes : Writes) (logs : List Log)
  | ite (c : WExpr) (t e : Tree)
  deriving DecidableEq, Repr

/-- Equality of trees as a `Bool`, by structural recursion on both: the kernel evaluates it on the
large trees of a call where it gets stuck on the derived `DecidableEq Tree`. -/
def Tree.beq : Tree → Tree → Bool
  | .halt s o w l, .halt s' o' w' l' => s == s' && decide (o = o') && decide (w = w') && decide (l = l')
  | .ite c t e, .ite c' t' e' => decide (c = c') && Tree.beq t t' && Tree.beq e e'
  | _, _ => false

theorem Tree.eq_of_beq : ∀ {a b : Tree}, Tree.beq a b = true → a = b
  | .halt _ _ _ _, .halt _ _ _ _, h => by
    simp only [Tree.beq, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
    obtain ⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩ := h
    rfl
  | .ite _ _ _, .ite _ _ _, h => by
    simp only [Tree.beq, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨rfl, ht⟩, he⟩ := h
    rw [Tree.eq_of_beq ht, Tree.eq_of_beq he]
  | .halt _ _ _ _, .ite _ _ _, h => by simp [Tree.beq] at h
  | .ite _ _ _, .halt _ _ _ _, h => by simp [Tree.beq] at h

/-- What a call shows: whether it succeeded, its output, its logs and the storage after it. -/
structure Res where
  success : Bool
  output : List Nat
  logs : List (List Nat × List Nat)
  store : Nat → Nat

/-- The result of a call: the tree's branch the call's words take. A failure keeps the storage
before the call and logs nothing. -/
def Tree.eval (ρ : Val) : Tree → Res
  | .halt ok out ws ls =>
    { success := ok, output := out.map (OByte.eval ρ),
      logs := if ok then ls.map (Log.eval ρ) else [],
      store := if ok then Writes.store ρ ws else ρ.store }
  | .ite c t e => if c.eval ρ = 0 then e.eval ρ else t.eval ρ

/-- What a call shows outside, from its result. -/
def Res.obs (R : Res) : SolarTV.Observable :=
  { success := R.success, output := R.output, logs := R.logs, storage := R.store }

/-! ## Normal forms

Both sides of the generic source stage compute a tree; `Tree.norm` folds the constant words
of a tree (`mkBin`, `mkUn`, selects on constants), the bytes of constant words and the branches
on constants, so that the kernel compares two trees by `=` on their normal forms.
`Tree.eval_norm`: a tree and its normal form give every call the same result. -/

/-- A binary operation, folded when both operands are constants. -/
def mkBin (op : BinOp) : WExpr → WExpr → WExpr
  | .lit a, .lit b => .lit (op.eval (a % wordSize) (b % wordSize) % wordSize)
  | a, b => .bin op a b

/-- A unary operation, folded on a constant. -/
def mkUn (op : UnOp) : WExpr → WExpr
  | .lit a => .lit (op.eval (a % wordSize) % wordSize)
  | a => .un op a

theorem eval_mkBin (ρ : Val) (op : BinOp) (a b : WExpr) :
    (mkBin op a b).eval ρ = (WExpr.bin op a b).eval ρ := by
  unfold mkBin
  split <;> simp [WExpr.eval, Nat.mod_mod]

theorem eval_mkUn (ρ : Val) (op : UnOp) (a : WExpr) :
    (mkUn op a).eval ρ = (WExpr.un op a).eval ρ := by
  unfold mkUn
  split <;> simp [WExpr.eval, Nat.mod_mod]

/-- The constant a word is, if it is one. -/
def WExpr.lit? : WExpr → Option Nat
  | .lit n => some n
  | _ => none

theorem WExpr.eq_of_lit? {e : WExpr} {n : Nat} (h : e.lit? = some n) : e = .lit n := by
  cases e <;> simp_all [WExpr.lit?]

/-- A select, taken when its condition is a constant. -/
def mkSel (c a b : WExpr) : WExpr :=
  match c with
  | .lit n => if n % wordSize = 0 then b else a
  | _ => .sel c a b

theorem eval_mkSel (ρ : Val) (c a b : WExpr) : (mkSel c a b).eval ρ = (WExpr.sel c a b).eval ρ := by
  unfold mkSel
  split
  · simp only [WExpr.eval]
    split <;> simp_all
  · rfl

/-- A word with its constant operations folded. -/
def WExpr.norm : WExpr → WExpr
  | .lit n => .lit (n % wordSize)
  | .arg i => .arg i
  | .init k => .init k
  | .un op a => mkUn op a.norm
  | .bin op a b => mkBin op a.norm b.norm
  | .sinit k => .sinit k.norm
  | .sel c a b => mkSel c.norm a.norm b.norm
  | .hash a b => .hash a.norm b.norm
  | .caller => .caller

theorem WExpr.eval_norm (ρ : Val) : ∀ e : WExpr, e.norm.eval ρ = e.eval ρ
  | .lit n => by simp [WExpr.norm, WExpr.eval, Nat.mod_mod]
  | .arg i => rfl
  | .init k => rfl
  | .un op a => by rw [WExpr.norm, eval_mkUn]; simp only [WExpr.eval, WExpr.eval_norm ρ a]
  | .bin op a b => by
    rw [WExpr.norm, eval_mkBin]; simp only [WExpr.eval, WExpr.eval_norm ρ a, WExpr.eval_norm ρ b]
  | .sinit k => by simp only [WExpr.norm, WExpr.eval, WExpr.eval_norm ρ k]
  | .sel c a b => by
    rw [WExpr.norm, eval_mkSel]
    simp only [WExpr.eval, WExpr.eval_norm ρ c, WExpr.eval_norm ρ a, WExpr.eval_norm ρ b]
  | .hash a b => by simp only [WExpr.norm, WExpr.eval, WExpr.eval_norm ρ a, WExpr.eval_norm ρ b]
  | .caller => rfl

/-- A byte of output, a literal when its word is a constant. -/
def OByte.norm : OByte → OByte
  | .lit b => .lit (b % 256)
  | .byteOf e i =>
    match e.norm with
    | .lit n => .lit (n % wordSize / 256 ^ (31 - i) % 256)
    | e' => .byteOf e' i

theorem OByte.eval_norm (ρ : Val) (b : OByte) : b.norm.eval ρ = b.eval ρ := by
  cases b with
  | lit b => simp [OByte.norm, OByte.eval, Nat.mod_mod]
  | byteOf e i =>
    have h := WExpr.eval_norm ρ e
    simp only [OByte.norm]
    split
    · rename_i n hn
      rw [hn] at h
      simp only [OByte.eval, ← h, WExpr.eval, Nat.mod_mod]
    · simp only [OByte.eval, h]

/-- The writes with `f` applied to their slot and value words. -/
def Writes.mapW (f : WExpr → WExpr) (ws : Writes) : Writes := ws.map fun p => (f p.1, f p.2)

theorem Writes.store_mapW (ρ : Val) (f : WExpr → WExpr) (hf : ∀ e, (f e).eval ρ = e.eval ρ) :
    ∀ ws : Writes, Writes.store ρ (ws.mapW f) = Writes.store ρ ws
  | [] => rfl
  | (k, e) :: rest => by
    funext n
    have ih := Writes.store_mapW ρ f hf rest
    simp only [Writes.mapW, List.map_cons, Writes.store, hf] at ih ⊢
    rw [ih]

/-- Storage writes with their words in normal form. -/
def Writes.norm (ws : Writes) : Writes := ws.mapW WExpr.norm

theorem Writes.store_norm (ρ : Val) (ws : Writes) : Writes.store ρ ws.norm = Writes.store ρ ws :=
  Writes.store_mapW ρ _ (WExpr.eval_norm ρ) ws

/-- A log with `f` applied to its topics and `g` to its data bytes. -/
def Log.mapL (f : WExpr → WExpr) (g : OByte → OByte) (l : Log) : Log :=
  ⟨l.topics.map f, l.data.map g⟩

theorem Log.eval_mapL (ρ : Val) (f : WExpr → WExpr) (g : OByte → OByte)
    (hf : ∀ e, (f e).eval ρ = e.eval ρ) (hg : ∀ b, (g b).eval ρ = b.eval ρ) (l : Log) :
    (l.mapL f g).eval ρ = l.eval ρ := by
  simp only [Log.mapL, Log.eval, List.map_map]
  congr 1
  · exact List.map_congr_left fun e _ => hf e
  · exact List.map_congr_left fun b _ => hg b

/-- A tree in normal form: constants folded, branches on constants taken. -/
def Tree.norm : Tree → Tree
  | .halt ok out ws ls => .halt ok (out.map OByte.norm) ws.norm (ls.map (Log.mapL WExpr.norm OByte.norm))
  | .ite c t e =>
    match c.norm.lit? with
    | some n => if n % wordSize = 0 then e.norm else t.norm
    | none => .ite c.norm t.norm e.norm

theorem Tree.eval_norm (ρ : Val) : ∀ T : Tree, T.norm.eval ρ = T.eval ρ
  | .halt ok out ws ls => by
    simp only [Tree.norm, Tree.eval, List.map_map, Writes.store_norm]
    congr 2
    · funext b
      exact OByte.eval_norm ρ b
    · congr 1
      funext l
      exact Log.eval_mapL ρ _ _ (WExpr.eval_norm ρ) (OByte.eval_norm ρ) l
  | .ite c t e => by
    have hc := WExpr.eval_norm ρ c
    simp only [Tree.norm]
    split
    · rename_i n hn
      rw [WExpr.eq_of_lit? hn] at hc
      simp only [WExpr.eval] at hc
      simp only [Tree.eval, ← hc]
      split
      · exact Tree.eval_norm ρ e
      · exact Tree.eval_norm ρ t
    · simp only [Tree.eval, hc, Tree.eval_norm ρ t, Tree.eval_norm ρ e]

/-! ## Sign extension

A signed parameter of `b` bits (`int8` for `b = 8`) holds a word that is its own sign extension from
bit `b - 1`. Solar checks it with `xor x (signextend k x)` for `b = 8 (k + 1)`; the tree has no
`signextend`, so `sextW` writes it with the fragment's operations, `((x + h) & (2^b - 1)) - h` for
`h = 2^(b - 1)`, and `sextGuard` is the check. -/

/-- The sign extension of the low `b` bits of the word `a`, for `0 < b < 256`. -/
def sextNat (b a : Nat) : Nat :=
  if 2 ^ (b - 1) ≤ a % 2 ^ b then a % 2 ^ b + (wordSize - 2 ^ b) else a % 2 ^ b

/-- The sign extension of the low `b` bits of a word, from the fragment's operations. -/
def sextW (b : Nat) (x : WExpr) : WExpr :=
  .bin .sub (.bin .and (.bin .add x (.lit (2 ^ (b - 1)))) (.lit (2 ^ b - 1))) (.lit (2 ^ (b - 1)))

/-- Nonzero exactly when the word is not its own sign extension from `b` bits. -/
def sextGuard (b : Nat) (x : WExpr) : WExpr := .bin .xor x (sextW b x)

theorem pow_facts {b : Nat} (hb : 0 < b ∧ b < 256) :
    2 ^ b = 2 * 2 ^ (b - 1) ∧ 2 ^ b < wordSize ∧ 2 ^ b ∣ wordSize ∧ 0 < 2 ^ (b - 1) := by
  refine ⟨?_, ?_, ?_, Nat.two_pow_pos _⟩
  · rw [← Nat.pow_succ']; congr 1; omega
  · exact Nat.pow_lt_pow_right (by decide) hb.2
  · exact Nat.pow_dvd_pow 2 (by omega)

theorem eval_sextW (ρ : Val) {b : Nat} (hb : 0 < b ∧ b < 256) (x : WExpr) :
    (sextW b x).eval ρ = sextNat b (x.eval ρ) := by
  obtain ⟨hP, hPW, hdvd, hh⟩ := pow_facts hb
  have ha := x.eval_lt ρ
  simp only [sextW, WExpr.eval, BinOp.eval]
  generalize x.eval ρ = a at *
  have h1 : 2 ^ (b - 1) % wordSize = 2 ^ (b - 1) := Nat.mod_eq_of_lt (by omega)
  have h2 : (2 ^ b - 1) % wordSize = 2 ^ b - 1 := Nat.mod_eq_of_lt (by omega)
  simp only [h1, h2, Nat.mod_mod, Nat.and_two_pow_sub_one_eq_mod, Nat.mod_mod_of_dvd _ hdvd]
  rw [Nat.mod_eq_of_lt (show (a + 2 ^ (b - 1)) % 2 ^ b < wordSize from
    Nat.lt_trans (Nat.mod_lt _ (by omega)) hPW)]
  rw [Nat.add_mod a, Nat.mod_eq_of_lt (show 2 ^ (b - 1) < 2 ^ b by omega)]
  unfold sextNat
  have hy := Nat.mod_lt a (show 0 < 2 ^ b by omega)
  generalize a % 2 ^ b = y at *
  generalize 2 ^ (b - 1) = h at *
  generalize 2 ^ b = P at *
  subst hP
  generalize wordSize = W at *
  by_cases hc : h ≤ y
  · rw [if_pos hc, Nat.mod_eq_sub_mod (show 2 * h ≤ y + h by omega),
      Nat.mod_eq_of_lt (show y + h - 2 * h < 2 * h by omega),
      show y + h - 2 * h + (W - h) = y + (W - 2 * h) by omega]
    exact Nat.mod_eq_of_lt (by omega)
  · rw [if_neg hc, Nat.mod_eq_of_lt (show y + h < 2 * h by omega),
      show y + h + (W - h) = y + W by omega, Nat.add_mod_right]
    exact Nat.mod_eq_of_lt (by omega)

theorem sextNat_lt {b : Nat} (hb : 0 < b ∧ b < 256) (a : Nat) : sextNat b a < wordSize := by
  obtain ⟨hP, hPW, -, -⟩ := pow_facts hb
  have := Nat.mod_lt a (Nat.two_pow_pos b)
  unfold sextNat
  generalize 2 ^ (b - 1) = h at *
  generalize 2 ^ b = P at *
  split <;> omega

theorem xor_zero {a b : Nat} (h : a ^^^ b = 0) : a = b := by
  apply Nat.eq_of_testBit_eq
  intro i
  have := congrArg (Nat.testBit · i) h
  simp only [Nat.testBit_xor, Nat.zero_testBit] at this
  revert this
  cases a.testBit i <;> cases b.testBit i <;> decide

theorem eval_sextGuard (ρ : Val) {b : Nat} (hb : 0 < b ∧ b < 256) (x : WExpr) :
    (sextGuard b x).eval ρ = 0 ↔ sextNat b (x.eval ρ) = x.eval ρ := by
  have ha : x.eval ρ < 2 ^ 256 := x.eval_lt ρ
  have hs : sextNat b (x.eval ρ) < 2 ^ 256 := sextNat_lt hb _
  simp only [sextGuard, WExpr.eval, BinOp.eval, eval_sextW ρ hb]
  rw [show wordSize = 2 ^ 256 from rfl, Nat.mod_eq_of_lt (Nat.xor_lt_two_pow ha hs), ]
  exact ⟨fun h => (xor_zero h).symm, fun h => by rw [h, Nat.xor_self]⟩


theorem sextNat_eq_iff {b w : Nat} (hb : 0 < b ∧ b < 256) (hw : w < wordSize) :
    sextNat b w = w ↔ (w < 2 ^ (b - 1) ∨ wordSize - 2 ^ (b - 1) ≤ w) := by
  obtain ⟨hP, hPW, ⟨m, hm⟩, hh⟩ := pow_facts hb
  have hy := Nat.mod_lt w (Nat.two_pow_pos b)
  constructor
  · unfold sextNat
    intro he
    split at he <;> omega
  · rintro (hlt | hge)
    · have : w % 2 ^ b = w := Nat.mod_eq_of_lt (by omega)
      unfold sextNat; rw [this, if_neg (by omega)]
    · have hm1 : wordSize - 2 ^ b = 2 ^ b * (m - 1) := by rw [hm, Nat.mul_sub_one]
      have hwt : w = (w - (wordSize - 2 ^ b)) + 2 ^ b * (m - 1) := by omega
      have hmod : w % 2 ^ b = w - (wordSize - 2 ^ b) := by
        rw [hwt, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]; omega
      unfold sextNat; rw [hmod, if_pos (by omega)]; omega


/-- The sign of a word, its top bit: `shr 255 a`, as solar's `slt a 0`. -/
def sneg (a : WExpr) : WExpr := .bin .shr (.lit 255) a

/-- The overflow check of a checked signed `a + b`: operands of one sign and a sum of the other. -/
def saddGuard (a b : WExpr) : WExpr :=
  .bin .and (.bin .eq (sneg a) (sneg b)) (.bin .xor (sneg (.bin .add a b)) (sneg a))

theorem eval_sneg (ρ : Val) (a : WExpr) :
    (sneg a).eval ρ = if 2 ^ 255 ≤ a.eval ρ then 1 else 0 := by
  have ha := a.eval_lt ρ
  have h1 : (sneg a).eval ρ = a.eval ρ / 2 ^ 255 % wordSize := by
    simp [sneg, WExpr.eval, BinOp.eval, show (255 : Nat) % wordSize = 255 by decide]
  rw [h1]
  generalize a.eval ρ = x at *
  have hW : wordSize = 2 * 2 ^ 255 := by decide
  by_cases h : 2 ^ 255 ≤ x
  · rw [if_pos h, Nat.div_eq_of_lt_le (k := 1) (n := 2 ^ 255) (by omega) (by omega)]
    exact Nat.mod_eq_of_lt (by decide)
  · rw [if_neg h, Nat.div_eq_of_lt (by omega), Nat.zero_mod]

theorem eval_saddGuard (ρ : Val) (a b : WExpr) :
    (saddGuard a b).eval ρ ≠ 0 ↔
      ((2 ^ 255 ≤ a.eval ρ ↔ 2 ^ 255 ≤ b.eval ρ) ∧
        ((2 ^ 255 ≤ (a.eval ρ + b.eval ρ) % wordSize) ↔ ¬ 2 ^ 255 ≤ a.eval ρ)) := by
  have e1 : (saddGuard a b).eval ρ =
      ((if (sneg a).eval ρ = (sneg b).eval ρ then 1 else 0) % wordSize &&&
        ((sneg (.bin .add a b)).eval ρ ^^^ (sneg a).eval ρ) % wordSize) % wordSize := rfl
  rw [e1, eval_sneg, eval_sneg, eval_sneg]
  simp only [WExpr.eval, BinOp.eval, Nat.mod_mod]
  generalize a.eval ρ = x
  generalize b.eval ρ = y
  by_cases h1 : 2 ^ 255 ≤ x <;> by_cases h2 : 2 ^ 255 ≤ y <;>
    by_cases h3 : 2 ^ 255 ≤ (x + y) % wordSize <;>
    simp only [h1, h2, h3, ↓reduceIte] <;> decide




/-! ## Powers of two

`(2 ^ j) ^ k mod 2 ^ 256` from the fragment's operations, for `0 < j < 256`: `shl k 1` for `j = 1`,
and otherwise `0` when `k > 255` and `shl (j * k) 1` below (where `j * k` cannot wrap), `j * k`
written `add k k` for `j = 2` as solar strength-reduces it. -/

def powTwoW (j : Nat) (k : WExpr) : WExpr :=
  if j = 1 then .bin .shl k (.lit 1)
  else .sel (.bin .gt k (.lit 255)) (.lit 0)
    (.bin .shl (if j = 2 then .bin .add k k else .bin .mul (.lit j) k) (.lit 1))

theorem pow2_mod_big {n : Nat} (h : 256 ≤ n) : 2 ^ n % wordSize = 0 :=
  Nat.mod_eq_zero_of_dvd (Nat.pow_dvd_pow 2 h)

theorem shl_one_eval (s : Nat) : BinOp.shl.eval s 1 % wordSize = 2 ^ s % wordSize := by
  simp only [BinOp.eval, Nat.one_mul]
  split
  · exact Nat.mod_mod _ _
  · rw [pow2_mod_big (by omega)]; rfl

theorem eval_powTwoW (ρ : Val) {j : Nat} (hj : 0 < j ∧ j < 256) (k : WExpr) :
    (powTwoW j k).eval ρ = (2 ^ j) ^ (k.eval ρ) % wordSize := by
  have hk := k.eval_lt ρ
  rw [← Nat.pow_mul]
  unfold powTwoW
  split
  · rename_i h1
    subst h1
    show BinOp.shl.eval (k.eval ρ) (1 % wordSize) % wordSize = _
    rw [show (1 : Nat) % wordSize = 1 from rfl, shl_one_eval, Nat.one_mul]
  · have hc : (WExpr.bin .gt k (.lit 255)).eval ρ = if 255 < k.eval ρ then 1 else 0 := by
      simp only [WExpr.eval, BinOp.eval, show (255 : Nat) % wordSize = 255 from rfl]
      split <;> rfl
    show (if (WExpr.bin .gt k (.lit 255)).eval ρ = 0 then _ else _) = _
    rw [hc]
    by_cases hgt : 255 < k.eval ρ
    · rw [if_pos hgt, if_neg (by decide)]
      rw [pow2_mod_big (by
        have : 1 * k.eval ρ ≤ j * k.eval ρ := Nat.mul_le_mul_right _ (by omega)
        omega)]
      rfl
    · rw [if_neg hgt, if_pos rfl]
      have hle : k.eval ρ ≤ 255 := by omega
      have hs : (if j = 2 then WExpr.bin .add k k else WExpr.bin .mul (.lit j) k).eval ρ =
          j * k.eval ρ := by
        split
        · rename_i h2; subst h2
          have hlt : k.eval ρ + k.eval ρ < wordSize := by show _ < 2 ^ 256; omega
          simp only [WExpr.eval, BinOp.eval, Nat.mod_mod, Nat.mod_eq_of_lt hlt]; omega
        · simp only [WExpr.eval, BinOp.eval, Nat.mod_eq_of_lt (show j < wordSize by
            show _ < 2 ^ 256; omega)]
          have : j * k.eval ρ ≤ 255 * 255 := Nat.mul_le_mul (by omega) hle
          have hlt : j * k.eval ρ < wordSize := by show _ < 2 ^ 256; omega
          rw [Nat.mod_mod, Nat.mod_eq_of_lt hlt]
      show BinOp.shl.eval _ (1 % wordSize) % wordSize = _
      rw [hs, show (1 : Nat) % wordSize = 1 from rfl, shl_one_eval]

end SolidCore.Refinement.Generic

import EthLib.Execution.Proofs.Evm.Logic.Log
import SolidCore.Refinement.Solar.Assemble
import SolidCore.Refinement.Compose
import SolidCore.Refinement.Evm.WideStorage

/-!
# EVM IR to bytecode, the simulation

The proof of `stage_of_check_env` (and of `stage_of_check_all`, `stage_of_check_eth` and
`stage_of_check`, its forms for programs that read neither the caller nor a hash, for EthLib's
caller and hash, and on calls with no value): EthLib's interpreter simulates SolarTV's EVM IR
semantics on every program and code the checker of `Assemble.lean` accepts. A walk segment
(`Seg`) is the checker's lockstep decoding between two offsets; the stack relation (`SR`)
relates SolarTV's stack to EthLib's word by word at the checker's types (a return label is its
block's number in SolarTV and its offset in EthLib); the invariant (`Inv`) relates SolarTV's
memory to EthLib's frame at the offset of the next item, with 22100 gas (SSTORE's highest price)
for each item left and the price of memory up to the certificate's bound; and `Rel` relates
SolarTV's storage to the storage of EthLib's account of the frame, from any initial storage, and
EthLib's logs to SolarTV's world (`LogsRel`). Each item takes one unit of potential, and a jump
or a fall into the next block lands where the potential left bounds the target's, so a run
executes at most the first block's potential in items, and the gas and the stack bound follow
from that count.
-/

namespace SolidCore.Refinement.Solar.Assemble

open SolarTV.Assembly
open EthLib.Base EthLib.Execution EthLib.Execution.Evm EthLib.Execution.Evm.Logic GasCosts
open SolidCore.Refinement.Evm.Wide

/-! ## Walk segments -/

/-- The checker's walk from `pc` over `items`, ending at `pc'`. -/
inductive Seg (code : List Nat) (offset : Nat → Nat) : Nat → List Item → Nat → Prop
  | nil {pc : Nat} : Seg code offset pc [] pc
  | cons {pc next pc' : Nat} {item : Item} {items : List Item} :
      decode code pc = some (item.expected offset, next) →
      (∀ label, item = .label label → offset label = pc) →
      Seg code offset next items pc' → Seg code offset pc (item :: items) pc'

theorem seg_of_walk {code : List Nat} {offset : Nat → Nat} {pc : Nat} {items : List Item}
    {stream : List (Nat × SolarTV.Assembly.Instr)} (w : Walk code offset pc items stream) :
    Seg code offset pc items code.length := by
  induction w with
  | nil => exact .nil
  | cons d l _ ih => exact .cons d l ih

theorem Seg.split {code : List Nat} {offset : Nat → Nat} :
    ∀ {pc pc'' : Nat} {A B : List Item}, Seg code offset pc (A ++ B) pc'' →
      ∃ pc', Seg code offset pc A pc' ∧ Seg code offset pc' B pc''
  | pc, _, [], _, h => ⟨pc, .nil, h⟩
  | _, _, a :: A, B, h => by
    rw [List.cons_append] at h
    cases h with
    | cons d l rest =>
      obtain ⟨pc', h1, h2⟩ := Seg.split rest
      exact ⟨pc', .cons d l h1, h2⟩

theorem Seg.nil_end {code : List Nat} {offset : Nat → Nat} {pc pc' : Nat}
    (h : Seg code offset pc [] pc') : pc = pc' := by
  cases h; rfl

theorem decode_lt {code : List Nat} {pc : Nat} {x : SolarTV.Assembly.Instr × Nat}
    (h : decode code pc = some x) : pc < code.length := by
  unfold decode at h
  split at h
  · cases h
  · rename_i byte hb
    exact (List.getElem?_eq_some_iff.1 hb).1

/-! ## The lowered program -/

theorem lowerFrom_drop (p : Program) (c : Cert) {b : Nat} (hb : b < p.blocks.length) :
    lowerFrom p c b (p.blocks.drop b) =
      lowerBlock p c b p.blocks[b] ++ lowerFrom p c (b + 1) (p.blocks.drop (b + 1)) := by
  rw [List.drop_eq_getElem_cons hb]
  rfl

theorem lowerFrom_nil (p : Program) (c : Cert) {b : Nat} (hb : p.blocks.length ≤ b) :
    lowerFrom p c b (p.blocks.drop b) = [] := by
  rw [List.drop_eq_nil_of_le hb]
  rfl

theorem seg_lowerFrom {code : List Nat} {offset : Nat → Nat} {e : Nat} (p : Program) (c : Cert) :
    ∀ (k : Nat) (l : List (List Instr)) (b pc : Nat),
      Seg code offset pc (lowerFrom p c b l) e → k < l.length →
      ∃ pc', Seg code offset pc' (lowerFrom p c (b + k) (l.drop k)) e ∧
        (isTarget p c (b + k) = true → offset (b + k) = pc')
  | _, [], _, _, _, hk => absurd hk (by simp)
  | 0, x :: l, b, pc, h, _ => by
    refine ⟨pc, by simpa using h, fun ht => ?_⟩
    simp only [Nat.add_zero] at ht ⊢
    simp only [lowerFrom, lowerBlock, ht, ite_true, List.cons_append] at h
    cases h with
    | cons _ l _ => exact l b rfl
  | k + 1, x :: l, b, pc, h, hk => by
    simp only [lowerFrom] at h
    obtain ⟨pc', -, h2⟩ := Seg.split h
    obtain ⟨pc'', h3, h4⟩ := seg_lowerFrom p c k l (b + 1) pc' h2 (by simp at hk; omega)
    rw [show b + (k + 1) = b + 1 + k by omega, List.drop_succ_cons]
    exact ⟨pc'', h3, h4⟩

/-! ## Stack types -/

/-- What a word of SolarTV's stack is to EthLib's at its type: the same word for data, the
offset of a block the certificate lists for a return label, anything where the type is
unknown. -/
def WR (c : Cert) : Ty → Word → Word → Prop
  | some false, x, y => y = x
  | some true, x, y => x.toNat ∈ c.rets ∧ y = BitVec.ofNat 256 (c.offset x.toNat)
  | none, _, _ => True

/-- SolarTV's stack and EthLib's have one height and agree word by word at their types. -/
def SR (c : Cert) (ty : List Ty) (S T : List Word) : Prop :=
  S.length = T.length ∧ ∀ i (h1 : i < S.length) (h2 : i < T.length), WR c (tyAt ty i) S[i] T[i]

theorem tyAt_tail (ty : List Ty) (i : Nat) : tyAt ty.tail i = tyAt ty (i + 1) := by
  cases ty <;> simp [tyAt]

theorem tyAt_cons_zero (τ : Ty) (ty : List Ty) : tyAt (τ :: ty) 0 = τ := by simp [tyAt]

theorem tyAt_cons_succ (τ : Ty) (ty : List Ty) (i : Nat) : tyAt (τ :: ty) (i + 1) = tyAt ty i := by
  simp [tyAt]

theorem SR.nil (c : Cert) (ty : List Ty) : SR c ty [] [] :=
  ⟨rfl, fun _ h => absurd h (by simp)⟩

theorem SR.uncons {c : Cert} {ty : List Ty} {x y : Word} {S T : List Word} :
    SR c ty (x :: S) (y :: T) ↔ WR c (tyAt ty 0) x y ∧ SR c ty.tail S T := by
  constructor
  · rintro ⟨hl, h⟩
    refine ⟨h 0 (by simp) (by simp), by simpa using hl, fun i h1 h2 => ?_⟩
    have := h (i + 1) (by simp; omega) (by simp; omega)
    simpa [tyAt_tail] using this
  · rintro ⟨hw, hl, h⟩
    refine ⟨by simp [hl], fun i h1 h2 => ?_⟩
    cases i with
    | zero => simpa using hw
    | succ i =>
      have := h i (by simpa using h1) (by simpa using h2)
      simpa [tyAt_tail] using this

theorem SR.cons {c : Cert} {τ : Ty} {ty : List Ty} {x y : Word} {S T : List Word}
    (hw : WR c τ x y) (h : SR c ty S T) : SR c (τ :: ty) (x :: S) (y :: T) :=
  SR.uncons.2 ⟨by simpa [tyAt_cons_zero] using hw, by simpa using h⟩

theorem SR.length {c : Cert} {ty : List Ty} {S T : List Word} (h : SR c ty S T) :
    S.length = T.length := h.1

theorem SR.get {c : Cert} {ty : List Ty} {S T : List Word} (h : SR c ty S T) {i : Nat}
    (hi : i < S.length) : WR c (tyAt ty i) S[i] (T[i]'(h.1 ▸ hi)) := h.2 i hi _

theorem SR.tail {c : Cert} {ty : List Ty} {S T : List Word} (h : SR c ty S T) :
    SR c ty.tail S.tail T.tail := by
  rcases S with _ | ⟨x, S⟩ <;> rcases T with _ | ⟨y, T⟩
  · exact SR.nil c _
  · exact absurd h.1 (by simp)
  · exact absurd h.1 (by simp)
  · exact (SR.uncons.1 h).2

theorem SR.drop {c : Cert} : ∀ (n : Nat) {ty : List Ty} {S T : List Word}, SR c ty S T →
    SR c (ty.drop n) (S.drop n) (T.drop n)
  | 0, _, _, _, h => by simpa using h
  | n + 1, _, _, _, h => by
    rw [← List.drop_tail, ← List.drop_tail, ← List.drop_tail]
    exact SR.drop n h.tail

theorem isData_lt {ty : List Ty} {n i : Nat} (h : isData ty n = true) (hi : i < n) :
    tyAt ty i = some false := by
  simp only [isData, List.all_eq_true, List.mem_range, beq_iff_eq] at h
  exact h i hi

/-- Data words are the same on both sides. -/
theorem SR.data {c : Cert} {ty : List Ty} {S T : List Word} (h : SR c ty S T) {n : Nat}
    (hd : isData ty n = true) : S.take n = T.take n := by
  apply List.ext_getElem
  · simp [h.1]
  · intro i h1 h2
    simp only [List.length_take] at h1 h2
    have hw := h.2 i (by omega) (by omega)
    rw [isData_lt hd (by omega)] at hw
    simp only [List.getElem_take]
    exact hw.symm

theorem SR.head {c : Cert} {ty : List Ty} {x y : Word} {S T : List Word}
    (h : SR c (ty) (x :: S) (y :: T)) (hd : isData ty 1 = true) : y = x := by
  have := (SR.uncons.1 h).1
  rw [isData_lt hd (by decide)] at this
  exact this

theorem SR.le {c : Cert} {ty σ : List Ty} {S T : List Word} (hle : tyLe ty σ = true)
    (h : SR c ty S T) : SR c σ S T := by
  refine ⟨h.1, fun i h1 h2 => ?_⟩
  have hw := h.2 i h1 h2
  simp only [tyLe, List.all_eq_true, List.mem_range, Bool.or_eq_true, beq_iff_eq] at hle
  by_cases hi : i < σ.length
  · rcases hle i hi with he | he
    · rw [he]; trivial
    · rw [he]; exact hw
  · have : tyAt σ i = none := by simp [tyAt, List.getD_eq_getElem?_getD, hi]
    rw [this]; trivial

theorem SR.dup {c : Cert} {ty : List Ty} {S T : List Word} (h : SR c ty S T) {i : Nat}
    (hi : i < S.length) (hi' : i < T.length) :
    SR c (tyAt ty i :: ty) (S[i] :: S) (T[i] :: T) :=
  SR.cons (h.2 i hi hi') h

/-- DUP of a word keeps the known constants a prefix of the stack. -/
theorem dupKnown_prefix {known S : List Word} (hk : known <+: S) {i : Nat} (hi : i < S.length) :
    dupKnown known i <+: S[i] :: S := by
  unfold dupKnown
  split
  · rename_i v hv
    have hS : S[i]? = some v := by
      obtain ⟨t, rfl⟩ := hk
      rw [List.getElem?_append_left (List.getElem?_eq_some_iff.1 hv).1, hv]
    rw [List.getElem?_eq_getElem hi, Option.some.injEq] at hS
    rw [hS]
    exact (List.prefix_cons_inj v).2 ((List.take_prefix 1 known).trans hk)
  · exact List.nil_prefix

theorem tyAt_tySwap (ty : List Ty) (i j : Nat) :
    tyAt (tySwap ty i) j =
      if j = 0 then tyAt ty (i + 1) else if j = i + 1 then tyAt ty 0 else tyAt ty j := by
  unfold tySwap
  by_cases hj : j < max ty.length (i + 2)
  · simp only [tyAt, List.getD_eq_getElem?_getD, List.getElem?_ofFn, hj]
    simp
  · have h1 : ¬ j = 0 := by omega
    have h2 : ¬ j = i + 1 := by omega
    simp only [h1, h2, ite_false]
    simp [tyAt, List.getD_eq_getElem?_getD, List.getElem?_eq_none (show ty.length ≤ j by omega),
      List.getElem?_eq_none (show (List.ofFn (n := max ty.length (i + 2)) _).length ≤ j by simp; omega)]

theorem SR.swap {c : Cert} {ty : List Ty} {a b : Word} {S T : List Word}
    (h : SR c ty (a :: S) (b :: T)) {i : Nat} (hi : i < S.length) (hi' : i < T.length) :
    SR c (tySwap ty i) (S[i] :: S.set i a) (T[i] :: T.set i b) := by
  refine ⟨by simpa using h.1, fun j h1 h2 => ?_⟩
  rw [tyAt_tySwap]
  rcases j with _ | j
  · simp only [ite_true, List.getElem_cons_zero]
    have := h.2 (i + 1) (by simp; omega) (by simp; omega)
    simpa using this
  · simp only [Nat.add_one_ne_zero, ite_false, List.getElem_cons_succ, Nat.add_right_cancel_iff]
    rw [List.getElem_set, List.getElem_set]
    by_cases hj : i = j
    · subst hj
      simp only [ite_true]
      have := h.2 0 (by simp) (by simp)
      simpa using this
    · simp only [hj, ite_false, show ¬ j = i from fun e => hj e.symm]
      have := h.2 (j + 1) (by simp at h1 ⊢; omega) (by simp at h2 ⊢; omega)
      simpa using this

/-! ## What the check gives -/

theorem blocksOk_get {p : Program} {c : Cert} : ∀ (l : List (List Instr)) (b : Nat),
    blocksOk p c b l = true → ∀ k (hk : k < l.length),
      labelItems p c (b + k) ≤ cost p c (b + k) ∧
      blockOk p c (b + k) (c.need (b + k)) [] (c.entry (b + k))
        (cost p c (b + k) - labelItems p c (b + k)) l[k] = true
  | [], _, _, _, hk => absurd hk (by simp)
  | x :: l, b, h, 0, _ => by
    simp only [blocksOk, Bool.and_eq_true, decide_eq_true_eq] at h
    simpa using h.1
  | x :: l, b, h, k + 1, hk => by
    simp only [blocksOk, Bool.and_eq_true] at h
    have := blocksOk_get l (b + 1) h.2 k (by simp at hk; omega)
    rw [show b + (k + 1) = b + 1 + k by omega]
    simpa using this

/-- The facts of the check the simulation uses at every block. -/
structure Glob (p : Program) (c : Cert) (code : ByteArray) : Prop where
  top_mod : c.top % 32 = 0
  top_le : c.top ≤ 2 ^ 32
  size_lt : code.size < 2 ^ 32
  target : ∀ t, t < p.blocks.length → isTarget p c t = true →
    isValidJumpDest (validJumpDestinations code) (c.offset t) = true ∧ c.offset t < code.size ∧
    Seg (bytesOf code) c.offset (c.offset t) (lowerFrom p c t (p.blocks.drop t)) code.size
  block : ∀ t (ht : t < p.blocks.length), labelItems p c t ≤ cost p c t ∧
    blockOk p c t (c.need t) [] (c.entry t) (cost p c t - labelItems p c t) p.blocks[t] = true

theorem glob_of_check {p : Program} {code : ByteArray} {c : Cert} (h : check p code c = true) :
    Glob p c code ∧ Seg (bytesOf code) c.offset 0 (lower p c) code.size ∧ c.need 0 = 0 ∧
      cost p c 0 ≤ 1000 ∧ 22100 * cost p c 0 + memoryGasCost c.top ≤ 10000000 := by
  simp only [check, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hw, hblocks⟩, hlabels⟩, hneed⟩, hmod⟩, hlen⟩, htop⟩, hgas⟩, hsize⟩ := h
  obtain ⟨stream, hw⟩ := Option.isSome_iff_exists.1 hw
  have hseg : Seg (bytesOf code) c.offset 0 (lower p c) code.size := by
    have := seg_of_walk (walk_sound hw)
    rwa [length_bytesOf] at this
  refine ⟨⟨hmod, htop, hsize, fun t ht htgt => ?_, fun t ht => ?_⟩, hseg, hneed, hlen, hgas⟩
  · have hv : isValidJumpDest (validJumpDestinations code) (c.offset t) = true := by
      simp only [labelsValid, List.all_eq_true, List.mem_range] at hlabels
      have := hlabels t ht
      simpa [htgt] using this
    obtain ⟨pc', hs, hpc⟩ := seg_lowerFrom p c t p.blocks 0 0 hseg ht
    simp only [Nat.zero_add] at hs hpc
    rw [← hpc htgt] at hs
    refine ⟨hv, ?_, hs⟩
    have hs' := hs
    rw [lowerFrom_drop p c ht] at hs'
    simp only [lowerBlock, htgt, ite_true, List.cons_append] at hs'
    cases hs' with
    | cons d _ _ =>
      have := decode_lt d
      rwa [length_bytesOf] at this
  · have := blocksOk_get p.blocks 0 hblocks t ht
    simpa using this

/-! ## The invariant -/

/-- SolarTV's stack, state and memory at EthLib's offset `pc` with `items` left and potential `k`:
the walk goes on from `pc` to the end, the stack and the potential fit in 1000 words, the gas
pays 22100 for each unit of potential and memory up to the bound, and SolarTV's memory is
EthLib's. Each item run takes a unit of potential; the check bounds the potential of each
block by those of the blocks it jumps or falls to. -/
structure Inv (c : Cert) (code : ByteArray) (call : SolarTV.Call) (items : List Item) (k pc : Nat)
    (S : List Word) (s : SolarTV.Machine.State) (M : ByteArray) (g : Nat) : Prop where
  seg : Seg (bytesOf code) c.offset pc items code.size
  stack : S.length + k ≤ 1000
  gas : 22100 * k + (memoryGasCost c.top - memoryGasCost M.size) ≤ g
  le_top : M.size ≤ c.top
  mem : MemRel s.memory M

theorem Inv.next {c : Cert} {code : ByteArray} {call : SolarTV.Call} {item : Item}
    {items : List Item} {k pc next : Nat} {S S' : List Word} {s : SolarTV.Machine.State}
    {M : ByteArray} {g g' : Nat} (I : Inv c code call (item :: items) k pc S s M g) (hk : 1 ≤ k)
    (hseg : Seg (bytesOf code) c.offset next items code.size) (hS : S'.length ≤ S.length + 1)
    (hg : g ≤ g' + 22100) : Inv c code call items (k - 1) next S' s M g' where
  seg := hseg
  stack := by have := I.stack; omega
  gas := by have := I.gas; omega
  le_top := I.le_top
  mem := I.mem

theorem Inv.weaken {c : Cert} {code : ByteArray} {call : SolarTV.Call} {items : List Item}
    {k k' pc : Nat} {S : List Word} {s : SolarTV.Machine.State} {M : ByteArray} {g : Nat}
    (I : Inv c code call items k pc S s M g) (hk : k' ≤ k) : Inv c code call items k' pc S s M g where
  seg := I.seg
  stack := by have := I.stack; omega
  gas := by have := I.gas; omega
  le_top := I.le_top
  mem := I.mem

/-- An event of SolarTV's world is a log EthLib's frame wrote at `a`: the same topics and data. -/
def LogMatch (a : Address) : SolarTV.Machine.Event → EthLib.Execution.Blocks.Log → Prop
  | .log topics data, l =>
    l.address = a ∧ l.topics = topics.map U256.toBeBytes ∧ l.data.toList.map (·.toNat) = data.map BitVec.toNat
  | .call .., _ | .read _, _ | .create .., _ => False

/-- EthLib's logs are those of `ss0` and then one for each event of SolarTV's world. -/
def LogsRel (a : Address) (ss0 ss : Substate) (w : List SolarTV.Machine.Event) : Prop :=
  ∃ L, ss.logs.toList = ss0.logs.toList ++ L ∧ List.Forall₂ (LogMatch a) w L

/-- SolarTV's storage is the storage of EthLib's account of the frame, which exists, and the
substate's logs are those of `ss0`, the substate the frame started from, and then SolarTV's. -/
structure Rel (msg : Message .fusaka) (ss0 : Substate) (st : State.TransactionState)
    (ss : Substate) (s : SolarTV.Machine.State) : Prop where
  storage : ∀ k : Word, st.getStorage msg.currentTarget (U256.toBeBytes k) = s.storage k
  account : (st.getAccountOptional msg.currentTarget).isSome = true
  logs : LogsRel msg.currentTarget ss0 ss s.world

/-- A slot of EthLib's storage at the callee is SolarTV's. -/
theorem Rel.slot {msg : Message .fusaka} {ss0 : Substate} {st : State.TransactionState}
    {ss : Substate} {s : SolarTV.Machine.State} (R : Rel msg ss0 st ss s)
    (htgt : msg.currentTarget = Target.address selfAddress) (slot : Nat) :
    (st.getStorage (Target.address selfAddress) (Target.storageKey slot)).toNat =
      SolarTV.Machine.storageOf s slot := by
  have hkey : Target.storageKey slot = U256.toBeBytes (BitVec.ofNat 256 slot) :=
    (storageKey_eq_toBeBytes slot _).2 (by simp)
  rw [hkey, ← htgt, R.storage]
  rfl

/-- How the frame ends for SolarTV's `halt` in state `s`: as `PostS` shows its observable, with logs
that are those of `ss0` and then SolarTV's. -/
def PostL (call : SolarTV.Call) (a : Address) (ss0 : Substate) (s : SolarTV.Machine.State)
    (halt : SolarTV.Machine.Halt) (evm : Evm .fusaka Nat) : Prop :=
  ∃ ssF, PostS (SolarTV.Machine.observe call s halt) ssF evm ∧ LogsRel a ss0 ssF s.world

/-- A frame stopped with no error and no output from `st` and `ss` shows SolarTV's STOP. -/
theorem postL_stop {msg : Message .fusaka} {ss0 : Substate} {st : State.TransactionState}
    {ss : Substate} {s : SolarTV.Machine.State} (R : Rel msg ss0 st ss s)
    (htgt : msg.currentTarget = Target.address selfAddress) {call : SolarTV.Call} {g : Nat}
    (evm : Evm .fusaka Nat) (h : Halted false .empty g st ss evm) :
    PostL call msg.currentTarget ss0 s .stop evm := by
  obtain ⟨-, herr, hout, -, hst, hss⟩ := h
  refine ⟨ss, ⟨by rw [herr]; rfl, by rw [hout]; simp [SolarTV.Machine.observe], by rw [hss],
    fun _ slot => ?_⟩, R.logs⟩
  rw [hst]
  exact R.slot htgt slot

/-- What a block's instructions from `pc` give, from EthLib's stack `T`, state `st` and substate
`ss`: a halt EthLib's frame shows, or the next block, reached by EthLib with its stack related
at the block's types, the invariant at its potential and the relation of the storage. -/
def SimOut (p : Program) (c : Cert) (code : ByteArray) (call : SolarTV.Call)
    (msg : Message .fusaka) (ss0 : Substate) (st : State.TransactionState) (ss : Substate)
    (pc : Nat) (T : List Word) (M : ByteArray) (g : Nat) :
    (SolarTV.Machine.Halt × SolarTV.Machine.State) ⊕ (Nat × List Word × SolarTV.Machine.State) →
      Prop
  | .inl (halt, s') =>
    Spec .fusaka (At code msg pc T M g st ss .empty) (PostL call msg.currentTarget ss0 s' halt)
  | .inr (t, S', s') => (t ≤ p.blocks.length ∧ (t < p.blocks.length → c.need t ≤ S'.length)) ∧
      ∃ pc' T' M' g' st' ss', Hoare .fusaka (At code msg pc T M g st ss .empty)
        (At code msg pc' T' M' g' st' ss' .empty) ∧ SR c (c.entry t) S' T' ∧
        Inv c code call (lowerFrom p c t (p.blocks.drop t)) (cost p c t) pc' S' s' M' g' ∧
        Rel msg ss0 st' ss' s'

theorem SimOut.pre {p : Program} {c : Cert} {code : ByteArray} {call : SolarTV.Call}
    {msg : Message .fusaka} {ss0 : Substate} {st st1 : State.TransactionState} {ss ss1 : Substate}
    {pc pc1 : Nat} {T T1 : List Word} {M M1 : ByteArray} {g g1 : Nat}
    {r : (SolarTV.Machine.Halt × SolarTV.Machine.State) ⊕ (Nat × List Word × SolarTV.Machine.State)}
    (h : Hoare .fusaka (At code msg pc T M g st ss .empty) (At code msg pc1 T1 M1 g1 st1 ss1 .empty))
    (h1 : SimOut p c code call msg ss0 st1 ss1 pc1 T1 M1 g1 r) :
    SimOut p c code call msg ss0 st ss pc T M g r := by
  match r, h1 with
  | .inl (_, _), hspec => exact Spec.seq h hspec
  | .inr (_, _, _), ⟨hneed, pc', T', M', g', st', ss', hh, hR, hinv, hrel⟩ =>
    exact ⟨hneed, pc', T', M', g', st', ss', Triple.seq h hh, hR, hinv, hrel⟩

/-! ## SolarTV's steps -/

open SolarTV.EVM.Program in
theorem exec_stack {o : SolarTV.Machine.Oracle} {call : SolarTV.Call} {b : Nat}
    {op : SolarTV.EVM.Op} {rest : List Instr} {S next : List Word} {s : SolarTV.Machine.State}
    (hstep : SolarTV.EVM.step (context o call s) op S = some next) (h1 : S.length ≤ 1024)
    (h2 : next.length ≤ 1024) :
    exec o call b (.op (.stack op) :: rest) S s = exec o call b rest next s := by
  simp [exec, stepOp, SolarTV.EVM.stepChecked, hstep, Except.map,
    show ¬ 1024 < S.length by omega, show ¬ 1024 < next.length by omega]

theorem opByte_of_stackNeed {op : SolarTV.EVM.Op} {x : Nat × Int} (h : stackNeed op = some x) :
    ∃ byte, opByte op = some byte := by
  cases op <;> simp [stackNeed, opByte] at h ⊢

theorem lowerInstr_stack {op : SolarTV.EVM.Op} (hne : ∀ v, op ≠ .push v) :
    lowerInstr (.op (.stack op)) = [.op ((opByte op).getD 0xfe)] := by
  cases op <;> first | rfl | exact absurd rfl (hne _)

/-- The check of a stack operation other than PUSH, DUP, SWAP and POP. -/
theorem blockStep_stack {p : Program} {c : Cert} {ok : Nat → List Word → List Ty → Nat → Bool}
    {h k : Nat} {known : List Word} {ty : List Ty} {op : SolarTV.EVM.Op} (hne : ∀ v, op ≠ .push v)
    (hd : ∀ i, op ≠ .dup i) (hs : ∀ i, op ≠ .swap i) (hp : op ≠ .pop) :
    blockStep p c ok h known ty k (.op (.stack op)) =
      match stackNeed op with
      | some (need, d) => decide (1 ≤ k) && decide (need ≤ h) && isData ty need &&
          ok (h + d).toNat [] (some false :: ty.drop need) (k - 1)
      | none => false := by
  cases op <;> first | rfl | exact absurd rfl (hne _) | exact absurd rfl (hd _) |
    exact absurd rfl (hs _) | exact absurd rfl hp

/-- A stack operation of the fragment other than DUP, SWAP and POP reads its top words and
puts one word in their place. -/
theorem step_data {op : SolarTV.EVM.Op} {need : Nat} {d : Int} (hn : stackNeed op = some (need, d))
    (h1 : ∀ i, op ≠ .dup i) (h2 : ∀ i, op ≠ .swap i) (h3 : op ≠ .pop) {ctx : SolarTV.EVM.Context}
    {S S' T : List Word} (hs : SolarTV.EVM.step ctx op S = some S') (ht : S.take need = T.take need)
    (hl : S.length = T.length) :
    ∃ v, S' = v :: S.drop need ∧ SolarTV.EVM.step ctx op T = some (v :: T.drop need) := by
  cases op <;> simp only [stackNeed, reduceCtorEq, Option.some.injEq, Prod.mk.injEq] at hn
  all_goals try first
    | exact absurd rfl (h1 _)
    | exact absurd rfl (h2 _)
    | exact absurd rfl h3
  all_goals obtain ⟨rfl, -⟩ := hn
  all_goals
    rcases S with _ | ⟨a, _ | ⟨b, S⟩⟩ <;> rcases T with _ | ⟨a', _ | ⟨b', T⟩⟩ <;>
      simp_all [SolarTV.EVM.step]
  all_goals (try subst_vars)
  all_goals (try simp)

/-- A checked stack operation other than PUSH runs on both stacks, to stacks related at the
types the check goes on with. -/
theorem stack_sim {p : Program} {c : Cert} {ok : Nat → List Word → List Ty → Nat → Bool}
    {h k : Nat} {known : List Word} {ty : List Ty} {op : SolarTV.EVM.Op} (hne : ∀ v, op ≠ .push v)
    {ctx : SolarTV.EVM.Context} {S T : List Word}
    (hok : blockStep p c ok h known ty k (.op (.stack op)) = true) (hh : h ≤ S.length)
    (hk : known <+: S) (hR : SR c ty S T) :
    1 ≤ k ∧ ∃ byte, opByte op = some byte ∧ ∃ h' ty' S' T',
      SolarTV.EVM.step ctx op S = some S' ∧ SolarTV.EVM.step ctx op T = some T' ∧
      SR c ty' S' T' ∧ h' ≤ S'.length ∧ S'.length ≤ S.length + 1 ∧
      ∃ known', known' <+: S' ∧ ok h' known' ty' (k - 1) = true := by
  have hL := hR.length
  by_cases hd : ∃ i, op = .dup i
  · obtain ⟨i, rfl⟩ := hd
    simp only [blockStep, Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨⟨hk1, hi⟩, hok⟩ := hok
    have hiS : i.val < S.length := by omega
    have hiT : i.val < T.length := by omega
    refine ⟨hk1, _, rfl, h + 1, _, _, _, ?_, ?_, SR.dup hR hiS hiT, by simp; omega, by simp, _,
      dupKnown_prefix hk hiS, hok⟩
    · simp [SolarTV.EVM.step, List.getElem?_eq_getElem hiS]
    · simp [SolarTV.EVM.step, List.getElem?_eq_getElem hiT]
  by_cases hs : ∃ i, op = .swap i
  · obtain ⟨i, rfl⟩ := hs
    simp only [blockStep, Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨⟨hk1, hi⟩, hok⟩ := hok
    rcases S with _ | ⟨a, S⟩
    · simp at hh; omega
    rcases T with _ | ⟨b, T⟩
    · simp at hL
    simp only [List.length_cons] at hh hL
    have hiS : i.val < S.length := by omega
    have hiT : i.val < T.length := by omega
    refine ⟨hk1, _, rfl, h, _, _, _, ?_, ?_, SR.swap hR hiS hiT, by simp; omega, by simp, [],
      List.nil_prefix, hok⟩
    · simp [SolarTV.EVM.step, List.getElem?_eq_getElem hiS]
    · simp [SolarTV.EVM.step, List.getElem?_eq_getElem hiT]
  by_cases hp : op = .pop
  · subst hp
    simp only [blockStep, Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨⟨hk1, h1⟩, hok⟩ := hok
    rcases S with _ | ⟨a, S⟩
    · simp at hh; omega
    rcases T with _ | ⟨b, T⟩
    · simp at hL
    refine ⟨hk1, _, rfl, h - 1, _, _, _, rfl, rfl, (SR.uncons.1 hR).2, by simp at hh; omega,
      by simp only [List.length_cons]; omega, [], List.nil_prefix, hok⟩
  have hd' : ∀ i, op ≠ .dup i := fun i e => hd ⟨i, e⟩
  have hs' : ∀ i, op ≠ .swap i := fun i e => hs ⟨i, e⟩
  rw [blockStep_stack hne hd' hs' hp] at hok
  split at hok
  · rename_i need d hn
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨⟨⟨hk1, hneed⟩, hdata⟩, hok⟩ := hok
    obtain ⟨byte, hbyte⟩ := opByte_of_stackNeed hn
    have hS' : ∃ S', SolarTV.EVM.step ctx op S = some S' := by
      cases op <;> simp only [stackNeed, reduceCtorEq, Option.some.injEq, Prod.mk.injEq] at hn
      all_goals try first
        | exact absurd rfl (hd' _)
        | exact absurd rfl (hs' _)
        | exact absurd rfl hp
      all_goals obtain ⟨rfl, -⟩ := hn
      all_goals rcases S with _ | ⟨a, _ | ⟨b, S⟩⟩ <;> simp_all [SolarTV.EVM.step] <;> omega
    obtain ⟨S', hstep⟩ := hS'
    obtain ⟨v, rfl, hstepT⟩ := step_data hn hd' hs' hp hstep (hR.data hdata) hL
    have hd1 : (need : Int) + d = 1 := by
      cases op <;> simp [stackNeed] at hn <;>
        first | omega | exact absurd rfl (hd' _) | exact absurd rfl (hs' _) | exact absurd rfl hp
    refine ⟨hk1, byte, hbyte, (h + d).toNat, _, _, _, hstep, hstepT,
      SR.cons (τ := some false) rfl (SR.drop need hR), ?_, ?_, [], List.nil_prefix, hok⟩
    · simp only [List.length_cons, List.length_drop]; omega
    · simp only [List.length_cons, List.length_drop]; omega
  · cases hok

theorem turnedElse_some {c : Cert} {b e : Nat} {i : Instr} {rest : List Instr}
    (h : turnedElse c b i rest = some e) : i = .jumpi (b + 1) ∧ rest = [.jump e] := by
  unfold turnedElse at h
  split at h
  · split at h
    · rename_i hc
      simp only [Option.some.injEq] at h
      simp only [Bool.and_eq_true, beq_iff_eq] at hc
      subst h
      rw [hc.2]
      exact ⟨rfl, rfl⟩
    · cases h
  · cases h

/-- What the assembler leaves out: a final jump to the next block, or the last block's STOP. -/
theorem dropped_true {p : Program} {b : Nat} {i : Instr} {rest : List Instr}
    (h : dropped p b i rest = true) :
    (i = .jump (b + 1) ∧ rest = []) ∨ (i = .stop ∧ rest = [] ∧ b + 1 = p.blocks.length) := by
  unfold dropped at h
  split at h
  · simp only [beq_iff_eq] at h
    subst h
    exact .inl ⟨rfl, rfl⟩
  · simp only [beq_iff_eq] at h
    exact .inr ⟨rfl, rfl, h⟩
  · cases h

theorem iszero_zero : EvmRules.Evm.iszero (0 : Word) ≠ 0 := by
  unfold EvmRules.Evm.iszero
  decide

theorem iszero_nonzero {x : Word} (h : x ≠ 0) : EvmRules.Evm.iszero x = 0 := by
  unfold EvmRules.Evm.iszero
  have : (x == 0) = false := by simpa using h
  rw [this]
  rfl

/-- CALLDATALOAD in SolarTV is EthLib's. -/
theorem shl_or_ofNat (acc b : Nat) (hb : b < 256) :
    (BitVec.ofNat 256 acc <<< 8) ||| BitVec.ofNat 256 b = BitVec.ofNat 256 (acc * 256 + b) := by
  have hand : (BitVec.ofNat 256 acc <<< 8) &&& BitVec.ofNat 256 b = 0 := by
    ext i hi
    rw [BitVec.getElem_and, BitVec.getElem_shiftLeft, ← BitVec.getLsbD_eq_getElem,
      ← BitVec.getLsbD_eq_getElem, BitVec.getLsbD_ofNat]
    by_cases h8 : i < 8
    · simp [h8]
    · have : b.testBit i = false :=
        Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hb
          (by simpa using Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.le_of_not_lt h8)))
      simp [BitVec.getLsbD_ofNat, this]
  rw [← BitVec.add_eq_or_of_and_eq_zero _ _ hand]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  omega

theorem foldl_word (data : ByteArray) (off : Nat) : ∀ (l : List Nat) (acc : Nat),
    l.foldl (fun (acc : BitVec 256) i =>
        (acc <<< 8) ||| BitVec.ofNat 256 (data.data.getD (off + i) 0).toNat)
        (BitVec.ofNat 256 acc) =
      BitVec.ofNat 256 (l.foldl (fun acc i => acc * 256 + (byteAt data (off + i)).toNat) acc)
  | [], _ => rfl
  | i :: l, acc => by
    simp only [List.foldl_cons]
    have hget : (data.data.getD (off + i) 0) = byteAt data (off + i) := rfl
    rw [hget, shl_or_ofNat _ _ (byteAt data (off + i)).toNat_lt, foldl_word data off l]

theorem calldataWord_eq (call : SolarTV.Call) (off : BitVec 256) :
    SolarTV.Machine.calldataWord call off = loadWord call.calldata off.toNat 32 := by
  unfold SolarTV.Machine.calldataWord loadWord bufferRead bytesToNat
  rw [show (0 : BitVec 256) = BitVec.ofNat 256 0 from rfl, foldl_word, List.foldl_map]


/-! ## SolarTV's steps, continued -/

open SolarTV.EVM.Program in
theorem exec_store {o : SolarTV.Machine.Oracle} {call : SolarTV.Call} {b : Nat}
    {rest : List Instr} {x y : Word} {S : List Word} {s : SolarTV.Machine.State}
    (h : S.length < 1023) :
    exec o call b (.op .store :: rest) (x :: y :: S) s =
      exec o call b rest S { s with memory := s.memory.store x.toNat y } := by
  have h1 : ¬ 1024 < S.length + 1 + 1 := by omega
  simp [exec, stepOp, h1]

open SolarTV.EVM.Program in
theorem exec_effect0 {o : SolarTV.Machine.Oracle} {call : SolarTV.Call} {b : Nat}
    {rest : List Instr} {e : SolarTV.Machine.Effect} {w : Word} {S : List Word}
    {s : SolarTV.Machine.State} (happ : SolarTV.Machine.Effect.apply o call e [] s = some (some w, s))
    (h : S.length < 1024) :
    exec o call b (.effect e 0 :: rest) S s = exec o call b rest (w :: S) s := by
  simp [exec, happ, show ¬ 1024 < S.length + 1 by omega]

open SolarTV.EVM.Program in
theorem exec_effect1 {o : SolarTV.Machine.Oracle} {call : SolarTV.Call} {b : Nat}
    {rest : List Instr} {e : SolarTV.Machine.Effect} {x w : Word} {S : List Word}
    {s : SolarTV.Machine.State}
    (happ : SolarTV.Machine.Effect.apply o call e [x] s = some (some w, s)) (h : S.length < 1024) :
    exec o call b (.effect e 1 :: rest) (x :: S) s = exec o call b rest (w :: S) s := by
  simp [exec, happ, show ¬ 1024 < S.length + 1 by omega]

open SolarTV.EVM.Program in
theorem exec_effect2 {o : SolarTV.Machine.Oracle} {call : SolarTV.Call} {b : Nat}
    {rest : List Instr} {e : SolarTV.Machine.Effect} {x y : Word} {S : List Word}
    {s s' : SolarTV.Machine.State}
    (happ : SolarTV.Machine.Effect.apply o call e [x, y] s = some (none, s')) (h : S.length ≤ 1024) :
    exec o call b (.effect e 2 :: rest) (x :: y :: S) s = exec o call b rest S s' := by
  simp [exec, happ, show ¬ 1024 < S.length by omega]

open SolarTV.EVM.Program in
theorem exec_keccak {o : SolarTV.Machine.Oracle} {call : SolarTV.Call} {b : Nat}
    {rest : List Instr} {x y : Word} {S : List Word} {s : SolarTV.Machine.State}
    (h : S.length < 1024) :
    exec o call b (.effect .keccak256 2 :: rest) (x :: y :: S) s =
      exec o call b rest (o.keccak ((s.memory.expand x.toNat y.toNat).read x.toNat y.toNat) :: S)
        { s with memory := s.memory.expand x.toNat y.toNat } := by
  simp [exec, SolarTV.Machine.Effect.apply, show ¬ 1024 < S.length + 1 by omega]

open SolarTV.EVM.Program in
theorem exec_log {o : SolarTV.Machine.Oracle} {call : SolarTV.Call} {b : Nat}
    {rest : List Instr} {x y : Word} {tops S : List Word} {s : SolarTV.Machine.State}
    (h : S.length ≤ 1024) :
    exec o call b (.effect (.log tops.length) (tops.length + 2) :: rest) (x :: y :: (tops ++ S)) s =
      exec o call b rest S ⟨s.memory.expand x.toNat y.toNat, s.storage, s.transient,
        s.world ++ [.log tops ((s.memory.expand x.toNat y.toNat).read x.toNat y.toNat)]⟩ := by
  have ht : (x :: y :: (tops ++ S)).take (tops.length + 2) = x :: y :: tops := by simp
  have hd : (x :: y :: (tops ++ S)).drop (tops.length + 2) = S := by simp
  simp only [exec, List.length_cons, List.length_append, ht, hd]
  simp [SolarTV.Machine.Effect.apply, show ¬ 1024 < S.length by omega,
    show ¬ tops.length + S.length + 1 + 1 < tops.length + 2 by omega]

theorem Inv.next2 {c : Cert} {code : ByteArray} {call : SolarTV.Call} {i1 i2 : Item}
    {items : List Item} {k pc next : Nat} {S S' : List Word} {s : SolarTV.Machine.State}
    {M : ByteArray} {g g' : Nat} (I : Inv c code call (i1 :: i2 :: items) k pc S s M g)
    (hk : 2 ≤ k) (hseg : Seg (bytesOf code) c.offset next items code.size)
    (hS : S'.length ≤ S.length + 1) (hg : g ≤ g' + 44200) :
    Inv c code call items (k - 2) next S' s M g' where
  seg := hseg
  stack := by have := I.stack; omega
  gas := by have := I.gas; omega
  le_top := I.le_top
  mem := I.mem

theorem toNat_offset {code : ByteArray} {n : Nat} (h : n < code.size) (hs : code.size < 2 ^ 32) :
    (BitVec.ofNat 256 n).toNat = n := by
  rw [BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt (Nat.lt_trans (Nat.lt_trans h hs) (by decide))

/-- A jump's target block, with the invariant at its offset and potential, from the invariant
before the `m` items of the jump. -/
theorem Inv.target {p : Program} {c : Cert} {code : ByteArray} (G : Glob p c code)
    {call : SolarTV.Call} {t m : Nat} {items : List Item} {k pc : Nat}
    {S S' : List Word} {s : SolarTV.Machine.State} {M : ByteArray} {g g' : Nat}
    (I : Inv c code call items k pc S s M g) (htn : t < p.blocks.length)
    (htgt : isTarget p c t = true) (hcost : cost p c t + m ≤ k) (hS : S'.length ≤ S.length)
    (hg : g ≤ g' + 22100 * m) :
    Inv c code call (lowerFrom p c t (p.blocks.drop t)) (cost p c t) (c.offset t) S' s M g' where
  seg := (G.target t htn htgt).2.2
  stack := by have := I.stack; omega
  gas := by
    have := I.gas
    have hm : 22100 * (cost p c t + m) ≤ 22100 * k := Nat.mul_le_mul_left _ hcost
    rw [Nat.mul_add] at hm
    omega
  le_top := I.le_top
  mem := I.mem

open SolarTV.Machine in
/-- Growth of memory for a range keeps the relation of the memories. -/
theorem memRel_expand {m : Mem} {M : ByteArray} {o sz : Word} (hm : MemRel m M)
    (hbound : sz = 0 ∨ o.toNat + sz.toNat ≤ 2 ^ 32) :
    MemRel (m.expand o.toNat sz.toNat) (memoryExtend M (extendMemory M.size [(o, sz)]).expandBy) := by
  have hmod : M.size % 32 = 0 := by rw [hm.1]; omega
  have hb : (m.expand o.toNat sz.toNat).bytes = m.bytes := by unfold Mem.expand; split <;> rfl
  refine ⟨?_, fun i => by rw [byteAt_memoryExtend, hb]; exact hm.2 i⟩
  by_cases hz : sz = 0
  · subst hz
    rw [extendMemory_zero', memoryExtend_zero]
    simpa [Mem.expand] using hm.1
  · have hbound := hbound.resolve_left hz
    rw [size_memoryExtend_extendMemory' hmod hz, hm.1, ceil32_eq]
    have hz' : sz.toNat ≠ 0 := fun h => hz (BitVec.eq_of_toNat_eq (by simpa using h))
    unfold Mem.expand SolarTV.Memory.grow
    simp only [hz', ite_false]
    have hlt : (o.toNat + sz.toNat + 31) / 32 < 2 ^ 251 := by omega
    split
    · rename_i h
      rw [BitVec.ult_iff_toNat_lt, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt] at h
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
      omega
    · rename_i h
      rw [BitVec.ult_iff_toNat_lt, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt] at h
      omega

/-- Bytes with the values of SolarTV's bytes are those bytes. -/
theorem byteArray_eq_of_map {B : ByteArray} {d : List (BitVec 8)}
    (h : B.toList.map (·.toNat) = d.map BitVec.toNat) : B = ⟨(d.map UInt8.ofBitVec).toArray⟩ := by
  have e : B.toList = B.data.toList := by simp
  have h1 : B.data.toList = d.map UInt8.ofBitVec := by
    apply List.map_injective_iff.2 (fun a b hab => UInt8.toNat_inj.1 hab)
    rw [← e, h, List.map_map]
    apply List.map_congr_left
    intro x _
    simp
  cases B with
  | mk data =>
    simp only at h1
    congr 1
    apply Array.toList_inj.1
    simpa using h1

theorem decode_log : ∀ n : Fin 5, Op.decode (UInt8.ofNat (0xa0 + n.val)) = some (.log n) := by
  decide

/-- An oracle whose CALLER is the caller of `Target`'s calls and whose hash is EthLib's. -/
def OracleOk (o : SolarTV.Machine.Oracle) : Prop :=
  o.caller.setWidth 256 = (Target.address callerAddress).toU256 ∧
    ∀ bytes, o.keccak bytes = keccak ⟨(bytes.map UInt8.ofBitVec).toArray⟩

/-- Any oracle with EthLib's caller and hash. -/
def ethOracle (o : SolarTV.Machine.Oracle) : SolarTV.Machine.Oracle :=
  { o with caller := BitVec.ofNat 160 callerAddress,
           keccak := fun bytes => keccak ⟨(bytes.map UInt8.ofBitVec).toArray⟩ }

theorem ethOracle_ok (o : SolarTV.Machine.Oracle) : OracleOk (ethOracle o) :=
  ⟨show (BitVec.ofNat 160 callerAddress).setWidth 256 = (Target.address callerAddress).toU256 by
    decide +kernel, fun _ => rfl⟩

theorem forall₂_snoc {α β : Type} {R : α → β → Prop} {a : α} {b : β} :
    ∀ {l1 : List α} {l2 : List β}, List.Forall₂ R l1 l2 → R a b →
      List.Forall₂ R (l1 ++ [a]) (l2 ++ [b])
  | [], [], .nil, h => .cons h .nil
  | _ :: _, _ :: _, .cons h1 t, h => .cons h1 (forall₂_snoc t h)

/-! ## The simulation of a block -/

/-- The first instruction of a walk segment and the segment after it. -/
theorem Seg.head {code : List Nat} {offset : Nat → Nat} {pc e : Nat} {item : Item}
    {items : List Item} (h : Seg code offset pc (item :: items) e) :
    ∃ next, decode code pc = some (item.expected offset, next) ∧ Seg code offset next items e := by
  cases h with | cons d _ r => exact ⟨_, d, r⟩

open SolarTV.EVM.Program in
/-- EthLib runs the code of a block's instructions from the offset of the next one as SolarTV
runs them. -/
theorem exec_sim {p : Program} {c : Cert} {code : ByteArray} (G : Glob p c code)
    {o : SolarTV.Machine.Oracle} {call : SolarTV.Call} {msg : Message .fusaka} {ss0 : Substate}
    (hdata : msg.data = call.calldata) (hvalue : msg.value = BitVec.ofNat 256 call.callvalue)
    (hstatic : msg.isStatic = false) (hself : msg.currentTarget = Target.address selfAddress)
    (hcaller : msg.caller = Target.address callerAddress) (ho : c.env = true → OracleOk o)
    (b : Nat) (hb : b < p.blocks.length) :
    ∀ (is : List Instr) (h : Nat) (known : List Word) (ty : List Ty) (S T : List Word) (k : Nat)
      (s : SolarTV.Machine.State) (pc : Nat) (M : ByteArray) (g : Nat)
      (st : State.TransactionState) (ss : Substate),
      blockOk p c b h known ty k is = true → h ≤ S.length → known <+: S → SR c ty S T →
      Inv c code call (lowerInstrs p c b is ++ lowerFrom p c (b + 1) (p.blocks.drop (b + 1))) k
        pc S s M g → Rel msg ss0 st ss s →
      SimOut p c code call msg ss0 st ss pc T M g (exec o call b is S s)
  | [], h, known, ty, S, T, k, s, pc, M, g, st, ss, hok, hh, _, hR, I, R => by
    simp only [blockOk, fallOk, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hok
    have I2 := I.weaken hok.2
    simp only [lowerInstrs, List.nil_append] at I2
    simp only [exec, SimOut]
    exact ⟨⟨by omega, fun ht => by omega⟩, pc, T, M, g, st, ss, Triple.of_imp fun _ h => h,
      SR.le hok.1.2 hR, I2, R⟩
  | i :: rest, h, known, ty, S, T, k, s, pc, M, g, st, ss, hok, hh, hk, hR, I, R => by
    have hL := hR.length
    have hctx : (⟨BitVec.ofNat 256 msg.data.size, o.env "returndatasize" s.world []⟩ :
        SolarTV.EVM.Context) = context o call s := by rw [hdata]; rfl
    cases hT : turnedElse c b i rest with
    | some e =>
      -- A turned branch: ISZERO; PUSH e; JUMPI, falling into the next block.
      obtain ⟨rfl, rfl⟩ := turnedElse_some hT
      simp only [blockOk, hT, jumpOk, fallOk, Bool.and_eq_true, Bool.or_eq_true,
        decide_eq_true_eq] at hok
      obtain ⟨⟨⟨⟨hk3, h1⟩, hdat⟩, ⟨⟨⟨hen, hetgt⟩, hneed⟩, hety⟩, hcost⟩, ⟨hfall, hfty⟩, hcost'⟩ := hok
      simp only [lowerInstrs, hT, List.cons_append, List.nil_append] at I
      rcases S with _ | ⟨cond, S'⟩
      · simp at hh; omega
      rcases T with _ | ⟨cond', T'⟩
      · simp at hL
      obtain rfl := (SR.head hR hdat).symm
      have hR' := (SR.uncons.1 hR).2
      simp only [List.length_cons] at hL
      obtain ⟨n0, hd0, hs0⟩ := I.seg.head
      obtain ⟨n1, hd1, hs1⟩ := hs0.head
      obtain ⟨n2, hd2, hseg⟩ := hs1.head
      simp only [Item.expected] at hd0 hd1 hd2
      obtain ⟨hlt0, hcode0, rfl⟩ := op_item hd0
      obtain ⟨hlt2, hcode2, rfl⟩ := op_item hd2
      have hS := I.stack; have hG := I.gas
      simp only [List.length_cons] at hS hh
      obtain ⟨g0, hg0, hisz⟩ := stack_rule (msg := msg) (M := M) (st := st) (ss := ss) (gas := g)
        (op := .iszero) (stack := cond :: T') (next := EvmRules.Evm.iszero cond :: T')
        (r := o.env "returndatasize" s.world []) rfl hlt0 hcode0 rfl (by omega)
        (by simp only [List.length_cons]; omega)
      obtain ⟨g1, hg1, hpush⟩ := push_item (msg := msg) (M := M) (st := st) (ss := ss)
        (gas := g0) (stack := EvmRules.Evm.iszero cond :: T') hd1 (by omega)
        (by simp only [List.length_cons]; omega)
      by_cases hc : cond = 0
      · -- The condition is zero: ISZERO gives one and the code jumps to the else block.
        subst hc
        have hoff := toNat_offset (G.target e hen hetgt).2.1 G.size_lt
        have hj := Logic.jumpi_taken (message := msg) (memory := M) (state := st)
          (substate := ss) (returnData := .empty) (destination := BitVec.ofNat 256 (c.offset e))
          (rest := T') hlt2 hcode2 (show 10 ≤ g1 by omega) iszero_zero
          (by rw [hoff]; exact (G.target e hen hetgt).1)
        rw [hoff] at hj
        simp only [exec, List.length_cons, show ¬ S'.length + 1 + 1 > 1024 by omega,
          show ¬ S'.length + 1 > 1024 by omega, ite_false, ite_true, SimOut]
        exact ⟨⟨by omega, fun _ => by omega⟩, c.offset e, T', M, g1 - 10, st, ss,
          Triple.seq hisz (Triple.seq hpush hj), SR.le hety hR',
          I.target G hen hetgt (m := 3) (by omega) (by simp) (by omega), R⟩
      · -- The condition is not zero: ISZERO gives zero and the code falls into the next block.
        have hj := Logic.jumpi_of_eq_zero (message := msg) (memory := M) (state := st)
          (substate := ss) (returnData := .empty) (destination := BitVec.ofNat 256 (c.offset e))
          (rest := T') hlt2 hcode2 (show 10 ≤ g1 by omega) (iszero_nonzero hc)
        simp only [exec, List.length_cons, show ¬ S'.length + 1 + 1 > 1024 by omega, ite_false,
          hc, SimOut]
        refine ⟨⟨by omega, fun _ => by omega⟩, _, T', M, g1 - 10, st, ss,
          Triple.seq hisz (Triple.seq hpush hj), SR.le hfty hR',
          ⟨hseg, by omega, ?_, I.le_top, I.mem⟩, R⟩
        have hm : 22100 * (cost p c (b + 1) + 3) ≤ 22100 * k := Nat.mul_le_mul_left _ (by omega)
        rw [Nat.mul_add] at hm
        omega
    | none =>
      by_cases hD : dropped p b i rest = true
      · rcases dropped_true hD with ⟨rfl, rfl⟩ | ⟨rfl, rfl, hn⟩
        · -- A jump to the next block, left out: the code falls into it.
          simp only [blockOk, hT, hD, ite_true, fallOk, Bool.and_eq_true, Bool.or_eq_true,
            decide_eq_true_eq] at hok
          simp only [lowerInstrs, hT, hD, ite_true, List.nil_append] at I
          have hS := I.stack
          simp only [exec, show ¬ S.length + 1 > 1024 by omega, ite_false, SimOut]
          exact ⟨⟨by omega, fun _ => by omega⟩, pc, T, M, g, st, ss, Triple.of_imp fun _ h => h,
            SR.le hok.1.2 hR, I.weaken hok.2, R⟩
        · -- The last block's STOP, left out: the code ends.
          simp only [lowerInstrs, hT, hD, ite_true, List.nil_append] at I
          have hseg := I.seg
          rw [lowerFrom_nil p c (by omega)] at hseg
          have hpc := hseg.nil_end
          simp only [exec, SimOut]
          exact Spec.consequence (Logic.stop_of_size_le (by omega))
            (fun _ h => h) fun evm h => postL_stop R hself evm h
      have hD' : dropped p b i rest = false := by simpa using hD
      have hok' : blockStep p c (fun h known ty k => blockOk p c b h known ty k rest) h known ty k i =
          true := by
        simpa only [blockOk, hT, hD', Bool.false_eq_true, ite_false] using hok
      have I' : Inv c code call (lowerInstr i ++ (lowerInstrs p c b rest ++
          lowerFrom p c (b + 1) (p.blocks.drop (b + 1)))) k pc S s M g := by
        simpa only [lowerInstrs, hT, hD', Bool.false_eq_true, ite_false, List.append_assoc] using I
      clear hok hD hD' hT
      have IH := exec_sim (o := o) (ss0 := ss0) G hdata hvalue hstatic hself hcaller ho b hb rest
      rcases i with mop | ⟨e, ar⟩ | t | t | t | _ | _ | _ | _ | _ | _ | _
      · rcases mop with sop | _ | _ | _ | _
        · by_cases hpush : ∃ v, sop = .push v
          · obtain ⟨v, rfl⟩ := hpush
            simp only [blockStep, Bool.and_eq_true, decide_eq_true_eq] at hok'
            simp only [lowerInstr, List.singleton_append] at I'
            obtain ⟨next, hd, hseg⟩ := I'.seg.head
            simp only [Item.expected] at hd
            have hS := I'.stack; have hG := I'.gas
            obtain ⟨g1, hg1, hpush⟩ := push_item (msg := msg) (M := M) (st := st) (ss := ss) (gas := g)
              (stack := T) hd (by omega) (by omega)
            have hv : BitVec.ofNat 256 v.toNat = v := by simp
            rw [hv] at hpush
            rw [exec_stack (next := v :: S) rfl (by omega) (by simp; omega)]
            exact SimOut.pre hpush (IH (h + 1) (v :: known.take 1) _ (v :: S) (v :: T) (k - 1) s next M g1
              st ss hok'.2 (by simp; omega)
              ((List.prefix_cons_inj v).2 ((List.take_prefix 1 known).trans hk))
              (SR.cons (τ := some false) rfl hR) (I'.next hok'.1 hseg (by simp) (by omega)) R)
          · have hne : ∀ v, sop ≠ .push v := fun v he => hpush ⟨v, he⟩
            obtain ⟨hk1, byte, hbyte, h', ty', S', T', hstep, hstepT, hR', hh', hlen', known', hkn,
              hok⟩ := stack_sim (ctx := context o call s) hne hok' hh hk hR
            rw [lowerInstr_stack hne, hbyte] at I'
            simp only [Option.getD_some, List.singleton_append] at I'
            obtain ⟨next, hd, hseg⟩ := I'.seg.head
            simp only [Item.expected] at hd
            obtain ⟨hlt, hcode, rfl⟩ := op_item hd
            rw [← hctx] at hstepT
            have hS := I'.stack; have hG := I'.gas
            obtain ⟨g1, hg1, hrule⟩ := stack_rule (M := M) (st := st) (ss := ss) (gas := g)
              (stack := T) hbyte hlt hcode hstepT (by omega) (by omega)
            rw [exec_stack hstep (by omega) (by omega)]
            exact SimOut.pre hrule (IH h' known' ty' S' T' (k - 1) s (pc + 1) M g1 st ss hok (by omega)
              hkn hR' (I'.next hk1 hseg (by omega) (by omega)) R)
        · simp [blockStep] at hok'
        · -- MSTORE.
          rcases known with _ | ⟨ow, known'⟩
          · simp [blockStep] at hok'
          simp only [blockStep, Bool.and_eq_true, decide_eq_true_eq] at hok'
          obtain ⟨⟨⟨⟨hk1, h2⟩, hin⟩, hdat⟩, hok'⟩ := hok'
          rcases S with _ | ⟨x, _ | ⟨v, S'⟩⟩
          · simp at hh; omega
          · simp at hh; omega
          rcases T with _ | ⟨x', _ | ⟨v', T'⟩⟩
          · simp at hL
          · simp at hL
          have htake := hR.data hdat
          simp only [List.take_succ_cons, List.take_zero, List.cons.injEq] at htake
          obtain ⟨rfl, rfl, -⟩ := htake
          have hR' : SR c (ty.drop 2) S' T' := by simpa using SR.drop 2 hR
          obtain ⟨rfl, -⟩ := List.cons_prefix_cons.1 hk
          simp only [lowerInstr, List.singleton_append] at I'
          obtain ⟨next, hd, hseg⟩ := I'.seg.head
          simp only [Item.expected] at hd
          obtain ⟨hlt, hcode, rfl⟩ := op_item hd
          have hS := I'.stack; have hG := I'.gas
          simp only [List.length_cons] at hS hG hh hL
          have hmod : M.size % 32 = 0 := by rw [I'.mem.1]; omega
          obtain ⟨hle, hcost⟩ := extend_cost (o := ow) (sz := 32) hmod G.top_mod I'.le_top
            (Or.inr hin)
          obtain ⟨hmem', hsize⟩ := memRel_store (o := ow) (v := v) I'.mem (by have := G.top_le; omega)
          have hext := size_memoryExtend_extendMemory' (memory := M) (start := ow) (length := 32)
            hmod (by decide)
          rw [size_memoryExtend] at hext
          have h32 : (32 : U256).toNat = 32 := rfl
          rw [h32] at hext
          have hM' : (memoryWrite (memoryExtend M (extendMemory M.size [(ow, 32)]).expandBy)
              ow.toNat (wordBytes v)).size = M.size + (extendMemory M.size [(ow, 32)]).expandBy := by
            rw [hsize, hext]
          rw [exec_store (by omega)]
          refine SimOut.pre (Logic.mstore (start := ow) (value := v) (rest := T') (memory := M)
            (gas := g) hlt hcode (by omega)) (IH (h - 2) [] _ S' T' (k - 1) _ (pc + 1) _ _ st ss hok'
            (by omega) (List.nil_prefix) hR' ⟨hseg, by omega, ?_, by rw [hM']; omega, hmem'⟩
            ⟨R.storage, R.account, R.logs⟩)
          rw [hM']; omega
        · simp [blockStep] at hok'
        · simp [blockStep] at hok'
      · rcases e with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | n | _ | _ | _
        all_goals try (simp [blockStep] at hok'; done)
        · -- SLOAD.
          rcases ar with _ | _ | ar
          · simp [blockStep] at hok'
          rotate_left
          · simp [blockStep] at hok'
          simp only [blockStep, Bool.and_eq_true, decide_eq_true_eq] at hok'
          obtain ⟨⟨⟨hk1, h1⟩, hdat⟩, hok⟩ := hok'
          rcases S with _ | ⟨x, S'⟩
          · simp at hh; omega
          rcases T with _ | ⟨x', T'⟩
          · simp at hL
          obtain rfl := (SR.head hR hdat).symm
          have hR' := (SR.uncons.1 hR).2
          simp only [lowerInstr, List.singleton_append] at I'
          obtain ⟨next, hd, hseg⟩ := I'.seg.head
          simp only [Item.expected] at hd
          obtain ⟨hlt, hcode, rfl⟩ := op_item hd
          have hS := I'.stack; have hG := I'.gas
          simp only [List.length_cons] at hS hG hh hL
          rw [exec_effect1 (w := s.storage x) rfl (by omega)]
          have hrule := Logic.sload (message := msg) (memory := M) (state := st) (substate := ss)
            (returnData := .empty) (key := x) (rest := T') (gas := g) (by decide) hlt hcode rfl
            (by split <;> omega)
          rw [R.storage x] at hrule
          refine SimOut.pre hrule ?_
          have hreads := fun k : Word => State.TransactionState.recordStorageRead_reads st
            msg.currentTarget msg.currentTarget (U256.toBeBytes x) (U256.toBeBytes k) default
          refine IH h [] _ _ _ (k - 1) s (pc + 1) M _ _ _ hok (by simp; omega) (List.nil_prefix)
            (SR.cons (τ := some false) rfl (by simpa using hR')) (I'.next hk1 hseg (by simp) (by split <;> omega))
            ⟨fun k => ?_, ?_, R.logs⟩
          · rw [(hreads k).2.1]
            exact R.storage k
          · rw [(hreads x).1]
            exact R.account
        · -- SSTORE.
          rcases ar with _ | _ | _ | ar
          · simp [blockStep] at hok'
          · simp [blockStep] at hok'
          rotate_left
          · simp [blockStep] at hok'
          simp only [blockStep, Bool.and_eq_true, decide_eq_true_eq] at hok'
          obtain ⟨⟨⟨hk1, h2⟩, hdat⟩, hok⟩ := hok'
          rcases S with _ | ⟨x, _ | ⟨v, S'⟩⟩
          · simp at hh; omega
          · simp at hh; omega
          rcases T with _ | ⟨x', _ | ⟨v', T'⟩⟩
          · simp at hL
          · simp at hL
          have htake := hR.data hdat
          simp only [List.take_succ_cons, List.take_zero, List.cons.injEq] at htake
          obtain ⟨rfl, rfl, -⟩ := htake
          have hR' : SR c (ty.drop 2) S' T' := by simpa using SR.drop 2 hR
          simp only [lowerInstr, List.singleton_append] at I'
          obtain ⟨next, hd, hseg⟩ := I'.seg.head
          simp only [Item.expected] at hd
          obtain ⟨hlt, hcode, rfl⟩ := op_item hd
          have hS := I'.stack; have hG := I'.gas
          simp only [List.length_cons] at hS hG hh hL
          rw [exec_effect2 (s' := { s with storage := SolarTV.Machine.update s.storage x v }) rfl
            (by omega)]
          have hcost := sstoreCost_le (st.getStorageOriginal msg.currentTarget (U256.toBeBytes x))
            (st.getStorage msg.currentTarget (U256.toBeBytes x)) v
            (decide (U256.toBeBytes x ∉ ss.accessedStorageKeys.getD msg.currentTarget ∅))
          obtain ⟨st', hnew, hothers, -, hacc, -, -, hrule⟩ := Logic.sstore_of_account
            (message := msg) (memory := M) (state := st) (substate := ss) (returnData := .empty)
            (key := x) (new := v) (rest := T') (gas := g) (by decide) (by decide) hlt hcode hstatic
            rfl (by simp only [CALL_STIPEND]; omega) (by omega) R.account
          refine SimOut.pre hrule ?_
          refine IH (h - 2) [] _ S' T' (k - 1) _ (pc + 1) M _ _ _ hok (by omega) (List.nil_prefix)
            hR' ?_ ⟨fun k => ?_, by rw [hacc]; exact R.account, R.logs⟩
          · exact ⟨hseg, by omega, by omega, I'.le_top, I'.mem⟩
          by_cases hk : k = x
          · subst hk
            rw [hnew]
            simp [SolarTV.Machine.update]
          · rw [hothers _ _ (Or.inr fun he => hk (U256.toBeBytes_inj he)), R.storage k]
            simp [SolarTV.Machine.update, hk]
        · -- CALLDATALOAD.
          rcases ar with _ | _ | ar
          · simp [blockStep] at hok'
          rotate_left
          · simp [blockStep] at hok'
          simp only [blockStep, Bool.and_eq_true, decide_eq_true_eq] at hok'
          obtain ⟨⟨⟨hk1, h1⟩, hdat⟩, hok⟩ := hok'
          rcases S with _ | ⟨x, S'⟩
          · simp at hh; omega
          rcases T with _ | ⟨x', T'⟩
          · simp at hL
          obtain rfl := (SR.head hR hdat).symm
          have hR' := (SR.uncons.1 hR).2
          simp only [lowerInstr, List.singleton_append] at I'
          obtain ⟨next, hd, hseg⟩ := I'.seg.head
          simp only [Item.expected] at hd
          obtain ⟨hlt, hcode, rfl⟩ := op_item hd
          have hS := I'.stack; have hG := I'.gas
          simp only [List.length_cons] at hS hG hh hL
          rw [exec_effect1 (w := SolarTV.Machine.calldataWord call x) rfl (by omega)]
          have hrule := Logic.calldataload (message := msg) (memory := M) (state := st)
            (substate := ss) (returnData := .empty) (start := x) (rest := T') (gas := g) hlt hcode
            (by omega)
          rw [hdata, ← calldataWord_eq] at hrule
          exact SimOut.pre hrule (IH h [] _ _ _ (k - 1) s (pc + 1) M (g - 3) st ss hok (by simp; omega)
            (List.nil_prefix) (SR.cons (τ := some false) rfl (by simpa using hR')) (I'.next hk1 hseg (by simp) (by omega)) R)
        · -- CALLDATASIZE.
          rcases ar with _ | ar
          rotate_left
          · simp [blockStep] at hok'
          simp only [blockStep, Bool.and_eq_true, decide_eq_true_eq] at hok'
          obtain ⟨hk1, hok⟩ := hok'
          simp only [lowerInstr, List.singleton_append] at I'
          obtain ⟨next, hd, hseg⟩ := I'.seg.head
          simp only [Item.expected] at hd
          obtain ⟨hlt, hcode, rfl⟩ := op_item hd
          have hS := I'.stack; have hG := I'.gas
          rw [exec_effect0 (w := BitVec.ofNat 256 call.calldata.size) rfl (by omega)]
          have hrule := Logic.calldatasize (message := msg) (memory := M) (state := st)
            (substate := ss) (returnData := .empty) (stack := T) (gas := g) hlt hcode (by omega)
            (by unfold STACK_LIMIT; omega)
          rw [hdata] at hrule
          exact SimOut.pre hrule (IH (h + 1) [] _ _ _ (k - 1) s (pc + 1) M (g - 2) st ss hok
            (by simp; omega) (List.nil_prefix) (SR.cons (τ := some false) rfl hR) (I'.next hk1 hseg (by simp) (by omega)) R)
        · -- CALLVALUE.
          rcases ar with _ | ar
          rotate_left
          · simp [blockStep] at hok'
          simp only [blockStep, Bool.and_eq_true, decide_eq_true_eq] at hok'
          obtain ⟨hk1, hok⟩ := hok'
          simp only [lowerInstr, List.singleton_append] at I'
          obtain ⟨next, hd, hseg⟩ := I'.seg.head
          simp only [Item.expected] at hd
          obtain ⟨hlt, hcode, rfl⟩ := op_item hd
          have hS := I'.stack; have hG := I'.gas
          rw [exec_effect0 (w := BitVec.ofNat 256 call.callvalue) rfl (by omega)]
          have hrule := Logic.callvalue (message := msg) (memory := M) (state := st)
            (substate := ss) (returnData := .empty) (stack := T) (gas := g) hlt hcode (by omega)
            (by unfold STACK_LIMIT; omega)
          rw [hvalue] at hrule
          exact SimOut.pre hrule (IH (h + 1) [] _ _ _ (k - 1) s (pc + 1) M (g - 2) st ss hok
            (by simp; omega) (List.nil_prefix) (SR.cons (τ := some false) rfl hR) (I'.next hk1 hseg (by simp) (by omega)) R)
        · -- CALLER.
          rcases ar with _ | ar
          rotate_left
          · simp [blockStep] at hok'
          simp only [blockStep, Bool.and_eq_true, decide_eq_true_eq] at hok'
          obtain ⟨⟨henv, hk1⟩, hok⟩ := hok'
          obtain ⟨hoc, -⟩ := ho henv
          simp only [lowerInstr, List.singleton_append] at I'
          obtain ⟨next, hd, hseg⟩ := I'.seg.head
          simp only [Item.expected] at hd
          obtain ⟨hlt, hcode, rfl⟩ := op_item hd
          have hS := I'.stack; have hG := I'.gas
          rw [exec_effect0 (w := o.caller.setWidth 256) rfl (by omega)]
          have hrule := Logic.caller (message := msg) (memory := M) (state := st)
            (substate := ss) (returnData := .empty) (stack := T) (gas := g) hlt hcode (by omega)
            (by unfold STACK_LIMIT; omega)
          rw [hcaller, ← hoc] at hrule
          exact SimOut.pre hrule (IH (h + 1) [] _ _ _ (k - 1) s (pc + 1) M (g - 2) st ss hok
            (by simp; omega) (List.nil_prefix) (SR.cons (τ := some false) rfl hR) (I'.next hk1 hseg (by simp) (by omega)) R)
        · -- LOGn.
          rcases known with _ | ⟨ow, _ | ⟨sw, known'⟩⟩
          · simp [blockStep] at hok'
          · simp [blockStep] at hok'
          simp only [blockStep, rangeOk, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hok'
          obtain ⟨⟨⟨⟨⟨⟨⟨hn4, rfl⟩, hk1⟩, hnh⟩, hdat⟩, hin⟩, hlc⟩, hok⟩ := hok'
          rcases S with _ | ⟨x, _ | ⟨y, S1⟩⟩
          · simp at hk
          · simp at hk
          obtain ⟨rfl, hk'⟩ := List.cons_prefix_cons.1 hk
          obtain ⟨rfl, -⟩ := List.cons_prefix_cons.1 hk'
          rcases T with _ | ⟨x', _ | ⟨y', T1⟩⟩
          · simp at hL
          · simp at hL
          simp only [List.length_cons] at hh hL
          obtain ⟨tops, S2, rfl, hlen⟩ : ∃ tops S2, S1 = tops ++ S2 ∧ tops.length = n :=
            ⟨S1.take n, S1.drop n, (List.take_append_drop n S1).symm, by simp; omega⟩
          obtain ⟨tops', T2, rfl, hlen'⟩ : ∃ tops' T2, T1 = tops' ++ T2 ∧ tops'.length = n :=
            ⟨T1.take n, T1.drop n, (List.take_append_drop n T1).symm, by simp; omega⟩
          subst hlen
          have htake := hR.data hdat
          simp only [List.take_succ_cons, List.cons.injEq, List.take_left' hlen',
            List.take_left' rfl] at htake
          obtain ⟨rfl, rfl, rfl⟩ := htake
          have hR' : SR c (ty.drop (tops.length + 2)) S2 T2 := by
            simpa using SR.drop (tops.length + 2) hR
          simp only [lowerInstr, hn4, ite_true, List.singleton_append] at I'
          obtain ⟨next, hd, hseg⟩ := I'.seg.head
          simp only [Item.expected] at hd
          obtain ⟨hlt, hcode, rfl⟩ := op_item hd
          have hS := I'.stack; have hG := I'.gas
          simp only [List.length_cons, List.length_append] at hS hG hh hL
          have hmod : M.size % 32 = 0 := by rw [I'.mem.1]; omega
          obtain ⟨hle, hcost⟩ := extend_cost (o := ow) (sz := sw) hmod G.top_mod I'.le_top
            (hin.imp_left fun h0 => BitVec.eq_of_toNat_eq (by simpa using h0))
          have hbound : sw = 0 ∨ ow.toNat + sw.toNat ≤ 2 ^ 32 :=
            hin.imp (fun h0 => BitVec.eq_of_toNat_eq (by simpa using h0))
              (fun h0 => by have := G.top_le; omega)
          have hrule := Logic.log (n := ⟨tops.length, by omega⟩) (message := msg) (memory := M)
            (state := st) (substate := ss) (returnData := .empty) (start := ow) (size := sw)
            (words := tops) (rest := T2) (gas := g) rfl hlt hcode (decode_log ⟨tops.length, by omega⟩) hstatic
            (show logCost tops.length sw + (extendMemory M.size [(ow, sw)]).cost ≤ g by omega)
          dsimp only at hrule
          rw [exec_log (by omega)]
          have hM' := size_memoryExtend M (extendMemory M.size [(ow, sw)]).expandBy
          obtain ⟨L, hL1, hL2⟩ := R.logs
          refine SimOut.pre hrule (IH (h - (tops.length + 2)) [] _ S2 T2 (k - 1) _ (pc + 1) _ _ st _
            hok (by omega) (List.nil_prefix) hR' ⟨hseg, by omega, ?_, by rw [hM']; omega,
            memRel_expand I'.mem hbound⟩ ⟨R.storage, R.account, ?_⟩)
          · rw [hM']; omega
          · refine ⟨L ++ [⟨msg.currentTarget, tops.map U256.toBeBytes,
              memoryReadBytes (memoryExtend M (extendMemory M.size [(ow, sw)]).expandBy)
                ow.toNat sw.toNat⟩], by simp [Array.toList_push, hL1],
              forall₂_snoc hL2 ⟨rfl, rfl, ?_⟩⟩
            exact read_eq I'.mem
        · -- KECCAK256.
          rcases ar with _ | _ | _ | ar
          · simp [blockStep] at hok'
          · simp [blockStep] at hok'
          rotate_left
          · simp [blockStep] at hok'
          rcases known with _ | ⟨ow, _ | ⟨sw, known'⟩⟩
          · simp [blockStep] at hok'
          · simp [blockStep] at hok'
          simp only [blockStep, rangeOk, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hok'
          obtain ⟨⟨⟨⟨⟨⟨henv, hk1⟩, h2⟩, hdat⟩, hin⟩, hkc⟩, hok⟩ := hok'
          rcases S with _ | ⟨x, _ | ⟨y, S'⟩⟩
          · simp at hk
          · simp at hk
          obtain ⟨rfl, hk'⟩ := List.cons_prefix_cons.1 hk
          obtain ⟨rfl, -⟩ := List.cons_prefix_cons.1 hk'
          rcases T with _ | ⟨x', _ | ⟨y', T'⟩⟩
          · simp at hL
          · simp at hL
          have htake := hR.data hdat
          simp only [List.take_succ_cons, List.take_zero, List.cons.injEq] at htake
          obtain ⟨rfl, rfl, -⟩ := htake
          have hR' : SR c (ty.drop 2) S' T' := by simpa using SR.drop 2 hR
          simp only [lowerInstr, List.singleton_append] at I'
          obtain ⟨next, hd, hseg⟩ := I'.seg.head
          simp only [Item.expected] at hd
          obtain ⟨hlt, hcode, rfl⟩ := op_item hd
          have hS := I'.stack; have hG := I'.gas
          simp only [List.length_cons] at hS hG hh hL
          have hmod : M.size % 32 = 0 := by rw [I'.mem.1]; omega
          obtain ⟨hle, hcost⟩ := extend_cost (o := ow) (sz := sw) hmod G.top_mod I'.le_top
            (hin.imp_left fun h0 => BitVec.eq_of_toNat_eq (by simpa using h0))
          have hbound : sw = 0 ∨ ow.toNat + sw.toNat ≤ 2 ^ 32 :=
            hin.imp (fun h0 => BitVec.eq_of_toNat_eq (by simpa using h0))
              (fun h0 => by have := G.top_le; omega)
          obtain ⟨-, hkec⟩ := ho henv
          have hrule := Logic.keccak256 (message := msg) (memory := M) (state := st) (substate := ss)
            (returnData := .empty) (start := ow) (size := sw) (rest := T') (gas := g) hlt hcode
            (by omega)
          rw [byteArray_eq_of_map (read_eq I'.mem), ← hkec] at hrule
          rw [exec_keccak (by omega)]
          have hM' := size_memoryExtend M (extendMemory M.size [(ow, sw)]).expandBy
          refine SimOut.pre hrule (IH (h - 1) [] _ _ _ (k - 1) _ (pc + 1) _ _ st ss hok
            (by simp; omega) (List.nil_prefix) (SR.cons (τ := some false) rfl hR') ⟨hseg, by simp; omega, ?_,
            by rw [hM']; omega, memRel_expand I'.mem hbound⟩ ⟨R.storage, R.account, R.logs⟩)
          rw [hM']; omega
      · -- JUMP.
        simp only [blockStep, jumpOk, Bool.and_eq_true, decide_eq_true_eq] at hok'
        obtain ⟨hk2, ⟨⟨⟨⟨htn, htgt⟩, hneed⟩, hty⟩, hcost⟩⟩ := hok'
        simp only [lowerInstr, List.cons_append, List.nil_append] at I'
        obtain ⟨n1, hd1, hs1⟩ := I'.seg.head
        obtain ⟨n2, hd2, -⟩ := hs1.head
        simp only [Item.expected] at hd1 hd2
        obtain ⟨hlt2, hcode2, rfl⟩ := op_item hd2
        have hS := I'.stack; have hG := I'.gas
        have hoff := toNat_offset (G.target t htn htgt).2.1 G.size_lt
        obtain ⟨g1, hg1, hpush⟩ := push_item (msg := msg) (M := M) (st := st) (ss := ss) (gas := g)
          (stack := T) hd1 (by omega) (by omega)
        have hj := Logic.jump (message := msg) (memory := M) (state := st) (substate := ss)
          (returnData := .empty) (rest := T) hlt2 hcode2 (show 8 ≤ g1 by omega)
          (by rw [hoff]; exact (G.target t htn htgt).1)
        rw [hoff] at hj
        simp only [exec, show ¬ S.length + 1 > 1024 by omega, ite_false, SimOut]
        exact ⟨⟨by omega, fun _ => le_trans hneed hh⟩, c.offset t, T, M, g1 - 8, st, ss,
          Triple.seq hpush hj, SR.le hty hR,
          I'.target G htn htgt (m := 2) (by omega) (le_refl _) (by omega), R⟩
      · -- JUMPI.
        simp only [blockStep, jumpOk, Bool.and_eq_true, decide_eq_true_eq] at hok'
        obtain ⟨⟨⟨⟨hk2, h1⟩, hdat⟩, ⟨⟨⟨⟨htn, htgt⟩, hneed⟩, hty⟩, hcost⟩⟩, hok'⟩ := hok'
        rcases S with _ | ⟨cond, S'⟩
        · simp at hh; omega
        rcases T with _ | ⟨cond', T'⟩
        · simp at hL
        obtain rfl := (SR.head hR hdat).symm
        have hR' := (SR.uncons.1 hR).2
        simp only [lowerInstr, List.cons_append, List.nil_append] at I'
        obtain ⟨n1, hd1, hs1⟩ := I'.seg.head
        obtain ⟨n2, hd2, hseg⟩ := hs1.head
        simp only [Item.expected] at hd1 hd2
        obtain ⟨hlt2, hcode2, rfl⟩ := op_item hd2
        have hS := I'.stack; have hG := I'.gas
        simp only [List.length_cons] at hS hh hL
        have hoff := toNat_offset (G.target t htn htgt).2.1 G.size_lt
        obtain ⟨g1, hg1, hpush⟩ := push_item (msg := msg) (M := M) (st := st) (ss := ss) (gas := g)
          (stack := cond :: T') hd1 (by omega) (by simp; omega)
        by_cases hc : cond = 0
        · subst hc
          have hj := Logic.jumpi_of_eq_zero (message := msg) (memory := M) (state := st)
            (substate := ss) (returnData := .empty) (destination := BitVec.ofNat 256 (c.offset t))
            (rest := T') hlt2 hcode2 (show 10 ≤ g1 by omega) rfl
          simp only [exec, List.length_cons, show ¬ S'.length + 1 + 1 > 1024 by omega, ite_false,
            ite_true]
          exact SimOut.pre (Triple.seq hpush hj) (IH (h - 1) [] _ S' T' (k - 2) s (n1 + 1) M
            (g1 - 10) st ss hok' (by omega) (List.nil_prefix) hR'
            (I'.next2 hk2 hseg (by simp only [List.length_cons]; omega) (by omega)) R)
        · have hj := Logic.jumpi_taken (message := msg) (memory := M) (state := st)
            (substate := ss) (returnData := .empty) (destination := BitVec.ofNat 256 (c.offset t))
            (rest := T') hlt2 hcode2 (show 10 ≤ g1 by omega) hc
            (by rw [hoff]; exact (G.target t htn htgt).1)
          rw [hoff] at hj
          simp only [exec, List.length_cons, show ¬ S'.length + 1 + 1 > 1024 by omega, ite_false,
            hc, SimOut]
          exact ⟨⟨by omega, fun _ => by omega⟩, c.offset t, T', M, g1 - 10, st, ss,
            Triple.seq hpush hj, SR.le hty hR',
            I'.target G htn htgt (m := 2) (by omega) (by simp) (by omega), R⟩
      · -- A pushed return label: a PUSH of the block's offset.
        simp only [blockStep, Bool.and_eq_true, decide_eq_true_eq] at hok'
        obtain ⟨⟨⟨hk1, hmem⟩, ht32⟩, hok⟩ := hok'
        have hmem' : t ∈ c.rets := by simpa using hmem
        simp only [lowerInstr, List.singleton_append] at I'
        obtain ⟨next, hd, hseg⟩ := I'.seg.head
        simp only [Item.expected] at hd
        have hS := I'.stack; have hG := I'.gas
        obtain ⟨g1, hg1, hpush⟩ := push_item (msg := msg) (M := M) (st := st) (ss := ss) (gas := g)
          (stack := T) hd (by omega) (by omega)
        have htn : (BitVec.ofNat 256 t).toNat = t := by
          rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
        simp only [exec, show ¬ S.length + 1 > 1024 by omega, ite_false]
        exact SimOut.pre hpush (IH (h + 1) [] _ _ _ (k - 1) s next M g1 st ss hok (by simp; omega)
          (List.nil_prefix) (SR.cons ⟨by rw [htn]; exact hmem', by rw [htn]⟩ hR)
          (I'.next hk1 hseg (by simp) (by omega)) R)
      · -- A dynamic jump to a return label: a JUMP to the label's offset.
        simp only [blockStep, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq,
          List.all_eq_true] at hok'
        obtain ⟨⟨⟨hk1, h1⟩, hlab⟩, hall⟩ := hok'
        rcases S with _ | ⟨x, S'⟩
        · simp at hh; omega
        rcases T with _ | ⟨y, T'⟩
        · simp at hL
        obtain ⟨hw, hR'⟩ := SR.uncons.1 hR
        rw [hlab] at hw
        obtain ⟨hmem, rfl⟩ := hw
        have hj' := hall _ hmem
        simp only [jumpOk, Bool.and_eq_true, decide_eq_true_eq] at hj'
        obtain ⟨⟨⟨⟨htn, htgt⟩, hneed⟩, hty⟩, hcost⟩ := hj'
        simp only [lowerInstr, List.singleton_append] at I'
        obtain ⟨next, hd, -⟩ := I'.seg.head
        simp only [Item.expected] at hd
        obtain ⟨hlt, hcode, rfl⟩ := op_item hd
        have hS := I'.stack; have hG := I'.gas
        simp only [List.length_cons] at hS hh hL
        have hoff := toNat_offset (G.target _ htn htgt).2.1 G.size_lt
        have hj := Logic.jump (message := msg) (memory := M) (state := st) (substate := ss)
          (returnData := .empty) (destination := BitVec.ofNat 256 (c.offset x.toNat)) (rest := T')
          hlt hcode (show 8 ≤ g by omega) (by rw [hoff]; exact (G.target _ htn htgt).1)
        rw [hoff] at hj
        simp only [exec, SimOut]
        exact ⟨⟨by omega, fun _ => by omega⟩, c.offset x.toNat, T', M, g - 8, st, ss, hj,
          SR.le hty hR', I'.target G htn htgt (m := 1) (by omega) (by simp) (by omega), R⟩
      · -- A conditional dynamic jump and a jump table: outside the fragment.
        simp [blockStep] at hok'
      · simp [blockStep] at hok'
      · -- STOP.
        simp only [lowerInstr, List.singleton_append] at I'
        obtain ⟨next, hd, -⟩ := I'.seg.head
        simp only [Item.expected] at hd
        obtain ⟨hlt, hcode, -⟩ := op_item hd
        simp only [exec, SimOut]
        exact Spec.consequence (Logic.stop hlt hcode) (fun _ h => h)
          fun evm h => postL_stop R hself evm h
      · -- RETURN.
        rcases known with _ | ⟨ow, _ | ⟨sw, known'⟩⟩
        · simp [blockStep] at hok'
        · simp [blockStep] at hok'
        simp only [blockStep, rangeOk, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hok'
        obtain ⟨hdat, hin⟩ := hok'
        rcases S with _ | ⟨x, _ | ⟨y, S'⟩⟩
        · simp at hk
        · simp at hk
        obtain ⟨rfl, hk'⟩ := List.cons_prefix_cons.1 hk
        obtain ⟨rfl, -⟩ := List.cons_prefix_cons.1 hk'
        rcases T with _ | ⟨x', _ | ⟨y', T'⟩⟩
        · simp at hL
        · simp at hL
        have htake := hR.data hdat
        simp only [List.take_succ_cons, List.take_zero, List.cons.injEq] at htake
        obtain ⟨rfl, rfl, -⟩ := htake
        simp only [lowerInstr, List.singleton_append] at I'
        obtain ⟨next, hd, -⟩ := I'.seg.head
        simp only [Item.expected] at hd
        obtain ⟨hlt, hcode, -⟩ := op_item hd
        have hG := I'.gas
        have hmod : M.size % 32 = 0 := by rw [I'.mem.1]; omega
        obtain ⟨-, hcost⟩ := extend_cost (o := ow) (sz := sw) hmod G.top_mod I'.le_top
          (hin.imp_left fun h0 => BitVec.eq_of_toNat_eq (by simpa using h0))
        simp only [exec, SolarTV.EVM.Program.output, SimOut, Bool.false_eq_true, ↓reduceIte]
        exact Spec.consequence (return_postS (ss := ss) hlt hcode (by omega) rfl
          (by rw [read_eq I'.mem]; rfl) rfl (R.slot hself)) (fun _ h => h)
          (fun _ h => ⟨ss, h, R.logs⟩)
      · -- REVERT.
        rcases known with _ | ⟨ow, _ | ⟨sw, known'⟩⟩
        · simp [blockStep] at hok'
        · simp [blockStep] at hok'
        simp only [blockStep, rangeOk, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hok'
        obtain ⟨hdat, hin⟩ := hok'
        rcases S with _ | ⟨x, _ | ⟨y, S'⟩⟩
        · simp at hk
        · simp at hk
        obtain ⟨rfl, hk'⟩ := List.cons_prefix_cons.1 hk
        obtain ⟨rfl, -⟩ := List.cons_prefix_cons.1 hk'
        rcases T with _ | ⟨x', _ | ⟨y', T'⟩⟩
        · simp at hL
        · simp at hL
        have htake := hR.data hdat
        simp only [List.take_succ_cons, List.take_zero, List.cons.injEq] at htake
        obtain ⟨rfl, rfl, -⟩ := htake
        simp only [lowerInstr, List.singleton_append] at I'
        obtain ⟨next, hd, -⟩ := I'.seg.head
        simp only [Item.expected] at hd
        obtain ⟨hlt, hcode, -⟩ := op_item hd
        have hG := I'.gas
        have hmod : M.size % 32 = 0 := by rw [I'.mem.1]; omega
        obtain ⟨-, hcost⟩ := extend_cost (o := ow) (sz := sw) hmod G.top_mod I'.le_top
          (hin.imp_left fun h0 => BitVec.eq_of_toNat_eq (by simpa using h0))
        simp only [exec, SolarTV.EVM.Program.output, SimOut, ↓reduceIte]
        exact Spec.consequence (revert_postS (ss := ss) (by decide) hlt hcode (by omega) rfl
          (by rw [read_eq I'.mem]; rfl) rfl) (fun _ h => h) (fun _ h => ⟨ss, h, R.logs⟩)
      · simp [blockStep] at hok'

open SolarTV.EVM.Program in
/-- EthLib runs the code from a block's offset as SolarTV runs the program from that block,
to the observable SolarTV's run ends with. -/
theorem run_sim {p : Program} {c : Cert} {code : ByteArray} (G : Glob p c code)
    {o : SolarTV.Machine.Oracle} {call : SolarTV.Call} {msg : Message .fusaka} {ss0 : Substate}
    (hdata : msg.data = call.calldata) (hvalue : msg.value = BitVec.ofNat 256 call.callvalue)
    (hstatic : msg.isStatic = false) (hself : msg.currentTarget = Target.address selfAddress)
    (hcaller : msg.caller = Target.address callerAddress) (ho : c.env = true → OracleOk o) :
    ∀ (fuel b : Nat) (S T : List Word) (s : SolarTV.Machine.State) (pc : Nat) (M : ByteArray)
      (g : Nat) (st : State.TransactionState) (ss : Substate)
      (r : SolarTV.Machine.Halt × SolarTV.Machine.State),
      b ≤ p.blocks.length → (b < p.blocks.length → c.need b ≤ S.length) → SR c (c.entry b) S T →
      Inv c code call (lowerFrom p c b (p.blocks.drop b)) (cost p c b) pc S s M g →
      Rel msg ss0 st ss s →
      SolarTV.Machine.iterate (block o call p) fuel (b, S, s) = some r →
      Spec .fusaka (At code msg pc T M g st ss .empty) (PostL call msg.currentTarget ss0 r.2 r.1)
  | 0, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hr => by simp [SolarTV.Machine.iterate] at hr
  | fuel + 1, b, S, T, s, pc, M, g, st, ss, r, hle, hneed, hR, I, R, hr => by
    by_cases hb : b < p.blocks.length
    · have hblk : p.blocks[b]? = some p.blocks[b] := List.getElem?_eq_getElem hb
      simp only [SolarTV.Machine.iterate, block, hblk] at hr
      obtain ⟨hL, hblock⟩ := G.block b hb
      obtain ⟨pc1, g1, hlabel, I1⟩ : ∃ pc1 g1, Hoare .fusaka (At code msg pc T M g st ss .empty)
          (At code msg pc1 T M g1 st ss .empty) ∧
          Inv c code call (lowerInstrs p c b p.blocks[b] ++
            lowerFrom p c (b + 1) (p.blocks.drop (b + 1))) (cost p c b - labelItems p c b)
            pc1 S s M g1 := by
        have I' := I
        rw [lowerFrom_drop p c hb, lowerBlock, List.append_assoc] at I'
        by_cases ht : isTarget p c b = true
        · have hl : labelItems p c b = 1 := by simp [labelItems, ht]
          rw [hl] at hL ⊢
          simp only [ht, ite_true, List.singleton_append] at I'
          obtain ⟨next, hd, hseg⟩ := I'.seg.head
          simp only [Item.expected] at hd
          obtain ⟨hlt, hcode, rfl⟩ := op_item hd
          have hG := I'.gas
          exact ⟨pc + 1, g - 1, Logic.jumpdest hlt hcode (by omega),
            I'.next hL hseg (Nat.le_succ _) (by omega)⟩
        · have hl : labelItems p c b = 0 := by simp [labelItems, ht]
          rw [hl, Nat.sub_zero]
          simp only [ht, Bool.false_eq_true, ite_false, List.nil_append] at I'
          exact ⟨pc, g, Triple.of_imp fun _ h => h, I'⟩
      have hsim := exec_sim (o := o) G hdata hvalue hstatic hself hcaller ho b hb p.blocks[b]
        (c.need b) [] (c.entry b) S T _ s pc1 M g1 st ss hblock (hneed hb) (List.nil_prefix) hR I1 R
      generalize exec o call b p.blocks[b] S s = x at hr hsim
      rcases x with ⟨halt, s'⟩ | ⟨t, S', s'⟩
      · simp only [Option.some.injEq] at hr
        subst hr
        exact Spec.seq hlabel hsim
      · simp only at hr
        obtain ⟨hneed', pc', T', M', g', st', ss', hh, hR', I', R'⟩ := hsim
        have := run_sim G hdata hvalue hstatic hself hcaller ho fuel t S' T' s' pc' M' g' st' ss' r
          hneed'.1 hneed'.2 hR' I' R' hr
        exact Spec.seq (Triple.seq hlabel hh) this
    · obtain rfl : b = p.blocks.length := by omega
      have hblk : p.blocks[p.blocks.length]? = none := List.getElem?_eq_none (by omega)
      simp only [SolarTV.Machine.iterate, block, hblk, ite_true, Option.some.injEq] at hr
      subst hr
      have hseg := I.seg
      rw [lowerFrom_nil p c (by omega)] at hseg
      have hpc := hseg.nil_end
      exact Spec.consequence (Logic.stop_of_size_le (by omega))
        (fun _ h => h) fun evm h => postL_stop R hself evm h

/-- The values of EthLib's logs that match SolarTV's world are SolarTV's logs. -/
theorem logs_of_match {a : Address} : ∀ {w : List SolarTV.Machine.Event}
    {L : List EthLib.Execution.Blocks.Log}, List.Forall₂ (LogMatch a) w L →
    L.map (fun log => (log.topics.map fun topic => bytesToNat topic.toList,
      log.data.toList.map (·.toNat))) =
      w.filterMap fun
        | .log topics data => some (topics.map BitVec.toNat, data.map BitVec.toNat)
        | .call .. | .read _ | .create .. => none
  | [], [], .nil => rfl
  | .log topics data :: w, l :: L, .cons ⟨_, ht, hd⟩ rest => by
    simp only [List.map_cons, List.filterMap_cons, logs_of_match rest, ht, hd, List.map_map]
    congr 2
    apply List.map_congr_left
    intro x _
    simp only [Function.comp_apply, U256.toList_toBeBytes]
    rw [bytesToNat_natToBytes_of_lt (by have := x.isLt; simpa using this)]
  | .call .. :: _, _ :: _, .cons h _ => h.elim
  | .read _ :: _, _ :: _, .cons h _ => h.elim
  | .create .. :: _, _ :: _, .cons h _ => h.elim

/-- The callee's storage before the call, at its account, which exists, is the call's: the
relation at the start of the frame. -/
theorem rel_initial (code : ByteArray) (call : SolarTV.Call) :
    Rel (Target.message code call) Substate.empty (Target.preState code call) Substate.empty
      (SolarTV.Machine.State.initial call) := by
  have htgt : (Target.message code call).currentTarget = Target.address selfAddress := rfl
  refine ⟨fun k => ?_, ?_, ⟨[], by simp, .nil⟩⟩
  · apply BitVec.eq_of_toNat_eq
    have hkey : U256.toBeBytes k = Target.storageKey k.toNat :=
      ((storageKey_eq_toBeBytes k.toNat k).2 (Nat.mod_eq_of_lt k.isLt)).symm
    rw [htgt, hkey, getStorage_preState code call k.toNat]
    simp only [SolarTV.Machine.State.initial, BitVec.toNat_ofNat]
    exact (Nat.mod_eq_of_lt (slotValue_lt _ _)).symm
  · rw [htgt]
    exact Option.isSome_iff_ne_none.2 (account_preState code call)

/-! ## Calls with value

A call with value moves it from the caller, who holds exactly it, to the contract before the
frame starts (`moveEther_preState_any`, for every value). The move changes balances only: the
contract keeps its storage and its account (`moveEther_recipient`), so the frame starts in a
state related to the call's storage as with no value, and `run_sim` holds from it. -/

section Move

open EthLib.Execution.State

theorem getAccount_recordAccountRead (tx : TransactionState) (a b : Address) :
    (tx.recordAccountRead a).getAccount b = tx.getAccount b := rfl

/-- After `modifyState` at `a`, the storage and the account of every other address are as before. -/
theorem modifyState_ne {fork : Fork} {tx tx' : TransactionState} {a : Address}
    {f : Account → Except StateError Account} (h : tx.modifyState fork a f = .ok tx') {b : Address}
    (hb : b ≠ a) (k : Bytes32) :
    tx'.getStorage b k = tx.getStorage b k ∧ tx'.getAccountOptional b = tx.getAccountOptional b := by
  unfold TransactionState.modifyState at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · cases h
  · split at h <;> cases h <;>
      simp [TransactionState.destroyAccount, TransactionState.destroyStorage,
        TransactionState.setAccount, TransactionState.recordAccountRead,
        TransactionState.getStorage, TransactionState.getAccountOptional, StorageMap.slot,
        Std.ExtTreeMap.getElem?_erase, Std.ExtTreeMap.getElem?_insert, Std.ExtTreeSet.mem_insert,
        Ne.symm hb] <;> rfl

/-- After `modifyState` at `a` with a step that keeps the nonce, from an account with a nonzero
nonce, the storage of `a` is as before and `a` has an account. -/
theorem modifyState_self {fork : Fork} {tx tx' : TransactionState} {a : Address}
    {f : Account → Except StateError Account} (h : tx.modifyState fork a f = .ok tx')
    (hf : ∀ acc acc', f acc = .ok acc' → acc'.nonce = acc.nonce) (hn : (tx.getAccount a).nonce ≠ 0)
    (k : Bytes32) :
    tx'.getStorage a k = tx.getStorage a k ∧ (tx'.getAccountOptional a).isSome = true := by
  unfold TransactionState.modifyState at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · cases h
  · rename_i acc' hacc
    have hnon := hf _ _ hacc
    rw [getAccount_recordAccountRead] at hnon
    split at h
    · rename_i hc
      exfalso
      simp [TransactionState.accountExistsAndIsEmpty, TransactionState.setAccount,
        TransactionState.getAccountOptional, hnon, hn] at hc
    · cases h
      exact ⟨rfl, by simp [TransactionState.setAccount, TransactionState.recordAccountRead,
        TransactionState.getAccountOptional]⟩

theorem credit_nonce (r : Address) (amt : U256) :
    ∀ acc acc', Account.credit r amt acc = .ok acc' → acc'.nonce = acc.nonce := by
  intro acc acc' h
  unfold Account.credit at h
  split at h <;> cases h
  rfl

/-- A move of ether from `s` to another address `r` with an account of nonzero nonce keeps the
storage of `r`, and `r` keeps an account. -/
theorem moveEther_recipient {fork : Fork} {tx tx' : TransactionState} {s r : Address} {amt : U256}
    (h : tx.moveEther fork s r amt = .ok tx') (hrs : r ≠ s) (hn : (tx.getAccount r).nonce ≠ 0)
    (k : Bytes32) :
    tx'.getStorage r k = tx.getStorage r k ∧ (tx'.getAccountOptional r).isSome = true := by
  unfold TransactionState.moveEther at h
  simp only [bind, Except.bind] at h
  split at h
  · cases h
  · rename_i t1 h1
    obtain ⟨hs1, ha1⟩ := modifyState_ne h1 hrs k
    have hn1 : (t1.getAccount r).nonce ≠ 0 := by
      simpa only [TransactionState.getAccount, ha1] using hn
    obtain ⟨hs2, ha2⟩ := modifyState_self h (credit_nonce r amt) hn1 k
    exact ⟨hs2.trans hs1, ha2⟩

theorem getAccount_preState_self (code : ByteArray) (call : SolarTV.Call) :
    (Target.preState code call).getAccount (Target.address selfAddress) =
      { nonce := 1, balance := 0, codeHash := EthLib.Cryptography.Hash.Keccak.keccak256 code } := by
  simp only [Target.preState, TransactionState.getAccount, TransactionState.getAccountOptional,
    TransactionState.ofBlock, State.getAccountOptional]
  rw [Std.ExtTreeMap.getElem?_insert, ite_eq_right (by decide +kernel), Std.ExtTreeMap.getElem?_insert,
    ite_eq_left (by decide +kernel)]
  simp

theorem getAccount_preState_caller (code : ByteArray) (call : SolarTV.Call) :
    ((Target.preState code call).getAccount (Target.address callerAddress)).balance =
      BitVec.ofNat 256 call.callvalue := by
  simp only [Target.preState, TransactionState.getAccount, TransactionState.getAccountOptional,
    TransactionState.ofBlock, State.getAccountOptional]
  simp

theorem modifyState_exists {fork : Fork} {tx : TransactionState} {a : Address}
    {f : Account → Except StateError Account} {acc : Account} (h : f (tx.getAccount a) = .ok acc) :
    ∃ tx', tx.modifyState fork a f = .ok tx' := by
  unfold TransactionState.modifyState
  simp only [bind, Except.bind, pure, Except.pure, getAccount_recordAccountRead, h]
  split <;> exact ⟨_, rfl⟩

/-- The move of the call's value from the caller, who holds exactly it, to the contract, which
holds none, succeeds, for every value. -/
theorem moveEther_preState_any (code : ByteArray) (call : SolarTV.Call) :
    ∃ st', (Target.preState code call).moveEther .fusaka (Target.address callerAddress)
      (Target.address selfAddress) (BitVec.ofNat 256 call.callvalue) = .ok st' := by
  have hAB : Target.address selfAddress ≠ Target.address callerAddress := by decide
  have hd : Account.debit (Target.address callerAddress) (BitVec.ofNat 256 call.callvalue)
      ((Target.preState code call).getAccount (Target.address callerAddress)) =
      .ok { (Target.preState code call).getAccount (Target.address callerAddress) with
        balance := 0 } := by
    simp [Account.debit, getAccount_preState_caller]
  obtain ⟨t1, h1⟩ := modifyState_exists (fork := .fusaka) hd
  have ha1 := (modifyState_ne h1 hAB (Target.storageKey 0)).2
  have hc : Account.credit (Target.address selfAddress) (BitVec.ofNat 256 call.callvalue)
      (t1.getAccount (Target.address selfAddress)) =
      .ok { t1.getAccount (Target.address selfAddress) with
        balance := 0 + BitVec.ofNat 256 call.callvalue } := by
    have : t1.getAccount (Target.address selfAddress) =
        (Target.preState code call).getAccount (Target.address selfAddress) := by
      simp only [TransactionState.getAccount, ha1]
    rw [this, getAccount_preState_self]
    unfold Account.credit
    rw [ite_eq_left_iff.mpr (fun h => absurd ?_ h)]
    dsimp only
    have h1 := (BitVec.ofNat 256 call.callvalue).isLt
    have h0 : (0 : U256).toNat = 0 := rfl
    omega
  obtain ⟨t2, h2⟩ := modifyState_exists (fork := .fusaka) hc
  exact ⟨t2, by simp [TransactionState.moveEther, bind, Except.bind, h1, h2]⟩

end Move

section RunAny

open SolidCore.Refinement.Evm.Symex

/-- What `processMessage` gives from a frame that ends as `PostS X` shows for a substate whose logs
are those of `ss` and then SolarTV's world `w`. -/
def MsgOut (X : SolarTV.Observable) (a : Address) (ss : Substate) (w : List SolarTV.Machine.Event)
    (evm : Evm .fusaka Nat) : Prop :=
  ∃ ssF, LogsRel a ss ssF w ∧ evm.error = errorOf X ∧ evm.output.toList.map (·.toNat) = X.output ∧
    (X.success = true → evm.substate.logs = ssF.logs ∧ ∀ slot,
      (evm.state.getStorage (Target.address selfAddress) (Target.storageKey slot)).toNat =
        X.storage slot)

/-- processMessage at Fusaka of a message with no value, to code that is no precompile. -/
theorem processMessage_postL {c : ByteArray} (message : Message .fusaka)
    (hcode : message.code = c) (hv : message.value = 0)
    (hpre : precompileAddress .fusaka message = none) (X : SolarTV.Observable) (a : Address)
    (w : List SolarTV.Machine.Event) (st : EthLib.Execution.State.TransactionState) (ss : Substate)
    (h : Spec .fusaka (At c message 0 [] .empty message.gas st ss .empty)
      (fun evm => ∃ ssF, PostS X ssF evm ∧ LogsRel a ss ssF w)) :
    ∃ evm, processMessage (Meter := Nat) .fusaka message st ss = .ok evm ∧ MsgOut X a ss w evm.1 := by
  rw [processMessage]
  have hss : startState .fusaka message st = st := by
    simp [startState, show ¬ (Fork.fusaka < Fork.paris) by decide]
  simp only [hss, hpre]
  split
  · rename_i htr; exact absurd htr.2 (by simp [hv])
  simp only [pure, Except.pure, bind, Except.bind]
  split
  · rename_i e hr
    simp only [hv, ne_eq, not_true_eq_false, and_false, ite_false] at hr
    obtain ⟨after, h', -⟩ := runFrame_of_spec hcode h hr
    cases h'
  · rename_i after hr
    simp only [hv, ne_eq, not_true_eq_false, and_false, ite_false] at hr
    obtain ⟨after', h', -, ssF, ⟨herr, hout, hlogs, hst⟩, hL⟩ := runFrame_of_spec hcode h hr
    cases h'
    refine ⟨_, rfl, ssF, hL, ?_, ?_, ?_⟩
    · simp only [rollbackOnError]; split <;> simp [herr]
    · simp only [rollbackOnError]; split <;> exact hout
    · intro hX
      have hE : errorOf X = none := by simp [errorOf, hX]
      simp only [rollbackOnError, herr, hE, Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
      exact ⟨hlogs, hst hX⟩

/-- processMessage at Fusaka of a message with nonzero value, whose move of the value succeeds
into st', to code that is no precompile. -/
theorem processMessage_postL_move {c : ByteArray} (message : Message .fusaka)
    (hcode : message.code = c) (htr : message.shouldTransferValue = true) (hv : message.value ≠ 0)
    (hpre : precompileAddress .fusaka message = none) (X : SolarTV.Observable) (a : Address)
    (w : List SolarTV.Machine.Event) (st st' : EthLib.Execution.State.TransactionState)
    (ss : Substate)
    (hmove : st.moveEther .fusaka message.caller message.currentTarget message.value = .ok st')
    (h : Spec .fusaka (At c message 0 [] .empty message.gas st' ss .empty)
      (fun evm => ∃ ssF, PostS X ssF evm ∧ LogsRel a ss ssF w)) :
    ∃ evm, processMessage (Meter := Nat) .fusaka message st ss = .ok evm ∧ MsgOut X a ss w evm.1 := by
  rw [processMessage]
  have hss : startState .fusaka message st = st := by
    simp [startState, show ¬ (Fork.fusaka < Fork.paris) by decide]
  simp only [hss, hpre, htr, ne_eq, hv, not_false_eq_true, and_self, ↓reduceIte, hmove]
  simp only [pure, Except.pure, bind, Except.bind, Except.mapError]
  -- At Fusaka a move of value pushes no transfer log.
  have hsub : ∀ x : Substate,
      { x with logs := (pushTransferLog .fusaka x.logs message.caller message.currentTarget
        message.value) } = x := fun x => by
    simp [pushTransferLog, show ¬ (Fork.fusaka ≥ Fork.glamsterdam) by decide]
  split
  · rename_i e hr
    simp only [htr, hv, not_false_eq_true, and_self, ↓reduceIte, hsub] at hr
    obtain ⟨after, h', -⟩ := runFrame_of_spec hcode h hr
    cases h'
  · rename_i after hr
    simp only [htr, hv, not_false_eq_true, and_self, ↓reduceIte, hsub] at hr
    obtain ⟨after', h', -, ssF, ⟨herr, hout, hlogs, hst⟩, hL⟩ := runFrame_of_spec hcode h hr
    cases h'
    refine ⟨_, rfl, ssF, hL, ?_, ?_, ?_⟩
    · simp only [rollbackOnError]; split <;> simp [herr]
    · simp only [rollbackOnError]; split <;> exact hout
    · intro hX
      have hE : errorOf X = none := by simp [errorOf, hX]
      simp only [rollbackOnError, herr, hE, Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
      exact ⟨hlogs, hst hX⟩

/-- Target.run of any call, with or without value, is SolarTV's observable of `halt` in `s` when the
frame from every state related to the call's storage ends as `PostL` shows: with value, the frame
starts after the move of the value, which keeps the contract's storage. -/
theorem run_of_rel (code : ByteArray) (call : SolarTV.Call) (s : SolarTV.Machine.State)
    (halt : SolarTV.Machine.Halt)
    (h : ∀ st, Rel (Target.message code call) Substate.empty st Substate.empty
        (SolarTV.Machine.State.initial call) →
      Spec .fusaka (At code (Target.message code call) 0 [] .empty 10000000 st Substate.empty
        .empty) (PostL call (Target.address selfAddress) Substate.empty s halt)) :
    Target.run code call = some (SolarTV.Machine.observe call s halt) := by
  have key : ∃ evm, processMessage (Meter := Nat) .fusaka (Target.message code call)
      (Target.preState code call) Substate.empty = .ok evm ∧
      MsgOut (SolarTV.Machine.observe call s halt) (Target.address selfAddress) Substate.empty
        s.world evm.1 := by
    by_cases hv : (Target.message code call).value = 0
    · exact processMessage_postL _ rfl hv (precompileAddress_message code call) _ _ _ _ _
        (h _ (rel_initial code call))
    · obtain ⟨st', hmove⟩ := moveEther_preState_any code call
      have hn : ((Target.preState code call).getAccount (Target.address selfAddress)).nonce ≠ 0 := by
        rw [getAccount_preState_self]; simp
      have hAB : Target.address selfAddress ≠ Target.address callerAddress := by decide
      have R0 := rel_initial code call
      have R : Rel (Target.message code call) Substate.empty st' Substate.empty
          (SolarTV.Machine.State.initial call) :=
        ⟨fun k => ((moveEther_recipient hmove hAB hn _).1).trans (R0.storage k),
          (moveEther_recipient hmove hAB hn (Target.storageKey 0)).2, R0.logs⟩
      exact processMessage_postL_move _ rfl rfl hv (precompileAddress_message code call) _ _ _ _
        st' _ hmove (h st' R)
  obtain ⟨evm, hr, ssF, ⟨L, hL1, hL2⟩, herr, hout, hst⟩ := key
  have hlogs := logs_of_match hL2
  have hL1' : ssF.logs.toList = L := by simpa [Substate.empty] using hL1
  have hfail : (SolarTV.Machine.observe call s halt).success = false →
      (SolarTV.Machine.observe call s halt).logs = [] ∧
      (SolarTV.Machine.observe call s halt).storage = slotValue call.storage := by
    cases halt <;> simp [SolarTV.Machine.observe]
  have hok : (SolarTV.Machine.observe call s halt).success = true →
      (SolarTV.Machine.observe call s halt).logs = SolarTV.Machine.logs s := by
    cases halt <;> simp [SolarTV.Machine.observe]
  simp only [Target.run, hr]
  generalize SolarTV.Machine.observe call s halt = X at *
  have hsucc : evm.1.error.isNone = X.success := by
    rw [herr]; cases hX : X.success <;> simp [errorOf, hX]
  congr 1
  cases X with
  | mk success output logs storage =>
    simp only at hsucc hout hfail hok hst ⊢
    rw [SolarTV.Observable.mk.injEq]
    refine ⟨hsucc, hout, ?_, ?_⟩
    · rw [hsucc]
      cases hs : success
      · simp [(hfail hs).1]
      · simp only [ite_true]
        rw [(hst hs).1, hL1', hlogs, hok hs]
        rfl
    · funext slot
      rw [hsucc]
      cases hs : success
      · simp [(hfail hs).2]
      · simp only [ite_true]
        exact (hst hs).2 slot

/-- EVM IR to bytecode, for every program and code the checker accepts: on every call, with or
without value, from any storage, under every oracle whose caller and hash are EthLib's when the
program reads them, every observable SolarTV's EVM IR semantics gives for p, EthLib gives for
code. -/
theorem stage_of_check_env {p : Program} {code : ByteArray} {c : Cert} (hc : check p code c = true)
    (o : SolarTV.Machine.Oracle) (ho : c.env = true → OracleOk o) (scope : SolarTV.Call → Prop) :
    SolarTV.Stage (SolarTV.evmirSem o) SolidCore.Refinement.ethLib p
      (show SolidCore.Refinement.ethLib.Prog from code) scope := by
  obtain ⟨G, hseg, hneed0, hlen, hgas⟩ := glob_of_check hc
  intro call _ obs hrun
  change (SolarTV.EVM.Program.layer.result o p call).map _ = _ at hrun
  obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.1 hrun
  obtain ⟨n, hn⟩ := SolarTV.EVM.Program.layer.ends_of_result hr
  have hm0 : memoryGasCost (ByteArray.empty).size = 0 := by decide
  have I0 : Inv c code call (lowerFrom p c 0 (p.blocks.drop 0)) (cost p c 0) 0 []
      (SolarTV.Machine.State.initial call) .empty 10000000 :=
    ⟨by rw [List.drop_zero]; exact hseg, by simpa using hlen, by rw [hm0]; omega,
      by simp, memRel_initial⟩
  exact run_of_rel code call r.2 r.1 fun st R => run_sim (msg := Target.message code call)
    (ss0 := Substate.empty) G rfl (by simp [Target.message]) rfl rfl rfl ho n 0 [] [] _ 0 .empty
    10000000 st Substate.empty r (Nat.zero_le _) (by simp [hneed0]) (SR.nil c _) I0 R hn

/--
info: 'SolidCore.Refinement.Solar.Assemble.stage_of_check_env' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms stage_of_check_env

/-- EVM IR to bytecode for a program that reads neither the caller nor a hash, under every
oracle: `stage_of_check_env`. -/
theorem stage_of_check_all {p : Program} {code : ByteArray} {c : Cert} (hc : check p code c = true)
    (o : SolarTV.Machine.Oracle) (scope : SolarTV.Call → Prop) (hpure : c.env = false := by rfl) :
    SolarTV.Stage (SolarTV.evmirSem o) SolidCore.Refinement.ethLib p
      (show SolidCore.Refinement.ethLib.Prog from code) scope :=
  stage_of_check_env hc o (fun h => absurd (h.symm.trans hpure) (by decide)) scope

/-- EVM IR to bytecode under every oracle with EthLib's caller and hash. -/
theorem stage_of_check_eth {p : Program} {code : ByteArray} {c : Cert} (hc : check p code c = true)
    (o : SolarTV.Machine.Oracle) (scope : SolarTV.Call → Prop) :
    SolarTV.Stage (SolarTV.evmirSem (ethOracle o)) SolidCore.Refinement.ethLib p
      (show SolidCore.Refinement.ethLib.Prog from code) scope :=
  stage_of_check_env hc _ (fun _ => ethOracle_ok o) scope

/--
info: 'SolidCore.Refinement.Solar.Assemble.stage_of_check_all' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms stage_of_check_all

end RunAny

/-- EVM IR to bytecode, for every program and code the checker accepts, on a scope of calls with
no value: `stage_of_check_all`, which holds on every call, with any value. -/
theorem stage_of_check {p : Program} {code : ByteArray} {c : Cert} (hc : check p code c = true)
    (o : SolarTV.Machine.Oracle) {scope : SolarTV.Call → Prop}
    (_hscope : ∀ call, scope call → call.callvalue = 0) (hpure : c.env = false := by rfl) :
    SolarTV.Stage (SolarTV.evmirSem o) SolidCore.Refinement.ethLib p
      (show SolidCore.Refinement.ethLib.Prog from code) scope :=
  stage_of_check_all hc o scope hpure

/--
info: 'SolidCore.Refinement.Solar.Assemble.stage_of_check' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms stage_of_check

end SolidCore.Refinement.Solar.Assemble

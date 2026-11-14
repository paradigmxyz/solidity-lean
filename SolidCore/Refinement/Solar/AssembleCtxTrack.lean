import SolidCore.Refinement.Solar.AssembleSim

/-!
# Which block a block of EVM IR leaves to, from the labels on its stack

The checker of \`AssembleCtx\` checks a block once in each of its contexts, and a context names
the context each successor enters in. A dynamic jump goes to the label on top of the stack, so
which block it reaches, and so which context, is what the words on the stack are: this file reads
it from SolarTV alone. A \`Lab\` is what a word is known to be: \`some ts\` says it is a label of
one of the blocks \`ts\`; \`none\`, nothing. \`exits\` runs a block's instructions over such words
(a pushed label is its block, DUP and SWAP move what they move, every other result is unknown),
and \`exits_sound\`: every next block SolarTV's run of the block reaches is one \`exits\` lists,
with the words it lists at it. The EVM side is \`AssembleCut.seg\`'s; nothing here reads the
bytecode.
-/

namespace SolidCore.Refinement.Solar.AssembleCtx

open SolarTV SolarTV.Machine
open SolarTV.EVM.Program (exec stepOp context)
open SolidCore.Refinement.Solar.Assemble

/-- What a word is known to be: a label of one of the blocks listed, or unknown. -/
abbrev Lab := Option (List Nat)

/-- What the word at depth \`i\` is known to be. -/
def labAt (L : List Lab) (i : Nat) : Lab := L.getD i none

/-- The words after SWAP of the top word and the word at depth \`i + 1\`. -/
def labSwap (L : List Lab) (i : Nat) : List Lab :=
  List.ofFn (n := max L.length (i + 2)) fun j =>
    if j.val = 0 then labAt L (i + 1) else if j.val = i + 1 then labAt L 0 else labAt L j.val

/-- Whether an effect leaves a result on the stack. -/
def pushesE : Effect → Bool
  | .mstore | .mstore8 | .sstore | .tstore | .log _ | .calldatacopy | .mcopy | .codecopy
  | .returndatacopy => false
  | _ => true

/-- The next blocks a block's instructions reach from words known as \`L\`, each with what the
words are known to be there; \`none\` for a dynamic jump to an unknown word, or an instruction
the reading leaves out. -/
def exits (b : Nat) : List Lab → List SolarTV.EVM.Program.Instr → Option (List (Nat × List Lab))
  | L, [] => some [(b + 1, L)]
  | L, .op o :: rest =>
    match o with
    | .stack op =>
      match op with
      | .push _ => exits b (none :: L) rest
      | .dup i => exits b (labAt L i.val :: L) rest
      | .swap i => exits b (labSwap L i.val) rest
      | .pop => exits b L.tail rest
      | op =>
        match stackNeed op with
        | some (n, _) => exits b (none :: L.drop n) rest
        | none => none
    | .load => exits b (none :: L.drop 1) rest
    | .store => exits b (L.drop 2) rest
    | _ => none
  | L, .effect e a :: rest =>
    if pushesE e then exits b (none :: L.drop a) rest else exits b (L.drop a) rest
  | L, .jump t :: _ => some [(t, L)]
  | L, .jumpi t :: rest => (exits b L.tail rest).map ((t, L.tail) :: ·)
  | L, .pushLabel t :: rest => exits b (some [t % 2 ^ 256] :: L) rest
  | L, .jumpDyn :: _ =>
    match labAt L 0 with
    | some ts => some (ts.map fun t => (t, L.tail))
    | none => none
  | _, .jumpiDyn :: _ => none
  | _, .jumpTable _ :: _ => none
  | _, .stop :: _ => some []
  | _, .ret :: _ => some []
  | _, .revert :: _ => some []
  | _, .invalid :: _ => some []

/-- The words of \`S\` are what \`L\` says they are. -/
def LabOk (L : List Lab) (S : List Word) : Prop :=
  ∀ i ts, labAt L i = some ts → ∀ w, S[i]? = some w → w.toNat ∈ ts

theorem labAt_drop (L : List Lab) (n i : Nat) : labAt (L.drop n) i = labAt L (n + i) := by
  simp [labAt, List.getD_eq_getElem?_getD, List.getElem?_drop]

theorem labAt_cons_zero (x : Lab) (L : List Lab) : labAt (x :: L) 0 = x := rfl

theorem labAt_cons_succ (x : Lab) (L : List Lab) (i : Nat) : labAt (x :: L) (i + 1) = labAt L i := by
  simp [labAt]

theorem labAt_nil (i : Nat) : labAt [] i = none := by simp [labAt]

theorem LabOk.nil (S : List Word) : LabOk [] S := fun i ts h => by simp [labAt_nil] at h

theorem LabOk.drop {L : List Lab} {S : List Word} (h : LabOk L S) (n : Nat) :
    LabOk (L.drop n) (S.drop n) := by
  intro i ts hl w hw
  rw [labAt_drop] at hl
  rw [List.getElem?_drop] at hw
  exact h _ ts hl w hw

theorem LabOk.tail {L : List Lab} {S : List Word} (h : LabOk L S) : LabOk L.tail S.tail := by
  have := h.drop 1
  simpa using this

theorem LabOk.cons {L : List Lab} {S : List Word} (h : LabOk L S) {x : Lab} {v : Word}
    (hx : ∀ ts, x = some ts → v.toNat ∈ ts) : LabOk (x :: L) (v :: S) := by
  intro i ts hl w hw
  cases i with
  | zero =>
    simp only [labAt_cons_zero] at hl
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hw
    subst hw
    exact hx ts hl
  | succ i =>
    rw [labAt_cons_succ] at hl
    simp only [List.getElem?_cons_succ] at hw
    exact h i ts hl w hw

theorem LabOk.cons_none {L : List Lab} {S : List Word} (h : LabOk L S) (v : Word) :
    LabOk (none :: L) (v :: S) := h.cons (by simp)

theorem LabOk.dup {L : List Lab} {S : List Word} (h : LabOk L S) {i : Nat} {v : Word}
    (hv : S[i]? = some v) : LabOk (labAt L i :: L) (v :: S) :=
  h.cons fun ts hl => h i ts hl v hv

theorem LabOk.swap {L : List Lab} {a : Word} {rest : List Word} (h : LabOk L (a :: rest)) {i : Nat}
    {v : Word} (hv : rest[i]? = some v) : LabOk (labSwap L i) (v :: rest.set i a) := by
  intro j ts hl w hw
  have hlen : j < max L.length (i + 2) := by
    by_contra hc
    simp [labSwap, labAt, List.getD_eq_getElem?_getD, hc] at hl
  have hl' : labAt (labSwap L i) j =
      (if j = 0 then labAt L (i + 1) else if j = i + 1 then labAt L 0 else labAt L j) := by
    simp [labSwap, labAt, List.getD_eq_getElem?_getD, hlen]
  rw [hl'] at hl
  by_cases h0 : j = 0
  · subst h0
    simp only [ite_true] at hl
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hw
    subst hw
    exact h (i + 1) ts hl v (by simpa using hv)
  · simp only [h0, ite_false] at hl
    obtain ⟨j, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
    simp only [List.getElem?_cons_succ] at hw
    by_cases hi : j + 1 = i + 1
    · simp only [hi, ite_true] at hl
      obtain rfl : i = j := by omega
      have hil : i < rest.length := by
        rcases Nat.lt_or_ge i rest.length with h' | h'
        · exact h'
        · simp [List.getElem?_eq_none h'] at hv
      rw [List.getElem?_set_self hil] at hw
      cases hw
      exact h 0 ts hl a rfl
    · simp only [hi, ite_false] at hl
      rw [List.getElem?_set_ne (by omega)] at hw
      exact h (j + 1) ts hl w (by simpa using hw)

theorem LabOk.label {L : List Lab} {S : List Word} (h : LabOk L S) (t : Nat) :
    LabOk (some [t % 2 ^ 256] :: L) (BitVec.ofNat 256 t :: S) :=
  h.cons fun ts hl => by cases hl; simp

/-! ## SolarTV's steps, read backwards -/

theorem pushesE_apply {o : Oracle} {call : Call} {e : Effect} {args : List Word} {s s' : State}
    {r : Option Word} (h : e.apply o call args s = some (r, s')) : r.isSome = pushesE e := by
  unfold Effect.apply at h
  split at h <;> (try split at h) <;> simp_all [pushesE, created]
  all_goals (obtain ⟨rfl, -⟩ := h; rfl)

variable {o : Oracle} {call : Call} {b : Nat}

theorem exec_stack_inv {op : SolarTV.EVM.Op} {rest : List SolarTV.EVM.Program.Instr} {S : List Word} {s : State}
    {y : Nat × List Word × State} (h : exec o call b (.op (.stack op) :: rest) S s = .inr y) :
    ∃ next, SolarTV.EVM.step (context o call s) op S = some next ∧ exec o call b rest next s = .inr y := by
  simp only [exec, stepOp] at h
  by_cases h1 : S.length > 1024
  · simp [h1] at h
  · simp only [h1, ite_false, SolarTV.EVM.stepChecked] at h
    cases hs : SolarTV.EVM.step (context o call s) op S with
    | none => simp [hs, Except.map] at h
    | some next =>
      by_cases h2 : next.length > 1024
      · simp [hs, h2, Except.map] at h
      · simp [hs, h2, Except.map] at h
        exact ⟨next, rfl, h⟩

theorem exec_load_inv {rest : List SolarTV.EVM.Program.Instr} {S : List Word} {s : State}
    {y : Nat × List Word × State} (h : exec o call b (.op .load :: rest) S s = .inr y) :
    ∃ v s1, exec o call b rest (v :: S.drop 1) s1 = .inr y := by
  simp only [exec, stepOp] at h
  by_cases h1 : S.length > 1024
  · simp [h1] at h
  · rcases S with _ | ⟨x, S⟩
    · simp at h
    · by_cases h2 : 1024 < S.length + 1
      · simp [h2] at h
      · simp [h2] at h
        exact ⟨_, _, h⟩

theorem exec_store_inv {rest : List SolarTV.EVM.Program.Instr} {S : List Word} {s : State}
    {y : Nat × List Word × State} (h : exec o call b (.op .store :: rest) S s = .inr y) :
    ∃ s1, exec o call b rest (S.drop 2) s1 = .inr y := by
  simp only [exec, stepOp] at h
  by_cases h1 : S.length > 1024
  · simp [h1] at h
  · rcases S with _ | ⟨x, _ | ⟨z, S⟩⟩
    · simp at h
    · simp at h
    · by_cases h2 : 1024 < S.length + 1 + 1
      · simp [h2] at h
      · simp [h2] at h
        exact ⟨_, h⟩

theorem exec_effect_inv {e : Effect} {a : Nat} {rest : List SolarTV.EVM.Program.Instr} {S : List Word} {s : State}
    {y : Nat × List Word × State} (h : exec o call b (.effect e a :: rest) S s = .inr y) :
    ∃ r s1, r.isSome = pushesE e ∧
      exec o call b rest (match r with | some v => v :: S.drop a | none => S.drop a) s1 = .inr y := by
  simp only [exec] at h
  by_cases h1 : S.length < a
  · simp [h1] at h
  · simp only [h1, ite_false] at h
    cases ha : e.apply o call (S.take a) s with
    | none => simp [ha] at h
    | some rs =>
      obtain ⟨r, s1⟩ := rs
      refine ⟨r, s1, pushesE_apply ha, ?_⟩
      simp only [ha] at h
      cases r with
      | none =>
        try simp only at h ⊢
        split at h
        · cases h
        · exact h
      | some v =>
        try simp only at h ⊢
        split at h
        · cases h
        · exact h

theorem exits_other {b : Nat} {L : List Lab} {rest : List SolarTV.EVM.Program.Instr} {op : SolarTV.EVM.Op}
    (h0 : ∀ v, op ≠ .push v) (h1 : ∀ i, op ≠ .dup i) (h2 : ∀ i, op ≠ .swap i) (h3 : op ≠ .pop) :
    exits b L (.op (.stack op) :: rest) =
      match stackNeed op with
      | some (n, _) => exits b (none :: L.drop n) rest
      | none => none := by
  cases op <;> first | rfl | exact absurd rfl (h0 _) | exact absurd rfl (h1 _) |
    exact absurd rfl (h2 _) | exact absurd rfl h3

/-! ## The reading is sound -/

/-- **Every next block SolarTV's run of a block reaches is one \`exits\` lists**, with the words
there what it lists them as. -/
theorem exits_sound (o : Oracle) (call : Call) (b : Nat) :
    ∀ (is : List SolarTV.EVM.Program.Instr) (L : List Lab) (S : List Word) (s : State) (E : List (Nat × List Lab))
      (y : Nat × List Word × State),
      LabOk L S → exits b L is = some E → exec o call b is S s = .inr y →
      ∃ L', (y.1, L') ∈ E ∧ LabOk L' y.2.1
  | [], L, S, s, E, y, hL, hE, hx => by
    simp only [exits, Option.some.injEq] at hE
    simp only [exec, Sum.inr.injEq] at hx
    subst hE hx
    exact ⟨L, by simp, hL⟩
  | .op o' :: rest, L, S, s, E, y, hL, hE, hx => by
    cases o' with
    | stack op =>
      obtain ⟨next, hstep, hx'⟩ := exec_stack_inv hx
      by_cases hpu : ∃ v, op = .push v
      · obtain ⟨v, rfl⟩ := hpu
        simp only [exits] at hE
        simp only [SolarTV.EVM.step, Option.some.injEq] at hstep
        subst hstep
        exact exits_sound o call b rest _ _ s E y (hL.cons_none v) hE hx'
      by_cases hdu : ∃ i, op = .dup i
      · obtain ⟨i, rfl⟩ := hdu
        simp only [exits] at hE
        simp only [SolarTV.EVM.step] at hstep
        cases hv : S[i.val]? with
        | none => simp [hv] at hstep
        | some v =>
          simp only [hv, Option.map_some, Option.some.injEq] at hstep
          subst hstep
          exact exits_sound o call b rest _ _ s E y (hL.dup hv) hE hx'
      by_cases hsw : ∃ i, op = .swap i
      · obtain ⟨i, rfl⟩ := hsw
        simp only [exits] at hE
        rcases S with _ | ⟨a, S⟩
        · simp [SolarTV.EVM.step] at hstep
        simp only [SolarTV.EVM.step] at hstep
        cases hv : S[i.val]? with
        | none => simp [hv] at hstep
        | some v =>
          simp only [hv, Option.map_some, Option.some.injEq] at hstep
          subst hstep
          exact exits_sound o call b rest _ _ s E y (hL.swap hv) hE hx'
      by_cases hpo : op = .pop
      · subst hpo
        simp only [exits] at hE
        rcases S with _ | ⟨a, S⟩
        · simp [SolarTV.EVM.step] at hstep
        simp only [SolarTV.EVM.step, Option.some.injEq] at hstep
        subst hstep
        exact exits_sound o call b rest _ _ s E y hL.tail hE hx'
      have h0 : ∀ v, op ≠ .push v := fun v e => hpu ⟨v, e⟩
      have h1 : ∀ i, op ≠ .dup i := fun i e => hdu ⟨i, e⟩
      have h2 : ∀ i, op ≠ .swap i := fun i e => hsw ⟨i, e⟩
      rw [exits_other h0 h1 h2 hpo] at hE
      cases hn : stackNeed op with
      | none => simp [hn] at hE
      | some nd =>
        obtain ⟨n, d⟩ := nd
        simp only [hn] at hE
        obtain ⟨v, rfl, -⟩ := step_data hn h1 h2 hpo hstep rfl rfl
        exact exits_sound o call b rest _ _ s E y ((hL.drop n).cons_none v) hE hx'
    | load =>
      simp only [exits] at hE
      obtain ⟨v, s1, hx'⟩ := exec_load_inv hx
      exact exits_sound o call b rest _ _ s1 E y ((hL.drop 1).cons_none v) hE hx'
    | store =>
      simp only [exits] at hE
      obtain ⟨s1, hx'⟩ := exec_store_inv hx
      exact exits_sound o call b rest _ _ s1 E y (hL.drop 2) hE hx'
    | storeByte => simp [exits] at hE
    | size => simp [exits] at hE
    | copy => simp [exits] at hE
    | hash => simp [exits] at hE
  | .effect e a :: rest, L, S, s, E, y, hL, hE, hx => by
    obtain ⟨r, s1, hr, hx'⟩ := exec_effect_inv hx
    simp only [exits] at hE
    cases r with
    | none =>
      simp only [Option.isSome_none] at hr
      rw [← hr] at hE
      simp only [Bool.false_eq_true, ite_false] at hE
      exact exits_sound o call b rest _ _ s1 E y (hL.drop a) hE hx'
    | some v =>
      simp only [Option.isSome_some] at hr
      rw [← hr] at hE
      simp only [ite_true] at hE
      exact exits_sound o call b rest _ _ s1 E y ((hL.drop a).cons_none v) hE hx'
  | .jump t :: rest, L, S, s, E, y, hL, hE, hx => by
    simp only [exits, Option.some.injEq] at hE
    simp only [exec] at hx
    split at hx
    · cases hx
    · simp only [Sum.inr.injEq] at hx
      subst hE hx
      exact ⟨L, by simp, hL⟩
  | .jumpi t :: rest, L, S, s, E, y, hL, hE, hx => by
    simp only [exits] at hE
    cases hE' : exits b L.tail rest with
    | none => simp [hE'] at hE
    | some E' =>
      simp only [hE', Option.map_some, Option.some.injEq] at hE
      subst hE
      simp only [exec] at hx
      split at hx
      · cases hx
      · rcases S with _ | ⟨cnd, S⟩
        · cases hx
        · simp only at hx
          split at hx
          · obtain ⟨L', h1, h2⟩ := exits_sound o call b rest L.tail S s E' y hL.tail hE' hx
            exact ⟨L', List.mem_cons_of_mem _ h1, h2⟩
          · simp only [Sum.inr.injEq] at hx
            subst hx
            exact ⟨L.tail, by simp, hL.tail⟩
  | .pushLabel t :: rest, L, S, s, E, y, hL, hE, hx => by
    simp only [exits] at hE
    simp only [exec] at hx
    split at hx
    · cases hx
    · exact exits_sound o call b rest _ _ s E y (hL.label t) hE hx
  | .jumpDyn :: rest, L, S, s, E, y, hL, hE, hx => by
    simp only [exits] at hE
    cases hl : labAt L 0 with
    | none => simp [hl] at hE
    | some ts =>
      simp only [hl, Option.some.injEq] at hE
      subst hE
      rcases S with _ | ⟨x, S⟩
      · simp [exec] at hx
      · simp only [exec, Sum.inr.injEq] at hx
        subst hx
        refine ⟨L.tail, ?_, by simpa using hL.tail⟩
        have := hL 0 ts hl x rfl
        simp only [List.mem_map]
        exact ⟨x.toNat, this, rfl⟩
  | .jumpiDyn :: rest, L, S, s, E, y, hL, hE, hx => by simp [exits] at hE
  | .jumpTable _ :: rest, L, S, s, E, y, hL, hE, hx => by simp [exits] at hE
  | .stop :: rest, L, S, s, E, y, hL, hE, hx => by simp [exec] at hx
  | .ret :: rest, L, S, s, E, y, hL, hE, hx => by simp [exec] at hx
  | .revert :: rest, L, S, s, E, y, hL, hE, hx => by simp [exec] at hx
  | .invalid :: rest, L, S, s, E, y, hL, hE, hx => by simp [exec] at hx

end SolidCore.Refinement.Solar.AssembleCtx

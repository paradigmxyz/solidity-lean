import Verify.LoopSource.Equiv.Emit
import Verify.LoopSource.Equiv.Seq

-- Inlined from SeqW.lean (kernel-checked) so the module is self-contained.
/-!
# Loop sequents for ends that return words (kernel-checked extension of `Seq.lean`)

`Inv.haltGoals` compares two ends only when their output bytes are constants: an end that returns
a computed word (`return b`) has no goals, so its sequent must be a contradiction and a loop whose
result is a loop word cannot be certified by `allSeqs`. `haltGoalsW` adds the case of two ends of
equal success, writes and logs whose output bytes pair up: equal after `OByte.norm`, or byte `i` of
words `e` and `e'`, which gives the goal `e = e'`. `allSeqsW` is `allSeqs` with `haltGoalsW`, and
`obl_of_seqsW` proves the same `Obl` statement `obl_of_seqs` does, through `obl_of_sound`. Nothing
here is trusted beyond the kernel: every lemma is proved.
-/

namespace Verify.Phase3.Infer
open SolidCore.Refinement.Generic Verify.LoopSource.Equiv Verify.LoopSource.Equiv.Inv

/-- The goal a pair of output bytes needs: none when they are equal after normal forms, `e = e'`
for byte `i` of words `e` and `e'`; `none` (no goal can say it) otherwise. -/
def byteGoal (a b : OByte) : Option (Option F) :=
  if a.norm = b.norm then some none else
  match a, b with
  | .byteOf e i, .byteOf e' i' => if i = i' then some (some (.eq e e')) else none
  | _, _ => none

/-- The goals of two outputs, byte by byte. -/
def outGoals : List OByte → List OByte → Option (List F)
  | [], [] => some []
  | a :: as, b :: bs =>
    match byteGoal a b, outGoals as bs with
    | some g, some gs => some (g.toList ++ gs)
    | _, _ => none
  | _, _ => none

/-- **What two ends must agree on**: `haltGoals`, else, for ends of equal success, writes and logs,
their outputs' goals. -/
def haltGoalsW (H H' : Tree) : Option (List F) :=
  match haltGoals H H' with
  | some gs => some gs
  | none =>
    match H, H' with
    | .halt ok out ws ls, .halt ok' out' ws' ls' =>
      if ok = ok' ∧ ws = ws' ∧ ls = ls' then outGoals out out' else none
    | _, _ => none

theorem byteGoal_sound {ρ : Val} {a b : OByte} {g : Option F} (h : byteGoal a b = some g)
    (hg : ∀ f ∈ g.toList, f.Holds ρ) : a.eval ρ = b.eval ρ := by
  unfold byteGoal at h
  by_cases hn : a.norm = b.norm
  · rw [← OByte.eval_norm ρ a, hn, OByte.eval_norm]
  · simp only [hn, ↓reduceIte] at h
    match a, b, h with
    | .byteOf e i, .byteOf e' i', h =>
      by_cases hi : i = i'
      · subst hi
        simp only [↓reduceIte, Option.some.injEq] at h
        subst h
        have he : e.eval ρ = e'.eval ρ := hg (.eq e e') (by simp)
        simp only [OByte.eval, he]
      · simp [hi] at h
    | .lit _, .lit _, h | .lit _, .byteOf _ _, h | .byteOf _ _, .lit _, h => simp at h

theorem outGoals_sound {ρ : Val} : ∀ {out out' : List OByte} {gs : List F},
    outGoals out out' = some gs → (∀ f ∈ gs, f.Holds ρ) →
      out.map (OByte.eval ρ) = out'.map (OByte.eval ρ)
  | [], [], _, _, _ => rfl
  | a :: as, b :: bs, gs, h, hg => by
    simp only [outGoals] at h
    cases hb : byteGoal a b with
    | none => simp [hb] at h
    | some g =>
      cases ho : outGoals as bs with
      | none => simp [hb, ho] at h
      | some gs' =>
        simp only [hb, ho, Option.some.injEq] at h
        subst h
        simp only [List.map_cons]
        rw [byteGoal_sound hb (fun f hf => hg f (List.mem_append_left _ hf)),
          outGoals_sound ho (fun f hf => hg f (List.mem_append_right _ hf))]
  | [], _ :: _, _, h, _ | _ :: _, [], _, h, _ => by simp [outGoals] at h

/-- **Two ends whose goals hold show the same.** -/
theorem halt_obsW {ρ : Val} (hρ : ρ.Ok) {H H' : Tree} {gs : List F} (h : haltGoalsW H H' = some gs)
    (hg : ∀ g ∈ gs, g.Holds ρ) : (H.eval ρ).obs = (H'.eval ρ).obs := by
  unfold haltGoalsW at h
  cases h0 : haltGoals H H' with
  | some gs0 =>
    rw [h0] at h
    simp only [Option.some.injEq] at h
    subst h
    exact halt_obs hρ h0 hg
  | none =>
    rw [h0] at h
    match H, H', h with
    | .halt ok out ws ls, .halt ok' out' ws' ls', h =>
      simp only at h
      by_cases hc : ok = ok' ∧ ws = ws' ∧ ls = ls'
      · obtain ⟨rfl, rfl, rfl⟩ := hc
        simp only [and_self, ↓reduceIte] at h
        simp only [Tree.eval, Res.obs, outGoals_sound h hg]
      · simp only [hc, ↓reduceIte] at h
        exact nomatch h
    | .ite _ _ _, _, h | .halt _ _ _ _, .ite _ _ _, h => simp at h

/-! ## Sequents with `haltGoalsW` -/

/-- `endSeqs` with `haltGoalsW`. -/
def endSeqsW (S K : List F) (T' T : Tree) : List Seq :=
  (paths T').flatMap fun p' => (paths T).flatMap fun p =>
    let k := K ++ factsF p'.1 ++ factsF p.1
    match haltGoalsW p'.2 p.2 with
    | some gs => gs.map fun g => (hyp S k (some g), some g)
    | none => [(hyp S k none, none)]

/-- `Task.seqs` with `endSeqsW`. -/
def taskSeqsW (n : Nat) (cases : List Facts) (T : Tree) (I : List F) (μ : WExpr) : Task → Option (List Seq)
  | .below => if treeBelow n T = true then some [] else none
  | .inv f entry p => match p.2 with
    | .back hs =>
      let g := f.sub n hs
      some [(hyp (if entry then [] else I) (factsF p.1) (some g), some g)]
    | .exit _ => some []
  | .entryEnd p => match p.2 with
    | .exit T' => some (endSeqsW [] (factsF p.1) T' T)
    | .back _ => some []
  | .iterLeaf p => match p.2 with
    | .exit T' => some (endSeqsW I (factsF p.1) T' T)
    | .back hs =>
      let g := F.lt (Inv.sub n hs μ) μ
      some [(hyp I (factsF p.1) (some g), some g)]
  | .cover => some [(hyp I (cases.map noCase) none, none)]

/-- **All sequents of the leaves**, with `haltGoalsW`. -/
def allSeqsW (n : Nat) (cases : List Facts) (T : Tree) (le li : List (Facts × Out)) (I : List F)
    (μ : WExpr) : Option (List Seq) :=
  ((tasks le li I).mapM (taskSeqsW n cases T I μ)).map List.flatten

theorem endSeqsW_sound {S K : List F} {T' T : Tree} (h : ∀ s ∈ endSeqsW S K T' T, s.Valid) {ρ : Val}
    (hρ : ρ.Ok) (hS : ∀ f ∈ S, f.Holds ρ) (hK : ∀ f ∈ K, f.Holds ρ) :
    (T'.eval ρ).obs = (T.eval ρ).obs := by
  obtain ⟨p', hp', hh', he', -⟩ := paths_sound ρ T'
  obtain ⟨p, hp, hhp, he, -⟩ := paths_sound ρ T
  have hk : ∀ f ∈ K ++ factsF p'.1 ++ factsF p.1, f.Holds ρ := by
    simp only [List.mem_append]
    rintro f ((hf | hf) | hf)
    exacts [hK f hf, factsF_holds hh' f hf, factsF_holds hhp f hf]
  have hv := fun s hs => h s (List.mem_flatMap.mpr ⟨p', hp', List.mem_flatMap.mpr ⟨p, hp, hs⟩⟩)
  simp only [] at hv
  rw [he', he]
  cases hg : haltGoalsW p'.2 p.2 with
  | none => exact (false_of_valid (hv _ (by rw [hg]; exact List.mem_singleton_self _)) hS hk).elim
  | some gs =>
    exact halt_obsW hρ hg fun g hgm =>
      goal_of_valid (hv _ (by rw [hg]; exact List.mem_map_of_mem hgm)) hS hk

theorem seqsW_mem {n : Nat} {cases : List Facts} {T : Tree} {le li : List (Facts × Out)} {I : List F}
    {μ : WExpr} {ss : List Seq} (h : allSeqsW n cases T le li I μ = some ss) {t : Task}
    (ht : t ∈ tasks le li I) : ∃ ts, taskSeqsW n cases T I μ t = some ts ∧ ∀ s ∈ ts, s ∈ ss := by
  unfold allSeqsW at h
  cases hm : (tasks le li I).mapM (taskSeqsW n cases T I μ) with
  | none => simp [hm] at h
  | some tss =>
    simp only [hm, Option.map_some, Option.some.injEq] at h
    subst h
    obtain ⟨ts, hts, hteq⟩ := mapM_mem hm t ht
    exact ⟨ts, hteq, fun s hs => List.mem_flatten.mpr ⟨ts, hts, hs⟩⟩

theorem taskSeqsW_sound {n : Nat} {cases : List Facts} {T : Tree} {I : List F} {μ : WExpr} {t : Task}
    {ts : List Seq} (h : taskSeqsW n cases T I μ t = some ts) (hv : ∀ s ∈ ts, s.Valid) :
    t.Sound n cases T I μ := by
  cases t with
  | below => simp only [taskSeqsW] at h; split at h <;> simp_all [Task.Sound]
  | cover =>
    simp only [taskSeqsW, Option.some.injEq] at h; subst h
    exact fun _ hS hK => (false_of_valid (hv _ (List.mem_singleton_self _)) hS hK).elim
  | inv _ _ p | entryEnd p | iterLeaf p =>
    obtain ⟨K, _ | _⟩ := p <;> simp only [taskSeqsW, Task.Sound, Option.some.injEq] at h ⊢ <;>
      subst h <;>
      first
      | exact fun _ hS hK => goal_of_valid (hv _ (List.mem_singleton_self _)) hS hK
      | exact fun _ hρ hS hK => endSeqsW_sound hv hρ hS hK

/-- **Valid sequents give the obligations**: the statement of `obl_of_seqs`, for `allSeqsW`. -/
theorem obl_of_seqsW {n : Nat} {cases : List Facts} {T : Tree} {le li : List (Facts × Out)}
    {I : List F} {μ : WExpr} {ss : List Seq} (h : allSeqsW n cases T le li I μ = some ss)
    (hv : ∀ s ∈ ss, s.Valid) :
    Obl (fun _ => recOf I μ) id (fun _ => True) (fun _ => True) n cases T le li :=
  obl_of_sound fun _ ht => by
    obtain ⟨_, h1, h2⟩ := seqsW_mem h ht
    exact taskSeqsW_sound h1 fun s hs => hv s (h2 s hs)

/-! ## Refusal: a counterexample to some sequent -/

/-- Some sequent of `ss` has the counterexample `σ`. -/
def rejectsAny (σ : Val) : Option (List Seq) → Bool
  | some ss => ss.any fun s => s.1.all (fun h => decide (h.Holds σ)) &&
      match s.2 with | some g => !decide (g.Holds σ) | none => true
  | none => false

/-- **A counterexample to one sequent refuses them all.** -/
theorem rejectsAny_sound {σ : Val} {ss : List Seq} (h : rejectsAny σ (some ss) = true) :
    ¬ ∀ s ∈ ss, s.Valid := fun hall => by
  simp only [rejectsAny, List.any_eq_true, Bool.and_eq_true] at h
  obtain ⟨s, hs, hh, hg⟩ := h
  refine not_valid_of σ (fun x hx => of_decide_eq_true (List.all_eq_true.mp hh x hx)) ?_ (hall s hs)
  revert hg; cases s.2 <;> simp

/-- **The word normalizer, with `omega` first**: `wordnorm`'s two normalizing steps, then `omega`
(after splitting `if`s when needed). `wordnorm` tries `trivial` first, whose `decide` reaches
the maximum recursion depth on subtraction by a literal word (`(a + (2 ^ 256 - 1)) % 2 ^ 256`)
before `omega` runs; that error is not caught by `first`. -/
macro "wordnormW" : tactic => `(tactic| (
  intro σ h
  simp only [List.forall_mem_cons, List.not_mem_nil, Verify.LoopSource.Equiv.Inv.F.Holds,
    Verify.LoopSource.Equiv.Inv.ev_iszero, Verify.LoopSource.Equiv.Inv.ev_eq,
    Verify.LoopSource.Equiv.Inv.ev_lt, Verify.LoopSource.Equiv.Inv.ev_gt,
    Verify.LoopSource.Equiv.Inv.ite01_eq_zero, Verify.LoopSource.Equiv.Inv.ite01_ne_zero,
    Bool.false_eq_true, Bool.true_eq_false, iff_true, iff_false, not_not, IsEmpty.forall_iff,
    implies_true, and_true] at h ⊢
  all_goals (simp only [SolidCore.Refinement.Generic.WExpr.eval, SolidCore.Refinement.Generic.BinOp.eval,
    SolidCore.Refinement.Generic.UnOp.eval, SolidCore.Refinement.Generic.wordSize, Nat.reducePow,
    Nat.mod_mod, Verify.LoopSource.Equiv.Inv.one_mod_W, Nat.zero_mod, Nat.zero_add] at h ⊢)
  all_goals (first | omega | (split_ifs at h ⊢ <;> omega))))

/-! ## Emission (untrusted): one self-contained obligation module -/

/-- The body of an obligation module after its prelude `pre` (imports, this module's definitions and
the stage and cut, in namespace `ns`): the leaves, tree, invariant, measure and unique sequents as
data, each sequent's `wordnorm` proof, and the theorems `leaves`, `seqs`, `valid`, `obl` and
`certified`. Every fact it states is checked by the kernel when the module is elaborated. -/
def emitW (pre ns chk : String) (n : Nat) (cases : String) (le li : List (Facts × Out)) (T : Tree)
    (I : List F) (μ : WExpr) (ss : List Seq) : String :=
  let uniq := ss.eraseDups
  let idx (s : Seq) : Nat := uniq.idxOf s
  let lit := "[" ++ String.intercalate ", " (ss.map fun s => s!"q{idx s}") ++ "]"
  let conj := ss.foldr (fun s acc => s!"List.forall_mem_cons.mpr ⟨v{idx s}, {acc}⟩") "fun _ h => absurd h List.not_mem_nil"
  let obl := s!"Obl (fun _ => recOf I μ) id (fun _ => True) (fun _ => True) {n} {cases} T le li"
  pre ++ s!"\nnamespace {ns}\nopen SolidCore.Refinement.Generic Verify.LoopSource.Equiv Verify.LoopSource.Equiv.Inv Verify.Phase3.Infer\n\n" ++
  "/-! Generated by `Verify.Phase3.Infer.emitW` from `loop_infer.py`'s candidates; every fact below is checked by the kernel. -/\n\n" ++
  s!"def le : List (Facts × Out) := {reprStr le}\n\ndef li : List (Facts × Out) := {reprStr li}\n\n" ++
  "/-- The property, as the tree the function must show on every call (part of the statement). -/\n" ++
  s!"def T : Tree := {reprStr T}\n\n" ++
  "/-- The discovered invariant (untrusted until `obl`). -/\n" ++
  s!"def I : List F := {reprStr I}\n\n" ++
  "/-- The discovered measure (untrusted until `obl`). -/\n" ++
  s!"def μ : WExpr := {reprStr μ}\n\n" ++
  String.intercalate "\n" ((uniq.zipIdx).map fun (s, i) => s!"def q{i} : Seq := {reprStr s}\n") ++
  s!"\ndef ss : List Seq := {lit}\n\n" ++
  s!"theorem leaves : {chk} = some (le, li) := resBeq_eq (by decide +kernel)\n\n" ++
  s!"theorem seqs : allSeqsW {n} {cases} T le li I μ = some ss := by decide +kernel\n\n" ++
  String.intercalate "\n" ((uniq.zipIdx).map fun (_, i) =>
    s!"theorem v{i} : Seq.Valid q{i} := by\n  simp only [q{i}, Seq.Valid]\n  wordnormW\n") ++
  s!"\ntheorem valid : ∀ s ∈ ss, s.Valid :=\n  show ∀ s ∈ {lit}, Seq.Valid s from\n  {conj}\n\n" ++
  s!"/-- **The loop's obligations hold** for the discovered invariant and measure. -/\ntheorem obl : {obl} :=\n  obl_of_seqsW seqs valid\n\n" ++
  s!"/-- **The certificate**: the cut-point check of solar's MIR succeeds, and its leaves meet the\nobligations of `I` and `μ` against the property `T`. -/\n" ++
  s!"theorem certified : ∃ le li, {chk} = some (le, li) ∧\n    Obl (fun _ => recOf I μ) id (fun _ => True) (fun _ => True) {n} {cases} T le li :=\n  ⟨le, li, leaves, obl⟩\n\n" ++
  s!"end {ns}\n\n#print axioms {ns}.obl\n#print axioms {ns}.certified\n"

end Verify.Phase3.Infer

namespace Verify.Phase3.Infer.HornOkTransfer
open SolidCore.Refinement.Generic Verify.LoopSource.Equiv

/-- solar's lowered MIR (verbatim from Stage0.lean). -/
def stage0 : SolarTV.MIR.Lowered.Module :=
  { entry := 2,
    functions := [
    -- @ok_transfer
    { params := [],
      blocks := [
      -- bb0
      ⟨[],
        [.effect (some 29) .calldataload [.const 4]],
        .jump 1⟩,
      -- bb1
      ⟨[(5, [(0, .value 29), (3, .value 10)]), (6, [(0, .const 0), (3, .value 14)])],
        [.ne 8 (.value 5) (.const 0)],
        .branch (.value 8) 3 2⟩,
      -- bb2
      ⟨[],
        [.effect none .mstore [.const 0, .value 6]],
        .ret (.const 0) (.const 32)⟩,
      -- bb3
      ⟨[],
        [.pure 10 .sub [.value 5, .const 1],
         .pure 14 .add [.value 6, .const 1]],
        .jump 1⟩] },
    -- @bad_transfer
    { params := [],
      blocks := [
      -- bb0
      ⟨[],
        [.effect (some 29) .calldataload [.const 4]],
        .jump 1⟩,
      -- bb1
      ⟨[(5, [(0, .value 29), (3, .value 10)]), (6, [(0, .const 0), (3, .value 14)])],
        [.ne 8 (.value 5) (.const 0)],
        .branch (.value 8) 3 2⟩,
      -- bb2
      ⟨[],
        [.effect none .mstore [.const 0, .value 6]],
        .ret (.const 0) (.const 32)⟩,
      -- bb3
      ⟨[],
        [.pure 10 .sub [.value 5, .const 1],
         .pure 14 .add [.value 6, .const 1]],
        .jump 1⟩] },
    -- @entry
    { params := [],
      blocks := [
      -- bb0
      ⟨[],
        [.effect (some 0) .callvalue [],
         .effect (some 1) .calldatasize [],
         .pure 3 .lt [.value 1, .const 36],
         .word 4 (.value 3),
         .pure 5 .or [.value 0, .value 4],
         .ne 7 (.value 5) (.const 0)],
        .branch (.value 7) 1 2⟩,
      -- bb1
      ⟨[],
        [],
        .revert (.const 0) (.const 0)⟩,
      -- bb2
      ⟨[],
        [.effect (some 9) .calldataload [.const 0],
         .pure 11 .shr [.const 224, .value 9]],
        .switch (.value 11) 1 [(.const 0x18a4b471, 3), (.const 0xfd0011a5, 4)]⟩,
      -- bb3
      ⟨[],
        [],
        .tailCall 1 []⟩,
      -- bb4
      ⟨[],
        [],
        .tailCall 0 []⟩] }] }

/-- The cut-point certificate (from Cut.lean; checked by Cut.check). -/
def cut : Cut :=
  { fn := 0, head := 1,
    ids := [
      (0, (.fixed (.lit 0))),
      (1, (.fixed (.lit 0))),
      (3, (.fixed (.lit 0))),
      (4, (.fixed (.lit 0))),
      (5, (.hw 0)),
      (6, (.hw 1)),
      (7, (.fixed (.lit 0))),
      (8, (.hw 2)),
      (9, (.fixed (.lit 0))),
      (10, (.hw 3)),
      (11, (.fixed (.lit 0))),
      (14, (.hw 4)),
      (29, (.fixed (.arg 0)))],
    mem := [], writes := [], nhw := 5,
    cases := [[]],
    fuel := 60 }

end Verify.Phase3.Infer.HornOkTransfer

namespace Verify.Phase3.Infer.HornOkTransfer
open SolidCore.Refinement.Generic Verify.LoopSource.Equiv Verify.LoopSource.Equiv.Inv Verify.Phase3.Infer

/-! Generated by tools/certify/loop_infer.py: elaborating it writes the obligation module. -/

def T : Tree := (Tree.halt true [(OByte.byteOf (WExpr.arg 0) 0), (OByte.byteOf (WExpr.arg 0) 1), (OByte.byteOf (WExpr.arg 0) 2), (OByte.byteOf (WExpr.arg 0) 3), (OByte.byteOf (WExpr.arg 0) 4), (OByte.byteOf (WExpr.arg 0) 5), (OByte.byteOf (WExpr.arg 0) 6), (OByte.byteOf (WExpr.arg 0) 7), (OByte.byteOf (WExpr.arg 0) 8), (OByte.byteOf (WExpr.arg 0) 9), (OByte.byteOf (WExpr.arg 0) 10), (OByte.byteOf (WExpr.arg 0) 11), (OByte.byteOf (WExpr.arg 0) 12), (OByte.byteOf (WExpr.arg 0) 13), (OByte.byteOf (WExpr.arg 0) 14), (OByte.byteOf (WExpr.arg 0) 15), (OByte.byteOf (WExpr.arg 0) 16), (OByte.byteOf (WExpr.arg 0) 17), (OByte.byteOf (WExpr.arg 0) 18), (OByte.byteOf (WExpr.arg 0) 19), (OByte.byteOf (WExpr.arg 0) 20), (OByte.byteOf (WExpr.arg 0) 21), (OByte.byteOf (WExpr.arg 0) 22), (OByte.byteOf (WExpr.arg 0) 23), (OByte.byteOf (WExpr.arg 0) 24), (OByte.byteOf (WExpr.arg 0) 25), (OByte.byteOf (WExpr.arg 0) 26), (OByte.byteOf (WExpr.arg 0) 27), (OByte.byteOf (WExpr.arg 0) 28), (OByte.byteOf (WExpr.arg 0) 29), (OByte.byteOf (WExpr.arg 0) 30), (OByte.byteOf (WExpr.arg 0) 31)] [] [])

def I : List F := [(F.le (WExpr.arg 2) (WExpr.arg 0)), (F.lin (WExpr.arg 0) (WExpr.arg 1) (WExpr.arg 2) (WExpr.lit 0))]

def μ : WExpr := (WExpr.arg 1)

#eval show IO Unit from do
  match cut.check .off stage0 4244640165 1 with
  | none => throw (IO.userError "cut.check is none")
  | some (le, li) =>
    match allSeqsW 1 cut.cases T le li I μ with
    | none => throw (IO.userError "allSeqsW is none")
    | some ss =>
      -- Runs only with the obligation module's prelude at `out/prelude.lean` (from the repository
      -- root), so a library build writes nothing.
      unless (← System.FilePath.pathExists "out/prelude.lean") do return
      let pre ← IO.FS.readFile "out/prelude.lean"
      IO.FS.writeFile "Verify/Phase3/Infer/Horn/Obl.lean" (emitW pre "Verify.Phase3.Infer.HornOkTransfer" "cut.check .off stage0 4244640165 1" 1 "cut.cases" le li T I μ ss)
      IO.println s!"wrote {ss.length} sequents ({ss.eraseDups.length} unique)"

end Verify.Phase3.Infer.HornOkTransfer

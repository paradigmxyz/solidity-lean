import Verify.LoopSource.Equiv.Obl

/-!
# Loop obligations as sequents over words, closed in the kernel

`Task.seqs` turns each task of a cut-point check's leaves into sequents: a list of formulas over a
valuation's words (`F`) and a goal formula, or none when the hypotheses must be contradictory.
`obl_of_seqs` proves that when every sequent is valid (`Seq.Valid`), the leaves meet `Obl` for
the loop record of the invariant `I` and the measure `μ` (`recOf`).

A sequent is a statement about words mod `2 ^ 256`: addition, subtraction and comparisons of
words, as `WExpr.eval` defines them. `wordnorm` closes one: it unfolds the words to natural
number arithmetic with `% 2 ^ 256` (the word normalizer), splits the comparisons' `if`s and calls
`omega`, which decides linear arithmetic with `%` by numerals. Every proof it makes is checked by
the kernel; nothing here is trusted beyond the kernel and the three standard axioms.
-/

namespace Verify.LoopSource.Equiv.Inv
open SolarTV SolidCore.Refinement.Generic Verify.LoopSource.Equiv Verify.LoopSource.Interface

/-! ## Sequents -/

/-- Hypotheses and a goal; `none`: the hypotheses have no common valuation. -/
abbrev Seq := List F × Option F

/-- **A sequent is valid**: every valuation of its hypotheses meets its goal. -/
def Seq.Valid (s : Seq) : Prop :=
  ∀ σ : Val, (∀ h ∈ s.1, h.Holds σ) → match s.2 with
    | some g => g.Holds σ
    | none => False

/-- The hypotheses of a goal: the facts `K`, and the formulas of `S` within one round of the
goal's and the facts' words. -/
def hyp (S K : List F) (g : Option F) : List F := slice 1 S (g.toList ++ K) ++ K

/-- The sequents of an end against a tree: for every pair of paths, each goal of the pair under
both paths' facts, or a contradiction when the pair's ends are not comparable. -/
def endSeqs (S K : List F) (T' T : Tree) : List Seq :=
  (paths T').flatMap fun p' => (paths T).flatMap fun p =>
    let k := K ++ factsF p'.1 ++ factsF p.1
    match haltGoals p'.2 p.2 with
    | some gs => gs.map fun g => (hyp S k (some g), some g)
    | none => [(hyp S k none, none)]

/-- **The sequents of a task.** -/
def Task.seqs (n : Nat) (cases : List Facts) (T : Tree) (I : List F) (μ : WExpr) : Task → Option (List Seq)
  | .below => if treeBelow n T = true then some [] else none
  | .inv f entry p => match p.2 with
    | .back hs =>
      let g := f.sub n hs
      some [(hyp (if entry then [] else I) (factsF p.1) (some g), some g)]
    | .exit _ => some []
  | .entryEnd p => match p.2 with
    | .exit T' => some (endSeqs [] (factsF p.1) T' T)
    | .back _ => some []
  | .iterLeaf p => match p.2 with
    | .exit T' => some (endSeqs I (factsF p.1) T' T)
    | .back hs =>
      let g := F.lt (Inv.sub n hs μ) μ
      some [(hyp I (factsF p.1) (some g), some g)]
  | .cover => some [(hyp I (cases.map noCase) none, none)]

/-- **All sequents of the leaves** `le` (entry run) and `li` (iteration runs). -/
def allSeqs (n : Nat) (cases : List Facts) (T : Tree) (le li : List (Facts × Out)) (I : List F)
    (μ : WExpr) : Option (List Seq) :=
  ((tasks le li I).mapM (Task.seqs n cases T I μ)).map List.flatten

/-! ## Soundness -/

theorem hyp_holds {S K : List F} {g : Option F} {σ : Val} (hS : ∀ f ∈ S, f.Holds σ)
    (hK : ∀ f ∈ K, f.Holds σ) : ∀ f ∈ hyp S K g, f.Holds σ :=
  slice_holds hS hK

/-- A valid sequent's goal holds where `S` and `K` do. -/
theorem goal_of_valid {S K : List F} {g : F} (h : Seq.Valid (hyp S K (some g), some g)) {σ : Val}
    (hS : ∀ f ∈ S, f.Holds σ) (hK : ∀ f ∈ K, f.Holds σ) : g.Holds σ :=
  h σ (hyp_holds hS hK)

/-- A valid contradiction has no valuation where `S` and `K` hold. -/
theorem false_of_valid {S K : List F} (h : Seq.Valid (hyp S K none, none)) {σ : Val}
    (hS : ∀ f ∈ S, f.Holds σ) (hK : ∀ f ∈ K, f.Holds σ) : False :=
  h σ (hyp_holds hS hK)

/-- **An end whose sequents are valid shows the tree's result.** -/
theorem endSeqs_sound {S K : List F} {T' T : Tree} (h : ∀ s ∈ endSeqs S K T' T, s.Valid) {ρ : Val}
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
  cases hg : haltGoals p'.2 p.2 with
  | none => exact (false_of_valid (hv _ (by rw [hg]; exact List.mem_singleton_self _)) hS hk).elim
  | some gs =>
    exact halt_obs hρ hg fun g hgm =>
      goal_of_valid (hv _ (by rw [hg]; exact List.mem_map_of_mem hgm)) hS hk

theorem seqs_mem {n : Nat} {cases : List Facts} {T : Tree} {le li : List (Facts × Out)} {I : List F}
    {μ : WExpr} {ss : List Seq} (h : allSeqs n cases T le li I μ = some ss) {t : Task}
    (ht : t ∈ tasks le li I) : ∃ ts, t.seqs n cases T I μ = some ts ∧ ∀ s ∈ ts, s ∈ ss := by
  unfold allSeqs at h
  cases hm : (tasks le li I).mapM (Task.seqs n cases T I μ) with
  | none => simp [hm] at h
  | some tss =>
    simp only [hm, Option.map_some, Option.some.injEq] at h
    subst h
    obtain ⟨ts, hts, hteq⟩ := mapM_mem hm t ht
    exact ⟨ts, hteq, fun s hs => List.mem_flatten.mpr ⟨ts, hts, hs⟩⟩

/-- **A task whose sequents are valid holds.** -/
theorem Task.seqs_sound {n : Nat} {cases : List Facts} {T : Tree} {I : List F} {μ : WExpr} {t : Task}
    {ts : List Seq} (h : t.seqs n cases T I μ = some ts) (hv : ∀ s ∈ ts, s.Valid) :
    t.Sound n cases T I μ := by
  cases t with
  | below => simp only [Task.seqs] at h; split at h <;> simp_all [Task.Sound]
  | cover =>
    simp only [Task.seqs, Option.some.injEq] at h; subst h
    exact fun _ hS hK => (false_of_valid (hv _ (List.mem_singleton_self _)) hS hK).elim
  | inv _ _ p | entryEnd p | iterLeaf p =>
    obtain ⟨K, _ | _⟩ := p <;> simp only [Task.seqs, Task.Sound, Option.some.injEq] at h ⊢ <;>
      subst h <;>
      first
      | exact fun _ hS hK => goal_of_valid (hv _ (List.mem_singleton_self _)) hS hK
      | exact fun _ hρ hS hK => endSeqs_sound hv hρ hS hK

/-- **Valid sequents give the obligations.** -/
theorem obl_of_seqs {n : Nat} {cases : List Facts} {T : Tree} {le li : List (Facts × Out)}
    {I : List F} {μ : WExpr} {ss : List Seq} (h : allSeqs n cases T le li I μ = some ss)
    (hv : ∀ s ∈ ss, s.Valid) :
    Obl (fun _ => recOf I μ) id (fun _ => True) (fun _ => True) n cases T le li :=
  obl_of_sound fun _ ht => by
    obtain ⟨_, h1, h2⟩ := seqs_mem h ht
    exact Task.seqs_sound h1 fun s hs => hv s (h2 s hs)

/-! ## Deciding a formula at one valuation (for negatives) -/

instance F.decHolds (σ : Val) : ∀ f : F, Decidable (f.Holds σ)
  | .fact e b => inferInstanceAs (Decidable (_ ↔ _))
  | .le a b => inferInstanceAs (Decidable (_ ≤ _))
  | .lt a b => inferInstanceAs (Decidable (_ < _))
  | .eq a b => inferInstanceAs (Decidable (_ = _))
  | .lin a b c d => inferInstanceAs (Decidable (_ = _))
  | .or f g => @instDecidableOr _ _ (F.decHolds σ f) (F.decHolds σ g)
  | .not f => @instDecidableNot _ (F.decHolds σ f)

/-- **A sequent with a counterexample is not valid.** -/
theorem not_valid_of {s : Seq} (σ : Val) (hh : ∀ h ∈ s.1, h.Holds σ)
    (hg : match s.2 with | some g => ¬ g.Holds σ | none => True) : ¬ s.Valid := fun hv => by
  have := hv σ hh
  revert hg this
  cases s.2 <;> simp

/-- Sequent \`i\` of \`ss\` has the counterexample \`σ\`: its hypotheses hold at \`σ\` and its goal does
not. \`false\` when there are no sequents. -/
def rejects (σ : Val) (i : Nat) : Option (List Seq) → Bool
  | some ss => match ss[i]? with
    | some s => s.1.all (fun h => decide (h.Holds σ)) &&
        match s.2 with | some g => !decide (g.Holds σ) | none => true
    | none => false
  | none => false

/-- **A counterexample to one sequent rejects them all**: they are not all valid. -/
theorem rejects_sound {σ : Val} {i : Nat} {ss : List Seq} (h : rejects σ i (some ss) = true) :
    ¬ ∀ s ∈ ss, s.Valid := fun hall => by
  simp only [rejects] at h
  split at h
  · rename_i s hs
    simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
    refine not_valid_of σ h.1 ?_ (hall s (List.mem_of_getElem? hs))
    revert h; cases s.2 <;> simp
  · simp at h

end Verify.LoopSource.Equiv.Inv

namespace Verify.LoopSource.Equiv.Inv

open SolidCore.Refinement.Generic in
theorem one_mod_W : (1 : Nat) % 115792089237316195423570985008687907853269984665640564039457584007913129639936 = 1 := by
  decide

/-- A comparison word is 1 or 0 by its comparison, with no reduction mod `2 ^ 256` left. -/
theorem ev_iszero (σ : SolidCore.Refinement.Generic.Val) (a : SolidCore.Refinement.Generic.WExpr) :
    (SolidCore.Refinement.Generic.WExpr.un .iszero a).eval σ = if a.eval σ = 0 then 1 else 0 := by
  simp only [SolidCore.Refinement.Generic.WExpr.eval, SolidCore.Refinement.Generic.UnOp.eval]
  split <;> rfl

theorem ev_eq (σ : SolidCore.Refinement.Generic.Val) (a b : SolidCore.Refinement.Generic.WExpr) :
    (SolidCore.Refinement.Generic.WExpr.bin .eq a b).eval σ = if a.eval σ = b.eval σ then 1 else 0 := by
  simp only [SolidCore.Refinement.Generic.WExpr.eval, SolidCore.Refinement.Generic.BinOp.eval]
  split <;> rfl

theorem ev_lt (σ : SolidCore.Refinement.Generic.Val) (a b : SolidCore.Refinement.Generic.WExpr) :
    (SolidCore.Refinement.Generic.WExpr.bin .lt a b).eval σ = if a.eval σ < b.eval σ then 1 else 0 := by
  simp only [SolidCore.Refinement.Generic.WExpr.eval, SolidCore.Refinement.Generic.BinOp.eval]
  split <;> rfl

theorem ev_gt (σ : SolidCore.Refinement.Generic.Val) (a b : SolidCore.Refinement.Generic.WExpr) :
    (SolidCore.Refinement.Generic.WExpr.bin .gt a b).eval σ = if b.eval σ < a.eval σ then 1 else 0 := by
  simp only [SolidCore.Refinement.Generic.WExpr.eval, SolidCore.Refinement.Generic.BinOp.eval]
  split <;> first | rfl | simp_all | omega

theorem ite01_eq_zero (p : Prop) [Decidable p] : ((if p then 1 else 0 : Nat) = 0) = ¬ p := by
  apply propext; split <;> simp_all

theorem ite01_ne_zero (p : Prop) [Decidable p] : (¬ (if p then 1 else 0 : Nat) = 0) = p := by
  apply propext; split <;> simp_all

end Verify.LoopSource.Equiv.Inv

/-- **The word normalizer**: comparison words to `if`s on their operands (`ev_iszero`, `ev_eq`,
`ev_lt`, `ev_gt`) and those, compared with 0, to propositions; then the remaining words to natural
number arithmetic mod `2 ^ 256`, `if`s split, and `omega`. -/
macro "wordnorm" : tactic => `(tactic| (
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
  all_goals (first | trivial | omega | (split_ifs at h ⊢ <;> first | trivial | omega))))

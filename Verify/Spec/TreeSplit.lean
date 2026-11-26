import Verify.Spec.TreeMapNested

/-!
# Tree specs by cases on a tree's tests

`TreeMeetsFixedOn P` is `TreeMeetsFixed` on the evaluations that meet `P`. `TreeMeetsFixedOn.ite`
splits a tree's test into its two branches, each with the test's outcome added to `P`, so a spec of a
tree with many paths is proved as several smaller theorems, one per branch, each its own kernel
check. `tree_meets_map2_on` is `tree_meets_map2` for one branch: it reads the branch's tests from
`P` beside the other hypotheses. Nothing here is trusted: a case it cannot close is an error.
-/

namespace SolidCore.Spec

open SolidCore.Refinement SolidCore.Refinement.Generic

/-- `TreeMeetsFixed` on the evaluations that meet `P`. -/
def TreeMeetsFixedOn (P : Val → Prop) (b : Bundle) (fs : FnSpec) (ctx : Ctx) (n : Nat) (T : Tree) :
    Prop :=
  ∀ (args : List Nat) (s : Storage) (iargs : List Int) (pre : State),
    args.length = n → (∀ a ∈ args, a < 2 ^ 256) → (∀ k, s k < 2 ^ 256) →
    decodeWords fs.params args = some iargs → pre.storage = s → pre.time ≤ ctx.timestamp →
    b.satAll fs.requires (mkEnv ctx iargs [] pre pre) →
    b.satAll b.spec.invariants (mkEnv ctx iargs [] pre pre) →
    P ⟨args, s, solHash, SolidCore.Refinement.Generic.callerWord⟩ →
    Post b fs ctx pre pre.ghost (T.eval ⟨args, s, solHash, SolidCore.Refinement.Generic.callerWord⟩).obs iargs

theorem TreeMeetsFixedOn.fixed {b : Bundle} {fs : FnSpec} {ctx : Ctx} {n : Nat} {T : Tree}
    (h : TreeMeetsFixedOn (fun _ => True) b fs ctx n T) : TreeMeetsFixed b fs ctx n T :=
  fun args s iargs pre hl hargs hs hdec hst ht hreq hinv =>
    h args s iargs pre hl hargs hs hdec hst ht hreq hinv trivial

/-- **A test splits a tree spec into its branches.** -/
theorem TreeMeetsFixedOn.ite {P : Val → Prop} {b : Bundle} {fs : FnSpec} {ctx : Ctx} {n : Nat}
    {c : WExpr} {t e : Tree}
    (h1 : TreeMeetsFixedOn (fun ρ => P ρ ∧ c.eval ρ ≠ 0) b fs ctx n t)
    (h2 : TreeMeetsFixedOn (fun ρ => P ρ ∧ c.eval ρ = 0) b fs ctx n e) :
    TreeMeetsFixedOn P b fs ctx n (.ite c t e) := by
  intro args s iargs pre hl hargs hs hdec hst ht hreq hinv hP
  simp only [Tree.eval]
  split
  · exact h2 args s iargs pre hl hargs hs hdec hst ht hreq hinv ⟨hP, by assumption⟩
  · exact h1 args s iargs pre hl hargs hs hdec hst ht hreq hinv ⟨hP, by assumption⟩

/-- info: 'SolidCore.Spec.TreeMeetsFixedOn.ite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TreeMeetsFixedOn.ite

open Lean Meta Elab Tactic in
/-- `inst_forall_lits`: `inst_foralls` at the numerals of the context. It instantiates every hypothesis
`∀ x : Nat, x < b → P x` (a quantified clause of an invariant, such as `allowance[address(0)][s] == 0`
for every address `s`) at every numeral that is an argument of a two-argument application of a local
function (a slot hash `H k s`, such as the one of the caller's address), its bound discharged by
`omega`. Each instance is a consequence of a hypothesis; one whose bound `omega` does not show is
left out. -/
elab "inst_forall_lits" : tactic => do
  let lits ← IO.mkRef (#[] : Array Nat)
  let fs ← withMainContext do
    let mut fs := #[]
    let mut tys := #[← instantiateMVars (← getMainTarget)]
    for d in (← getLCtx) do
      if d.isImplementationDetail then continue
      let t ← instantiateMVars d.type
      tys := tys.push t
      if (← isBoundedForall t) then
        fs := fs.push d.fvarId
    for t in tys do
      t.forEach fun e => do
        if let .app (.app (.fvar _) a) b := e then
          for x in [a, b] do
            if let some n := x.nat? then
              lits.modify fun acc => if acc.contains n then acc else acc.push n
    pure fs
  instClauses fs (← lits.get) fun n => `(($(Syntax.mkNumLit (toString n)) : Nat))

/-- `tree_meets_map2` for one branch of a split tree (`TreeMeetsFixedOn`): `P`'s tests join the
hypotheses. -/
macro "tree_meets_map2_on" "[" ds:Lean.Parser.Tactic.simpLemma,* "]" hsep:term:max : tactic => do
  seqTactics (#[← `(tactic| intro args s iargs pre hl hargs hs hdec hst ht hreq hinv hP),
    ← `(tactic| simp only [Nat.reducePow] at hs),
    ← chainTactics ((← decodeArgs ds) ++ (← nestedLinks hsep) ++ #[
      ← `(tactic| generalize solHash = H at hinj hge hgn hln hnn hlt hkec hP ⊢),
      ← `(tactic| simp only [true_and, WExpr.eval, BinOp.eval, UnOp.eval, Generic.wordSize, List.getD_cons_zero,
      List.getD_cons_succ, Nat.reducePow] at hP),
      ← `(tactic| refine ⟨fun hsucc => ?_, fun hne => ?_⟩)])] ++
    (← meetsSteps ds true true (← nestedInv)) ++
    (← nestedSteps true #[← allGoals true (← `(tactic| inst_forall_lits))]))

end SolidCore.Spec

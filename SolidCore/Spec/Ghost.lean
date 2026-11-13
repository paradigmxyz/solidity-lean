/-!
# Ghost erasure

solar-verify proves a contract together with its ghost code: `@custom:ghost x = e` updates,
`@custom:assert` and `@custom:assume`, and the lemmas `@custom:use` applies. The bytecode runs
without any of it: NatSpec is a comment to the compiler. A proof with ghost code is a proof of the
deployed program only if erasing the ghost code leaves every real execution as it was.
solar-verify checks the discipline of Filliâtre, Gondelman and Paskevich, "The Spirit of Ghost
Code" (CAV 2014), before it verifies anything (crates/verify/src/ghost.rs, README "Ghost code"):

1. ghost code writes only ghost variables (it may read real ones);
2. ghost code never reverts, and no ghost condition decides a real write;
3. ghost code terminates;
4. real code never reads a ghost variable.

This module proves that the discipline suffices, for a core statement language with that shape:
assignments, `require`, sequencing, conditionals and loops over real and ghost variables of one
store, ghost updates, `assert` and `assume`. `WF` is rules 1, 2 and 4 as a boolean check on the
syntax, as ghost.rs grades variables; rule 3 is `GhostTotal`, that every piece of ghost code
finishes from every state (solar-verify proves it through `@custom:decreases` variants and its
syntactic rules; `ghostTotal_of_straight` proves it here for ghost code without loops or assumes).

* `sound`: every instrumented execution that does not fail an assertion is, on the real
  variables, an execution of the erased program.
* `complete`: every execution of the erased program is, on the real variables, an instrumented
  execution from any ghost state, or one that fails an assertion.
* `spec_of_erased`: a property proved of every instrumented execution, with no failing
  assertion, holds of every execution of the erased program, with some ghost state.

What this module leaves to solar-verify's encoding (crates/verify/src/vc.rs, a named hypothesis of
the final theorem, `SolidCore.Spec.TrustedBase`): that its model of a Solidity function is the
instrumented program of this language whose erasure is the function SolidCore runs.
-/

namespace SolidCore.Spec.Ghost

/-- One store of real and ghost variables. -/
abbrev Store := String → Int

/-- Expressions over the store. -/
inductive Exp where
  | lit (v : Int)
  | var (x : String)
  | un (f : Int → Int) (a : Exp)
  | bin (f : Int → Int → Int) (a b : Exp)

/-- An expression's value. -/
def Exp.eval (σ : Store) : Exp → Int
  | .lit v => v
  | .var x => σ x
  | .un f a => f (a.eval σ)
  | .bin f a b => f (a.eval σ) (b.eval σ)

/-- The variables an expression reads. -/
def Exp.vars : Exp → List String
  | .lit _ => []
  | .var x => [x]
  | .un _ a => a.vars
  | .bin _ a b => a.vars ++ b.vars

/-- Statements: real code (`assign`, `require`), ghost code (`ghost`, `assert`, `assume`), and the
control flow both share. -/
inductive Stmt where
  | skip
  | assign (x : String) (e : Exp)
  | require (e : Exp)
  | seq (s t : Stmt)
  | ite (c : Exp) (s t : Stmt)
  | loop (c : Exp) (body : Stmt)
  /-- `@custom:ghost x = e`. -/
  | ghost (x : String) (e : Exp)
  /-- `@custom:assert e`: proved, so a failure is a failed proof. -/
  | assert (e : Exp)
  /-- `@custom:assume e` (and a lemma's ensures, or a trusted contract): an execution where it
  does not hold does not exist. -/
  | assume (e : Exp)

/-- What a statement finishes with: normally, by reverting (which undoes everything, so no
store), or by failing an assertion. -/
inductive Out where
  | ok (σ : Store)
  | rev
  | fail

/-- Update a variable. -/
def Store.set (σ : Store) (x : String) (v : Int) : Store := fun y => if y = x then v else σ y

/-- Big-step semantics. A loop that does not terminate, and an `assume` that does not hold, have
no execution. -/
inductive Exec : Stmt → Store → Out → Prop where
  | skip : Exec .skip σ (.ok σ)
  | assign : Exec (.assign x e) σ (.ok (σ.set x (e.eval σ)))
  | requireOk : e.eval σ ≠ 0 → Exec (.require e) σ (.ok σ)
  | requireRev : e.eval σ = 0 → Exec (.require e) σ .rev
  | seqOk : Exec s σ (.ok σ') → Exec t σ' o → Exec (.seq s t) σ o
  | seqRev : Exec s σ .rev → Exec (.seq s t) σ .rev
  | seqFail : Exec s σ .fail → Exec (.seq s t) σ .fail
  | iteT : c.eval σ ≠ 0 → Exec s σ o → Exec (.ite c s t) σ o
  | iteF : c.eval σ = 0 → Exec t σ o → Exec (.ite c s t) σ o
  | loopDone : c.eval σ = 0 → Exec (.loop c b) σ (.ok σ)
  | loopOk : c.eval σ ≠ 0 → Exec b σ (.ok σ') → Exec (.loop c b) σ' o → Exec (.loop c b) σ o
  | loopRev : c.eval σ ≠ 0 → Exec b σ .rev → Exec (.loop c b) σ .rev
  | loopFail : c.eval σ ≠ 0 → Exec b σ .fail → Exec (.loop c b) σ .fail
  | ghost : Exec (.ghost x e) σ (.ok (σ.set x (e.eval σ)))
  | assertOk : e.eval σ ≠ 0 → Exec (.assert e) σ (.ok σ)
  | assertFail : e.eval σ = 0 → Exec (.assert e) σ .fail
  | assume : e.eval σ ≠ 0 → Exec (.assume e) σ (.ok σ)

section
variable (isGhost : String → Bool)

/-- The expression reads no ghost variable. -/
def Exp.real (e : Exp) : Bool := e.vars.all fun x => !isGhost x

/-- Ghost code: statements made only of ghost updates of ghost variables, assertions and
assumptions, under any control flow. -/
def Stmt.ghostCode : Stmt → Bool
  | .skip | .assert _ | .assume _ => true
  | .ghost x _ => isGhost x
  | .assign _ _ | .require _ => false
  | .seq s t | .ite _ s t => s.ghostCode && t.ghostCode
  | .loop _ b => b.ghostCode

/-- Erase the ghost code. -/
def Stmt.erase : Stmt → Stmt
  | s@(.seq a b) => if s.ghostCode isGhost then .skip else .seq (a.erase) (b.erase)
  | s@(.ite c a b) => if s.ghostCode isGhost then .skip else .ite c (a.erase) (b.erase)
  | s@(.loop c b) => if s.ghostCode isGhost then .skip else .loop c (b.erase)
  | s => if s.ghostCode isGhost then .skip else s

/-- The discipline, as a check on the syntax: real assignments write real variables from real
values (rules 1 and 4), `require` and every real condition read only real variables (rules 2
and 4), and ghost updates write ghost variables (rule 1). Ghost code has no `require` and no real
assignment by `ghostCode` (rule 2). -/
def Stmt.WF : Stmt → Bool
  | .skip | .assert _ | .assume _ => true
  | .ghost x _ => isGhost x
  | .assign x e => !isGhost x && e.real isGhost
  | .require e => e.real isGhost
  | .seq s t => s.WF && t.WF
  | s@(.ite c a b) => s.ghostCode isGhost || (c.real isGhost && a.WF && b.WF)
  | s@(.loop c b) => s.ghostCode isGhost || (c.real isGhost && b.WF)

/-- Two stores agree on the real variables. -/
def Agree (σ τ : Store) : Prop := ∀ x, isGhost x = false → σ x = τ x

/-- Two outcomes agree on the real variables. -/
def OutAgree : Out → Out → Prop
  | .ok σ, .ok τ => Agree isGhost σ τ
  | .rev, .rev => True
  | .fail, .fail => True
  | _, _ => False

/-- Rule 3: every piece of ghost code finishes from every state (perhaps failing an assertion). -/
def GhostTotal : Stmt → Prop
  | s@(.seq a b) | s@(.ite _ a b) =>
    (s.ghostCode isGhost = true → ∀ σ, ∃ o, Exec s σ o) ∧ GhostTotal a ∧ GhostTotal b
  | s@(.loop _ b) => (s.ghostCode isGhost = true → ∀ σ, ∃ o, Exec s σ o) ∧ GhostTotal b
  | s => s.ghostCode isGhost = true → ∀ σ, ∃ o, Exec s σ o
end

/-! ## Lemmas -/

variable {isGhost : String → Bool}

theorem Agree.refl (σ : Store) : Agree isGhost σ σ := fun _ _ => rfl

theorem Agree.symm {σ τ : Store} (h : Agree isGhost σ τ) : Agree isGhost τ σ :=
  fun x hx => (h x hx).symm

theorem Agree.trans {σ τ υ : Store} (h : Agree isGhost σ τ) (h' : Agree isGhost τ υ) :
    Agree isGhost σ υ := fun x hx => (h x hx).trans (h' x hx)

theorem Agree.set {σ τ : Store} (h : Agree isGhost σ τ) (x : String) (v : Int) :
    Agree isGhost (σ.set x v) (τ.set x v) := by
  intro y hy
  simp only [Store.set]
  split
  · rfl
  · exact h y hy

theorem Agree.set_ghost {σ : Store} {x : String} (hx : isGhost x = true) (v : Int) :
    Agree isGhost (σ.set x v) σ := by
  intro y hy
  simp only [Store.set]
  split
  · subst_vars; simp_all
  · rfl

theorem Exp.eval_agree {σ τ : Store} (h : Agree isGhost σ τ) :
    ∀ e : Exp, e.real isGhost = true → e.eval σ = e.eval τ
  | .lit _, _ => rfl
  | .var x, he => by
    simp [Exp.real, Exp.vars] at he
    exact h x he
  | .un f a, he => by
    simp only [Exp.real, Exp.vars] at he
    simp only [Exp.eval, Exp.eval_agree h a he]
  | .bin f a b, he => by
    simp only [Exp.real, Exp.vars, List.all_append, Bool.and_eq_true] at he
    simp only [Exp.eval, Exp.eval_agree h a he.1, Exp.eval_agree h b he.2]

/-- Ghost code changes no real variable and never reverts. -/
theorem ghostCode_exec {s : Stmt} {σ : Store} {o : Out} (hx : Exec s σ o)
    (hg : s.ghostCode isGhost = true) :
    o = .fail ∨ ∃ σ', o = .ok σ' ∧ Agree isGhost σ' σ := by
  induction hx with
  | skip => exact .inr ⟨_, rfl, Agree.refl _⟩
  | assign => simp [Stmt.ghostCode] at hg
  | requireOk => simp [Stmt.ghostCode] at hg
  | requireRev => simp [Stmt.ghostCode] at hg
  | seqOk _ _ ih1 ih2 =>
    simp only [Stmt.ghostCode, Bool.and_eq_true] at hg
    rcases ih1 hg.1 with h | ⟨σ1, h1, a1⟩
    · cases h
    · cases h1
      rcases ih2 hg.2 with h | ⟨σ2, h2, a2⟩
      · exact .inl h
      · exact .inr ⟨σ2, h2, a2.trans a1⟩
  | seqRev _ ih =>
    simp only [Stmt.ghostCode, Bool.and_eq_true] at hg
    rcases ih hg.1 with h | ⟨_, h, _⟩ <;> cases h
  | seqFail => exact .inl rfl
  | iteT _ _ ih =>
    simp only [Stmt.ghostCode, Bool.and_eq_true] at hg
    exact ih hg.1
  | iteF _ _ ih =>
    simp only [Stmt.ghostCode, Bool.and_eq_true] at hg
    exact ih hg.2
  | loopDone => exact .inr ⟨_, rfl, Agree.refl _⟩
  | loopOk _ _ _ ih1 ih2 =>
    rcases ih1 hg with h | ⟨σ1, h1, a1⟩
    · cases h
    · cases h1
      rcases ih2 hg with h | ⟨σ2, h2, a2⟩
      · exact .inl h
      · exact .inr ⟨σ2, h2, a2.trans a1⟩
  | loopRev _ _ ih =>
    rcases ih hg with h | ⟨_, h, _⟩ <;> cases h
  | loopFail => exact .inl rfl
  | ghost => exact .inr ⟨_, rfl, Agree.set_ghost (by simpa [Stmt.ghostCode] using hg) _⟩
  | assertOk => exact .inr ⟨_, rfl, Agree.refl _⟩
  | assertFail => exact .inl rfl
  | assume => exact .inr ⟨_, rfl, Agree.refl _⟩

theorem erase_of_ghostCode {s : Stmt} (hg : s.ghostCode isGhost = true) :
    s.erase isGhost = .skip := by
  cases s <;> simp_all [Stmt.erase]

theorem erase_of_not_ghostCode {s : Stmt} (hg : s.ghostCode isGhost = false) :
    s.erase isGhost = match s with
      | .seq a b => .seq (a.erase isGhost) (b.erase isGhost)
      | .ite c a b => .ite c (a.erase isGhost) (b.erase isGhost)
      | .loop c b => .loop c (b.erase isGhost)
      | s => s := by
  cases s <;> simp_all [Stmt.erase]

/-! ## Soundness: instrumented executions are executions of the erased program -/

/-- **Soundness of erasure.** An instrumented execution of a well-formed program that does not
fail an assertion is, from any store agreeing on the real variables, an execution of the erased
program agreeing on the real variables. -/
theorem sound {s : Stmt} {σ : Store} {o : Out} (hx : Exec s σ o) (hwf : s.WF isGhost = true)
    (hnf : o ≠ .fail) : ∀ τ, Agree isGhost σ τ →
      ∃ o', Exec (s.erase isGhost) τ o' ∧ OutAgree isGhost o o' := by
  induction hx with
  | skip => intro τ h; exact ⟨.ok τ, by simp [Stmt.erase, Stmt.ghostCode]; exact .skip, h⟩
  | @assign x e σ =>
    intro τ h
    simp only [Stmt.WF, Bool.and_eq_true, Bool.not_eq_true'] at hwf
    have he : (Stmt.assign x e).erase isGhost = .assign x e := by simp [Stmt.erase, Stmt.ghostCode]
    rw [he]
    refine ⟨_, .assign, ?_⟩
    show Agree isGhost _ _
    rw [Exp.eval_agree h e hwf.2]
    exact h.set x _
  | @requireOk e σ hc =>
    intro τ h
    simp only [Stmt.WF] at hwf
    have he : (Stmt.require e).erase isGhost = .require e := by simp [Stmt.erase, Stmt.ghostCode]
    rw [he]
    exact ⟨.ok τ, .requireOk (by rwa [← Exp.eval_agree h e hwf]), h⟩
  | @requireRev e σ hc =>
    intro τ h
    simp only [Stmt.WF] at hwf
    have he : (Stmt.require e).erase isGhost = .require e := by simp [Stmt.erase, Stmt.ghostCode]
    rw [he]
    exact ⟨_, .requireRev (by rwa [← Exp.eval_agree h e hwf]), trivial⟩
  | @seqOk a σ σ1 b o h1 h2 ih1 ih2 =>
    intro τ h
    simp only [Stmt.WF, Bool.and_eq_true] at hwf
    cases hg : (Stmt.seq a b).ghostCode isGhost
    · rw [erase_of_not_ghostCode hg]
      obtain ⟨o1, e1, a1⟩ := ih1 hwf.1 (by simp) τ h
      cases o1 with
      | ok τ1 =>
        obtain ⟨o2, e2, a2⟩ := ih2 hwf.2 hnf τ1 a1
        exact ⟨o2, .seqOk e1 e2, a2⟩
      | rev => exact absurd a1 (by simp [OutAgree])
      | fail => exact absurd a1 (by simp [OutAgree])
    · rw [erase_of_ghostCode hg]
      rcases ghostCode_exec (.seqOk h1 h2) hg with hf | ⟨σ', ho, ha⟩
      · exact absurd hf hnf
      · subst ho; exact ⟨.ok τ, .skip, ha.trans h⟩
  | @seqRev a σ b h1 ih =>
    intro τ h
    simp only [Stmt.WF, Bool.and_eq_true] at hwf
    cases hg : (Stmt.seq a b).ghostCode isGhost
    · rw [erase_of_not_ghostCode hg]
      obtain ⟨o1, e1, a1⟩ := ih hwf.1 (by simp) τ h
      cases o1 with
      | rev => exact ⟨_, .seqRev e1, trivial⟩
      | ok _ => exact absurd a1 (by simp [OutAgree])
      | fail => exact absurd a1 (by simp [OutAgree])
    · rcases ghostCode_exec (.seqRev (t := b) h1) hg with hf | ⟨σ', ho, _⟩
      · cases hf
      · cases ho
  | seqFail => exact absurd rfl hnf
  | @iteT a σ o c b hc h1 ih =>
    intro τ h
    cases hg : (Stmt.ite c a b).ghostCode isGhost
    · rw [erase_of_not_ghostCode hg]
      simp only [Stmt.WF, hg, Bool.false_or, Bool.and_eq_true] at hwf
      obtain ⟨o1, e1, a1⟩ := ih hwf.1.2 hnf τ h
      exact ⟨o1, .iteT (by rwa [← Exp.eval_agree h c hwf.1.1]) e1, a1⟩
    · rw [erase_of_ghostCode hg]
      rcases ghostCode_exec (.iteT (t := b) hc h1) hg with hf | ⟨σ', ho, ha⟩
      · exact absurd hf hnf
      · subst ho; exact ⟨.ok τ, .skip, ha.trans h⟩
  | @iteF b σ o c a hc h1 ih =>
    intro τ h
    cases hg : (Stmt.ite c a b).ghostCode isGhost
    · rw [erase_of_not_ghostCode hg]
      simp only [Stmt.WF, hg, Bool.false_or, Bool.and_eq_true] at hwf
      obtain ⟨o1, e1, a1⟩ := ih hwf.2 hnf τ h
      exact ⟨o1, .iteF (by rwa [← Exp.eval_agree h c hwf.1.1]) e1, a1⟩
    · rw [erase_of_ghostCode hg]
      rcases ghostCode_exec (.iteF (s := a) hc h1) hg with hf | ⟨σ', ho, ha⟩
      · exact absurd hf hnf
      · subst ho; exact ⟨.ok τ, .skip, ha.trans h⟩
  | @loopDone c b σ hc =>
    intro τ h
    cases hg : (Stmt.loop c b).ghostCode isGhost
    · rw [erase_of_not_ghostCode hg]
      simp only [Stmt.WF, hg, Bool.false_or, Bool.and_eq_true] at hwf
      exact ⟨.ok τ, .loopDone (by rwa [← Exp.eval_agree h c hwf.1]), h⟩
    · rw [erase_of_ghostCode hg]; exact ⟨.ok τ, .skip, h⟩
  | @loopOk b σ σ1 c o hc h1 h2 ih1 ih2 =>
    intro τ h
    cases hg : (Stmt.loop c b).ghostCode isGhost
    · have hwf' := hwf
      rw [erase_of_not_ghostCode hg] at ih2 ⊢
      simp only [Stmt.WF, hg, Bool.false_or, Bool.and_eq_true] at hwf
      obtain ⟨o1, e1, a1⟩ := ih1 hwf.2 (by simp) τ h
      cases o1 with
      | ok τ1 =>
        obtain ⟨o2, e2, a2⟩ := ih2 hwf' hnf τ1 a1
        exact ⟨o2, .loopOk (by rwa [← Exp.eval_agree h c hwf.1]) e1 e2, a2⟩
      | rev => exact absurd a1 (by simp [OutAgree])
      | fail => exact absurd a1 (by simp [OutAgree])
    · rw [erase_of_ghostCode hg]
      rcases ghostCode_exec (.loopOk hc h1 h2) hg with hf | ⟨σ', ho, ha⟩
      · exact absurd hf hnf
      · subst ho; exact ⟨.ok τ, .skip, ha.trans h⟩
  | @loopRev b σ c hc h1 ih =>
    intro τ h
    cases hg : (Stmt.loop c b).ghostCode isGhost
    · rw [erase_of_not_ghostCode hg]
      simp only [Stmt.WF, hg, Bool.false_or, Bool.and_eq_true] at hwf
      obtain ⟨o1, e1, a1⟩ := ih hwf.2 (by simp) τ h
      cases o1 with
      | rev => exact ⟨_, .loopRev (by rwa [← Exp.eval_agree h c hwf.1]) e1, trivial⟩
      | ok _ => exact absurd a1 (by simp [OutAgree])
      | fail => exact absurd a1 (by simp [OutAgree])
    · rcases ghostCode_exec (.loopRev hc h1) hg with hf | ⟨σ', ho, _⟩
      · cases hf
      · cases ho
  | loopFail => exact absurd rfl hnf
  | @ghost x e σ =>
    intro τ h
    simp only [Stmt.WF] at hwf
    have hg : (Stmt.ghost x e).ghostCode isGhost = true := by simpa [Stmt.ghostCode] using hwf
    rw [erase_of_ghostCode hg]
    exact ⟨.ok τ, .skip, (Agree.set_ghost hwf _).trans h⟩
  | assertOk =>
    intro τ h; exact ⟨.ok τ, by simp [Stmt.erase, Stmt.ghostCode]; exact .skip, h⟩
  | assertFail => exact absurd rfl hnf
  | assume =>
    intro τ h; exact ⟨.ok τ, by simp [Stmt.erase, Stmt.ghostCode]; exact .skip, h⟩

/-! ## Completeness: every execution of the erased program is matched -/

theorem ghostTotal_here {s : Stmt} (ht : GhostTotal isGhost s) (hg : s.ghostCode isGhost = true) :
    ∀ σ, ∃ o, Exec s σ o := by
  cases s <;> simp only [GhostTotal] at ht
  all_goals first | exact ht hg | exact ht.1 hg

/-- **Completeness of erasure.** Every execution of the erased program of a well-formed program
whose ghost code terminates is matched, from any store agreeing on the real variables (any ghost
state), by an instrumented execution that agrees with it on the real variables or fails an
assertion. -/
theorem complete : ∀ {s : Stmt}, s.WF isGhost = true → GhostTotal isGhost s →
    ∀ {τ : Store} {o : Out}, Exec (s.erase isGhost) τ o → ∀ σ, Agree isGhost σ τ →
      ∃ o', Exec s σ o' ∧ (o' = .fail ∨ OutAgree isGhost o' o) := by
  intro s
  induction s with
  | skip =>
    intro _ _ τ o hx σ h
    simp only [Stmt.erase, Stmt.ghostCode, ite_true] at hx
    cases hx
    exact ⟨_, .skip, .inr h⟩
  | assign x e =>
    intro hwf _ τ o hx σ h
    simp only [Stmt.WF, Bool.and_eq_true, Bool.not_eq_true'] at hwf
    simp only [Stmt.erase, Stmt.ghostCode] at hx
    cases hx
    refine ⟨_, .assign, .inr ?_⟩
    show Agree isGhost _ _
    rw [Exp.eval_agree h e hwf.2]
    exact h.set x _
  | require e =>
    intro hwf _ τ o hx σ h
    simp only [Stmt.WF] at hwf
    simp only [Stmt.erase, Stmt.ghostCode] at hx
    cases hx with
    | requireOk hc => exact ⟨_, .requireOk (by rwa [Exp.eval_agree h e hwf]), .inr h⟩
    | requireRev hc => exact ⟨_, .requireRev (by rwa [Exp.eval_agree h e hwf]), .inr trivial⟩
  | seq a b iha ihb =>
    intro hwf ht τ o hx σ h
    cases hg : (Stmt.seq a b).ghostCode isGhost
    · rw [erase_of_not_ghostCode hg] at hx
      simp only [Stmt.WF, Bool.and_eq_true] at hwf
      simp only [GhostTotal] at ht
      cases hx with
      | seqOk h1 h2 =>
        obtain ⟨o1, e1, a1⟩ := iha hwf.1 ht.2.1 h1 σ h
        rcases a1 with rfl | a1
        · exact ⟨_, .seqFail e1, .inl rfl⟩
        · cases o1 with
          | ok σ1 =>
            obtain ⟨o2, e2, a2⟩ := ihb hwf.2 ht.2.2 h2 σ1 a1
            exact ⟨o2, .seqOk e1 e2, a2⟩
          | _ => simp [OutAgree] at a1
      | seqRev h1 =>
        obtain ⟨o1, e1, a1⟩ := iha hwf.1 ht.2.1 h1 σ h
        rcases a1 with rfl | a1
        · exact ⟨_, .seqFail e1, .inl rfl⟩
        · cases o1 with
          | rev => exact ⟨_, .seqRev e1, .inr trivial⟩
          | _ => simp [OutAgree] at a1
      | seqFail h1 =>
        obtain ⟨o1, e1, a1⟩ := iha hwf.1 ht.2.1 h1 σ h
        rcases a1 with rfl | a1
        · exact ⟨_, .seqFail e1, .inl rfl⟩
        · cases o1 with
          | fail => exact ⟨_, .seqFail e1, .inl rfl⟩
          | _ => simp [OutAgree] at a1
    · rw [erase_of_ghostCode hg] at hx
      cases hx
      obtain ⟨o', e'⟩ := ghostTotal_here ht hg σ
      rcases ghostCode_exec e' hg with rfl | ⟨σ', rfl, a'⟩
      · exact ⟨_, e', .inl rfl⟩
      · exact ⟨_, e', .inr (a'.trans h)⟩
  | ite c a b iha ihb =>
    intro hwf ht τ o hx σ h
    cases hg : (Stmt.ite c a b).ghostCode isGhost
    · rw [erase_of_not_ghostCode hg] at hx
      simp only [Stmt.WF, hg, Bool.false_or, Bool.and_eq_true] at hwf
      simp only [GhostTotal] at ht
      cases hx with
      | iteT hc h1 =>
        obtain ⟨o1, e1, a1⟩ := iha hwf.1.2 ht.2.1 h1 σ h
        exact ⟨o1, .iteT (by rwa [Exp.eval_agree h c hwf.1.1]) e1, a1⟩
      | iteF hc h1 =>
        obtain ⟨o1, e1, a1⟩ := ihb hwf.2 ht.2.2 h1 σ h
        exact ⟨o1, .iteF (by rwa [Exp.eval_agree h c hwf.1.1]) e1, a1⟩
    · rw [erase_of_ghostCode hg] at hx
      cases hx
      obtain ⟨o', e'⟩ := ghostTotal_here ht hg σ
      rcases ghostCode_exec e' hg with rfl | ⟨σ', rfl, a'⟩
      · exact ⟨_, e', .inl rfl⟩
      · exact ⟨_, e', .inr (a'.trans h)⟩
  | loop c b ihb =>
    intro hwf ht τ o hx σ h
    cases hg : (Stmt.loop c b).ghostCode isGhost
    · have he : (Stmt.loop c b).erase isGhost = .loop c (b.erase isGhost) := by
        simp [Stmt.erase, hg]
      rw [he] at hx
      simp only [Stmt.WF, hg, Bool.false_or, Bool.and_eq_true] at hwf
      simp only [GhostTotal] at ht
      generalize hl : Stmt.loop c (b.erase isGhost) = l at hx
      induction hx generalizing σ with
      | loopDone hc =>
        cases hl
        exact ⟨_, .loopDone (by rwa [Exp.eval_agree h c hwf.1]), .inr h⟩
      | loopOk hc h1 _ _ ih2 =>
        cases hl
        obtain ⟨o1, e1, a1⟩ := ihb hwf.2 ht.2 h1 σ h
        rcases a1 with rfl | a1
        · exact ⟨_, .loopFail (by rwa [Exp.eval_agree h c hwf.1]) e1, .inl rfl⟩
        · cases o1 with
          | ok σ1 =>
            obtain ⟨o2, e2, a2⟩ := ih2 σ1 a1 rfl
            exact ⟨o2, .loopOk (by rwa [Exp.eval_agree h c hwf.1]) e1 e2, a2⟩
          | _ => simp [OutAgree] at a1
      | loopRev hc h1 =>
        cases hl
        obtain ⟨o1, e1, a1⟩ := ihb hwf.2 ht.2 h1 σ h
        rcases a1 with rfl | a1
        · exact ⟨_, .loopFail (by rwa [Exp.eval_agree h c hwf.1]) e1, .inl rfl⟩
        · cases o1 with
          | rev => exact ⟨_, .loopRev (by rwa [Exp.eval_agree h c hwf.1]) e1, .inr trivial⟩
          | _ => simp [OutAgree] at a1
      | loopFail hc h1 =>
        cases hl
        obtain ⟨o1, e1, a1⟩ := ihb hwf.2 ht.2 h1 σ h
        rcases a1 with rfl | a1
        · exact ⟨_, .loopFail (by rwa [Exp.eval_agree h c hwf.1]) e1, .inl rfl⟩
        · cases o1 with
          | fail => exact ⟨_, .loopFail (by rwa [Exp.eval_agree h c hwf.1]) e1, .inl rfl⟩
          | _ => simp [OutAgree] at a1
      | _ => cases hl
    · rw [erase_of_ghostCode hg] at hx
      cases hx
      obtain ⟨o', e'⟩ := ghostTotal_here ht hg σ
      rcases ghostCode_exec e' hg with rfl | ⟨σ', rfl, a'⟩
      · exact ⟨_, e', .inl rfl⟩
      · exact ⟨_, e', .inr (a'.trans h)⟩
  | ghost x e =>
    intro hwf ht τ o hx σ h
    have hg : (Stmt.ghost x e).ghostCode isGhost = true := by simpa [Stmt.WF, Stmt.ghostCode] using hwf
    rw [erase_of_ghostCode hg] at hx
    cases hx
    exact ⟨_, .ghost, .inr ((Agree.set_ghost (by simpa [Stmt.WF] using hwf) _).trans h)⟩
  | assert e =>
    intro _ _ τ o hx σ h
    simp only [Stmt.erase, Stmt.ghostCode, ite_true] at hx
    cases hx
    by_cases hc : e.eval σ = 0
    · exact ⟨_, .assertFail hc, .inl rfl⟩
    · exact ⟨_, .assertOk hc, .inr h⟩
  | assume e =>
    intro _ ht τ o hx σ h
    simp only [Stmt.erase, Stmt.ghostCode, ite_true] at hx
    cases hx
    obtain ⟨o', e'⟩ := ht (by simp [Stmt.ghostCode]) σ
    cases e'
    exact ⟨_, .assume ‹_›, .inr h⟩

/-! ## A spec proved with ghost code holds of the erased program -/

/-- **A spec proved with ghost code holds of the erased program.** If every instrumented
execution of a well-formed program whose ghost code terminates passes its assertions and ends in
an outcome meeting `Q`, then every execution of the erased program, from any store, ends in an
outcome that agrees on the real variables with one meeting `Q`: one started from that store with
any ghost state. When `Q` reads only real variables it holds of the erased outcome itself
(`spec_of_erased_real`). -/
theorem spec_of_erased {s : Stmt} {Q : Store → Out → Prop} (hwf : s.WF isGhost = true)
    (ht : GhostTotal isGhost s)
    (hproof : ∀ σ o, Exec s σ o → o ≠ .fail ∧ Q σ o) :
    ∀ τ o, Exec (s.erase isGhost) τ o → ∀ σ, Agree isGhost σ τ →
      ∃ o', Exec s σ o' ∧ Q σ o' ∧ OutAgree isGhost o' o := by
  intro τ o hx σ h
  obtain ⟨o', e', a'⟩ := complete hwf ht hx σ h
  obtain ⟨hnf, hq⟩ := hproof σ o' e'
  rcases a' with rfl | a'
  · exact absurd rfl hnf
  · exact ⟨o', e', hq, a'⟩

/-- `Q` reads only the real variables of the outcome. -/
def RealOnly (isGhost : String → Bool) (Q : Out → Prop) : Prop :=
  ∀ o o', OutAgree isGhost o o' → Q o → Q o'

/-- A real postcondition proved with ghost code holds of every execution of the erased program. -/
theorem spec_of_erased_real {s : Stmt} {Q : Out → Prop} (hwf : s.WF isGhost = true)
    (ht : GhostTotal isGhost s) (hq : RealOnly isGhost Q)
    (hproof : ∀ σ o, Exec s σ o → o ≠ .fail ∧ Q o) :
    ∀ τ o, Exec (s.erase isGhost) τ o → Q o := by
  intro τ o hx
  obtain ⟨o', _, hq', a'⟩ := spec_of_erased (Q := fun _ o => Q o) hwf ht hproof τ o hx τ
    (Agree.refl τ)
  exact hq o' o a' hq'

/-! ## Ghost code without loops or assumptions terminates -/

/-- Ghost code made of ghost updates and assertions, under sequencing and conditionals. -/
def Stmt.straight : Stmt → Bool
  | .skip | .assert _ | .ghost _ _ | .assign _ _ | .require _ => true
  | .seq a b | .ite _ a b => a.straight && b.straight
  | .loop _ _ | .assume _ => false

theorem total_of_straight : ∀ {s : Stmt}, s.straight = true → ∀ σ, ∃ o, Exec s σ o
  | .skip, _, σ => ⟨_, .skip⟩
  | .assign _ _, _, σ => ⟨_, .assign⟩
  | .ghost _ _, _, σ => ⟨_, .ghost⟩
  | .require e, _, σ => by
    by_cases hc : e.eval σ = 0
    · exact ⟨_, .requireRev hc⟩
    · exact ⟨_, .requireOk hc⟩
  | .assert e, _, σ => by
    by_cases hc : e.eval σ = 0
    · exact ⟨_, .assertFail hc⟩
    · exact ⟨_, .assertOk hc⟩
  | .seq a b, hs, σ => by
    simp only [Stmt.straight, Bool.and_eq_true] at hs
    obtain ⟨o1, e1⟩ := total_of_straight hs.1 σ
    cases o1 with
    | ok σ1 =>
      obtain ⟨o2, e2⟩ := total_of_straight hs.2 σ1
      exact ⟨_, .seqOk e1 e2⟩
    | rev => exact ⟨_, .seqRev e1⟩
    | fail => exact ⟨_, .seqFail e1⟩
  | .ite c a b, hs, σ => by
    simp only [Stmt.straight, Bool.and_eq_true] at hs
    by_cases hc : c.eval σ = 0
    · obtain ⟨o, e⟩ := total_of_straight hs.2 σ
      exact ⟨_, .iteF hc e⟩
    · obtain ⟨o, e⟩ := total_of_straight hs.1 σ
      exact ⟨_, .iteT hc e⟩

/-- **Rule 3 for straight-line ghost code**: a program whose statements have no loop and no
assumption meets `GhostTotal`. -/
theorem ghostTotal_of_straight : ∀ {s : Stmt}, s.straight = true → GhostTotal isGhost s
  | .skip, _ | .assert _, _ | .ghost _ _, _ | .assign _ _, _ | .require _, _ =>
    fun _ => total_of_straight (by simp [Stmt.straight])
  | .seq a b, hs => by
    simp only [Stmt.straight, Bool.and_eq_true] at hs
    exact ⟨fun _ => total_of_straight (by simp [Stmt.straight, hs]),
      ghostTotal_of_straight hs.1, ghostTotal_of_straight hs.2⟩
  | .ite c a b, hs => by
    simp only [Stmt.straight, Bool.and_eq_true] at hs
    exact ⟨fun _ => total_of_straight (by simp [Stmt.straight, hs]),
      ghostTotal_of_straight hs.1, ghostTotal_of_straight hs.2⟩

end SolidCore.Spec.Ghost

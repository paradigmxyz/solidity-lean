import Verify.LoopSource.Equiv.Inv

/-!
# The decided obligations are the obligations

`obl_of_checkWith`: when `Inv.checkWith` accepts the leaves of a cut-point check with an invariant
`I` and a measure `μ`, the leaves meet `Obl` for the loop record whose invariant is `I` and whose
measure is `μ` (`recOf`). Every step of the check is a refutation by `refuteOb`, sound by
`refuteOb_sound`, of formulas that hold at the valuation (`obIn_holds`: `env ρ` interprets each word's
term as its value, and each case split of a word's arithmetic holds).
-/

namespace Verify.LoopSource.Equiv.Inv
open SolarTV SolidCore.Refinement.Generic Verify.LoopSource.Equiv Verify.LoopSource.Interface
open SolidCore.Verify.VC (Tm refuteOb refuteOb_sound eval_app holds_app eval_num Value applyOp
  isOpName)

/-! ## Terms of words -/

theorem W_pos : 0 < W := by unfold W wordSize; positivity

theorem applyOp_uf (u : String → List Int → Int) (f : String) (vs : List Value) (h : isOpName f = false)
    (h1 : f ≠ "+") (h2 : f ≠ "-") (h3 : f ≠ "*") (h4 : f ≠ "div") (h5 : f ≠ "mod") (h6 : f ≠ "<=")
    (h7 : f ≠ "<") (h8 : f ≠ ">=") (h9 : f ≠ ">") (h10 : f ≠ "=") (h11 : f ≠ "not") (h12 : f ≠ "=>")
    (h13 : f ≠ "and") (h14 : f ≠ "or") (h15 : f ≠ "ite") (h16 : f ≠ "select") (h17 : f ≠ "store")
    (h18 : f ≠ "(as const (Array Int Int))") (h19 : f ≠ "(as const (Array Int (Array Int Int)))") :
    applyOp u f vs = .int (u f (vs.map Value.toInt)) := by
  unfold applyOp
  split <;> simp_all

theorem eval_uf (σ : SolidCore.Verify.VC.Env) (f : String) (args : List Tm) (h : isOpName f = false)
    (h1 : f ≠ "+") (h2 : f ≠ "-") (h3 : f ≠ "*") (h4 : f ≠ "div") (h5 : f ≠ "mod") (h6 : f ≠ "<=")
    (h7 : f ≠ "<") (h8 : f ≠ ">=") (h9 : f ≠ ">") (h10 : f ≠ "=") (h11 : f ≠ "not") (h12 : f ≠ "=>")
    (h13 : f ≠ "and") (h14 : f ≠ "or") (h15 : f ≠ "ite") (h16 : f ≠ "select") (h17 : f ≠ "store")
    (h18 : f ≠ "(as const (Array Int Int))") (h19 : f ≠ "(as const (Array Int (Array Int Int)))") :
    (Tm.app f args).eval σ = .int (σ.u f (args.map (fun t => (t.eval σ).toInt))) := by
  rw [eval_app, applyOp_uf σ.u f _ h h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19]
  simp [List.map_map, Function.comp_def]

/-- The value of a term that is an integer. -/
theorem toInt_int (n : Int) : (Value.int n).toInt = n := rfl

/-- **A word's term is its value.** -/
theorem tr_eval (ρ : Val) : ∀ e : WExpr, (tr e).eval (env ρ) = .int (e.eval ρ : Int)
  | .lit v => by simp [tr, eval_num, WExpr.eval, W]
  | .arg i => by
    rw [tr, eval_uf _ _ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    simp [env, uOf, eval_num, Value.toInt, WExpr.eval, W]
  | .init k => by
    rw [tr, eval_uf _ _ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    simp [env, uOf, eval_num, Value.toInt, WExpr.eval, W]
  | .un op a => by
    rw [tr, eval_uf _ _ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    simp only [List.map, eval_num, tr_eval ρ a, toInt_int]
    simp [env, uOf, WExpr.eval, W, unOf_code]
  | .bin op a b => by
    rw [tr, eval_uf _ _ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    simp only [List.map, eval_num, tr_eval ρ a, tr_eval ρ b, toInt_int]
    simp [env, uOf, WExpr.eval, W, binOf_code]
  | .sinit k => by
    rw [tr, eval_uf _ _ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    simp only [List.map, tr_eval ρ k, toInt_int]
    simp [env, uOf, WExpr.eval, W]
  | .sel c a b => by
    rw [tr, eval_uf _ _ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    simp only [List.map, tr_eval ρ c, tr_eval ρ a, tr_eval ρ b, toInt_int]
    simp only [env, uOf, WExpr.eval]
    split <;> simp_all
  | .hash a b => by
    rw [tr, eval_uf _ _ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    simp only [List.map, tr_eval ρ a, tr_eval ρ b, toInt_int]
    simp [env, uOf, WExpr.eval, W]
  | .caller => by
    rw [tr, eval_uf _ _ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    simp [env, uOf, eval_num, Value.toInt, WExpr.eval, W]

/-! ## Formulas -/

theorem h_cmp (σ : SolidCore.Verify.VC.Env) (f : String) (a b : Tm) :
    (Tm.app f [a, b]).Holds σ = (applyOp σ.u f [a.eval σ, b.eval σ]).toProp := by
  rw [holds_app]; rfl

theorem h_not (σ : SolidCore.Verify.VC.Env) (a : Tm) : (Tm.app "not" [a]).Holds σ ↔ ¬ a.Holds σ := by
  rw [holds_app]; simp [applyOp, Value.toProp, SolidCore.Verify.VC.Tm.Holds]

theorem h_or2 (σ : SolidCore.Verify.VC.Env) (a b : Tm) :
    (Tm.app "or" [a, b]).Holds σ ↔ a.Holds σ ∨ b.Holds σ := by
  rw [SolidCore.Verify.VC.holds_or]; simp

theorem h_and2 (σ : SolidCore.Verify.VC.Env) (a b : Tm) :
    (Tm.app "and" [a, b]).Holds σ ↔ a.Holds σ ∧ b.Holds σ := by
  rw [SolidCore.Verify.VC.holds_and]; simp

theorem e_add (σ : SolidCore.Verify.VC.Env) (a b : Tm) :
    (Tm.app "+" [a, b]).eval σ = .int ((a.eval σ).toInt + (b.eval σ).toInt) := by
  rw [eval_app]; rfl

theorem e_sub (σ : SolidCore.Verify.VC.Env) (a b : Tm) :
    (Tm.app "-" [a, b]).eval σ = .int ((a.eval σ).toInt - (b.eval σ).toInt) := by
  rw [eval_app]; rfl

theorem h_le (ρ : Val) (a b : WExpr) :
    (Tm.app "<=" [tr a, tr b]).Holds (env ρ) ↔ a.eval ρ ≤ b.eval ρ := by
  rw [h_cmp, tr_eval, tr_eval]; simp [applyOp, Value.toProp, Value.toInt]

theorem h_lt (ρ : Val) (a b : WExpr) :
    (Tm.app "<" [tr a, tr b]).Holds (env ρ) ↔ a.eval ρ < b.eval ρ := by
  rw [h_cmp, tr_eval, tr_eval]; simp [applyOp, Value.toProp, Value.toInt]

theorem h_eq (ρ : Val) (a b : WExpr) :
    (Tm.app "=" [tr a, tr b]).Holds (env ρ) ↔ a.eval ρ = b.eval ρ := by
  rw [h_cmp, tr_eval, tr_eval]; simp [applyOp, Value.toProp, Value.eq]

theorem h_eq0 (ρ : Val) (a : WExpr) :
    (Tm.app "=" [tr a, .num 0]).Holds (env ρ) ↔ a.eval ρ = 0 := by
  rw [h_cmp, tr_eval, eval_num]; simp [applyOp, Value.toProp, Value.eq]

/-- **A formula's term holds exactly when the formula does.** -/
theorem F.tr_holds (ρ : Val) : ∀ f : F, f.tr.Holds (env ρ) ↔ f.Holds ρ
  | .fact e true => by
    simp only [F.tr, F.Holds, ↓reduceIte, h_not, h_eq0]
    simp
  | .fact e false => by
    simp only [F.tr, F.Holds, Bool.false_eq_true, ↓reduceIte, h_eq0]
    simp
  | .le a b => h_le ρ a b
  | .lt a b => h_lt ρ a b
  | .eq a b => h_eq ρ a b
  | .lin a b c d => by
    simp only [F.tr, F.Holds]
    rw [h_cmp, e_add, e_add, tr_eval, tr_eval, tr_eval, tr_eval]
    simp only [applyOp, Value.toProp, Value.eq, Value.toInt]
    omega
  | .or f g => by simp only [F.tr, F.Holds, h_or2, F.tr_holds ρ f, F.tr_holds ρ g]
  | .not f => by simp only [F.tr, F.Holds, h_not, F.tr_holds ρ f]

/-! ## Every word's facts hold -/

theorem rng_holds (ρ : Val) (e : WExpr) : ∀ t ∈ rng e, t.Holds (env ρ) := by
  have hl := e.eval_lt ρ
  intro t ht
  simp only [rng, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl
  · rw [h_cmp, eval_num, tr_eval]; simp [applyOp, Value.toProp, Value.toInt]
  · rw [h_cmp, eval_num, tr_eval]
    simp only [applyOp, Value.toProp, Value.toInt]
    have : (W : Int) - 1 = ((W - 1 : Nat) : Int) := by have := W_pos; omega
    unfold W at *
    omega

theorem W_eq : W = 2 ^ 256 := rfl

theorem defs_holds (ρ : Val) (e : WExpr) : ∀ t ∈ defs e, t.Holds (env ρ) := by
  intro t ht
  cases e with
  | bin op a b =>
    have ha := a.eval_lt ρ
    have hb := b.eval_lt ρ
    unfold wordSize at ha hb
    cases op <;> simp only [defs, List.mem_singleton, List.not_mem_nil] at ht <;> subst ht <;>
      rw [h_or2, h_and2, h_and2] <;>
      simp only [h_cmp, h_not, e_add, e_sub, tr_eval, eval_num, applyOp, Value.toProp, Value.toInt,
        Value.eq, WExpr.eval, BinOp.eval, W, wordSize] <;>
      (try split_ifs) <;> omega
  | un op a =>
    have ha := a.eval_lt ρ
    unfold wordSize at ha
    cases op <;> simp only [defs, List.mem_singleton, List.not_mem_nil] at ht <;> subst ht <;>
      rw [h_or2, h_and2, h_and2] <;>
      simp only [h_cmp, h_not, tr_eval, eval_num, applyOp, Value.toProp, Value.toInt,
        Value.eq, WExpr.eval, UnOp.eval, W, wordSize] <;>
      (try split_ifs) <;> omega
  | _ => simp [defs] at ht

/-- **Every term of an obligation holds** at a valuation where its formulas do. -/
theorem obIn_holds {keep : WExpr → Bool} {ρ : Val} {hyps : List F} (h : ∀ f ∈ hyps, f.Holds ρ) :
    ∀ t ∈ obIn keep hyps, t.Holds (env ρ) := by
  intro t ht
  simp only [obIn, List.mem_append, List.mem_flatMap, List.mem_map, List.mem_filter] at ht
  rcases ht with (⟨e, -, he⟩ | ⟨f, hf, rfl⟩) | ⟨e, -, he⟩
  · exact rng_holds ρ e t he
  · exact (F.tr_holds ρ f).mpr (h f hf)
  · exact defs_holds ρ e t he

/-- **A refutation has no valuation.** -/
theorem refutes_sound {n : Nat} {hyps : List F} (h : refutes n hyps = true) (ρ : Val) :
    ¬ ∀ f ∈ hyps, f.Holds ρ := fun hh => by
  simp only [refutes, Bool.or_eq_true] at h
  rcases h with h | h
  · exact refuteOb_sound h (env ρ) (obIn_holds hh)
  · exact refuteOb_sound h (env ρ) (obIn_holds hh)

theorem slice_sub (k : Nat) (S seed : List F) : ∀ f ∈ slice k S seed, f ∈ S := by
  intro f hf
  simp only [slice, List.mem_filter] at hf
  exact hf.1

/-- **What `proves` accepts holds.** -/
theorem proves_sound {n : Nat} {S K : List F} {g : F} (h : proves n S K g = true) {ρ : Val}
    (hS : ∀ f ∈ S, f.Holds ρ) (hK : ∀ f ∈ K, f.Holds ρ) : g.Holds ρ := by
  simp only [proves, Bool.or_eq_true, List.contains_iff_mem] at h
  by_contra hg
  have key : ∀ k, refutes n (slice k S (g :: K) ++ K ++ [.not g]) = true → False := fun k hr =>
    refutes_sound hr ρ fun f hf => by
      simp only [List.mem_append, List.mem_singleton] at hf
      rcases hf with (hf | hf) | rfl
      · exact hS f (slice_sub k S _ f hf)
      · exact hK f hf
      · exact hg
  rcases h with ((hm | hm) | hr) | hr
  · exact hg (hS g (by simpa using hm))
  · exact hg (hK g (by simpa using hm))
  · exact key 0 hr
  · exact key 1 hr

/-! ## Header valuations -/

theorem sub_eval {n : Nat} {σ : Val} (hl : n ≤ σ.args.length) (hs : List WExpr) :
    ∀ e : WExpr, (sub n hs e).eval σ = e.eval (nextVal n σ hs)
  | .lit _ => rfl
  | .arg i => by
    simp only [sub]
    split
    · rename_i hi
      simp only [WExpr.eval, nextVal]
      rw [take_getD hi hl]
    · rename_i hi
      have ht : (σ.args.take n).length = n := by simp; omega
      simp only [WExpr.eval, nextVal]
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), ht, List.getElem?_map]
      cases hk : hs[i - n]? with
      | none => simp [WExpr.eval]
      | some e =>
        simp only [Option.getD_some, Option.map_some]
        exact (Nat.mod_eq_of_lt (e.eval_lt σ)).symm
  | .init _ => rfl
  | .un op a => by simp only [sub, WExpr.eval, sub_eval hl hs a]
  | .bin op a b => by simp only [sub, WExpr.eval, sub_eval hl hs a, sub_eval hl hs b]
  | .sinit k => by simp only [sub, WExpr.eval, sub_eval hl hs k]; rfl
  | .sel c a b => by simp only [sub, WExpr.eval, sub_eval hl hs c, sub_eval hl hs a, sub_eval hl hs b]
  | .hash a b => by simp only [sub, WExpr.eval, sub_eval hl hs a, sub_eval hl hs b]; rfl
  | .caller => rfl

theorem F.sub_holds {n : Nat} {σ : Val} (hl : n ≤ σ.args.length) (hs : List WExpr) :
    ∀ f : F, (f.sub n hs).Holds σ ↔ f.Holds (nextVal n σ hs)
  | .fact e b => by simp only [F.sub, F.Holds, sub_eval hl hs]
  | .le a b => by simp only [F.sub, F.Holds, sub_eval hl hs]
  | .lt a b => by simp only [F.sub, F.Holds, sub_eval hl hs]
  | .eq a b => by simp only [F.sub, F.Holds, sub_eval hl hs]
  | .lin a b c d => by simp only [F.sub, F.Holds, sub_eval hl hs]
  | .or f g => by simp only [F.sub, F.Holds, F.sub_holds hl hs f, F.sub_holds hl hs g]
  | .not f => by simp only [F.sub, F.Holds, F.sub_holds hl hs f]

theorem factsF_holds {ρ : Val} {K : Facts} (h : K.Hold ρ) : ∀ f ∈ factsF K, f.Holds ρ := by
  intro f hf
  simp only [factsF, List.mem_map] at hf
  obtain ⟨p, hp, rfl⟩ := hf
  exact h p hp

theorem noCase_holds {ρ : Val} : ∀ {c : Facts}, ¬ c.Hold ρ → (noCase c).Holds ρ
  | [], h => absurd (fun _ hp => absurd hp List.not_mem_nil) h
  | p :: c, h => by
    simp only [noCase, List.foldr_cons]
    show F.Holds ρ (.or _ _)
    simp only [F.Holds]
    by_cases hp : (p.1.eval ρ = 0 ↔ p.2 = false)
    · right
      exact noCase_holds fun hc => h fun q hq => by
        rcases List.mem_cons.mp hq with rfl | hq
        · exact hp
        · exact hc q hq
    · left; exact hp

/-! ## Ends -/

theorem paths_sound (ρ : Val) : ∀ T : Tree, ∃ p ∈ paths T, p.1.Hold ρ ∧ T.eval ρ = p.2.eval ρ ∧
    ∃ ok out ws ls, p.2 = .halt ok out ws ls
  | .halt ok out ws ls => ⟨_, List.mem_singleton_self _, fun _ h => absurd h List.not_mem_nil, rfl,
      ok, out, ws, ls, rfl⟩
  | .ite c t e => by
    by_cases h0 : c.eval ρ = 0
    · obtain ⟨p, hp, hh, he, hhalt⟩ := paths_sound ρ e
      refine ⟨((c, false) :: p.1, p.2), ?_, ?_, ?_, hhalt⟩
      · simp only [paths, List.mem_append, List.mem_map]
        exact Or.inr ⟨p, hp, rfl⟩
      · intro q hq
        rcases List.mem_cons.mp hq with rfl | hq
        · simp [h0]
        · exact hh q hq
      · simp only [Tree.eval, h0, ↓reduceIte, he]
    · obtain ⟨p, hp, hh, he, hhalt⟩ := paths_sound ρ t
      refine ⟨((c, true) :: p.1, p.2), ?_, ?_, ?_, hhalt⟩
      · simp only [paths, List.mem_append, List.mem_map]
        exact Or.inl ⟨p, hp, rfl⟩
      · intro q hq
        rcases List.mem_cons.mp hq with rfl | hq
        · simp [h0]
        · exact hh q hq
      · simp only [Tree.eval, h0, ↓reduceIte, he]

theorem readLit_some {K : Nat} : ∀ {ws : Writes}, ws.all isLitKey = true → ∃ e, readLit K ws = some e
  | [], _ => ⟨_, rfl⟩
  | (k, e) :: ws, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    cases k with
    | lit k =>
      simp only [readLit]
      split
      · exact ⟨_, rfl⟩
      · exact readLit_some h.2
    | _ => simp [isLitKey] at h

theorem readLit_none {K : Nat} : ∀ {ws : Writes}, ws.all isLitKey = true → K ∉ keysLit ws →
    readLit K ws = some (.init K)
  | [], _, _ => rfl
  | (k, e) :: ws, h, hk => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    cases k with
    | lit k =>
      simp only [keysLit, List.mem_cons, not_or] at hk
      simp only [readLit, Ne.symm hk.1, ↓reduceIte]
      exact readLit_none h.2 hk.2
    | _ => simp [isLitKey] at h

theorem store_readLit {ρ : Val} (hρ : ρ.Ok) (n : Nat) : ∀ {ws : Writes} {e : WExpr},
    readLit (n % W) ws = some e → Writes.store ρ ws n = e.eval ρ
  | [], e, h => by
    simp only [readLit, Option.some.injEq] at h
    subst h
    simp only [Writes.store, WExpr.eval]
    exact (hρ n).symm
  | (k, e') :: ws, e, h => by
    cases k with
    | lit k =>
      simp only [readLit] at h
      by_cases hk : k % W = n % W
      · rw [if_pos hk] at h
        simp only [Option.some.injEq] at h
        subst h
        have hk' : k % wordSize = n % wordSize := hk
        simp [Writes.store, WExpr.eval, hk']
      · rw [if_neg hk] at h
        have hk' : ¬ k % wordSize = n % wordSize := hk
        simp [Writes.store, WExpr.eval, hk', store_readLit hρ n h]
    | _ => simp [readLit] at h

theorem obytes_eq {ρ : Val} {out out' : List OByte} (h : out.map OByte.norm = out'.map OByte.norm) :
    out.map (OByte.eval ρ) = out'.map (OByte.eval ρ) := by
  have e1 : out.map (OByte.eval ρ) = (out.map OByte.norm).map (OByte.eval ρ) := by
    simp [List.map_map, Function.comp_def, OByte.eval_norm]
  have e2 : out'.map (OByte.eval ρ) = (out'.map OByte.norm).map (OByte.eval ρ) := by
    simp [List.map_map, Function.comp_def, OByte.eval_norm]
  rw [e1, e2, h]

theorem mapM_mem {α β : Type} {f : α → Option β} : ∀ {l : List α} {gs : List β}, l.mapM f = some gs →
    ∀ x ∈ l, ∃ y ∈ gs, f x = some y
  | [], _, _, x, hx => absurd hx List.not_mem_nil
  | a :: l, gs, h, x, hx => by
    rw [List.mapM_cons] at h
    cases ha : f a with
    | none => simp [ha] at h
    | some b =>
    cases hl : l.mapM f with
    | none => simp [ha, hl] at h
    | some bs =>
    simp only [ha, hl, Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.some.injEq] at h
    subst h
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ⟨b, List.mem_cons_self .., ha⟩
    · obtain ⟨y, hy, hfy⟩ := mapM_mem hl x hx
      exact ⟨y, List.mem_cons_of_mem _ hy, hfy⟩

/-- **Two ends whose goals hold show the same.** -/
theorem halt_obs {ρ : Val} (hρ : ρ.Ok) {H H' : Tree} {gs : List F} (h : haltGoals H H' = some gs)
    (hg : ∀ g ∈ gs, g.Holds ρ) : (H.eval ρ).obs = (H'.eval ρ).obs := by
  cases H with
  | ite => simp [haltGoals] at h
  | halt ok out ws ls =>
  cases H' with
  | ite => simp [haltGoals] at h
  | halt ok' out' ws' ls' =>
  simp only [haltGoals] at h
  split at h
  · simp only [Option.some.injEq] at h
    subst h
    exact absurd (hg _ (List.mem_singleton_self _)) (by simp [F.Holds, WExpr.eval])
  · rename_i hok
    simp only [ne_eq, Decidable.not_not] at hok
    subst hok
    split at h
    · rename_i hc
      obtain ⟨hout, -, rfl, rfl, hw, hw'⟩ := hc
      simp only [Tree.eval, Res.obs, obytes_eq hout, List.map_nil, ite_self]
      cases ok with
      | false => rfl
      | true =>
        simp only [↓reduceIte, SolarTV.Observable.mk.injEq, true_and]
        funext k
        rw [← Writes.store_mod ρ hρ k ws, ← Writes.store_mod ρ hρ k ws']
        obtain ⟨a, ha⟩ := readLit_some (K := k % wordSize) hw
        obtain ⟨b, hb⟩ := readLit_some (K := k % wordSize) hw'
        have hk : (k % wordSize) % W = k % wordSize := Nat.mod_mod _ _
        rw [store_readLit hρ (k % wordSize) (by rw [hk]; exact ha),
          store_readLit hρ (k % wordSize) (by rw [hk]; exact hb)]
        by_cases hin : k % wordSize ∈ keysLit ws ++ keysLit ws'
        · simp only at h
          obtain ⟨g, hgm, hgk⟩ := mapM_mem h _ hin
          simp [ha, hb] at hgk
          subst hgk
          exact hg _ hgm
        · simp only [List.mem_append, not_or] at hin
          rw [readLit_none hw hin.1] at ha
          rw [readLit_none hw' hin.2] at hb
          simp only [Option.some.injEq] at ha hb
          subst ha hb
          rfl
    · simp at h

theorem refutesSl_sound {n : Nat} {S K : List F} (h : refutesSl n S K = true) {ρ : Val}
    (hS : ∀ f ∈ S, f.Holds ρ) (hK : ∀ f ∈ K, f.Holds ρ) : False := by
  simp only [refutesSl, Bool.or_eq_true] at h
  have key : ∀ k, refutes n (slice k S K ++ K) = true → False := fun k hr =>
    refutes_sound hr ρ fun f hf => by
      simp only [List.mem_append] at hf
      rcases hf with hf | hf
      · exact hS f (slice_sub k S _ f hf)
      · exact hK f hf
  rcases h with hr | hr
  · exact key 0 hr
  · exact key 1 hr

/-- **An accepted end shows the tree's result.** -/
theorem exitOk_sound {n : Nat} {S K : List F} {T' T : Tree} (h : exitOk n S K T' T = true) {ρ : Val} (hρ : ρ.Ok)
    (hS : ∀ f ∈ S, f.Holds ρ) (hK : ∀ f ∈ K, f.Holds ρ) : (T'.eval ρ).obs = (T.eval ρ).obs := by
  obtain ⟨p', hp', hh', he', -⟩ := paths_sound ρ T'
  obtain ⟨p, hp, hhp, he, -⟩ := paths_sound ρ T
  have hall : ∀ f ∈ K ++ factsF p'.1 ++ factsF p.1, f.Holds ρ := by
    intro f hf
    simp only [List.mem_append] at hf
    rcases hf with (hf | hf) | hf
    · exact hK f hf
    · exact factsF_holds hh' f hf
    · exact factsF_holds hhp f hf
  have hc := List.all_eq_true.mp (List.all_eq_true.mp h p' hp') p hp
  simp only [Bool.or_eq_true] at hc
  rw [he', he]
  rcases hc with hr | hg
  · exact (refutesSl_sound hr hS hall).elim
  · split at hg
    · rename_i gs hgs
      exact halt_obs hρ hgs fun g hgm => proves_sound (List.all_eq_true.mp hg g hgm) hS hall
    · simp at hg

/-! ## The call's words -/

theorem trunc_eq (n : Nat) (σ : Val) : trunc n σ = nextVal n σ [] := by
  simp [trunc, nextVal]

theorem obyte_below {n : Nat} {σ : Val} (hl : n ≤ σ.args.length) (b : OByte)
    (h : (match b with | .lit _ => true | .byteOf e _ => argsBelow n e) = true) :
    b.eval (trunc n σ) = b.eval σ := by
  cases b with
  | lit _ => rfl
  | byteOf e i => simp only [OByte.eval, trunc_eq, eval_below hl [] e h]

theorem store_below {n : Nat} {σ : Val} (hl : n ≤ σ.args.length) :
    ∀ ws : Writes, ws.all (fun w => argsBelow n w.1 && argsBelow n w.2) = true →
      Writes.store (trunc n σ) ws = Writes.store σ ws
  | [], _ => rfl
  | (k, e) :: ws, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    funext m
    simp only [Writes.store, trunc_eq, eval_below hl [] k h.1.1, eval_below hl [] e h.1.2]
    rw [← trunc_eq, congrFun (store_below hl ws h.2) m]

/-- **A tree over the call's words gives every header valuation the call's result.** -/
theorem tree_below {n : Nat} {σ : Val} (hl : n ≤ σ.args.length) :
    ∀ T : Tree, treeBelow n T = true → T.eval (trunc n σ) = T.eval σ
  | .halt ok out ws ls, h => by
    simp only [treeBelow, Bool.and_eq_true, List.all_eq_true] at h
    obtain ⟨⟨hout, hws⟩, hls⟩ := h
    simp only [Tree.eval]
    congr 1
    · exact List.map_congr_left fun b hb => obyte_below hl b (hout b hb)
    · split
      · refine List.map_congr_left fun l hl' => ?_
        have := hls l hl'
        simp only [Log.eval, Prod.mk.injEq]
        exact ⟨List.map_congr_left fun e he => by rw [trunc_eq, eval_below hl [] e (this.1 e he)],
          List.map_congr_left fun b hb => obyte_below hl b (this.2 b hb)⟩
      · rfl
    · split
      · exact store_below hl ws (List.all_eq_true.mpr fun w hw => by simp [hws w hw])
      · rfl
  | .ite c t e, h => by
    simp only [treeBelow, Bool.and_eq_true] at h
    simp only [Tree.eval, trunc_eq, eval_below hl [] c h.1.1]
    rw [← trunc_eq, tree_below hl t h.1.2, tree_below hl e h.2]

/-! ## The obligations -/

/-- **The loop record of an invariant and a measure.** Its header and body tree are unused by
`Obl`, which reads only the invariant, the measure and the condition of a step: here, that the
measure is positive. -/
def recOf (I : List F) (μ : WExpr) : LoopRecord :=
  { H := { scopes := [], writes := [], logs := [] }, P := fun σ => ∀ f ∈ I, f.Holds σ,
    m := fun σ => μ.eval σ, c := .bin .lt (.lit 0) μ,
    bb := .leaf (.normal { scopes := [], writes := [], logs := [] }) }

/-- **The decided obligations are the obligations.** -/
theorem obl_of_checkWith {n : Nat} {cases : List Facts} {T : Tree} {le li : List (Facts × Out)}
    {I : List F} {μ : WExpr} (h : checkWith n cases T le li I μ = true) :
    Obl (fun _ => recOf I μ) id (fun _ => True) (fun _ => True) n cases T le li := by
  unfold checkWith at h
  rw [List.all_eq_true] at h
  have task : ∀ t ∈ tasks le li I, t.ok n cases T I μ = true := h
  have mem_inv : ∀ f ∈ I, ∀ (e : Bool) (p : Facts × Out), (e = true → p ∈ le) → (e = false → p ∈ li) →
      Task.inv f e p ∈ tasks le li I := by
    intro f hf e p h1 h2
    simp only [tasks, List.mem_append, List.mem_flatMap, List.mem_map, List.mem_singleton]
    left; left; left; right
    refine ⟨f, hf, ?_⟩
    cases e with
    | true => exact Or.inl ⟨p, h1 rfl, rfl⟩
    | false => exact Or.inr ⟨p, h2 rfl, rfl⟩
  have hbelow : treeBelow n T = true := task .below (by simp [tasks])
  refine ⟨?_, ?_, ?_⟩
  · intro ρ hlen hok _ p hp hph
    split
    · rename_i T' hT'
      have := task (.entryEnd p) (by simp [tasks, hp])
      simp only [Task.ok, hT'] at this
      exact exitOk_sound this hok (fun _ h => absurd h List.not_mem_nil) (factsF_holds hph)
    · rename_i hs hhs
      refine ⟨fun f hf => ?_, trivial⟩
      have := task (.inv f true p) (mem_inv f hf true p (fun _ => hp) (fun h => absurd h (by decide)))
      simp only [Task.ok, hhs, ↓reduceIte] at this
      exact (F.sub_holds (by omega) hs f).mp (proves_sound this (fun _ h => absurd h List.not_mem_nil)
        (factsF_holds hph))
  · intro σ hl hok _ hP _ p hp hph
    have hleaf := task (.iterLeaf p) (by simp [tasks, hp])
    split
    · rename_i T' hT'
      simp only [Task.ok, hT'] at hleaf
      rw [exitOk_sound hleaf hok hP (factsF_holds hph), tree_below hl T hbelow]
    · rename_i hs hhs
      simp only [Task.ok, hhs] at hleaf
      have hm := proves_sound hleaf hP (factsF_holds hph)
      have hm' : μ.eval (nextVal n σ hs) < μ.eval σ := by
        rw [← sub_eval hl hs]; simpa [F.Holds] using hm
      refine ⟨⟨hP, ?_, fun f hf => ?_, hm'⟩, trivial⟩
      · show (WExpr.bin .lt (.lit 0) μ).eval σ ≠ 0
        simp only [WExpr.eval, BinOp.eval]
        have : 0 < μ.eval σ := by omega
        simp [this, wordSize]
      · have := task (.inv f false p) (mem_inv f hf false p (fun h => absurd h (by decide)) (fun _ => hp))
        simp only [Task.ok, hhs, Bool.false_eq_true, ↓reduceIte] at this
        exact (F.sub_holds hl hs f).mp (proves_sound this hP (factsF_holds hph))
  · intro σ _ hok _ hP _
    by_contra hno
    simp only [not_exists, not_and] at hno
    have hc := task .cover (by simp [tasks])
    simp only [Task.ok] at hc
    have := proves_sound hc hP fun f hf => by
      simp only [List.mem_map] at hf
      obtain ⟨c, hc, rfl⟩ := hf
      exact noCase_holds (hno c hc)
    simp [F.Holds, WExpr.eval] at this

end Verify.LoopSource.Equiv.Inv

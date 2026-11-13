import W1Proofs.Tactic
import SolarTV.CutPoint

/-! Symbolic execution of loop-free segments between cut points.

`sym_exec` runs two programs from their first configurations to their ends. A program that
loops has no such end within a fuel its blocks bound, so its stages are proved through cut
points instead (`SolarTV.CutPoint`): from every pair of configurations the exporter relates,
the two segments (`seg`) end alike. `sym_seg` proves one such obligation for configurations
whose words and state are variables: it evaluates both segments with the same definitional
steps as `sym_exec`, splits on the branch conditions they leave, and closes each leaf:

- two ends, by the agreement of equal results (`agree_of_eq`) and `sym_exec`'s leaf procedures;
- two stuck segments, trivially;
- two cut points, by the relation lemma (`mk`) of a related pair: its source configuration
  unifies with the leaf's, which fixes the related words, and the target configuration must
  then equal the leaf's, by evaluation and the same leaf procedures.

A segment that runs out of fuel, or ends differently from the other, leaves `False` or a
goal the procedures cannot close: the proof fails by mismatch. Nothing here proves an
invariant: the relations are the exporter's, and Lean only checks that they are preserved. -/

namespace SolarTV.Milestone.W1

open SolarTV.CutPoint Machine

theorem agree_of_eq {a b : Halt × State} (h : a = b) : Agree a b := h ▸ Agree.refl a

/-- One step of a segment from a configuration the code has built. Matching only a pair keeps
`dsimp` from unfolding the steps after one it cannot compute yet, as `iterate_mk` does for runs. -/
@[defeq] theorem seg_mk {α β R : Type} (step : α × β → Option (R ⊕ (α × β))) (cut : α × β → Bool)
    (k : Nat) (a : α) (b : β) :
    seg step cut (k + 1) (a, b) =
      match step (a, b) with
      | none => .stuck
      | some (.inl r) => .done r
      | some (.inr y) => if cut y then .cut y else seg step cut k y := by
  rw [seg]
  cases step (a, b) with
  | none => rfl
  | some v => cases v <;> rfl

@[defeq] theorem seg_zero {σ R : Type} (step : σ → Option (R ⊕ σ)) (cut : σ → Bool) (x : σ) :
    seg step cut 0 x = .fuel := by
  rw [seg]

/-- A related pair from one relation of a list. -/
theorem rel_mem {α β : Type} {rels : List (α → β → Prop)} {Q : α → β → Prop} {y : α} {y' : β}
    (mem : Q ∈ rels) (h : Q y y') : ∃ Q ∈ rels, Q y y' := ⟨Q, mem, h⟩

open Lean Meta Simp in
/-- A stack position, a numeral of `Fin n`, as the number it is: a segment starts from a stack of
variables, so a `dup` or `swap` reads it at that number. -/
dsimproc_decl finValLit (Fin.val _) := fun e => do
  let_expr Fin.val n a := e | return .continue
  let some n ← Nat.fromExpr? n | return .continue
  let_expr OfNat.ofNat _ lit _ := a | return .continue
  let some k := lit.rawNatLit? | return .continue
  if n == 0 then return .continue
  return .done (toExpr (k % n))

open Lean Meta Simp in
/-- `||` and `&&` of a literal, as a cut test of a known block leaves them. -/
dsimproc_decl boolLit (_ || _) := fun e => do
  let_expr or a b := e | return .continue
  match a.constName?, b.constName? with
  | some ``true, _ | _, some ``true => return .done (mkConst ``true)
  | some ``false, _ => return .done b
  | _, some ``false => return .done a
  | _, _ => return .continue

open Lean Meta Simp in
/-- `&&` of a literal. -/
dsimproc_decl boolAndLit (_ && _) := fun e => do
  let_expr and a b := e | return .continue
  match a.constName?, b.constName? with
  | some ``false, _ | _, some ``false => return .done (mkConst ``false)
  | some ``true, _ => return .done b
  | _, some ``true => return .done a
  | _, _ => return .continue

open Lean Meta Simp in
/-- A conditional on two numerals being equal, as a MIR value lookup leaves it (`Env.set`
compares value numbers): the branch the numerals pick. Definitional, since equality of numerals
decides by evaluation, so `dsimp` keeps the decision instance and the term type-correct. -/
dsimproc_decl iteNatLit (ite _ _ _) := fun e => do
  let_expr ite _ c _ a b := e | return .continue
  let_expr Eq ty x y := c | return .continue
  unless ty.isConstOf ``Nat do return .continue
  let some m ← Nat.fromExpr? x | return .continue
  let some n ← Nat.fromExpr? y | return .continue
  return .done (if m == n then a else b)

/-- Unfold a segment's step and its cut test. -/
syntax "seg_eval" "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic
macro_rules
  | `(tactic| seg_eval [$ids,*]) => `(tactic|
      dsimp only [seg_mk, seg_zero, SegRel, $ids,*, finValLit, boolLit, boolAndLit, iteNatLit, Nat.reduceBEq, ↓reduceIte, Bool.false_eq_true])

/-- The cut test of a block a branch picks, distributed over the branch. -/
theorem ite_beq {α : Type} [BEq α] (c : Prop) [Decidable c] (a b n : α) :
    ((if c then a else b) == n) = (if c then a == n else b == n) := by
  split <;> rfl

/-- `0 < a` as a word is `a ≠ 0`: the scheduler may test a value's `ne` against zero with
`lt`, and a segment's two ends then agree only through this. -/
theorem evm_lt_zero_left (a : EvmRules.Word) : EvmRules.Evm.lt 0 a = EvmRules.Evm.ne a 0 := by
  unfold EvmRules.Evm.lt EvmRules.Evm.ne
  by_cases h : a = 0
  · subst h; decide
  · have hn : a.toNat ≠ 0 := fun e => h (BitVec.eq_of_toNat_eq (by simpa using e))
    have hu : (0#256).ult a = true := by
      simp only [BitVec.ult, BitVec.toNat_ofNat, decide_eq_true_eq]; omega
    simpa [hu] using h

/-- The initial state rebuilt field by field, as a program that writes none of it leaves it, is
the initial state: a cut point reached before either program writes the state relates it as one
state. -/
theorem state_initial_eta (call : Call) :
    ({ memory := Mem.initial, storage := (State.initial call).storage,
       transient := (State.initial call).transient, world := (State.initial call).world } : State) =
      State.initial call := rfl

/-- A cut test of a block a branch picks (`(if c then 15 else 14) == 1`) evaluates on both
branches, so a test that holds on neither is `false` before any case split. Splitting on it
first instead leaves leaves whose contradiction only the branch condition shows, and the case
splits multiply. -/
macro "seg_cut_test" : tactic => `(tactic|
  simp only [ite_beq, Nat.reduceBEq, BitVec.reduceEq, BitVec.reduceNe, ite_self, Bool.false_eq_true,
    evm_lt_zero_left, state_initial_eta,
    ↓reduceIte, Mem.load_store_of_disjoint, Mem.load_store_same, Mem.load_expand, Nat.reduceAdd,
    Nat.reduceLeDiff, true_or, or_true])

syntax "seg_norm" "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic
macro_rules
  | `(tactic| seg_norm [$ids,*]) =>
    `(tactic| repeat (first | sym_eval | seg_eval [$ids,*] | seg_cut_test | sym_cond))

/-- The equation of two words, configurations or results, by evaluation and `sym_exec`'s leaf
procedures. -/
macro "seg_word_eq" : tactic => `(tactic| (
  first
    | with_reducible rfl
    | ((try seg_cut_test); sym_norm; first
        | with_reducible rfl
        | (exfalso; bv_omega)
        | (exfalso; sym_omega)
        | (exfalso; sym_comm_contra)
        | sym_select
        | sym_agree)))

/-- What a relation lemma asks of the target configuration: the variables only the target
names, given by unification, then its configuration and each condition. -/
macro "seg_eq" : tactic => `(tactic| (
  repeat (apply Exists.intro)
  repeat' (apply And.intro)
  all_goals seg_word_eq))

/-- A leaf at two cut points, by one of the relation lemmas `mks` (each
`mk (words…) (state) (y') (h : y' = …) : ∃ Q ∈ rels, Q (…) y'`). -/
syntax "seg_cut" "[" ident,* "]" : tactic
macro_rules
  | `(tactic| seg_cut []) => `(tactic| fail "sym_seg: no relation relates the cut points")
  | `(tactic| seg_cut [$m]) => `(tactic| (refine $m ?_; seg_eq))
  | `(tactic| seg_cut [$m, $ms,*]) => `(tactic|
      first
        | (refine $m ?_; seg_eq)
        | seg_cut [$ms,*])

/-- One segment obligation, from configurations of variables: evaluate both segments, split
on the conditions they leave, and close each leaf. `unfolds` are the cut tests' definitions
and `mks` the relation lemmas. -/
syntax "sym_seg" "[" Lean.Parser.Tactic.simpLemma,* "]" "[" ident,* "]" : tactic
set_option hygiene false in
macro_rules
  | `(tactic| sym_seg [$us,*] [$ms,*]) => `(tactic| (
      obtain ⟨cd, hcd⟩ : ∃ cd, cd = calldataWord call := ⟨_, rfl⟩
      seg_norm [$us,*]
      repeat' (split_cond <;> seg_norm [$us,*])
      all_goals first
        | exact True.intro
        | (apply agree_of_eq; seg_eq)
        | seg_cut [$ms,*]
        | (exfalso; bv_omega)
        | (exfalso; sym_omega)
        | (exfalso; sym_comm_contra)
        | fail "sym_seg: the segments end differently on this path, or the procedure cannot tell"))

end SolarTV.Milestone.W1

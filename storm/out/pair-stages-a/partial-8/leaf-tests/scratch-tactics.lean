
open Lean Meta in
/-- A comparison of two numerals, decided. -/
def natLitCmp? (t x y : Expr) (f : Nat → Nat → Bool) : Simp.SimpM (Option Bool) := do
  unless t.isConstOf ``Nat do return none
  let some m ← Nat.fromExpr? x | return none
  let some n ← Nat.fromExpr? y | return none
  return some (f m n)

open Lean Meta Simp in
/-- A conditional on a comparison of numerals, as the stack-depth checks leave it once the height
is known: the branch the comparison picks, by `ite_cond_eq_true`/`ite_cond_eq_false` with the
comparison decided. A proof rather than a `dsimp` step, since the decision instance may still
name the unevaluated height (`Nat.decLt 1024 l.length`) after the condition was evaluated. -/
simproc_decl iteNatCmp (ite _ _ _) := fun e => do
  let_expr ite _ c _ _ _ := e | return .continue
  let r? ← match_expr c with
    | LT.lt t _ x y => natLitCmp? t x y (fun m n => decide (m < n))
    | LE.le t _ x y => natLitCmp? t x y (fun m n => decide (m ≤ n))
    | GT.gt t _ x y => natLitCmp? t x y (fun m n => decide (m > n))
    | GE.ge t _ x y => natLitCmp? t x y (fun m n => decide (m ≥ n))
    | _ => pure none
  let some r := r? | return .continue
  let args := e.getAppArgs
  let lvls := e.getAppFn.constLevels!
  if r then
    let h ← mkDecideProof c
    let hc := h
    let heq ← mkAppM ``eq_true #[hc]
    let pf := mkAppN (mkConst ``ite_cond_eq_true lvls) #[args[0]!, args[1]!, args[2]!, args[3]!, args[4]!, heq]
    return .done { expr := args[3]!, proof? := some pf }
  else
    let h ← mkDecideProof (mkNot c)
    let hc := h
    let heq ← mkAppM ``eq_false #[hc]
    let pf := mkAppN (mkConst ``ite_cond_eq_false lvls) #[args[0]!, args[1]!, args[2]!, args[3]!, args[4]!, heq]
    return .done { expr := args[4]!, proof? := some pf }

open Lean Elab Tactic Meta in
elab "show_ite1024" : tactic => withMainContext do
  let g ← instantiateMVars (← getMainTarget)
  let has1024 (x : Expr) : Bool := (x.find? (fun y => y.rawNatLit? == some 1024)).isSome
  match g.find? (fun e => e.isAppOfArity ``ite 5 && has1024 (e.getArg! 1)) with
  | some e => logInfo m!"ITE1024 cond: {repr (e.getArg! 1)} || inst: {e.getArg! 2}"
  | none => logInfo "ITE1024 none"


theorem evm_eq_comm2 (a b : EvmRules.Word) : EvmRules.Evm.eq a b = EvmRules.Evm.eq b a := by
  unfold EvmRules.Evm.eq
  rw [Bool.beq_comm]

theorem evm_gt_lt2 (a b : EvmRules.Word) : EvmRules.Evm.gt a b = EvmRules.Evm.lt b a := rfl

macro "seg_nat_cmp" : tactic => `(tactic|
  simp (config := { maxSteps := 20000000 }) only [iteNatCmp])


macro "seg_cut_test2" : tactic => `(tactic|
  simp only [ite_beq, Nat.reduceBEq, BitVec.reduceEq, BitVec.reduceNe, ite_self, Bool.false_eq_true,
    evm_lt_zero_left, state_initial_eta, Bool.or_true, Bool.or_false, Bool.and_true, Bool.and_false,
    ↓reduceIte, Mem.load_store_of_disjoint, Mem.load_store_same, Mem.load_expand, Nat.reduceAdd,
    Nat.reduceLeDiff, true_or, or_true, ite_or_ite_not, ite_not_or_ite, iteNatCmp])

syntax "seg_norm2" "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic
macro_rules
  | `(tactic| seg_norm2 [$ids,*]) =>
    `(tactic| repeat (first | sym_eval | seg_eval [$ids,*] | seg_cut_test2 | sym_cond))

macro "seg_word_eq2" : tactic => `(tactic| (
  first
    | with_reducible rfl
    | (simp only [evm_iszero_eq]; with_reducible rfl)
    | ((try seg_cut_test); sym_norm; first
        | with_reducible rfl
        | (simp only [evm_iszero_eq]; with_reducible rfl)
        | (simp only [evm_iszero_eq, evm_gt_lt2]; with_reducible rfl)
        | (simp only [evm_iszero_eq, evm_gt_lt2, evm_eq_comm2]; with_reducible rfl)
        | (exfalso; bv_omega)
        | (exfalso; sym_omega)
        | (exfalso; sym_comm_contra)
        | sym_select
        | sym_agree)))

macro "seg_eq2" : tactic => `(tactic| (
  repeat (apply Exists.intro)
  repeat' (apply And.intro)
  all_goals seg_word_eq2))

syntax "seg_cut2" "[" ident,* "]" : tactic
macro_rules
  | `(tactic| seg_cut2 []) => `(tactic| fail "sym_seg: no relation relates the cut points")
  | `(tactic| seg_cut2 [$m]) => `(tactic| (refine $m ?_; seg_eq2))
  | `(tactic| seg_cut2 [$m, $ms,*]) => `(tactic|
      first
        | (refine $m ?_; seg_eq2)
        | seg_cut2 [$ms,*])

syntax "sym_seg2" "[" Lean.Parser.Tactic.simpLemma,* "]" "[" ident,* "]" : tactic
set_option hygiene false in
macro_rules
  | `(tactic| sym_seg2 [$us,*] [$ms,*]) => `(tactic| (
      obtain ⟨cd, hcd⟩ : ∃ cd, cd = calldataWord call := ⟨_, rfl⟩
      seg_norm2 [$us,*]
      repeat' (split_cond <;> seg_norm2 [$us,*])
      all_goals first
        | exact True.intro
        | (apply agree_of_eq; seg_eq2)
        | seg_cut2 [$ms,*]
        | (exfalso; bv_omega)
        | (exfalso; sym_omega)
        | (exfalso; sym_comm_contra)
        | (exfalso; seg_case_contra)
        | (show_ite1024; fail "open")))


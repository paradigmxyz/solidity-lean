import SolarTV.Termination
import W1Proofs.Segment
import W1Proofs.Stage
import Contracts.CallSqrt.Inferred

/-!
# Math.sqrt's loop ends, under any caller

CallSqrt calls Uniswap v2-core's Math.sqrt from its two functions, so the Newton loop
(`while (x < z) { z = x; x = (y / x + x) / 2; }`) runs inside an internal call frame. Its ranking
certificate is generated (`Inferred.lean`, from solar-verify's measure `z` by
`inferred_callee.py`) and checked here through the generic checker
(`SolarTV.CutPoint.reaches_of_start`):

* `seg0`, `seg1`, `seg9`: sqrt's segments, from its entry and from its header entered from
  either predecessor, under any caller's return record and any stack: each ends in a revert,
  back in the caller, or at the header with a lower `z` (the guard `x < z` and the update
  `z = x`). None is stuck: the compiler's `assume`s are discharged (`shr1_lt_max`).
* `sqrt_reaches`: **sqrt's total contract**: from its entry, under any caller, it returns to
  the caller or reverts.
* `stage0_ends`: every call of CallSqrt ends on solar's first lowered MIR, whatever its
  calldata: the entry's checks and dispatch, f or g, sqrt by its contract, then the caller's
  rest.
-/

namespace SolarTV.Milestone.CallSqrt

open Machine SolarTV.Export.CallSqrt SolarTV.Milestone.W1
open SolarTV.CutPoint (seg SegReaches)
open Inferred (cut Inv Back rank)

theorem cut_enter (rs : List MIR.Lowered.Return) (f p b : Nat) (env : MIR.Lowered.Env) (s : State) :
    cut (rs, .enter f p b, env, s) = (f == 2 && (p == 1 || p == 9)) := rfl

theorem cut_resume (rs : List MIR.Lowered.Return) (f b : Nat) (is : List MIR.Lowered.Inst)
    (t : MIR.Lowered.Terminator) (env : MIR.Lowered.Env) (s : State) :
    cut (rs, .resume f b is t, env, s) = true := rfl

/-- The cut test of a block a branch picks, distributed over the branch. -/
theorem ite_beq' {α : Type} [BEq α] (c : Prop) [Decidable c] (a b n : α) :
    ((if c then a else b) == n) = (if c then a == n else b == n) := by
  split <;> rfl

/-- A cut test of a block a branch picks evaluates on both branches before any case split. -/
macro "sq_cut_test" : tactic => `(tactic|
  simp only [ite_beq', Nat.reduceBEq, ite_self, Bool.false_eq_true, Bool.true_and, Bool.false_and,
    ↓reduceIte, true_or, or_true])

set_option hygiene false in
/-- The case just split, rewritten into the branch that tests it. -/
macro "sq_case" : tactic => `(tactic| simp only [hc, ↓reduceIte, Nat.reduceBEq, Bool.false_eq_true,
  Bool.true_and, Bool.false_and, Bool.or_false, Bool.false_or])

/-- `seg_norm` with the cut test evaluated first and the last case rewritten. -/
syntax "sq_norm" "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic
macro_rules
  | `(tactic| sq_norm [$ids,*]) =>
    `(tactic| repeat (first | sym_eval | seg_eval [$ids,*] | sq_cut_test | sym_cond | sq_case))

/-- A caller's return record whose call binds one result. -/
def ret (fn block d : Nat) (rest : List MIR.Lowered.Inst) (term : MIR.Lowered.Terminator)
    (renv : MIR.Lowered.Env) (publish : Option EvmRules.Word) : MIR.Lowered.Return :=
  ⟨fn, block, some d, rest, term, renv, [], publish⟩

theorem lt_of_evm_lt {a b : EvmRules.Word} (h : ¬EvmRules.Evm.lt a b = 0) : a.toNat < b.toNat := by
  unfold EvmRules.Evm.lt at h
  cases hu : a.ult b
  · simp [hu] at h
  · simpa [BitVec.ult, decide_eq_true_eq] using hu

/-- sqrt's entry assumes `y >> 1` is below the largest word, which holds of every word. -/
theorem shr1_lt_max (x : EvmRules.Word) :
    ¬EvmRules.Evm.lt (EvmRules.Evm.shr 1 x)
      115792089237316195423570985008687907853269984665640564039457584007913129639935 = 0 := by
  have hs : (EvmRules.Evm.shr 1 x).toNat < 2 ^ 255 := by
    simp only [EvmRules.Evm.shr]
    rw [show BitVec.ult (1 : EvmRules.Word) 256 = true by decide]
    simp only [Bool.cond_true, BitVec.ushiftRight_eq', BitVec.toNat_ushiftRight,
      Nat.shiftRight_eq_div_pow]
    rw [show (1 : EvmRules.Word).toNat = 1 from rfl]
    have := x.isLt
    omega
  have hu : (EvmRules.Evm.shr 1 x).ult
      115792089237316195423570985008687907853269984665640564039457584007913129639935 = true := by
    simp only [BitVec.ult, decide_eq_true_eq]
    rw [show (115792089237316195423570985008687907853269984665640564039457584007913129639935 :
      EvmRules.Word).toNat = 2 ^ 256 - 1 from rfl]
    omega
  unfold EvmRules.Evm.lt
  rw [hu]
  decide

/-- The same, as the entry's branch reads it. -/
theorem shr1_lt_max' (x : EvmRules.Word) :
    EvmRules.Evm.shr 1 x < 115792089237316195423570985008687907853269984665640564039457584007913129639935 := by
  have h := shr1_lt_max x
  unfold EvmRules.Evm.lt at h
  cases hu : (EvmRules.Evm.shr 1 x).ult
      115792089237316195423570985008687907853269984665640564039457584007913129639935
  · rw [hu] at h; exact absurd rfl h
  · exact BitVec.ult_iff_lt.mp hu

/-- The leaves of sqrt's segments: a revert, the caller resumed, the header again with a lower
rank, or a contradiction of the cases. -/
macro "sq_leaf" : tactic => `(tactic| first
  | trivial
  | exact Or.inr ⟨_, _, rfl⟩
  | (refine Or.inl ⟨⟨_, _, _, rfl, Or.inl rfl⟩, trivial⟩)
  | (refine Or.inl ⟨⟨_, _, _, rfl, Or.inr rfl⟩, ?_⟩
     simp only [rank, MIR.Lowered.Env.set, ↓reduceIte, Nat.reduceEqDiff]
     exact lt_of_evm_lt ‹_›)
  | exact absurd ‹(0 : EvmRules.Word) = 1› (by decide)
  | exact absurd ‹EvmRules.Evm.lt (EvmRules.Evm.shr 1 _) _ = 0› (shr1_lt_max _)
  | (exfalso; bv_omega))

set_option backward.dsimp.instances true in
set_option maxHeartbeats 4000000 in
theorem seg9 (o : Oracle) (call : Call) (fn block d : Nat) (rest : List MIR.Lowered.Inst)
    (term : MIR.Lowered.Terminator) (renv : MIR.Lowered.Env) (publish : Option EvmRules.Word)
    (stack : List MIR.Lowered.Return) (env : MIR.Lowered.Env) (s : State) :
    SegReaches (Inv (ret fn block d rest term renv publish) stack)
      (Back (ret fn block d rest term renv publish) stack) (fun _ => True)
      (fun y => rank y < rank (ret fn block d rest term renv publish :: stack, .enter 2 9 4, env, s))
      (seg (MIR.Lowered.moduleBlock o call stage0) cut 20
        (ret fn block d rest term renv publish :: stack, .enter 2 9 4, env, s)) := by
  unfold ret
  sq_norm [SegReaches, cut_enter, cut_resume]
  repeat' (split_cond <;> sq_norm [SegReaches, cut_enter, cut_resume])
  all_goals sq_leaf

set_option backward.dsimp.instances true in
set_option maxHeartbeats 4000000 in
theorem seg1 (o : Oracle) (call : Call) (fn block d : Nat) (rest : List MIR.Lowered.Inst)
    (term : MIR.Lowered.Terminator) (renv : MIR.Lowered.Env) (publish : Option EvmRules.Word)
    (stack : List MIR.Lowered.Return) (env : MIR.Lowered.Env) (s : State) :
    SegReaches (Inv (ret fn block d rest term renv publish) stack)
      (Back (ret fn block d rest term renv publish) stack) (fun _ => True)
      (fun y => rank y < rank (ret fn block d rest term renv publish :: stack, .enter 2 1 4, env, s))
      (seg (MIR.Lowered.moduleBlock o call stage0) cut 20
        (ret fn block d rest term renv publish :: stack, .enter 2 1 4, env, s)) := by
  unfold ret
  sq_norm [SegReaches, cut_enter, cut_resume]
  repeat' (split_cond <;> sq_norm [SegReaches, cut_enter, cut_resume])
  all_goals sq_leaf

set_option backward.dsimp.instances true in
set_option maxHeartbeats 4000000 in
theorem seg0 (o : Oracle) (call : Call) (fn block d : Nat) (rest : List MIR.Lowered.Inst)
    (term : MIR.Lowered.Terminator) (renv : MIR.Lowered.Env) (publish : Option EvmRules.Word)
    (stack : List MIR.Lowered.Return) (env : MIR.Lowered.Env) (s : State) :
    SegReaches (Inv (ret fn block d rest term renv publish) stack)
      (Back (ret fn block d rest term renv publish) stack) (fun _ => True)
      (fun _ => True)
      (seg (MIR.Lowered.moduleBlock o call stage0) cut 20
        (ret fn block d rest term renv publish :: stack, .enter 2 0 0, env, s)) := by
  unfold ret
  sq_norm [SegReaches, cut_enter, cut_resume]
  repeat' (split_cond <;> sq_norm [SegReaches, cut_enter, cut_resume])
  all_goals sq_leaf


/-! ## The whole call -/

/-- What f runs after its call of sqrt returns. -/
def restF : List MIR.Lowered.Inst := [.pure 5 .add [.value 2, .const 1], .pure 6 .eq [.value 5, .const 0]]
def termF : MIR.Lowered.Terminator := .branch (.value 6) 1 2
/-- What g runs after its call of sqrt returns. -/
def restG : List MIR.Lowered.Inst := [.effect none .mstore [.const 0, .value 4]]
def termG : MIR.Lowered.Terminator := .ret (.const 0) (.const 32)

/-- sqrt's header under f's or g's call. -/
def TopInv (x : MIR.Lowered.Frame) : Prop :=
  ∃ renv, Inv (ret 0 0 2 restF termF renv none) [] x ∨ Inv (ret 1 0 4 restG termG renv none) [] x

/-- f or g resumed after sqrt returned. -/
def TopBack (x : MIR.Lowered.Frame) : Prop :=
  ∃ env s, x = ([], .resume 0 0 restF termF, env, s) ∨ x = ([], .resume 1 0 restG termG, env, s)

/-- The first configuration of a call. -/
def start (call : Call) : MIR.Lowered.Frame :=
  ([], .enter stage0.entry 0 0, fun _ => 0, MIR.Lowered.Module.startState stage0 (State.initial call))

macro "top_leaf" : tactic => `(tactic| first
  | trivial
  | exact Or.inl ⟨⟨_, Or.inl ⟨_, _, _, rfl, Or.inl rfl⟩⟩, trivial⟩
  | exact Or.inl ⟨⟨_, Or.inr ⟨_, _, _, rfl, Or.inl rfl⟩⟩, trivial⟩
  | exact Or.inl ⟨_, Or.inl ⟨_, _, _, rfl, Or.inl rfl⟩⟩
  | exact Or.inl ⟨_, Or.inr ⟨_, _, _, rfl, Or.inl rfl⟩⟩
  | exact Or.inr ⟨_, _, Or.inl rfl⟩
  | exact Or.inr ⟨_, _, Or.inr rfl⟩
  | exact absurd (shr1_lt_max' _) ‹¬EvmRules.Evm.shr 1 _ < _›
  | exact absurd ‹(0 : EvmRules.Word) = 1› (by decide)
  | exact absurd ‹EvmRules.Evm.lt (EvmRules.Evm.shr 1 _) _ = 0› (shr1_lt_max _)
  | (exfalso; bv_omega))

set_option backward.dsimp.instances true in
set_option maxHeartbeats 4000000 in
/-- From a call's start: the entry's checks and selector, f or g, into sqrt, to its header or
(for `y <= 3`) back to the caller. -/
theorem segTop (o : Oracle) (call : Call) :
    SegReaches TopInv TopBack (fun _ => True) (fun _ => True)
      (seg (MIR.Lowered.moduleBlock o call stage0) cut 40 (start call)) := by
  unfold start
  obtain ⟨cd, hcd⟩ : ∃ cd, cd = calldataWord call := ⟨_, rfl⟩
  sq_norm [SegReaches, cut_enter, cut_resume]
  repeat' (split_cond <;> sq_norm [SegReaches, cut_enter, cut_resume])
  all_goals top_leaf

set_option backward.dsimp.instances true in
set_option maxHeartbeats 4000000 in
theorem segF (o : Oracle) (call : Call) (env : MIR.Lowered.Env) (s : State) :
    CutPoint.SegEnds (fun _ => False) (fun _ => True) (fun _ => True)
      (seg (MIR.Lowered.moduleBlock o call stage0) cut 10 ([], .resume 0 0 restF termF, env, s)) := by
  unfold restF termF
  sq_norm [CutPoint.SegEnds, cut_enter, cut_resume]
  repeat' (split_cond <;> sq_norm [CutPoint.SegEnds, cut_enter, cut_resume])
  all_goals trivial

set_option backward.dsimp.instances true in
set_option maxHeartbeats 4000000 in
theorem segG (o : Oracle) (call : Call) (env : MIR.Lowered.Env) (s : State) :
    CutPoint.SegEnds (fun _ => False) (fun _ => True) (fun _ => True)
      (seg (MIR.Lowered.moduleBlock o call stage0) cut 10 ([], .resume 1 0 restG termG, env, s)) := by
  unfold restG termG
  sq_norm [CutPoint.SegEnds, cut_enter, cut_resume]
  repeat' (split_cond <;> sq_norm [CutPoint.SegEnds, cut_enter, cut_resume])
  all_goals trivial

/-- sqrt's segments from its header, under any caller. -/
theorem segH (o : Oracle) (call : Call) (fn block d : Nat) (rest : List MIR.Lowered.Inst)
    (term : MIR.Lowered.Terminator) (renv : MIR.Lowered.Env) (publish : Option EvmRules.Word)
    (stack : List MIR.Lowered.Return) :
    ∀ x, Inv (ret fn block d rest term renv publish) stack x →
      ∃ k, SegReaches (Inv (ret fn block d rest term renv publish) stack)
        (Back (ret fn block d rest term renv publish) stack) (fun _ => True)
        (fun y => rank y < rank x) (seg (MIR.Lowered.moduleBlock o call stage0) cut k x) := by
  rintro x ⟨p, env, s, rfl, rfl | rfl⟩
  · exact ⟨20, seg1 o call fn block d rest term renv publish stack env s⟩
  · exact ⟨20, seg9 o call fn block d rest term renv publish stack env s⟩

/-- **Math.sqrt's total contract, under any caller**: from its entry, with any argument and any
caller's return record, it returns to the caller or reverts, after finitely many steps; the
rank is the measure `z` solar-verify infers, read off the header's phi of `z`. -/
theorem sqrt_reaches (o : Oracle) (call : Call) (fn block d : Nat) (rest : List MIR.Lowered.Inst)
    (term : MIR.Lowered.Terminator) (renv : MIR.Lowered.Env) (publish : Option EvmRules.Word)
    (stack : List MIR.Lowered.Return) (env : MIR.Lowered.Env) (s : State) :
    (∃ n r, CutPoint.run (MIR.Lowered.moduleBlock o call stage0) n
        (ret fn block d rest term renv publish :: stack, .enter 2 0 0, env, s) = some r) ∨
      ∃ j y, CutPoint.steps (MIR.Lowered.moduleBlock o call stage0) j
        (ret fn block d rest term renv publish :: stack, .enter 2 0 0, env, s) = some (.inr y) ∧
        Back (ret fn block d rest term renv publish) stack y := by
  rcases CutPoint.reaches_of_start (Post := fun _ => True) rank
      ⟨20, seg0 o call fn block d rest term renv publish stack env s⟩
      (segH o call fn block d rest term renv publish stack) with ⟨n, r, h, -⟩ | h
  · exact Or.inl ⟨n, r, h⟩
  · exact Or.inr h

theorem back_ends (o : Oracle) (call : Call) (y : MIR.Lowered.Frame) (hy : TopBack y) :
    ∃ n r, CutPoint.run (MIR.Lowered.moduleBlock o call stage0) n y = some r := by
  obtain ⟨env, s, rfl | rfl⟩ := hy
  · obtain ⟨n, r, h, -⟩ := CutPoint.ends_of_start (Inv := fun _ => False) (Post := fun _ => True)
      (fun _ => 0) ⟨10, segF o call env s⟩ (fun _ h => h.elim)
    exact ⟨n, r, h⟩
  · obtain ⟨n, r, h, -⟩ := CutPoint.ends_of_start (Inv := fun _ => False) (Post := fun _ => True)
      (fun _ => 0) ⟨10, segG o call env s⟩ (fun _ h => h.elim)
    exact ⟨n, r, h⟩

/-- **Every call of CallSqrt ends on solar's first lowered MIR**, whatever its calldata: the
entry checks and dispatches, f and g call Math.sqrt, whose loop ends by its ranking certificate,
and the caller finishes. -/
theorem stage0_ends (o : Oracle) (call : Call) : ∃ r, MIR.Lowered.moduleLayer.Ends o stage0 call r := by
  have top := CutPoint.reaches_of_start (Inv := TopInv) (Q := TopBack) (Post := fun _ => True) rank
    ⟨40, segTop o call⟩ (by
      rintro x ⟨renv, hx | hx⟩
      · obtain ⟨k, hk⟩ := segH o call 0 0 2 restF termF renv none [] x hx
        exact ⟨k, hk.mono (fun y h => ⟨renv, Or.inl h⟩)
          (fun y ⟨env, s, e⟩ => ⟨env, s, Or.inl e⟩) (fun _ h => h)⟩
      · obtain ⟨k, hk⟩ := segH o call 1 0 4 restG termG renv none [] x hx
        exact ⟨k, hk.mono (fun y h => ⟨renv, Or.inr h⟩)
          (fun y ⟨env, s, e⟩ => ⟨env, s, Or.inr e⟩) (fun _ h => h)⟩)
  have hrun : ∃ n r, CutPoint.run (MIR.Lowered.moduleBlock o call stage0) n (start call) = some r := by
    rcases top with ⟨n, r, h, -⟩ | ⟨j, y, hy, qy⟩
    · exact ⟨n, r, h⟩
    · obtain ⟨n, r, h⟩ := back_ends o call y qy
      exact ⟨j + n, r, by rw [CutPoint.run_add j n _ y hy]; exact h⟩
  obtain ⟨n, r, h⟩ := hrun
  exact ⟨r, n, by
    change Machine.iterate _ n _ = some r
    rw [CutPoint.iterate_eq]
    exact h⟩

/-- info: 'SolarTV.Milestone.CallSqrt.stage0_ends' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms stage0_ends

end SolarTV.Milestone.CallSqrt

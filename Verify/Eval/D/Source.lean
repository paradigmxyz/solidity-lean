import Verify.Eval.D.Bridge
import Verify.Eval.Common.Measure
import Verify.W1
import Verify.W4

/-!
# Lane D, target 1: source-level VCs, `sc_vcgen` against `vcgen` on the same statements

Each statement below is the repository's own, unchanged: `Verify.W1.vcs` (`f(x)` returns `x + 1`
or panics) and the inner goal of `Verify.W4.vcsAt` (`set(v)` from any storage `σ`, a write with a
frame). `*_old` is the repository's proof text (`sc_vcgen`); `*_new` keeps `sc_vcgen`'s scope
reduction (the ABI cases, which are not VC generation) and replaces its weakest-precondition
`simp only` cascade and `sc_close` by the bridge (`vc_of_triple`: Loom's `wp` is `Std.WP`'s) and
`vcgen … with finish` (the SymM driver of Lean 4.35, residual VCs closed by `grind`);
`*_mvcgen` does the same with the deprecated `mvcgen` (`Std.Do`) and `grind`.
-/

namespace SolidCore.Verify.Eval.D.Source

open Lean SolidCore.Verify SolidCore.Refinement SolidCore.Refinement.Abi
open scoped Std.WP

set_option experimental.vcgen true
set_option Elab.async false
set_option grind.warning false
set_option linter.deprecated.syntax false

/-- The empty storage reads 0 (`sc_vcgen` unfolds `slotValue` with `simp` instead). -/
@[grind =] theorem slotValue_nil (k : Nat) : slotValue [] k = 0 := rfl

/-- `sc_vcgen`'s scope reduction, then the Loom goal as a `Std.WP` triple and `vcgen`. -/
syntax "sd_vcgen" " [" term,* "]" : tactic

macro_rules
  | `(tactic| sd_vcgen [$ts,*]) => do
    let ts' : Array (TSyntax `Lean.Parser.Tactic.simpLemma) ←
      ts.getElems.mapM fun t => `(Lean.Parser.Tactic.simpLemma| $t:term)
    `(tactic| set_option linter.unusedSimpArgs false in (
      try simp only [$ts',*]
      refine vcs_of_fullScope (by simp [$ts',*]) ?_
      intro fn hfn call args hcall hw hlen hargs hinit hpre
      simp only [$ts',*, List.mem_cons, List.not_mem_nil, or_false] at hfn
      try casesm* _ ∨ _
      all_goals subst fn
      all_goals rcases args with _ | ⟨a1, _ | ⟨a2, _ | ⟨a3, _ | ⟨a4, _⟩⟩⟩⟩
      all_goals try (simp at hlen; done)
      all_goals try simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq, imp_false, not_false_eq_true, implies_true, and_true, IsEmpty.forall_iff] at hargs
      all_goals simp only [$ts',*, hw, List.getD_cons_zero, List.getD_cons_succ]
      all_goals subst hcall
      all_goals refine loom_wp_of_triple_pt ?_
      all_goals vcgen with finish))

/-- The same with the deprecated `mvcgen` on `Std.Do`, residual VCs closed by `grind`. -/
syntax "sm_vcgen" " [" term,* "]" : tactic

macro_rules
  | `(tactic| sm_vcgen [$ts,*]) => do
    let ts' : Array (TSyntax `Lean.Parser.Tactic.simpLemma) ←
      ts.getElems.mapM fun t => `(Lean.Parser.Tactic.simpLemma| $t:term)
    `(tactic| set_option linter.unusedSimpArgs false in (
      try simp only [$ts',*]
      refine vcs_of_fullScope (by simp [$ts',*]) ?_
      intro fn hfn call args hcall hw hlen hargs hinit hpre
      simp only [$ts',*, List.mem_cons, List.not_mem_nil, or_false] at hfn
      try casesm* _ ∨ _
      all_goals subst fn
      all_goals rcases args with _ | ⟨a1, _ | ⟨a2, _ | ⟨a3, _ | ⟨a4, _⟩⟩⟩⟩
      all_goals try (simp at hlen; done)
      all_goals try simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq, imp_false, not_false_eq_true, implies_true, and_true, IsEmpty.forall_iff] at hargs
      all_goals simp only [$ts',*, hw, List.getD_cons_zero, List.getD_cons_succ]
      all_goals subst hcall
      all_goals refine loom_wp_of_stdDo_triple_pt ?_
      all_goals mvcgen
      all_goals grind))

/-! ## w1 -/

#timed theorem w1_old : ∀ call, W1.scope call → W1.pre call → vc W1.model (argWords 1) W1.post call := by
  sc_vcgen [W1.scope, Corpus.W1.fns, W1.model, W1.post]

#timed theorem w1_new : ∀ call, W1.scope call → W1.pre call → vc W1.model (argWords 1) W1.post call := by
  sd_vcgen [W1.scope, Corpus.W1.fns, W1.model, W1.post]

#timed theorem w1_mvcgen : ∀ call, W1.scope call → W1.pre call → vc W1.model (argWords 1) W1.post call := by
  sm_vcgen [W1.scope, Corpus.W1.fns, W1.model, W1.post]

#print axioms w1_mvcgen
#proof_stats w1_mvcgen
#kernel_recheck w1_mvcgen
#print axioms w1_old
#print axioms w1_new
#proof_stats w1_old
#proof_stats w1_new
#kernel_recheck w1_old
#kernel_recheck w1_new

/-! ## w4, from any storage -/

#timed theorem w4_old (σ : List (Nat × Nat)) :
    ∀ call, fullScope Corpus.W4.fns σ call → W4.pre call → vc W4.model (argWords 1) W4.postAt call := by
  sc_vcgen [Corpus.W4.fns, W4.model, W4.postAt]

#timed theorem w4_new (σ : List (Nat × Nat)) :
    ∀ call, fullScope Corpus.W4.fns σ call → W4.pre call → vc W4.model (argWords 1) W4.postAt call := by
  sd_vcgen [Corpus.W4.fns, W4.model, W4.postAt]

#timed theorem w4_mvcgen (σ : List (Nat × Nat)) :
    ∀ call, fullScope Corpus.W4.fns σ call → W4.pre call → vc W4.model (argWords 1) W4.postAt call := by
  sm_vcgen [Corpus.W4.fns, W4.model, W4.postAt]

#print axioms w4_mvcgen
#proof_stats w4_mvcgen
#kernel_recheck w4_mvcgen
#print axioms w4_old
#print axioms w4_new
#proof_stats w4_old
#proof_stats w4_new
#kernel_recheck w4_old
#kernel_recheck w4_new

end SolidCore.Verify.Eval.D.Source

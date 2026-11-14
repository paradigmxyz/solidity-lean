import Contracts.UniswapV2.PairSpec.Stages

/-!
# UniswapV2Pair: the composition wrapper

`published_of_stages` proves the published `Statement` from the binding, the checked source and
the nine stage theorems (Stages.lean), by `OpenFunctional.of_parts` alone. Every input is a named
hypothesis of the theorem: nothing is assumed, and the theorem says exactly what is still owed.
When the lanes' theorems land, `published := published_of_stages bound contract_ok ...` is the
published theorem, checked against `Statement` by the driver (tools/certify/check_final.lean).
-/

namespace SolidCore.Spec.UniswapV2.PairSpec

open SolarTV SolidCore.Refinement SolidCore.Refinement.Shapes SolidCore.Spec.UniswapV2.PairSpec.Stages

/-- A valid call exists: `sync()` from the empty storage. -/
theorem inhabited : ∃ call, Valid call :=
  ⟨_, Or.inr (Or.inr ⟨[], rfl⟩)⟩

/-- **The composition**: the statement from the binding, the checked source and the stages. -/
theorem published_of_stages (hbound : Bound)
    (hc : ∃ c, SolidCore.Verify.VC.UniswapV2Pair.contract? = .ok c)
    (heq : ∀ c, SolidCore.Verify.VC.UniswapV2Pair.contract? = .ok c →
      EquivSwap c ∧ EquivSkim c ∧ EquivSync c)
    (hterm : ∀ c, SolidCore.Verify.VC.UniswapV2Pair.contract? = .ok c →
      TermSwap c ∧ TermSkim c ∧ TermSync c)
    (hmeets : ∀ c, SolidCore.Verify.VC.UniswapV2Pair.contract? = .ok c →
      MeetsSwap c ∧ MeetsSkim c ∧ MeetsSync c) :
    Statement := by
  refine ⟨hbound, fun hk => ?_⟩
  obtain ⟨c, hc⟩ := hc
  obtain ⟨e1, e2, e3⟩ := heq c hc
  obtain ⟨t1, t2, t3⟩ := hterm c hc
  obtain ⟨m1, m2, m3⟩ := hmeets c hc
  refine ⟨c, hc, OpenFunctional.of_parts inhabited (e1.or (e2.or e3)) (t1.or (t2.or t3)) ?_⟩
  exact fun W hW => (m1.or (m2.or m3)) hk W hW

/-- info: 'SolidCore.Spec.UniswapV2.PairSpec.published_of_stages' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms published_of_stages

/-- **What the statement gives of the bytes**: in every admitted environment, every result of the
exact bytecode on a valid call, at any gas below `2 ^ 256`, is allowed and meets the exported
specification (for some admitted world), or changes nothing, or is explained only by a world
with a reentrant state change. -/
theorem bytecode_of_statement {c0 : SolidCore.Solidity.TypeCheck.CheckedContract}
    (hc0 : SolidCore.Verify.VC.UniswapV2Pair.contract? = .ok c0) (h : Statement) (hk : HashScope) (env : TargetEnv) (he : EnvOk env)
    (gas : Nat) (hg : gas < 2 ^ 256) (call : Call) (hv : Valid call) (obs : Observable)
    (hrun : Target.runWithIn env gas code call = some obs) :
    (∃ W, Admit W ∧ Allowed W call obs ∧ Post W call obs) ∨ Inert call obs ∨
      Unadmitted SolidCore.Verify.VC.UniswapV2Pair.fuel c0 Wide Admit call obs := by
  obtain ⟨c, hc, hf⟩ := h.2 hk
  obtain rfl : c = c0 := Except.ok.inj (hc.symm.trans hc0)
  exact hf.bytecode_any env he gas hg call hv obs hrun

end SolidCore.Spec.UniswapV2.PairSpec


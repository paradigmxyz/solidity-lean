import Verify.Shapes
import Verify.Spec.Contract

/-!
# A postcondition read off solar-verify's exported spec

`bundlePost b ctxOf step` is the meaning of an exported spec bundle `b`
(`solar-verify --emit-lean-spec`, `SolidCore.Spec.Bundle`) as a postcondition of one call: for every
function spec of the bundle and every pre-state meeting its precondition on the call
(`SolidCore.Spec.Pre`), the observable meets its postcondition (`SolidCore.Spec.Post`). The certify
driver states a published `Shapes.Certified` with this postcondition over the bundle it exports in
the same run, so the specification the statement speaks of is solar-verify's, bound by the kernel's
type check rather than restated by hand.

`meets_of_bundle` turns `SolidCore.Spec.Holds` of the source on a scope that covers the valid
calls into `Shapes.Meets` of `bundlePost` (the source is deterministic, so the observable `Holds`
names is the one every run gives).
-/

namespace SolidCore.Refinement.Shapes

open SolarTV SolidCore.Refinement SolidCore.Refinement.Final

/-- solar-verify's exported spec `b` as a postcondition of one call. -/
def bundlePost (b : SolidCore.Spec.Bundle) (ctxOf : Call → SolidCore.Spec.Ctx)
    (step : SolidCore.Spec.GhostStep) (call : Call) (obs : Observable) : Prop :=
  ∀ fs ∈ b.spec.specs, ∀ (args : List Int) (pre : SolidCore.Spec.State),
    SolidCore.Spec.Pre b fs (ctxOf call) pre call args →
      SolidCore.Spec.Post b fs (ctxOf call) pre (step call pre.ghost) obs args

/-- `Holds` of the exported spec on a scope covering the valid calls is `Meets` of `bundlePost`. -/
theorem meets_of_bundle {S : Sem} {p : S.Prog} {Valid scope : Call → Prop}
    {b : SolidCore.Spec.Bundle} {ctxOf : Call → SolidCore.Spec.Ctx} {step : SolidCore.Spec.GhostStep}
    (hv : ∀ call, Valid call → scope call) (h : SolidCore.Spec.Holds S p scope b ctxOf step) :
    Meets S p Valid (bundlePost b ctxOf step) := by
  intro call hc obs hrun fs hfs args pre hpre
  obtain ⟨obs', h1, h2⟩ := h fs hfs call (hv call hc) args pre hpre
  rw [hrun] at h1
  cases h1
  exact h2

/-- info: 'SolidCore.Refinement.Shapes.meets_of_bundle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms meets_of_bundle

end SolidCore.Refinement.Shapes

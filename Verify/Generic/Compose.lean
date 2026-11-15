import Verify.Generic.Certificate
import Verify.ShapeSpecExport

/-!
# The certificate's fields from the generic stages

`translation_of_compiled` carries `Shapes.Compiled` (what `Shapes.compiled_of` and `compiled0XL`
give: the generic source stage, solar-tv's backend stages and an assembly checker) into the default
context's `TranslationAt`; `specProof_of_holds` reads `SpecProof` off solar-verify's exported spec.
Separate from Certificate.lean because its imports (the generic shape's totality results) clash
with some contracts' generated stage modules.
-/

namespace SolidCore.Verify.Generic

open SolidCore.Refinement SolidCore.Refinement.Shapes SolidCore.Solidity

/-- `Shapes.Compiled` (the default context's translation) is `TranslationAt` the default context. -/
theorem translation_of_compiled {fuel : Nat} {c : TypeCheck.CheckedContract} {code : ByteArray}
    {Valid : Call → Prop} {G : Call → Nat} (h : Compiled (solidCore fuel) c code Valid G) :
    TranslationAt (solidCoreFrom Context.default.caller fuel) c Context.default code Valid G where
  inhabited := h.inhabited
  equiv := by
    intro gas hg call hc obs hrun
    rw [runAt_default] at hrun
    exact (h.equiv gas hg call hc obs hrun).imp id And.left
  terminates := h.terminates
  resources := fun call hc => by
    obtain ⟨hG, hr⟩ := h.resources call hc
    exact ⟨hG, fun gas h1 h2 => by rw [runAt_default]; exact hr gas h1 h2⟩

/-- **solar-verify's exported specification**: `Holds` of the source on a scope covering the
valid calls is the proof of `bundleAllowed` and `bundlePost`. -/
theorem specProof_of_holds {S : Sem} {p : S.Prog} {Valid scope : Call → Prop}
    {b : SolidCore.Spec.Bundle} {ctxOf : Call → SolidCore.Spec.Ctx}
    {step : SolidCore.Spec.GhostStep} (hv : ∀ call, Valid call → scope call)
    (hh : SolidCore.Spec.Holds S p scope b ctxOf step) :
    SpecProof S p Valid (bundleAllowed b ctxOf) (bundlePost b ctxOf step) :=
  ⟨allowed_of_holds hv hh, meets_of_bundle hv hh⟩

/-- info: 'SolidCore.Verify.Generic.translation_of_compiled' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms translation_of_compiled

end SolidCore.Verify.Generic

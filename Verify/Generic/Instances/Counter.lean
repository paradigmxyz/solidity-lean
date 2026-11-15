import Verify.Generic.Certificate
import Contracts.Counter.ShapeExport
import counter.Final

/-!
# Counter as an instance of the generic expected theorem

Counter's existing published statement (`Contracts.Counter.ShapeExport.published`: the four
obligations with solar-verify's exported spec, and its non-vacuity witnesses) restated as
`Generic.Expected src spec bytes`, with no Counter-specific statement:

* `src`: solc's AST of `Certified/counter/counter.sol` (`Source.Counter.importedSourceUnit`), the
  contract `Counter`, fuel 4096;
* `spec`: covered contexts: the default frame (caller `0x2000`) only; entrypoints: `inc(uint256)`
  and `get()`, each with a valid call in that context; valid calls `cspec.Calls`; allowed statuses
  `ShapeSpec.allowed`; postcondition solar-verify's exported `bundlePost`; gas bound 1,281,806; no
  assumptions (unconditional tier, single-caller coverage);
* `bytes`: the runtime bytes the certify driver bound (`Certified.counter.Final.runtimeBytes`),
  checked equal to the exported code by the kernel (`Certified.counter.Final.bound`).
-/

namespace SolidCore.Verify.Generic.Instances.Counter

open SolidCore.Refinement SolidCore.Refinement.Shapes SolidCore.Refinement.Final
open SolidCore.Refinement.Solar.Counter SolidCore.Refinement.Solar.Counter.ShapeSpec
open SolidCore.Refinement.Solar.Counter.Final

/-- The entrypoints of a contract specification: each function and its calls. -/
def entriesOf {St : Type} (cs : ContractSpec St) : List (String × (Context → Call → Prop)) :=
  cs.fns.map fun f => (f.name, fun _ call => ∃ args v σ, call = f.call args v σ)

def src : Source :=
  ⟨SolidCore.Refinement.Source.Counter.importedSourceUnit, "Counter",
    SolidCore.Refinement.Solar.Counter.fuel⟩

def spec : Spec where
  Contexts ctx := ctx = Context.default
  entries := entriesOf cspec
  Valid _ := cspec.Calls
  Allowed _ := allowed
  Post _ := Shapes.bundlePost Headline.spec Headline.ctxOf Headline.step
  gas _ := gasBound
  assumptions := []

def bytes : List Nat := Certified.counter.Final.runtimeBytes

theorem checked_eq : src.checked = contract? := rfl

theorem covered : spec.Covered := by
  refine ⟨⟨_, rfl⟩, by rintro _ rfl; exact Context.default_ok, ?_, ?_, ?_⟩
  · rintro _ rfl e he
    simp only [spec, entriesOf, cspec, SolidCore.Refinement.Solar.Counter.Final.spec,
      List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl
    · exact ⟨_, ⟨incSpec, by simp [cspec, SolidCore.Refinement.Solar.Counter.Final.spec], [1],
        .cons (by decide) .nil, 0, by decide, [], rfl⟩, [1], 0, [], rfl⟩
    · exact ⟨_, ⟨getSpec, by simp [cspec, SolidCore.Refinement.Solar.Counter.Final.spec], [],
        .nil, 0, by decide, [], rfl⟩, [], 0, [], rfl⟩
  · obtain ⟨call, obs, hv, hn⟩ := ShapeExport.post_rejects
    exact ⟨_, call, obs, rfl, hv, hn⟩
  · obtain ⟨call, obs, hv, hs, hn⟩ := ShapeExport.allowed_rejects
    exact ⟨_, call, obs, rfl, hv, hs, hn⟩

/-- **Counter's certificate**, from its existing published theorem. -/
def certificate : Certificate src spec bytes where
  code := SolidCore.Refinement.Solar.CounterRun.code
  bound := Certified.counter.Final.bound
  checked := contract_ok
  translation := by
    rintro - _ rfl c hc
    obtain ⟨c', hc', h⟩ := ShapeExport.published
    rw [checked_eq, hc'] at hc
    cases hc
    exact (certifiedAt_default h).translation
  specProof := by
    rintro - _ rfl c hc
    obtain ⟨c', hc', h⟩ := ShapeExport.published
    rw [checked_eq, hc'] at hc
    cases hc
    exact (certifiedAt_default h).spec
  covered := covered

/-- **Counter meets the generic expected theorem.** -/
theorem expected : Expected src spec bytes := certificate.expected

/-- info: 'SolidCore.Verify.Generic.Instances.Counter.expected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms expected

end SolidCore.Verify.Generic.Instances.Counter

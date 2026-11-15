import SolidCore.Refinement.Spec
import SolidCore.Refinement.Corpus.C1
import SolidCore.Refinement.Corpus.W1
import SolidCore.Refinement.Corpus.W4
import SolidCore.Refinement.Corpus.C4
import SolidCore.Refinement.Corpus.W5
import Verify
import Verify.C4
import Verify.W5

/-!
# Verified source, verified bytecode

The end-to-end theorem for contracts the VC generator verifies: a specification proved
of SolidCore with the Loom-based generator (`SolidCore.Verify`) holds of solar's runtime
bytecode on EthLib.

For c1, c4, w1, w4 and w5 it holds with no hypothesis, through each contract's generated
refinement proof (`Corpus.<C>.refines`, `refines_full`). The staged forms reach the
same conclusion through a compiler's stages instead, each stated as a hypothesis named
after the obligation that discharges it:

* `lowering`: SolidCore to lowered MIR, including ABI decoding and dispatch;
* `backend`: solar's `mir_to_evmir_certified` (MIR pass, stack scheduling and EVM IR pass
  certificates);
* `assembly`: solar's `AssemblyStage`, EVM IR to bytecode on EthLib.
-/

namespace SolidCore.Refinement.Headline

open SolidCore.Refinement SolidCore.Refinement.Abi

theorem satisfies_iff {S : Sem} {p : S.Prog} {scope : Call → Prop} {pre : Call → Prop}
    {post : Call → Observable → Prop} :
    SolidCore.Verify.Satisfies S p scope pre post ↔ Satisfies S p scope pre post := Iff.rfl

/-- c1's verified specification holds of solar's bytecode. -/
theorem c1 : Satisfies ethLib Corpus.C1.code Verify.C1.scope Verify.C1.pre Verify.C1.post := by
  obtain ⟨c, hc, hs, hspec⟩ := Verify.C1.satisfies
  obtain ⟨c', s, hc', hs', href⟩ := Corpus.C1.refines
  rw [hc] at hc'
  cases hc'
  rw [hs] at hs'
  cases hs'
  exact bytecode_of_refines (satisfies_iff.mp hspec) href

/-- w1's verified specification holds of solar's bytecode, on every argument word. -/
theorem w1 : Satisfies ethLib Corpus.W1.code Verify.W1.scope Verify.W1.pre Verify.W1.post := by
  obtain ⟨c, hc, hspec⟩ := Verify.W1.satisfies
  obtain ⟨c', s, hc', hs', href⟩ := Corpus.W1.refines_full
  rw [hc] at hc'
  cases hc'
  rw [(Corpus.W1.shape_of hc).2.1] at hs'
  cases hs'
  exact bytecode_of_refines (satisfies_iff.mp hspec) href

/-- w4's verified specification holds of solar's bytecode, on every argument word. -/
theorem w4 : Satisfies ethLib Corpus.W4.code Verify.W4.scope Verify.W4.pre Verify.W4.post := by
  obtain ⟨c, hc, hspec⟩ := Verify.W4.satisfies
  obtain ⟨c', s, hc', hs', href⟩ := Corpus.W4.refines_full
  rw [hc] at hc'
  cases hc'
  rw [(Corpus.W4.shape_of hc).2.1] at hs'
  cases hs'
  exact bytecode_of_refines (satisfies_iff.mp hspec) href

/-- c4's verified specification holds of solar's bytecode, on every argument word, from the
deployed storage (`v = 0` and `w = 7` packed in slot 0). -/
theorem c4 : Satisfies ethLib Corpus.C4.code Verify.C4.scope Verify.C4.pre Verify.C4.post := by
  obtain ⟨c, hc, hs, hspec⟩ := Verify.C4.satisfies
  obtain ⟨c', s, hc', hs', href⟩ := Corpus.C4.refines_full
  rw [hc] at hc'
  cases hc'
  rw [hs] at hs'
  cases hs'
  exact bytecode_of_refines (satisfies_iff.mp hspec) href

/-- w5's verified specification holds of solar's `-Ogas` bytecode, on every pair of argument
words: `f(a, b)` returns `a + b` when it fits in 256 bits and otherwise reverts with
`Panic(0x11)`, with no logs and storage unchanged. Its proof uses neither `native_decide` nor
`bv_decide`: the kernel checks the type checker's output (`Corpus.W5.shape_eq`). -/
theorem w5 : Satisfies ethLib Corpus.W5.code Verify.W5.scope Verify.W5.pre Verify.W5.post := by
  obtain ⟨c, hc, hspec⟩ := Verify.W5.satisfies
  obtain ⟨c', s, hc', hs', href⟩ := Corpus.W5.refines_full
  rw [hc] at hc'
  cases hc'
  rw [(Corpus.W5.shape_of hc).2.1] at hs'
  cases hs'
  exact bytecode_of_refines (satisfies_iff.mp hspec) href

/-- The same for w1 through a compiler's stages, each a hypothesis. -/
theorem w1_staged {mirSem evmirSem : Sem} {mir : mirSem.Prog} {evmir : evmirSem.Prog}
    (lowering : ∀ c, Corpus.W1.contract? = .ok c →
      Stage (solidCore Corpus.W1.fuel) mirSem c mir Verify.W1.scope)
    (backend : Stage mirSem evmirSem mir evmir Verify.W1.scope)
    (assembly : Stage evmirSem ethLib evmir Corpus.W1.code Verify.W1.scope) :
    Satisfies ethLib Corpus.W1.code Verify.W1.scope Verify.W1.pre Verify.W1.post := by
  obtain ⟨c, hc, hspec⟩ := Verify.W1.satisfies
  exact bytecode_of_stages (satisfies_iff.mp hspec) (lowering c hc) backend assembly

end SolidCore.Refinement.Headline

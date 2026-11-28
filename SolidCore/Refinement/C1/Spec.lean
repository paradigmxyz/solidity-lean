import SolidCore.Refinement.Spec
import SolidCore.Refinement.C1.Refinement

/-!
# c1's specification on bytecode

c1's specification carried to solar's bytecode, directly from `C1.refines` and through a
compiler's stages. `C1.Refinement` evaluates SolidCore with `native_decide`, which trusts Lean's
compiler, so this module and it are the `SolidCoreNative` library, outside the default `SolidCore`
library, which uses none.
-/

namespace SolidCore.Refinement

namespace C1

/-- c1's specification: `f(x)` returns `3 * x + 1` when it fits in `uint8`, reverts with
`Panic(0x11)` when it overflows, and reverts with no data for a dirty argument word; it
never logs and leaves storage empty. -/
def post (call : Call) (obs : Observable) : Prop :=
  ∃ w, call = C1.call w ∧ obs = expected w

/-- SolidCore's c1 meets its specification on every argument word. -/
theorem satisfies_source {c : SolidCore.Solidity.TypeCheck.CheckedContract}
    (h : contract? = .ok c) : Satisfies (solidCore fuel) c scope (fun _ => True) post := by
  rintro _ ⟨w, rfl⟩ -
  exact ⟨expected w, source_run h w, w, rfl, rfl⟩

/-- solar's bytecode for c1 meets c1's specification on every argument word, with no
hypothesis. -/
theorem satisfies_bytecode : Satisfies ethLib code scope (fun _ => True) post := by
  obtain ⟨c, hc, href⟩ := refines
  exact bytecode_of_refines (satisfies_source hc) href

/-- The same through a compiler's stages, each a hypothesis. -/
theorem satisfies_bytecode_staged {mirSem evmirSem : Sem} {c : SolidCore.Solidity.TypeCheck.CheckedContract}
    {mir : mirSem.Prog} {evmir : evmirSem.Prog} (hc : contract? = .ok c)
    (lowering : Stage (solidCore fuel) mirSem c mir scope)
    (backend : Stage mirSem evmirSem mir evmir scope)
    (assembly : Stage evmirSem ethLib evmir code scope) :
    Satisfies ethLib code scope (fun _ => True) post :=
  bytecode_of_stages (satisfies_source hc) lowering backend assembly

end C1

end SolidCore.Refinement

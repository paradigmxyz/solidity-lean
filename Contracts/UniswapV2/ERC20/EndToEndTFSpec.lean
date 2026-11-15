import Contracts.UniswapV2.ERC20.EndToEndTF
import Contracts.UniswapV2.ERC20.ConnectTFSplit

/-!
# UniswapV2ERC20's transferFrom: equivalence, termination and its exported spec on the exact bytecode

`published_tf` is `functional_tf` with solar-verify's exported spec of `transferFrom`, proved of
SolidCore's checked contract branch by branch (ConnectTFSplit's `transferFrom_holds`, under
`NestedSlotsSeparated [1, 4] [2]`), with the identity ghost step. No gas bound: not
`Shapes.Certified`.
-/

namespace SolidCore.Spec.UniswapV2.ERC20.EndToEndTF

open SolidCore.Spec SolidCore.Refinement SolidCore.Refinement.Shapes SolidCore.Spec.UniswapV2.ERC20

def idStep : GhostStep := fun _ g => g

/-- transferFrom's exported spec of every result on its calls. -/
def Post (call : SolarTV.Call) (obs : SolarTV.Observable) : Prop :=
  holdsPost SolidCore.Spec.UniswapV2.ERC20TF.spec SolidCore.Spec.UniswapV2.ERC20TF.ctxOf idStep
    SolidCore.Spec.UniswapV2.ERC20TF.transferFrom_spec
    (SolidCore.Verify.VC.stageScope SolidCore.Spec.UniswapV2.ERC20TF.fn_transferFrom
      SolidCore.Spec.UniswapV2.ERC20TF.deployed) call obs

theorem published_tf (hsep : NestedSlotsSeparated [1, 4] [2])
    (hP : ∀ gas, SolidCore.Refinement.Solar.AssembleCallSeg.StaticRunner gas)
    (hQ : ∀ gas call, genericValid0 fnsTF deployed call →
      SolidCore.Refinement.Solar.AssembleCallSeg.CalleesRun gas SolarTV.Export.UniswapV2ERC20.Ctx.code call) :
    ∃ c, SolidCore.Verify.VC.UniswapV2ERC20.contract? = .ok c ∧
      Functional (solidCore SolidCore.Verify.VC.UniswapV2ERC20.fuel) c SolarTV.Export.UniswapV2ERC20.Ctx.code
        (genericValid0 fnsTF deployed) (fun _ _ => True) Post := by
  obtain ⟨c, hc⟩ := SolidCore.Verify.VC.UniswapV2ERC20.contract_ok
  exact ⟨c, hc, functional_tf hP hQ hc
    (meets_of_holdsFn (SolidCore.Spec.UniswapV2.ERC20TF.transferFrom_holds hsep hc idStep (fun _ _ _ => rfl)))⟩

/-- info: 'SolidCore.Spec.UniswapV2.ERC20.EndToEndTF.published_tf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms published_tf

end SolidCore.Spec.UniswapV2.ERC20.EndToEndTF

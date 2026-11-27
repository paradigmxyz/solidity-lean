import erc20_any.Final
open SolarTV SolidCore.Refinement SolidCore.Spec SolidCore.Verify.Generic Certified.erc20_any.Final
open SolidCore.Spec.UniswapV2.ERC20.Slice (Valid transferCall balKey balanceSlot)
set_option maxRecDepth 100000

def mutPost (a : Nat) (call : Call) (obs : Observable) : Prop := TargetPostAt a call obs ∧ ∀ σ dst v, call = transferCall σ dst v → a = dst → obs.success = true → slotValue σ (balKey dst) + v < 2 ^ 256
example : Expected src { specScoped with Post := fun ctx => mutPost ctx.caller } runtimeBytes := Certified.erc20_any.Proof.scopedExpected

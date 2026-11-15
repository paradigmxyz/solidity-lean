import Contracts.UniswapV2.ERC20.Meets

/-!
# UniswapV2ERC20: solar-verify's exported specs of SolidCore's checked contract

The statement this lane delivers, for the functions the generic source stage erases with a spec
proved of their tree (`approve` and `transfer`): solar-verify's exported spec of each holds of SolidCore's
checked UniswapV2ERC20 (`contract? = .ok c`, the kernel's type check and translation of the port,
`Contracts.UniswapV2.ERC20.Core`) on the stage's calls of it (any argument words, no value, any storage
covering the deployed one), in every world `W` (the functions call out nowhere), under two named
hypotheses:

* `NestedSlotsSeparated [1, 4] [2]`: keccak256 separated on the slots of `balanceOf[a]`, `nonces[a]` and
  `allowance[o][s]` (injective, images at least `2 ^ 128`); not provable of keccak256, so a premise;
* the ghost step leaves the ghost state (`sumBalances`, `zeroMinted`) alone on these calls: the spec
  updates the ghosts only in `_mint` and `_burn`, which neither function reaches.

Scope: runtime calls of `approve` and `transfer` from the stage's caller (`0x2000`) with no value; the
constructor is covered only through the deployed storage it leaves (`deploy_eq`). Not covered here:
`transferFrom` (tree erased; its spec of the tree is pending), `permit` (outside the generic stage:
keccak256 of memory and the ECRECOVER call), and the bytecode side (the stages from SolidCore to
solar's bytecode for UniswapV2ERC20 are not yet built), so this is a source-level spec result, not
an end-to-end one.
-/

namespace SolidCore.Spec.UniswapV2.ERC20

open SolidCore.Spec SolidCore.Refinement

/-- **approve's and transfer's exported specs hold of SolidCore's checked UniswapV2ERC20 in every
world**, under keccak256's separation on the mapping slots and a ghost step that leaves the ghosts
alone on these calls. -/
theorem specs_hold_in (W : SolidCore.Refinement.World) (hsep : NestedSlotsSeparated [1, 4] [2])
    {c : SolidCore.Solidity.TypeCheck.CheckedContract}
    (hc : SolidCore.Verify.VC.UniswapV2ERC20.contract? = .ok c) (step : GhostStep)
    (hstep : ∀ fn ∈ [fn_approve, fn_transfer], ∀ call,
      SolidCore.Verify.VC.stageScope fn deployed call → ∀ g, step call g = g) :
    HoldsFn (solidCoreIn W SolidCore.Verify.VC.UniswapV2ERC20.fuel) c
        (SolidCore.Verify.VC.stageScope fn_approve deployed) spec ctxOf step approve_spec ∧
      HoldsFn (solidCoreIn W SolidCore.Verify.VC.UniswapV2ERC20.fuel) c
        (SolidCore.Verify.VC.stageScope fn_transfer deployed) spec ctxOf step transfer_spec :=
  ⟨approve_holds_in W hsep hc step (hstep _ (by simp)),
    transfer_holds_in W hsep hc step (hstep _ (by simp))⟩

/-- info: 'SolidCore.Spec.UniswapV2.ERC20.specs_hold_in' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms specs_hold_in

end SolidCore.Spec.UniswapV2.ERC20

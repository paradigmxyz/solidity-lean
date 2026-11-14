import Verify.Spec.Tree
import Verify.Spec.Hash
import Verify.Spec.TreeIn
import Contracts.Token.TransferMeets
import Contracts.Token.EndToEnd

/-!
# Token: solar-verify's exported spec of `transfer` of solar's bytecode, generically

`Spec/Export.lean` is solar-verify's `--emit-lean-spec` export of `scripts/verify/Token.sol`.
`transfer_meets` (TransferMeets.lean, by the generic mapping tactic `tree_meets_map`) proves
`transfer`'s exported spec of the generic source stage's tree (`transferTree`, `transferShape_eq`):
the two balance clauses, the frame clause over every other address, the supply clause and the
invariant `totalSupply == sumBalances` (`TreeMeetsFixed`: `transfer` writes no ghost). The mapping
slots are SolidCore's `solHash`, which is the spec semantics' slot by `solHash_eq`; their
separation (distinct on distinct addresses, and from the scalar slots) is the one hypothesis,
`SlotsSeparated 0`. `transfer_holds` lifts it to SolidCore's checked Token (`holdsFn_of_tree_fixed`)
and `transfer_spec_bytecode` carries it to solar's bytecode through the certified stages
(`Contracts.Token.certified`). No solver verdict is used. The negative, `wrong_not_meets`, is in
TransferMeets.lean.
-/

namespace SolidCore.Spec.TreeDemo.Token

open SolidCore.Spec SolidCore.Refinement SolidCore.Refinement.Generic SolidCore.Verify.VC.Token

/-- **`transfer`'s exported spec holds of SolidCore's checked Token** on the stage's calls of
`transfer` (storage covering the deployed owner slot), for a ghost step that leaves the ghost
state alone on them. -/
theorem transfer_holds (hsep : SlotsSeparated 0) {c : SolidCore.Solidity.TypeCheck.CheckedContract}
    (hc : contract? = .ok c) (step : GhostStep)
    (hstep : ∀ call, SolidCore.Verify.VC.stageScope fnTransfer [(2, 4096)] call → ∀ g, step call g = g) :
    HoldsFn (solidCore fuel) c (SolidCore.Verify.VC.stageScope fnTransfer [(2, 4096)]) spec ctxOf step
      transferSpec := by
  have hdep := burnShape_eq
  simp only [burnShape?, hc, Option.some.injEq, Prod.mk.injEq] at hdep
  obtain ⟨d, hd⟩ := Wide.deployedAt_of hdep.1
  have hshape := transferShape_eq
  simp only [transferShape?, hc, Option.some.injEq, Option.map_eq_some_iff, Prod.mk.injEq] at hshape
  obtain ⟨f, hf, hlen, hT⟩ := hshape
  exact holdsFn_of_tree_fixed (fn := fnTransfer) hd (by decide) hf hlen hT
    (fun call h => by simp [ctxOf, ctx, h]) hstep (transfer_meets hsep)


/-- **`transfer`'s exported spec holds of SolidCore's checked Token in every world `W`** (Token
calls out nowhere), the source side `compose_in` and `holds_of_runs` take. -/
theorem transfer_holds_in (W : SolidCore.Refinement.World) (hsep : SlotsSeparated 0)
    {c : SolidCore.Solidity.TypeCheck.CheckedContract} (hc : contract? = .ok c) (step : GhostStep)
    (hstep : ∀ call, SolidCore.Verify.VC.stageScope fnTransfer [(2, 4096)] call → ∀ g, step call g = g) :
    HoldsFn (solidCoreIn W fuel) c (SolidCore.Verify.VC.stageScope fnTransfer [(2, 4096)]) spec ctxOf
      step transferSpec := by
  have hdep := burnShape_eq
  simp only [burnShape?, hc, Option.some.injEq, Prod.mk.injEq] at hdep
  obtain ⟨d, hd⟩ := Wide.deployedAt_of hdep.1
  have hshape := transferShape_eq
  simp only [transferShape?, hc, Option.some.injEq, Option.map_eq_some_iff, Prod.mk.injEq] at hshape
  obtain ⟨f, hf, hlen, hT⟩ := hshape
  exact holdsFn_of_tree_fixed_in W (fn := fnTransfer) hd (by decide) hf hlen hT
    (fun call h => by simp [ctxOf, ctx, h]) hstep (transfer_meets hsep)

/-- info: 'SolidCore.Spec.TreeDemo.Token.transfer_holds_in' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms transfer_holds_in

end SolidCore.Spec.TreeDemo.Token

namespace SolidCore.Refinement.Solar.Token.SpecTree

open SolidCore.Spec SolidCore.Refinement

/-- **solar-verify's exported spec of `transfer` holds of solar's runtime bytecode** under EthLib,
on every call of `transfer(address,uint256)` in the stage's scope (any argument words, no value,
any storage covering the owner slot), given `SlotsSeparated 0`, for any ghost step that leaves
the ghost state alone on those calls: the spec of the erased tree (`transfer_meets`), SolidCore's
run of the tree (`holdsFn_of_tree_fixed`) and the certified stage from SolidCore's Token to the
bytecode (`Contracts.Token.certified`). No solver verdict. -/
theorem transfer_spec_bytecode (hsep : SlotsSeparated 0) (step : GhostStep)
    (hstep : ∀ call, SolidCore.Verify.VC.stageScope SolidCore.Verify.VC.Token.fnTransfer [(2, 4096)] call →
      ∀ g, step call g = g) :
    HoldsFn ethLib SolidCore.Refinement.Solar.VerifyTokenAsm.code
      (SolidCore.Verify.VC.stageScope SolidCore.Verify.VC.Token.fnTransfer [(2, 4096)])
      SolidCore.Spec.TreeDemo.Token.spec SolidCore.Spec.TreeDemo.Token.ctxOf step
      SolidCore.Spec.TreeDemo.Token.transferSpec := by
  obtain ⟨c, hc⟩ := SolidCore.Refinement.Solar.VerifyTokenSource.contract_ok
  exact (SolidCore.Spec.TreeDemo.Token.transfer_holds hsep hc step hstep).of_stage
    (Contracts.Token.certified hc SolidCore.Refinement.Solar.VerifyTokenSource.check_transfer_eq)

/-- info: 'SolidCore.Refinement.Solar.Token.SpecTree.transfer_spec_bytecode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms transfer_spec_bytecode

end SolidCore.Refinement.Solar.Token.SpecTree

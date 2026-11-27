import Contracts.Token.VC.Burn

/-!
# Oracle allow-list corollaries: `Token.vc_eq`

The simplification pass changed or removed these declarations. The oracle
(/home/hand/simp/oracle/oracle.sh with the allow-list ACCEPTED.md) accepts each change
only because its outside users were rewritten in the same commit (fad955ce) against the generic
`triple_of_binds` with their own statements unchanged, and the lemma still holds of
`Verify.Basic`'s `vc`, which did not change. Each theorem below
restates a base statement verbatim, under the same name in a `Base` namespace, and
proves it again from `vc` and `wp_eq`. Nothing imports this module.
-/

namespace SolidCore.Verify.VC.Token.Base

open SolidCore.Refinement SolidCore.Refinement.Abi SolidCore.Refinement.Generic
open SolidCore.Solidity SolidCore.Solidity.Source

/-- Base `vc_eq` (removed): the verification condition is `post` of the model's observable. -/
theorem vc_eq (model : List Nat → SolM (List Nat)) (args : Call → List Nat)
    (post : Call → SolarTV.Observable → Prop) (call : Call) :
    vc model args post call =
      post call (observe (initStorage call) (model (args call) (initStorage call))) := by
  unfold vc
  rw [wp_eq]
  rcases h : model (args call) (initStorage call) with e | ⟨out, s'⟩ <;> simp only [h] <;> rfl

end SolidCore.Verify.VC.Token.Base

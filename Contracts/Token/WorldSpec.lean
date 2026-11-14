import Contracts.Token.EndToEnd
import Verify.SourceOracle

/-!
# solar-verify's Token: its triples in every world

`transfer_tripleIn` and `burn_tripleIn` are solar-verify's triples of SolidCore's Token
(`transfer_triple_discharged`, `burn_triple`) with SolidCore run in any world `W` (any call oracle, any
other accounts' code), from the generic check that accepts both functions
(`tripleIn_of_triple`): the open worlds of `holds_of_runs` included, with the same hypothesis
(`HashInj` for `transfer`, none for `burn`) and none on the world.
-/

namespace Contracts.Token

open SolidCore.Refinement SolidCore.Verify SolidCore.Verify.VC SolidCore.Verify.VC.Token
open SolidCore.Refinement.Solar.VerifyTokenSource (check_of deployed check_transfer_eq check_burn_eq)

/-- **`transfer`'s triple in every world**, given `HashInj`. -/
theorem transfer_tripleIn (inj : HashInj) {c : SolidCore.Solidity.TypeCheck.CheckedContract}
    (hc : contract? = .ok c) (W : World) :
    TripleIn W fuel c (stageScope fnTransfer [(2, 4096)]) (fun _ => True) trPost := by
  obtain ⟨d, hd⟩ := deployed hc
  exact tripleIn_of_triple hd (check_of hc check_transfer_eq) (fun _ h => h)
    (transfer_triple_discharged inj hc) W

/-- **`burn`'s triple in every world**, with no hypothesis. -/
theorem burn_tripleIn {c : SolidCore.Solidity.TypeCheck.CheckedContract} (hc : contract? = .ok c)
    (W : World) : TripleIn W fuel c (stageScope fnBurn [(2, 4096)]) (fun _ => True) burnPost := by
  obtain ⟨d, hd⟩ := deployed hc
  exact tripleIn_of_triple hd (check_of hc check_burn_eq) (fun _ h => h) (burn_triple hc) W

/-- info: 'Contracts.Token.transfer_tripleIn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms transfer_tripleIn

/-- info: 'Contracts.Token.burn_tripleIn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms burn_tripleIn

end Contracts.Token

import Contracts.Counter.Final
import Verify.Abi

/-!
# Counter's declared valid calls, allowed statuses and specification

The inputs the certify driver names in the published statement of `Certified/counter`
(`Certified/counter/shape.json`): reviewed specification, not proof. The valid calls are
`cspec.Calls`; the postcondition is `Shapes.specPost cspec`; the allowed statuses are
`allowed`; the gas bound is `gasBound`.
-/

namespace SolidCore.Refinement.Solar.Counter.ShapeSpec

open SolidCore.Refinement SolidCore.Refinement.Final SolidCore.Refinement.Evm.Wide
open SolidCore.Refinement.Solar.Counter
open EthLib.Base

/-- The declared specification (solar-verify's, as `Final.spec`). -/
abbrev cspec : ContractSpec Nat := SolidCore.Refinement.Solar.Counter.Final.spec

/-- The statuses the specification allows. -/
def allowed (call : Call) (obs : Observable) : Prop :=
  obs.success = true ∨ call.callvalue ≠ 0 ∨
    (obs.output = SolidCore.Verify.panic 0x11 ∧ ∃ d : U256, call.calldata = (callOf incSelector [d]).calldata ∧
      2 ^ 256 ≤ slotValue call.storage 0 + d.toNat)

/-- The gas bound: from this gas on every valid call ends with the source's result. -/
def gasBound : Call → Nat := fun _ => 1281806

end SolidCore.Refinement.Solar.Counter.ShapeSpec

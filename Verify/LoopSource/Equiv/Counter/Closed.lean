import Verify.LoopSource.Equiv.Counter.Expected
import Verify.LoopSource.Equiv.Counter.Proofs.Execution

/-!
# Counter.bump: source to the exact emitted runtime, with the backend discharged

The backend's MIR-to-EVM-IR stage (\`counterLoop_mir_to_evmir\`, proved through cut points by the
driver's stage generator) and the assembler's loop check of the exact runtime bytes the compiler
emits (\`check_ok\`: \`AssembleLoop.checkL evm7 code cert maxs = true\`, evaluated by the kernel) are
proved here for Counter's export, not assumed.

* \`counter_equiv_closed\`: \`Shapes.Equiv\` of the source semantics and the emitted runtime \`code\` on
  every call \`bump(a)\`, \`a < 2 ^ 256\`, any storage, no value. No premise.
* \`counter_certified_closed\`: the driver's whole \`Shapes.Certified\` statement with \`bump\`'s
  postcondition, given only \`Shapes.Resources\` (the gas bound) for \`code\`, which stays a premise.
-/

namespace Verify.LoopSource.Equiv.CounterClosed
open SolarTV SolarTV.Machine SolidCore.Refinement SolidCore.Refinement.Generic
open Contracts.VerifyCounter.Source Verify.LoopSource.MirLink Verify.LoopSource.Equiv.CounterExpected

/-- **Equivalence of Counter's source and its exact emitted runtime**, with no premise. -/
theorem counter_equiv_closed {c : SolidCore.Solidity.TypeCheck.CheckedContract} (hc : contract? = .ok c) :
    Shapes.Equiv stmtSem c SolarTV.Milestone.X.code BumpCall :=
  counter_equiv hc (SolarTV.Milestone.X.counterLoop_mir_to_evmir Shapes.oracle) (fun _ _ => trivial)
    SolarTV.Milestone.X.check_ok

/-- **The driver's Statement for Counter**, given only the emitted runtime's resources. -/
theorem counter_certified_closed (G : Call → Nat)
    (hres : ∀ c, contract? = .ok c → Shapes.Resources stmtSem c SolarTV.Milestone.X.code BumpCall G) :
    ∃ c, contract? = .ok c ∧
      Shapes.Certified stmtSem c SolarTV.Milestone.X.code BumpCall (fun _ _ => True) BumpPost G :=
  counter_certified G (SolarTV.Milestone.X.counterLoop_mir_to_evmir Shapes.oracle) (fun _ _ => trivial)
    SolarTV.Milestone.X.check_ok hres

end Verify.LoopSource.Equiv.CounterClosed

/-- info: 'Verify.LoopSource.Equiv.CounterClosed.counter_equiv_closed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Verify.LoopSource.Equiv.CounterClosed.counter_equiv_closed

/-- info: 'Verify.LoopSource.Equiv.CounterClosed.counter_certified_closed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Verify.LoopSource.Equiv.CounterClosed.counter_certified_closed

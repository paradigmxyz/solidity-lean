import Verify.Eval.G.Capture.Hook
import abi_hash.gen.AbiHash.Evm1
import abi_hash.gen.AbiHash.Evm2
import abi_hash.gen.AbiHash.Sched

/-! abi_hash's stage proofs Evm1 and Evm2 under the capture hook. -/


namespace SolarTV.Milestone.AbiHash
open Machine SolarTV.Export.AbiHash SolarTV.Milestone.W1

set_option maxHeartbeats 2000000 in
theorem evm1_run (o : Oracle) (call : Call) :
    EVM.Program.run o sched call 7 = EVM.Program.run o evm1 call 4 := by
  sym_exec

set_option maxHeartbeats 2000000 in
theorem evm2_run (o : Oracle) (call : Call) :
    EVM.Program.run o evm1 call 4 = EVM.Program.run o evm2 call 4 := by
  sym_exec

end SolarTV.Milestone.AbiHash

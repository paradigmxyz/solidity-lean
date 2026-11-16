import PerPC.Tactic
-- Bench copy of the generated proof: only sym_exec -> sym_exec_pc and the namespace differ.
import W1Proofs.Tactic
import W1Proofs.Axioms
import flag_4ce5cf9a.gen.Flag.Evm3
import flag_4ce5cf9a.gen.Flag.Evm2

/-! `terminal-dedup`: its input and output end in the same result on every call. -/

namespace SolarTV.Milestone.Flag4ce5cf9a.PC

open Machine SolarTV.Export.Flag SolarTV.Milestone.W1

set_option maxHeartbeats 2000000 in
theorem evm3_run (o : Oracle) (call : Call) :
    EVM.Program.run o evm2 call 7 = EVM.Program.run o evm3 call 7 := by
  sym_exec_pc

/-- info: 'SolarTV.Milestone.Flag4ce5cf9a.PC.evm3_run' depends on axioms within [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#axioms_within evm3_run

#block_entry_counts

end SolarTV.Milestone.Flag4ce5cf9a.PC

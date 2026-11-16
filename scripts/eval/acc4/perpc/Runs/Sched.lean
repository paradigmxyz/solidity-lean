import PerPC.Tactic
-- Bench copy of the generated proof: only sym_exec -> sym_exec_pc and the namespace differ.
import W1Proofs.Tactic
import W1Proofs.Axioms
import flag_4ce5cf9a.gen.Flag.Sched
import flag_4ce5cf9a.gen.Flag.Stage0

/-! Stack scheduling: the last lowered MIR and the scheduled EVM IR end in the same result on every call. -/

namespace SolarTV.Milestone.Flag4ce5cf9a.PC

open Machine SolarTV.Export.Flag SolarTV.Milestone.W1

set_option maxHeartbeats 2000000 in
theorem sched_run (o : Oracle) (call : Call) :
    MIR.Lowered.Module.run o stage0 call 13 = EVM.Program.run o sched call 13 := by
  sym_exec_pc

/-- info: 'SolarTV.Milestone.Flag4ce5cf9a.PC.sched_run' depends on axioms within [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#axioms_within sched_run

#block_entry_counts

end SolarTV.Milestone.Flag4ce5cf9a.PC

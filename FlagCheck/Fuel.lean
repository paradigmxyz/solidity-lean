import Verify.Gas.FixedFuel.Acyclic
import FlagCheck.Evm5

open SolarTV SolarTV.Machine

theorem flag_rank_ok : Verify.Gas.FixedFuel.Acyclic.rankOk SolarTV.Export.Flag.evm5 [2, 0, 0, 0, 1, 0] = true := by
  decide +kernel

theorem flag_ends_6 (o : Machine.Oracle) (call : Call) :
    (EVM.Program.run o SolarTV.Export.Flag.evm5 call 6).isSome = true :=
  Verify.Gas.FixedFuel.Acyclic.ends_of_rank flag_rank_ok (by decide +kernel) o call

#print axioms flag_ends_6

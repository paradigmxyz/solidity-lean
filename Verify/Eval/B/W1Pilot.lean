import Verify.W1
import Verify.Eval.B.SymEval
import Verify.Eval.Common.Measure

/-!
# Lane B pilot: `Verify.W1.run_f`, baseline (`wide_symex`) and `wide_symex_sym`

The statement is copied verbatim from `Verify/W1.lean`. `run_f_base` is the repository's proof
text; `run_f_sym` replaces only the evaluator call with `wide_symex_sym` (Sym.simp, with the
existing `Meta.simp` loop as per-goal fallback, whose progressing rounds it counts).
-/

namespace SolidCore.Verify.W1.EvalB

open EthLib.Base SolidCore.Refinement SolidCore.Refinement.Abi SolidCore.Refinement.Wide
open SolidCore.Refinement.Evm.Wide SolidCore.Solidity SolidCore.Solidity.Source
open SolidCore.Refinement.Corpus.W1 SolidCore.Verify.W1

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem run_f_base {c : TypeCheck.CheckedContract} (hcore : c.core = coreLit) {d : Source.State}
    (hd : Deployed fuel c d) (w : U256) :
    Source.run fuel c (callOf Bytecode.W1.Main.fSelector [w]) =
      some (Verify.observe (fun _ => 0) (model [w.toNat] (fun _ => 0))) := by
  rw [run_eq hd]
  have hs := hd.storage
  have hev := hd.events
  simp only [hcore, List.map_cons, List.map_nil]
  wide_symex [coreLit, fuel, ctxOf, hcore, Bytecode.W1.Main.fSelector]
  all_goals
    have hw := w.isLt
    simp only [model, List.getD_cons_zero]
    split
    all_goals try omega
  all_goals
    try rw [Nat.mod_eq_of_lt (by omega)]
    simp [Source.observe, Verify.observe, revert, pure, StateT.pure, Except.pure, panic, word,
      State.logEntries, State.loadSlot, StorageMap.lookup?, getElem?_of_isEmpty hs,
      slotValue, callOf]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem run_f_sym {c : TypeCheck.CheckedContract} (hcore : c.core = coreLit) {d : Source.State}
    (hd : Deployed fuel c d) (w : U256) :
    Source.run fuel c (callOf Bytecode.W1.Main.fSelector [w]) =
      some (Verify.observe (fun _ => 0) (model [w.toNat] (fun _ => 0))) := by
  rw [run_eq hd]
  have hs := hd.storage
  have hev := hd.events
  simp only [hcore, List.map_cons, List.map_nil]
  wide_symex_sym [coreLit, fuel, ctxOf, hcore, Bytecode.W1.Main.fSelector]
  all_goals
    have hw := w.isLt
    simp only [model, List.getD_cons_zero]
    split
    all_goals try omega
  all_goals
    try rw [Nat.mod_eq_of_lt (by omega)]
    simp [Source.observe, Verify.observe, revert, pure, StateT.pure, Except.pure, panic, word,
      State.logEntries, State.loadSlot, StorageMap.lookup?, getElem?_of_isEmpty hs,
      slotValue, callOf]

#proof_stats run_f_base
#proof_stats run_f_sym
#kernel_recheck run_f_base
#kernel_recheck run_f_sym
#print axioms run_f_base
#print axioms run_f_sym

end SolidCore.Verify.W1.EvalB

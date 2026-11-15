import Verify.W4
import Verify.Eval.B.SymEval
import Verify.Eval.Common.Measure

/-!
# Lane B pilot: `Verify.W4.run_set`, baseline (`wide_symex`) and `wide_symex_sym`

The statement is copied verbatim from `Verify/W4.lean`; `run_set_base` is the repository's proof
-/

namespace SolidCore.Verify.W4.EvalB

open EthLib.Base SolidCore.Refinement SolidCore.Refinement.Abi SolidCore.Refinement.Wide
open SolidCore.Refinement.Evm.Wide SolidCore.Solidity SolidCore.Solidity.Source
open SolidCore.Refinement.Corpus.W4 SolidCore.Verify.W4

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem run_set_base {c : TypeCheck.CheckedContract} (hcore : c.core = coreLit) {d : Source.State}
    (hd : Deployed fuel c d) (w : U256) :
    Source.run fuel c (callOf Bytecode.W4.Main.setSelector [w]) =
      some (Verify.observe (fun _ => 0) (model [w.toNat] (fun _ => 0))) := by
  rw [run_eq hd]
  have hs := hd.storage
  have hev := hd.events
  simp only [hcore, List.map_cons, List.map_nil]
  wide_symex [coreLit, fuel, ctxOf, hcore, Bytecode.W4.Main.setSelector]
  have hw := w.isLt
  simp only [Source.observe, Verify.observe, model, sstore, bind, StateT.bind, pure, StateT.pure,
    Except.bind, Except.pure, Observable.mk.injEq]
  refine ⟨trivial, trivial, by simp [State.logEntries], ?_⟩
  funext slot
  simp only [ite_true, State.loadSlot, StorageMap.lookup?, Std.HashMap.get?_eq_getElem?,
    Std.HashMap.getElem?_insert, getElem?_of_isEmpty hs, Shared.norm, Shared.wordModulus]
  rw [show EvmYul.UInt256.size = 2 ^ 256 from rfl]
  generalize slot % 115792089237316195423570985008687907853269984665640564039457584007913129639936 = k
  by_cases h : k = 0
  · subst h; simp; exact (Nat.mod_eq_of_lt hw).symm
  · have h' : ¬0 = k := fun e => h e.symm
    simp [h, h']

#proof_stats run_set_base
#kernel_recheck run_set_base
#print axioms run_set_base

end SolidCore.Verify.W4.EvalB

import Verify.W1
import Verify.Eval.B.SymEval

namespace SolidCore.Verify.W1
open EthLib.Base SolidCore.Refinement SolidCore.Refinement.Abi SolidCore.Refinement.Wide
open SolidCore.Refinement.Evm.Wide SolidCore.Solidity SolidCore.Solidity.Source
open SolidCore.Refinement.Corpus.W1

set_option pp.maxSteps 3000
set_option pp.deepTerms false
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
example {c : TypeCheck.CheckedContract} (hcore : c.core = coreLit) {d : Source.State}
    (hd : Deployed fuel c d) (w : U256) :
    Source.run fuel c (callOf Bytecode.W1.Main.fSelector [w]) =
      some (Verify.observe (fun _ => 0) (model [w.toNat] (fun _ => 0))) := by
  rw [run_eq hd]
  have hs := hd.storage
  have hev := hd.events
  simp only [hcore, List.map_cons, List.map_nil]
  wide_symex_sym nofallback debug budget60 [coreLit, fuel, ctxOf, hcore, Bytecode.W1.Main.fSelector]
  trace_state
  all_goals sorry

end SolidCore.Verify.W1

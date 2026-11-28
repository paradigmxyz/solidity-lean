import Contracts.Token.VC.Transfer

/-!
# Token.transfer's obligations, discharged in Lean

`transfer_triple` takes solar-verify's verdict `Valid Export.Token.script` and reads each of
`transfer`'s three clauses off the obligation the checked script gives (`checkScript_sound`). The three
obligations `trObs` it uses hold in the array theory on their own: `trObs_valid` proves them for
every assignment, by the semantics of `select` and `store` (no solver, no verdict). So
`transfer_triple_discharged` is `transfer_triple` with the verdict gone: its one hypothesis is `HashInj`,
injectivity of the mapping slot on address keys. `transfer_check` (the kernel's check that solar-verify's
script has these obligations) still ties them to solar-verify's encoding of the clauses.
-/

namespace SolidCore.Verify.VC.Token

open SolidCore.Verify SolidCore.Verify.VC SolidCore.Refinement SolidCore.Refinement.Abi
open SolidCore.Refinement.Generic

/-- `transfer`'s three obligations hold at every assignment of the array theory. -/
theorem trObs_valid : ObsValid trObs := by
  intro o ho σ _
  simp only [trObs, List.mem_cons, List.mem_nil_iff, or_false] at ho
  rcases ho with rfl | rfl | rfl
  · simp only [trGoalFrom]
    simp [Tm.Holds, Tm.eval, Tm.evalList, applyOp, Value.select, Value.store, Value.toProp, Value.toInt, Value.toArr, Value.eq, Ob.eq, Ob.sel, Ob.sub, Ob.add, Ob.S2, Ob.S1, Ob.sto, Ob.ms, Ob.rcpt, Ob.B, Ob.bal, Ob.amt]
    intro h1 h2
    exact absurd h2 h1
  · simp only [trGoalTo]
    simp [Tm.Holds, Tm.eval, Tm.evalList, applyOp, Value.select, Value.store, Value.toProp, Value.toInt, Value.toArr, Value.eq, Ob.eq, Ob.sel, Ob.sub, Ob.add, Ob.S2, Ob.S1, Ob.sto, Ob.ms, Ob.rcpt, Ob.B, Ob.bal, Ob.amt]
    intro h
    exact ite_cond_eq_false _ _ (eq_false (Ne.symm h))
  · simp only [trGoalFrame]
    simp [Tm.Holds, Tm.eval, Tm.evalList, applyOp, Value.select, Value.store, Value.toProp, Value.toInt, Value.toArr, Value.eq, Ob.eq, Ob.sel, Ob.sub, Ob.add, Ob.S2, Ob.S1, Ob.sto, Ob.ms, Ob.rcpt, Ob.B, Ob.bal, Ob.amt]
    intro n _ _ h1 h2
    simp only [Env.setI] at *
    simp_all


/-- `Token.transfer` meets its three ensures clauses on distinct addresses on the stage's scope,
given only injectivity of the mapping slot on address keys. -/
theorem transfer_triple_discharged (inj : HashInj)
    {c : SolidCore.Solidity.TypeCheck.CheckedContract} (hc : contract? = .ok c) :
    Triple fuel c (stageScope fnTransfer [(2, 4096)]) (fun _ => True) trPost :=
  transfer_triple_of trObs_valid inj hc

/-- info: 'SolidCore.Verify.VC.Token.transfer_triple_discharged' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms transfer_triple_discharged

end SolidCore.Verify.VC.Token

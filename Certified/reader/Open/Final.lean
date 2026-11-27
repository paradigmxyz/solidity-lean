import reader.Open.Target
import Contracts.Reader.Stage

/-! **Reader's external-call target, closed.** `read_final` composes `read_open` (the bytes edge in
every environment, with nothing assumed of the message runner) with `Reader.reader_stage` (SolidCore's
checked Reader, type checked from `reader.sol`'s solc AST by the kernel, refines solar's first lowered
MIR in every open world that fits, and runs to an answer there). What is left in the statement:
`AssembleCallPre.EcrecoverAgree` (SolidCore's and EthLib's ECRECOVER agree, used only when the callee
is address 1) and `CalleesRunOpen` (the run's STATICCALL goes to code, or to ECRECOVER priced). The
world the conclusion names fits (`AssembleCallOpen.Fits`) and is a run's world
(`AssembleCallOpen.RunWorld`: each answer is the flag and output of a callee frame EthLib's runner
gave); it is not yet tied to the environment's state at the call (see `AssembleCallOpen.RunWorld`). -/

namespace SolarTV.Export.Reader.Open

open SolarTV SolidCore.Refinement SolidCore.Refinement.Solar

/-- **Every result of Reader's exact bytecode in every environment is SolidCore's checked Reader's
result in some fitting open world (its answers are some EthLib callee frames' outputs, not tied to this
environment's callee, so the returned word is not pinned), or a failure that changes nothing**, at
every gas below `2 ^ 256`, for every valid call whose STATICCALL goes to code or ECRECOVER
(`CalleesRunOpen`), under `EcrecoverAgree`. -/
theorem read_final (hagree : AssembleCallPre.EcrecoverAgree) :
    ∃ c, SolidCore.Verify.VC.Reader.contract? = .ok c ∧
      ∀ env : Shapes.TargetEnv, env.WF → ∀ gas, gas < 2 ^ 256 → ∀ call, Valid call →
        AssembleCallOpen.CalleesRunOpen env gas Ctx.code call →
        ∀ obs, Shapes.Target.runWithIn env gas Ctx.code call = some obs →
          (∃ W : World, W.Open ∧ AssembleCallOpen.Fits W ∧ AssembleCallOpen.RunWorld gas W ∧
            Source.runIn W SolidCore.Verify.VC.Reader.fuel c call = some obs) ∨
          Shapes.Inert call obs := by
  obtain ⟨c, hc, hstage, htotal⟩ := SolidCore.Refinement.Reader.reader_stage
  exact ⟨c, hc, read_open SolidCore.Verify.VC.Reader.fuel c hagree
    (fun W hW hF call hv => htotal W hW hF.1 hF.2 call hv)
    (fun o W hW hF hA => hstage W hW hF.1 hF.2 o hA)⟩

/-- info: 'SolarTV.Export.Reader.Open.read_final' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms read_final

end SolarTV.Export.Reader.Open

import reader.Open.Bytes
import reader.Proofs.Stages

/-! Reader's external-call target in every environment. `Reader.read(IOracle o)` returns
`o.price() + 1`, one STATICCALL to an address the caller names. Everything from solar's first
lowered MIR to the exact bytecode is proved here for every callee (any code at any other address,
`Shapes.TargetEnv`), with nothing assumed of the message runner. The world the conclusion names is
a run's world (`AssembleCallOpen.RunWorld`): each answer to a static call to code is the flag and
output of a callee frame EthLib's runner of messages gave, of fewer than `2 ^ 256` bytes
(`AssembleCallOpen.Fits`). The statement names what the source side owes: the SolidCore source stage
of `read` in every open world that fits, under `CallsAgree` (`source`), and its totality there
(`total`). `Fits` is needed: SolidCore decodes a call's return data at its full length, the EVM at
its length modulo `2 ^ 256`, so with no bound on the answer's size the stage is false. -/

namespace SolarTV.Export.Reader.Open

open SolarTV SolidCore.Refinement SolidCore.Refinement.Solar

/-- The calls of `read(address)` with a clean address argument that is not the contract itself
(no reentrant call into itself, the non-reentrancy premise), no value, from any storage. -/
def Valid (call : Call) : Prop :=
  ∃ a σ, a < 2 ^ 160 ∧ a ≠ selfAddress ∧
    call = { calldata := Abi.calldata 0xa087a87e [a], callvalue := 0, storage := σ }

theorem valid_inhabited : ∃ call, Valid call :=
  ⟨_, 0xC0, [], by decide, by decide, rfl⟩

/-- **Reader's exact bytecode in every environment, from its source stage in the worlds that fit.**
For every environment of other accounts (any code: the callee's success flag and return data are
whatever EthLib computes), every gas below `2 ^ 256` and every valid call whose STATICCALL goes to
code or to ECRECOVER priced (`CalleesRunOpen`), under `EcrecoverAgree`: every result of the bytes is
SolidCore's result in some open world that fits, whose answers are some callee frames' outputs
(existential: not tied to this environment's callee), or a
failure that changes nothing. Nothing is assumed of the message runner. -/
theorem read_open (fuel : Nat) (c : SolidCore.Solidity.TypeCheck.CheckedContract)
    (hagree : AssembleCallPre.EcrecoverAgree)
    (total : ∀ W : World, W.Open → AssembleCallOpen.Fits W → ∀ call, Valid call →
      (Source.runIn W fuel c call).isSome)
    (source : ∀ o W, W.Open → AssembleCallOpen.Fits W → CallsAgree o W →
      Stage (solidCoreIn W fuel) (mirSem o) c SolarTV.Export.Reader.stage0 Valid) :
    ∀ env : Shapes.TargetEnv, env.WF → ∀ gas, gas < 2 ^ 256 → ∀ call, Valid call →
      AssembleCallOpen.CalleesRunOpen env gas Ctx.code call →
      ∀ obs, Shapes.Target.runWithIn env gas Ctx.code call = some obs →
        (∃ W : World, W.Open ∧ AssembleCallOpen.Fits W ∧ AssembleCallOpen.RunWorld gas W ∧
          Source.runIn W fuel c call = some obs) ∨ Shapes.Inert call obs :=
  AssembleCallOpen.open_equiv_run (mirSem := mirSem) (m := fun _ => SolarTV.Export.Reader.stage0)
    (q := SolarTV.Export.Reader.evm7) total source
    (fun o => (SolarTV.Milestone.Reader.reader_mir_to_evmir o).mono fun _ _ => trivial)
    (fun env hwf gas hgas call hv hrun => by
      obtain ⟨o, W, hW, hF, hR, hA, -, hwi⟩ := Ctx.bytecode_run Valid hagree env hwf gas hgas call hv hrun
      exact ⟨o, W, hW, hF, hR, hA, hwi⟩)

/-- info: 'SolarTV.Export.Reader.Open.read_open' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms read_open

end SolarTV.Export.Reader.Open

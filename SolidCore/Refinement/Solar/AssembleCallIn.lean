import SolidCore.Refinement.Solar.AssembleCtxCall
import SolidCore.Refinement.Solar.AssembleCallStaticRunner

/-!
# STATICCALLs to the bytecode without the refuted runner hypothesis

The checker's per-run theorems for code with STATICCALLs (`AssembleCallSeg.runs_of_checkCB`,
`AssembleCtx.runs_of_checkXB`) assume `AssembleCallSeg.StaticRunner`: every message the runner
ends has an output of fewer than `2 ^ 256` bytes (`AssembleCallCut.OutputFits`). That is false:
the IDENTITY precompile returns its data, so a message with `2 ^ 256` bytes of data refutes it
(`AssembleNoCall.not_forall_lt_staticRunner`), and every theorem assuming it is vacuous.

A STATICCALL cut only needs the output bound for the message the frame sends, whose data is a range
of its memory of `inSize < 2 ^ 256` bytes (`AssembleCallCut.data_lt_of_read`). So the cut, the
segments and the blocks now ask `AssembleCallCut.StaticOkIn` of the runner, with
`OutputFitsIn`: **a message with fewer than `2 ^ 256` bytes of data ends with fewer than
`2 ^ 256` bytes of output**. IDENTITY does not refute it (its output is its data); a frame of code
returns at most a `U256` size from memory, and the other precompiles return fixed sizes or a length
read from a word of their data. It stays a named hypothesis (`OutputRunnerIn`), not derived here.

* `StaticOkEIn`, `OutputRunnerIn`, `staticOkEIn_of`: what the runner meets, from
  `AssembleCall.meets_static` (proved), `AssembleCallStaticRunner.meets_staticNoLogs` (proved),
  `AssembleCallPre.meets_ecrecover` (proved) and `OutputRunnerIn` (named).
* `CalleesRunIn`: `AssembleCallSeg.CalleesRunR` over the same runner premise: each STATICCALL of
  the run calls code (not a precompile address), or ECRECOVER with its price passed on.
* `runs_of_checkXB_in`, `assembly_of_checkXB_in`, `assembly_of_checkXB_norm_in`: the
  checker with contexts' theorems under `OutputRunnerIn`, `AssembleCallPre.EcrecoverAgree` and
  `CalleesRunIn`, every one of them in the statement.
-/

namespace SolidCore.Refinement.Solar.AssembleCallIn

open SolarTV SolarTV.Machine SolidCore.Refinement SolidCore.Refinement.Witness SolidCore.Refinement.Final
open SolidCore.Refinement.Solar.Assemble SolidCore.Refinement.Solar.RunOracle
open SolidCore.Refinement.Solar.AssembleCut SolidCore.Refinement.Solar.AssembleEffects
open SolidCore.Refinement.Solar.AssembleLoop SolidCore.Refinement.Solar.AssembleRun
open SolidCore.Refinement.Solar.AssembleRunLoop
open SolidCore.Refinement.Solar.AssembleCall SolidCore.Refinement.Solar.AssembleCallWorld
open SolidCore.Refinement.Solar.AssembleCallCut SolidCore.Refinement.Solar.AssembleDyn
open SolidCore.Refinement.Solar.AssembleCallSeg SolidCore.Refinement.Solar.AssembleCtx
open EthLib.Base EthLib.Execution EthLib.Execution.Evm EthLib.Execution.Evm.Logic

/-- What the runner's callee frames meet: `StaticOkIn` and EthLib's ECRECOVER on priced messages. -/
def StaticOkEIn (caller : Evm .fusaka Nat) (m : Message .fusaka) (child : Evm .fusaka Nat) : Prop :=
  StaticOkIn caller m child ∧ AssembleCallPre.EcrecoverRuns caller m child

/-- **Named hypothesis on the runner of messages**: a message with fewer than `2 ^ 256` bytes of
data ends with fewer than `2 ^ 256` bytes of output (`OutputFitsIn`). -/
def OutputRunnerIn (gas : Nat) : Prop :=
  Meets (bound := gas) OutputFitsIn (processRunner .fusaka (Meter := Nat) gas)

/-- The refuted hypothesis implies this one: `OutputRunnerIn` is weaker than `OutputRunner`. -/
theorem outputRunnerIn_of {gas : Nat} (h : AssembleCallStaticRunner.OutputRunner gas) :
    OutputRunnerIn gas :=
  ⟨fun a b c d e _ => h.ok a b c d e, h.aborts⟩

theorem staticOkEIn_of (gas : Nat) (h : OutputRunnerIn gas) :
    Meets (bound := gas) StaticOkEIn (processRunner .fusaka (Meter := Nat) gas) :=
  ⟨fun a b c d e => ⟨⟨(meets_static gas).ok a b c d e,
      (AssembleCallStaticRunner.meets_staticNoLogs gas).ok a b c d e, h.ok a b c d e⟩,
    (AssembleCallPre.meets_ecrecover gas).ok a b c d e⟩, h.aborts⟩

/-- **Named hypothesis on a run of the bytecode**: when it succeeds, each of its STATICCALLs calls
code, or ECRECOVER with no delegation at address 1 and at least 3000 gas passed on (`PreRun`). -/
def CalleesRunIn (gas : Nat) (code : ByteArray) (call : Call) : Prop :=
  ∀ r, processMessage (Meter := Nat) .fusaka (Final.Target.messageWith gas code call)
      (SolidCore.Refinement.Target.preState code call) Substate.empty = .ok r → r.1.error = none →
    CalleesOkR code (Final.Target.messageWith gas code call) StaticOkEIn gas
      (processRunner .fusaka (Meter := Nat) gas) r.1

theorem calleesOk_of_in (hagree : AssembleCallPre.EcrecoverAgree) {gas : Nat} {code : ByteArray}
    {call : Call} (h : CalleesRunIn gas code call) :
    ∀ r, processMessage (Meter := Nat) .fusaka (Final.Target.messageWith gas code call)
      (SolidCore.Refinement.Target.preState code call) Substate.empty = .ok r → r.1.error = none →
    CalleesOk code (Final.Target.messageWith gas code call) StaticOkEIn gas
      (processRunner .fusaka (Meter := Nat) gas) r.1 := by
  intro r hr he e within pc asked addr inOff inSize outOff outSize S M g st ss rd hat hlt hb hrun
  exact (h r hr he hat hlt hb hrun).imp id fun ⟨a, b, c, d⟩ => ⟨a, hagree, b, c, d⟩

/-- **EVM IR to bytecode, run by run, for code with STATICCALLs, under hypotheses that hold**:
`AssembleCtx.runs_of_checkXB` with `OutputRunnerIn` for the refuted `StaticRunner`. -/
theorem runs_of_checkXB_in {p : Assemble.Program} {code : ByteArray} {cx : CtxCert}
    (hc : checkXB p code cx = true) (codes : SolidCore.Solidity.Shared.Account.BytesMap)
    (gas : Nat) (hgas : gas < 2 ^ 256) (call : Call) (hO : OutputRunnerIn gas)
    (hagree : AssembleCallPre.EcrecoverAgree) (hQ : CalleesRunIn gas code call) :
    ∃ T, Within (evmirSem (OS codes T)) (ethLibWith gas) p code (· = call) := by
  obtain ⟨G, hseg, hcount, hneed0⟩ := globXB_of_checkXB hc
  refine within_of_advancesQ (OS codes) StaticOkEIn
    (CalleesOk code (Final.Target.messageWith gas code call) StaticOkEIn)
    (fun ss0 => EntXS codes p cx code (Final.Target.messageWith gas code call) ss0)
    (fun y e => AssembleLoop.meas p cx.base e.gas y.1) (staticOkEIn_of gas hO)
    (calleesOk_of_in hagree hQ) (fun st' ss' R => ?_)
    (fun ss0 T x evm hE => advances_checkXS_in G codes rfl
      (by simp [Final.Target.messageWith, SolidCore.Refinement.Target.message]) rfl rfl rfl rfl rfl
      hgas (by show 0 + 1 ≤ 1024; decide) T x evm hE (fun _ _ _ h => h.1))
  have h0n : 0 < p.blocks.length + 1 := by omega
  have hsame := certAt_same cx (p.blocks.length + 1) 0 0
  have hn0 : (certAt cx (p.blocks.length + 1) 0 0).need 0 = (cx.at 0 0).need := by
    rw [certAt_need h0n, pick_of_exit (exitCtx_self cx 0 0)]
  have hseg0 : Seg (bytesOf code) (certAt cx (p.blocks.length + 1) 0 0).offset 0
      (lowerFrom p (certAt cx (p.blocks.length + 1) 0 0) 0 (p.blocks.drop 0)) code.size := by
    rw [hsame.offset, lowerFrom_congr hsame.2.1, List.drop_zero]
    exact hseg
  refine ⟨certAt cx (p.blocks.length + 1) 0 0, maxsAt cx (p.blocks.length + 1) 0 0, hsame,
    ⟨⟨[], 0, .empty, st', ss', .empty, Nat.zero_le _, fun _ => ⟨by simp [hn0, hneed0], by simp⟩,
    SR.nil _ _, hseg0, by simp, memRel_initial, R, ?_⟩, rfl, ⟨rfl, rfl, rfl⟩,
    fun T'' _ => rdRel_nil codes T'', ?_⟩, fun _ => ⟨0, hcount,
    hn0, by rw [maxsAt_max h0n, pick_of_exit (exitCtx_self cx 0 0)],
    by rw [certAt_entry h0n, pick_of_exit (exitCtx_self cx 0 0)], LabOk.empty _⟩⟩
  have hcode : (Final.Target.messageWith gas code call).code = code := rfl
  · exact ⟨by simp [startFrame, hcode], by simp [startFrame, hcode], rfl, rfl, rfl, rfl, rfl, rfl, rfl,
      rfl, rfl, rfl, rfl⟩
  · have h0 : memoryGasCost 0 = 0 := by rw [memoryGasCost_eq]; simp [wordCount, ceil32, WORD_BYTES]
    simp only [startFrame, ByteArray.size_empty, h0, Nat.zero_add]
    exact le_refl _

/-- **The assembly premise of `holds_of_runs` / `equiv_of_runs` for code with STATICCALLs**,
under `OutputRunnerIn`, `EcrecoverAgree` and `CalleesRunIn`: below `2 ^ 256` gas, for every
call in scope, an oracle and an open world that agree (the run's table answers its static calls),
under which the EVM IR gives the bytecode's result or a failure that changes nothing. -/
theorem assembly_of_checkXB_in {p : Assemble.Program} {code : ByteArray} {cx : CtxCert}
    (hc : checkXB p code cx = true) (codes : SolidCore.Solidity.Shared.Account.BytesMap)
    (scope : Call → Prop) (hO : ∀ gas, gas < 2 ^ 256 → OutputRunnerIn gas)
    (hagree : AssembleCallPre.EcrecoverAgree)
    (hQ : ∀ gas call, scope call → CalleesRunIn gas code call) :
    ∀ gas, gas < 2 ^ 256 → ∀ call, scope call → ∃ (o : Oracle) (W : World), W.Open ∧
      CallsAgree o W ∧ CertOk cx.base o ∧ Within (evmirSem o) (ethLibWith gas) p code (· = call) := by
  intro gas hgas call hs
  obtain ⟨T, hT⟩ := runs_of_checkXB_in hc codes gas hgas call (hO gas hgas) hagree (hQ gas call hs)
  exact ⟨OS codes T, tabWorld T.oks T.outs codes, (OS_agree codes T).1, (OS_agree codes T).2,
    OS_ok codes cx.base T, hT⟩

/-- `assembly_of_checkXB_in` for a program whose RETURNDATASIZE is the stack operation solar's
export writes (`AssembleCtx.norm`). -/
theorem assembly_of_checkXB_norm_in {p : Assemble.Program} {code : ByteArray} {cx : CtxCert}
    (hc : checkXB (norm p) code cx = true) (codes : SolidCore.Solidity.Shared.Account.BytesMap)
    (scope : Call → Prop) (hO : ∀ gas, gas < 2 ^ 256 → OutputRunnerIn gas)
    (hagree : AssembleCallPre.EcrecoverAgree)
    (hQ : ∀ gas call, scope call → CalleesRunIn gas code call) :
    ∀ gas, gas < 2 ^ 256 → ∀ call, scope call → ∃ (o : Oracle) (W : World), W.Open ∧
      CallsAgree o W ∧ CertOk cx.base o ∧ Within (evmirSem o) (ethLibWith gas) p code (· = call) := by
  intro gas hgas call hs
  obtain ⟨o, W, hW, hA, hok, hwi⟩ := assembly_of_checkXB_in hc codes scope hO hagree hQ gas hgas call hs
  exact ⟨o, W, hW, hA, hok, within_norm hwi⟩

/-- info: 'SolidCore.Refinement.Solar.AssembleCallIn.assembly_of_checkXB_norm_in' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms assembly_of_checkXB_norm_in

end SolidCore.Refinement.Solar.AssembleCallIn

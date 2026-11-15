import SolidCore.Refinement.Solar.AssembleCallSeg
import SolidCore.Refinement.Solar.AssembleCallStatic

/-!
# EIP-214 discharged: StaticNoLogs is a theorem of EthLib's runner

AssembleCallCut.StaticNoLogs (a static message that succeeds ends with no log) was a named
hypothesis of AssembleCallSeg.StaticRunner. EthLib.Execution.Evm.StaticLogs.meets_staticNoLogs
proves it of the interpreter's runner of messages before Glamsterdam, so at Fusaka:

* meets_staticNoLogs: the runner meets StaticNoLogs at every bound (proved, no hypothesis).
* OutputRunner: what is left of StaticRunner, the named hypothesis that each callee's output
  has fewer than 2 ^ 256 bytes (AssembleCallCut.OutputFits; not derived here).
* holds_of_checkCB_out: holds_of_checkCB_named with StaticRunner replaced by OutputRunner, so the
  final theorem names OutputRunner, EcrecoverAgree and CalleesRunR and nothing about logs.
-/

namespace SolidCore.Refinement.Solar.AssembleCallStaticRunner

open SolarTV SolarTV.Machine SolidCore.Refinement SolidCore.Refinement.Witness SolidCore.Refinement.Final
open SolidCore.Refinement.Solar.Assemble SolidCore.Refinement.Solar.AssembleCallCut
open SolidCore.Refinement.Solar.AssembleCallSeg SolidCore.Refinement.Solar.AssembleCut
open EthLib.Base EthLib.Execution EthLib.Execution.Evm EthLib.Execution.Evm.Logic

/-- **EIP-214, proved**: at Fusaka, the interpreter's runner of messages ends every static
message that succeeds with no log, at every bound on the gas of messages. -/
theorem meets_staticNoLogs (gas : Nat) :
    Meets (bound := gas) StaticNoLogs (processRunner .fusaka (Meter := Nat) gas) :=
  EthLib.Execution.Evm.StaticLogs.meets_staticNoLogs (by decide) gas

/-- **Named hypothesis on the runner of messages**: each callee's output has fewer than
2 ^ 256 bytes (OutputFits), the part of StaticRunner not derived. -/
def OutputRunner (gas : Nat) : Prop :=
  Meets (bound := gas) OutputFits (processRunner .fusaka (Meter := Nat) gas)

/-- StaticRunner from OutputRunner alone: its StaticNoLogs half is meets_staticNoLogs. -/
theorem staticRunner_of_output {gas : Nat} (h : OutputRunner gas) : StaticRunner gas :=
  ⟨fun a b c d e => ⟨(meets_staticNoLogs gas).ok a b c d e, h.ok a b c d e⟩, h.aborts⟩

/-- **holds_of_checkCB_named without the EIP-214 hypothesis**: the source's specification at
every open world, its totality, the stages and the checker give the specification of the exact
bytecode at every gas below 2 ^ 256, under the named hypotheses OutputRunner (callee outputs
below 2 ^ 256 bytes), AssembleCallPre.EcrecoverAgree and CalleesRunR. -/
theorem holds_of_checkCB_out {St : Type} {fuel : Nat}
    {mirSem : SolarTV.Machine.Oracle → Sem} {c : SolidCore.Solidity.TypeCheck.CheckedContract}
    {mir : ∀ o, (mirSem o).Prog} {p : Assemble.Program} {code : ByteArray} {cert : Cert}
    {mx : List Nat} {spec : Final.ContractSpec St}
    (source : ∀ W : World, W.Open → Final.Holds (solidCoreIn W fuel) c spec)
    (fin : ∀ W : World, W.Open → ∀ call, spec.Calls call → (Source.runIn W fuel c call).isSome)
    (lowering : ∀ o W, CallsAgree o W → Stage (solidCoreIn W fuel) (mirSem o) c (mir o) spec.Calls)
    (backend : ∀ o, Stage (mirSem o) (evmirSem o) (mir o) p spec.Calls)
    (hc : checkCB p code cert mx = true) (codes : SolidCore.Solidity.Shared.Account.BytesMap)
    (hO : ∀ gas, OutputRunner gas) (hagree : AssembleCallPre.EcrecoverAgree)
    (hQ : ∀ gas call, spec.Calls call → CalleesRunR gas code call)
    (gas : Nat) (hgas : gas < 2 ^ 256) : Final.Holds (Final.ethLibWith gas) code spec :=
  holds_of_checkCB_named source fin lowering backend hc codes
    (fun gas => staticRunner_of_output (hO gas)) hagree hQ gas hgas

/-- info: 'SolidCore.Refinement.Solar.AssembleCallStaticRunner.meets_staticNoLogs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms meets_staticNoLogs

/-- info: 'SolidCore.Refinement.Solar.AssembleCallStaticRunner.holds_of_checkCB_out' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms holds_of_checkCB_out

end SolidCore.Refinement.Solar.AssembleCallStaticRunner

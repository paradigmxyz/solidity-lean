import SolidCore.Refinement.Solar.AssembleNoCall
import SolidCore.Refinement.Solar.AssembleDynExample
import SolidCore.Refinement.Solar.AssembleCallExample

/-!
# The call-free check on examples, by evaluation

* Positive: `AssembleDynExample`'s bytecode (MLOAD at an offset the call data names) passes
  `callFree` and has no `0xfa` byte; the checker with STATICCALLs accepts its program under a
  certificate that allows calls, and `runs_shape_of_checkCB_callFree` gives its per-run theorem with
  no hypothesis on the runner; `CalleesRun` holds at every gas and call.
* Negative: `AssembleCallExample`'s bytecode (a STATICCALL to code) fails `callFree` and
  `noFaByte`, and so does `AssembleDynExample`'s with its MLOAD byte replaced by STATICCALL.
-/

namespace SolidCore.Refinement.Solar.AssembleNoCallExample

open SolarTV SolarTV.Machine SolidCore.Refinement SolidCore.Refinement.Final
open SolidCore.Refinement.Solar SolidCore.Refinement.Solar.AssembleCut
open SolidCore.Refinement.Solar.AssembleNoCall SolidCore.Refinement.Solar.RunOracle SolidCore.Refinement.Witness

theorem dyn_callFree : callFree AssembleDynExample.code = true := by decide +kernel

theorem dyn_noFaByte : noFaByte AssembleDynExample.code = true := by decide +kernel

/-- The checker with STATICCALLs accepts the call-free program under a certificate that allows
calls. -/
theorem dyn_checkCB : checkCB AssembleDynExample.prog AssembleDynExample.code
    { AssembleDynExample.cert with calls := true } AssembleDynExample.maxs = true := by
  decide +kernel

/-- Its per-run theorem with no runner hypothesis. -/
theorem dyn_runs : ∀ gas, gas < 2 ^ 256 → ∀ call, True → ∃ o : Oracle,
    (CertOk { AssembleDynExample.cert with calls := true } o ∧ ∃ W : World, W.Open ∧ CallsAgree o W) ∧
    Within (evmirSem o) (ethLibWith gas) AssembleDynExample.prog AssembleDynExample.code (· = call) :=
  runs_shape_of_checkCB_callFree dyn_checkCB dyn_callFree (fun _ => True)

theorem dyn_calleesRun (gas : Nat) (call : Call) :
    AssembleCallSeg.CalleesRun gas AssembleDynExample.code call :=
  calleesRun_of_noFaByte dyn_noFaByte gas call

/-- STATICCALL (0xfa) in place of MLOAD. -/
def dynStatic : ByteArray := ⟨#[0x5f, 0x35, 0xfa, 0x5f, 0x52, 0x60, 0x20, 0x5f, 0xf3]⟩

theorem dynStatic_not_callFree : callFree dynStatic = false := by decide +kernel

/-- 0xfa only as a PUSH1 immediate: call-free, though not free of the byte. -/
def dynPushFa : ByteArray := ⟨#[0x60, 0xfa, 0x50, 0x5f, 0x35, 0x51, 0x5f, 0x52, 0x60, 0x20, 0x5f, 0xf3]⟩

theorem dynPushFa_callFree : callFree dynPushFa = true := by decide +kernel

theorem dynPushFa_not_noFaByte : noFaByte dynPushFa = false := by decide +kernel

theorem call_not_callFree : callFree AssembleCallExample.code = false := by decide +kernel

theorem call_not_noFaByte : noFaByte AssembleCallExample.code = false := by decide +kernel

/-- info: 'SolidCore.Refinement.Solar.AssembleNoCallExample.dyn_runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms dyn_runs

end SolidCore.Refinement.Solar.AssembleNoCallExample

import SolidCore.Refinement.Solar.AssembleNoCall
import Contracts.UniswapV2.ERC20.Runtime

/-!
# UniswapV2ERC20's exact runtime bytes and the call-free route

`Runtime.code` is the runtime bytecode solar emits for the port (`-Ogas --evm-version osaka`),
written at build time by `scripts/verify/uniswap_v2_runtime.sh` (not committed). The kernel evaluates
`AssembleNoCall`'s call-free checks on it, and both **fail**:

* `runtime_not_callFree`: the linear decode has instructions `callFree` refuses
  (`NoCallAt`: a STATICCALL at 903, permit's call to ECRECOVER, and return-data reads at 1158, 1161 and
  1162; `NoCallOnly`: no other message-sending instruction). So
  `AssembleNoCall.holds_of_checkCB_callFree` and `assembly_of_checkXB_norm_callFree` do not apply to
  UniswapV2ERC20's runtime, and the call-free route cannot remove `StaticRunner`/`CalleesRun` there.
* `runtime_not_noFaByte`: `calleesRun_of_noFaByte` does not apply either.

Each kernel evaluation of the 1183-byte decode peaks near 4.6 GB, so the checks are split across
the `NoCall*` modules, one process each under `-M 6000`.
-/

namespace SolidCore.Spec.UniswapV2.ERC20.NoCall

open SolidCore.Refinement.Solar.AssembleNoCall SolidCore.Refinement.Solar.Assemble
open SolarTV.Assembly

abbrev code : ByteArray := Runtime.code

/-- The decoded instructions of `c`, as `callFree` reads them. -/
def decoded (c : ByteArray) : List (Nat × SolarTV.Assembly.Instr) := decodeFrom (bytesOf c) c.size 0

/-- The counters of the instructions `callFree` refuses. -/
def refusedAt (c : ByteArray) : List Nat :=
  (decoded c).filterMap fun x => if instrFree x.2 then none else some x.1

/-- **The exact runtime fails the call-free check.** -/
theorem runtime_not_callFree : callFree code = false := by decide +kernel

/-- info: 'SolidCore.Spec.UniswapV2.ERC20.NoCall.runtime_not_callFree' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms runtime_not_callFree

end SolidCore.Spec.UniswapV2.ERC20.NoCall

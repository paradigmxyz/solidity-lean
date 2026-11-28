import Verify.Lifecycle.CreationFrame
import Verify.Lifecycle.Route
import Verify.LoopSource.Equiv.CounterSame

/-!
# Counter's creation with the pinned words `[8]`

The generic creation frame's check (`Verify.Lifecycle.Creation.check`) of solar's init code for
Counter (`CounterCtor.counterInit`, 307 bytes, the freeze-head producer's) with the words `[8]`:
EthLib's creation installs `runtime` and leaves storage `[(1, 8)]`. Evaluated by the kernel
(`kernel_decide`), as the driver's lifecycle certificate does.
-/

namespace Verify.LoopSource.Equiv.CounterDeploy8
open EthLib.Base EthLib.Execution EthLib.Execution.Evm EthLib.Execution.Evm.Logic
open SolidCore.Refinement Verify.Lifecycle Verify.Lifecycle.Creation

/-- Box-only: the kernel's creation-frame check exceeds 6000 MB on the hosted Hand. -/
def frameFuel : Nat := 4096

def checkB : Bool := check frameFuel (initArgs Verify.LoopSource.Equiv.CounterCtor.counterInit [8]) Verify.LoopSource.Equiv.CounterSame.runtime [(1, 8)]

kernel_decide checkB_eq checkB

theorem deploys : Deploys (initArgs Verify.LoopSource.Equiv.CounterCtor.counterInit [8]) Verify.LoopSource.Equiv.CounterSame.runtime [(1, 8)] :=
  deploys_of_check frameFuel checkB_eq

end Verify.LoopSource.Equiv.CounterDeploy8

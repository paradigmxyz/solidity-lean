import SolidCore.Refinement.Kernel
import SolidCore.Refinement.Abi
import SolidCore.Refinement.Dirty.Source
import SolidCore.Refinement.Wide.Refines

/-!
# Shared kernel copies of the type checker and the interpreter

The copies (`SolidCore.Refinement.Kernel`) of the definitions every corpus contract's
shape checks reach: the type checker and elaborator behind `contract?`, and the
interpreter behind `deployedStorage`, `deployedEmpty` and `Dirty.fnShapeOk`. Each
contract's module copies only what is its own, and anew what reaches the selectors it
reads from its table (`kernel_rfl … using selector_eq`, `SolidCore.Refinement.KernelRfl`).
-/

namespace SolidCore.Refinement.KernelCopies

open SolidCore.Refinement

set_option maxHeartbeats 0

kernel_clone SolidCore.Solidity.TypeCheck.CheckedInput.contract
kernel_clone SolidCore.Solidity.TypeCheck.checkedInputSourceUnit
kernel_clone SolidCore.Refinement.Abi.deployedStorage
kernel_clone SolidCore.Refinement.Wide.deployedEmpty
kernel_clone SolidCore.Refinement.Dirty.fnShapeOk

end SolidCore.Refinement.KernelCopies

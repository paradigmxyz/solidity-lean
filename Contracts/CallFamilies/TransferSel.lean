import SolidCore.Solidity.ABI
import SolidCore.Refinement.KernelRfl

/-!
# The selector of transfer(address,uint256), by Keccak-256 in the kernel

pay's TRANSFER constant is bytes4(keccak256("transfer(address,uint256)")). transfer_sel_eq
evaluates SolidCore's selector (Keccak-256 of the signature's bytes, first four bytes) in the
kernel once; transfer_word_eq shows the word solar's MIR stores before the call's arguments is
that selector in the top four bytes.
-/

namespace SolidCore.Verify.VC.Calls

/-- The selector of transfer(address,uint256), by Keccak-256 of its signature. -/
def selTransfer : SolidCore.Solidity.Shared.Word :=
  SolidCore.Solidity.Source.ABI.selectorFromSignature "transfer(address,uint256)"

kernel_rfl transfer_sel_eq selTransfer 2835717307

/-- The selector word solar's MIR stores at the head of transfer's input. -/
theorem transfer_word_eq :
    (76450787359836037641860180984291677749980919077056822294353438043884394381312 : Nat) =
      selTransfer * 2 ^ 224 := by
  rw [transfer_sel_eq]; rfl

/-- info: 'SolidCore.Verify.VC.Calls.transfer_word_eq' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms transfer_word_eq

end SolidCore.Verify.VC.Calls

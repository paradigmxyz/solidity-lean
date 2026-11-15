import SolidCore.Refinement.Evm.Symex
import Verify.Eval.H.Mutation

/-!
# Mutation tests: EthLib's `evm_step` on a three-opcode program (lane H)

`PUSH1 1; PUSH1 2; ADD; STOP` (bytes `60 01 60 02 01 00`) as a `NatCode` number, stepped with
EthLib's `evm_step` and closed with `evm_stop`, the engine `dirty_symex` (SolidCore/Refinement/Evm/
Symex.lean) runs per opcode. The original: from any frame at pc 0 with at least 9 gas (3 + 3 + 3),
the frame halts at STOP with `g - 9` gas left. The mutants:

* gas exhaustion: 8 gas, one below the price of the three steps, must not step through;
* wrong price: the same run claimed with `g - 8` left;
* a halt claimed one opcode early (the program is cut before STOP, so ADD is at the end, and
  the run instead halts past the end with only two pushes paid);
* a different program (`PUSH1 1; PUSH1 2; ADD; ADD; STOP`), whose second ADD underflows the stack.
-/

namespace Verify.Eval.H.EvmMutants

open EthLib.Base EthLib.Execution EthLib.Execution.Evm EthLib.Execution.Evm.Logic GasCosts

def prog : ByteArray := NatCode.ofNat 0x600160020100 6
def progAddAdd : ByteArray := NatCode.ofNat 0x60016002010100 7

#mutation_check "evm_push_push_add_stop" :
    ∀ (message : Message .fusaka) (st : State.TransactionState) (ss : Substate) (rd : ByteArray)
      (g : Nat), 9 ≤ g →
      Spec .fusaka (At prog message 0 [] .empty g st ss rd) (Halted false .empty (g - 9) st ss)
  rejects [
    "gas_exhaustion_8" => ∀ (message : Message .fusaka) (st : State.TransactionState) (ss : Substate)
      (rd : ByteArray) (g : Nat), 8 ≤ g →
      Spec .fusaka (At prog message 0 [] .empty g st ss rd) (Halted false .empty (g - 9) st ss),
    "gas_exactly_8" => ∀ (message : Message .fusaka) (st : State.TransactionState) (ss : Substate)
      (rd : ByteArray),
      Spec .fusaka (At prog message 0 [] .empty 8 st ss rd) (Halted false .empty 0 st ss),
    "wrong_price" => ∀ (message : Message .fusaka) (st : State.TransactionState) (ss : Substate)
      (rd : ByteArray) (g : Nat), 9 ≤ g →
      Spec .fusaka (At prog message 0 [] .empty g st ss rd) (Halted false .empty (g - 8) st ss),
    "add_underflow" => ∀ (message : Message .fusaka) (st : State.TransactionState) (ss : Substate)
      (rd : ByteArray) (g : Nat), 12 ≤ g →
      Spec .fusaka (At progAddAdd message 0 [] .empty g st ss rd) (Halted false .empty (g - 12) st ss) ]
  using (intros; evm_step [prog, progAddAdd]; evm_step [prog, progAddAdd]; evm_step [prog, progAddAdd]; evm_stop [prog, progAddAdd])

end Verify.Eval.H.EvmMutants

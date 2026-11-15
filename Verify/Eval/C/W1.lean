import Verify.Eval.C.Stepper
import Verify.Eval.Common.Measure
import SolidCore.Refinement.Bytecode.W1

/-!
# Lane C targets on solar's W1 runtime bytecode

Each statement is stated once as a `def` and proved twice: with the baseline (EthLib's `evm_step`,
Symex's `symex_one`) and with the lane C stepper `evm_sym`.
-/

open EthLib.Base EthLib.Execution EthLib.Execution.Evm EthLib.Execution.Evm.Logic GasCosts
open SolidCore.Refinement.Evm.Logic SolidCore.Refinement.Evm.Symex
open SolidCore.Refinement.Bytecode.W1

namespace Verify.Eval.C.W1

/-- Straight line, pc 0x1a to 0x24 (PUSH1 01, PUSH1 04, CALLDATALOAD, ADD, DUP1, ISZERO, PUSH1 2f):
the frame at 0x1a with the selector word `s` reaches the frame at the JUMPI at 0x24. -/
def straightStmt : Prop :=
  ∀ (msg : Message .fusaka) (st : State.TransactionState) (ss : Substate) (s : U256) (g : Nat),
    100 ≤ g →
    Hoare .fusaka
      (At (NatCode.ofNat Main.runtimeNat Main.runtimeSize) msg 0x1a [s] .empty g st ss .empty)
      (At (NatCode.ofNat Main.runtimeNat Main.runtimeSize) msg 0x24
        [0x2f, (if loadWord msg.data 4 32 + 1 = 0 then 1 else 0), loadWord msg.data 4 32 + 1, s]
        .empty (g - 21) st ss .empty)

/-- Branching, from pc 0 with a symbolic message: a call with value, another selector or short
call data reverts with empty output. Three JUMPIs on symbolic conditions; both continuations of
each are explored, and the path on which all three fall through is closed as infeasible. -/
def branchStmt : Prop :=
  ∀ (msg : Message .fusaka) (st : State.TransactionState) (ss : Substate),
    (msg.value ≠ 0 ∨ loadWord msg.data 0 32 >>> 224 ≠ 0xb3de648b ∨ msg.data.size < 36) →
    Spec .fusaka
      (At (NatCode.ofNat Main.runtimeNat Main.runtimeSize) msg 0 [] .empty 10000000 st ss .empty)
      Reverted

set_option maxRecDepth 100000

theorem straight_base : straightStmt := by
  unfold straightStmt
  intro msg st ss s g hg
  iterate 7 evm_step [Main.runtimeNat, Main.runtimeSize]
  exact reshape (by simp [isZero, add] <;> exact if_congr Iff.rfl rfl rfl) rfl (by omega)

/- Baseline for `branchStmt` (not a theorem: it fails). Symex's driver

    all_goals repeat symex_one [Main.runtimeNat, Main.runtimeSize] [] hfork

stops at the first JUMPI (pc 3, condition `msg.value`) with the goal unsolved: every alternative of
`symex_one` fails there, although `jumpi_split` itself applies (checked by hand with the same
`evm_code`/`evm_gas`/`evm_dest` side tactics, log 20261115T042932-C-W1). The split alternative runs
`exfalso; symex_bv` on each branch, whose `bv_omega` on the disjunctive hypothesis reaches the
recursion limit, a runtime exception `try` does not catch, so the alternative fails as a whole.
The lane C stepper refutes the same infeasible leaves with grind in the branch's own state. -/

theorem straight_sym : straightStmt := by
  unfold straightStmt
  evm_sym [Main.runtimeNat, Main.runtimeSize]

theorem branch_sym : branchStmt := by
  unfold branchStmt
  evm_sym [Main.runtimeNat, Main.runtimeSize]

#proof_stats straight_base
#proof_stats straight_sym
#proof_stats branch_sym
#kernel_recheck straight_base
#kernel_recheck straight_sym
#kernel_recheck branch_sym
#print axioms straight_sym
#print axioms branch_sym

end Verify.Eval.C.W1

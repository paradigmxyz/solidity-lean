import Verify.Eval.C.Stepper
import Verify.Eval.C.Fix.BranchNeg64Stmt

/-!
# Lane C: sibling isolation (negative test)

The program (23 bytes):

    00 CALLVALUE  01 DUP1  02 PUSH1 0b  04 JUMPI          split on v = msg.value
    05 ISZERO  06 PUSH1 13  08 JUMPI  09 STOP             fall-through (v = 0): ISZERO v = 1, jumps
    0b JUMPDEST  0c ISZERO  0d PUSH1 13  0f JUMPI  10 STOP taken (v ≠ 0): ISZERO v = 0, stops at 0x10
    13 JUMPDEST  14 PUSH0  15 PUSH0  16 REVERT

`negStmt` (every call reverts) is false: a call with value stops at 0x10. The two siblings of the
first JUMPI carry contradictory path conditions (`v = 0` and `v ≠ 0`), and with
`verify.eval.c.condRewrite` the ISZERO results are rewritten by conditional rules whose side
conditions (`v = 0`, `v ≠ 0`) hold on one sibling only, discharged by grind in that sibling's state.
If any fact of the fall-through sibling reached the taken sibling, the open path at 0x10 would be
refuted (or its ISZERO rewritten to 1) and the proof would go through: `#guard_msgs` pins the one
open path, so the test fails on any leak. `posStmt` (with `msg.value = 0`) is the positive control.
-/

open EthLib.Base EthLib.Execution EthLib.Execution.Evm EthLib.Execution.Evm.Logic
open SolidCore.Refinement.Evm.Symex

namespace Verify.Eval.C.Isolation

def codeNat : Nat := 0x3480600b571560135700005b156013570000005b5f5ffd
def codeSize : Nat := 23

def negStmt : Prop :=
  ∀ (msg : Message .fusaka) (st : State.TransactionState) (ss : Substate),
    Spec .fusaka (At (NatCode.ofNat codeNat codeSize) msg 0 [] .empty 100000 st ss .empty) Reverted

def posStmt : Prop :=
  ∀ (msg : Message .fusaka) (st : State.TransactionState) (ss : Substate), msg.value = 0 →
    Spec .fusaka (At (NatCode.ofNat codeNat codeSize) msg 0 [] .empty 100000 st ss .empty) Reverted

theorem pos_threaded : posStmt := by unfold posStmt; evm_sym [codeNat, codeSize]

set_option verify.eval.c.condRewrite true in
theorem pos_threaded_cond : posStmt := by unfold posStmt; evm_sym [codeNat, codeSize]

set_option verify.eval.c.fresh true in
theorem pos_fresh : posStmt := by unfold posStmt; evm_sym [codeNat, codeSize]

/-- error: evm_sym: 1 open path(s): [no rule applies for opcode 0 at pc 16] -/
#guard_msgs in
example : negStmt := by unfold negStmt; evm_sym [codeNat, codeSize]

/-- error: evm_sym: 1 open path(s): [no rule applies for opcode 0 at pc 16] -/
#guard_msgs in
set_option verify.eval.c.condRewrite true in
example : negStmt := by unfold negStmt; evm_sym [codeNat, codeSize]

/-- error: evm_sym: 1 open path(s): [no rule applies for opcode 0 at pc 16] -/
#guard_msgs in
set_option verify.eval.c.eager true in
example : negStmt := by unfold negStmt; evm_sym [codeNat, codeSize]

/-- error: evm_sym: 1 open path(s): [no rule applies for opcode 0 at pc 16] -/
#guard_msgs in
set_option verify.eval.c.fresh true in
set_option verify.eval.c.condRewrite true in
example : negStmt := by unfold negStmt; evm_sym [codeNat, codeSize]

/-! ## Sibling isolation on a scaling fixture

§BranchNeg64§ (64 opcodes, 5 genuine splits on call-data words, 10 JUMPIs decided by
§msg.value = 0§) ends its all-fall-through path in STOP, so its statement (every path reverts) is
false on exactly that path, which carries the five §word = 0§ path conditions; each taken sibling
carries §word ≠ 0§. If any taken sibling's fact reached the fall-through path, the stepper would
refute it and the proof would go through. The one open path must remain, threaded or fresh. -/

/-- error: evm_sym: 1 open path(s): [no rule applies for opcode 0 at pc 98] -/
#guard_msgs in
example : Verify.Eval.C.Fix.BranchNeg64.stmt := by
  unfold Verify.Eval.C.Fix.BranchNeg64.stmt
  evm_sym [Verify.Eval.C.Fix.BranchNeg64.codeNat, Verify.Eval.C.Fix.BranchNeg64.codeSize]

/-- error: evm_sym: 1 open path(s): [no rule applies for opcode 0 at pc 98] -/
#guard_msgs in
set_option verify.eval.c.eager true in
example : Verify.Eval.C.Fix.BranchNeg64.stmt := by
  unfold Verify.Eval.C.Fix.BranchNeg64.stmt
  evm_sym [Verify.Eval.C.Fix.BranchNeg64.codeNat, Verify.Eval.C.Fix.BranchNeg64.codeSize]

/-- error: evm_sym: 1 open path(s): [no rule applies for opcode 0 at pc 98] -/
#guard_msgs in
set_option verify.eval.c.fresh true in
set_option verify.eval.c.eager true in
example : Verify.Eval.C.Fix.BranchNeg64.stmt := by
  unfold Verify.Eval.C.Fix.BranchNeg64.stmt
  evm_sym [Verify.Eval.C.Fix.BranchNeg64.codeNat, Verify.Eval.C.Fix.BranchNeg64.codeSize]

#print axioms pos_threaded
#print axioms pos_threaded_cond
#print axioms pos_fresh

end Verify.Eval.C.Isolation

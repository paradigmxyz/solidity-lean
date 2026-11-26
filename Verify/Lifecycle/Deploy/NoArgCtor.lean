import Verify.Lifecycle.DeployFrame
import EthLib.Execution.Proofs.Evm.Logic.Copy

/-!
# `NoArgCtor` deploys

The bytecode half of `NoArgCtor`'s lifecycle statement: EthLib runs solar's init code for
tools/certify/examples/lifecycle/NoArgCtor.sol (solar 0479b90a, -Ogas, osaka) to success, returns
exactly its 42-byte runtime code and leaves slot 0 holding 7, by `deploys_of_postS` and one
frame stepped by EthLib's program logic:

    CALLVALUE PUSH1 0x11 JUMPI             ; not payable
    PUSH1 0x07 PUSH0 SSTORE                ; x = 7
    PUSH1 0x2a DUP1 PUSH1 0x15 PUSH0       ; 42 bytes from offset 21 to memory 0
    CODECOPY PUSH0 RETURN                  ; return them

SSTORE is stepped at a price bounded by its most expensive case (`sstore_then`), so the frame
holds for every message the creation sends, whatever its access lists.
-/

open EthLib.Base EthLib.Execution EthLib.Execution.Evm EthLib.Execution.Evm.Logic GasCosts
open SolidCore.Refinement SolidCore.Refinement.Evm.Logic SolidCore.Refinement.Evm.Symex
open SolidCore.Refinement.Evm.Wide

namespace Verify.Lifecycle.Deploy.NoArgCtor

/-- solar's init code, read big-endian. -/
def initNat : Nat := 10715293703241361811014123202645468443465903242712748929245237465904604300910620647577406479277526680434458616347982938898322424376525867602081736515581
def initSize : Nat := 63
def initcode : ByteArray := NatCode.ofNat initNat initSize
def codeNat : Nat := 28639634085878733390356966713628268571794318497599552101260479426727232901636059703017389291200274429
def codeSize : Nat := 42
def code : ByteArray := NatCode.ofNat codeNat codeSize

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
/-- **`NoArgCtor`'s init code deploys its runtime code with slot 0 holding 7.** -/
theorem deploys : Deploys initcode code [(0, 7)] := by
  refine deploys_of_postS initcode code [(0, 7)] ?_
  intro msg hv hd hstat htgt
  evm_step [initcode, initNat, initSize]
  evm_step [initcode, initNat, initSize, hv]
  evm_step [initcode, initNat, initSize, hv]
  evm_step [initcode, initNat, initSize]
  refine' Triple.seq (push0 (by decide) ?lt ?op ?gas ?room) ?n1
  case lt => evm_code [initcode, initNat, initSize]
  case op => evm_code [initcode, initNat, initSize]
  case gas => wide_mem
  case room => evm_room
  all_goals evm_tidy
  refine sstore_then ?lt ?op hstat ?gas (setStorage_ok _ _ ?acc) ?next
  case lt => evm_code [initcode, initNat, initSize]
  case op => evm_code [initcode, initNat, initSize]
  case gas => omega
  case acc => rw [htgt]; exact account_preState _ _
  intro g hg
  evm_step [initcode, initNat, initSize]
  evm_step [initcode, initNat, initSize]
  evm_step [initcode, initNat, initSize]
  refine' Triple.seq (push0 (by decide) ?lt ?op ?gas ?room) ?n2
  case lt => evm_code [initcode, initNat, initSize]
  case op => evm_code [initcode, initNat, initSize]
  case gas => (try wide_mem) <;> omega
  case room => evm_room
  all_goals evm_tidy
  refine' Triple.seq (codecopy ?lt ?op ?gas) ?n3
  case lt => evm_code [initcode, initNat, initSize]
  case op => evm_code [initcode, initNat, initSize]
  case gas => (try wide_mem) <;> omega
  all_goals evm_tidy
  refine' Triple.seq (push0 (by decide) ?lt ?op ?gas ?room) ?n4
  case lt => evm_code [initcode, initNat, initSize]
  case op => evm_code [initcode, initNat, initSize]
  case gas => (try wide_mem) <;> omega
  case room => evm_room
  all_goals evm_tidy
  refine return_postS ?lt ?op ?gas rfl ?out rfl ?st
  case lt => evm_code [initcode, initNat, initSize]
  case op => evm_code [initcode, initNat, initSize]
  case gas =>
    have hm : (extendMemory ByteArray.empty.size [((0 : U256), (42#256 : U256))]).cost ≤ 100 := by decide +kernel
    have hw : wordCount 42 = 2 := by decide
    refine Nat.le_trans (Nat.le_of_lt_succ (Nat.lt_succ_of_le (by decide +kernel : _ ≤ 100))) ?r
    omega
  case out => decide +kernel
  case st =>
    intro slot
    rw [htgt, getStorage_writeOf initcode deployCall rfl]
    simp only [deployed, SolarTV.slotValue, List.foldl, true_and, storageKey_eq_toBeBytes]
    show _ = if 0 % 2 ^ 256 = slot % 2 ^ 256 then 7 % 2 ^ 256 else 0
    by_cases h : slot % 2 ^ 256 = 0
    · rw [if_pos (by simpa using h), if_pos (by rw [h])]; rfl
    · rw [if_neg (by simpa using h), if_neg (by simp; omega)]; rfl

/-- info: 'Verify.Lifecycle.Deploy.NoArgCtor.deploys' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms deploys

end Verify.Lifecycle.Deploy.NoArgCtor

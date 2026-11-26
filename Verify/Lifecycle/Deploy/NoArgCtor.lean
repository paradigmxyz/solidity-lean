import Verify.Lifecycle.CreationFrame

/-!
# `NoArgCtor` deploys

The bytecode half of `NoArgCtor`'s lifecycle statement: EthLib runs solar's init code for
tools/certify/examples/lifecycle/NoArgCtor.sol (solar 0479b90a, -Ogas, osaka) to success, returns
exactly its 42-byte runtime code and leaves slot 0 holding 7, by one kernel evaluation of the
generic creation frame (`Creation.deploys_of_check`) on the frame

    CALLVALUE PUSH1 0x11 JUMPI             ; not payable
    PUSH1 0x07 PUSH0 SSTORE                ; x = 7
    PUSH1 0x2a DUP1 PUSH1 0x15 PUSH0       ; 42 bytes from offset 21 to memory 0
    CODECOPY PUSH0 RETURN                  ; return them

SSTORE is priced at its most expensive case (`sstore_then`), so the frame holds for every message
the creation sends, whatever its access lists.
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

/-- **`NoArgCtor`'s init code deploys its runtime code with slot 0 holding 7.** -/
theorem deploys : Deploys initcode code [(0, 7)] :=
  Creation.deploys_of_check 512 (by decide +kernel)

/-- info: 'Verify.Lifecycle.Deploy.NoArgCtor.deploys' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms deploys

end Verify.Lifecycle.Deploy.NoArgCtor

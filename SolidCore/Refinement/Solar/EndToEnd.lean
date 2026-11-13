import SolidCore.Refinement.Solar.AssembleSim
import SolidCore.Refinement.Solar.AssembleLoopWithin

/-!
# The backend to exact bytecode, for any contract

solar-tv's backend stages give, for each certified contract, the first lowered MIR `stage0` to the
final EVM IR `p` forwards (`<name>_mir_to_evmir`, a `Stage`) and backwards
(`<name>_certified_back`, a `Certified` from `p` to `stage0`). The assembler checks give the
final EVM IR to the exported bytes `code`: `Assemble.check` (straight-line code, gas bounded by
each block's potential) as a stage at EthLib's default gas, `AssembleLoop.checkL` (code with loops)
as `Within` at every gas. This file composes them once, so that a generated proof only supplies
the backend theorems and a check the kernel evaluates:

* `stage_of_check`: stage0 to the bytes, forwards, at EthLib's default gas.
* `within_of_checkL`: at every gas, every result of the bytes is stage0's or a failure that
  changes nothing.
* `holds_of_checkL`: a specification stage0 meets holds of the bytes at every gas.

No hypothesis beyond the two checks' own: the oracle's caller and hash are EthLib's when the
certificate says the code reads them (`c.env`).
-/

namespace SolidCore.Refinement.Solar.EndToEnd

open SolarTV SolarTV.Machine SolidCore.Refinement SolidCore.Refinement.Final

variable {o : Oracle}

/-- **stage0 to the exact bytes at EthLib's default gas**, from the backend stages and the
assembler check of straight-line code. -/
theorem stage_of_check {stage0 : (mirSem o).Prog} {p : Assemble.Program} {code : ByteArray}
    {c : Assemble.Cert} {S scope : Call → Prop}
    (backend : Stage (mirSem o) (evmirSem o) stage0 p S) (hS : ∀ call, scope call → S call)
    (hc : Assemble.check p code c = true) (ho : c.env = true → Assemble.OracleOk o) :
    Stage (mirSem o) ethLib stage0 (show ethLib.Prog from code) scope :=
  Stage.trans (backend.mono hS) (Assemble.stage_of_check_env hc o ho scope)

/-- **At every gas, every result of the exact bytes is stage0's or a failure that changes
nothing**, from the backend stages read backwards and the assembler check of code with loops. -/
theorem within_of_checkL {stage0 : MIR.Lowered.moduleLayer.Prog} {p : Assemble.Program}
    {code : ByteArray} {c : Assemble.Cert} {mx : List Nat} {S scope : Call → Prop}
    (back : Certified EVM.Program.layer MIR.Lowered.moduleLayer o p stage0 S)
    (hS : ∀ call, scope call → S call)
    (hc : AssembleLoop.checkL p code c mx = true) (ho : c.env = true → Assemble.OracleOk o)
    (gas : Nat) :
    Within (mirSem o) (ethLibWith gas) stage0 code scope := by
  intro call hcall obs hrun
  rcases AssembleLoop.within_of_checkL hc o ho scope gas call hcall obs hrun with h | h
  · exact Or.inl (stage_of_certified back call (hS call hcall) obs h)
  · exact Or.inr h

/-- **A specification stage0 meets holds of the exact bytes at every gas.** -/
theorem holds_of_checkL {St : Type} {spec : ContractSpec St} {stage0 : MIR.Lowered.moduleLayer.Prog}
    {p : Assemble.Program} {code : ByteArray} {c : Assemble.Cert} {mx : List Nat}
    {S : Call → Prop} (holds : Holds (mirSem o) stage0 spec)
    (back : Certified EVM.Program.layer MIR.Lowered.moduleLayer o p stage0 S)
    (hS : ∀ call, spec.Calls call → S call)
    (hc : AssembleLoop.checkL p code c mx = true) (ho : c.env = true → Assemble.OracleOk o)
    (gas : Nat) : Holds (ethLibWith gas) code spec :=
  holds.of_within (within_of_checkL back hS hc ho gas)

/-- info: 'SolidCore.Refinement.Solar.EndToEnd.stage_of_check' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms stage_of_check

/-- info: 'SolidCore.Refinement.Solar.EndToEnd.within_of_checkL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms within_of_checkL

/-- info: 'SolidCore.Refinement.Solar.EndToEnd.holds_of_checkL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms holds_of_checkL

end SolidCore.Refinement.Solar.EndToEnd

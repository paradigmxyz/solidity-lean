import Verify.LoopSource.Equiv.Counter.Cut
import Verify.LoopSource.Equiv.Counter.Stage0

/-!
# Counter.bump's cut-point certificate checks, and its mutations do not

`counter_check`: the certificate `loop_equiv.py` emits from solar's loop-head manifest and lowered
MIR for `Counter.bump` checks against that MIR (the kernel runs `Cut.check`).

The negatives change one thing each and the check rejects them: a jump target of the loop's back
edge, a memory write of the loop's body outside the template, a header block outside the loop, and the
runs' fuel. A swapped header branch passes this structural check and fails the obligations
(`Counter/Neg.lean`).
-/

namespace Verify.LoopSource.Equiv.CounterTest
open SolarTV SolarTV.MIR.Lowered SolidCore.Refinement.Generic Verify.LoopSource.Equiv
open Verify.LoopSource.Equiv.Generated.Counter

/-- `Counter.bump`'s selector. -/
def sel : Nat := 0xb20eb4c4

/-- The module with block `b` of function `fn` changed by `g`. -/
def setBlock (m : Module) (fn b : Nat) (g : Block → Block) : Module :=
  { m with functions := m.functions.modify fn fun f => { f with blocks := f.blocks.modify b g } }

/-- **The certificate checks against Counter's lowered MIR.** -/
theorem counter_check : (cut.check .off SolarTV.Export.Counter.stage0 sel 1).isSome = true := by
  decide +kernel

/-- The loop's back edge jumps into the body instead of the header: no run reaches an arrival or
an end within the fuel. -/
theorem neg_jump : (cut.check .off (setBlock SolarTV.Export.Counter.stage0 4 10
    fun blk => { blk with term := .jump 3 }) sel 1).isSome = false := by
  decide +kernel

/-- The body writes `count` to memory outside the template. -/
theorem neg_body : (cut.check .off (setBlock SolarTV.Export.Counter.stage0 4 10
    fun blk => { blk with insts := .effect none .mstore [.const 192, .value 20] :: blk.insts })
    sel 1).isSome = false := by
  decide +kernel

/-- The certificate names a block outside the loop as the header: the entry run unrolls the loop
until its fuel runs out. -/
theorem neg_head : ({ cut with head := 11 }.check .off SolarTV.Export.Counter.stage0 sel 1).isSome = false := by
  decide +kernel

/-- The runs' fuel is too small to reach the header. -/
theorem neg_fuel : ({ cut with fuel := 3 }.check .off SolarTV.Export.Counter.stage0 sel 1).isSome = false := by
  decide +kernel

end Verify.LoopSource.Equiv.CounterTest

/-- info: 'Verify.LoopSource.Equiv.CounterTest.counter_check' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Verify.LoopSource.Equiv.CounterTest.counter_check

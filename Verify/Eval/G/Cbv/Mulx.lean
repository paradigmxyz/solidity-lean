import W1Proofs.Items
import mulx.gen.Main.Evm8
import mulx.gen.Main.Bytecode
import Verify.Eval.G.Kernel
import Verify.Eval.G.Shared

/-!
# Lane G: cbv against decide on mulx's assembly leaves

Certified/mulx/Proofs/Assembly.lean's items_eq (proved there by decide) and walk_eq (decide
+kernel), restated over the same definitions (items, offset, stream, copied verbatim) and proved
by decide, decide +kernel, decide_cbv and cbv, with the same metrics as Cbv/Sat.lean. The
interpreter boundary is unchanged: itemsOf and walk are the checker's own functions. Negative: a
bytecode with one byte flipped must not walk (fail_if_success for every variant). Nothing here
changes the generated Assembly.lean; any change there belongs in the generator.
-/

namespace Verify.Eval.G.CbvMulx

open SolarTV.Assembly SolarTV.Export.Main SolarTV.Milestone.W1

set_option maxRecDepth 100000
set_option maxHeartbeats 0

def items : List Item := (itemsOf evm8).getD []
def offset (label : Nat) : Nat := if label = 1 then 0x1d else if label = 2 then 0x21 else if label = 3 then 0x33 else if label = 4 then 0x6d else 0
def stream : List (Nat × Instr) := (walk bytecode offset 0 items).getD []
/-- The bytecode with its 40th byte flipped. -/
def flipped : List Nat := bytecode.set 40 (bytecode[40]! ^^^ 0xff)

g_time "items_eq decide" in
theorem items_eq_decide : itemsOf evm8 = some items := by decide
#kernel_recheck_all items_eq_decide
#proof_stats items_eq_decide
#print axioms items_eq_decide

g_time "items_eq kernel" in
theorem items_eq_kernel : itemsOf evm8 = some items := by decide +kernel
#kernel_recheck_all items_eq_kernel
#proof_stats items_eq_kernel
#print axioms items_eq_kernel

g_time "items_eq dcbv" in
theorem items_eq_dcbv : itemsOf evm8 = some items := by decide_cbv
#kernel_recheck_all items_eq_dcbv
#proof_stats items_eq_dcbv
#print axioms items_eq_dcbv

g_time "items_eq cbv" in
theorem items_eq_cbv : itemsOf evm8 = some items := by cbv
#kernel_recheck_all items_eq_cbv
#proof_stats items_eq_cbv
#print axioms items_eq_cbv

g_time "walk_eq decide" in
theorem walk_eq_decide : walk bytecode offset 0 items = some stream := by decide
#kernel_recheck_all walk_eq_decide
#proof_stats walk_eq_decide
#print axioms walk_eq_decide

g_time "walk_eq kernel" in
theorem walk_eq_kernel : walk bytecode offset 0 items = some stream := by decide +kernel
#kernel_recheck_all walk_eq_kernel
#proof_stats walk_eq_kernel
#print axioms walk_eq_kernel

g_time "walk_eq dcbv" in
theorem walk_eq_dcbv : walk bytecode offset 0 items = some stream := by decide_cbv
#kernel_recheck_all walk_eq_dcbv
#proof_stats walk_eq_dcbv
#print axioms walk_eq_dcbv

g_time "walk_eq cbv" in
theorem walk_eq_cbv : walk bytecode offset 0 items = some stream := by cbv
#kernel_recheck_all walk_eq_cbv
#proof_stats walk_eq_cbv
#print axioms walk_eq_cbv

-- a flipped byte must not walk (decide)
example : True := by
  fail_if_success have : walk flipped offset 0 items = some stream := by decide
  trivial

-- a flipped byte must not walk (kernel)
example : True := by
  fail_if_success have : walk flipped offset 0 items = some stream := by decide +kernel
  trivial

-- a flipped byte must not walk (dcbv)
example : True := by
  fail_if_success have : walk flipped offset 0 items = some stream := by decide_cbv
  trivial

-- a flipped byte must not walk (cbv)
example : True := by
  fail_if_success have : walk flipped offset 0 items = some stream := by cbv
  trivial

end Verify.Eval.G.CbvMulx

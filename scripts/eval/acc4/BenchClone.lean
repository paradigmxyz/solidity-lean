import flag_4ce5cf9a.Lowering
import SolidCore.Refinement.KernelRfl

/-! Bench only: split kernel_rfl shape_eq's 8.7 s into clone construction and kernel check by
running the same clone call under fresh prefixes (no cache hit on the module's own copies). -/

open Lean Meta SolidCore.Refinement SolidCore.Refinement.Kernel

run_meta do
  let c := `Certified.flag_4ce5cf9a.Lowering.shape?
  let eqs := #[`Certified.flag_4ce5cf9a.Lowering.selector_eq]
  let h0 ← IO.monoNanosNow
  let r ← cloneRootSubst c `Bench.kernel.using_selector_eq `Bench.kernel eqs
  let h1 ← IO.monoNanosNow
  logInfo m!"clone shape?: {r.map (·.2) |>.getD 0} copies, {(h1 - h0).toFloat / 1e6} ms (includes their addDecl)"

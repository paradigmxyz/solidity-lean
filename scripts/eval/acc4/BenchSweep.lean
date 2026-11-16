import flag_4ce5cf9a.SpecConnect
import SolidCore.Refinement.KernelRfl

/-! Bench only: time cloneRootSubst on roots of increasing size, each under fresh prefixes so no
copy is reused from the module that already cloned it. Run interpreted and with the clone code's
dynlibs loaded; the copies (and their kernel checks) are the same in both. -/

open Lean Meta SolidCore.Refinement SolidCore.Refinement.Kernel

def bench (tag : String) (c : Name) (eqs : Array Name) : MetaM Unit := do
  let pre := Name.mkSimple ("Bench_" ++ tag)
  let h0 ← IO.monoNanosNow
  let r ← cloneRootSubst c (pre ++ `kernel ++ `using) (pre ++ `kernel) eqs
  let h1 ← IO.monoNanosNow
  logInfo m!"sweep,{tag},{c},{r.map (·.2) |>.getD 0},{(h1 - h0).toFloat / 1e6}"

def sel := `Certified.flag_4ce5cf9a.Lowering.selector_eq
def idx := `SolidCore.Verify.VC.mkIdx_eq

run_meta bench "deployedEmpty" `SolidCore.Refinement.Wide.deployedEmpty #[sel]
run_meta bench "deployedStorage" `SolidCore.Refinement.Abi.deployedStorage #[sel]
run_meta bench "fnShapeOk" `SolidCore.Refinement.Dirty.fnShapeOk #[sel]
run_meta bench "contract" `Certified.flag_4ce5cf9a.Lowering.contract? #[sel]
run_meta bench "shape" `Certified.flag_4ce5cf9a.Lowering.shape? #[sel]
run_meta bench "deploy" `flag_4ce5cf9a.SpecConnect.deploy? #[sel, idx]

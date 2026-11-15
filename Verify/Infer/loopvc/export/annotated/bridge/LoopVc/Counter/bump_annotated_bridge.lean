import Lean
import Counter.bump_loopvc
import LoopVc.Counter.bump_annotated

open SolarVerify.Smt SolarVerify.Vc SolarVerify.LoopVc

namespace SolarVerifyVc.LoopVc.Counter.bump_annotated.Bridge

/-- The candidate, in the interface's terms. -/
def cand : Cand := { conj := [.app .le [.fn 27 [], .fn 20 []], .app .eq [.fn 26 [], .app .add [.fn 16 [], .fn 27 []]]], rank := some (.app .sub [.fn 20 [], .fn 27 []]) }

/-- It is the candidate of the run. -/
theorem cand_eq : cand = SolarVerifyLoopVc.Counter.bump.cand := rfl

theorem t0_exact : SolarVerifyLoopVc.Counter.bump.t0.instances SolarVerifyLoopVc.Counter.bump.cut cand = [SolarVerifyVc.LoopVc.Counter.bump_annotated.ob0, SolarVerifyVc.LoopVc.Counter.bump_annotated.ob1] := rfl

theorem t1_exact : SolarVerifyLoopVc.Counter.bump.t1.instances SolarVerifyLoopVc.Counter.bump.cut cand = [SolarVerifyVc.LoopVc.Counter.bump_annotated.ob2, SolarVerifyVc.LoopVc.Counter.bump_annotated.ob3] := rfl

theorem t2_exact : SolarVerifyLoopVc.Counter.bump.t2.instances SolarVerifyLoopVc.Counter.bump.cut cand = [SolarVerifyVc.LoopVc.Counter.bump_annotated.ob4] := rfl

theorem t3_exact : SolarVerifyLoopVc.Counter.bump.t3.instances SolarVerifyLoopVc.Counter.bump.cut cand = [SolarVerifyVc.LoopVc.Counter.bump_annotated.ob5] := rfl

theorem t4_exact : SolarVerifyLoopVc.Counter.bump.t4.instances SolarVerifyLoopVc.Counter.bump.cut cand = [SolarVerifyVc.LoopVc.Counter.bump_annotated.ob6] := rfl

end SolarVerifyVc.LoopVc.Counter.bump_annotated.Bridge

open Lean Elab Command in
#eval show CommandElabM Unit from do
  for n in [`SolarVerifyVc.LoopVc.Counter.bump_annotated.Bridge.t0_exact, `SolarVerifyVc.LoopVc.Counter.bump_annotated.Bridge.t1_exact, `SolarVerifyVc.LoopVc.Counter.bump_annotated.Bridge.t2_exact, `SolarVerifyVc.LoopVc.Counter.bump_annotated.Bridge.t3_exact, `SolarVerifyVc.LoopVc.Counter.bump_annotated.Bridge.t4_exact] do
    let axs ← Lean.collectAxioms n
    IO.println s!"AXIOMS {n}: {String.intercalate " " (axs.toList.map toString)}"

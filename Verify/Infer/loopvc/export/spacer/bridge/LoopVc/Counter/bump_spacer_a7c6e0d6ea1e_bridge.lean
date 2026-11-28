import Lean
import Counter.bump_loopvc
import LoopVc.Counter.bump_spacer_a7c6e0d6ea1e

open SolarVerify.Smt SolarVerify.Vc SolarVerify.LoopVc

namespace SolarVerifyVc.LoopVc.Counter.bump_spacer_a7c6e0d6ea1e.Bridge

/-- The candidate, in the interface's terms. -/
def cand : Cand := { conj := [.app .not [.app .le [.app .add [.fn 16 [], .app .mul [.app .sub [.int 1], .fn 26 []], .fn 27 []], .app .sub [.int 1]]], .app .not [.app .ge [.app .add [.fn 16 [], .app .mul [.app .sub [.int 1], .fn 26 []], .fn 27 []], .int 1]], .app .not [.app .le [.app .add [.fn 16 [], .app .mul [.app .sub [.int 1], .fn 26 []], .fn 20 []], .app .sub [.int 1]]]], rank := some (.app .sub [.fn 20 [], .fn 27 []]) }

theorem t0_exact : SolarVerifyLoopVc.Counter.bump.t0.instances SolarVerifyLoopVc.Counter.bump.cut cand = [SolarVerifyVc.LoopVc.Counter.bump_spacer_a7c6e0d6ea1e.ob0, SolarVerifyVc.LoopVc.Counter.bump_spacer_a7c6e0d6ea1e.ob1, SolarVerifyVc.LoopVc.Counter.bump_spacer_a7c6e0d6ea1e.ob2] := rfl

theorem t1_exact : SolarVerifyLoopVc.Counter.bump.t1.instances SolarVerifyLoopVc.Counter.bump.cut cand = [SolarVerifyVc.LoopVc.Counter.bump_spacer_a7c6e0d6ea1e.ob3, SolarVerifyVc.LoopVc.Counter.bump_spacer_a7c6e0d6ea1e.ob4, SolarVerifyVc.LoopVc.Counter.bump_spacer_a7c6e0d6ea1e.ob5] := rfl

theorem t2_exact : SolarVerifyLoopVc.Counter.bump.t2.instances SolarVerifyLoopVc.Counter.bump.cut cand = [SolarVerifyVc.LoopVc.Counter.bump_spacer_a7c6e0d6ea1e.ob6] := rfl

theorem t3_exact : SolarVerifyLoopVc.Counter.bump.t3.instances SolarVerifyLoopVc.Counter.bump.cut cand = [SolarVerifyVc.LoopVc.Counter.bump_spacer_a7c6e0d6ea1e.ob7] := rfl

theorem t4_exact : SolarVerifyLoopVc.Counter.bump.t4.instances SolarVerifyLoopVc.Counter.bump.cut cand = [SolarVerifyVc.LoopVc.Counter.bump_spacer_a7c6e0d6ea1e.ob8] := rfl

end SolarVerifyVc.LoopVc.Counter.bump_spacer_a7c6e0d6ea1e.Bridge

open Lean Elab Command in
#eval show CommandElabM Unit from do
  for n in [`SolarVerifyVc.LoopVc.Counter.bump_spacer_a7c6e0d6ea1e.Bridge.t0_exact, `SolarVerifyVc.LoopVc.Counter.bump_spacer_a7c6e0d6ea1e.Bridge.t1_exact, `SolarVerifyVc.LoopVc.Counter.bump_spacer_a7c6e0d6ea1e.Bridge.t2_exact, `SolarVerifyVc.LoopVc.Counter.bump_spacer_a7c6e0d6ea1e.Bridge.t3_exact, `SolarVerifyVc.LoopVc.Counter.bump_spacer_a7c6e0d6ea1e.Bridge.t4_exact] do
    let axs ← Lean.collectAxioms n
    IO.println s!"AXIOMS {n}: {String.intercalate " " (axs.toList.map toString)}"

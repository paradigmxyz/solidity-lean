import Verify.LoopSource.Equiv.GenObl
import Verify.LoopSource.MirLink.Link
import Verify.LoopSource.Proof.LoopVC

/-!
# Counter.bump's body summary, as a checked `GenObl.Summary`

`summary_ok`: on every checked contract whose storage fields are `vcFields` and whose function at
`bump`'s selector is `bumpFn` (whose body is `bumpBody`), that body runs to `bumpBr` from fuel
`2 ^ 256 + 8` on. It is the loop route's `body_runs_vc` (the ranking-certificate proof checked from
solar-verify's obligations), restated over the shape. The generator checks the shape against the
imported contract; the generated module proves it there by `kernel_rfl`.
-/

namespace Verify.LoopSource.Equiv.CounterSummary
open SolidCore.Refinement.Generic SolidCore.Refinement.Generic.Loop Contracts.VerifyCounter.Source
open Verify.LoopSource.Equiv.GenObl

/-- The shape `bumpBr` was proved for. -/
def shape : List SolidCore.Solidity.Source.StorageField × FunctionDef := (vcFields, bumpFn)

theorem summary_ok : SummaryOk bumpSel (2 ^ 256 + 8) shape bumpBr := by
  intro c hs ws hw fuel hfu
  simp only [shape] at hw ⊢
  simp only [shapeOfC, shape, Option.map_eq_some_iff, Prod.mk.injEq] at hs
  obtain ⟨fn, -, hfields, rfl⟩ := hs
  have hw' : ws = [256] := by
    have : widthsOf bumpFn.params bumpFn.paramAbiCleanups = some [256] := rfl
    rw [this] at hw; exact (Option.some.inj hw).symm
  subst hw'
  have hE : ({ envOf c.core with facts := argFacts [256] 0 } : EraseEnv) =
      env c.core.eventDecls c.core.table := by
    simp only [envOf, env, hfields]
    rfl
  rw [hE]
  exact Contracts.VerifyCounter.LoopVC.body_runs_vc _ _ bumpFn rfl rfl fuel hfu

/-- **Counter.bump's summary.** -/
def summary : Summary :=
  { br := bumpBr, brName := "Contracts.VerifyCounter.Source.bumpBr",
    shape := shape, shapeName := "Verify.LoopSource.Equiv.CounterSummary.shape",
    minFuel := 2 ^ 256 + 8, okName := "Verify.LoopSource.Equiv.CounterSummary.summary_ok" }

end Verify.LoopSource.Equiv.CounterSummary

/-- info: 'Verify.LoopSource.Equiv.CounterSummary.summary_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Verify.LoopSource.Equiv.CounterSummary.summary_ok

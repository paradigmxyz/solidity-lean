import Verify.LoopSource.Equiv.GenObl
import Verify.LoopSource.Proof.LoopVC

/-!
# Counter.bump's body summary, as a checked `GenObl.Summary`

`summary_ok`: on every checked contract whose storage fields are `vcFields` and whose function at
`bump`'s selector is `fn` (whose body is `bumpBody`), that body runs to `bumpBr` from fuel
`2 ^ 256 + 8` on. It is the loop route's `body_runs_vc` (the ranking-certificate proof checked from
solar-verify's obligations), restated over the shape. The generator checks the shape against the
imported contract; the generated module proves it there by `kernel_rfl`.

It imports neither `Contracts.VerifyCounter.Source` nor anything that does: that module's
`kernel_rfl` commands run their elaborator in Lean's interpreter, whose memory its library's
`-M 3000` caps, and the generator's imports must build within that cap. `fn` restates the
checked `bump` here (the shape check compares it with the imported contract's).
-/

namespace Verify.LoopSource.Equiv.CounterSummary
open SolidCore.Refinement.Generic SolidCore.Refinement.Generic.Loop Contracts.VerifyCounter.Source
open Verify.LoopSource.Equiv.GenObl

/-- `bump`'s selector. -/
def sel : Nat := 0xb20eb4c4

/-- `bump` as the type checker leaves it (the same value as `Contracts.VerifyCounter.Source.bumpFn`). -/
def fn : FunctionDef :=
  { name := "bump", selector? := some 2987308228, payable := false,
    params := [{ name := "n", ty := SolidCore.Solidity.Source.Ty.uint256, isStorageRef := false }],
    paramAbiCleanups := [SolidCore.Solidity.Source.AbiCleanup.uint 256], returns := [], body := bumpBody,
    dispatchId? := none }

/-- The shape `bumpBr` was proved for. -/
def shape : List SolidCore.Solidity.Source.StorageField × FunctionDef := (vcFields, fn)

theorem summary_ok : SummaryOk sel (2 ^ 256 + 8) shape bumpBr := by
  intro c hs ws hw fuel hfu
  simp only [shape] at hw ⊢
  simp only [shapeOfC, shape, Option.map_eq_some_iff, Prod.mk.injEq] at hs
  obtain ⟨fn, -, hfields, rfl⟩ := hs
  have hw' : ws = [256] := by
    have : widthsOf fn.params fn.paramAbiCleanups = some [256] := rfl
    rw [this] at hw; exact (Option.some.inj hw).symm
  subst hw'
  rw [envOf_eq hfields]
  exact Contracts.VerifyCounter.LoopVC.body_runs_vc _ _ fn rfl rfl fuel hfu

/-- **Counter.bump's summary.** -/
def summary : Summary :=
  { br := bumpBr, brName := "Contracts.VerifyCounter.Source.bumpBr",
    shape := shape, shapeName := "Verify.LoopSource.Equiv.CounterSummary.shape",
    minFuel := 2 ^ 256 + 8, okName := "Verify.LoopSource.Equiv.CounterSummary.summary_ok" }

end Verify.LoopSource.Equiv.CounterSummary

/-- info: 'Verify.LoopSource.Equiv.CounterSummary.summary_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Verify.LoopSource.Equiv.CounterSummary.summary_ok

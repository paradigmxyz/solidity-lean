import Contracts.UniswapV2.PairSpec.Published

namespace SolidCore.Spec.UniswapV2.PairSpec

open SolarTV SolidCore.Refinement SolidCore.Spec

/-- sync() from the empty storage. -/
def syncCall : Call := mkCall ((EthLib.Base.natToBytes 4 syncSel).map (·.toNat)) []

/-- A success that changes the total supply (slot 0) from 0 to 1. -/
def badObs : Observable :=
  { success := true, output := [], logs := [], storage := fun s => if s = 0 then 1 else 0 }

theorem nonVacuous : NonVacuous := by
  refine ⟨syncCall, badObs, Or.inr (Or.inr ⟨[], rfl⟩), fun W h => ?_⟩
  have hmem : (SolidCore.Spec.Export.UniswapV2Pair.UniswapV2Pair.spec.specs[10]'(by decide)) ∈
      SolidCore.Spec.Export.UniswapV2Pair.UniswapV2Pair.spec.specs := List.getElem_mem _
  have hpre : SolidCore.Spec.Pre SolidCore.Spec.Export.UniswapV2Pair.UniswapV2Pair
      (SolidCore.Spec.Export.UniswapV2Pair.UniswapV2Pair.spec.specs[10]'(by decide)) (ctxOf syncCall)
      { storage := slotValue [], ghost := Ghost.zero, time := 0 } syncCall [] := by
    refine ⟨⟨by decide, by decide, by decide⟩, rfl, by decide, ?_, ?_⟩
    · simp [Bundle.satAll, SolidCore.Spec.Export.UniswapV2Pair.UniswapV2Pair]
    · simp [Bundle.satAll, Bundle.sat, SolidCore.Spec.Export.UniswapV2Pair.UniswapV2Pair, eval,
        BinOp.apply, mkEnv, Env.cur, slotOf, slotValue, Ty.ofBits, toWord, Ghost.zero, Env.bind]
  have hp := (h _ hmem [] _ hpre).1 rfl
  obtain ⟨rets, -, hens, -⟩ := hp
  have h0 := hens _ (List.getElem_mem (by decide : 0 < (SolidCore.Spec.Export.UniswapV2Pair.UniswapV2Pair.spec.specs[10]'(by decide)).ensures.length))
  simp [Bundle.sat, SolidCore.Spec.Export.UniswapV2Pair.UniswapV2Pair, eval, BinOp.apply, mkEnv,
    Env.cur, slotOf, slotValue, Ty.ofBits, toWord, badObs, idStep] at h0

/-- info: 'SolidCore.Spec.UniswapV2.PairSpec.nonVacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms nonVacuous

end SolidCore.Spec.UniswapV2.PairSpec


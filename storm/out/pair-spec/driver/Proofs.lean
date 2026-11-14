import uniswap_v2_pair.Statement
import Contracts.UniswapV2.PairSpec.Inputs

/-! The proof module of uniswap_v2_pair's published statement (tools/certify/final.py, kind
open_functional): the non-vacuity witness now; `published` once the stage theorems land
(Contracts/UniswapV2/PairSpec/Published.lean composes them). -/

namespace Certified.uniswap_v2_pair.Proofs

open SolarTV SolidCore.Refinement SolidCore.Spec SolidCore.Spec.UniswapV2.PairSpec

/-- sync() from the empty storage. -/
def syncCall : Call := mkCall ((EthLib.Base.natToBytes 4 syncSel).map (·.toNat)) []

/-- A success that changes the total supply (slot 0) from 0 to 1. -/
def badObs : Observable :=
  { success := true, output := [], logs := [], storage := fun s => if s = 0 then 1 else 0 }

theorem nonVacuous : Certified.uniswap_v2_pair.Final.NonVacuous := by
  refine ⟨syncCall, badObs, Or.inr (Or.inr ⟨[], rfl⟩), fun W h => ?_⟩
  have hmem : (Certified.uniswap_v2_pair.gen.UniswapV2Pair.Spec.UniswapV2Pair.spec.specs[10]'(by decide)) ∈
      Certified.uniswap_v2_pair.gen.UniswapV2Pair.Spec.UniswapV2Pair.spec.specs := List.getElem_mem _
  have hpre : SolidCore.Spec.Pre Certified.uniswap_v2_pair.gen.UniswapV2Pair.Spec.UniswapV2Pair
      (Certified.uniswap_v2_pair.gen.UniswapV2Pair.Spec.UniswapV2Pair.spec.specs[10]'(by decide)) (ctxOf syncCall)
      { storage := slotValue [], ghost := Ghost.zero, time := 0 } syncCall [] := by
    refine ⟨⟨by decide, by decide, by decide⟩, rfl, by decide, ?_, ?_⟩
    · simp [Bundle.satAll, Certified.uniswap_v2_pair.gen.UniswapV2Pair.Spec.UniswapV2Pair]
    · simp [Bundle.satAll, Bundle.sat, Certified.uniswap_v2_pair.gen.UniswapV2Pair.Spec.UniswapV2Pair, eval,
        BinOp.apply, mkEnv, Env.cur, slotOf, slotValue, Ty.ofBits, toWord, Ghost.zero, Env.bind]
  have hp := (h _ hmem [] _ hpre).1 rfl
  obtain ⟨rets, -, hens, -⟩ := hp
  have h0 := hens _ (List.getElem_mem (by decide : 0 < (Certified.uniswap_v2_pair.gen.UniswapV2Pair.Spec.UniswapV2Pair.spec.specs[10]'(by decide)).ensures.length))
  simp [Bundle.sat, Certified.uniswap_v2_pair.gen.UniswapV2Pair.Spec.UniswapV2Pair, eval, BinOp.apply, mkEnv,
    Env.cur, slotOf, slotValue, Ty.ofBits, toWord, badObs, idStep] at h0

/-- info: 'Certified.uniswap_v2_pair.Proofs.nonVacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms nonVacuous

end Certified.uniswap_v2_pair.Proofs


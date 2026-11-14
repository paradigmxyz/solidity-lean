import Contracts.UniswapV2.PairSpec.Published
import Contracts.UniswapV2.PairSpec.SpecWrongK

/-!
# UniswapV2Pair: refusals of the executed observables

The kernel half of the negative controls (Negative.lean runs the programs): for the swap
`swap(0, 906, 0x3000, "")` from reserves 10000/10000 with 1000 of token0 in, the published
specification refuses **every** observable that succeeds and leaves the reserves at 10000/10000
(what the pair without `_update` does), the wrong-K specification refuses every observable that
succeeds with reserves 11000/9094 (what the pair does), and the published fee-adjusted clause
accepts those reserves. The pre-state meets the specification's precondition under the
statement's premise `HashScope` (the ERC20 invariants read `allowance[address(0)][s]`, which must
not be one of the pair's fixed slots).
-/

namespace SolidCore.Spec.UniswapV2.PairSpec.Negative

open SolarTV SolidCore.Refinement SolidCore.Refinement.Shapes SolidCore.Spec
open SolidCore.Spec.UniswapV2.PairSpec

/-- The pair's storage: token0, token1, reserves 10000/10000, unlocked. -/
def σ : List (Nat × Nat) := [(6, 0x4000), (7, 0x5000), (8, 10000 + 10000 * 2 ^ 112), (12, 1)]

/-- `swap(0, 906, 0x3000, "")` after 1000 of token0 arrived (token0 balance 11000). -/
def swapCall : Call := mkCall (swapData 0 906 0x3000 []) σ

theorem swapCall_valid : Valid swapCall :=
  Or.inl ⟨σ, 0, 906, 0x3000, [], by decide, by decide, by decide, by decide, by simp, rfl⟩


/-- swap's spec in a bundle (the ninth). -/
abbrev swapFs (b : Bundle) (h : 8 < b.spec.specs.length) : FnSpec := b.spec.specs[8]

/-- The pre-state of the swap. -/
def preSt : State := { storage := slotValue σ, ghost := Ghost.zero, time := 0 }

theorem slotValue_σ_big {x : Nat} (hx : 13 ≤ x % 2 ^ 256) : slotValue σ x = 0 := by
  simp only [slotValue, σ, List.foldl]
  split_ifs <;> omega

/-- The swap's arguments as the spec decodes them. -/
def swapArgs : List Int := [0, 906, 0x3000, 0x80]

set_option maxRecDepth 100000 in
theorem pre_swap (hk : HashScope) :
    Pre SolidCore.Spec.Export.UniswapV2Pair.UniswapV2Pair
      (SolidCore.Spec.Export.UniswapV2Pair.UniswapV2Pair.spec.specs[8]'(by decide)) (ctxOf swapCall) preSt swapCall swapArgs := by
  obtain ⟨hk0, hk1⟩ := hk
  refine ⟨⟨by decide +kernel, by decide +kernel, by decide +kernel⟩, rfl, by decide, ?_, ?_⟩
  · simp [Bundle.satAll, SolidCore.Spec.Export.UniswapV2Pair.UniswapV2Pair]
  · simp [Bundle.satAll, Bundle.sat, SolidCore.Spec.Export.UniswapV2Pair.UniswapV2Pair, eval,
      BinOp.apply, mkEnv, Env.cur, slotOf, preSt, Ty.ofBits, toWord, Ghost.zero, Env.bind]
    refine ⟨by decide, fun v hv => ?_, Int.emod_nonneg _ (by decide)⟩
    obtain ⟨hv0, hv1⟩ := hv
    have hs : (v % 115792089237316195423570985008687907853269984665640564039457584007913129639936).toNat
        = v.toNat := by rw [Int.emod_eq_of_lt hv0 (by omega)]
    have h2 : 2 % wordMod = 2 := by decide
    rw [hs, h2]
    have := slotValue_σ_big (hk1 v.toNat (by omega))
    simp only [zeroAllowanceSlot] at this
    rw [this]
    rfl

/-- The published specification as a postcondition (the statement's `Post`, any world). -/
abbrev PostPub : Call → Observable → Prop :=
  bundlePost SolidCore.Spec.Export.UniswapV2Pair.UniswapV2Pair ctxOf idStep

/-- The wrong-K specification as a postcondition. -/
abbrev PostWrongK : Call → Observable → Prop :=
  bundlePost SolidCore.Spec.Export.UniswapV2PairWrongK.UniswapV2Pair ctxOf idStep

set_option maxRecDepth 100000 in
/-- **Missing reserve update, refused**: the published specification refuses every observable of
the swap that succeeds with the reserves left at 10000/10000. -/
theorem noUpdate_refused (hk : HashScope) (W : World) (obs : Observable) (hs : obs.success = true)
    (h0 : obs.storage 8 % 2 ^ 112 = 10000) (h1 : obs.storage 8 / 2 ^ 112 % 2 ^ 112 = 10000) :
    ¬ Post W swapCall obs := by
  intro h
  have hmem : (SolidCore.Spec.Export.UniswapV2Pair.UniswapV2Pair.spec.specs[8]'(by decide)) ∈
      SolidCore.Spec.Export.UniswapV2Pair.UniswapV2Pair.spec.specs := List.getElem_mem _
  obtain ⟨rets, -, hens, -⟩ := (h _ hmem swapArgs preSt (pre_swap hk)).1 hs
  have hK := hens _ (List.getElem_mem (by decide : 0 < (SolidCore.Spec.Export.UniswapV2Pair.UniswapV2Pair.spec.specs[8]'(by decide)).ensures.length))
  simp only [Nat.reducePow] at h0 h1
  have h0i : ((obs.storage 8 : Nat) : Int) % 5192296858534827628530496329220096 = 10000 := by omega
  have h1i : ((obs.storage 8 : Nat) : Int) / 5192296858534827628530496329220096 %
      5192296858534827628530496329220096 = 10000 := by omega
  simp [Bundle.sat, SolidCore.Spec.Export.UniswapV2Pair.UniswapV2Pair, eval, BinOp.apply, mkEnv,
    Env.cur, slotOf, Ty.ofBits, toWord, idStep, preSt, swapArgs, wordMod, slotValue, σ, h0i, h1i] at hK

set_option maxRecDepth 100000 in
theorem pre_swapWrongK (hk : HashScope) :
    Pre SolidCore.Spec.Export.UniswapV2PairWrongK.UniswapV2Pair
      (SolidCore.Spec.Export.UniswapV2PairWrongK.UniswapV2Pair.spec.specs[8]'(by decide)) (ctxOf swapCall) preSt swapCall swapArgs := by
  obtain ⟨hk0, hk1⟩ := hk
  refine ⟨⟨by decide +kernel, by decide +kernel, by decide +kernel⟩, rfl, by decide, ?_, ?_⟩
  · simp [Bundle.satAll, SolidCore.Spec.Export.UniswapV2PairWrongK.UniswapV2Pair]
  · simp [Bundle.satAll, Bundle.sat, SolidCore.Spec.Export.UniswapV2PairWrongK.UniswapV2Pair, eval,
      BinOp.apply, mkEnv, Env.cur, slotOf, preSt, Ty.ofBits, toWord, Ghost.zero, Env.bind]
    refine ⟨by decide, fun v hv => ?_, Int.emod_nonneg _ (by decide)⟩
    obtain ⟨hv0, hv1⟩ := hv
    have hs : (v % 115792089237316195423570985008687907853269984665640564039457584007913129639936).toNat
        = v.toNat := by rw [Int.emod_eq_of_lt hv0 (by omega)]
    have h2 : 2 % wordMod = 2 := by decide
    rw [hs, h2]
    have := slotValue_σ_big (hk1 v.toNat (by omega))
    simp only [zeroAllowanceSlot] at this
    rw [this]
    rfl

set_option maxRecDepth 100000 in
/-- **Wrong K, refused**: the wrong-K specification (fee 4/1000) refuses every observable of the
swap that succeeds with reserves 11000/9094, what the pair's bytes and source do. -/
theorem wrongK_refused (hk : HashScope) (obs : Observable) (hs : obs.success = true)
    (h0 : obs.storage 8 % 2 ^ 112 = 11000) (h1 : obs.storage 8 / 2 ^ 112 % 2 ^ 112 = 9094) :
    ¬ PostWrongK swapCall obs := by
  intro h
  have hmem : (SolidCore.Spec.Export.UniswapV2PairWrongK.UniswapV2Pair.spec.specs[8]'(by decide)) ∈
      SolidCore.Spec.Export.UniswapV2PairWrongK.UniswapV2Pair.spec.specs := List.getElem_mem _
  obtain ⟨rets, -, hens, -⟩ := (h _ hmem swapArgs preSt (pre_swapWrongK hk)).1 hs
  have hK := hens _ (List.getElem_mem (by decide : 0 < (SolidCore.Spec.Export.UniswapV2PairWrongK.UniswapV2Pair.spec.specs[8]'(by decide)).ensures.length))
  simp only [Nat.reducePow] at h0 h1
  have h0i : ((obs.storage 8 : Nat) : Int) % 5192296858534827628530496329220096 = 11000 := by omega
  have h1i : ((obs.storage 8 : Nat) : Int) / 5192296858534827628530496329220096 %
      5192296858534827628530496329220096 = 9094 := by omega
  simp [Bundle.sat, SolidCore.Spec.Export.UniswapV2PairWrongK.UniswapV2Pair, eval, BinOp.apply, mkEnv,
    Env.cur, slotOf, Ty.ofBits, toWord, idStep, preSt, swapArgs, wordMod, slotValue, σ, h0i, h1i] at hK

set_option maxRecDepth 100000 in
/-- **The published clause accepts the pair's swap**: the fee-adjusted constant product holds of
every post-state with reserves 11000/9094 after the swap from 10000/10000. -/
theorem k_accepts (obs : Observable) (h0 : obs.storage 8 % 2 ^ 112 = 11000)
    (h1 : obs.storage 8 / 2 ^ 112 % 2 ^ 112 = 9094) (rets : List Int) :
    SolidCore.Spec.Export.UniswapV2Pair.UniswapV2Pair.sat
      ((SolidCore.Spec.Export.UniswapV2Pair.UniswapV2Pair.spec.specs[8]'(by decide)).ensures[0]'(by decide))
      (mkEnv (ctxOf swapCall) swapArgs rets preSt
        { storage := obs.storage, ghost := idStep swapCall preSt.ghost, time := (ctxOf swapCall).timestamp }) := by
  simp only [Nat.reducePow] at h0 h1
  have h0i : ((obs.storage 8 : Nat) : Int) % 5192296858534827628530496329220096 = 11000 := by omega
  have h1i : ((obs.storage 8 : Nat) : Int) / 5192296858534827628530496329220096 %
      5192296858534827628530496329220096 = 9094 := by omega
  simp [Bundle.sat, SolidCore.Spec.Export.UniswapV2Pair.UniswapV2Pair, eval, BinOp.apply, mkEnv,
    Env.cur, slotOf, Ty.ofBits, toWord, idStep, preSt, swapArgs, wordMod, slotValue, σ, h0i, h1i]

/-- info: 'SolidCore.Spec.UniswapV2.PairSpec.Negative.noUpdate_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms noUpdate_refused

/-- info: 'SolidCore.Spec.UniswapV2.PairSpec.Negative.wrongK_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms wrongK_refused

/-- info: 'SolidCore.Spec.UniswapV2.PairSpec.Negative.k_accepts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms k_accepts

end SolidCore.Spec.UniswapV2.PairSpec.Negative

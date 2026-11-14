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
statement's premise `PairAllowanceApart` (the ERC20 invariants read `allowance[address(0)][s]`, which must
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
theorem pre_swap (hk : PairAllowanceApart) :
    Pre SolidCore.Spec.Export.UniswapV2Pair.UniswapV2Pair
      (SolidCore.Spec.Export.UniswapV2Pair.UniswapV2Pair.spec.specs[8]'(by decide)) (ctxOf swapCall) preSt swapCall swapArgs := by
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
    have := slotValue_σ_big (hk v.toNat (by omega))
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
theorem noUpdate_refused (hk : PairAllowanceApart) (W : World) (obs : Observable) (hs : obs.success = true)
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
theorem pre_swapWrongK (hk : PairAllowanceApart) :
    Pre SolidCore.Spec.Export.UniswapV2PairWrongK.UniswapV2Pair
      (SolidCore.Spec.Export.UniswapV2PairWrongK.UniswapV2Pair.spec.specs[8]'(by decide)) (ctxOf swapCall) preSt swapCall swapArgs := by
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
    have := slotValue_σ_big (hk v.toNat (by omega))
    simp only [zeroAllowanceSlot] at this
    rw [this]
    rfl

set_option maxRecDepth 100000 in
/-- **Wrong K, refused**: the wrong-K specification (fee 4/1000) refuses every observable of the
swap that succeeds with reserves 11000/9094, what the pair's bytes and source do. -/
theorem wrongK_refused (hk : PairAllowanceApart) (obs : Observable) (hs : obs.success = true)
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

/-- `balanceOf[address(0)]`'s word is no fixed slot, by the kernel's evaluation of keccak256
(`TrustedBase.image3`): no premise needed for it. -/
theorem zeroBalance_ge : 13 ≤ SolidCore.Spec.keccakWord (SolidCore.Spec.wordBytes 0 ++ SolidCore.Spec.wordBytes 1) % 2 ^ 256 := by
  have h := SolidCore.Spec.TrustedBase.image3
  simp only [SolidCore.Spec.TrustedBase.mappingPreimage] at h
  rw [h]; decide

/-- **The premise is satisfiable**: with the hash replaced by any function whose images are at
least 13 (here the constant `2 ^ 128`), it holds. The premise is about keccak256 itself and stays a
premise; this shows it is not `False` in disguise. -/
theorem PairAllowanceApart.satisfiable : ∃ h : List Nat → Nat,
    ∀ s, s < 2 ^ 160 → 13 ≤ h (SolidCore.Spec.wordBytes s ++
      SolidCore.Spec.wordBytes (h (SolidCore.Spec.wordBytes 0 ++ SolidCore.Spec.wordBytes 2))) % 2 ^ 256 :=
  ⟨fun _ => 2 ^ 128, fun _ _ => by norm_num⟩

/-- info: 'SolidCore.Spec.UniswapV2.PairSpec.Negative.zeroBalance_ge' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms zeroBalance_ge

/-- info: 'SolidCore.Spec.UniswapV2.PairSpec.Negative.pre_swap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms pre_swap

/-- `skim(0x3000)` from the same storage (the runs: token balances 11000/10500 over reserves 10000/10000). -/
def skimCall : Call := mkCall ((EthLib.Base.natToBytes 4 skimSel).map (·.toNat) ++ word 0x3000) σ

theorem skimCall_valid : Valid skimCall := Or.inr (Or.inl ⟨σ, 0x3000, by decide, rfl⟩)

set_option maxRecDepth 100000 in
theorem pre_skim (hk : PairAllowanceApart) :
    Pre SolidCore.Spec.Export.UniswapV2Pair.UniswapV2Pair
      (SolidCore.Spec.Export.UniswapV2Pair.UniswapV2Pair.spec.specs[9]'(by decide)) (ctxOf skimCall) preSt skimCall [0x3000] := by
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
    have := slotValue_σ_big (hk v.toNat (by omega))
    simp only [zeroAllowanceSlot] at this
    rw [this]
    rfl

set_option maxRecDepth 100000 in
/-- **Skim that moves the reserves, refused**: the published specification refuses every observable
of `skim(0x3000)` that succeeds with reserve0 moved off 10000 (the mutant's 11000). -/
theorem skimUpdate_refused (hk : PairAllowanceApart) (W : World) (obs : Observable) (hs : obs.success = true)
    (h0 : obs.storage 8 % 2 ^ 112 ≠ 10000) : ¬ Post W skimCall obs := by
  intro h
  have hmem : (SolidCore.Spec.Export.UniswapV2Pair.UniswapV2Pair.spec.specs[9]'(by decide)) ∈
      SolidCore.Spec.Export.UniswapV2Pair.UniswapV2Pair.spec.specs := List.getElem_mem _
  obtain ⟨rets, -, hens, -⟩ := (h _ hmem [0x3000] preSt (pre_skim hk)).1 hs
  have hK := hens _ (List.getElem_mem (by decide : 0 < (SolidCore.Spec.Export.UniswapV2Pair.UniswapV2Pair.spec.specs[9]'(by decide)).ensures.length))
  simp only [Nat.reducePow] at h0
  have h0i : ((obs.storage 8 : Nat) : Int) % 5192296858534827628530496329220096 ≠ 10000 := by omega
  simp [Bundle.sat, SolidCore.Spec.Export.UniswapV2Pair.UniswapV2Pair, eval, BinOp.apply, mkEnv,
    Env.cur, slotOf, Ty.ofBits, toWord, idStep, preSt, wordMod, slotValue, σ] at hK
  omega

/-- info: 'SolidCore.Spec.UniswapV2.PairSpec.Negative.skimUpdate_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms skimUpdate_refused

end SolidCore.Spec.UniswapV2.PairSpec.Negative

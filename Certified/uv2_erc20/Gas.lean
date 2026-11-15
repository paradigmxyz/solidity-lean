import Verify.ShapeCtxGasFrom
import uv2_erc20.GasGuard

-- Untrusted proof script: the kernel checks it. The certificate and the guarded program are
-- generated data (CtxGas.lean); the theorems below state what they give.

/-!
# UniswapV2ERC20.transfer: a proved gas bound on the exact runtime bytes (E8)

`G` = `gasBoundL cx.base N` = 22100 · (7 · 53) + 12 = 8199112: seven blocks (the most a call of
`transfer` runs, `GasGuard.N`), each of at most 53 items of the lowered program (the dispatcher's,
the largest block such a call runs), each charged 22100 gas, plus the memory up to 128 bytes.
22100 is at least the price of every instruction the checker admits under EIP-2929 and EIP-2200,
whatever the call finds warm or cold: an SSTORE that sets a zero slot it reads cold (20000 + 2100),
a cold SLOAD (2100), a KECCAK256 of 64 bytes, a LOG3 of 32 bytes. EthLib's interpreter meters the
accesses the run actually makes (its access sets start with the caller, the contract and the
precompiles warm, per EIP-2929), so the theorem holds of the real warm and cold slots, not of a
model of them.

* `gas_edge`: from every caller `a` (below `2 ^ 160`, not the contract itself), on every call of
  `transfer`'s selector, under every oracle whose CALLER is `a` and whose Keccak-256 is EthLib's,
  at every gas from `G` on, EthLib runs the exact bytes to exactly the final EVM IR's result
  (success, return data, revert data, logs, storage). Its only inputs are the kernel's checks of
  generated programs: `check_ok` (the checker with contexts and gas on the exact bytes against
  `evm11`) and the guard stage (`guard_ends`, `guard_run`). No premise mentions gas.
* `resources`: `Shapes.ResourcesFrom` for any valid-call predicate inside `transfer`'s selector and
  any source semantics per caller, from the functional stage from that source to `evm11` (E3∘E4:
  the hypothesis `stage`) and its totality (`total`). At `callerAddress` it is `Shapes.Resources`
  (`resources_at`).
* Negative controls: the checker refuses the bytes with the dispatcher's first jump target moved
  and with transfer's debit SSTORE dropped.
-/

namespace SolarTV.Export.UniswapV2ERC20.CtxGas

open SolarTV SolidCore.Refinement SolidCore.Refinement.Shapes SolidCore.Refinement.Solar

/-- **The proved gas bound** of a call of `transfer`. -/
def G : Nat := AssembleLoop.gasBoundL cx.base N

theorem G_eq : G = 8199112 := by decide +kernel

theorem G_lt : G < 2 ^ 64 := by rw [G_eq]; decide

theorem reads_false : cx.base.reads = false := rfl

/-- **The gas edge of UniswapV2ERC20.transfer on its exact runtime bytes, from any caller.** -/
theorem gas_edge : ∀ a, a < 2 ^ 160 → a ≠ selfAddress → ∀ o, AssembleLoop.OracleOkAt a o →
    ∀ call, TransferCall call → ∀ gas, G ≤ gas →
      ∃ obs, (evmirSem o).run prog call = some obs ∧
        Final.Target.runWithFrom a gas code call = some obs := by
  intro a ha hne o ho call hc gas hg
  obtain ⟨obs, hq, hb⟩ := gasEdge_ofXL check_ok reads_false (fun o call h => guard_ends o call h)
    (fun o call h => guard_run o call h) a ha hne o ho call hc gas hg
  exact ⟨obs, (AssembleCtx.sem_norm o prog call).symm.trans hq, hb⟩

/-- **Resources of UniswapV2ERC20.transfer from any caller**, from the functional stage. -/
theorem resources {Valid : Call → Prop} {run : Nat → Call → Option Observable}
    (hv : ∀ call, Valid call → TransferCall call)
    (total : ∀ a, a < 2 ^ 160 → a ≠ selfAddress → ∀ call, Valid call → ∃ obs, run a call = some obs)
    (stage : ∀ a, a < 2 ^ 160 → a ≠ selfAddress → ∀ call, Valid call → ∀ obs, run a call = some obs →
      (evmirSem (oracleFrom a)).run prog call = some obs) :
    ResourcesFrom run code Valid (fun _ => G) :=
  resourcesFrom_ofXL total
    (fun a ha hne call hc obs h => (AssembleCtx.sem_norm _ prog call).trans (stage a ha hne call hc obs h))
    check_ok reads_false
    (fun o call h => guard_ends o call (hv call h)) (fun o call h => guard_run o call (hv call h)) G_lt

/-- At `callerAddress`: `Shapes.Resources` of a source semantics. -/
theorem resources_at {S : Sem} {p : S.Prog} {Valid : Call → Prop}
    {run : Nat → Call → Option Observable} (hrun : run callerAddress = S.run p)
    (hv : ∀ call, Valid call → TransferCall call)
    (total : ∀ a, a < 2 ^ 160 → a ≠ selfAddress → ∀ call, Valid call → ∃ obs, run a call = some obs)
    (stage : ∀ a, a < 2 ^ 160 → a ≠ selfAddress → ∀ call, Valid call → ∀ obs, run a call = some obs →
      (evmirSem (oracleFrom a)).run prog call = some obs) :
    Resources S p code Valid (fun _ => G) :=
  (resources hv total stage).resources hrun

/-- The bytes with byte `i` replaced by `b`. -/
def mutant (i b : Nat) : ByteArray := ⟨((bytes.set i b).map UInt8.ofNat).toArray⟩

/-- A checker run whose walk of the bytes against the program fails refuses the bytes. -/
theorem refuses_of_walk {code' : ByteArray}
    (h : Assemble.walkS cx.base.offset (Assemble.bytesOf code') 0
      (Assemble.lower (AssembleCtx.norm prog) cx.base) = false) :
    AssembleCtxGas.checkXL F (AssembleCtx.norm prog) code' cx = false := by
  have hw := Assemble.walkS_drop (Assemble.bytesOf code') cx.base.offset
    (Assemble.lower (AssembleCtx.norm prog) cx.base) 0 (Nat.zero_le _)
  rw [List.drop_zero, h] at hw
  simp only [AssembleCtxGas.checkXL, ← hw, Bool.false_and]

set_option maxRecDepth 100000 in
/-- The checker refuses the bytes with the dispatcher's first jump target moved (byte 7). -/
theorem rejects_jump : AssembleCtxGas.checkXL F (AssembleCtx.norm prog) (mutant 7 0x64) cx = false :=
  refuses_of_walk (by decide +kernel)

set_option maxRecDepth 100000 in
/-- The checker refuses the bytes with transfer's debit SSTORE dropped, as POP (byte 0x427). -/
theorem rejects_sstore : AssembleCtxGas.checkXL F (AssembleCtx.norm prog) (mutant 0x427 0x50) cx = false :=
  refuses_of_walk (by decide +kernel)

/-- info: 'SolarTV.Export.UniswapV2ERC20.CtxGas.gas_edge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms gas_edge

/-- info: 'SolarTV.Export.UniswapV2ERC20.CtxGas.resources' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms resources

end SolarTV.Export.UniswapV2ERC20.CtxGas

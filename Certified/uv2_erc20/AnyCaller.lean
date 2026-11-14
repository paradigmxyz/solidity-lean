import uv2_erc20.Gas
import uv2_erc20.ProofsT.Stages

-- Untrusted proof script: the kernel checks it.

/-!
# UniswapV2ERC20.transfer's backend stages from any caller (E4, E4∘E5)

The backend stages (`uv2_erc20_transfer_mir_to_evmir`, E4) hold under every oracle, and the machine
reads CALLER from the oracle (`Oracle.caller`), so E4 is a statement about every caller: its proofs
execute `CALLER` as an unknown 160-bit word, never as `0x2000`. This module states that for the
calls of `transfer` and composes it with the gas edge (E5, `CtxGas.gas_edge`, also from any
caller) down to EthLib's run of the exact bytes:

* `stages_from`: E4 under the oracle of a call from any account `a` (`oracleFrom a`).
* `backend_any_caller`: from every caller `a` (below `2 ^ 160`, not the contract), under every
  oracle whose CALLER is `a` and whose Keccak-256 is EthLib's, every result the first lowered MIR
  `stage0` gives on a call of `transfer` is EthLib's result on the exact runtime bytes, at every
  gas from `G` = 8199112 on.
* `resources_any_caller`: `Shapes.ResourcesFrom` for any source semantics per caller, from a source
  stage per caller into `stage0` (E3 with a symbolic caller, the hypothesis `source`) and its
  totality: what E3 must give for the whole chain to hold from any caller.
* `any_caller_inhabited`: the premises hold of a caller other than `0x2000` (`0x3000`).

The negative control that a stage hardcoding the caller is refused is by execution, outside
Lean's build (the slice-stages RESULT: `CALLER` replaced by `PUSH 0x2000` in `evm11`).
-/

namespace SolarTV.Export.UniswapV2ERC20.AnyCaller

open SolarTV SolarTV.Machine SolidCore.Refinement SolidCore.Refinement.Shapes SolidCore.Refinement.Solar
open SolarTV.Milestone.Uv2Erc20T (scope uv2_erc20_transfer_mir_to_evmir)
open SolarTV.Export.UniswapV2ERC20.CtxGas (G code prog TransferCall gas_edge resources)

/-- A call of `transfer` is in the stages' scope: its selector is none of the excluded ones. -/
theorem transfer_scope {call : Call} (h : TransferCall call) : scope call := by
  unfold TransferCall at h
  simp only [scope, h]
  decide

/-- **E4 from any caller**: the backend stages under the oracle of a call from `a`. -/
theorem stages_from (a : Nat) :
    Stage (mirSem (oracleFrom a)) (evmirSem (oracleFrom a)) stage0 evm11 scope :=
  uv2_erc20_transfer_mir_to_evmir (oracleFrom a)

/-- **E4∘E5 from any caller**: the first lowered MIR's result on a call of `transfer` is EthLib's
result on the exact runtime bytes, from every caller, at every gas from `G` on. -/
theorem backend_any_caller : ∀ a, a < 2 ^ 160 → a ≠ selfAddress → ∀ o, AssembleLoop.OracleOkAt a o →
    ∀ call, TransferCall call → ∀ obs, (mirSem o).run stage0 call = some obs →
      ∀ gas, G ≤ gas → Final.Target.runWithFrom a gas code call = some obs := by
  intro a ha hne o ho call hc obs hrun gas hg
  have h4 := uv2_erc20_transfer_mir_to_evmir o call (transfer_scope hc) obs hrun
  obtain ⟨obs', hq, hb⟩ := gas_edge a ha hne o ho call hc gas hg
  rw [show (evmirSem o).run prog call = (evmirSem o).run evm11 call from rfl, h4] at hq
  cases hq
  exact hb

/-- **Resources from any caller, from a source stage per caller into `stage0`** (E3 with a symbolic
caller as the hypothesis `source`, with its totality `total`). -/
theorem resources_any_caller {Valid : Call → Prop} {run : Nat → Call → Option Observable}
    (hv : ∀ call, Valid call → TransferCall call)
    (total : ∀ a, a < 2 ^ 160 → a ≠ selfAddress → ∀ call, Valid call → ∃ obs, run a call = some obs)
    (source : ∀ a, a < 2 ^ 160 → a ≠ selfAddress → ∀ call, Valid call → ∀ obs, run a call = some obs →
      (mirSem (oracleFrom a)).run stage0 call = some obs) :
    ResourcesFrom run code Valid (fun _ => G) :=
  resources hv total fun a _ _ call hc obs h =>
    stages_from a call (transfer_scope (hv call hc)) obs (source a ‹_› ‹_› call hc obs h)

/-- The premises of `backend_any_caller` hold of a caller other than `0x2000`. -/
theorem any_caller_inhabited :
    ∃ a o, a ≠ callerAddress ∧ a < 2 ^ 160 ∧ a ≠ selfAddress ∧ AssembleLoop.OracleOkAt a o :=
  ⟨0x3000, oracleFrom 0x3000, by decide, by decide, by decide, oracleFrom_ok (by decide)⟩

/-- info: 'SolarTV.Export.UniswapV2ERC20.AnyCaller.stages_from' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms stages_from

/-- info: 'SolarTV.Export.UniswapV2ERC20.AnyCaller.backend_any_caller' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms backend_any_caller

/-- info: 'SolarTV.Export.UniswapV2ERC20.AnyCaller.resources_any_caller' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms resources_any_caller

/-- info: 'SolarTV.Export.UniswapV2ERC20.AnyCaller.any_caller_inhabited' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms any_caller_inhabited

end SolarTV.Export.UniswapV2ERC20.AnyCaller

# slice-runners: the runner premises (StaticRunner, CalleesRun) for call-free bytecode

Branch: solidity-lean `slice-runners/no-call-a1c`, one commit **0b1f8bb** on top of PR head **a1c3143**
(`alpharush/certified-translation`). Lean only; no solar change. Delivered as `slice-runners.bundle`
(range a1c3143..slice-runners/no-call-a1c) and `0001-runner-premises-call-free.patch`.
Apply: `git fetch storm/out/slice-runners/slice-runners.bundle slice-runners/no-call-a1c && git checkout FETCH_HEAD`
(or `git am 0001-*.patch` on a1c3143). No earlier work in this lane, so no wip/ bundle.

Files: `SolidCore/Refinement/Solar/AssembleNoCall.lean` (new), `SolidCore/Refinement/Solar/AssembleNoCallExample.lean`
(new), `lakefile.lean` (both added to the roots of `SolidCoreSolarRunOracle`). `erc20/NoCallERC20.lean.template`: the
UniswapV2ERC20 instantiation, which needs the generated `uv2_erc20.Ctx` (not built here, see below).

## Headline

1. **`StaticRunner` cannot be discharged: it is false.** EthLib's IDENTITY precompile returns its call data, so a message
   to address 4 carrying 2^256 bytes, with the gas to pay for them (15 + 3·2^251 < 2^255), ends with an output of 2^256
   bytes, against `AssembleCallCut.OutputFits`. Proved: `¬ StaticRunner (2^255)`, `¬ OutputRunner (2^255)`, hence
   `¬ ∀ gas, StaticRunner gas`, `¬ ∀ gas < 2^256, StaticRunner gas`, `¬ ∀ gas, OutputRunner gas`. Every theorem that takes
   `hP : ∀ gas, StaticRunner gas` or `hO : ∀ gas, OutputRunner gas` is vacuous: `AssembleCallSeg.assembly_of_checkCB`,
   `holds_of_checkCB`, `holds_of_checkCB_named`, `runs_shape_of_checkCB`, `AssembleCallStaticRunner.holds_of_checkCB_out`,
   `AssembleCtx.assembly_of_checkXB(_norm)`, `AssembleCallExample.*`, and the ERC20 `EndToEnd.published`,
   `EndToEndAll.published`, `functional_tf`, `compiled_tf`, `EndToEndTFSpec`. (The reduction to `OutputRunner` in
   AssembleCallStaticRunner.lean is correct, but `OutputRunner` is the false half.)
2. **For call-free bytecode neither premise is needed** (general theorems, no runner hypothesis), from a syntactic check
   over the exact bytes.
3. **UniswapV2ERC20's runtime is not call-free**: permit calls ECRECOVER by STATICCALL. So the call-free route does not
   reach the first slice, and E5 for UniswapV2ERC20.transfer stays blocked on two named bridges (below).

## Proved (all: axioms propext, Classical.choice, Quot.sound, checked by #guard_msgs; no sorry, no native_decide)

Namespace `SolidCore.Refinement.Solar.AssembleNoCall`.

| theorem | statement (premises exactly as in Lean) |
|---|---|
| `identity_output` | `m.shouldTransferValue = false → precompileAddress .fusaka m = some 4 → m.disablePrecompiles = false → Identity.gasCost m.data.size ≤ m.gas → ∃ ended, processMessage .fusaka m state substate = .ok ended ∧ ended.val.output = m.data` |
| `not_outputRunner_of_lt` | `bigGas < gas → Evm .fusaka Nat → ¬ OutputRunner gas` (`bigGas := Identity.gasCost (2^256)`) |
| `not_outputRunner`, `not_staticRunner` | `¬ OutputRunner (2^255)`, `¬ StaticRunner (2^255)` |
| `not_forall_staticRunner`, `not_forall_lt_staticRunner`, `not_forall_outputRunner` | `¬ ∀ gas, StaticRunner gas`, `¬ ∀ gas, gas < 2^256 → StaticRunner gas`, `¬ ∀ gas, OutputRunner gas` |
| `callFree` (def) | `(decodeFrom (bytesOf code) code.size 0).all (instrFree ·.2)`: linear decode from 0 (PUSH immediates skipped, as the walk reads), no CREATE f0, CALL f1, CALLCODE f2, DELEGATECALL f4, CREATE2 f5, STATICCALL fa, RETURNDATASIZE 3d, RETURNDATACOPY 3e |
| `noCallI_of_callFree` | `Seg (bytesOf code) c.offset 0 (lower p c) code.size → callFree code = true → ∀ b < p.blocks.length, ∀ i ∈ p.blocks[b], isScI i = false ∧ isRdsI i = false ∧ isRdcI i = false` |
| `checkC_of_checkCB_callFree` | `checkCB p code c mx = true → callFree code = true → checkC p code (noCallCert c) mx = true` (`noCallCert c := {c with calls := false}`) |
| `checkX_of_checkXB_callFree` | `checkXB p code cx = true → callFree code = true → checkX p code (noCallCtx cx) = true` |
| `assembly_of_checkCB_callFree` | `checkCB p code c mx = true → callFree code = true → ∀ gas < 2^256, ∀ call, scope call → ∃ o W, W.Open ∧ CallsAgree o W ∧ Within (evmirSem o) (ethLibWith gas) p code (· = call)` |
| `runs_shape_of_checkCB_callFree` | `runs_shape_of_checkCB` without `hP`/`hQ`, plus `callFree code = true`; gives `CertOk c o` for the original certificate |
| `holds_of_checkCB_callFree` | `holds_of_checkCB` (source, fin, lowering, backend, `checkCB`) with `callFree code = true` in place of `hP`, `hQ` → `Final.Holds (Final.ethLibWith gas) code spec` for every `gas < 2^256` |
| `assembly_of_checkXB_norm_callFree` | `assembly_of_checkXB_norm` (the shape of an exported `Ctx.bytecode`) without `hP`/`hQ`, plus `callFree code = true` |
| `noFaByte` (def), `calleesRun_of_noFaByte`, `calleesRunR_of_noFaByte` | `noFaByte code = true → ∀ gas call, CalleesRun gas code call` (and `CalleesRunR`). `noFaByte`: no byte 0xfa anywhere, immediates included |

Why `CalleesRun` needs the raw-byte check: `CalleesOk` quantifies over **every** frame at any counter whose byte is 0xfa
(not only frames the run reaches, not only instruction starts), so a scan that skips PUSH immediates cannot discharge it
as stated. `callFree` code does not need it: `holds_of_checkCB_callFree` drops it.

Controls (`SolidCore.Refinement.Solar.AssembleNoCallExample`, all `decide +kernel`):
- positive: `AssembleDynExample.code` is `callFree` and `noFaByte`; `checkCB` accepts its program under `{cert with calls := true}`;
  `dyn_runs` is its per-run theorem with no runner hypothesis; `dyn_calleesRun` at every gas and call.
- `dynPushFa` (0xfa only as a PUSH1 immediate): `callFree = true`, `noFaByte = false` (the scan skips immediates).
- negative: `dynStatic` (MLOAD byte replaced by STATICCALL) and `AssembleCallExample.code` fail `callFree` (and `noFaByte`).

## UniswapV2ERC20 (the first slice)

Fresh bytes: solar 38b5232 (`alpharush/certified`), `solar -Ogas --evm-version osaka --emit bin-runtime` on the port
(`solar-tv/uniswap-v2/port.py`), 1183 bytes. Kernel-evaluated in a scratch module (bytes not committed: GPL-derived):
`callFree = false`, `noFaByte = false`; call opcodes at pc 903 STATICCALL (permit → ECRECOVER), 1158 RETURNDATASIZE,
1161 RETURNDATACOPY, 1162 RETURNDATASIZE. `erc20/NoCallERC20.lean.template` states the same against
`SolarTV.Export.UniswapV2ERC20.Ctx.code` (`decide +kernel`) plus `staticRunner_premise_false`; it is not built here
because `uv2_erc20.Ctx` is generated and in no lean_lib.

CERTIFICATION_TARGET (a1c3143) says for the slice "No external calls: StaticRunner/CalleesRun discharged". That is not true
of these bytes. Proposed text: "The runtime makes one STATICCALL (permit → ECRECOVER). StaticRunner as stated is false
(AssembleNoCall.not_forall_staticRunner); E5 for transfer needs a message-scoped runner premise and a reachability-scoped
CalleesRun (bridges B1, B2)."

## Missing bridges (block E5 → CERTIFIED for UniswapV2ERC20.transfer)

- **B1 runner premise, restated soundly.** Replace `StaticRunner` by a premise over the messages a STATICCALL can send,
  e.g. `Meets (fun _ m child => m.data.size < 2^256 → StaticNoLogs … ∧ OutputFits …) (processRunner gas)`, prove it of EthLib
  (RETURN/REVERT outputs come from U256 sizes; IDENTITY returns its data; the other precompiles' outputs are bounded), and
  change `AssembleCallCut.staticcall_cut` to use it with the call's input size (`inSize : U256`). Not started.
- **B2 callees, scoped to reachable frames.** `CalleesRun` must quantify over the frames the run reaches (thread a
  reachability witness through `AssembleCallSeg.segS`), and then transfer-selector runs must be shown never to reach
  pc 903 (selector dispatch), or permit's site needs `EcrecoverAgree`/3000 gas only for permit calls. Not started.
- hash premise: the lane hash-scope's `ScopedSep (transferFootprint 1 caller to)` (placeholder name per its RESULT.md).

## Build (Hand: 5 cores, 14 GB; Lean v4.35.0, LEAN_NUM_THREADS=1, -KleanMemory=6000)

- `lake build -KleanMemory=6000 SolidCoreSolarRunOracle` on 0b1f8bb: **exit 0**, 2615 jobs, peak RSS 2305 MB (whole lake run).
- forced rebuild of the two new modules: exit 0; `AssembleNoCall` 2.3 s, `AssembleNoCallExample` 1.5 s.
- scratch ERC20 check: exit 0.


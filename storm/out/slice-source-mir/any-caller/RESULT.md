# slice-source-mir / any-caller: E3 for UniswapV2ERC20.transfer from every caller

Base: solidity-lean `alpharush/certified-translation` at d0ab5d6 (E3/E4/E5/E7/E8, ScopedSep, NoCall merged).
Solar: #2637 head 697fc68 for the stage export (`uniswap_v2_erc20_stages.sh`), and the CI pin 6edf8f4
(`uniswap_v2_stages.sh`, an ancestor of 697fc68). Both export the same stage0
(`Stage0.lean` sha256 dbbdffe888c2891471285365b6312cdb334aeb58b7d0989cca4e3a9cd8b87a59, the same as the
fixed-caller delivery).

Deliverable: `0001-feat-uniswap-v2-transfer-E3-for-every-caller.patch` (one commit df5c3cc, 36 files,
+742 -84) and `slice-source-mir-any-caller.bundle` (`git bundle` of d0ab5d6..caller, the same commit).
`git am` applies it to d0ab5d6 cleanly.

## Result

E3 for `transfer(address,uint256)` is proved for every caller `a < 2^160` with one theorem. The caller
is a symbolic word, so the kernel evaluates the generic check once. There is no per-address instance.

```lean
-- SolidCore.Spec.UniswapV2.ERC20.SourceMirFrom
theorem transfer_stage_from (a : Nat) (ha : a < 2 ^ 160) (o : SolarTV.Machine.Oracle) (ho : FromOk a o)
    {c : CheckedContract} (hc : UniswapV2ERC20.contract? = .ok c) :
    SolarTV.Stage (solidCoreFrom a fuel) (SolarTV.MIR.Lowered.moduleSem o) c
      SolarTV.Export.UniswapV2ERC20.stage0 (genericValid0 fns deployed)

theorem transfer_source_mir_any_caller :
    (∃ c, contract? = .ok c ∧ ∀ a, a < 2 ^ 160 → ∀ o, FromOk a o →
        SolarTV.Stage (solidCoreFrom a fuel) (moduleSem o) c stage0 (genericValid0 fns deployed)) ∧
    (∀ a, a < 2 ^ 160 → ∃ o, FromOk a o) ∧ (∃ call, genericValid0 fns deployed call)
```

`solidCoreFrom a` runs SolidCore's checked contract, deployed by `callerAddress` as before, on a call
sent by `a` (`Source.runFrom a`). `Stage` means each valid call shows the same SolidCore and MIR
observables: status, return data, revert data, storage and logs. At `a = callerAddress` it is the
fixed-caller stage: `solidCoreFrom callerAddress = solidCore` holds by `rfl`
(`transfer_stage_callerAddress`).

## How (generic, not per contract)

* `WExpr.caller`: a new atom whose value is the new `Val.caller` field. `msg.sender` erases to
  `SymState.caller`. That field defaults to the literal `callerWord`, so every existing fixed-caller check,
  stage and proof keeps its meaning. `initFrom` sets it to `.caller`.
* MIR side: `EnvFlags.sym` and `EnvFlags.allSym` make `CALLER` read `WExpr.caller` rather than the
  literal. `EnvOk` and `EnvAsk` take the caller from the valuation.
* `Generic.checkSym` (`StageFrom.lean`) erases with `initFrom` and the fact `caller < 2^160` (`callerFact`),
  then compares the trees under `.allSym`. `Generic.stageFrom` and `stageDeployedFrom` turn acceptance into
  the stage for every `a < 2^160` and every `o` with `FromOk a o`. The source side's `source_run_from`
  generalizes `source_run_clean` with `ExprRel` and `StmtRel` carrying `ctx.sender = S.caller.eval ρ`.

## Exact premises

* `a < 2 ^ 160`: the caller is an address.
* `FromOk a o`: `(o.caller.setWidth 256).toNat = a`, so the oracle's `CALLER` is `a`, and `HashOk o`, so the
  oracle's Keccak-256 of two words is SolidCore's `solHash`, which is Keccak-256. This is not a
  hash-separation premise. Both sides compute the same slots, so no injectivity is assumed.
  `fromOk_inhabited` shows the premise holds for every `a`: EthLib's Keccak-256 with `caller := a`.
* Valid calls are the same as in the fixed-caller E3: transfer on any two argument words, callvalue 0, and
  any storage that lists slot 3 (`Covers deployed`).
* The deployer is fixed at `callerAddress`. Transfer's constructor storage `deployed` does not depend on
  it, and only the call's sender varies.

## Negative controls (refused by execution)

The new mutant **PinnedCaller** (`scripts/verify/uniswap_v2_erc20_mutants.py`) replaces transfer's
`CALLER` with the constant 0x2000. It shows that the generalization adds a check:

* `SourceMirPinned.pinned_fixed_accepts` (`kernel_rfl`): the old fixed-caller check **accepts** the
  pinned stage0, because at caller 0x2000 the two programs agree.
* `SourceMirFromNeg.refuses_PinnedCaller` (`kernel_rfl`): the symbolic-caller check **refuses** it.
* The 8 earlier mutants are refused by the symbolic check too (`refuses_NoDebit`, `WrongSlot`,
  `NoOverflowCheck`, `NoUnderflowCheck`, `WrongTopic`, `WrongReturn`, `WrongRevertData`,
  `SwappedLogArgs`).

## Not covered (named, not hidden)

1. **Byte side (E5) is still fixed-caller.** This lane generalizes source to MIR. The MIR backend stages
   (E4) already hold under every oracle. EthLib's byte run still sends from `callerAddress`
   (`Target.txEnvFrom a` exists in `AssembleCtxGasFrom.lean` and is the starting point), so composing E3
   through E5 for every caller needs E5 restated with `txEnvFrom a`.
2. The approve and transferFrom stages (Nested) and the other contracts' stages still use the
   fixed-caller check. They are unchanged and rebuilt, and `checkSym` applies to them as is.

## Build receipts

Hosted Hand: 5 cores, 14 GB, Lean v4.35.0. Each command was `lake -R build -KleanMemory=<M>`. Peak is
the largest single `lean` process RSS, sampled every second.

New and E3 modules (`LEAN_NUM_THREADS=1`, `-M 6000`):

| Module | Exit | Peak MB |
|---|---|---|
| SolidCore.Refinement.Generic.StageFrom | 0 | 2493 |
| Contracts.UniswapV2.ERC20.SourceMirDefs | 0 | 2456 |
| Contracts.UniswapV2.ERC20.SourceMirCheck | 0 | 5369 |
| Contracts.UniswapV2.ERC20.SourceMirDeploy | 0 | 5892 |
| Contracts.UniswapV2.ERC20.SourceMir | 0 | 4200 |
| Contracts.UniswapV2.ERC20.SourceMirNeg | 0 | 5299 |
| Contracts.UniswapV2.ERC20.SourceMirFromDefs | 0 | 1470 |
| Contracts.UniswapV2.ERC20.SourceMirFromCheck (`checkFrom_eq`) | 0 | 5371 |
| Contracts.UniswapV2.ERC20.SourceMirFrom | 0 | 5258 |
| Contracts.UniswapV2.ERC20.SourceMirFromNeg (9 mutants) | 0 | 5376 |
| Contracts.UniswapV2.ERC20.SourceMirPinned | 0 | 5376 |

The CI workflow's steps (`.github/workflows/refinement.yml`) were rerun after the change, in order:

| Step | Exit | Peak MB |
|---|---|---|
| `EvmRules SolarTV W1Proofs` (-M 3000) | 0 | 1707 |
| Certified contracts (-M 3000) | 1 (see note a) | 3000 |
| Verification libraries and Contracts (-M 6000) | 0 | 3622 |
| `uniswap_v2_gen.sh`, `ContractsUniswapV2` | 0 | 5394 |
| `ContractsUniswapV2Pair` (-M 6000) | 0 except `UniswapV2Pair__mintFee` (see note b) | 5715 |
| `uniswap_v2_spec.sh` (solar-verify at 91fc248), `ContractsUniswapV2ERC20Spec` | 0 | 5921 |
| `uniswap_v2_stages.sh` (solar at 6edf8f4), `uv2_erc20 ContractsUniswapV2ERC20SourceMir` | 0 | 4705 |
| `uniswap_v2_stage0_mutants.py`, `uniswap_v2_trees.py`, `uv2_erc20 ContractsUniswapV2ERC20Nested` | 0 | 5894 |
| SolidCore milestones and `Axioms.*` (-M 7000) | 0 | 3120 |
| `scripts/refinement/axiom-audit.sh` | 0 | 2855 |
| `scripts/refinement/check.sh` | 0 | 3251 |

Notes, both checked against an unchanged d0ab5d6 worktree on the same Hand:

* a. `Contracts.Token.VC.Burn` exceeds `-M 3000` in the interpreter: 3196 MB with the change and 3176 MB at
  d0ab5d6. The failure predates this change. Built at `-M 6000`, it passes.
* b. `Contracts.UniswapV2.Pair.Fn.UniswapV2Pair__mintFee` needs 6081 MB with the change and 6082 MB at
  d0ab5d6. It does not import the changed generic modules. The failure predates this change. At `-M 9000`
  it passes, and the rest of `ContractsUniswapV2Pair` then builds at `-M 6000`.

Earlier fixes in the regression: `StmtRel.congr` takes a `caller` equation, which defaults to `rfl`, and
the CallFamilies sources gave their anonymous `SymState` constructors the fourth field.

## Axioms

`lake env lean -M 6000 AnyCallerAxioms.lean` exits 0 with a peak of 2610 MB. Every theorem printed
depends on exactly `[propext, Classical.choice, Quot.sound]`: `Generic.stageFrom`, `stageDeployedFrom`,
`source_run_from`, `solidCoreFrom_callerAddress`, `checkFrom_eq`, `checkFrom_ok`, `transfer_stage_from`,
`fromOk_inhabited`, `transfer_source_mir_any_caller`, `transfer_stage_callerAddress`, `refuses_PinnedCaller`,
`refuses_NoDebit`, `pinned_fixed_accepts` and the fixed-caller `SourceMir.transfer_source_mir`.
`SourceMirFrom.lean` pins the axioms of `transfer_source_mir_any_caller` and `transfer_stage_from` with
`#guard_msgs`. A scan of the diff's added lines for sorry, native_decide, bv_decide, ofReduceBool, axiom,
implemented_by and extern found nothing. The generated GPL-derived sources and stages are not committed.

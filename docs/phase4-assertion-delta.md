# Phase 4 — observation-layer deletion: assertion delta

Phase 4 deletes the speculative observation layer (all `*Observation` structures,
`observe*` walkers, and their support glue) from the semantics modules and the
witness corpus. This file enumerates every change to the harness manifest's
assertion set, classified per the roadmap rule: a witness that checks **behavior**
(return value, revert payload, storage readback, log, call result) is re-expressed
against plain interpreter results and kept; a witness that inspects only the
**observation record** is dropped.

Manifest eval count: **420 → 419** (net −1).

## Dropped (observation-record-only): 1

- **`abi-malformed`, eval #3** — built three `SourceUnitDeploymentAbiObservation`
  records via `SourceUnit.observeDeploymentAbiAtFrom` and inspected their
  `constructorParamAbiCleanups?`, `decodedArgs?`, `deployment?`, and `result?`
  fields. The record fields are observation-layer internals. Its one behavioral
  claim — malformed constructor calldata is rejected (strict ABI decode fails →
  deployment reverts empty) — has no plain re-expression target: the
  deployment-ABI *entry itself* was the observe-layer function
  (`observeDeploymentAbiAtFrom` → `observeDeploymentAtFrom?`), and there is no
  calldata-driven constructor path in the plain interpreter (`constructContract`
  takes already-decoded `Value` args, not raw calldata). The underlying strict
  ABI-decode-rejection mechanism (`ABI.decodeFunctionArgsStrict?`) remains covered
  behaviorally by `abi-malformed` evals #0 and #1 at the function-entry level
  (malformed `bytes`/`bool`/`address`/`uint8`/array args rejected). This is a
  documented, intentional coverage delta of the kind ROADMAP definition-of-done
  #7 anticipates.

## Re-expressed (external-interaction transcript): 8

Eight evals across `try-catch` (#2, #3), `contract-creation` (#1),
`create-options` (#2), `high-level-call-options` (#3, #4), and
`low-level-call-options` (#2, #3) checked the emitted external-call/create
transcript via `(CallResult.observe self).state.externalInteractions`.
`externalInteractions` is a **real `State` field** (behavior), and the deleted
`State.observeEffects` copied it verbatim (no filtering), so this is faithfully
re-expressed against the plain call result: a new accessor
`CallResult.resultState : CallResult → State` returns the post-execution state,
and each eval now reads `(CallResult.resultState r).externalInteractions`. No
assertion content changed; the observation wrapper was the only thing removed.

## Re-expressed (mixed → behavior-only kept): 2

Both evals were a conjunction of a typecheck-**acceptance** behavior and an
observation-walker result. Each was split: the acceptance behavior is kept
(re-expressed against the plain checker), the observation-walker conjunct dropped.
The eval count is unchanged for these two (still one eval each).

- **`checked-arithmetic`, eval #4** — was
  `checkedArithmeticContractAccepted && binaryArithmeticObservationMatches`.
  Re-expressed to the acceptance behavior alone via a renamed witness
  `checkedBinaryArithmeticAccepted := Except.ok checkedArithmeticContractAccepted`
  (`Result.isOk (TypecheckedInput.checkedSourceUnit checkedArithmeticContract)`).
  The arithmetic *computation/overflow* behavior is covered by the case's other
  evals; only the per-construct observation walker was dropped.
- **`terminal-statements`, eval #6** — was two `ContractDecl.checkedContract`
  acceptance checks plus `terminalEvaluationObservationMatches`. Re-expressed to
  the two acceptance checks alone via a renamed witness
  `checkedTerminalStatementContractsAccepted` (drops only the observation walker).

## Semantics/witness code removed (no assertion impact)

- Semantics: all `*Observation` structures + `observe*` walkers from
  `ABI.lean`, `Interface.lean`, `Interpreter.lean` (~4.8k lines). The two live
  dual-use choke points (`observeLowLevelCallResolution`,
  `observeContractCreationResolution`, whose `.result` the interpreter consumed)
  were replaced by plain result functions `Context.lowLevelCallResult` /
  `Context.contractCreationResult` before deletion — no behavior change.
- Witness corpus: all observation-referencing witness defs plus 5 now-dead
  aggregator defs that only combined them (~7k lines). None were referenced by
  the manifest (verified), so no asserted coverage was lost.
- Storage-layout machinery (`StorageLayout`, `StorageLayoutCursor`, `slotSpan`,
  `Context.storageSlot?`, packing/path resolution) was **not** touched — it is
  core semantics, not observation code.

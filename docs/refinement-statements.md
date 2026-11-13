# Refinement statements, end to end

What the theorems from SolidCore to solar's bytecode state, in which direction, how fuel and
gas enter, why none of them holds vacuously, and what is still open. Lean names are relative to
`SolidCore.Refinement` unless they start with `SolarTV`.

## The objects

* `Call` (`SolarTV.Call`): call data, call value, and the callee's storage before the call as
  (slot, value) pairs, a later pair winning. One frame, caller `0x2000`, callee `0x1000`.
* `Observable` (`SolarTV.Observable`): `success`, `output` (return data on success, revert data on
  failure), `logs` (topics and data, in order) and `storage : Nat → Nat` (the callee's whole storage
  after the call). A failed call has no logs and its initial storage (`Sem.FailureConvention`,
  proved for `ethLib` and `solidCore` in `Behaviours.lean`).
* `Sem`: a type of programs and `run : Prog → Call → Option Observable`, a function, so a program has
  at most one observable per call. `none` means no observable: the run did not finish, or used
  something its semantics leaves undefined.
  * `solidCore fuel`: `Source.run fuel`, SolidCore with a fixed statement fuel. Running out of statement
    fuel is `none`.
  * `SolarTV.mirSem o`, `SolarTV.evmirSem o`: solar's lowered MIR and EVM IR under an oracle `o` (caller,
    Keccak, the results of calls out). `run` is the end some fuel reaches (`Layer.result`), which is unique
    because each layer is deterministic and fuel-monotone (`Layer.mono`), so there is no fuel cut-off:
    `none` means no fuel reaches an end.
  * `ethLib`: `Target.run`, one `processMessage` at Fusaka with `gasLimit = 10_000_000` gas. Running out of
    gas, `INVALID` and every exceptional halt are failures (`success = false`), never `none`; `none` only when
    `processMessage` raises.

## The relations

All four are stated per call, for every call in a scope `scope : Call → Prop`.

| name | statement | direction |
|---|---|---|
| `Stage A B p q scope` | `A.run p call = some obs → B.run q call = some obs` | forward, partial |
| `Backward A B p q scope` | `B.run q call = some obs → A.run p call = some obs` | target ⊆ source |
| `Total A B p q scope` | `∃ obs, A.run p call = some obs ∧ B.run q call = some obs` | both finish, equal |
| `Satisfies S p scope pre post` | `pre call → ∃ obs, S.run p call = some obs ∧ post call obs` | total correctness |

`Refines fuel c code scope` is `Total (solidCore fuel) ethLib c code scope` (`refines_iff_total`, by `Iff.rfl`).
solar-tv's `Certified A B o p q scope` (every end of `p` some fuel reaches, `q` reaches an end that
`Agree`s with it) gives a `Stage` (`stage_of_certified`); `Agree` is finer than equal observables (it
tells `invalid` from `revert []` and compares transient storage and the world on success).

### How they relate (`Behaviours.lean`, all proved)

* `total_iff_stage`: `Total ↔ Stage ∧ Defined A p scope`.
* `total_iff_backward`: `Total ↔ Backward ∧ Defined B q scope`.
* `Total.backward`, `Refines.backward`: every observable of the bytecode on a call of the scope is
  SolidCore's observable of that call: the same success, the same return or revert data, the same
  logs and the same final storage.
* `Stage.backward_of_defined`: a stage whose source finishes on the scope is backward.
* `Backward.failure`: a backward simulation from a semantics whose failures roll back gives a target
  whose failures roll back.

### Composition

* `Stage.trans` (solar-tv), `Total.trans`, `Backward.trans`: each relation composes with itself on a common
  scope.
* `Total.trans_stage`: a total first stage followed by plain stages is total. A chain is as total as
  its first source, so the only totality to prove is SolidCore's.
* `Satisfies.of_stage` carries a specification forward through a stage, `Satisfies.of_backward`
  through a backward simulation onto a defined target, and `Satisfies.total_of_stage` turns a
  specification and a stage into a total refinement on `scope ∧ pre`.
* `bytecode_total_of_stages`: from SolidCore's specification and the three stages (lowering, backend,
  assembly), both `Refines fuel c code (scope ∧ pre)` and `Satisfies ethLib code scope pre post`.

## Vacuity

A bare `Stage` (and solar-tv's `Certified`) says nothing on a call its source does not finish:
`Stage.of_never` proves a stage from a never-finishing source to any target, and `never_stage_total`
exhibits one that is a stage but not total. Every end-to-end theorem must therefore rest on the
source's totality, and these are the places it comes from:

* the headline theorems (`Headline.c1`, `w1`, `w4`, `c4`, `w5`, `w1_staged`) and counter's
  `certified*`: from `Satisfies (solidCore fuel)`, which requires SolidCore to finish every specified
  call, or from `Refines` directly;
* the generic source stage: its proof runs SolidCore to an observable on every call of its scope
  (`Generic.source_run`), now exposed as `Generic.definedAt` / `Generic.defined` and the total forms
  `Generic.totalAtWith`, `totalAt`, `totalAtEnv`, `totalAtCaller` (`Generic/Total.lean`);
* bank and events, whose `certified` theorems are bare stages under an oracle hypothesis
  (`Assemble.OracleOk`): `Solar.Bank.defined` and `Solar.Events.defined` (`Solar/Total.lean`) give SolidCore's
  totality on their whole scope (every function, any argument words, any storage, no value), so
  `Bank.refines_of_stage` / `Events.refines_of_stage` turn their stages into `Refines`;
  `Solar.ethOracle_sourceEnvOk` shows the source stage's oracle hypothesis is met by EthLib's caller and
  Keccak (the oracle `Assemble.ethOracle_ok` already shows meets `OracleOk`). The one-line composition
  `Bank.refines_of_stage hc (Bank.certified (Assemble.ethOracle o) (Assemble.ethOracle_ok o)
  Bank.ethKeccakAgree hc)` is not checked yet: `Bank.certified` does not build at this branch's solar-tv pin
  (below).

The relations tell observables apart: on `Fixed` (programs are their own observables) a stage
between two observables holds iff they are equal (`Fixed.stage_iff`, `total_iff`, `backward_iff`), and
`stage_rejects_success`, `_output`, `_logs`, `_storage` each refute a stage between observables differing
in one field.

### Concrete calls (`NonVacuity.lean`)

For each headline, a call where both sides finish and the relation is checked, read off the
theorems alone (no evaluation of either semantics outside them):

| headline | call | bytecode and SolidCore both give |
|---|---|---|
| w5 | `f(1, 2)` | success, `word 3`, no logs, storage 0 |
| w5 | `f(2^256-1, 1)` | failure, `Panic(0x11)`, no logs, storage 0 |
| w1 | `f(41)`, `f(2^256-1)` | `word 42`; `Panic(0x11)` |
| w4 | `set(9)` | success, no output, slot 0 holds 9 |
| c1 | `f(2)`, `f(85)` | `word 7`; `Panic(0x11)` |
| c4 | `add(3)` from the deployed storage | `word 3`, slot 0 holds `3 + (7 xor 3) * 256` |
| c4 | `add(256)` (dirty `uint8`) | failure, empty data, deployed storage kept |

Each `*_rejects` theorem refutes a neighbouring observable (a wrong word, success instead of a
revert, a wrong slot). With a relation that related everything none of these would be provable.

## Fuel and gas

* SolidCore: a run that runs out of statement fuel is `none`, which refutes `Total`, `Refines` and
  `Satisfies`; it never satisfies them. Expression and ABI-decoding fuel are structural (computed from
  the expression or type) and their exhaustion is a revert; the design argues it is unreachable,
  which is not proved. `FuelMonotonicity.lean` proves the statement-fuel interpreter's trees equal at
  every higher fuel when no branch runs out (`callTree_fuel_mono`). **Open**: the same at the folded
  seam `Source.run` (`Source.run n c call = some obs → n ≤ m → Source.run m c call = some obs`). It
  needs a per-path form of the tree theorem, since the fold answers precompile and resource requests
  and a successful fold says nothing about other branches.
* solar's MIR and EVM IR: no fuel cut-off (`Layer.result`).
* EthLib: one fixed gas, `gasLimit`. `Total` at it forces the bytecode not to run out of gas on any call of
  the scope where SolidCore finishes (it would give `success = false` where SolidCore succeeds).
  **Open**: every other gas. The intended statement, with `Target.runGas g` the same message with `g`
  gas and `oog call = ⟨false, [], [], slotValue call.storage⟩`:

  `∀ g, ∀ call, scope call → ∀ obs, Target.runGas g code call = some obs → Source.run fuel c call = some obs ∨ obs = oog call`

  together with `Refines` at `gasLimit`, which keeps it from relating an always-failing bytecode. It
  needs EthLib's gas monotonicity for the frame; the composition work has started on this
  (`Within`, `compose_anyGas`). Note that `oog call` is also the observable of `revert(0, 0)`: the
  observable does not tell the two apart (nor `INVALID`), only gas consumption does.

## Build state at this pin (solar-tv 2144dccb)

* `SolidCore/Refinement/Solar/Assemble.lean` fails: solar-tv's `dup`/`swap` now take `Fin 256` and the
  assembly proofs expect `Fin 16`. Everything that imports it (every assembly stage, `Bank.certified`,
  `Events.certified`, the counter milestone) does not build here.
* solar-tv's own bank and events milestone run proofs (`milestone/bank/Proofs/Runs/Sched.lean`, `Evm1` to
  `Evm11`, and the events ones) fail in `sym_exec`, so `SolarTV.Milestone.Bank.evm*_run` depend on
  `sorryAx` at this pin. A newer solar-tv is expected to fix both.
* Built and checked here: `Behaviours.lean`, `Generic/Total.lean`, `NonVacuity.lean` (on the headline
  theorems, which do not import the assembly stage) and `Solar/Total.lean`.

## Assumptions every theorem keeps

From `Statement.lean`: one frame and a fixed environment (no block or account reads, no calls out:
solar-tv's `FrameLocal` rejects `CALL`, `CREATE`, balance, environment and `GAS` opcodes); the bytecode
starts from runtime code with the call's storage while SolidCore runs its constructor first; transient
storage is not observed; one gas amount (above). The oracle hypotheses of the staged theorems are
satisfiable (`Solar.ethOracle_sourceEnvOk`, `Assemble.ethOracle_ok`).

## Checked

`#print axioms` for the new theorems is pinned with `#guard_msgs` in each file: `propext`,
`Classical.choice` and `Quot.sound` only. No `sorry`, `native_decide` or `bv_decide`.

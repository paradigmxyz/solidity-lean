# Held-out acceptance contracts

Contracts for the generic certification driver that have **no hand-written proofs** anywhere in
this repository: nothing under Certified/, Contracts/ or tests/ was written for them. The driver
has to get each one from its source and spec alone: compile it freshly with solar, export
the stages, generate the proofs and kernel-check the fixed generic theorem over the exact fresh
bytes. The specs are solar-verify NatSpec annotations (`@custom:requires`, `@custom:ensures`,
`@custom:invariant`, `@custom:ghost`, `@custom:decreases`) in the sources themselves.

| contract | what it exercises | expected |
|---|---|---|
| [Meter.sol](Meter.sol) | inside the generic source stage at bc6da61b: no constructor, no loop, no mapping, no reason string, no internal call; checked addition, one branch | Certified |
| [Gate.sol](Gate.sol) | the same envelope; `require` without a reason (empty revert) | Certified |
| [Clamp.sol](Clamp.sol) | branches, pure functions, checked comparisons, one guarded storage write, a contract invariant; no mapping, no hash, no loop | Certified |
| [StepSum.sol](StepSum.sol) | a bounded loop with a supplied invariant and variant (`triangle`), a checked addition against a storage cap | Certified (loop invariant supplied in the source and kernel-checked) |
| [Band.sol](Band.sol) | Clamp renamed, with constants in place of stored bounds | Certified |
| [EmptyRevert.sol](EmptyRevert.sol) | an empty revert next to a bounded loop (revert, not out of gas) | Certified |
| [Registry.sol](Registry.sol) | a `mapping(address => bool)`, an owner check, a ghost counter invariant, an indexed event | Certified |

At bc6da61b the generic source stage does not yet cover constructor parameters (Clamp, StepSum),
early returns in pure functions (Clamp.clamp), internal calls and constants (Band), mappings and
reason strings (Registry) or loops (StepSum, EmptyRevert): until it does, the driver must report
those BLOCKED with the reason, never Certified. Meter and Gate are the held-out targets inside it.

Order for the driver: Meter and Gate first; then Clamp first (straight-line code, smallest proof surface), then StepSum
(the loop), then Registry (keccak slots and logs). None makes an external call, uses inline
assembly, `delegatecall` or value transfers.

Pre-checks run on these sources (the driver re-runs them; they are not proofs):

* solar 0.3.0-dev+commit.697fc686 (compiler sources equal to 902cccc2) `--emit=bin` compiles
  all three without errors.
* solar-verify at the same commit with z3 4.x proves every obligation: Clamp 3/3 functions
  (8 obligations), StepSum 3/3 (31), Registry 3/3 (8).

## Negative inputs

The generic negative suite ([scripts/verify/mutant/generic/negatives.py](../../scripts/verify/mutant/generic/negatives.py))
runs these through the driver; none may come out Certified.

| source | expected | why |
|---|---|---|
| [negative/ClampWrongSpec.sol](negative/ClampWrongSpec.sol) | REJECTED | `ensures result > a` is false at x <= a |
| [negative/SiblingLeak.sol](negative/SiblingLeak.sol) | REJECTED | provable only if the then-branch's `x > 5` leaks into the else-branch |
| [negative/SiblingOk.sol](negative/SiblingOk.sol) | Certified | the control: the same code with the true postcondition |
| [negative/MeterWrongSpec.sol](negative/MeterWrongSpec.sol) | REJECTED | Meter with `+ 1` too many; inside the driver's envelope at bc6da61b |
| [negative/FalseEnvFlat.sol](negative/FalseEnvFlat.sol), [InitBrokenFlat](negative/InitBrokenFlat.sol), [InvBrokenFlat](negative/InvBrokenFlat.sol), [SiblingFnsFlat](negative/SiblingFnsFlat.sol) | REJECTED | the same faults as FalseEnv, InitBroken, InvBroken and SiblingFns, written inside the envelope (no checked arithmetic, reason strings or early returns) |
| [negative/FalseEnvFixed.sol](negative/FalseEnvFixed.sol) | REJECTED | `requires block.chainid == 424242`: satisfiable, but false in the statement's fixed environment, where the false postcondition then holds vacuously |
| [negative/VacuousSecond.sol](negative/VacuousSecond.sol) | REJECTED | the first function (a non-vacuity witness) is correct; the second has a contradictory premise and a false postcondition (solar-verify proves it, vacuously) |
| [negative/SiblingFns.sol](negative/SiblingFns.sol) | REJECTED | lo()'s false postcondition, provable only if hi()'s premise or proof state reaches it |
| [negative/FalseEnv.sol](negative/FalseEnv.sol) | REJECTED | contradictory environment premise: the postcondition holds only vacuously |
| [negative/InitBroken.sol](negative/InitBroken.sol) | REJECTED | the constructor does not establish the invariant |
| [negative/InvBroken.sol](negative/InvBroken.sol) | REJECTED | a second entrypoint (reset) breaks the invariant |
| [blocked/ExternalCall.sol](blocked/ExternalCall.sol) | BLOCKED | external call |
| [blocked/Reentrancy.sol](blocked/Reentrancy.sol) | BLOCKED | value call with the state written after it |
| [blocked/Delegatecall.sol](blocked/Delegatecall.sol) | BLOCKED | delegatecall |
| [blocked/Assembly.sol](blocked/Assembly.sol) | BLOCKED | inline assembly |

solar-verify alone (same commit, z3) refutes ClampWrongSpec and SiblingLeak and proves SiblingOk,
and refuses InitBroken, InvBroken and SiblingFns, but it reports FalseEnv (vacuously),
ExternalCall, Reentrancy and Assembly as verified: the envelope and non-vacuity checks
have to come from the driver, not from solar-verify's verdict.

[MANIFEST](MANIFEST) pins the sources by SHA-256; the driver should refuse a run whose source
hash differs.

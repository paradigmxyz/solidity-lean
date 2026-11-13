# ArrayMax: solar-verify's obligations in the Lean kernel

`Vc/` holds the frozen v1 export of `crates/verify/examples/ArrayMax.sol` (paradigmxyz/solar
7f4e94e, `solar-verify --emit-lean`, z3 4.13.4, cvc5 1.3.1). Each module is the exporter's output
with one change: its first line `import SolarVerify` reads `import Verify.Obligation`, where the
same library now lives (the `VerifyDischarge` library). `Vc/frozen.sha256` is the lock of the unchanged export, which
`Vc/manifest.json` and the modules match before that rewrite.

The loop of `ArrayMax.max` carries no written invariant: solar-verify infers it, and the inferred
clauses reach Lean only as the ordinary loop obligations (on entry, preserved, and the
postconditions they imply), which are proved here like any other.

`Bounded.lean` is the search that closes the obligations the default `vc_valid` cannot
(`max`'s preserved quantified invariants, and Vault's reentrancy-lock obligations); it builds
proof terms only, and every theorem's axioms are checked to be `propext`, `Classical.choice` and
`Quot.sound`.

## Inferred invariant and memory writes

solar-verify's loop-invariant inference was later found to be unsound for loops around internal
calls that write a memory array the caller passed; solar now refuses those loops. ArrayMax is
outside that case: `max` only reads `xs`, calls nothing, and neither `ArrayMaxEntry.max` nor
`clamp` writes an array, so the inferred clauses checked here are unaffected. They are, in any
case, not trusted: each is re-proved here as an ordinary obligation.

## Building

`lake build ContractsArrayMaxVault` builds the exports, the proofs and `Audit.lean`, which fails
unless every theorem uses no axiom but `propext`, `Classical.choice` and `Quot.sound`.

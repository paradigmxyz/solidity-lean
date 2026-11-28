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

## ArrayMaxEntry.max on solar's code

`Entry.lean` (with `Entry/{Basic,Loop,Start}.lean`) proves `ArrayMaxEntry.max`'s ensures clauses (every
element of the calldata array is at most the result, and one equals it) of solar's first lowered
MIR of this file (Certified/arraymax), on every call of `max(uint256[])`, whatever the array's
length: one cut point at the loop's header, where `Inferred.lean` is the invariant solar-verify
inferred for `ArrayMax.max`'s loop (its `forall` and `exists` clauses over `xs` included), carried to the
header by solar's `solar-tv/milestone/arraymax/inferred.sh`; it is generated, never written here, and
every conjunct is checked on every segment. One named hypothesis, `CalldataFits`: the calldata
is shorter than 2^64 bytes, without which the decoder's word arithmetic could wrap.
`Wrong.lean`: the kernel runs the code on `max([1, 7, 3])` to a return of 7, which refutes the mutant
spec "returns the first element".

`Execution.lean`: the bytecode runs as the final EVM IR (`AssembleCut.checkC`, memory at any offset).
Not covered: Certified/arraymax's MIR stages (`Runs.Mir1` fails `sym_seg` on the ABI decoder's
checks, so the spec is not yet carried from the first lowered MIR to the final EVM IR), and the link from the VCs in `Vc/` (about solar-verify's
model of the source) to this code: the spec here is restated on the code.

# Lifecycle

Construction with arguments, for the certification driver's lifecycle tier
(solar's tools/certify/generic.py --tier lifecycle).

- Route.lean: the argument-aware route. initArgs appends the ABI-encoded static
  argument words to the init code. DeployedAtWith and deployedAtWith are the
  constructor's result when called with those arguments (Wide.DeployedAt is the
  no-argument case, by deployedAt_iff_nil). Statement is the lifecycle
  statement: EthLib's run of the creation code returns the runtime bytes and
  storage (Deploys), and SolidCore's constructor leaves the same storage.
- KernelIndex.lean: mkIdx_eq, Std's HashMap bucket index equals mkIdxNat,
  the same index computed on Nat below 2^32 buckets. mkIdx reads the opaque
  platform word size, so without this every HashMap entry outside the first
  bucket is stuck in the kernel. Checks use it with kernel_rfl ... using.
- Examples.lean: kernel regressions for the source half: no parameters, a
  uint256 and an address in two slots, two uint256s, and a parameter that sets
  an immutable. Negative cases cover a wrong or missing argument, a missing
  slot, swapped slots and an immutable claimed as storage.

Check with
```
lake env lean Verify/Lifecycle/Route.lean
lake env lean Verify/Lifecycle/Examples.lean
```
after building Verify.Lifecycle.Examples' imports, including
SolidCore.Refinement.Deploy.

- DeployFrame.lean: deploys_of_postS, the bytecode half from a cut point at
  the creation frame. A PostS specification of the one frame a creation runs
  gives Deploys initcode code s, for any init code, runtime code and storage,
  without reducing EthLib's processMessage.
- Deploy/NoArgCtor.lean: the first instance. NoArgCtor's frame is stepped by
  EthLib's program logic, with SSTORE priced at its bound (sstore_then), and
  gives Deploys initcode code [(0, 7)].

- CreationFrame.lean: the generic creation frame. run is an evaluator of
  the creation frame over the opcodes solar's constructors run (PUSH0 to
  PUSH32, DUP, SWAP, POP, the stack's one- and two-operand opcodes,
  CALLVALUE, CODESIZE, CODECOPY, MLOAD, MSTORE, SSTORE, JUMP, JUMPI, JUMPDEST,
  RETURN), built from EthLib's decoder, prices, memory growth and copies.
  run_good proves it sound against EthLib's program logic once, by
  induction on its steps (SSTORE at its bound, sstore_then). observes turns
  that into EthLib's run of the creation through processMessage_postS. The
  results are deploys_of_check (check fuel init code s = true gives
  Deploys init code s) and not_deploys_of_refutes (refutes ... = true gives
  not Deploys). They depend on propext, Classical.choice and Quot.sound
  only.
- Deploy/Ctors.lean: NoArgCtor, ArgCtor, PairCtor and ImmutableCtor deploy,
  with their arguments appended by initArgs. Each is one kernel evaluation
  of check, with no instruction stepped by hand. ImmutableCtor's installed
  code is solar's runtime code with the immutable patched in (patchWord).
  The kernel negatives are a wrong argument (ArgCtor with 41, ImmutableCtor
  with 999), a missing slot (ArgCtor, PairCtor) and an unpatched immutable
  (ImmutableCtor's code as compiled).

Outside the evaluator: SLOAD, KECCAK256, calls, logs, CREATE and other
opcodes that solar's constructors don't run today. A creation that reverts is
outside it too, so a refutation of a revert (missing arguments) is not
covered. Each theorem is about concrete argument words. Until the generic
theorem is routed to the publisher, the driver's lifecycle tier ends
UNSUPPORTED-lifecycle (exit 4) and never certifies.

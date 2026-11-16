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

Open: the bytecode half (Deploys) has no generic proof yet. Until it does,
the driver's lifecycle tier ends UNSUPPORTED-lifecycle (exit 4) and never
certifies.

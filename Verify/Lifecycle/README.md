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

Open: the frame is still stepped per contract. A generic frame proof for
solar's constructor shape is not done yet: the CALLVALUE guard, the body's
SSTOREs, the argument copy from the end of the code, immutable patching and
the CODECOPY/RETURN epilogue. Until it is, the driver's lifecycle tier ends UNSUPPORTED-lifecycle (exit 4) and never
certifies.

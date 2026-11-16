# Lifecycle

Construction with arguments, for the certification driver's lifecycle tier
(solar's tools/certify/generic.py --tier lifecycle).

- Route.lean: the argument-aware route. initArgs appends the ABI-encoded static
  argument words to the init code. DeployedAtWith and deployedAtWith are the
  constructor's result when called with those arguments (Wide.DeployedAt is the
  no-argument case, by deployedAt_iff_nil). Statement is the lifecycle
  statement: EthLib's run of the creation code returns the runtime bytes and
  storage (Deploys), and SolidCore's constructor leaves the same storage.
- Examples.lean: kernel regressions for the source half. They cover a
  constructor with no parameters and one with a uint256 parameter that sets an
  immutable. Negative cases cover a wrong argument, a missing argument and an
  immutable claimed as storage.

Check with
```
lake env lean Verify/Lifecycle/Route.lean
lake env lean Verify/Lifecycle/Examples.lean
```
after building Verify.Lifecycle.Examples' imports, including
SolidCore.Refinement.Deploy.

Open (see Examples.lean): the bytecode half (Deploys) has no kernel proof yet.
Constructors that leave two or more storage slots get stuck in the kernel at
this base. Until both close, the driver's lifecycle tier ends
UNSUPPORTED-lifecycle (exit 4) and never certifies.

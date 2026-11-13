import SolidCore.Verify.VC.Term
import SolidCore.Verify.VC.Check
import SolidCore.Verify.VC.Model
import SolidCore.Verify.VC.Export.Counter
import SolidCore.Verify.VC.Export.Token
import SolidCore.Verify.VC.Bind

/-!
# solar-verify's verification conditions, checked in Lean

solar-verify (paradigmxyz/solar, `crates/verify`) proves a Solidity function by sending SMT-LIB to a
solver; its README lists the encoding in `src/vc.rs` as part of its trusted base. This library takes
that encoding out of it, one step at a time:

* `Term`: the SMT-LIB fragment solar-verify emits, its meaning, and `Valid`, what a verdict of
  solar-verify claims of a script (every obligation has no model).
* `Check`: `checkScript`, decided by the kernel, and `checkScript_sound`: a script's obligations,
  normalized (definitions inlined, names renamed, conjunctions flattened, range facts derived), give
  the obligations of the Lean side.
* `Model`: the generic source stage's tree of a function as a model in `SolM`, the monad of the
  Loom generator `SolidCore.Verify` (`Basic`), and `implements_tree`, proved once from `source_run`,
  so that Loom's weakest precondition of the model gives a `Triple` against SolidCore's
  `Source.run` through `triple_of_wp`.
* `Export`: solar-verify's transcripts of `scripts/verify/Counter.sol` and `Token.sol`
  (`solar-verify --dry-run --dump-lean`), and `Bind`, which checks that each script prints back to
  its transcript byte for byte.
* `Token` (its own root, since it imports this one): `Token`'s `burn` end to end. The kernel computes
  that `Token` deploys with only `owner` in storage and that the stage erases `burn` to `burnTree`;
  `burn_triple` is its ensures clause as a `Triple` against SolidCore, and `burn_obligation` is
  solar-verify's obligation for it, normalized by `checkScript` and instantiated at the assignment a
  successful call gives. `KernelIdx` makes `Std.HashMap`, the storage of SolidCore's state, reduce in
  the kernel (`mkIdx_eq`), which the constructor run needs.
* `TokenTransfer`: `Token.transfer`'s three ensures clauses on distinct addresses as a `Triple`
  against SolidCore (`transfer_triple`), each read off solar-verify's checked obligation through the
  binding `trStore_eval`: SolidCore's storage after the call, read through `balanceOf`'s layout, is
  solar-verify's array term at the assignment the call binds. Injectivity of the mapping slot on
  address keys (`HashInj`) is a hypothesis of the theorem. `TokenMutants`: for a one-line source
  mutant and a one-line spec mutant of `Token.sol`, exported by the same solar-verify, `checkScript`
  rejects the obligations `transfer`'s clauses need.
* `CounterInc`: the certified counter milestone's `inc` (`scripts/refinement/counter/counter.sol`,
  annotated in `scripts/verify/CounterMilestone.sol`). `inc_triple`: on the stage's scope `inc`
  succeeds exactly when `x + d < 2 ^ 256`, then slot 0 holds `x + d` and every other slot is unchanged.
  solar-verify's obligation for its clause is valid by its own encoding (`x + d = x + d` once its
  definition is inlined), so the theorem takes no verdict: `inc_check` ties solar-verify's script to the
  Lean obligation and `inc_binding` ties solar-verify's encoded effect and guard to what SolidCore runs.
  `CounterMutants`: `checkScript` rejects a one-line source mutant and a one-line spec mutant.

Nothing here uses `native_decide`, `bv_decide` or `ofReduceBool`, or imports
`SolidCore.Verify.Finite`. `Bind`'s check runs Lean's evaluator (`#guard`), not the kernel: it
checks that the generated module is the transcript, as `scripts/verify/check.sh` checks that the
transcript is solar-verify's.
-/

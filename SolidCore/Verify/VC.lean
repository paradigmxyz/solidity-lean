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

Nothing here uses `native_decide`, `bv_decide` or `ofReduceBool`, or imports
`SolidCore.Verify.Finite`. `Bind`'s check runs Lean's evaluator (`#guard`), not the kernel: it
checks that the generated module is the transcript, as `scripts/verify/check.sh` checks that the
transcript is solar-verify's.
-/

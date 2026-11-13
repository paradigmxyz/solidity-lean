# Loom, vendored

**Port in progress (branch loom-4.35).** All of upstream Loom (and its case studies) is now
under vendor/loom. Built on Lean 4.35 so far: Defs, Instances/Basic (with DivM and its partial
and total correctness algebras), Instances/StateT, ExceptT, ReaderT, Gen, WP/Basic (with the
loop, lifting, ExceptT, StateT and ReaderT sections) and WP/Liberal; the lean_lib Loom lists
these as roots. The VC tactic layer, NonDetT and the SMT layer follow. The sections below
describe the earlier, partial vendoring and are rewritten when the port completes.

The parts of [Loom](https://github.com/verse-lab/loom) (verse-lab, Apache-2.0, see
`LICENSE`) that SolidCore's verification-condition generator (`SolidCore/Verify/`) builds on,
from commit `78928abc9054b31d0bea85985496490baae95244` (master, 2026-02-21), which targets Lean
4.24 and Mathlib v4.24. Ported to this repository's Lean 4.35 and Mathlib v4.35.0 and built as
the `Loom` library of the main package (`lean_lib Loom where srcDir := "vendor/loom"` in the
root lakefile), so it adds no package and no manifest entry.

## Kept

* `Loom/MonadUtil.lean`, `Loom/SpecMonad.lean`: unchanged.
* `Loom/MonadAlgebras/Defs.lean`: monad algebras (`MAlg`, `MAlgOrdered`, `MAlgDet`), logic
  lifts and monad-transformer algebras.
* `Loom/MonadAlgebras/Instances/Basic.lean`: the algebra of `Id` on `Prop`, and the
  `CCPOBot` classes.
* `Loom/MonadAlgebras/WP/Basic.lean`: `wp`, `triple` and their generic rules (`wp_pure`,
  `wp_bind`, `wp_map`, `wp_cons`, `triple_*`, `wp_and`, `wp_or`, ...).

## Changed for Lean 4.35

* `MAlgPartial.csup_lift` takes the chain proof explicitly, since `Lean.Order.CCPO.csup` now
  takes a proof of `chain` rather than the set.
* The `LogicLiftT` composition instance's `lift_top` and `lift_bot`, and `MAlgLiftTTrans`'s
  `μ_lift`, are reproved: their `simp` calls no longer make progress.
* `Loom.lean` imports only what is kept.

## Dropped

* `Instances/StateT.lean`, `ExceptT.lean`, `ReaderT.lean`, `Gen.lean`, and the matching
  sections of `WP/Basic.lean` (loops, lifting, `ExceptT`, `StateT`, `ReaderT`, `Gen`): their
  proofs depend on Lean 4.24's `simp` normal forms and on the old `CCPO` API throughout.
  `SolidCore/Verify/Basic.lean` gives its own ordered algebra for the one stack it needs,
  `StateT Storage (Except Revert)`.
* `DivM` and its partial- and total-correctness algebras (`Instances/Basic.lean`).
* `WP/Liberal.lean`, `WP/Gen.lean`, `WP/Attr.lean`, `WP/Tactic.lean`, `WP/Matcher.lean`,
  `WP/DoNames'.lean`, `WP/Options.lean`, `Meta.lean`, `TacticAsync.lean`, `SMT.lean` and
  `NonDetT`: the VC tactic layer, SMT (lean-auto, z3, cvc5) and nondeterminism. SolidCore's
  generator computes weakest preconditions with `simp` and Loom's `wp` rules instead.

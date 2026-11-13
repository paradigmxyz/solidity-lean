# Loom, vendored

**Port in progress (branch loom-4.35).** All of upstream Loom (and its case studies) is under
vendor/loom. Built on Lean 4.35 so far: Defs, Instances/Basic (with DivM and its partial and
total correctness algebras), Instances/StateT, ExceptT, ReaderT, Gen, WP/Basic (with the loop,
lifting, ExceptT, StateT and ReaderT sections) and WP/Liberal; the lean_lib Loom lists the
built modules as roots. The VC tactic layer (DoNames', Options, Gen, Attr, Matcher, Tactic),
NonDetT, Meta, TacticAsync and the SMT layer are not ported yet and nothing builds them.

Statements changed by the Lean 4.35 API:

* `MAlgPartial.csup_lift` and `PartialCorrectness.wp_csup` take the chain proof
  (`Lean.Order.CCPO.csup` now takes a proof of `chain`, not the set).
* `triple_forIn_range` and `triple_forIn_range_step1` are on `Std.Legacy.Range` (Lean renamed
  `Std.Range`).
* The `ForIn m Lean.Loop Unit` instance's `forIn` no longer takes the loop value separately
  (`ForIn.forIn`'s signature changed).

Added (not upstream; candidates for an upstream PR):

* `DivM.csup_eq`, `StateT.csup_apply`, `StateT.bot_apply`, `ReaderT.csup_apply`,
  `ReaderT.bot_apply`: the supremum of a chain, now a choice, as the flat or pointwise one.
* `Instances/ExceptTErr.lean`: an error-aware algebra, `MAlgExceptErr` on `ExceptT ε m` with
  assertions `(ε → l) → l`, and `MAlgExceptErrProp` on `Except ε` with `(ε → Prop) → Prop`
  (and `MAlgDet`), whose weakest precondition takes the predicate an exception must meet.
* `WP/Variant.lean`: `Loop.bounded`, `Loop.whileBounded`, and the total-correctness rules
  `triple_bounded` and `triple_while` (invariant plus a natural-number variant) for monads
  that cannot diverge, with `bounded_eq_of_variant`.

The sections below describe the earlier, partial vendoring.

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

# Loom, ported to Lean 4.35

Loom's monad algebras and weakest preconditions, from upstream Loom, ported to Lean 4.35. This
directory keeps exactly the modules that build here; every one is in `Loom.lean`'s import closure
and `lake build Loom` builds them all. Nothing in it uses `sorry`, `native_decide`,
`bv_decide` or an axiom (`Verify/LoomAxioms.lean` audits the pieces the verification uses).

## Kept

* `MonadUtil.lean`, `SpecMonad.lean`: unchanged.
* `MonadAlgebras/Defs.lean`: monad algebras (`MAlg`, `MAlgOrdered`, `MAlgDet`), logic lifts
  and monad-transformer algebras.
* `MonadAlgebras/Instances/Basic.lean` (with `DivM` and its partial and total correctness
  algebras), `StateT.lean`, `ExceptT.lean`, `ReaderT.lean`, `Gen.lean`.
* `MonadAlgebras/WP/Basic.lean` (with the loop, lifting, `ExceptT`, `StateT` and `ReaderT`
  sections) and `WP/Liberal.lean`.

## Changed for Lean 4.35

* `MAlgPartial.csup_lift` and `PartialCorrectness.wp_csup` take the chain proof
  (`Lean.Order.CCPO.csup` now takes a proof of `chain`, not the set).
* `triple_forIn_range` and `triple_forIn_range_step1` are on `Std.Legacy.Range` (Lean renamed
  `Std.Range`).
* The `ForIn m Lean.Loop Unit` instance's `forIn` no longer takes the loop value separately.

## Added (not upstream)

* `DivM.csup_eq`, `StateT.csup_apply`, `StateT.bot_apply`, `ReaderT.csup_apply`,
  `ReaderT.bot_apply`: the supremum of a chain, now a choice, as the flat or pointwise one.
* `Instances/ExceptTErr.lean`: an error-aware algebra, `MAlgExceptErr` on `ExceptT ε m` with
  assertions `(ε → l) → l`, and `MAlgExceptErrProp` on `Except ε`, whose weakest precondition
  takes the predicate an exception must meet.
* `WP/Variant.lean`: `Loop.bounded`, `Loop.whileBounded`, and the total-correctness rules
  `triple_bounded` and `triple_while` (invariant plus a natural-number variant) for monads that
  cannot diverge, with `bounded_eq_of_variant`.

## Not ported

Upstream's VC tactic layer (`WP/Gen`, `Attr`, `Tactic`, `Matcher`, `DoNames'`, `Options`),
`NonDetT`, `Meta`, `TacticAsync`, the SMT layer (lean-auto, z3, cvc5) and the case studies are
not here. The verification computes weakest preconditions with `simp` and the `wp` rules above
(`Verify/Basic.lean`), and `Verify/LoomImports.lean` fails if any of those layers reaches its
import closure.

# Verify/Discharge

Kernel discharge of exported obligations. How to run it, the backends and the acceptance checks
are in [README.md](README.md) and the header of `discharge.sh`; don't restate them elsewhere.

- Discharge only: no semantics or VC generation changes here (those are `Verify/Obligation`,
  `Verify/VC`). A backend is untrusted; only a kernel-checked term with clean axioms counts.
- Proof sessions over many related goals (paths, cases) keep one persistent `Lean.Meta.Grind.Goal`
  per branch ([Types.lean](https://github.com/leanprover/lean4/blob/v4.35.0/src/Lean/Meta/Tactic/Grind/Types.lean)): a child extends its
  parent's state by explicitly internalizing the new facts; a branch never sees facts from a
  sibling.
- Bounded ground computation (closed hypotheses, finite checks): `cbv`
  ([Init/Tactics.lean](https://github.com/leanprover/lean4/blob/v4.35.0/src/Init/Tactics.lean)) or kernel evaluation (`vc_ground`), never
  `native_decide` or `bv_decide`.
- `grind` goes before `vc_smt` in `DISCHARGE_BACKENDS` only where `results.tsv` on the
  frozen locks shows it proves more or faster; keep the measurement with the change.
- No blanket `simp`/`unfold`: name the lemmas and definitions a backend uses.
- Don't claim obligations are linear in general; nonlinear goals exist (`Nonlinear.lean`).
- `frozen/` and `results/` are recorded evidence: regenerate with the runner, never hand-edit.

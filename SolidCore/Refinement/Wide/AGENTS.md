# SolidCore/Refinement/Wide

Source-side symbolic evaluation (`src_eval`, `src_symex` in `Tactic.lean`; its header says
how they work).

- Unfold only what the goal reaches, as `src_eval` does; no blanket `simp`/`unfold` of the
  interpreter. Well-founded definitions stay folded.
- Proof sessions over many related goals (paths, cases) keep one persistent `Lean.Meta.Grind.Goal`
  per branch ([Types.lean](https://github.com/leanprover/lean4/blob/v4.35.0/src/Lean/Meta/Tactic/Grind/Types.lean)): a child extends its
  parent's state by explicitly internalizing the new facts; a branch never sees facts from a
  sibling. `src_symex`'s branch conditions stay on their branch.
- Symbolic normalization shares one simplifier with `../Evm` (`Lean.Meta.Sym`,
  [Sym/Simp.lean](https://github.com/leanprover/lean4/blob/v4.35.0/src/Lean/Meta/Sym/Simp.lean)); bounded concrete evaluation uses `cbv`.
- Prefer `grind` over external solvers only where measured (see the root `AGENTS.md`).
- Don't assume path conditions are linear; `omega` closing a branch is a fast path, not a
  completeness claim.

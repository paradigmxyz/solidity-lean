# SolidCore/Refinement/Evm

Bytecode-side symbolic execution on EthLib (`Symex.lean`, `Wide.lean`, storage variants). Each
file's header documents its tactic and lemmas.

- Step bytecode with the existing step rules (`evm_step`, the call-data rules in
  `Calldata.lean`); bounded concrete stepping uses `cbv`, not `decide` on large terms and never
  `native_decide`.
- Proof sessions over many related goals (paths, cases) keep one persistent `Lean.Meta.Grind.Goal`
  per branch ([Types.lean](https://github.com/leanprover/lean4/blob/v4.35.0/src/Lean/Meta/Tactic/Grind/Types.lean)): a child extends its
  parent's state by explicitly internalizing the new facts; a branch never sees facts from a
  sibling. Path conditions from one side of a JUMPI never reach the other.
- No blanket `simp`/unfolding of EthLib: name the definitions and lemmas each step needs.
- Normalize symbolic words through one shared simplifier (`Lean.Meta.Sym`,
  [Sym/Simp.lean](https://github.com/leanprover/lean4/blob/v4.35.0/src/Lean/Meta/Sym/Simp.lean)) shared with `../Wide`, not a second set.
- Statements and frame specs come from `../Statement.lean`; don't restate or weaken them here.

# solar's analysis facts in Lean

`scripts/refinement/facts.sh` checks, in Lean, the dataflow facts solar's optimizer relied on
when it compiled each contract of `scripts/refinement/corpus`. It builds solar and
`tools/prove-analyses` at the commit in `scripts/refinement/prove-rev`, compiles every corpus
contract at `-O gas` with `-Zprove-analyses`, has Z3 prove each recorded fact, and has
`crates/smt/src/certify/lean.rs` translate each proved query into a Lean theorem that
`bv_decide` proves. It writes one module per contract to `SolidCore/Refinement/Facts/`, with
`SolidCore/Refinement/Facts.lean` importing them; `lake build SolidCore.Refinement.Facts`
checks every theorem. `facts.sh --check` regenerates the modules and fails when they differ from
the checked-in ones. `PROVE_TARGET` names a directory holding prebuilt `solar` and
`solar-prove-analyses` binaries of the pinned commit, and `Z3` a Z3 binary.

## What a theorem says

A fact is a claim `lhs pred rhs` (`pred` one of `eq`, `ne`, `ult`, `ule`) about two MIR values
at the end of one MIR block, recorded by the pass whose rewrite relied on it:

- `sccp`: a constant SCCP substituted for a value;
- `check_elim`: a branch, check, overflow test or equality that check elimination decided;
- `cse`: a memory, storage or transient read CSE forwarded from an earlier value;
- `load_pre`: a read load PRE forwarded;
- `indvar_simplify`: the entry bound induction variable simplification relied on.

The corpus has `check_elim` and `cse` facts only. Each theorem's comment names the contract,
the function, the block, the claim and the query it came from. Its hypotheses are the query's
assertions: the definitions of the values in the blocks that dominate the fact's block, with
EVM word semantics, the branch conditions into them, the facts checked before it (Regehr's
induction: in the first execution that violates a fact, every earlier fact held), and the
fact's negation; its conclusion is `False`. Memory, storage, calls and hashes are
unconstrained functions, and a theorem whose comment names `heap-floor` also assumes the
backend's placement of deferred allocations. A theorem certified in the abstract tier proves a
weaker query, with non-constant multiplication, division and remainder replaced by functions
obeying their laws, which implies the exact one. A fact Z3 or Lean did not prove has a comment
with the reason in place of a theorem.

The theorems trust `bv_decide`'s LRAT checker as Lean's compiler evaluates it: each theorem
that reaches `bv_decide` depends on its own `<theorem>._native.bv_decide.ax_*` axiom besides
`propext`, `Classical.choice` and `Quot.sound`. They also trust that the translator renders
the query faithfully and that the query encodes the MIR faithfully.

## What they do not yet connect to

The facts are about solar's MIR at `lower-assumes`, in a compile that records them, not about
the runtime bytecode the refinement theorems in `SolidCore/Refinement` are about. Recording
keeps the values a fact is about alive, so a recording compile can optimize slightly
differently from a plain one, and `prove-rev` may name a different commit from `solar-rev`.
Composing the facts with a bytecode refinement needs, at least, a semantics of solar's MIR in
Lean, a proof that each query's assertions hold of every MIR execution reaching the fact's
block (so the theorem gives the fact there), a proof that the optimized MIR, rewritten under
those facts, refines the MIR before the rewrite, and a proof or validation that the backend
compiles that MIR to the bytecode `gen.sh` checks in, from the same commit and without
recording.

## Commits

`prove-rev` and `solar-rev` name the same solar commit, so the facts and the bytecode
proofs describe one compile of each contract. Keep them equal when moving either.

# Counterexamples to induction (CTIs) for loop invariants

cti/ turns a loop's Horn clauses and a candidate invariant into counterexamples to induction,
labels each one as an ICE sample (Garg, Löding, Madhusudan, Neider, *ICE: A Robust Framework for
Learning Invariants*, CAV 2014, https://madhu.cs.illinois.edu/CAV14ice.pdf), replays it from the
loop's entry for a bounded number of iterations, and writes the result as a corpus that a test
re-checks record by record. It learns nothing: candidates are dropped by the existing Houdini
(solar crates/verify/src/vc/infer.rs); this is the evidence for why.

## Inputs

- cti/problems.json: one entry per loop. chc is a Horn problem over one predicate Inv with
  exactly one entry clause, one back-edge clause and one or more query clauses; anything else
  (two Inv in one body, Inv under a connective) is reported unsupported and never classified.
  Each candidate is a list of conjuncts in SMT-LIB over the loop's variables, an optional
  decreases term, and the status, rank result and flag it is expected to get.
- Handwritten problems: the three loops of Verify/Infer (counter, okwhile, drain, as _u256 and
  _int), read from Verify/Infer/chc unchanged, with Spacer's answers as candidates
  (spacer:FILE). Their clauses were written by hand (Verify/Infer/README.md).
- Generated problems: cti/chc/bump_*.smt2 are the Horn problems solar-verify itself builds for
  Counter.bump's loop (crates/verify/src/vc/horn.rs, problem()), cut unedited from its
  SOLAR_VERIFY_DEBUG output by cti/export-solar.sh at the solar commit in cti/solar-rev.
  solar-verify builds one only for a function that still fails after Houdini, so these are the
  problems of the mutants solar-verify mutate draws for Counter.bump plus one spec mutant
  (chc/SOLAR_EXPORT lists all nine and what each gave). Their clause variables are solar's SSA
  constants, so a name means one value across clauses (shared), and the constants the entry
  clause binds are fixed for the whole run. frame names the ones a candidate may read:
  old_count is the entry clause's head term for count, limit the entry constant limit@N.

## Edges and labels

For a candidate I (the conjunction) and, if given, a measure r:

| edge | obligation | CTI | label |
| --- | --- | --- | --- |
| entry | initiation | entry(s') and not I(s') | positive: s' is reached (an entry state) |
| back | preservation | I(s), back(s, s'), not I(s') | implication (s, s'); positive if replay reaches s |
| back | decrease | I(s), back(s, s'), not (0 <= r(s) and r(s') < r(s)) | rank-pair |
| query_edge | use | I(s), query(s), not goal(s) | negative: the goal fails from s |

query_edge is exit for the handwritten problems. In solar's problems the query clause is the
failed obligation's guard and goal, which can sit on the entry (crp26: an annotated invariant
false on entry) or on the back path (ror26, sdl27, aor27: an annotated invariant false after the
body), and problems.json says which.

The ICE discipline the checker enforces:

- Only a use (goal) CTI is negative. The pre-state of a back-edge CTI is never labelled
  negative: it is half of an implication pair, which says only that s' must be in the
  invariant if s is.
- A positive needs a replayed trace: entry states are reached at depth 0, and an implication
  pair becomes a positive only when replay reaches its s (then s' is reached one step later).
- A CTI is not a bug. A negative that replay reaches is a reachable violation of the goal (the
  source or the spec is wrong: status goal-violated). A negative it does not reach says the
  candidate is too weak to prove the goal, nothing about the program.
- not-reached-within-k is recorded as that, never as unreachable.
- A z3 unknown or timeout gives inconclusive, never inductive.

## Bounded replay

replay unrolls the entry clause once and the back clause up to k times (default 6) with fresh
copies of each clause's other variables (the frame kept), and asks for the least depth at which
a target holds. It is used three ways: on each edge, first for a CTI whose pre-state is reached
(so reachable counterexamples are found before arbitrary ones); for each arbitrary CTI z3
returns, to try to reach its pre-state exactly; and for each conjunct, for a reached state that
falsifies it. Up to per_edge (2) CTIs per edge are kept, small values first.

## Candidate status

| status | meaning |
| --- | --- |
| rejected | a reached state falsifies the candidate (a positive) |
| goal-violated | no positive, but a reached state violates the goal |
| not-inductive | only implication pairs whose pre-states replay did not reach |
| too-weak | only negatives replay did not reach |
| inductive | z3 found no CTI on any edge (not a proof: the kernel discharge is Verify/Discharge's) |
| inconclusive | some query answered unknown |

rank is none (no measure), decreases (no rank pair), rejected (a reached rank pair),
nonterminating (a reached rank pair with s = s') or not-proved (rank pairs only from unreached
states).

flags: vacuous-back-edge when no head state under the candidate takes the back edge. For each
conjunct A => B: guarded, with whether A is satisfiable at a head state under the candidate,
whether a reached state satisfies A, and the status with B in its place;
passes-only-because-antecedent-false when the candidate has no initiation or preservation CTI,
the unguarded version has one, and A is unsatisfiable under the candidate or never reached.

## Record format

Each corpus/<problem>.jsonl holds, one JSON object per line (keys sorted):

- kind problem: schema (solidity-lean/cti/v1), chc and its chc_sha256, origin (handwritten or
  solar-verify), vars, frame, shared, query_edge, k, z3 version, source (the loop: file, line,
  col, text), mutation (what was mutated, for solar's problems), outcome (normal: these clauses
  keep only paths that do not revert; revert and out-of-gas paths are not in them).
- kind candidate: id (problem/candidate), conjuncts, decreases, source (the annotation or file it
  came from), expectations, status, rank, flags, number of CTIs.
- kind cti: id, candidate, edge (entry, back, call, exit), obligation (initiation, preservation,
  decrease, use), s and s' (variable to decimal string, the frame included), label, replay
  (result reached with depth and trace, or not-reached-within-k or inconclusive with k),
  falsified (the conjuncts false at s'), measure (r(s), r(s')), lasso, exit (which query clause),
  by replay when replay found it first, and source (loop and candidate).

corpus/SUMMARY.tsv has one row per candidate.

## The corpus

14 problems, 65 candidates, 150 CTIs: 42 reached positives, 34 reached negatives, 46 negatives
and 16 implication pairs not reached within k, 12 rank pairs (6 reached). Examples:

- infer-counter-*/annotated: the two annotated invariants of bump are too weak in the
  handwritten CHC, where old(count) and limit are head variables and the entry fact
  count + n <= limit is lost at the head: the negative c0 + n > lim is never reached. With that
  fact as a conjunct (annotated-frame) the candidate is inductive.
- infer-counter-*/mut-weak-count: count bounded instead of equal gives implication pairs whose
  pre-states are never reached; the candidate is not-inductive, and no state is called negative.
- */mut-i-zero: i == 0 holds on entry; replay reaches the pre-state of its back-edge CTI, so the
  pair becomes a positive and the candidate is rejected.
- */guarded-dead: (i > n) => (count == 0) passes only because no state under the candidate has
  i > n; the unguarded count == 0 is rejected.
- solar-bump-spec-post: solar's own clauses of bump's loop with the postcondition claiming one
  more. The annotated invariants and the eight candidates Houdini keeps on the unmutated source
  (houdini-kept) have no initiation or preservation CTI; their only CTIs are reached negatives,
  so the spec, not the candidate, is wrong. wrong-rank (decreases i - n) has reached rank pairs.
- solar-bump-sdl22, aor22 (the require removed or weakened): the contract invariant
  count <= limit fails at a reached exit.

What solar's export shows:

- Its back clause assumes the hand-written invariants and the Houdini candidates kept at the head
  (they are in the guard), so its back relation is conditioned on them. A candidate that
  contradicts them makes the back edge vacuous (solar-bump-spec-post/mut-off-by-one).
- For crp26 (i starts at 1) the exported back clause is unsatisfiable on its own: the head guard
  assumes count == old(count) + i, count == old(count) and i == 1 together (vacuous-back-edge on
  every candidate).
- ror22 (require(count + n < limit)) and aor26 (i-- for i++) are proved by solar-verify, so no
  problem is exported. aor26's back edge always reverts (i-- underflows at 0 after count++), so
  its decreases obligation holds only vacuously on normal paths.
- The unmutated bump is proved, so its problem is never built: the correct goal over solar's
  clauses is not in the corpus. The handwritten infer-counter problems stand in for it.

## Running

    python3 -m venv .venv-cti && .venv-cti/bin/pip install --require-hashes -r Verify/Infer/cti/requirements.txt
    PYTHON=.venv-cti/bin/python Verify/Infer/cti/test.sh

test.sh (run by the refinement workflow's cti job) regenerates the corpus and requires it to match
byte for byte (z3 5.4.1), re-checks every record from problems.json and the chc files alone (each
claimed CTI is a real edge instance with the candidate true and false where stated, each trace is
an entry state followed by back-edge steps, each status follows from its records and matches
its expectation), and requires eight corrupted corpora to be refused (a back-edge pre-state
labelled negative, an unreached pair promoted to positive, a forged trace, a not-inductive
candidate claimed inductive, a non-CTI, a hidden unknown, a dropped guard flag, a reached goal
violation reported as too-weak) and a nonlinear problem to be unsupported.

cti.py gen problems.json corpus rewrites the corpus; cti.py check problems.json corpus checks it.
export-solar.sh rewrites chc/bump_*.smt2 from a solar checkout at solar-rev
(SOLAR=<checkout> Z3=<z3 5.4.1> Verify/Infer/cti/export-solar.sh).

## Not covered

- The check re-verifies every CTI the corpus claims, but the absence of CTIs (inductive) rests on
  z3 and on regeneration matching; it is not a proof. Lean obligations and their discharge are
  Verify/Discharge's and Verify/VC's.
- Only the shapes above: one predicate, linear clauses, Int and Bool head variables, no call
  edges (no loop here calls a function; a problem with call clauses is refused).
- Solar's problems exist only for failing functions, so the unmutated bump's correct goal is
  covered only through the handwritten CHC.
- Replay is bounded (k = 6); with uint256 ranges most arbitrary CTIs have pre-states far beyond
  any bounded run, which is why they stay implication pairs or unreached negatives.
- Reverting and out-of-gas outcomes are not modelled: solar's clauses and the _u256 CHCs drop
  reverting paths.

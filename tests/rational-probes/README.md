# Rational-constant audit probes (gap A1)

Audit artifacts for `docs/rational-constants-audit.md`. Not yet wired into
`manifest.json` (see the audit doc §(c) for how they become corpus lanes).

- `accepts.sol` — constants solc 0.8.35 folds and accepts; the folded value is
  visible in the AST `typeIdentifier` (`t_rational_<num>_by_<den>`).
- `rejects/*.sol` — one bad constant each; solc must reject with a compile error.
- `extract_solc.py` — compiles the probes with pinned solc and prints, per
  ACCEPT constant, the folded num/den; per REJECT file, the error headline.
  Run: `python3 tests/rational-probes/extract_solc.py`
- `our_side_eval.lean` — `#eval`s our folder/fit functions on the same probes.
  Run: `lake env lean tests/rational-probes/our_side_eval.lean`

Finding: 0 WRONG-VALUE, 3 OVER-REJECT (negative constants via subtraction —
`NumberRat` is over `Nat`). Details in the audit doc.

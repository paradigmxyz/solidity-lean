# Verify/Infer

Invariant discovery evidence. Scope, the trusted inputs and how to check each file are in
[README.md](README.md).

- Discovery only: solvers (Spacer, Flex) propose invariants; a proof checks them. A solver's
  answer is never evidence, and Flex's `flex_auto` (a trusted SMT axiom) is not used.
- Nothing here is built by `lake build`; check files with `lean` on the pinned toolchain and
  gate every theorem with `#print axioms`.
- Generated files (`Reconstruct.lean`, `*.out`, `*.axioms.txt`) come from
  `gen_reconstruct.sh`; regenerate and update `SHA256SUMS` rather than editing them.
- Hand-written Horn clauses are not the emitted VCs: don't present results here as certificates
  for a contract.

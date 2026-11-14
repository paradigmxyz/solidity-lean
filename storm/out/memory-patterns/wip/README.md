# memory-patterns: pre-reset work (wip)

Bundle `memory-patterns-pre-reset.bundle`: branch `wip/memory-patterns-pre-reset` on top of
storm/base d54dabf (`git fetch memory-patterns-pre-reset.bundle wip/memory-patterns-pre-reset`).
Unreviewed work in progress, kept so that the restarted lane can build on it.

- 4606ed7 feat(generic): the symbolic MIR run (`Generic.symTree`) takes a function's entry heap
  (stores the constant free-memory pointer at 0x40 on entering, `symStart`), `heap_floor`
  (its constant word) and `mload` at a constant offset whose memory holds one word.
  `symTree_sound` re-proved; `lake build SolidCore.Refinement.Generic.MirRun` and
  `SolidCore.Refinement.Generic.Stage` exit 0 (-KleanMemory=2500/3500).
- c68bcce, 77fe163 feat(certified): event_words (a Swap-shaped event: four data words ABI-encoded
  at the free memory pointer, three topics). `SolidCore.Refinement.Solar.EventWords.Lowering`
  builds (exit 0, -KleanMemory=4000): `check_stage0`, `checkValue_stage0`, `lowering`,
  `loweringValue` and five rejected mutants (caller, topic, topic order, data order, entry
  heap), axioms within propext, Classical.choice, Quot.sound. The driver run reached the
  published statement build (stages, backend proofs and 47 audited theorems passed); the final
  statement was not built before the reset.
- 1581b6b wip(generic): `eraseExpr` takes `uint256(keccak256(abi.encode(x, y)))` of two atoms
  as `WExpr.hash` (`eval_hash_pair`, `hashPair?`); Source.lean elaborates with no errors as a
  standalone file; not yet run through a contract. Front-end sources for the other patterns
  (abi encode, keccak of packed memory, calldata array loop, dynamic event, return-data decode,
  low-level call, try/catch). Inline-assembly revert bubbling is refused by the front end
  (Yul nodes are out of its scope).

# Certified: generated per-contract stages and proofs

Each directory is one contract that solar's certify driver exported and proved, laid out as the
driver writes it: `<name>/<name>.sol` (the source), `options` (the compiler options),
`bytecode.hex`, `gen/<Contract>/*.lean` (the exported stages, modules `<name>.gen.<Contract>.*`)
and `Proofs.lean`, `Proofs/**` (the backend proofs, modules `<name>.Proofs.*`). `w1/` also holds
the `W1` checks of w1's stages. The `srcDir` of each library is `Certified`, so module names carry
no `Certified` prefix, as the solidity-lean refinement proofs import them.

Only the contracts a headline theorem or milestone check here imports are committed: w1, w4,
counter, masks, c4, mulx, bank, events, reader, verify_token, verify_counter and callsqrt
(Uniswap v2-core's Math.sqrt loop entered through internal calls from two functions; its record
is MIR to EVM IR proved and the bytecode decoded, not end to end). Regenerate one with solar's certify
driver against this commit (solar's pin file names it); it rewrites the directory in place.

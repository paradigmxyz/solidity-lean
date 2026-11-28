# EvmRules (vendored)

solar's word semantics and rewrite-rule lemmas (`EvmRules`, `EvmRules.*`), which the SolarTV
library's MIR and EVM IR semantics are written in. Copied verbatim from
paradigmxyz/solar `scripts/evm-rules/lean/EvmRules.lean` and `scripts/evm-rules/lean/EvmRules/`
at main de3967800 (only the library: solar's rule checker, `Checker.lean`, and its generated rule
proofs stay in solar, which keeps its own copy for checking its ISLE rules).

To update, copy those paths from the solar commit and update the commit above;
`scripts/check-evm-rules-vendor.sh <solar checkout>` reports any difference.

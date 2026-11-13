# Vault: solar-verify's obligations in the Lean kernel

`Vc/` holds the frozen v1 export of `crates/verify/examples/Vault.sol` (paradigmxyz/solar
7f4e94e, `solar-verify --emit-lean`), with its first line `import SolarVerify` read as
`import Verify.Obligation`; `Vc/frozen.sha256` locks the unchanged export. `Proofs/Vault/` proves
every required obligation with `vc_valid` or the bounded search of `../ArrayMax/Bounded.lean`, and
`Audit.lean` fails unless every theorem uses only `propext`, `Classical.choice` and `Quot.sound`.

## Vacuous obligations

Five obligations hold only because their hypotheses refute: `Proofs/Vacuous.lean` proves, for
each, the obligation with its goal replaced by `false`. Their proofs say nothing about their
goals, so they are not evidence for the property they name:

| Obligation | Kind |
| --- | --- |
| Vault.deposit#6 | side |
| Vault.deposit#7 | entry point does not revert while the reentrancy guard is held |
| Vault.withdraw#6 | assertion `totalShares == sumShares && totalShares <= totalAssets` |
| Vault.withdraw#7 | side |
| Vault.withdraw#8 | entry point does not revert while the reentrancy guard is held |

They are the queries of each entry point's second script (`script1`), which models a call
that enters while `locked` is held: its first guard is `locked` and the next conjoins
`!locked` (the entry point's `require(!locked)`), so every path of the script is infeasible. For
the reentrancy checks (#7, #8) that refutation is the intended answer: a reentrant call cannot get
past the guard. withdraw#6 is the invariant assertion on that infeasible path; the same
assertion on the feasible path is withdraw#0, which is not vacuous.

# Vendored dependencies

Ports of two dependencies to Lean 4.35 and Mathlib v4.35.0, which EthLib needs.
Only the modules SolidCore imports are kept.

| Directory | Upstream | Commit |
|---|---|---|
| `evmyul/` | https://github.com/danrobinson/EVMYulLean | `b08573c65e33feb5331abe2b7c1d76be89bb8eff` |
| `evm-interaction/` | https://github.com/danrobinson/evm-interaction | `c939817c55f966dab97e1ba8df05ceca1fdfbdb2` |

The port changes only what Lean 4.35 rejects:

* Batteries moved `RBMap`, `RBSet` and `RBNode` from `Batteries` to `RBTree`.
* `EvmYul.toExecute` matches on the operation type and the account map together,
  so the match refines the map's type.
* Two proofs in `EvmInteraction.Simulation.OpenWorld` (`extCodeHash_evm`,
  `sstore_eq`) close goals that Lean 4.35's `simp` and matchers leave open.
* `evmyul`'s lakefile pins the SHA-2 and Keccak C sources it clones, and no longer
  initializes the EthereumTests submodule.

Once the upstream repositories move to Lean 4.35, require them from git again.

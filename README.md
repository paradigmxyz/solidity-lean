# solidity-lean — a machine-checked Solidity semantics (SolidCore)

**SolidCore** is an executable, machine-checked semantics of Solidity written in
[Lean 4](https://lean-lang.org/). It typechecks, lowers, and *runs* real
single-contract Solidity programs inside Lean, and its behavior is continuously
validated against the reference toolchain: **pinned `solc` 0.8.35 + the real
EVM** (via [Foundry](https://github.com/foundry-rs/foundry)).

The claim this repo makes is narrow and falsifiable: **for programs in scope,
the on-chain observable computed by the Lean semantics — return data,
revert/panic data, emitted events, final storage — is byte-identical to what
solc-compiled bytecode produces on the EVM.** When that claim fails, it's a
bug here, and we fix it at the root.

## Spec Hunt — find a divergence, get credited

This repo is the subject of **[Spec Hunt](https://www.paradigm.xyz/puzzles/spec-hunt)**:
submit a Solidity program where this semantics disagrees with real
solc + EVM. Every accepted divergence is a concrete, credited bug in the
formal model — and its fix lands here, in public, with a regression witness.

- **How to submit:** [contest/SUBMITTING.md](contest/SUBMITTING.md)
  (submission layout, `claim.json` schema, local adjudication via
  `python -m contest.adjudicate`)
- **What's in scope:** [contest/README.md](contest/README.md) and the
  [exclusion register](contest/exclusion_register.py) (versioned; currently
  single-contract v1 scope — no external calls, no inline assembly, no gas
  introspection; precompile `staticcall`s to literal addresses are in scope)
- **Known/fixed divergences:** [DIVERGENCE-LOG.md](DIVERGENCE-LOG.md) and the
  fingerprint registry (`contest/known_gaps.py`) — submissions matching an
  already-known gap don't score

## Validation, continuously

- **99 witness modules** (`SolidCore/Witness/`) pin end-to-end behavior of
  fixed programs — every bug fix ships with one.
- **290-case replay corpus** (`tests/forge-harness/`): each case compiles with
  pinned solc, executes on a real EVM via `forge`, and must match the Lean
  observable byte-for-byte
  (`scripts/run_forge_interpreter_harness.py`).
- **Proof obligations** (`FuelMonotonicity`, `AdoptionLaws`) are checked on
  every build — Lean will not compile a module whose proofs don't close.
- **Contest sample suite** (`python3 -m contest.run_samples`): ~85 end-to-end
  adjudication checks, including fault-injection selftests of the detectors
  themselves.

## Building

Prerequisites: [elan](https://github.com/leanprover/elan) (Lean toolchain is
pinned by `lean-toolchain`), pinned **solc 0.8.35**
(`solc-select install 0.8.35`), and **Foundry** (`foundryup`) for the EVM side.

```sh
lake build                      # full build: semantics + proofs + all witnesses
scripts/fast_inner_gate.sh      # fast inner loop: semantic spine + laws only
scripts/compare_forge_solc_interpreter.sh   # replay corpus vs real EVM
python3 -m contest.run_samples  # contest harness end-to-end suite
```

## Repository map

| Path | What |
|---|---|
| `SolidCore/Solidity/` | The semantics: importer, `TypeCheck`, `Interface` (lowering), `Interpreter`, ABI, proofs |
| `SolidCore/Witness/` | Pinned end-to-end behavior witnesses (one per fixed bug family) |
| `contest/` | The Spec Hunt adjudication harness: reject gate, exclusion register, observable comparator, dedup fingerprints, sample suite |
| `tests/forge-harness/` | The solc+EVM replay corpus |
| `scripts/` | Build/replay/measurement tooling |
| `docs/`, `*_DESIGN.md` | Design notes and decision records |

## Scope

v1 is deliberately **single-contract**: one contract, one entrypoint call, a
pinned environment (Foundry defaults). External calls, contract creation,
inline assembly, and gas introspection are out of scope and rejected by the
gate — see the exclusion register for the precise, versioned list. The
multi-contract responder (v2) has a documented seam but is not part of the
contest today.

## License

Licensed under either of [Apache License, Version 2.0](LICENSE-APACHE) or
[MIT License](LICENSE-MIT) at your option.

Unless you explicitly state otherwise, any contribution intentionally
submitted for inclusion in this work by you, as defined in the Apache-2.0
license, shall be dual licensed as above, without any additional terms or
conditions.

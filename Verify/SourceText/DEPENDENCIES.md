# G0's inputs, and what a LedgerRelay certificate still needs

Everything a clean checkout of this branch needs to rebuild and recheck G0. Nothing else: no
local `.olean`, no working-tree file outside the commit, no earlier build.

## Clean checkout

    git clone --branch alpharush/acc5-source-e2e https://github.com/paradigmxyz/solidity-lean
    cd solidity-lean
    lake exe cache get                      # Mathlib's published build cache (optional; lake can rebuild it)
    Verify/SourceText/check.sh SOLC SOLAR_VERIFY --flag

`check.sh --flag` runs `flag_record.sh`, which fetches the record commit below and assembles
Flag's modules from it; every other input is in the commit.

## Pinned inputs

| input | pin |
|---|---|
| Lean | `leanprover/lean4:v4.35.0` (lean-toolchain) |
| lake packages | lake-manifest.json, unchanged from the base 49d1d7f5 (table below) |
| G0's sources, tests, frozen cases | this commit; cases pinned by CASES.sha256 (70 files) |
| Flag's record modules | solidity-lean commit abcd096127559797224a4fdf330dd3476c65b79c (branch alpharush/t1-generic-records), path `Certified/record/rc2-acc5-flag/generated/Certified/flag_4ce5cf9a`, 33 files pinned by FLAG_RECORD.sha256, which must also equal the record's own MANIFEST.sha256 at that commit |
| Flag's lean_lib `flag_4ce5cf9a` | lakefile.lean, as in the record's `replay/inputs/lakefile.lean` |
| solc | 0.8.35+commit.47b9dedd, sha256 fa8ac9a32d301ad023a36ee5a29f8e291fe3200c60244e43c142539e82a617f4 (check.sh checks it) |
| solar-verify | built from solar 902cccc2 `crates/verify` (identical to 0479b90a's), sha256 4468c71522c1e26e15e20808b87f5d4e0e81070602fce1ed2eea02c262cbd464 (check.sh checks it) |
| importer | `scripts/solc_ast_to_lean_source.py` at this commit, sha256 5b35afb6…2e3b |

solc, solar-verify and the importer only regenerate the frozen upstream readings
(`gen_cases.py`); the Lean build and its theorems never run them.

### Lake packages (lake-manifest.json)

| package | source | rev |
|---|---|---|
| mathlib | https://github.com/leanprover-community/mathlib4 | 56a005855ea17e0b0958f73ec801ae140b0a1679 |
| evm-interaction | vendor/evm-interaction | in tree |
| evmyul | vendor/evmyul | in tree |
| EthLib | https://github.com/ethereum/EthLib.git | 2cd5d14a6a2f6fd22ef6b68423e45cfa3a21001a |
| plausible | https://github.com/leanprover-community/plausible | dfa4f38190d07c37e315953e08b90fe2d95b3c24 |
| LeanSearchClient | https://github.com/leanprover-community/LeanSearchClient | d6b4c7be5be75ec4917c873ac50c756dc1436372 |
| importGraph | https://github.com/leanprover-community/import-graph | a41f0e9a4dea23188ea9cc1c41ac9f8bbafe0b93 |
| proofwidgets | https://github.com/leanprover-community/ProofWidgets4 | df72b022e558978a1c50264cfc4d7fec86fa8e04 |
| aesop | https://github.com/leanprover-community/aesop | 4a174c490d8707121c4a9290800489f105d85e07 |
| Qq | https://github.com/leanprover-community/quote4 | dce0ad79c486cb1fb504af04f953c3466b0c6db8 |
| batteries | https://github.com/leanprover-community/batteries | 66e469188fe07963e5cf666c7d4433f45b8131c5 |
| VCVio | https://github.com/Verified-zkEVM/VCVio.git | bbf05eeeedf84c5f98baaf5ab846f2d2479cc8ab |
| Cli | https://github.com/leanprover/lean4-cli | c24fe6078c630e89b489bffe59b3e20ac30d12c8 |
| QuantumFoundations | https://github.com/lean-crypto-foundations/QuantumFoundations | 901aaab7967ceecd2240d0b38bbde7cf3e2c14ac |
| PolyFun | https://github.com/Verified-zkEVM/PolyFun | 4181c82238142d9b73403fbf4c4b13e1a801e400 |
| cslib | https://github.com/leanprover/cslib | 5b56df99362532c46e1175381fbbdd755bd56030 |

### Root imports outside Verify/SourceText

| module | imports outside G0 |
|---|---|
| Grammar | SolidCore.Solidity.Checked, Verify.Spec.Contract, SolidCore.Refinement.Abi |
| Bridge | Verify.Generic.Expected, Verify.ShapeBundle, Verify.ShapeSpecExport, Verify.ShapeGeneric, SolidCore.Solidity.Shared.PrecompileCrypto |
| TestRuns | Verify.VC.KernelIdx (mkIdx_eq, at the base) |
| Cases/*/Imported | SolidCore.Solidity.Checked |
| Cases/Selectors | SolidCore.Refinement.KernelRfl, SolidCore.Solidity.Checked |
| Instances/Flag | flag_4ce5cf9a.Final (the record's modules) |
| Audit, AuditFlag | Lean |

## Production and diagnostics

Production: the lean_libs `VerifySourceText` (Grammar, Bridge, Run, Tests, TestRuns, and the cases)
and `VerifySourceTextFlag` (Instances/Flag). Audit.lean and AuditFlag.lean walk every constant of
every `Verify.SourceText` module in that closure through `Lean.collectAxioms`: Lean's three axioms
only (3826 constants; 3854 with Flag). They fail on native_decide's axioms, a declared axiom or
sorry (check.sh's tampered audits), and on any imported `Verify.SourceText.Diagnostics` module, a
name reserved for diagnostic witnesses outside this policy. The branch has no such module: the
earlier native-evaluation runs are replaced by kernel runs of `Source.run` (TestRuns.lean, with `mkIdx_eq`).

## LedgerRelay: what its certificate still needs

The property row for LedgerRelay is NOT RUN. It needs one artifact and one small module:

1. **A certify record of LedgerRelay at the frozen candidate pin.** The generic driver (solar's
   `scripts/certify` with `tools/certify/generic.py` and `final.py`) writes `Certified/<name>/Final.lean` with
   `Final.final`, whose second component is `Expected Final.src Final.spec Final.runtimeBytes`
   (`Verify.Generic.Expected : Source → Spec → List Nat → Prop`). Checked so far, by the
   frontend steps only (no build, no certify): generic.py's `envelope` accepts LedgerRelay with its
   five functions and natspec, and `tools/certify/spec.sh` exports its spec with no function
   refused. Not checked: the stage export at the pin, the stage proofs, final.py's `Final`, the build.
   Owner: the run is the publisher's and acceptance's to schedule after the candidate freeze.
   No missing lemma or emitter is known; any gap would show in that run as a named stage.
2. **Instances/LedgerRelay.lean** (owner: this branch), the same four facts as Flag's: `read_eq`
   against the record's `Src`, `Lowering` hints and spec bundle; `source_eq` and `spec_eq` (`rfl`
   for Flag, expected the same since final.py's spec has `Reading.spec`'s form, confirmed only on
   Flag); and `statement_of_agree … Final.final.2`. Plus a record assembly like `flag_record.sh`.

The spec semantics being noncomputable does not block this: the property comes from the proved
certificate, not from evaluating the spec.

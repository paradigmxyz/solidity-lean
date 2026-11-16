# UniswapV2ERC20.transfer: exact-input binding receipt

`verify_binding.sh` is the fail-closed successor of `verify_bytes.sh` (kept unchanged; it compares
bytes only). Before it compares anything, it checks the sha256 of every input in `PINS` and exits 2
naming the first pin that differs. It then copies the source once and runs all four tools on that
one copy:
1. solar's fresh emit and its stage export, in one run;
2. solc's AST and the importer;
3. the spec export.

It re-checks the copy's sha256 at the end. The runtime bytes must equal `Statement.lean`'s
`runtimeBytes`. The stage modules, the imported `Source.lean` and the spec export must equal the
generated files the proof was built and replayed from, byte for byte. Any difference exits 1 and
names the artifact.

## The one source identity

The four outputs come from the same raw bytes, sha256
**14da00cdeaf2ab3709d2d9838be2c2a144502b32b874b55394d7a8792deac80b** (the flattened
`scripts/verify/uniswap-v2/UniswapV2ERC20.sol`).

The earlier mismatch: `uniswap_v2_erc20_stages.sh` exported the stages from the unflattened port
(sha256 762294af…5d4c). Exporting them again from the flattened bytes gives the same 18 stage
modules byte for byte (`Stage0`, `Mir1`–`Mir4`, `Evm1`–`Evm11`, `Sched`, `Bytecode`). Only
`Manifest.lean` differs: it lists the source files read and the export directory, no module in the
replayed closure imports it, and `verify_binding.sh` skips it by name. The modules the proof uses
are therefore the export of 14da00cd.

## Pins (enforced)

| Pin | sha256 |
|---|---|
| source (flattened port) | 14da00cdeaf2ab3709d2d9838be2c2a144502b32b874b55394d7a8792deac80b |
| options (`-Ogas --evm-version osaka`) | e8dcb59d1d2c9325d924f23afb16523ebcef2750f7fa447cf67b494f81a9038c |
| solc 0.8.35+commit.47b9dedd | fa8ac9a32d301ad023a36ee5a29f8e291fe3200c60244e43c142539e82a617f4 |
| emitter: solar 697fc686 release binary | dca17546509f702c38639487a73c101b72d97718f0e13d51c307d1b971b92851 |
| spec exporter: solar-verify (solar 902cccc2) | 4468c71522c1e26e15e20808b87f5d4e0e81070602fce1ed2eea02c262cbd464 |
| spec (`transfer-slice.spec`, solar 902cccc2) | df8e094e5ab682001e87ee14eca9d20e7d56ba8db4bdadb348523f70c0d2199c |
| spec applier (`apply_specs.py`, solar 902cccc2) | dd85461ff04414986d21a52d768aa9895cdda5bb89681d29bacf355c5ba6e59e |
| importer (`scripts/solc_ast_to_lean_source.py`) | 5b35afb636bdda997b0b7a51a492d134dadabf7e04eb97f9625c0d1f21e12e3b |
| importer's cache module (`scripts/harness_cache.py`) | baf2965207de14bce9c029e3969d6c580be7a03ae44b2b2f445398651188d18a |
| import driver (`scripts/verify/uniswap_v2_sources.py`) | 9b9a3f658e077dc35c13799eafd39127ef3630759f57323e2798835d6e13b03e |

## Checked outputs

These are the values from `binding.json` (sha256 085c2b64de4ea2451291bc8b4a91731f0925a8f29fa6d22b38792d32ba082467, committed beside this file).
* The 1183 runtime bytes equal `runtimeBytes`; runtime hex sha256 0bba75d501e65bc87829d7dfbee57711df84c91d2cf44d19907b1a26b043e12c.
* The imported `Source.lean` sha256 is e7f4cd9c7fcf69d59d92f8e8e3d466d6eeaf4ccf0a215a97137ed094bf94cfbc.
* The spec export `Slice/Gen/Spec.lean` sha256 is 52b44937f5f85d6c022d448258d5ad5d5a1720c4aa6545323e44426efa60360a.
* `binding.json` also lists each of the 18 stage modules with its sha256.

## Receipts

```sh
SOLAR_DIR=<solar at 902cccc2 with target/release/solar-verify> bash Certified/uv2_transfer_e6/verify_binding.sh
# pins: all 10 match; runtime equal True; stages: 18 modules equal the fresh export;
# import: equal True; spec: equal True; BOUND: source 14da00cd…  -> exit 0
SOLAR_DIR=<same> bash Certified/uv2_transfer_e6/verify_binding_negatives.sh   # exit 0 when every control exits as required
```

```
pass source exit 2: BINDING FAILED: pin source: sha256 aafd324609d6fcb24f33bf696ba70ddff466c298e1c60672bf2966c0cf9bbdad
pass options exit 2: BINDING FAILED: pin options: sha256 a6067e088d93b14a07e32d6ea1fce1e6edc289fcbed96dd33efaff3f213e8f80
pass solc exit 2: BINDING FAILED: pin solc: sha256 fb8930c984830db9642ccb405a2a39ff8240633899b6d750345e097ae29442c0
pass emitter exit 2: BINDING FAILED: pin emitter: sha256 37efd9c5586349a2f15fc85983f7411bf2a065deda1e8689500b4d0c1d2f821c
pass spec-exporter exit 2: BINDING FAILED: pin spec-exporter: sha256 2544a8ea516d4e0f4ac7efccfbd90ab9ba162ff6efdf42ef7fbd53badc8c101b
pass copy-unaltered exit 0: BOUND: source 14da00cdeaf2ab3709d2d9838be2c2a144502b32b874b55394d7a8792deac80b
pass runtime-bytes exit 1: BINDING FAILED: runtime bytes differ from Statement.lean's runtimeBytes
pass stage exit 1: BINDING FAILED: stage Mir2.lean differs from the fresh export
pass import exit 1: BINDING FAILED: import: imported source differs from Contracts/UniswapV2/ERC20/Source.lean
pass spec exit 1: BINDING FAILED: spec export differs from Slice/Gen/Spec.lean
NEGATIVES EXIT 0
```

Each pin control replaces one input with an altered copy (one flipped source byte, `-Osize` for
`-Ogas`, one byte appended to the solc, emitter or spec-exporter binary) and exits 2 naming that
pin before anything runs. The copy controls run the script on a copy of the inputs and expect exit
1 with the stage named; the unaltered copy binds with exit 0. That shows each copy control fails
only because of its alteration.

## Scope and what stays OPEN

* This binds one exact source file to the bytes, stages, import and spec the proof uses. It is not
  a universal source-text end-to-end result. The flattened file is the port's text, not v2-core's,
  and the port, the flattener and the spec text stay in the TCB along with solc's AST, the importer
  and the spec export.
* **Path normalization.** `importedSourceName` in `Source.lean` is solc's absolute path of the file
  in the checkout where it was generated (`/home/hand/wt/e6`). `verify_binding.sh` rewrites that one
  string to the recorded checkout before comparing. It also maps the private copy's file name back
  to `UniswapV2ERC20.sol` (2 occurrences, checked).
* **Generated files are not committed** (GPL-3.0 port); the script compares against the checkout's
  generated files. Their hashes are in `GENERATED.sha256` and `binding.json`.
* **Toolchain identities, OPEN:** the toolchain is pinned by hash, but the emitter binary's
  reproducibility from solar 697fc686 is not shown (one build, one hash).
* **Process-tree RSS admission: OPEN.** The 5.6 GiB peak covers `leanchecker` only.
* The closure replay (4027 of 4027, 0 trusted, 0 unaccounted) is reused from MANIFEST.md, not rerun.

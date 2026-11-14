# slice-spec (E7): UniswapV2ERC20.transfer, the spec carried from source to bytes

**Status: E7 proved for the first slice over SolidCore's runs, carried to bytes conditionally.** The transfer spec (sequential post, scoped hash premise, physical-slot frame) is proved of SolidCore's checked `transfer` for every valid call. solar-verify's exported spec is discharged over SolidCore runs, including its succeeds-if. NonVacuous holds for all three posts. Three semantic mutants are refused by execution. The transfer lemma carries Meets to the bytes through `Equiv`. **Not CERTIFIED:** `Equiv` (E4 to E6) and `Resources` (E8) are named hypotheses here, and two gaps against the target remain open (listed below).

Base: solidity-lean `alpharush/certified-translation` 6cb2c01 (includes aa0b3eb and 423bf6d), plus this lane's one commit ea2b198 (bundle and patch here). The only rebase conflict was `Contracts/UniswapV2/.gitignore` (both sides appended lines); every receipt below is from the rebased tree. solar: `alpharush/certified` 38b5232, plus `solar-slice-spec.patch`. Lean 4.35.0, `LEAN_NUM_THREADS=1`, `lake build -KleanMemory=6000`.

## Proved edges (theorem names, namespace `SolidCore.Spec.UniswapV2.ERC20.Slice`)

| Edge | Theorems | Premises |
|---|---|---|
| Spec export (solar) | `Gen/Spec.lean` (`--emit-lean-spec` of `transfer-slice.spec`), `UniswapV2ERC20_wf` | none |
| Erased tree = SolidCore's checked `transfer` | `Gen.transfer_erase_eq`, `Gen.deploy_eq` (kernel_rfl), `tree_eq` | none |
| Tree semantics | `tree_seq`, `res_ok`, `res_sub`, `res_add` | none (slots are the source's `solHash k 1`) |
| SolidCore runs | `run_tree`, `meets_seq : Meets (solidCore fuel) c (Valid deployed) SeqPost` | `hc : contract? = .ok c` |
| Target post | `targetPost_of_seq`, `meets_target : Meets (solidCore fuel) c ValidIn TargetPost` | `ValidIn` includes `Scope` |
| Exported spec VC | `transfer_meets` (tree), `transfer_holds` (`HoldsFnUnder` over SolidCore), `meets_bundle` (`Meets … bundlePost`) | `SepArgs` = `Scope` (`sepArgs_iff`) |
| NonVacuous | `valid_inhabited`, `nonVacuous_seq`, `nonVacuous_target`, `Mutants.nonVacuous_bundle` | the premise holds of the real keccak256 (`scopedSep_transfer_example`, kernel) |
| Required concrete runs | `self_max` (balance 2^256-1, self-transfer 1: success, balance unchanged, Transfer logged), `self_short` (self-transfer 6 > 5: reverts `ds-math-sub-underflow`, no change); general `self_ok`, `self_fail` | `hc` only (no hash premise) |
| Source to bytes (transfer lemma) | `meets_bytes` (Equiv + Meets ⇒ Post ∨ Inert at every gas < 2^256), `meets_bytes_enough` (+ Resources ⇒ Post); `bytes_target`, `bytes_seq`, `bytes_bundle`, `bytes_target_enough`; `terminates`, `functional_of_equiv`, `certified_of` | **`heq : Equiv (solidCore fuel) c code ValidIn` (E4–E6), `hres : Resources …` (E8)** |
| Semantic mutants refused by execution | `Mutants.debit_refuted_target/seq`, `log_refuted_target/seq`, `ret_refuted_target/seq`, `ret_refuted_bundle` | the mutant's own `contract? = .ok c` |

The **posts**:
- `SeqPost`: storage updates in source order (debit the caller, then credit the recipient reading the debited state). Success iff `v ≤ bal[caller]` and `debit(bal)[to] + v < 2^256`. On success, the storage is `seqStore`, the logs are `[Transfer(caller,to,v)]` and the output is `true`. Otherwise the call reverts with `Error("ds-math-sub-underflow"|"ds-math-add-overflow")`, no log and no change.
- `TargetPost` is docs/CERTIFICATION_TARGET.md's form:
  - `caller ≠ to`: success iff the balance covers `v` and `bal[to]+v < 2^256`; then the debit and the credit.
  - `caller = to`: success iff `v ≤ bal`, with the storage unchanged and **no recipient-overflow condition**.
  - Frame: every physical slot `n` with `n mod 2^256` outside {slot(caller), slot(to)} is unchanged. It never quantifies over keys.

**Hash premise:** `Scope call := ScopedSep (transferFootprint 1 caller to)` (Verify/Spec/HashScope.lean, 27a02d4). It asks keccak256 to be injective, with images ≥ 2^128, on the two balance preimages only. There is no frame family and nothing about other keys. It is part of `ValidIn`, so it appears in every statement that uses it. `SeqPost`, `self_max` and `self_short` need no premise.

## Build receipts (clean rebuild, one module at a time; peak = max VmHWM of lean)

Regeneration from scratch (`scripts/verify/uniswap_v2_transfer_slice.sh`): `generate EXIT 0 73s; gen diff EXIT 0` (`gen.diff` empty: regeneration is byte-identical)

| Module | Exit | Time | Peak KiB |
|---|---|---|---|
| Gen.Spec | 0 | 3 s | (under the 1 s sampling) |
| Gen.Tree | 0 | 94 s | 6,055,944 |
| Post | 0 | 10 s | 2,985,480 |
| Run | 0 | 8 s | 2,587,000 |
| Vc | 0 | 34 s | 3,747,596 |
| Statement | 0 | 6 s | 2,577,092 |
| Bytes | 0 | 6 s | 2,577,284 |
| Gen.MutLog.Source | 0 | 6 s | 2,089,584 |
| Gen.MutLog.Core | 0 | 104 s | 4,712,540 |
| Gen.MutLog.Tree | 0 | 89 s | 6,058,012 |
| Gen.MutRet.Source | 0 | 5 s | 2,049,948 |
| Gen.MutRet.Core | 0 | 97 s | 4,715,672 |
| Gen.MutRet.Tree | 0 | 84 s | 6,056,216 |
| Mutants | 0 | 33 s | 4,343,880 |
| BundleNeg | 0 | 6 s | 2,266,648 |
| Gen.MutDebit.Source | 0 | 5 s | 2,026,920 |
| Gen.MutDebit.Core | 0 | 100 s | 4,735,280 |
| Gen.MutDebit.Tree | 0 | 82 s | 6,085,620 |
| MutantsDebit | 0 | 17 s | 3,473,496 |
| All | 0 | 7 s | 2,606,976 |
| lib ContractsUniswapV2TransferSlice | 0 | 3 s | (under the 1 s sampling) |

Axioms: `All.lean` guards `#print axioms` for every theorem above with `#guard_msgs`. Each depends on at most `[propext, Classical.choice, Quot.sound]`; `tree_eq` and `inert_not_target` depend on `[propext]` only. No `sorry` appears in any Slice module (`receipts/sorry.txt` is empty; `grep -rn sorry` over the Slice sources finds none).

SMT sanity check (not a proof edge): solar-verify on `transfer-slice.spec` gives `UniswapV2ERC20.transfer (7 obligations)` verified, 10 verified, 0 errors, z3 4.13.4. `receipts/smt.log`: exit 0, 61 s, peak 209,872 KiB.

## Missing bridges and gaps (block CERTIFIED)

1. **`Equiv` for this slice's bytes (E4–E6)** and **`Resources` (E8)** are hypotheses. 423bf6d proves a gas bound for transfer (`Shapes.ResourcesFrom`, G = 8199112). Composing it with `certified_of` needs `Resources` on `ValidIn` and the same `code`.
2. **Any caller:** `SolarTV.Call` has no caller field, so `Valid` fixes the caller at `0x2000` (`Generic.callerWord`), while the target asks for any caller. 423bf6d generalizes only the gas side to any CALLER.
3. **Any storage:** `Valid` takes storages that write the constructor's slot 3 (`Covers deployed σ`, the generic stage's scope), while the target asks for any storage.
4. Exact ABI calldata only: a clean address and a word, 68 bytes. Dirty or short calldata is outside `Valid`.
5. Without `Resources`, the bytes side is "Post or Inert". An out-of-gas failure leaves nothing changed and does not meet `TargetPost` (`inert_not_target`).
6. The exported spec language has no log or revert-data clauses. So the log mutant is refused by `SeqPost`/`TargetPost` but not by `bundlePost`.
7. Byte-level negatives (altered bytecode or jump, mismatched environment) belong to the E5/E6 lanes. These mutants are source mutants, executed by SolidCore.

## Findings on the landed tooling

- `tree_meets_scoped` (Verify/Spec/HashScope.lean): `hash_facts_scoped` adds no instance. Its `try (have := …; rotate_left; simp; done)` calls `done` while the main goal is still open, so every instance is rolled back. This slice's copy (`Vc.lean`) adds the one fact it needs (`hk`, `hk'`) explicitly.
- The landed tactic also cannot discharge `succeeds-if`: its second goal is assumed closed by `simp at hne`. `Vc.lean`'s copy evaluates the `succeeds-if` premise (`hsi`) beside the invariants. This is the repository's first discharged `succeeds-if`.
- A mutant edit that leaves a bare expression statement (`balanceOf[from].sub(value);`) is outside the generic source stage. The debit mutant is therefore `.sub(value).add(value)`.

## Files

- `solidity-lean-slice-spec.bundle` (`git bundle`, base 6cb2c01) and `solidity-lean-slice-spec.patch` (`format-patch`). They add `Contracts/UniswapV2/ERC20/Slice/{Post,Run,Vc,Statement,Bytes,Mutants,MutantsDebit,BundleNeg,All}.lean`, the `lakefile` library `ContractsUniswapV2TransferSlice`, `scripts/verify/uniswap_v2_transfer_slice.sh`, `uniswap_v2_mutant.py` and `uniswap-v2/transfer-mutants.txt`. `Slice/Gen/` is generated from the GPL-3.0 port and is not committed.
- `solar-slice-spec.patch`: `crates/verify/uniswap-v2/transfer-slice.spec`, and `tools/certify/spec_connect.py --tree-only`.
- `receipts/`: per-module build logs, `modules.txt`, `generate.log`, `gen.diff` (empty) and `smt.log`.
- `wip/`: the pre-reset WIP bundle (a698313), superseded by this delivery.

Reproduce: run `scripts/verify/uniswap_v2_gen.sh`, then `SOLAR_DIR=… SOLAR_VERIFY=… scripts/verify/uniswap_v2_transfer_slice.sh`, then `lake build -KleanMemory=6000 ContractsUniswapV2TransferSlice`.

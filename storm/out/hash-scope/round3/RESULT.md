# hash-scope round 3: the driver prints and checks the scoped hash premise

**solar** branch `hash-scope3`: one commit **0b98e45d** on PR #2637 head **902cccc2**, delivered as `solar-hash-scope3.bundle`
(range 902cccc2..hash-scope3) and `0001-feat-certify-*.patch`. **solidity-lean**: no change needed; tested against PR #166 head
**f8a4a744** (which already holds `ScopedSep`, `HashScopeCheck` and the slice's per-call `Scope`).

Apply: `git fetch storm/out/hash-scope/round3/solar-hash-scope3.bundle hash-scope3 && git checkout FETCH_HEAD`, or `git am` the patch on 902cccc2.

## What changed (solar)

- `tools/certify/check_final.lean`: after its existing checks, it walks the published `Statement`'s value and every definition it unfolds to.
  It skips the toolchain and upstream packages, never walks through theorems, and stops at the premise constants. It prints one line per
  keccak256 premise, `PREMISE <class> <definition> <constant> <term>`, or `PREMISE none`. The classes are:
  - `scoped`: `SolidCore.Spec.ScopedSep L`, or `TrustedBase.KeccakSeparated (· ∈ L)` written out.
  - `global`: `MapSlotsSeparated`, `UniversalTransferSep`, `SolidCore.Verify.VC.Token.HashInj`, the Factory's `KeccakModel`,
    `KeccakSeparated` of any other predicate, or `NestedSlotsSeparated _ []`.
  - `refuted`: `NestedSlotsSeparated` with a nested map (`not_nestedSlotsSeparated`), or `KeccakSeparated (fun _ => True)`
    (`not_keccakSeparated_univ`). **The checker exits 1 on this class**: the statement is vacuous.
  The term is fully qualified, with implicit arguments dropped and numerals as decimals. A variable bound by the definition prints as `#name`.
- `tools/certify/footprint.py` (new): the decidable footprint check. For each scoped premise it writes one Lean file importing
  `NAME.Statement` and `Verify.Spec.HashScopeCheck`, with `theorem fp_i : SolidCore.Spec.ScopedSep (FP) := SolidCore.Spec.scopedSep_of_check (by decide +kernel)`
  per concrete instance, and audits `#print axioms` (propext, Classical.choice, Quot.sound only).
  - An open address in `transferFootprint`, `approveFootprint` or `transferFromFootprint` is instantiated at the footprint's
    closed addresses (the self-call), 1, 2^160-1 and `shape.json`'s `footprint_witnesses`. At most 32 instances are checked.
  - An open mapping slot or an unknown footprint shape is reported as not checked, and so is a global premise.
  - Exit codes: 1 when any instance is refused (or the audit fails), 2 on malformed input.
- `scripts/certify` (step 6b): runs `footprint.py` right after `check_final` and dies on a refusal. The run record gets
  `statuses.hash_premise` (e.g. "scoped … real keccak256 accepted by the kernel at N concrete call(s) (…), not proved for every call") and
  `hash_premises` (the premise list with each instance and its axioms). The status summary line prints `hash_premise`.
  The strongest status is unchanged: a global single-level premise stays a named, printed assumption, as the target allows.
- `tools/certify/test.sh`: 7 Lean-free unit cases for `footprint.py` (malformed line, refuted, bad witness, none, global,
  open slot, a failing lean). `tools/certify/README.md`: a "Hash premises" paragraph.

## Receipts (hosted Hand, Lean 4.35.0, LEAN_NUM_THREADS=1; `~/bin/peak.py` reports getrusage max RSS of the children)

Fixture: four published-statement-shaped modules in `fixture/hstest`, built in the f8a4a744 checkout through a scratch lean_lib
(`fixture/lakefile-scratch.diff`, not committed). `hs_scoped.Statement` is `∀ call, Scope call ∧ True ↔ Scope call` over the slice's real
`SolidCore.Spec.UniswapV2.ERC20.Slice.Scope` (Contracts/UniswapV2/ERC20/Slice/Post.lean). The other three put
`MapSlotsSeparated [0]`, `NestedSlotsSeparated [1,4] [2]` or no premise in front of a trivial proposition. Each `final` uses propext only.

```
lake build -KleanMemory=5000 HsTest                                  (all 8 modules built; lake exit 1 only from the scratch glob's missing root files)
                                                                        RECEIPT wall 175.8 s, peak 4158 MB
lake env lean --run tools/certify/check_final.lean hs_scoped hs_scoped.Proof    exit 0  19.6 s  peak 7582 MB
  PREMISE scoped SolidCore.Spec.UniswapV2.ERC20.Slice.Scope SolidCore.Spec.ScopedSep (SolidCore.Spec.transferFootprint SolidCore.Spec.UniswapV2.ERC20.Slice.balanceSlot SolidCore.Spec.UniswapV2.ERC20.Slice.caller #dst)
check_final hs_global   exit 0  14.1 s  peak 7613 MB   PREMISE global Certified.hs_global.Final.Statement SolidCore.Spec.MapSlotsSeparated (List.cons 0 (List.nil))
check_final hs_refuted  exit 1  13.6 s  peak 7613 MB   "... rests on SolidCore.Spec.NestedSlotsSeparated ... which Lean proves false: the statement is vacuous"
check_final hs_none     exit 0  14.3 s  peak 7614 MB   PREMISE none
baseline: check_final at 902cccc2 on hs_none           exit 0  16.0 s  peak 7524 MB   (the walk adds no measurable memory)

footprint.py on hs_scoped's log                         exit 0  23.9 s  peak 3323 MB
  kernel accepted ScopedSep (transferFootprint balanceSlot caller caller)          axioms [propext, Quot.sound]   (self-transfer)
  kernel accepted ScopedSep (transferFootprint balanceSlot caller 1)               axioms [propext, Quot.sound]
  kernel accepted ScopedSep (transferFootprint balanceSlot caller 2^160-1)         axioms [propext, Quot.sound]
  (an earlier run with --witness 0x5B38Da6a…ddC4 accepted that recipient as well: 4 of 4, exit 0, 27.4 s, peak 3324 MB)
footprint.py on hs_global's log                         exit 0   not checked: global premise (no Lean run)
footprint.py, negative control: ScopedSep [[0],[256]]   exit 1  18.3 s  peak 3309 MB   refused (the kernel decides the check false: the two preimages collide)
test.sh footprint unit cases (extracted, Lean-free)     7 ok, 0 failed
ruff format --check / ruff check tools/certify/footprint.py: clean; ty check tools/certify: no footprint.py diagnostic
bash -n scripts/certify: ok
```
The fixture logs and JSON records are in `fixture/`.

## What this does and does not claim

- The footprint check proves the transfer premise for the real keccak256 **at the listed concrete calls**, by kernel evaluation. It is
  not a proof for every (caller, to). That would be `UniversalTransferSep`, which is global (`universalTransferSep_iff`) and
  unproved. The record says this in words.
- Premise discovery is syntactic. A premise reached only through a theorem or an opaque constant is not reported, and neither is a
  premise under a name not in the list above. A `ScopedSep` the statement concludes rather than assumes would also be reported as a premise.
- Not run: the full `scripts/certify` driver end to end. Its pin, `tools/certify/solidity-lean.rev` = d0ab5d63, is not f8a4a744,
  and there is no `Certified/uv2_erc20/shape.json` that publishes `Contracts.UniswapV2.ERC20.Certified.Transfer.certified` through the
  driver yet. That module needs the GPL-generated uv2 stages, which were not regenerated here. The driver glue was checked with `bash -n`,
  and the record block was run in isolation on the three fixture JSONs (scoped, global, missing).
- Next: a `Certified/uv2_erc20/shape.json` (kind certified, valid `Slice.ValidIn`, proof `…Certified.certified`), then a real driver run.
  Its record should show `hash_premise: scoped … ScopedSep (transferFootprint balanceSlot caller #dst) … accepted at 3 concrete calls`.

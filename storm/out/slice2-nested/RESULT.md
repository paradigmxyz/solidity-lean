# slice2-nested: UniswapV2ERC20 approve and transferFrom (checkpoint 2)

Base: solidity-lean 9fb89ee (alpharush/certified-translation). Lane commits 6f6d390..aca1a6b on top
(bundle sl-slice2-nested.bundle, range 9fb89ee..work/slice2-nested; same as sl-patches/0001-0004).
solar used for stage0: 38b5232ad (alpharush/certified), `-Ogas --evm-version osaka`.
Pinned source: scripts/verify/uniswap-v2/UniswapV2ERC20.sol as uniswap_v2_gen.sh writes it,
sha256 14da00cdeaf2ab3709d2d9838be2c2a144502b32b874b55394d7a8792deac80b. Runtime of that run: 1183
bytes, sha256 ca4c19254b2852f3b0642e24002c616a048c6f343671324c7ae81a4cad971a0b (-Zemit-lean-stages
checked not to change them).

No GPL-derived file is in the patches: the erased trees (Nested/Trees.lean), stage0 and its mutants
(Certified/uv2_erc20/) are generated at build and gitignored.

## Edge status

| Edge | approve | transferFrom |
|---|---|---|
| E1 frontend | TRUSTED (stated; shared with transfer) | same |
| E3 source -> MIR stage0 | **PROVED** `approve_source_to_mir`, `approve_defined` | **PROVED** `transferFrom_source_to_mir`, `transferFrom_defined` |
| E3 negative controls | **PROVED** `rejects_approve_no_write`, `rejects_approve_wrong_slot` | **PROVED** `rejects_transferFrom_no_spend` |
| Spec, source level | **PROVED** `approve_meets` (exact sequential result, no premise); `approve_keys` (scoped premise) | **PROVED** `transferFrom_meets` (exact sequential result, no premise); `transferFrom_keys`, `transferFrom_self`, `transferFrom_self_max`, `transferFrom_self_short` (scoped premise) |
| E4 stage0 -> EVM IR | MISSING: no stage certificates for this solar build (the earlier uv2_erc20 milestone was for an older 2187-byte build and is not in the tree) | same |
| E5 bytes | MISSING. 9fb89ee's AssembleNoCall (call-free runner premises) does not apply as is: the runtime has a STATICCALL (permit's ecrecover, offset 0x387), so StaticRunner/CalleesRun must be discharged for a runtime with a STATICCALL that approve and transferFrom never reach | same |
| E6, E7, E8 | MISSING (need E4, E5) | same |

Status: NOT CERTIFIED. Blocking edges: E4, E5, E6, E7 (spec carried to bytes), E8.
Shared gap with transfer: the caller is the stage's (0x2000): SolarTV.Call has no caller field.

## Theorems (namespace SolidCore.Spec.UniswapV2.ERC20.Nested unless noted)

Specs are the source's effect as sequential storage updates in source order
(`upd st k v n := if k = n % 2^256 then v else st n`), at the slots SolidCore computes
(`allowanceSlot o s := solHash s (solHash o 2)`, `balanceSlot a := solHash a 1`). They need no hash
premise: aliasing of slots is the source's own. The premise enters only key-level corollaries.

approve (Nested/Approve.lean):
- `approveResult st spender value`: spender >= 2^160 reverts (no data, no change); else success, output
  word 1, log `([approvalTopic, caller, spender], word32 value)`, storage `upd st (allowanceSlot caller spender) value`.
- `approve_tree_eval`: the erased tree gives exactly `approveResult` for every argument word and storage.
- `approve_frame`: every slot n with `n % 2^256 ≠ allowanceSlot caller spender` unchanged (slots, no premise).
- `approve_meets (hc : contract? = .ok c) : Meets (solidCore fuel) c ApproveValid ApprovePost`.
- `approve_keys (hsp : spender < 2^160) (h : HashScopeNested.Scoped (approveFootprint caller spender))`:
  success, the allowance slot holds value, every slot below 2^128 (totalSupply, DOMAIN_SEPARATOR) unchanged.

transferFrom (Nested/TransferFromSpec.lean, Nested/TransferFrom.lean):
- `transferFromResult st frm dst value`: dirty frm or dst reverts with no data; `a := st (allowanceSlot frm caller)`;
  unless `a = 2^256-1`, `value > a` reverts with SafeMath's `ds-math-sub-underflow` data, else writes `a - value`;
  then debit `balanceOf[frm]` reading that storage (`ds-math-sub-underflow`), then credit `balanceOf[dst]` reading
  the debited storage (`ds-math-add-overflow` when it reaches 2^256); log Transfer(frm, dst, value); return true.
  Reverts change nothing and log nothing.
- `transferFrom_tree_eq : transferFrom_tree = tfTree` (decide +kernel; tfTree names the tree's words).
- `transferFrom_tree_eval (hst : ∀ k, st k < 2^256)`: the erased tree gives exactly `transferFromResult`.
- `transferFrom_meets hc : Meets (solidCore fuel) c TransferFromValid TransferFromPost`.
- `transferFrom_keys` (frm ≠ dst, clean addresses, `Scoped (transferFromFootprint caller frm dst)`): success iff
  (allowance infinite or ≥ value) ∧ value ≤ balanceOf[frm] ∧ balanceOf[dst] + value < 2^256, all on the storage
  before the call; on success the allowance is `2^256-1` if it was, else `a - value`, the balances debited and credited.
- `transferFrom_self` (frm = dst, `Scoped (transferFromFootprint caller frm frm)`): success iff (allowance
  infinite or ≥ value) ∧ value ≤ balance, no overflow condition; balance unchanged.
- `transferFrom_self_max`: balance 2^256-1, infinite allowance, value 1, self: succeeds, balance stays 2^256-1.
- `transferFrom_self_short`: self-transfer with balance < value reverts.

E3 (Nested/LoweringApprove.lean, Nested/LoweringTransferFrom.lean, Nested/NegE3.lean):
- `check_approve_ok`, `check_transferFrom_ok`: `Generic.check fuel 200 c.core stage0 [fn] .all = true` (kernel_rfl).
- `approve_source_to_mir o (ho : Generic.SourceEnvOk o) hc : Stage (solidCore fuel) (moduleSem o) c stage0
  (fun call => ∃ σ, Covers deployed σ ∧ fullScope [fn_approve] σ call)`; likewise transferFrom.
- `approve_defined`, `transferFrom_defined`: SolidCore has a result on every valid call (by the checker).
- `rejects_approve_no_write`, `rejects_approve_wrong_slot`, `rejects_transferFrom_no_spend`: the same check
  evaluates to false on stage0 with _approve's SSTORE dropped, with _approve hashing into slot 3, and with
  transferFrom's allowance SSTORE dropped (scripts/verify/uniswap_v2_stage0_mutants.py).

## Exact premises

Verify/Spec/HashScopeNested.lean (namespace SolidCore.Spec.HashScopeNested):

```lean
abbrev Scoped (L : List (List Nat)) : Prop := ScopedSep L
-- hash-scope's Verify/Spec/HashScope.lean (27a02d4, in the base):
-- def ScopedSep (L : List (List Nat)) : Prop := TrustedBase.KeccakSeparated (· ∈ L)
-- def KeccakSeparated (S : Preimages) : Prop :=
--   (∀ x y, S x → S y → keccakWord x = keccakWord y → x = y) ∧ ∀ x, S x → 2 ^ 128 ≤ keccakWord x
abbrev pre (a m : Nat) : List Nat := TrustedBase.mappingPreimage a m   -- wordBytes a ++ wordBytes m
def nestedFootprint (n o s : Nat) : List (List Nat) := [pre o n, pre s (solHash o n)]
def approveFootprint (caller spender : Nat) : List (List Nat) := nestedFootprint 2 caller spender
def transferFromFootprint (caller frm dst : Nat) : List (List Nat) :=
  nestedFootprint 2 frm caller ++ [pre frm 1, pre dst 1]
```

Coordinated with hash-scope: `Scoped` is their `ScopedSep`, one premise for single-level and nested
maps; this module only adds the nested footprints and slot lemmas (`slot_ge`, `slot_ne`, `nested_ne_flat`,
`transferFrom_slots`, `approve_slot`). Satisfiable with the real keccak256 on a concrete nontrivial
footprint (`transferFrom_scoped_witness : Scoped (transferFromFootprint 0x2000 1 2)`, four images by
decide +kernel), and not trivial (`not_scoped_collision : ¬ Scoped [[0], [256]]`). E3 takes only
`Generic.SourceEnvOk o` (the oracle's caller and two-word keccak agree with SolidCore's).

## Build receipts (LEAN_NUM_THREADS=1, 14 GB Hand, Lean 4.35.0)

```
scripts/verify/uniswap_v2_gen.sh                                       exit 0
SOLAR=solar(38b5232ad) scripts/verify/uniswap_v2_stage0.sh             exit 0
python3 scripts/verify/uniswap_v2_stage0_mutants.py                    exit 0
lake build Contracts.UniswapV2.ERC20.Core Contracts.UniswapV2.ERC20.SpecTreeKeccak   exit 0
python3 scripts/verify/uniswap_v2_trees.py                             exit 0
lake build -KleanMemory=6000 ContractsUniswapV2ERC20Nested   (clean, 9 modules + HashScopeNested)
                                                   exit 0, peak RSS 5891 MB, 275 s
  Trees 77 s · LoweringApprove 20 s (5133 MB alone) · LoweringTransferFrom 24 s (5609 MB alone)
  NegE3 57 s (5430 MB alone) · HashScopeNested 14 s (3318 MB) · TransferFromSpec 71 s (2935 MB)
  Approve 3 s · TransferFrom 3 s
```

#print axioms (lake env lean on a file importing Nested.All, exit 0):

```
'SolidCore.Spec.UniswapV2.ERC20.Nested.approve_tree_eval' depends on axioms: [propext, Quot.sound]
'SolidCore.Spec.UniswapV2.ERC20.Nested.approve_frame' depends on axioms: [propext]
'SolidCore.Spec.UniswapV2.ERC20.Nested.approve_meets' depends on axioms: [propext, Classical.choice, Quot.sound]
'SolidCore.Spec.UniswapV2.ERC20.Nested.approve_keys' depends on axioms: [propext, Quot.sound]
'SolidCore.Spec.UniswapV2.ERC20.Nested.approve_source_to_mir' depends on axioms: [propext, Classical.choice, Quot.sound]
'SolidCore.Spec.UniswapV2.ERC20.Nested.approve_defined' depends on axioms: [propext, Classical.choice, Quot.sound]
'SolidCore.Spec.UniswapV2.ERC20.Nested.transferFrom_tree_eq' depends on axioms: [propext]
'SolidCore.Spec.UniswapV2.ERC20.Nested.transferFrom_tree_eval' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'SolidCore.Spec.UniswapV2.ERC20.Nested.transferFrom_meets' depends on axioms: [propext, Classical.choice, Quot.sound]
'SolidCore.Spec.UniswapV2.ERC20.Nested.transferFrom_keys' depends on axioms: [propext, Classical.choice, Quot.sound]
'SolidCore.Spec.UniswapV2.ERC20.Nested.transferFrom_self' depends on axioms: [propext, Classical.choice, Quot.sound]
'SolidCore.Spec.UniswapV2.ERC20.Nested.transferFrom_self_max' depends on axioms: [propext, Classical.choice, Quot.sound]
'SolidCore.Spec.UniswapV2.ERC20.Nested.transferFrom_self_short' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'SolidCore.Spec.UniswapV2.ERC20.Nested.transferFrom_source_to_mir' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'SolidCore.Spec.UniswapV2.ERC20.Nested.transferFrom_defined' depends on axioms: [propext, Classical.choice, Quot.sound]
'SolidCore.Spec.UniswapV2.ERC20.Nested.rejects_approve_no_write' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'SolidCore.Spec.UniswapV2.ERC20.Nested.rejects_approve_wrong_slot' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'SolidCore.Spec.UniswapV2.ERC20.Nested.rejects_transferFrom_no_spend' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'SolidCore.Spec.HashScopeNested.transferFrom_scoped_witness' depends on axioms: [propext, Quot.sound]
'SolidCore.Spec.HashScopeNested.not_scoped_collision' depends on axioms: [propext]
'SolidCore.Spec.HashScopeNested.transferFrom_slots' depends on axioms: [propext, Classical.choice, Quot.sound]
'SolidCore.Spec.HashScopeNested.approve_slot' depends on axioms: [propext, Quot.sound]
MAXRSS_MB 2476 WALL_S 3 EXIT 0
```

No sorry, native_decide, bv_decide, ofReduceBool, axiom or extern in the lane's files (grep).

## Next (blocking CERTIFIED)

E4: stage certificates stage0 -> sched -> evm_n for this solar build (certify.py), scoped to the
approve and transferFrom selectors. E5: the context checker on the 1183-byte runtime, with
StaticRunner/CalleesRun discharged for calls that never reach the STATICCALL (generalizing 9fb89ee's
AssembleNoCall). Then E7 composes `approve_meets`/`transferFrom_meets` with them through
`Shapes.functional_ctx`, and E8 needs a gas bound. Both are shared with the transfer slice's lanes.

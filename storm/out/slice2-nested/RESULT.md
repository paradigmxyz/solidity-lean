# slice2-nested: UniswapV2ERC20 approve and transferFrom (checkpoint 1)

Base: solidity-lean 9fb89ee (alpharush/certified-translation). Commits b5cf9ba on top (bundle
sl-slice2-nested.bundle, range 9fb89ee..work/slice2-nested; same as sl-patches/0001-0002).
solar used for stage0: 38b5232ad (alpharush/certified), `-Ogas --evm-version osaka`.
Pinned source: scripts/verify/uniswap-v2/UniswapV2ERC20.sol as uniswap_v2_gen.sh writes it,
sha256 14da00cdeaf2ab3709d2d9838be2c2a144502b32b874b55394d7a8792deac80b. Runtime bytes of that run:
1183 bytes, sha256 ca4c19254b2852f3b0642e24002c616a048c6f343671324c7ae81a4cad971a0b
(-Zemit-lean-stages checked not to change them).

No GPL-derived file is in the patches: Trees.lean (the erased trees) and Certified/uv2_erc20/
(stage0, runtime.hex) are generated at build and gitignored.

## Edge status

| Edge | approve | transferFrom |
|---|---|---|
| E1 frontend | TRUSTED (stated; shared with transfer) | same |
| E3 source -> MIR stage0 | **PROVED** `approve_source_to_mir`, `approve_defined` | **PROVED** `transferFrom_source_to_mir`, `transferFrom_defined` |
| Spec (source level) | **PROVED** `approve_meets` (exact sequential result, no hash premise), `approve_keys` (key-level, scoped premise) | spec stated (`transferFromResult`), tree proof NOT YET |
| E4 stage0 -> EVM IR | MISSING: no stage certificates for this solar build (the earlier uv2_erc20 milestone is for an older 2187-byte build and is not in the tree) | same |
| E5 bytes | MISSING here; 9fb89ee's AssembleNoCall (call-free runner premises) does not apply: the runtime has permit's STATICCALL | same |
| E6, E7, E8 | MISSING (depend on E4/E5) | same |

Status: NOT CERTIFIED. Blocking edges by name: E4, E5, E6, E7 (transfer to bytes), E8; for
transferFrom also its tree spec.

## Theorems (namespace SolidCore.Spec.UniswapV2.ERC20.Nested unless noted)

- `approve_tree_eval spender value st (hs : spender < 2^256) (hv : value < 2^256) :
  (approve_tree.eval ⟨[spender, value], st, solHash⟩).obs = approveResult st spender value`
- `approveResult st spender value`: dirty spender (>= 2^160) reverts with no data, no change; else
  success, output word 1, log `([approvalTopic, caller, spender], word32 value)`,
  storage `upd st (solHash spender (solHash caller 2)) value`.
- `approve_frame`: every slot n with `n % 2^256 ≠ allowanceSlot caller spender` unchanged. Stated over
  slots; no "all other keys" quantifier, no premise.
- `approve_meets (hc : contract? = .ok c) : Meets (solidCore fuel) c ApproveValid ApprovePost`
  (ApprovePost: obs = approveResult of the call's storage and argument words). No premise.
- `approve_keys (hsp : spender < 2^160) (h : HashScopeNested.Scoped (approveFootprint caller spender))`:
  success, allowance slot = value, every slot k < 2^128 (totalSupply 0, DOMAIN_SEPARATOR 3) unchanged.
- `check_approve_ok`, `check_transferFrom_ok`: `Generic.check fuel 200 c.core stage0 [fn] .all = true`
  (kernel_rfl from the source text).
- `approve_source_to_mir o (ho : Generic.SourceEnvOk o) hc : Stage (solidCore fuel) (moduleSem o) c stage0
  (fun call => ∃ σ, Covers deployed σ ∧ fullScope [fn_approve] σ call)`; likewise transferFrom.
- `approve_defined`, `transferFrom_defined`: `Defined (solidCore fuel) c …` (termination by the checker).

## Exact premises

Verify/Spec/HashScopeNested.lean (namespace SolidCore.Spec.HashScopeNested):

```lean
abbrev Scoped (L : List (List Nat)) : Prop := ScopedSep L
-- hash-scope's Verify/Spec/HashScope.lean (27a02d4):
-- def ScopedSep (L : List (List Nat)) : Prop := TrustedBase.KeccakSeparated (· ∈ L)
-- KeccakSeparated S := (∀ x y, S x → S y → keccakWord x = keccakWord y → x = y) ∧ ∀ x, S x → 2^128 ≤ keccakWord x
def nestedFootprint (n o s : Nat) : List (List Nat) := [pre o n, pre s (solHash o n)]
def approveFootprint (caller spender : Nat) := nestedFootprint 2 caller spender
def transferFromFootprint (caller frm dst : Nat) := nestedFootprint 2 frm caller ++ [pre frm 1, pre dst 1]
```

Premise names coordinated with hash-scope: `Scoped` is their `ScopedSep`, one premise for single and
nested maps; this module adds only the nested footprints. Satisfiable on a concrete nontrivial
footprint with the real keccak256 (`transferFrom_scoped_witness : Scoped (transferFromFootprint 0x2000 1 2)`,
four images by decide +kernel) and not trivial (`not_scoped_collision : ¬ Scoped [[0], [256]]`).
Slot lemmas: `slot_ge`, `slot_ne`, `nested_ne_flat`, `transferFrom_slots`, `approve_slot`.
E3 theorems take only `Generic.SourceEnvOk o` (oracle caller and two-word keccak agree with SolidCore's).

Gap shared with transfer: the caller is the stage's (0x2000); SolarTV.Call has no caller field, so
"any caller" needs a change to the shared call model.

## Build receipts (LEAN_NUM_THREADS=1, 14 GB Hand)

```
scripts/verify/uniswap_v2_gen.sh                                         exit 0
SOLAR=solar(38b5232ad) scripts/verify/uniswap_v2_stage0.sh               exit 0
lake build Contracts.UniswapV2.ERC20.Core Contracts.UniswapV2.ERC20.SpecTreeKeccak  exit 0
python3 scripts/verify/uniswap_v2_trees.py                               exit 0
lake build -KleanMemory=6000 Verify.Spec.HashScope Verify.Spec.HashScopeNested
                                                     exit 0, peak RSS 3318 MB, 60 s
lake build -KleanMemory=6000 ContractsUniswapV2ERC20Nested (clean, all 7 modules)
                                                     exit 0, peak RSS 5890 MB, 124 s
  Trees 71 s; LoweringApprove 18 s (5133 MB alone); LoweringTransferFrom 23 s (5609 MB alone);
  Approve 2.8 s (2482 MB alone)
```

#print axioms (lake env lean on a file importing Nested.All, exit 0):

```
'SolidCore.Spec.UniswapV2.ERC20.Nested.approve_tree_eval' depends on axioms: [propext, Quot.sound]
'SolidCore.Spec.UniswapV2.ERC20.Nested.approve_frame' depends on axioms: [propext]
'SolidCore.Spec.UniswapV2.ERC20.Nested.approve_meets' depends on axioms: [propext, Classical.choice, Quot.sound]
'SolidCore.Spec.UniswapV2.ERC20.Nested.approve_keys' depends on axioms: [propext, Quot.sound]
'SolidCore.Spec.UniswapV2.ERC20.Nested.check_approve_ok' depends on axioms: [propext, Classical.choice, Quot.sound]
'SolidCore.Spec.UniswapV2.ERC20.Nested.approve_source_to_mir' depends on axioms: [propext, Classical.choice, Quot.sound]
'SolidCore.Spec.UniswapV2.ERC20.Nested.approve_defined' depends on axioms: [propext, Classical.choice, Quot.sound]
'SolidCore.Spec.UniswapV2.ERC20.Nested.check_transferFrom_ok' depends on axioms: [propext, Classical.choice, Quot.sound]
'SolidCore.Spec.UniswapV2.ERC20.Nested.transferFrom_source_to_mir' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'SolidCore.Spec.UniswapV2.ERC20.Nested.transferFrom_defined' depends on axioms: [propext, Classical.choice, Quot.sound]
'SolidCore.Spec.HashScopeNested.transferFrom_scoped_witness' depends on axioms: [propext, Quot.sound]
'SolidCore.Spec.HashScopeNested.not_scoped_collision' depends on axioms: [propext]
'SolidCore.Spec.HashScopeNested.transferFrom_slots' depends on axioms: [propext, Classical.choice, Quot.sound]
'SolidCore.Spec.HashScopeNested.approve_slot' depends on axioms: [propext, Quot.sound]
MAXRSS_MB 2467 WALL_S 3 EXIT 0
```

No sorry, native_decide, bv_decide, ofReduceBool, axiom or extern in the lane's files (grep).

## Next

transferFrom's tree proof (`transferFrom_tree_eval` against `transferFromResult`, then
`transferFrom_meets`, `transferFrom_keys` with self-transfer and infinite-allowance cases); negative
controls by execution (spec mutant; stage0 with the allowance write dropped refused by Generic.check).
E4/E5 need stage certificates and the context checker for this solar build (shared with transfer's lanes).

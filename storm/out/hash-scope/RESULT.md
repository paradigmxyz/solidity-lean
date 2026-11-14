# hash-scope: keccak256 separation scoped to a call's footprint

Branch: solidity-lean `hash-scope`, one commit **1b75749** on top of PR head **a1c3143**
(`alpharush/certified-translation`). Delivered as `sl-hash-scope.bundle` (range a1c3143..hash-scope) and
`patches/0001-*.patch`. No solar changes in this delivery (see "Missing").

Apply: `git fetch storm/out/hash-scope/sl-hash-scope.bundle hash-scope && git checkout FETCH_HEAD` (or `git am patches/*.patch` on a1c3143).

## The premise (exact Lean text, Verify/Spec/HashScope.lean)

```lean
-- Verify/Spec/TrustedBase/Hypotheses.lean (unchanged, already on the PR)
def KeccakSeparated (S : Preimages) : Prop :=
  (∀ x y, S x → S y → keccakWord x = keccakWord y → x = y) ∧ ∀ x, S x → 2 ^ 128 ≤ keccakWord x

-- Verify/Spec/HashScope.lean (new), namespace SolidCore.Spec
def ScopedSep (L : List (List Nat)) : Prop := TrustedBase.KeccakSeparated (· ∈ L)

def transferFootprint (m caller recipient : Nat) : List (List Nat) :=
  [mappingPreimage caller m, mappingPreimage recipient m]
```

For UniswapV2ERC20.transfer the premise is `ScopedSep (transferFootprint 1 caller to)` (balanceOf at slot 1);
for Token it is `ScopedSep (transferFootprint 0 caller to)`. It says keccak256 is injective, with images at least
2^128, on exactly those two preimages. It says nothing about any other key: no frame family, no "all addresses" clause.
The frame CERTIFICATION_TARGET (a1c3143) asks for ("every slot outside the call's footprint unchanged") is a statement
about slots, so it needs no further hash premise.

## Satisfiability (in Lean, no hypothesis)

| theorem | statement | axioms |
|---|---|---|
| `exists_separatedBy` | `∀ L, ∃ h, SeparatedBy h L` with `h x := 2^128 + L.idxOf x`: every finite footprint has a model | propext, Classical.choice, Quot.sound (via Mathlib/List lemmas) |
| `scopedSep_iff` | `ScopedSep L ↔ SeparatedBy keccakWord L` (the premise is the model statement at the real hash) | — |
| `scopedSep_transfer_example` | `ScopedSep (transferFootprint 1 0x2000 1)`: the **real keccak256** meets UniswapV2ERC20 transfer's footprint for caller 0x2000, to 1 (kernel evaluation of the sponge, TrustedBase.image4/image5) | **propext only** (#guard_msgs) |
| `transferFP_real` (Contracts/Token/HashScope.lean) | real keccak256 meets Token transfer(1, ·)'s footprint from caller 0x2000 (image1/image2) | propext, Classical.choice, Quot.sound |

`SeparatedBy`:
```lean
def SeparatedBy (h : List Nat → Nat) (L : List (List Nat)) : Prop :=
  (∀ x ∈ L, ∀ y ∈ L, h x = h y → x = y) ∧ ∀ x ∈ L, 2 ^ 128 ≤ h x
```

## Slot lemmas re-derived from the scoped premise

- `scoped_inj (h : ScopedSep L) … (hx : mappingPreimage a m ∈ L) (hy : mappingPreimage b n ∈ L) (he : solHash a m = solHash b n) : a = b ∧ m = n`
- `scoped_ge (h : ScopedSep L) (hx : mappingPreimage a m ∈ L) : 2 ^ 128 ≤ solHash a m`
- `transfer_slots (h : ScopedSep (transferFootprint m c t)) … : (c ≠ t → solHash c m ≠ solHash t m) ∧ 2^128 ≤ solHash c m ∧ 2^128 ≤ solHash t m`
  — exactly the facts the sequential transfer post needs (distinct slots when caller ≠ to; neither aliases a small fixed slot such as totalSupply).

Both lemmas need both keys in the footprint; nothing is derivable about a key outside it.

## Nested separation is false (pigeonhole)

- `not_nestedSlotsSeparated (hn : n ∈ ns) (hnw : n < 2^256) : ¬ NestedSlotsSeparated ms ns` — 2^160×2^160 nested keys into 2^256 slots (Fintype.card_le_of_injective).
- `not_nestedSlotsSeparated_erc20 : ¬ NestedSlotsSeparated [1, 4] [2]` — the ERC20 instance. Axioms: propext, Classical.choice, Quot.sound (#guard_msgs).

So any nested (allowance) statement must also be footprint-scoped.

## Negative control

`collide_refuted : ¬ TreeMeetsFixedOn (fun ρ => TransferFP ρ.args) TokenSpecCollide.Token collideSpec ctx 2 transferTree`
where `TransferFP args := ScopedSep (transferFootprint 0 8192 (args.getD 0 0 % 2^160))` and the collision spec
(scripts/verify/keccak/TokenSpecCollide.sol, `balanceOf[to] == old(balanceOf[msg.sender]) + amount`) holds only if the two slots
coincide. Proven from `collide_not_meets_scoped` + `transferFP_real`: no premise left. Axioms: propext, Classical.choice, Quot.sound.

## Answer to slice2-nested

My single-level premise is exactly `SolidCore.Spec.ScopedSep L := TrustedBase.KeccakSeparated (· ∈ L)`, the same shape as your
`HashScope.Scoped L`; the transfer footprint is `transferFootprint m caller recipient := [mappingPreimage caller m, mappingPreimage recipient m]`.
Either name can be an abbrev of the other (`abbrev Scoped := ScopedSep`); `scoped_inj`/`scoped_ge` work for any L, so your
nested footprints (mappingPreimage a m plus the inner preimages) reuse them for the outer level. `exists_separatedBy` gives you
satisfiability for any footprint list for free.

## Build receipts (hosted Hand, Lean 4.35.0, Mathlib cache)

```
export PATH=$HOME/.elan/bin:$PATH LEAN_NUM_THREADS=1
lake build -KleanMemory=5000 Verify.Spec.HashScope Contracts.Token.HashScope
# Build completed successfully (2585 jobs).  EXIT=0   (at 1b75749, rebased on a1c3143)
grep -rn 'sorry\|native_decide' Verify/Spec/HashScope.lean Contracts/Token/HashScope.lean   # no matches
```
Axiom checks are `#guard_msgs in #print axioms …` in the files, so the build fails if any changes.

## Changed from the earlier attempt

- Dropped the global/all-address forms for the certification statement: the earlier `HashScope L F` / `MapScope` (with an `apart` clause
  over every address's slot, `mapFamily`) remain in the file only as legacy for the old Token tactic and are **not** to be used in
  the statement: that clause is the "all other keys" form a1c3143 rules out.
- Token's legacy exported transfer spec frames balanceOf at every other address, so it is not proved under ScopedSep; the
  earlier `transfer_meets_scoped` was removed. The a1c3143 sequential post (debit, then credit reading the debited state; slot frame)
  is what should be proved, with `transfer_slots` as its hash input.
- Superseded global KeccakModel attempt is preserved in `wip/`.

## Missing (not done here)

- The UniswapV2ERC20.transfer theorem itself under `ScopedSep (transferFootprint 1 caller to)` with the a1c3143 post and the required
  concrete cases (2^256-1 self-transfer succeeds unchanged with Transfer; self-transfer with balance < value reverts). The hash side is ready (`transfer_slots`).
- Driver printing: solar `check_final` at 38b5232 does not yet print the premise; proposal: print the line
  `PREMISE ScopedSep (transferFootprint 1 caller to)` from the statement's hypothesis list, and refuse any keccak premise not of the form `ScopedSep <footprint>`.
  The earlier WIP solar bundle in `wip/` has the printing/refusal code for the old model premise to port.
- Archon CLI segfaults on this Hand; not used.

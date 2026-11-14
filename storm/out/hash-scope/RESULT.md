# hash-scope (round 2): nested footprints and the kernel check

Branch `hash-scope2`: one commit **4808f3e** on PR head **9fb89ee** (`alpharush/certified-translation`, which already holds round 1's
ScopedSep). Delivered as `sl-hash-scope-nested.bundle` (range 9fb89ee..4808f3e) and `patches/0001-*.patch`.
Files: `Verify/Spec/HashScopeCheck.lean` (new, added to the `VerifySpec` roots so CI builds it),
`scripts/verify/keccak/footprint_check.sh` (new). Round 1's bundle/patch (`sl-hash-scope.bundle`, merged at 9fb89ee) is kept beside it.

Apply: `git fetch storm/out/hash-scope/sl-hash-scope-nested.bundle HEAD && git checkout FETCH_HEAD`, or `git am patches/0001-feat-spec-kernel-check*.patch` on 9fb89ee.

## Exact definitions (Verify/Spec/HashScopeCheck.lean, namespace SolidCore.Spec)

```lean
-- unchanged from 9fb89ee (Verify/Spec/HashScope.lean)
def ScopedSep (L : List (List Nat)) : Prop := TrustedBase.KeccakSeparated (· ∈ L)
def transferFootprint (m caller recipient : Nat) : List (List Nat) :=
  [mappingPreimage caller m, mappingPreimage recipient m]
def SeparatedBy (h : List Nat → Nat) (L : List (List Nat)) : Prop :=
  (∀ x ∈ L, ∀ y ∈ L, h x = h y → x = y) ∧ ∀ x ∈ L, 2 ^ 128 ≤ h x

-- new
def sepCheckBy (h : List Nat → Nat) (L : List (List Nat)) : Bool :=
  let P := L.map fun x => (x, h x)
  P.all (fun p => decide (2 ^ 128 ≤ p.2)) && P.all fun p => P.all fun q => decide (p.2 = q.2 → p.1 = q.1)

def approveFootprintBy (h : List Nat → Nat) (a caller spender : Nat) : List (List Nat) :=
  [mappingPreimage caller a, mappingPreimage spender (h (mappingPreimage caller a))]
def transferFromFootprintBy (h : List Nat → Nat) (b a src dst caller : Nat) : List (List Nat) :=
  [mappingPreimage src b, mappingPreimage dst b, mappingPreimage src a,
    mappingPreimage caller (h (mappingPreimage src a))]
abbrev approveFootprint (a caller spender : Nat) := approveFootprintBy keccakWord a caller spender
abbrev transferFromFootprint (b a src dst caller : Nat) := transferFromFootprintBy keccakWord b a src dst caller

def UniversalTransferSep (m : Nat) : Prop :=
  ∀ c t, c < 2 ^ 160 → t < 2 ^ 160 → ScopedSep (transferFootprint m c t)
```

The nested footprint names the outer preimage `owner . a` and the inner `spender . H(owner . a)`, with the inner key computed by the
same hash `H`: `nested_slot_eq` proves SolidCore's `solHash k2 (solHash k1 a)` is exactly the inner preimage's keccak. At most four
preimages per call, so the pigeonhole refutation of the global nested premise (`not_nestedSlotsSeparated`) does not apply.

## Three kinds of claim, kept apart

| kind | theorem | statement | axioms |
|---|---|---|---|
| check ⇔ premise | `separatedBy_iff_check` | `SeparatedBy h L ↔ sepCheckBy h L = true` for any h | not printed separately (scopedSep_iff_check, below, depends on it) |
| | `scopedSep_iff_check` | `ScopedSep L ↔ sepCheckBy keccakWord L = true`; hence `instance : Decidable (ScopedSep L)` | propext, Quot.sound |
| | `scopedSep_of_check` | `sepCheckBy keccakWord L = true → ScopedSep L` — the driver's entry point | propext, Quot.sound |
| **1. abstract model** | `approve_model a c s` | `∃ h, (∀ x, h x < 2^256) ∧ SeparatedBy h (approveFootprintBy h a c s)` (word-valued, inner key by the model itself) | propext, Classical.choice, Quot.sound |
| | `transferFrom_model b a f t c` | same for `transferFromFootprintBy h b a f t c` | propext, Classical.choice, Quot.sound |
| **2. real witness** (kernel keccak) | `real_transfer_AB` | `ScopedSep (transferFootprint 1 addrA addrB)` | propext, Quot.sound |
| | `real_transfer_AA` | self-transfer footprint | propext, Quot.sound |
| | `real_approve_AB` | `ScopedSep (approveFootprint 2 addrA addrB)` | propext, Quot.sound |
| | `real_transferFrom_ABC` | `ScopedSep (transferFromFootprint 1 2 addrA addrB addrC)` | propext, Quot.sound |
| **3. universal** (NOT proved, NOT assumed) | `universalTransferSep_iff` | `UniversalTransferSep m ↔ KeccakSeparated (fun x => ∃ k < 2^160, x = mappingPreimage k m)`: the all-pairs claim is keccak separation on all 2^160 balance preimages, a global computational claim | propext |

(addrA/B/C are three arbitrary 160-bit addresses; slots 1 and 2 are UniswapV2ERC20's balanceOf and allowance.) "Holds for real keccak on
any concrete pair" is delivered as: decidable (`scopedSep_iff_check`), sound (`scopedSep_of_check`), and run per pair by the kernel — not as a
∀-pairs theorem, which would be claim 3.

## Slot lemmas for the nested calls

```lean
theorem approve_slots {a c s : Nat} (h : ScopedSep (approveFootprint a c s)) :
    2 ^ 128 ≤ solHash c a ∧ 2 ^ 128 ≤ solHash s (solHash c a)
theorem transferFrom_slots {b a f t c : Nat} (h : ScopedSep (transferFromFootprint b a f t c))
    (hb : b < 2 ^ 128) (ha : a < 2 ^ 256) (hf : f < 2 ^ 256) (ht : t < 2 ^ 256) (hc : c < 2 ^ 256) :
    (f ≠ t → solHash f b ≠ solHash t b) ∧ solHash c (solHash f a) ≠ solHash f b ∧
      solHash c (solHash f a) ≠ solHash t b ∧ 2 ^ 128 ≤ solHash f b ∧ 2 ^ 128 ≤ solHash t b ∧
      2 ^ 128 ≤ solHash c (solHash f a)
```
The allowance slot differs from both balance slots for every choice of addresses (including f = t = c): its inner key is a hash ≥ 2^128, the
balance mapping slot b is small. Axioms: approve_slots [propext, Quot.sound]; transferFrom_slots [propext, Classical.choice, Quot.sound].

## Negative controls (refused by execution, kernel `decide +kernel`)

- `check_refuses_constant`: `sepCheckBy (fun _ => 2^128) (transferFootprint 1 addrA addrB) = false` (collision).
- `check_refuses_truncated`: `sepCheckBy (fun x => keccakWord x % 2^128) … = false` (image in the small slots).
- `check_refuses_length_hash`: a hash colliding on the nested `transferFromFootprintBy` footprint is refused.
- Driver input refusals (exit 2, below).

## Driver check (scripts/verify/keccak/footprint_check.sh)

`footprint_check.sh transfer <balSlot> <caller> <to>` | `approve <allowSlot> <caller> <spender>` | `transferFrom <balSlot> <allowSlot> <src> <dst> <caller>`.
Validates slots < 2^128 and addresses < 2^160, prints `PREMISE ScopedSep (<footprint>)`, proves it in a fresh Lean file by
`scopedSep_of_check (by decide +kernel)`, audits `#print axioms` (only propext/Classical.choice/Quot.sound), exits 0 / 1 (check or axiom
audit failed) / 2 (malformed input). Runs (each a separate process, RECEIPT from a getrusage wrapper):

```
transfer 1 0x5B38…ddC4 0xAb84…5cb2            exit=0  10.9 s  peak 3275 MB  axioms [propext, Quot.sound]
transfer 1 0xff…ff 0xff…ff (max address, self) exit=0   7.9 s  peak 2862 MB
transfer 0 0x0 0x1                             exit=0  11.2 s  peak 3274 MB
approve 2 0xCA35…733c 0x1472…160C             exit=0  10.7 s  peak 3276 MB
transferFrom 1 2 A A A (all equal)             exit=0  14.3 s  peak 3692 MB
transfer 1 0x1000…0 (2^160) 0x1               exit=2  REFUSED out of range (2^160)
transfer 1 0xzz 0x1                            exit=2  REFUSED not a number
approve 2 0x1                                  exit=2  REFUSED wrong arity
mint 1 2 3                                     exit=2  REFUSED unknown call kind
```
Not exercised: the exit-1 path on real keccak (no concrete collision exists to feed it); the check's refusal is shown in Lean by the three
negative controls above, at model hashes.

## Build receipts (hosted Hand, Lean 4.35.0, LEAN_NUM_THREADS=1)

```
python3 ~/bin/peak.py lake build -KleanMemory=5000 Verify.Spec.HashScopeCheck
  -> Build completed; RECEIPT exit=0 wall_s=39.8 peak_rss_mb=4155   (fresh compile of HashScopeCheck, at 4808f3e)
python3 ~/bin/peak.py lake build -KleanMemory=5000 VerifySpec Verify.Spec.HashScope Contracts.Token.HashScope
  -> Build completed successfully (2589 jobs); RECEIPT exit=0 (cached after the above)
grep -rn 'sorry\|native_decide' Verify/Spec/HashScopeCheck.lean scripts/verify/keccak/footprint_check.sh   -> no matches (exit 1)
```
`~/bin/peak.py` runs the command and reports `getrusage(RUSAGE_CHILDREN).ru_maxrss` (largest child, i.e. the lean process).
Every theorem in the table has a `#guard_msgs in #print axioms` block at the end of the file, so a changed axiom set fails the build.

## Not done / next

- The UniswapV2ERC20 transfer/approve/transferFrom theorems under these premises (the hash side they need is `transfer_slots`,
  `approve_slots`, `transferFrom_slots`).
- Solar driver wiring: `check_final` should call `footprint_check.sh` (or emit the same theorem) for the concrete call of a
  certification run and print the PREMISE line; not changed in solar.
- If slice2-nested lands `HashScope.Scoped`/`approveFootprint` of its own, it should become an abbrev of these (same shape:
  `Scoped L = ScopedSep L` definitionally).

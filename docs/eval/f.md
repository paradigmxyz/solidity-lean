# Lane F: library equivalences

Small checked bridges from repo-local definitions to Lean core operations, so proofs can use core
lemmas and simprocs instead of unfolding. Core only (no Mathlib imports). Every file is checked
with `scripts/eval/check.sh F <file>` (receipts in `~/eval-receipts.jsonl`, logs in `~/eval-logs/`).
Each "new" file holds the bridge proofs *and* the fixture, so its cost includes proving the bridge.
"Old" files hold the same fixture statement proved (or attempted) the current way.

## 1. Exponentiation

**SolarTV (EVM EXP, wrapping).** `Verify/Eval/F/Power.lean`
- `power_eq_ofNat_powMod : power b e = BitVec.ofNat w (Nat.powMod b.toNat e (2^w))`
- `power_toNat : (power b e).toNat = Nat.powMod b.toNat e (2^w)`, `power_toNat_pow` (`= b.toNat^e % 2^w`)
- `binary_exp` for MIR's `binary .exp`
- Axioms: `[propext, Quot.sound]`.
- EXP has no overflow check (EVM wraps); nothing in tv relies on one.
- Fixture `power (3#256) (2^255+12345) = <literal>`. New: `rw [power_eq_ofNat_powMod]; simp only [..., Nat.reducePowMod]`.
  Old (`PowerOld.lean`): `simp [power]` fails at the default `maxRecDepth`. With `maxRecDepth 100000`
  it passes (simp 150 ms, kernel 502 ms). New total for the file, bridge included: simp 21 ms, kernel 55 ms.
  `decide` cannot run either form, because the kernel does not reduce the well-founded `power` or `Nat.powMod`.
  Use the simproc for this.
- Copy: Power.lean re-proves `SolarTV.Word.power_eq_pow` (tv/SolarTV/WordSafety.lean:19) verbatim as
  `power_eq_pow'`, because `SolarTV.WordSafety` has no shared .olean. Drop the copy once it is built.

**SolidCore checked `**` (Solidity, panics 0x11).** `Verify/Eval/F/CheckedExp.lean`
- `expBySquaring_eq`: for a multiplication that reduces both factors, the 257-fuel loop equals `g (acc * b^e)`.
- `natPowMod_eq_powMod` (`= Nat.powMod`) and `natPowCapped_eq` (`= min (b^e) cap`), for `e < 2^257`.
- `checkedExp_eq`: `checkedExp c b e = if c && 2^256 ≤ b'^e' then .error overflow else .ok (Nat.powMod b' e' 2^256)`.
  The panic point is now stated on the true power, so the checked semantics is kept exactly.
- `checkedExp_unchecked`: the unchecked result is `(BitVec.ofNat 256 b ^ e').toNat`, which links to SolarTV via `power_eq_pow`.
- Axioms: `[propext, Classical.choice, Quot.sound]`.
- Fixtures: `checkedExp c 1 e = .ok 1` for a symbolic `e`; `b**2` for `b < 2^128`; overflow of `3**e` for every `e ≥ 256`
  (proved by monotonicity, without evaluating anything). New file: wall 2.24 s, exit 0.
  Old (`CheckedExpOld.lean`): unfolding into `expBySquaring` hits the 200000-heartbeat limit after
  11.4 s of simp (wall 13.5 s). The file checks this with `#guard_msgs` on an `example`, so it exits 0 and adds no `sorryAx`. Concrete exponents already worked before (structural fuel, `decide` with a raised
  recDepth in about 30 ms), so the win is in symbolic proofs.

## 2. Storage writes. `Verify/Eval/F/Storage.lean`
- `write s slot v` is the lambda `wp_sstore` produces, by `rfl`. Supporting lemmas: `sstore_eq_write`,
  `wp_sstore_write` and `lam_eq_write`.
- Laws:
  - reading: `write_apply_self` (simp, grind), `write_apply_same`, `write_apply_other` (simp), `write_apply` (grind)
  - writing: `write_write_same`, `write_write_self` (simp), `write_comm`, `write_write_write_same`
  - `write_comm_lt` (simp): a sorted normal form for concrete slots
  - Slots are compared mod 2^256.
- Axioms: `[propext, Quot.sound]`. The fixtures add `Classical.choice`.
- Fixture family: N = 16/32/64 `sstore`s cycling over slots 0..3; the final storage equals four writes.
  - New: `simp only [progN, wp_bind, wp_sstore_write]; simp`. File wall 2.91 s, simp 855 ms, kernel 74 ms.
  - Old (`StorageOld.lean`): `wp_sstore`, then `funext k; simp only [write]; split_ifs <;> rfl`.
    File wall 5.19 s, simp 3.59 s, kernel 209 ms.
  - So simp time drops about 4.2x and kernel time about 2.8x across the family, and the proof needs no
    `funext` or case split.

## 3. clz. `Verify/Eval/F/Clz.lean`
- `clzWord_eq_clz : clzWord v = (BitVec.ofNat 256 v).clz.toNat`, `clzWord_toNat` for BitVec inputs.
- Zero case: `clzWord_eq_256_iff : clzWord v = 256 ↔ v % 2^256 = 0` and `clzWord_zero`. Bound: `clzWord_le`.
- Axioms: `[propext, Quot.sound]`.
- Fixtures: `clzWord_le` and `fixture_clz_top` (top bit set gives 0) use core's `clz_le` / `clz_eq_zero_iff`.
  New file: wall 2.07 s, simp 69 ms.
  Old (`ClzOld.lean`): unfolding the 256-step scan for `clzWord v ≤ 256` makes `split_ifs`/`simp` exceed
  maxSteps (simp 3.4 s, wall 5.7 s). The file asserts this with `fail_if_success` in an `example`, so it exits 0 and adds no `sorryAx`. A concrete `clzWord (2^200+7) = 55` works by `decide` both ways.

## Where the bridges could be used (files not edited)
- tv/SolarTV/EVMIR/Ops.lean:39 and tv/W1Proofs/Tactic.lean:433 (`EVM.step .exp` = `Word.power`); tv/SolarTV/Word.lean:32 (`binary .exp`).
- tv/SolarTV/Agreement/Tactic.lean:78: a duplicate `toNat_pow`. Its :85 `exp_power_of_two` could start from `power_toNat_pow`.
- SolidCore/Solidity/Interpreter.lean:6703 `checkedExp` and :6784 `checkedSignedExp` (same `natPowMod`/`natPowCapped`).
  Dispatched at :6827, with witnesses at SolidCore/Witness/Checked.lean:8648-8659.
- Verify/Basic.lean:87/97: `sstore`/`wp_sstore` could state `write` directly.
  - Verify/Tactic.lean:105 (the VC simp set) could add `wp_sstore_write` + `write_*` in place of `wp_sstore`.
  - Verify/CounterBump.lean:76: the frame step `simp only [Nat.zero_mod, hk, ite_false]` becomes `write_apply_other`.
- SolidCore/Solidity/Shared/Word.lean:145 `clzWord`: there are no callers today. The bridge ties it to SolarTV's
  `unary .clz` (tv/SolarTV/Word.lean:42, `BitVec.clz`) and to EVMIR/Ops.lean:51 for refinement.
- `powModWordAux` (Shared/Word.lean:56) is unused and could be replaced by `Nat.powMod`.

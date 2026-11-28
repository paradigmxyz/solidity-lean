import Verify.Gas.FixedFuel.Counted
import W1Proofs.Tactic

/-!
# A loop's `Loops` over the final EVM IR, from a measure of its header stack

`Counted.loops_of` covers one layout of a counted loop in the final EVM IR: the header tests a
counter word directly and the body steps it by one up to zero. The loops the source erasure
(`eraseLoopStmt`) accepts reach the final EVM IR in more layouts, depending on how the backend
rewrote `for (i = s; i < n; i++)`:

* a counter word stepped by one up to zero and tested at the header (`down k`, as in `Counted`),
  entered as `0 - n` for a limit `n`: a call argument, a storage word or a literal;
* the counter compared with an unchanged limit word, `i < n` (`up k j`);
* a rotated loop, whose test ends the body block: the header is the body, every header stack has
  a nonzero counter (the guard `nonzero k`), and the back edge tests the stepped word.

This module proves `Loops` for each of them from one bridge, generic over the step function. The
record `record` keeps only a flag and the iterations left; the header relation `At` takes the
header block `H`, the stack depth `n`, a guard `G` on header stacks and a measure `μ` of them
(`loops_of`). The obligations are `Counted.loops_of`'s with `G` and `μ` in place of the counter
word: from a header stack with the guard and a nonzero measure, the header again (guard, lower
measure) or a configuration that ends, within `B` blocks; from one of measure zero, an end within
`X` blocks; from the entry, the header (guard, measure at most `M`) or an end within `E` blocks.
The measures, the lemmas a generated proof closes its paths with and `sym_exec_st`, for a block that
reads storage after writing it, follow (`down`, `up`,
`nonzero`, `fit_of`). Nothing here names a contract, a program or a file.
-/

namespace Verify.Gas.FixedFuel.Measured

open SolarTV SolarTV.Machine Verify.LoopSource.Interface
open SolidCore.Refinement.Generic (Val WExpr wordSize)
open Verify.Gas.FixedFuel.Counted (Cfg Reaches val meas)

/-! ## The record -/

/-- The loop's record: valuation word 0 tells the header (1) from an end (0), word 1 is the
iterations left; the condition is that word at the header. -/
def record : LoopRecord where
  H := { scopes := [], writes := [], logs := [] }
  P _ := True
  m σ := if σ.args.getD 0 0 = 0 then 0 else σ.args.getD 1 0
  c := .sel (.arg 0) (.arg 1) (.lit 0)
  bb := .leaf (.normal { scopes := [], writes := [], logs := [] })

theorem m_head (μ : Nat) : record.m (val [1, μ]) = μ := by
  simp [record, val]

theorem m_zero : record.m (val [0]) = 0 := by
  simp [record, val]

theorem c_head {μ : Nat} (h : μ < 2 ^ 256) : record.c.eval (val [1, μ]) = 0 ↔ μ = 0 := by
  simp only [record, val, WExpr.eval, List.getD_cons_zero, List.getD_cons_succ, wordSize,
    Nat.mod_eq_of_lt h]
  simp

theorem c_zero : record.c.eval (val [0]) = 0 := by
  simp [record, val, WExpr.eval]

/-! ## The bridge -/

variable {step : Cfg → Option (Res ⊕ Cfg)}

/-- Where an iteration from header stack `ws` may stop: the header again, with `n` stack words,
the guard and a lower measure, or a configuration that ends within `X` blocks. -/
abbrev IterQ (step : Cfg → Option (Res ⊕ Cfg)) (H n X : Nat) (G : EVM.Stack → Prop)
    (μ : EVM.Stack → Nat) (ws : EVM.Stack) (y : Cfg) : Prop :=
  (∃ ws' s', y = (H, ws', s') ∧ ws'.length = n ∧ G ws' ∧ μ ws' < μ ws) ∨
  ∃ r, iterate step X y = some r

/-- Where the entry may stop: the header, with `n` stack words, the guard and at most `M`
iterations left, or a configuration that ends within `X` blocks. -/
abbrev EntryQ (step : Cfg → Option (Res ⊕ Cfg)) (H n X : Nat) (G : EVM.Stack → Prop)
    (μ : EVM.Stack → Nat) (M : Nat) (y : Cfg) : Prop :=
  (∃ ws s, y = (H, ws, s) ∧ ws.length = n ∧ G ws ∧ μ ws ≤ M) ∨
  ∃ r, iterate step X y = some r

/-- The machine at the loop's header (block `H`, `n` stack words with the guard, valuation `1`
and their measure), or at a configuration that ends within `X` blocks (valuation `0`). -/
def At (step : Cfg → Option (Res ⊕ Cfg)) (H n X : Nat) (G : EVM.Stack → Prop)
    (μ : EVM.Stack → Nat) (σ : Val) (x : Cfg) : Prop :=
  (∃ ws s, x = (H, ws, s) ∧ ws.length = n ∧ G ws ∧ σ = val [1, μ ws]) ∨
  (σ = val [0] ∧ ∃ r, iterate step X x = some r)

/-- **The bridge of a measured loop**, from its iteration and its exit at every header stack. -/
def bridge (H n : Nat) {B X : Nat} (G : EVM.Stack → Prop) (μ : EVM.Stack → Nat)
    (hμ : ∀ ws, μ ws < 2 ^ 256)
    (iter : ∀ ws s, ws.length = n → G ws → μ ws ≠ 0 →
      Reaches step B (H, ws, s) (IterQ step H n X G μ ws))
    (done : ∀ ws s, ws.length = n → G ws → μ ws = 0 → ∃ r, iterate step X (H, ws, s) = some r) :
    Bridge record step B X where
  At := At step H n X G μ
  iter := by
    intro σ x hx _ hc
    rcases hx with ⟨ws, s, rfl, hn, hg, rfl⟩ | ⟨rfl, -⟩
    · have hk : μ ws ≠ 0 := fun h => hc ((c_head (hμ ws)).2 h)
      obtain ⟨y, hw, ⟨ws', s', rfl, hn', hg', hm⟩ | hr⟩ := iter ws s hn hg hk
      · exact ⟨_, _, ⟨trivial, hc, trivial, by rw [m_head, m_head]; exact hm⟩,
          .inl ⟨ws', s', rfl, hn', hg', rfl⟩, hw⟩
      · exact ⟨val [0], y, ⟨trivial, hc, trivial, by rw [m_zero, m_head]; omega⟩,
          .inr ⟨rfl, hr⟩, hw⟩
    · exact absurd c_zero hc
  done := by
    intro σ x hx _ hc
    rcases hx with ⟨ws, s, rfl, hn, hg, rfl⟩ | ⟨-, h⟩
    · exact done ws s hn hg ((c_head (hμ ws)).1 hc)
    · exact h

/-- **`Loops` of a measured loop** from its iteration, its exit and its entry. -/
theorem loops_of {init : Cfg} {H n E B X M : Nat} (G : EVM.Stack → Prop) (μ : EVM.Stack → Nat)
    (hμ : ∀ ws, μ ws < 2 ^ 256)
    (iter : ∀ ws s, ws.length = n → G ws → μ ws ≠ 0 →
      Reaches step B (H, ws, s) (IterQ step H n X G μ ws))
    (done : ∀ ws s, ws.length = n → G ws → μ ws = 0 → ∃ r, iterate step X (H, ws, s) = some r)
    (entry : Reaches step E init (EntryQ step H n X G μ M)) :
    Loops step init record E B X M := by
  obtain ⟨y, hw, ⟨ws, s, rfl, hn, hg, hm⟩ | hr⟩ := entry
  · exact ⟨bridge H n G μ hμ iter done, _, _, hw, .inl ⟨ws, s, rfl, hn, hg, rfl⟩, trivial,
      by rw [m_head]; exact hm⟩
  · exact ⟨bridge H n G μ hμ iter done, val [0], y, hw, .inr ⟨rfl, hr⟩, trivial,
      by rw [m_zero]; exact Nat.zero_le _⟩

/-! ## Guards and measures -/

/-- No guard. -/
abbrev always : EVM.Stack → Prop := fun _ => True

/-- The guard of a rotated loop: header word `k` is nonzero. -/
abbrev nonzero (k : Nat) : EVM.Stack → Prop := fun ws => ¬ws.getD k 0 = 0

/-- Header word `k` steps by one up to zero: the iterations left are its distance to zero. -/
def down (k : Nat) (ws : EVM.Stack) : Nat := meas (ws.getD k 0).toNat

/-- `i < n`, with `i` stepping by one and `n` unchanged: the iterations left are `n - i`. -/
def upM (i n : EvmRules.Word) : Nat := if i < n then n.toNat - i.toNat else 0

/-- Header word `k` steps by one below header word `j`. -/
def up (k j : Nat) (ws : EVM.Stack) : Nat := upM (ws.getD k 0) (ws.getD j 0)

theorem down_lt (k : Nat) (ws : EVM.Stack) : down k ws < 2 ^ 256 :=
  Nat.mod_lt _ (by decide)

theorem up_lt (k j : Nat) (ws : EVM.Stack) : up k j ws < 2 ^ 256 := by
  unfold up upM
  have := (ws.getD j 0).isLt
  split <;> omega

theorem meas_eq_zero {w : EvmRules.Word} : meas w.toNat = 0 ↔ w = 0 := by
  have := w.isLt
  constructor
  · intro h
    apply BitVec.eq_of_toNat_eq
    unfold meas at h
    show w.toNat = 0
    omega
  · rintro rfl
    rfl

/-- A counter word of measure zero is zero. -/
theorem down_zero {w : EvmRules.Word} (h : meas w.toNat = 0) : w = 0 := meas_eq_zero.1 h

/-- A counter word of nonzero measure is nonzero. -/
theorem down_ne {w : EvmRules.Word} (h : meas w.toNat ≠ 0) : ¬w = 0 :=
  fun e => h (meas_eq_zero.2 e)

theorem upM_pos {i n : EvmRules.Word} (h : upM i n ≠ 0) : i < n := by
  unfold upM at h
  split at h
  · assumption
  · exact absurd rfl h

theorem upM_zero {i n : EvmRules.Word} (h : upM i n = 0) : ¬i < n := by
  intro hl
  unfold upM at h
  rw [ite_eq_left hl] at h
  have : i.toNat < n.toNat := hl
  omega

/-- One step of `i < n`: `i + 1` leaves fewer iterations. -/
theorem upM_step {i n : EvmRules.Word} (h : i < n) : upM (EvmRules.Evm.add 1 i) n < upM i n := by
  have hl : i.toNat < n.toNat := h
  have hn := n.isLt
  have hs : (EvmRules.Evm.add 1 i).toNat = i.toNat + 1 := by
    unfold EvmRules.Evm.add
    rw [BitVec.toNat_add, show (1 : BitVec 256).toNat = 1 from rfl]
    omega
  unfold upM
  rw [ite_eq_left h]
  split
  · rw [hs]; omega
  · omega

theorem upM_step' {i n : EvmRules.Word} (h : i < n) : upM (EvmRules.Evm.add i 1) n < upM i n := by
  rw [show EvmRules.Evm.add i 1 = EvmRules.Evm.add 1 i from BitVec.add_comm _ _]
  exact upM_step h

/-- The entry of `i < n`: at most `n`'s value. -/
theorem upM_le {i n : EvmRules.Word} {K : Nat} (h : n.toNat ≤ K) : upM i n ≤ K := by
  unfold upM
  split <;> omega

/-- The entry of `i < n` at a header stack: at most `n`'s value. Stated over `up`, so a use
unifies with the goal's measure without unfolding the comparison. -/
theorem up_le {k j : Nat} {ws : EVM.Stack} {K : Nat} (h : (ws.getD j 0).toNat ≤ K) :
    up k j ws ≤ K :=
  upM_le h

/-- The entry of a counter word `0 - x`: at most `x`'s value. -/
theorem meas_neg_le {x : EvmRules.Word} {K : Nat} (h : x.toNat ≤ K) :
    meas (EvmRules.Evm.sub 0 x).toNat ≤ K :=
  Counted.meas_neg_le rfl h

/-- A call argument's value, at most `K`. -/
theorem arg_le {x : EvmRules.Word} {a K : Nat} (ha : x.toNat = a) (hK : a ≤ K) : x.toNat ≤ K :=
  ha ▸ hK

/-- A storage word of the call's initial state, at most `K` when its slot's value is. -/
theorem initial_storage_le {c : Call} {slot : EvmRules.Word} {K : Nat}
    (h : slotValue c.storage slot.toNat ≤ K) : ((State.initial c).storage slot).toNat ≤ K := by
  simp only [State.initial, BitVec.toNat_ofNat]
  exact Nat.le_trans (Nat.mod_le _ _) h

open SolidCore.Refinement SolidCore.Refinement.Generic in
/-- What a call of selector `sel` with word arguments `as`, no value and storage `σ` gives the
block facts of a loop whose limit is no argument: its value, its calldata size and its selector. -/
theorem call_facts0 (sel : Nat) (hs : sel < 2 ^ 32) (as : List Nat) (has : ∀ a ∈ as, a < 2 ^ 256)
    (σ : List (Nat × Nat)) {n : Nat} (hn : as.length = n) :
    ({ calldata := Abi.calldata sel as, callvalue := 0, storage := σ } : Call).callvalue = 0 ∧
    ({ calldata := Abi.calldata sel as, callvalue := 0, storage := σ } : Call).calldata.size =
      4 + 32 * n ∧
    EvmRules.Evm.shr 224
        (calldataWord ({ calldata := Abi.calldata sel as, callvalue := 0, storage := σ } : Call) 0) =
      BitVec.ofNat 256 sel := by
  subst hn
  have hf := callFacts sel hs as has σ
  exact ⟨rfl, hf.size, hf.selector⟩


/-! ## Block facts that read storage after writing it -/

/-- A storage word after an `SSTORE`, as the machine's `update` gives it. -/
theorem update_apply (m : EvmRules.Word → EvmRules.Word) (k v j : EvmRules.Word) :
    SolarTV.Machine.update m k v j = if j = k then v else m j := rfl

set_option hygiene false in
/-- `sym_exec` for a block that reads a storage slot after writing a slot: after every split the
reads through `update` at literal slots are resolved (`update_apply`, the slots' equality decided),
so the path's hypotheses, stated over the entry state's words, decide its conditions. The leaves
close as `sym_exec`'s do. -/
macro "sym_exec_st" : tactic => `(tactic| (
  obtain ⟨cd, hcd⟩ : ∃ cd, cd = calldataWord call := ⟨_, rfl⟩
  sym_norm
  repeat' ((first | split_cond | split_table) <;>
    (try simp (config := { decide := true }) only
      [Verify.Gas.FixedFuel.Measured.update_apply, ite_true, ite_false] at *) <;> sym_norm)
  all_goals first
    | with_reducible rfl
    | (exfalso; bv_omega)
    | (exfalso; sym_omega)
    | (exfalso; sym_comm_contra)
    | sym_select
    | sym_agree
    | sym_expand
    | fail "sym_exec_st: the run ends in another result on this path, or the procedure cannot tell"))

/-! ## The fit -/

open SolidCore.Refinement.Solar in
/-- **The fixed fuel's gas fits in 64 bits**, from the per-iteration and exit parts. -/
theorem fit_of {c : Assemble.Cert} {E B X pi ex K : Nat}
    (hp : perIterGas c B = pi) (he : exitGas c E X = ex) (h : K * pi + ex < 2 ^ 64) :
    AssembleLoop.gasBoundL c (fixedFuel E B X K) < 2 ^ 64 := by
  rw [gasBoundL_fixed, fixedGas, hp, he]
  exact h

end Verify.Gas.FixedFuel.Measured

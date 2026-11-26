import Verify.Gas.FixedFuel.Gas
import SolidCore.Refinement.Solar.AssembleFast
import SolidCore.Refinement.Generic.Stage

/-!
# A counted loop's `Loops` over the final EVM IR

The generated fixed-fuel resource proofs (solar's `tools/certify/loop_resources.py`) prove
`Loops` for a program whose one loop is counted: its header block `H` is entered with `n` stack
words, and word `k` of them steps by one up to zero, so the iterations it has left are
`meas w = (2 ^ 256 - w) % 2 ^ 256` of its value `w`. What a generated module would otherwise repeat
is here, generic over the step function:

* the loop record `record k` (valuation word 0 tells the header, `1`, from an end, `0`; the
  header's stack words follow) and the measure lemmas;
* the bridge, whose header relation is fixed by `H`, `n` and `X` (`At`), from per-stack obligations
  (`loops_of`): an iteration reaches `IterQ` within `B` blocks, the exit ends within `X` blocks,
  and the entry reaches `EntryQ` within `E` blocks;
* the path combinators those obligations are proved with, one block fact at a time
  (`Reaches.next`, `ends_next`, `ends_of_halts`);
* the loop checker's and the verdict's facts, and totality from `Loops`.
-/

namespace Verify.Gas.FixedFuel.Counted

open SolarTV SolarTV.Machine Verify.LoopSource.Interface
open SolidCore.Refinement.Generic (Val WExpr wordSize)

/-! ## The measure -/

/-- The iterations left from a counter word that the body steps by one up to zero. -/
def meas (w : Nat) : Nat := (2 ^ 256 - w) % 2 ^ 256

theorem meas_add_one {h : EvmRules.Word} (hh : ¬h = 0) :
    meas (EvmRules.Evm.add 1 h).toNat < meas h.toNat := by
  have : h.toNat ≠ 0 := fun e => hh (BitVec.eq_of_toNat_eq (by simpa using e))
  have := h.isLt
  unfold meas EvmRules.Evm.add
  rw [BitVec.toNat_add, show (1 : BitVec 256).toNat = 1 from rfl]
  omega

theorem meas_add_one' {h : EvmRules.Word} (hh : ¬h = 0) :
    meas (EvmRules.Evm.add h 1).toNat < meas h.toNat := by
  rw [show EvmRules.Evm.add h 1 = EvmRules.Evm.add 1 h from BitVec.add_comm _ _]
  exact meas_add_one hh

theorem meas_pos {h : EvmRules.Word} (hh : ¬h = 0) : 0 < meas h.toNat := by
  have : h.toNat ≠ 0 := fun e => hh (BitVec.eq_of_toNat_eq (by simpa using e))
  have := h.isLt
  unfold meas
  omega

/-- A counter word `0 - x` has `x` iterations left. -/
theorem meas_neg_le {x : EvmRules.Word} {a K : Nat} (ha : x.toNat = a) (hK : a ≤ K) :
    meas (EvmRules.Evm.sub 0 x).toNat ≤ K := by
  have := x.isLt
  unfold meas EvmRules.Evm.sub
  rw [BitVec.toNat_sub, show (0 : BitVec 256).toNat = 0 from rfl]
  omega

/-! ## The record -/

/-- A valuation of header words. -/
def val (as : List Nat) : Val := ⟨as, fun _ => 0, fun _ _ => 0, 0⟩

/-- The loop's record when its counter is header stack word `k`: valuation word 0 tells the
header (1) from an end (0); the condition is the counter word, the measure the iterations it has
left. -/
def record (k : Nat) : LoopRecord where
  H := { scopes := [], writes := [], logs := [] }
  P _ := True
  m σ := if σ.args.getD 0 0 = 0 then 0 else meas (σ.args.getD (k + 1) 0)
  c := .sel (.arg 0) (.arg (k + 1)) (.lit 0)
  bb := .leaf (.normal { scopes := [], writes := [], logs := [] })

theorem getD_toNat (ws : List EvmRules.Word) (k : Nat) :
    (ws.map BitVec.toNat).getD k 0 = (ws.getD k 0).toNat := by
  induction ws generalizing k with
  | nil => rfl
  | cons w ws ih => cases k <;> simp only [List.map_cons, List.getD_cons_zero, List.getD_cons_succ, ih]

theorem m_head (k : Nat) (ws : List EvmRules.Word) :
    (record k).m (val (1 :: ws.map BitVec.toNat)) = meas (ws.getD k 0).toNat := by
  simp only [record, val, List.getD_cons_zero, List.getD_cons_succ, getD_toNat, Nat.one_ne_zero,
    ↓reduceIte]

theorem m_zero (k : Nat) : (record k).m (val [0]) = 0 := by simp [record, val]

theorem c_head (k : Nat) (ws : List EvmRules.Word) :
    (record k).c.eval (val (1 :: ws.map BitVec.toNat)) = 0 ↔ ws.getD k 0 = 0 := by
  have := (ws.getD k 0).isLt
  simp only [record, val, WExpr.eval, List.getD_cons_zero, List.getD_cons_succ, getD_toNat,
    wordSize, Nat.mod_eq_of_lt this]
  simp [BitVec.toNat_eq]

theorem c_zero (k : Nat) : (record k).c.eval (val [0]) = 0 := by
  simp [record, val, WExpr.eval]

/-! ## Paths of block facts -/

/-- A configuration of the final EVM IR: block, stack, state. -/
abbrev Cfg := Nat × EVM.Stack × State

variable {step : Cfg → Option (Res ⊕ Cfg)}

/-- A block result that ends the run. -/
@[reducible] def halts : Option (Res ⊕ Cfg) → Bool
  | some (.inl _) => true
  | _ => false

theorem ends_of_halts {x : Cfg} {j : Nat} (h : halts (step x) = true) :
    ∃ r, iterate step (j + 1) x = some r := by
  cases hs : step x with
  | none => simp [hs] at h
  | some v =>
    cases v with
    | inl r => exact ⟨r, by simp [iterate, hs]⟩
    | inr _ => simp [hs] at h

/-- One block that continues, then a run that ends. -/
theorem ends_next {x : Cfg} {b : Nat} {st : EVM.Stack} {j : Nat}
    (h : ∃ s', step x = some (.inr (b, st, s')))
    (k : ∀ s', ∃ r, iterate step j (b, st, s') = some r) :
    ∃ r, iterate step (j + 1) x = some r := by
  obtain ⟨s', hs⟩ := h
  obtain ⟨r, hr⟩ := k s'
  exact ⟨r, by simp [iterate, hs, hr]⟩

/-- From `x`, at most `j` blocks that continue reach a configuration where `Q` holds. -/
def Reaches (step : Cfg → Option (Res ⊕ Cfg)) (j : Nat) (x : Cfg) (Q : Cfg → Prop) : Prop :=
  ∃ y, Within step j x y ∧ Q y

theorem Reaches.here {j : Nat} {x : Cfg} {Q : Cfg → Prop} (h : Q x) : Reaches step j x Q :=
  ⟨x, ⟨0, Nat.zero_le _, .refl _⟩, h⟩

theorem Reaches.next {j : Nat} {x : Cfg} {Q : Cfg → Prop} {b : Nat} {st : EVM.Stack}
    (h : ∃ s', step x = some (.inr (b, st, s'))) (k : ∀ s', Reaches step j (b, st, s') Q) :
    Reaches step (j + 1) x Q := by
  obtain ⟨s', hs⟩ := h
  obtain ⟨y, ⟨i, hi, hr⟩, hq⟩ := k s'
  exact ⟨y, ⟨i + 1, by omega, .cont hs hr⟩, hq⟩

/-! ## The bridge -/

/-- Where an iteration from header stack `ws` may stop: the header again, with `n` stack words
and the counter's measure lower, or a configuration that ends within `X` blocks. -/
abbrev IterQ (step : Cfg → Option (Res ⊕ Cfg)) (H n k X : Nat) (ws : EVM.Stack) (y : Cfg) :
    Prop :=
  (∃ ws' s', y = (H, ws', s') ∧ ws'.length = n ∧
    meas (ws'.getD k 0).toNat < meas (ws.getD k 0).toNat) ∨
  ∃ r, iterate step X y = some r

/-- Where the entry may stop: the header, with `n` stack words and at most `M` iterations left,
or a configuration that ends within `X` blocks. -/
abbrev EntryQ (step : Cfg → Option (Res ⊕ Cfg)) (H n k X M : Nat) (y : Cfg) : Prop :=
  (∃ ws s, y = (H, ws, s) ∧ ws.length = n ∧ meas (ws.getD k 0).toNat ≤ M) ∨
  ∃ r, iterate step X y = some r

/-- The machine at the loop's header (block `H`, `n` stack words, valuation `1` and their
values), or at a configuration that ends within `X` blocks (valuation `0`). -/
def At (step : Cfg → Option (Res ⊕ Cfg)) (H n X : Nat) (σ : Val) (x : Cfg) : Prop :=
  (∃ ws s, x = (H, ws, s) ∧ ws.length = n ∧ σ = val (1 :: ws.map BitVec.toNat)) ∨
  (σ = val [0] ∧ ∃ r, iterate step X x = some r)

/-- **The bridge of a counted loop**, from its iteration and its exit at every header stack. -/
def bridge (H n k : Nat) {B X : Nat}
    (iter : ∀ ws s, ws.length = n → ¬ws.getD k 0 = 0 →
      Reaches step B (H, ws, s) (IterQ step H n k X ws))
    (done : ∀ ws s, ws.length = n → ws.getD k 0 = 0 → ∃ r, iterate step X (H, ws, s) = some r) :
    Bridge (record k) step B X where
  At := At step H n X
  iter := by
    intro σ x hx _ hc
    rcases hx with ⟨ws, s, rfl, hn, rfl⟩ | ⟨rfl, -⟩
    · have hk : ¬ws.getD k 0 = 0 := fun h => hc ((c_head k ws).2 h)
      obtain ⟨y, hw, ⟨ws', s', rfl, hn', hm⟩ | hr⟩ := iter ws s hn hk
      · exact ⟨_, _, ⟨trivial, hc, trivial, by rw [m_head, m_head]; exact hm⟩,
          .inl ⟨ws', s', rfl, hn', rfl⟩, hw⟩
      · exact ⟨val [0], y, ⟨trivial, hc, trivial, by rw [m_zero, m_head]; exact meas_pos hk⟩,
          .inr ⟨rfl, hr⟩, hw⟩
    · exact absurd (c_zero k) hc
  done := by
    intro σ x hx _ hc
    rcases hx with ⟨ws, s, rfl, hn, rfl⟩ | ⟨-, h⟩
    · exact done ws s hn ((c_head k ws).1 hc)
    · exact h

/-- **`Loops` of a counted loop** from its iteration, its exit and its entry. -/
theorem loops_of {init : Cfg} {H n k E B X M : Nat}
    (iter : ∀ ws s, ws.length = n → ¬ws.getD k 0 = 0 →
      Reaches step B (H, ws, s) (IterQ step H n k X ws))
    (done : ∀ ws s, ws.length = n → ws.getD k 0 = 0 → ∃ r, iterate step X (H, ws, s) = some r)
    (entry : Reaches step E init (EntryQ step H n k X M)) :
    Loops step init (record k) E B X M := by
  obtain ⟨y, hw, ⟨ws, s, rfl, hn, hm⟩ | hr⟩ := entry
  · exact ⟨bridge H n k iter done, _, _, hw, .inl ⟨ws, s, rfl, hn, rfl⟩, trivial,
      by rw [m_head]; exact hm⟩
  · exact ⟨bridge H n k iter done, val [0], y, hw, .inr ⟨rfl, hr⟩, trivial,
      by rw [m_zero]; exact Nat.zero_le _⟩

/-! ## The call -/

open SolidCore.Refinement SolidCore.Refinement.Generic in
/-- What a call of selector `sel` with word arguments `as`, no value and storage `σ` gives the
block facts: its value, its calldata size, its selector and its argument `i`. -/
theorem call_facts (sel : Nat) (hs : sel < 2 ^ 32) (as : List Nat) (has : ∀ a ∈ as, a < 2 ^ 256)
    (σ : List (Nat × Nat)) {n : Nat} (hn : as.length = n) (i : Nat) (hi : i < n)
    (hw : 4 + 32 * i < 2 ^ 256) :
    ({ calldata := Abi.calldata sel as, callvalue := 0, storage := σ } : Call).callvalue = 0 ∧
    ({ calldata := Abi.calldata sel as, callvalue := 0, storage := σ } : Call).calldata.size =
      4 + 32 * n ∧
    EvmRules.Evm.shr 224
        (calldataWord ({ calldata := Abi.calldata sel as, callvalue := 0, storage := σ } : Call) 0) =
      BitVec.ofNat 256 sel ∧
    (calldataWord ({ calldata := Abi.calldata sel as, callvalue := 0, storage := σ } : Call)
      (BitVec.ofNat 256 (4 + 32 * i))).toNat = as.getD i 0 := by
  subst hn
  have hf := callFacts sel hs as has σ
  have hlt : as.getD i 0 < 2 ^ 256 := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
    exact has _ (List.getElem_mem hi)
  refine ⟨rfl, hf.size, hf.selector, ?_⟩
  rw [hf.args i hi hw]
  exact Nat.mod_eq_of_lt hlt

/-! ## The checker, the verdict and totality -/

open SolidCore.Refinement.Solar in
/-- **The loop checker accepts the bytes**, from its parts, each closed by evaluation. -/
theorem checkL_of {p : Assemble.Program} {code : ByteArray} {c : Assemble.Cert} {mx : List Nat}
    (hw : Assemble.walkS c.offset (Assemble.bytesOf code) 0 (Assemble.lower p c) = true)
    (hb : AssembleLoop.blocksOkL p c mx 0 p.blocks = true) (hs : code.size < 2 ^ 32)
    (hc : c.need 0 = 0 ∧ c.top % 32 = 0 ∧ c.top ≤ 2 ^ 32) :
    AssembleLoop.checkL p code c mx = true := by
  have hw' := Assemble.walkS_drop (Assemble.bytesOf code) c.offset (Assemble.lower p c) 0
    (Nat.zero_le _)
  rw [List.drop_zero, hw] at hw'
  simp only [AssembleLoop.checkL, ← hw', hb, Assemble.labelsValid_of_walk hw'.symm,
    decide_eq_true hc.1, decide_eq_true hc.2.1, decide_eq_true hc.2.2, decide_eq_true hs,
    Bool.and_self]

/-- **The verdict is bounded** below `2 ^ 64`. -/
theorem verdict_of {c : SolidCore.Refinement.Solar.Assemble.Cert} {B E X pi ex K : Nat}
    (hp : perIterGas c B = pi) (he : exitGas c E X = ex) (h : K * pi + ex < 2 ^ 64) :
    verdictOf (some K) (perIterGas c B) (exitGas c E X) = .bounded (K * pi + ex) := by
  rw [hp, he]
  simp only [verdictOf, h, ite_true]

/-- **Totality** of the final EVM IR on the calls whose runs have `Loops`. -/
theorem total_of_loops {o : Oracle} {p : EVM.Program.Program} {Valid : Call → Prop}
    {L : LoopRecord} {E B X M : Nat}
    (loops : ∀ call, Valid call →
      Loops (EVM.Program.block o call p) (0, [], State.initial call) L E B X M) :
    ∀ call, Valid call → ∃ obs, (evmirSem o).run p call = some obs := by
  intro call hv
  obtain ⟨r, hr⟩ := ends_of_loops (loops call hv)
  have hr' : EVM.Program.run o p call (fixedFuel E B X M) = some r := hr
  exact ⟨_, by
    change (SolarTV.EVM.Program.layer.result o p call).map _ = _
    rw [SolarTV.EVM.Program.layer.result_of_ends ⟨fixedFuel E B X M, hr'⟩]
    rfl⟩

end Verify.Gas.FixedFuel.Counted

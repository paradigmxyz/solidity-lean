import Verify.Shapes
import Verify.Spec.HashScope

/-!
# UniswapV2ERC20.transfer: the slice's valid calls and postcondition over the observable

The first certified slice of docs/CERTIFICATION_TARGET.md, `transfer(address,uint256)` of the
pinned 0.8 port's `UniswapV2ERC20`, stated over `SolarTV.Call` and `SolarTV.Observable`, the
interface both SolidCore and EthLib run on. Nothing here depends on the port's code.

* `Valid s`: the selector `transfer(address,uint256)`, well-formed call data (a clean address
  `to` and any word `value`), no value, any storage that writes the slots of `s` (the
  constructor's storage, as every generic-stage scope asks). The caller is the interface's one
  caller, `0x2000` (`Generic.callerWord`): `SolarTV.Call` has no caller field, so "any caller"
  is not expressible yet (a missing bridge, named in RESULT.md); `to` ranges over every
  address, the caller among them.
* `SeqPost`: what the source does, as sequential storage updates in source order: the debit of
  the caller, then the credit of the recipient reading the debited state (`seqStore`). It
  succeeds iff the caller's balance covers `value` and the credit does not overflow, logs
  `Transfer(caller, to, value)` and returns `true`; otherwise it reverts with the source's
  revert data (`Error("ds-math-sub-underflow")` or `Error("ds-math-add-overflow")`), no log and
  the storage it started with. It needs no hash premise: it is stated at the slots the source
  computes, `solHash k 1`.
* `TargetPost`: the same in the target's words, split on `caller = to`, reading the recipient's
  balance in the state before the call, with the frame over the footprint. It follows from
  `SeqPost` under `Scope` (`targetPost_of_seq`): keccak256 separated on the call's two balance
  preimages only (`ScopedSep (transferFootprint 1 caller to)`, Verify/Spec/HashScope.lean), never
  over all keys and with no frame family.
* `Post`: `SeqPost`, and `TargetPost` and solar-verify's exported spec under the call's
  `Scope`: the scoped premise is printed in the statement, at the call it is about.
-/

namespace SolidCore.Spec.UniswapV2.ERC20.Slice

open SolarTV SolidCore.Refinement SolidCore.Refinement.Generic SolidCore.Spec

/-- `balanceOf`'s slot in the port's storage layout. -/
abbrev balanceSlot : Nat := 1

/-- The caller of every call (the interface's one caller). -/
abbrev caller : Nat := Generic.callerWord

/-- The slot of `balanceOf[a]`. -/
abbrev balKey (a : Nat) : Nat := solHash a balanceSlot

/-- The selector of `transfer(address,uint256)`. -/
abbrev transferSel : Nat := 0xa9059cbb

/-- The call `transfer(to, value)` from the storage `σ`, with no value. -/
def transferCall (σ : List (Nat × Nat)) (dst v : Nat) : Call :=
  { calldata := Abi.calldata transferSel [dst, v], callvalue := 0, storage := σ }

/-- **The valid calls**: `transfer(to, value)` on a clean address and any word, no value, from any
storage that writes every slot of `s`. -/
def Valid (s : List (Nat × Nat)) (call : Call) : Prop :=
  ∃ σ dst v, Generic.Covers s σ ∧ dst < 2 ^ 160 ∧ v < 2 ^ 256 ∧ call = transferCall σ dst v

/-- The storage `s` with the slot `k` (a word) set to `x`. -/
def upd (s : Nat → Nat) (k x : Nat) : Nat → Nat := fun n => if n % 2 ^ 256 = k then x else s n

/-- The debited state: the caller's balance less `v`. -/
def debit (s : Nat → Nat) (v : Nat) : Nat → Nat := upd s (balKey caller) (s (balKey caller) - v)

/-- **The source's storage updates, in order**: the debit of the caller, then the credit of `to`
reading the debited state. -/
def seqStore (s : Nat → Nat) (dst v : Nat) : Nat → Nat :=
  upd (debit s v) (balKey dst) (debit s v (balKey dst) + v)

/-- A word's 32 bytes, big-endian. -/
def be32 (w : Nat) : List Nat := (List.range 32).map fun i => w / 256 ^ (31 - i) % 256

/-- The topic of `Transfer(address,address,uint256)`. -/
abbrev transferTopic : Nat :=
  0xddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef

/-- The log `Transfer(from, to, value)`: its topics and data. -/
def transferLog (f t v : Nat) : List Nat × List Nat := ([transferTopic, f, t], be32 v)

/-- The revert data of `Error(msg)` for a message of at most 32 bytes: the selector, the offset
`0x20`, the length and the message padded to a word. -/
def errorData (msg : List Nat) : List Nat :=
  [0x08, 0xc3, 0x79, 0xa0] ++ be32 0x20 ++ be32 msg.length ++ msg ++
    List.replicate (32 - msg.length) 0

/-- `"ds-math-sub-underflow"`'s bytes (`subMsg_eq`). -/
def subMsg : List Nat :=
  [100, 115, 45, 109, 97, 116, 104, 45, 115, 117, 98, 45, 117, 110, 100, 101, 114, 102, 108, 111, 119]
/-- `"ds-math-add-overflow"`'s bytes (`addMsg_eq`). -/
def addMsg : List Nat :=
  [100, 115, 45, 109, 97, 116, 104, 45, 97, 100, 100, 45, 111, 118, 101, 114, 102, 108, 111, 119]

theorem subMsg_eq : subMsg = "ds-math-sub-underflow".toUTF8.toList.map (·.toNat) := by decide +kernel
theorem addMsg_eq : addMsg = "ds-math-add-overflow".toUTF8.toList.map (·.toNat) := by decide +kernel

/-- **What the source does** on `transfer(to, v)` from `σ`: see the module comment. -/
def SeqPost (call : Call) (obs : Observable) : Prop :=
  ∀ σ dst v, call = transferCall σ dst v → dst < 2 ^ 160 → v < 2 ^ 256 →
    (obs.success = true ↔
      (v ≤ slotValue σ (balKey caller) ∧ debit (slotValue σ) v (balKey dst) + v < 2 ^ 256)) ∧
    (obs.success = true → obs.storage = seqStore (slotValue σ) dst v ∧
      obs.logs = [transferLog caller dst v] ∧ obs.output = be32 1) ∧
    (obs.success = false → obs.storage = slotValue σ ∧ obs.logs = [] ∧
      obs.output = errorData (if v ≤ slotValue σ (balKey caller) then addMsg else subMsg))

/-- **The scoped premise of a call**: keccak256 separated on its footprint, the preimages of the
caller's and the recipient's `balanceOf` slots, and nothing else. -/
def Scope (call : Call) : Prop :=
  ∀ σ dst v, call = transferCall σ dst v → dst < 2 ^ 160 → v < 2 ^ 256 →
    ScopedSep (transferFootprint balanceSlot caller dst)

/-- **The target's postcondition** (docs/CERTIFICATION_TARGET.md, "First slice"): with `s` the
storage before the call, `caller ≠ to` succeeds iff `s[caller] ≥ v` and `s[to] + v < 2 ^ 256`,
then debits and credits; `caller = to` succeeds iff `s[caller] ≥ v` and leaves the storage as it
was; a success logs `Transfer(caller, to, v)`, returns `true` and changes no slot outside the
footprint; a failure reverts with the source's revert data, no log, no change. -/
def TargetPost (call : Call) (obs : Observable) : Prop :=
  ∀ σ dst v, call = transferCall σ dst v → dst < 2 ^ 160 → v < 2 ^ 256 →
    (caller ≠ dst →
      (obs.success = true ↔
        v ≤ slotValue σ (balKey caller) ∧ slotValue σ (balKey dst) + v < 2 ^ 256) ∧
      (obs.success = true → obs.storage (balKey caller) = slotValue σ (balKey caller) - v ∧
        obs.storage (balKey dst) = slotValue σ (balKey dst) + v)) ∧
    (caller = dst →
      (obs.success = true ↔ v ≤ slotValue σ (balKey caller)) ∧
      (obs.success = true → obs.storage = slotValue σ)) ∧
    (obs.success = true → obs.logs = [transferLog caller dst v] ∧ obs.output = be32 1 ∧
      ∀ n, n % 2 ^ 256 ≠ balKey caller → n % 2 ^ 256 ≠ balKey dst → obs.storage n = slotValue σ n) ∧
    (obs.success = false → obs.storage = slotValue σ ∧ obs.logs = [] ∧
      obs.output = errorData (if v ≤ slotValue σ (balKey caller) then addMsg else subMsg))

theorem balKey_mod (a : Nat) : balKey a % 2 ^ 256 = balKey a := Nat.mod_eq_of_lt (solHash_lt a _)

theorem balKey_mod' (a : Nat) :
    balKey a % 115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      balKey a := Nat.mod_eq_of_lt (solHash_lt a _)

theorem slotValue_mod (σ : List (Nat × Nat)) (n : Nat) :
    slotValue σ (n % 2 ^ 256) = slotValue σ n := by
  unfold slotValue
  simp only [Nat.mod_mod]

/-- **The target's postcondition from the source's, under the call's scope.** -/
theorem targetPost_of_seq {call : Call} {obs : Observable} (h : SeqPost call obs)
    (hs : Scope call) : TargetPost call obs := by
  intro σ dst v hc hto hv
  obtain ⟨hsucc, hok, hfail⟩ := h σ dst v hc hto hv
  have hsep := hs σ dst v hc hto hv
  have hlt : ∀ a, balKey a < 2 ^ 256 := fun a => solHash_lt a balanceSlot
  -- the debited state at the recipient's slot
  have hdeb_ne : caller ≠ dst → debit (slotValue σ) v (balKey dst) = slotValue σ (balKey dst) := by
    intro hne
    have hk : balKey caller ≠ balKey dst :=
      (transfer_slots hsep (by decide) (by decide) (by omega)).1 hne
    simp only [debit, upd, Nat.mod_eq_of_lt (hlt dst)]
    rw [if_neg (Ne.symm hk)]
  refine ⟨fun hne => ?_, fun heq => ?_, fun hsc => ?_, hfail⟩
  · have hk : balKey caller ≠ balKey dst :=
      (transfer_slots hsep (by decide) (by decide) (by omega)).1 hne
    have hd := hdeb_ne hne
    refine ⟨by rw [hsucc, hd], fun hsc => ?_⟩
    obtain ⟨hst, -, -⟩ := hok hsc
    rw [hst]
    constructor
    · simp [seqStore, upd, debit, balKey_mod', hk, Ne.symm hk]
    · simp only [seqStore, upd, balKey_mod, ↓reduceIte]
      rw [hd]
  · subst heq
    have hlt' : slotValue σ (balKey caller) < 2 ^ 256 := Generic.slotValue_lt σ _
    have hd : debit (slotValue σ) v (balKey caller) = slotValue σ (balKey caller) - v := by
      simp [debit, upd, balKey_mod']
    refine ⟨?_, fun hsc => ?_⟩
    · rw [hsucc, hd]
      exact ⟨fun h => h.1, fun h => ⟨h, by omega⟩⟩
    · obtain ⟨hst, -, -⟩ := hok hsc
      have hle := (hsucc.mp hsc).1
      rw [hst]
      funext n
      by_cases h1 : n % 2 ^ 256 = balKey caller
      · simp only [seqStore, upd, h1, ↓reduceIte]
        rw [hd, ← slotValue_mod σ n, h1]
        omega
      · simp only [seqStore, debit, upd, if_neg h1]
  · obtain ⟨hst, hlog, hout⟩ := hok hsc
    refine ⟨hlog, hout, fun n h1 h2 => ?_⟩
    rw [hst]
    simp only [seqStore, debit, upd, if_neg h1, if_neg h2]

/-- info: 'SolidCore.Spec.UniswapV2.ERC20.Slice.targetPost_of_seq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms targetPost_of_seq

end SolidCore.Spec.UniswapV2.ERC20.Slice

import Verify.Tactic
import SolidCore.Refinement.Corpus.W4

/-!
# w4: `set(uint256 v)` stores `v` in slot 0

The specification of `Main.set` in `scripts/refinement/corpus/w4.sol`, proved against
SolidCore with the Loom VC generator of `Verify.Basic`: on every call of `set` with any
argument word `v < 2 ^ 256`, from the deployed (empty) storage, the call succeeds with empty
output and no logs, and afterwards slot 0 holds `v` and every other slot 0.

`model` is the function as a `SolM` program (one `sstore`); `implements` ties it to
SolidCore by symbolic evaluation of the interpreter (`wide_symex`), and `spec` follows
from Loom's weakest precondition of the model.

`specAt` widens it to any initial storage: on every call of `set` with no value from any
storage `σ` (`scopeAt`), slot 0 ends holding `v` and every other slot of `σ` is kept
(`postAt`).
-/

namespace SolidCore.Verify.W4

open EthLib.Base SolidCore.Refinement SolidCore.Refinement.Abi SolidCore.Refinement.Wide
open SolidCore.Refinement.Evm.Wide SolidCore.Solidity SolidCore.Solidity.Source
open SolidCore.Refinement.Corpus.W4

/-- `set` as a Loom program over the storage. -/
def model (ws : List Nat) : SolM (List Nat) := do
  sstore 0 (ws.getD 0 0)
  pure []

/-- The calls of the specification: `set` on any word, from the deployed storage. -/
def scope : Call → Prop := fullScope fns []

/-- No precondition beyond the scope. -/
def pre : Call → Prop := fun _ => True

/-- `set(v)` succeeds with no output and no logs, and leaves `v` in slot 0 and 0 elsewhere. -/
def post (call : Call) (obs : Observable) : Prop :=
  let v := (argWords 1 call).getD 0 0
  obs.success = true ∧ obs.output = [] ∧ obs.logs = [] ∧
  ∀ slot, obs.storage slot = if slot % 2 ^ 256 = 0 then v else 0

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
/-- SolidCore runs `set` on any argument word as `model` does. -/
theorem run_set {c : TypeCheck.CheckedContract} (hcore : c.core = coreLit) {d : Source.State}
    (hd : Deployed fuel c d) (w : U256) :
    Source.run fuel c (callOf Bytecode.W4.Main.setSelector [w]) =
      some (Verify.observe (fun _ => 0) (model [w.toNat] (fun _ => 0))) := by
  rw [run_eq hd]
  have hs := hd.storage
  have hev := hd.events
  simp only [hcore, List.map_cons, List.map_nil]
  wide_symex [coreLit, fuel, ctxOf, hcore, Bytecode.W4.Main.setSelector]
  have hw := w.isLt
  simp only [Source.observe, Verify.observe, model, sstore, bind, StateT.bind, pure, StateT.pure,
    Except.bind, Except.pure, Observable.mk.injEq]
  refine ⟨trivial, trivial, by simp [State.logEntries], ?_⟩
  funext slot
  simp only [ite_true, State.loadSlot, StorageMap.lookup?, Std.HashMap.get?_eq_getElem?,
    Std.HashMap.getElem?_insert, getElem?_of_isEmpty hs, Shared.norm, Shared.wordModulus]
  rw [show EvmYul.UInt256.size = 2 ^ 256 from rfl]
  generalize slot % 115792089237316195423570985008687907853269984665640564039457584007913129639936 = k
  by_cases h : k = 0
  · subst h; simp; exact (Nat.mod_eq_of_lt hw).symm
  · have h' : ¬0 = k := fun e => h e.symm
    simp [h, h']

/-- `model` implements SolidCore's `Main` on every call of the scope. -/
theorem implements {c : TypeCheck.CheckedContract} (hcore : c.core = coreLit) {d : Source.State}
    (hd : Deployed fuel c d) : Implements fuel c scope (argWords 1) model :=
  implements_of_run' (by simp [fns]) fun fn hfn ws hl => by
    simp only [fns, List.mem_cons, List.not_mem_nil, or_false] at hfn
    subst hfn
    rcases ws with _ | ⟨w, _ | _⟩ <;> simp at hl
    exact run_set hcore hd w

/-- The verification conditions of `set`, by Loom's weakest preconditions. -/
theorem vcs : ∀ call, scope call → pre call → vc model (argWords 1) post call := by
  sc_vcgen [scope, fns, model, post]

/-- **The specification of `w4`'s `set`**, as a triple against SolidCore. -/
theorem spec : ∃ c, contract? = .ok c ∧ Triple fuel c scope pre post := by
  obtain ⟨c, hc⟩ := contract_ok
  obtain ⟨hk, _, hemp⟩ := shape_of hc
  obtain ⟨d, hd⟩ := deployed_of hemp
  exact ⟨c, hc, triple_of_wp (implements hk hd) vcs⟩

/-- The specification of `w4`'s `set` as `Satisfies` on SolidCore. -/
theorem satisfies : ∃ c, contract? = .ok c ∧ Satisfies (solidCore fuel) c scope pre post := by
  obtain ⟨c, hc, h⟩ := spec
  exact ⟨c, hc, satisfies_of_triple h⟩


/-! ## From any storage

`specAt` states the same on `scopeAt`, every call of `set` with no value from any storage `σ`,
whose postcondition `postAt` keeps every slot of `σ` but slot 0: `run_set_at` runs SolidCore
from `σ` written over the deployed storage (`run_eq_at`), and `vcsAt` is `sc_vcgen` for each
`σ`. -/

/-- The calls of `set` on any word, with no value, from any storage. -/
def scopeAt : Call → Prop := fun call => ∃ σ, fullScope fns σ call

/-- `set(v)` succeeds with no output and no logs, and leaves `v` in slot 0 and every other
slot of the call's storage as it was. -/
def postAt (call : Call) (obs : Observable) : Prop :=
  let v := (argWords 1 call).getD 0 0
  obs.success = true ∧ obs.output = [] ∧ obs.logs = [] ∧
  ∀ slot, obs.storage slot = if slot % 2 ^ 256 = 0 then v else slotValue call.storage slot

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
/-- SolidCore runs `set` on any argument word from any storage `σ` as `model` does. -/
theorem run_set_at {c : TypeCheck.CheckedContract} (hcore : c.core = coreLit) {d : Source.State}
    (hd : DeployedAt fuel c d []) (w : U256) (σ : List (Nat × Nat)) :
    Source.run fuel c (callAt Bytecode.W4.Main.setSelector [w] σ) =
      some (Verify.observe (slotValue σ) (model [w.toNat] (slotValue σ))) := by
  rw [run_eq_at hd]
  have hev := hd.events
  have h0 : ∀ q : Nat, d.storage[q]? = none := fun q => hd.getElem?_eq_none (by simp)
  have hget := getD_storage h0 σ
  generalize σ.foldl (fun acc kv => StorageMap.insertLoop acc kv.1 kv.2) d.storage = m at hget
  simp only [hcore, List.map_cons, List.map_nil]
  wide_symex [coreLit, fuel, ctxOf, hcore, Bytecode.W4.Main.setSelector]
  have hw := w.isLt
  simp only [Source.observe, Verify.observe, model, sstore, bind, StateT.bind, pure, StateT.pure,
    Except.bind, Except.pure, Observable.mk.injEq]
  refine ⟨trivial, trivial, by simp [State.logEntries], ?_⟩
  funext slot
  have hs := hget slot
  simp only [Nat.reducePow] at hs
  simp only [ite_true, State.loadSlot, StorageMap.lookup?, Std.HashMap.get?_eq_getElem?,
    Std.HashMap.getElem?_insert, Shared.norm, Shared.wordModulus, EvmYul.UInt256.size,
    List.getD_cons_zero, Nat.zero_mod, beq_iff_eq]
  generalize slot % 115792089237316195423570985008687907853269984665640564039457584007913129639936 = k at hs ⊢
  by_cases h : k = 0
  · subst h; simp [Nat.mod_eq_of_lt hw]
  · have h' : ¬0 = k := fun e => h e.symm
    simp only [h, h', ↓reduceIte, ← hs]
    cases m[k]? <;> rfl

/-- `model` implements SolidCore's `Main` on every call of `scopeAt`. -/
theorem implementsAt {c : TypeCheck.CheckedContract} (hcore : c.core = coreLit) {d : Source.State}
    (hd : DeployedAt fuel c d []) : Implements fuel c scopeAt (argWords 1) model := by
  rintro call ⟨σ, hs⟩
  refine implements_of_run' (s := σ) (by simp [fns]) (fun fn hfn ws hl => ?_) call hs
  simp only [fns, List.mem_cons, List.not_mem_nil, or_false] at hfn
  subst hfn
  rcases ws with _ | ⟨w, _ | _⟩ <;> simp at hl
  exact run_set_at hcore hd w σ

/-- The verification conditions of `set` from any storage, by Loom's weakest preconditions. -/
theorem vcsAt : ∀ call, scopeAt call → pre call → vc model (argWords 1) postAt call := by
  rintro call ⟨σ, hs⟩ hp
  have h : ∀ call, fullScope fns σ call → pre call → vc model (argWords 1) postAt call := by
    sc_vcgen [fns, model, postAt]
  exact h call hs hp

/-- **The specification of `w4`'s `set` from any storage**, as a triple against SolidCore. -/
theorem specAt : ∃ c, contract? = .ok c ∧ Triple fuel c scopeAt pre postAt := by
  obtain ⟨c, hc⟩ := contract_ok
  obtain ⟨hk, _, hemp⟩ := shape_of hc
  obtain ⟨d, hd⟩ := deployed_of hemp
  exact ⟨c, hc, triple_of_wp (implementsAt hk (deployedAt_of_deployed hd)) vcsAt⟩

/-- The specification from any storage as `Satisfies` on SolidCore. -/
theorem satisfiesAt : ∃ c, contract? = .ok c ∧ Satisfies (solidCore fuel) c scopeAt pre postAt := by
  obtain ⟨c, hc, h⟩ := specAt
  exact ⟨c, hc, satisfies_of_triple h⟩

end SolidCore.Verify.W4

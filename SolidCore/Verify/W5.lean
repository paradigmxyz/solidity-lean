import SolidCore.Verify.Tactic
import SolidCore.Refinement.Corpus.W5

/-!
# w5: `f(uint256 a, uint256 b)` returns `a + b`, or panics on overflow

The specification of `Main.f` in `scripts/refinement/corpus/w5.sol` (compiled by solar with
`-Ogas`), proved against SolidCore with the Loom VC generator of `Verify.Basic`: on every call
of `f` with any argument words `a b < 2 ^ 256`, from the deployed (empty) storage, the call
returns the word `a + b` when it fits in 256 bits and otherwise reverts with `Panic(0x11)`;
it emits no logs and storage stays empty.

`model` is the function as a `SolM` program; `implements` ties it to SolidCore by symbolic
evaluation of the interpreter (`wide_symex`), and `vcs` follows from Loom's weakest
precondition of the model by `sc_vcgen`. Nothing here, nor in `Corpus.W5`, uses
`native_decide` or `bv_decide`: the kernel checks `Corpus.W5.shape_eq` by evaluation.
-/

namespace SolidCore.Verify.W5

open EthLib.Base SolidCore.Refinement SolidCore.Refinement.Abi SolidCore.Refinement.Wide
open SolidCore.Refinement.Evm.Wide SolidCore.Solidity SolidCore.Solidity.Source
open SolidCore.Refinement.Corpus.W5

/-- `f` as a Loom program over the storage. -/
def model (ws : List Nat) : SolM (List Nat) :=
  if ws.getD 0 0 + ws.getD 1 0 < 2 ^ 256 then pure (word (ws.getD 0 0 + ws.getD 1 0))
  else revert (panic 0x11)

/-- The calls of the specification: `f` on any two words, from the deployed storage. -/
def scope : Call → Prop := fullScope fns []

/-- No precondition beyond the scope. -/
def pre : Call → Prop := fun _ => True

/-- `f(a, b)` returns `a + b` when it fits, else reverts with `Panic(0x11)`; it emits no
logs and leaves storage empty. -/
def post (call : Call) (obs : Observable) : Prop :=
  let a := (argWords 2 call).getD 0 0
  let b := (argWords 2 call).getD 1 0
  (if a + b < 2 ^ 256 then obs.success = true ∧ obs.output = word (a + b)
   else obs.success = false ∧ obs.output = panic 0x11) ∧
  obs.logs = [] ∧ ∀ slot, obs.storage slot = 0

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
/-- SolidCore runs `f` on any argument words as `model` does. -/
theorem run_f {c : TypeCheck.CheckedContract} (hcore : c.core = coreLit) {d : Source.State}
    (hd : Deployed fuel c d) (w1 w2 : U256) :
    Source.run fuel c (callOf Bytecode.W5.Main.fSelector [w1, w2]) =
      some (Verify.observe (fun _ => 0) (model [w1.toNat, w2.toNat] (fun _ => 0))) := by
  rw [run_eq hd]
  have hs := hd.storage
  have hev := hd.events
  simp only [hcore, List.map_cons, List.map_nil]
  wide_symex [coreLit, fuel, ctxOf, hcore, Bytecode.W5.Main.fSelector]
  all_goals
    have hw1 := w1.isLt
    have hw2 := w2.isLt
    simp only [model, List.getD_cons_zero, List.getD_cons_succ]
    split
    all_goals try omega
  all_goals
    try rw [Nat.mod_eq_of_lt (by omega)]
    simp [Source.observe, Verify.observe, revert, pure, StateT.pure, Except.pure, panic, word,
      State.logEntries, State.loadSlot, StorageMap.lookup?, getElem?_of_isEmpty hs,
      slotValue, callOf]

/-- `model` implements SolidCore's `Main` on every call of the scope. -/
theorem implements {c : TypeCheck.CheckedContract} (hcore : c.core = coreLit) {d : Source.State}
    (hd : Deployed fuel c d) : Implements fuel c scope (argWords 2) model :=
  implements_of_run' (by simp [fns]) fun fn hfn ws hl => by
    simp only [fns, List.mem_cons, List.not_mem_nil, or_false] at hfn
    subst hfn
    rcases ws with _ | ⟨w1, _ | ⟨w2, _ | _⟩⟩ <;> simp at hl
    exact run_f hcore hd w1 w2

/-- The verification conditions of `f`, by Loom's weakest preconditions. -/
theorem vcs : ∀ call, scope call → pre call → vc model (argWords 2) post call := by
  sc_vcgen [scope, fns, model, post]

/-- **The specification of `w5`'s `f`**, as a triple against SolidCore. -/
theorem spec : ∃ c, contract? = .ok c ∧ Triple fuel c scope pre post := by
  obtain ⟨c, hc⟩ := contract_ok
  obtain ⟨hk, _, hemp⟩ := shape_of hc
  obtain ⟨d, hd⟩ := deployed_of hemp
  exact ⟨c, hc, triple_of_wp (implements hk hd) vcs⟩

/-- The specification of `w5`'s `f` as `Satisfies` on SolidCore. -/
theorem satisfies : ∃ c, contract? = .ok c ∧ Satisfies (solidCore fuel) c scope pre post := by
  obtain ⟨c, hc, h⟩ := spec
  exact ⟨c, hc, satisfies_of_triple h⟩


/-! ## From any storage

`specAt` states the same on `scopeAt`, every call of `f` with no value from any storage `σ`,
whose postcondition `postAt` keeps `σ`: `run_f_at` runs SolidCore from `σ` written over the
deployed storage (`run_eq_at`), and `vcsAt` is `sc_vcgen` for each `σ`. -/

/-- The calls of `f` on any two words, with no value, from any storage. -/
def scopeAt : Call → Prop := fun call => ∃ σ, fullScope fns σ call

/-- `f(a, b)` returns `a + b` when it fits, else reverts with `Panic(0x11)`; it emits no
logs and leaves the call's storage as it was. -/
def postAt (call : Call) (obs : Observable) : Prop :=
  let a := (argWords 2 call).getD 0 0
  let b := (argWords 2 call).getD 1 0
  (if a + b < 2 ^ 256 then obs.success = true ∧ obs.output = word (a + b)
   else obs.success = false ∧ obs.output = panic 0x11) ∧
  obs.logs = [] ∧ ∀ slot, obs.storage slot = slotValue call.storage slot

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
/-- SolidCore runs `f` on any argument words from any storage `σ` as `model` does. -/
theorem run_f_at {c : TypeCheck.CheckedContract} (hcore : c.core = coreLit) {d : Source.State}
    (hd : DeployedAt fuel c d []) (w1 w2 : U256) (σ : List (Nat × Nat)) :
    Source.run fuel c (callAt Bytecode.W5.Main.fSelector [w1, w2] σ) =
      some (Verify.observe (slotValue σ) (model [w1.toNat, w2.toNat] (slotValue σ))) := by
  rw [run_eq_at hd]
  have hev := hd.events
  have h0 : ∀ q : Nat, d.storage[q]? = none := fun q => hd.getElem?_eq_none (by simp)
  have hget := getD_storage h0 σ
  generalize σ.foldl (fun acc kv => StorageMap.insertLoop acc kv.1 kv.2) d.storage = m at hget
  simp only [hcore, List.map_cons, List.map_nil]
  wide_symex [coreLit, fuel, ctxOf, hcore, Bytecode.W5.Main.fSelector]
  all_goals
    have hw1 := w1.isLt
    have hw2 := w2.isLt
    simp only [model, List.getD_cons_zero, List.getD_cons_succ]
    split
    all_goals try omega
  all_goals
    try rw [Nat.mod_eq_of_lt (by omega)]
    simp [Source.observe, Verify.observe, revert, pure, StateT.pure, Except.pure, panic, word,
      State.logEntries, State.loadSlot, StorageMap.lookup?, callAt]
  funext slot
  have hs := hget slot
  simp only [Nat.reducePow] at hs
  simp only [Shared.norm, Shared.wordModulus, EvmYul.UInt256.size]
  rw [← hs]
  split <;> (rename_i h; simp [h])

/-- `model` implements SolidCore's `Main` on every call of `scopeAt`. -/
theorem implementsAt {c : TypeCheck.CheckedContract} (hcore : c.core = coreLit) {d : Source.State}
    (hd : DeployedAt fuel c d []) : Implements fuel c scopeAt (argWords 2) model := by
  rintro call ⟨σ, hs⟩
  refine implements_of_run' (s := σ) (by simp [fns]) (fun fn hfn ws hl => ?_) call hs
  simp only [fns, List.mem_cons, List.not_mem_nil, or_false] at hfn
  subst hfn
  rcases ws with _ | ⟨w1, _ | ⟨w2, _ | _⟩⟩ <;> simp at hl
  exact run_f_at hcore hd w1 w2 σ

/-- The verification conditions of `f` from any storage, by Loom's weakest preconditions. -/
theorem vcsAt : ∀ call, scopeAt call → pre call → vc model (argWords 2) postAt call := by
  rintro call ⟨σ, hs⟩ hp
  have h : ∀ call, fullScope fns σ call → pre call → vc model (argWords 2) postAt call := by
    sc_vcgen [fns, model, postAt]
  exact h call hs hp

/-- **The specification of `w5`'s `f` from any storage**, as a triple against SolidCore. -/
theorem specAt : ∃ c, contract? = .ok c ∧ Triple fuel c scopeAt pre postAt := by
  obtain ⟨c, hc⟩ := contract_ok
  obtain ⟨hk, _, hemp⟩ := shape_of hc
  obtain ⟨d, hd⟩ := deployed_of hemp
  exact ⟨c, hc, triple_of_wp (implementsAt hk (deployedAt_of_deployed hd)) vcsAt⟩

/-- The specification from any storage as `Satisfies` on SolidCore. -/
theorem satisfiesAt : ∃ c, contract? = .ok c ∧ Satisfies (solidCore fuel) c scopeAt pre postAt := by
  obtain ⟨c, hc, h⟩ := specAt
  exact ⟨c, hc, satisfies_of_triple h⟩

end SolidCore.Verify.W5

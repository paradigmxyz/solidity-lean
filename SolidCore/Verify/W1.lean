import SolidCore.Verify.Tactic
import SolidCore.Refinement.Corpus.W1

/-!
# w1: `f(uint256 x)` returns `x + 1`, or panics on overflow

The specification of `Main.f` in `scripts/refinement/corpus/w1.sol`, proved against SolidCore
with the Loom VC generator of `Verify.Basic`: on every call of `f` with any argument word
`x < 2 ^ 256`, from the deployed (empty) storage, the call returns the word `x + 1` when it
fits in 256 bits and otherwise reverts with `Panic(0x11)`; storage stays empty.

`model` is the function as a `SolM` program; `implements` ties it to SolidCore by symbolic
evaluation of the interpreter (`wide_symex`), and `spec` follows from Loom's weakest
precondition of the model, which `simp` computes and `omega` discharges.
-/

namespace SolidCore.Verify.W1

open EthLib.Base SolidCore.Refinement SolidCore.Refinement.Abi SolidCore.Refinement.Wide
open SolidCore.Refinement.Evm.Wide SolidCore.Solidity SolidCore.Solidity.Source
open SolidCore.Refinement.Corpus.W1

/-- `f` as a Loom program over the storage. -/
def model (ws : List Nat) : SolM (List Nat) :=
  if ws.getD 0 0 + 1 < 2 ^ 256 then pure (word (ws.getD 0 0 + 1)) else revert (panic 0x11)

/-- The calls of the specification: `f` on any word, from the deployed storage. -/
def scope : Call → Prop := fullScope fns []

/-- No precondition beyond the scope. -/
def pre : Call → Prop := fun _ => True

/-- `f(x)` returns `x + 1` when it fits, else reverts with `Panic(0x11)`, and leaves
storage empty. -/
def post (call : Call) (obs : Observable) : Prop :=
  let x := (argWords 1 call).getD 0 0
  (if x + 1 < 2 ^ 256 then obs.success = true ∧ obs.output = word (x + 1)
   else obs.success = false ∧ obs.output = panic 0x11) ∧
  obs.logs = [] ∧ ∀ slot, obs.storage slot = 0

end SolidCore.Verify.W1


namespace SolidCore.Verify.W1

open EthLib.Base SolidCore.Refinement SolidCore.Refinement.Abi SolidCore.Refinement.Wide
open SolidCore.Refinement.Evm.Wide SolidCore.Solidity SolidCore.Solidity.Source
open SolidCore.Refinement.Corpus.W1

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
/-- SolidCore runs `f` on any argument word as `model` does. -/
theorem run_f {c : TypeCheck.CheckedContract} (hcore : c.core = coreLit) {d : Source.State}
    (hd : Deployed fuel c d) (w : U256) :
    Source.run fuel c (callOf Bytecode.W1.Main.fSelector [w]) =
      some (Verify.observe (fun _ => 0) (model [w.toNat] (fun _ => 0))) := by
  rw [run_eq hd]
  have hs := hd.storage
  have hev := hd.events
  simp only [hcore, List.map_cons, List.map_nil]
  wide_symex [coreLit, fuel, ctxOf, hcore, Bytecode.W1.Main.fSelector]
  all_goals
    have hw := w.isLt
    simp only [model, List.getD_cons_zero]
    split
    all_goals try omega
  all_goals
    try rw [Nat.mod_eq_of_lt (by omega)]
    simp [Source.observe, Verify.observe, revert, pure, StateT.pure, Except.pure, panic, word,
      State.logEntries, State.loadSlot, StorageMap.lookup?, getElem?_of_isEmpty hs,
      slotValue, callOf]

/-- `model` implements SolidCore's `Main` on every call of the scope. -/
theorem implements {c : TypeCheck.CheckedContract} (hcore : c.core = coreLit) {d : Source.State}
    (hd : Deployed fuel c d) : Implements fuel c scope (argWords 1) model :=
  implements_of_run' (by simp [fns]) fun fn hfn ws hl => by
    simp only [fns, List.mem_cons, List.not_mem_nil, or_false] at hfn
    subst hfn
    rcases ws with _ | ⟨w, _ | _⟩ <;> simp at hl
    exact run_f hcore hd w

/-- The verification conditions of `f`, by Loom's weakest preconditions. -/
theorem vcs : ∀ call, scope call → pre call → vc model (argWords 1) post call := by
  sc_vcgen [scope, fns, model, post]

/-- **The specification of `w1`'s `f`**, as a triple against SolidCore. -/
theorem spec : ∃ c, contract? = .ok c ∧ Triple fuel c scope pre post := by
  obtain ⟨c, hc⟩ := contract_ok
  obtain ⟨hk, _, hemp⟩ := shape_of hc
  obtain ⟨d, hd⟩ := deployed_of hemp
  exact ⟨c, hc, triple_of_wp (implements hk hd) vcs⟩

/-- The specification of `w1`'s `f` as `Satisfies` on SolidCore. -/
theorem satisfies : ∃ c, contract? = .ok c ∧ Satisfies (solidCore fuel) c scope pre post := by
  obtain ⟨c, hc, h⟩ := spec
  exact ⟨c, hc, satisfies_of_triple h⟩

end SolidCore.Verify.W1

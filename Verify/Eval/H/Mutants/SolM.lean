import Loom.MonadAlgebras.WP.Basic
import Mathlib.Tactic.SplitIfs
import Verify.Eval.H.Mutation
import Verify.Eval.H.Close

/-!
# Mutation tests: the baseline \`sc_vcgen\` cascade on \`SolM\` models (lane H)

\`SolM\`, \`sload\`, \`sstore\`, \`revert\` and their weakest-precondition rules are copied from
\`Verify/Basic.lean\` (same definitions; \`Verify.Basic\` itself imports the SolidCore refinement,
which this check does not need). \`sc_cascade\` is the engine of \`Verify/Tactic.lean\`'s \`sc_vcgen\`
after it has reduced the scope: \`simp only\` with \`wp_bind\`, \`wp_pure\` and the storage rules, then
\`sc_close\` (copied with \`sc_bounds\`).

Each \`#mutation_check\` proves the original with one fixed script and shows that the same script
fails on every mutant: a swapped branch, a self-transfer whose two \`sstore\`s hit the same slot, a
claimed success where the model reverts, and the 256-bit boundary moved by one.
-/

namespace Verify.Eval.H.SolMModel

abbrev Storage := Nat → Nat
abbrev Revert := List Nat
abbrev SolM := StateT Storage (Except Revert)
abbrev Assn := (Revert → Prop) → Storage → Prop

def Assn.ofOutcome : Except Revert (Assn × Storage) → (Revert → Prop) → Prop
  | .ok (p, s'), herr => p herr s'
  | .error e, herr => herr e

instance : MAlgOrdered SolM Assn where
  μ x := fun herr s => Assn.ofOutcome (x s) herr
  μ_ord_pure := by intro l; rfl
  μ_ord_bind := by
    intro α f g h x herr s
    show Assn.ofOutcome ((x s).bind fun a => f a.1 a.2) herr →
      Assn.ofOutcome ((x s).bind fun a => g a.1 a.2) herr
    rcases x s with e | ⟨a, s'⟩
    · exact id
    · exact h a herr s'

theorem wp_eq (x : SolM α) (post : α → Assn) :
    wp x post = fun herr s => match x s with
      | .ok (a, s') => post a herr s'
      | .error e => herr e := by
  funext herr s
  show Assn.ofOutcome ((post <$> x) s) herr = _
  simp only [Functor.map, StateT.map]
  rcases h : x s with e | ⟨a, s'⟩ <;> simp [h, Assn.ofOutcome, bind, Except.bind, pure, Except.pure]

def sload (slot : Nat) : SolM Nat := fun s => .ok (s slot, s)
def sstore (slot v : Nat) : SolM Unit :=
  fun s => .ok ((), fun k => if k % 2 ^ 256 = slot % 2 ^ 256 then v % 2 ^ 256 else s k)
def revert (data : Revert) : SolM α := fun _ => .error data

@[simp] theorem wp_sload (slot : Nat) (post : Nat → Assn) :
    wp (sload slot) post = fun herr s => post (s slot) herr s := by
  rw [wp_eq]; rfl
@[simp] theorem wp_sstore (slot v : Nat) (post : Unit → Assn) :
    wp (sstore slot v) post = fun herr s =>
      post () herr (fun k => if k % 2 ^ 256 = slot % 2 ^ 256 then v % 2 ^ 256 else s k) := by
  rw [wp_eq]; rfl
@[simp] theorem wp_revert (data : Revert) (post : α → Assn) :
    wp (revert data : SolM α) post = fun herr _ => herr data := by
  rw [wp_eq]; rfl
@[simp] theorem wp_ite (c : Prop) [Decidable c] (x y : SolM α) (post : α → Assn) :
    wp (if c then x else y) post = if c then wp x post else wp y post := by
  split <;> rfl

/-! ## The engine: \`sc_vcgen\`'s cascade (Verify/Tactic.lean) -/

open Verify.Eval.H.Close

/-- The cascade after scope reduction: compute the weakest precondition, then close. -/
syntax "sc_cascade" " [" term,* "]" : tactic
macro_rules
  | `(tactic| sc_cascade [$ts,*]) => do
    let ts : Array (Lean.TSyntax `Lean.Parser.Tactic.simpLemma) ←
      ts.getElems.mapM fun t => `(Lean.Parser.Tactic.simpLemma| $t:term)
    `(tactic| (
      intros
      simp only [$ts,*, wp_bind, wp_pure, wp_sload, wp_sstore, wp_revert, wp_ite, ite_apply]
      sc_close))

/-! ## Models -/

/-- \`if x < 10 then slot0 := 1 else slot0 := 2\`. -/
def branch (x : Nat) : SolM Unit := if x < 10 then sstore 0 1 else sstore 0 2

/-- The checked increment of slot 0 (Panic 0x11 on overflow). -/
def inc : SolM Unit := do
  let c ← sload 0
  if c + 1 < 2 ^ 256 then pure () else revert [0x11]
  sstore 0 (c + 1)

/-- \`balances[src] -= amt; balances[dst] += amt\` with balances in slots \`src\` and \`dst\`: the
second read happens after the first write, as Solidity's checked arithmetic on storage does. -/
def transfer (src dst amt : Nat) : SolM Unit := do
  let bf ← sload src
  if amt ≤ bf then pure () else revert [1]
  sstore src (bf - amt)
  let bt ← sload dst
  if bt + amt < 2 ^ 256 then pure () else revert [0x11]
  sstore dst (bt + amt)

/-- The aliasing bug: both balances read before either write, so a self-transfer mints \`amt\`. -/
def transferStale (src dst amt : Nat) : SolM Unit := do
  let bf ← sload src
  let bt ← sload dst
  if amt ≤ bf then pure () else revert [1]
  if bt + amt < 2 ^ 256 then pure () else revert [0x11]
  sstore src (bf - amt)
  sstore dst (bt + amt)

/-! ## Mutation checks -/

#mutation_check "solm_branch" :
    ∀ (x : Nat) (s : Storage),
      wp (branch x) (fun _ _ s' => s' 0 = if x < 10 then 1 else 2) (fun _ => False) s
  rejects [
    "wrong_branch_spec" => ∀ (x : Nat) (s : Storage),
      wp (branch x) (fun _ _ s' => s' 0 = if x < 10 then 2 else 1) (fun _ => False) s,
    "wrong_branch_model" => ∀ (x : Nat) (s : Storage),
      wp (if x < 10 then sstore 0 2 else sstore 0 1 : SolM Unit)
        (fun _ _ s' => s' 0 = if x < 10 then 1 else 2) (fun _ => False) s,
    "boundary_lt_le" => ∀ (x : Nat) (s : Storage),
      wp (branch x) (fun _ _ s' => s' 0 = if x ≤ 10 then 1 else 2) (fun _ => False) s ]
  using sc_cascade [branch]

#mutation_check "solm_inc" :
    ∀ (s : Storage), s 0 ≤ 2 ^ 256 - 2 →
      wp inc (fun _ _ s' => s' 0 = s 0 + 1) (fun _ => False) s
  rejects [
    "boundary_2^256-1" => ∀ (s : Storage), s 0 ≤ 2 ^ 256 - 1 →
      wp inc (fun _ _ s' => s' 0 = s 0 + 1) (fun _ => False) s,
    "boundary_lt_2^256" => ∀ (s : Storage), s 0 < 2 ^ 256 →
      wp inc (fun _ _ s' => s' 0 = s 0 + 1) (fun _ => False) s,
    "revert_claimed_success" => ∀ (s : Storage), s 0 = 2 ^ 256 - 1 →
      wp inc (fun _ _ _ => True) (fun _ => False) s,
    "wrap_claimed" => ∀ (s : Storage), s 0 ≤ 2 ^ 256 - 2 →
      wp inc (fun _ _ s' => s' 0 = (s 0 + 1) % 2 ^ 255) (fun _ => False) s ]
  using sc_cascade [inc]

#mutation_check "solm_inc_revert" :
    ∀ (s : Storage), s 0 = 2 ^ 256 - 1 →
      wp inc (fun _ _ _ => False) (fun e => e = [0x11]) s
  rejects [
    "wrong_revert_data" => ∀ (s : Storage), s 0 = 2 ^ 256 - 1 →
      wp inc (fun _ _ _ => False) (fun e => e = [1]) s,
    "boundary_2^256-2" => ∀ (s : Storage), s 0 = 2 ^ 256 - 2 →
      wp inc (fun _ _ _ => False) (fun e => e = [0x11]) s ]
  using sc_cascade [inc]

#mutation_check "solm_transfer" :
    ∀ (src dst amt : Nat) (s : Storage),
      src < 2 ^ 256 → dst < 2 ^ 256 → s src < 2 ^ 256 → s dst < 2 ^ 256 →
      amt ≤ s src → (src ≠ dst → s dst + amt < 2 ^ 256) →
      wp (transfer src dst amt)
        (fun _ _ s' => if src = dst then s' src = s src
          else s' src = s src - amt ∧ s' dst = s dst + amt) (fun _ => False) s
  rejects [
    "self_transfer_alias_dropped" => ∀ (src dst amt : Nat) (s : Storage),
      src < 2 ^ 256 → dst < 2 ^ 256 → s src < 2 ^ 256 → s dst < 2 ^ 256 →
      amt ≤ s src → s dst + amt < 2 ^ 256 →
      wp (transfer src dst amt)
        (fun _ _ s' => s' src = s src - amt ∧ s' dst = s dst + amt) (fun _ => False) s,
    "self_transfer_stale_read" => ∀ (src dst amt : Nat) (s : Storage),
      src < 2 ^ 256 → dst < 2 ^ 256 → s src < 2 ^ 256 → s dst < 2 ^ 256 →
      amt ≤ s src → (src ≠ dst → s dst + amt < 2 ^ 256) →
      wp (transferStale src dst amt)
        (fun _ _ s' => if src = dst then s' src = s src
          else s' src = s src - amt ∧ s' dst = s dst + amt) (fun _ => False) s,
    "revert_claimed_success" => ∀ (src dst amt : Nat) (s : Storage),
      src < 2 ^ 256 → dst < 2 ^ 256 → s src < 2 ^ 256 → s dst < 2 ^ 256 →
      (src ≠ dst → s dst + amt < 2 ^ 256) →
      wp (transfer src dst amt)
        (fun _ _ s' => if src = dst then s' src = s src
          else s' src = s src - amt ∧ s' dst = s dst + amt) (fun _ => False) s,
    "slot_alias_mod_2^256" => ∀ (src dst amt : Nat) (s : Storage),
      dst < 2 ^ 256 → s src < 2 ^ 256 → s dst < 2 ^ 256 →
      amt ≤ s src → (src ≠ dst → s dst + amt < 2 ^ 256) →
      wp (transfer src dst amt)
        (fun _ _ s' => if src = dst then s' src = s src
          else s' src = s src - amt ∧ s' dst = s dst + amt) (fun _ => False) s ]
  using sc_cascade [transfer, transferStale]

end Verify.Eval.H.SolMModel

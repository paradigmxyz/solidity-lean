import Std.Tactic.Do
import Verify.Eval.H.Mutation
import Verify.Eval.H.Close
import Mathlib.Tactic.CasesM

/-!
# Mutation tests: Std.Do `mvcgen` and Std.WP `vcgen` (lane H)

The models of `Mutants/SolM.lean` (a branch, the checked increment, a transfer between two
balance slots and its stale-read variant) written in `StateT Storage (Except Revert)`, with
`sstore` writing modulo 2^256 as in `Verify/Basic.lean`. The same mutants, stated as Hoare
triples, against three scripts:

* `vcgen` (Std.WP, experimental) then the baseline closer `sc_close`;
* `vcgen` then `grind` (no closer of the baseline);
* `mvcgen` (Std.Do, deprecated in 4.35 in favour of `vcgen`) then `simp only` with `zetaDelta`
  (mvcgen leaves the post-state as a `let`) and `sc_close`.

The precondition arrives as one conjunction: the `sc_close` scripts split it (`casesm*`) and
substitute the ghost values first (`simp_all` on the unsplit conjunction of the transfer hits
the recursion limit).

Reverts: `vcgen` has a spec for `throw` but none for `StateT.lift (Except.error _)`; `mvcgen`
leaves unassigned universe and monad metavariables as goals for `throw` in this stack (see
docs/eval/h.md), so its models revert with `StateT.lift (Except.error _)`, which it handles.
The two forms are the same program.
-/

namespace Verify.Eval.H.StdDoMutants
open Verify.Eval.H.Close

abbrev Storage := Nat → Nat
abbrev Revert := List Nat
abbrev M := StateT Storage (Except Revert)
def sload (k : Nat) : M Nat := do return (← get) k
def sstore (k v : Nat) : M Unit :=
  modify fun s => fun j => if j % 2 ^ 256 = k % 2 ^ 256 then v % 2 ^ 256 else s j

namespace V
def revert (d : Revert) : M Unit := throw d
def branch (x : Nat) : M Unit := if x < 10 then sstore 0 1 else sstore 0 2
def branchSwapped (x : Nat) : M Unit := if x < 10 then sstore 0 2 else sstore 0 1
def inc : M Unit := do
  let c ← sload 0
  if c + 1 < 2 ^ 256 then pure () else revert [0x11]
  sstore 0 (c + 1)
def transfer (src dst amt : Nat) : M Unit := do
  let bf ← sload src
  if amt ≤ bf then pure () else revert [1]
  sstore src (bf - amt)
  let bt ← sload dst
  if bt + amt < 2 ^ 256 then pure () else revert [0x11]
  sstore dst (bt + amt)
def transferStale (src dst amt : Nat) : M Unit := do
  let bf ← sload src
  let bt ← sload dst
  if amt ≤ bf then pure () else revert [1]
  if bt + amt < 2 ^ 256 then pure () else revert [0x11]
  sstore src (bf - amt)
  sstore dst (bt + amt)

open Std.WP
set_option experimental.vcgen true

#mutation_check "vcgen_branch" :
    ∀ (x : Nat), ⦃fun s => True⦄ branch x ⦃fun _ s' => s' 0 = if x < 10 then 1 else 2; fun _ => False⦄
  rejects [
    "wrong_branch_spec" => ∀ (x : Nat), ⦃fun s => True⦄ branch x ⦃fun _ s' => s' 0 = if x < 10 then 2 else 1; fun _ => False⦄,
    "wrong_branch_model" => ∀ (x : Nat), ⦃fun s => True⦄ branchSwapped x ⦃fun _ s' => s' 0 = if x < 10 then 1 else 2; fun _ => False⦄,
    "boundary_lt_le" => ∀ (x : Nat), ⦃fun s => True⦄ branch x ⦃fun _ s' => s' 0 = if x ≤ 10 then 1 else 2; fun _ => False⦄ ]
  using (intros; vcgen [branch, branchSwapped, inc, transfer, transferStale, sload, sstore, revert]; all_goals (try casesm* _ ∧ _); all_goals (try dsimp only at *); all_goals (try subst_vars); all_goals sc_close)

#mutation_check "vcgen_inc" :
    ∀ (n : Nat), ⦃fun s => s 0 = n ∧ n ≤ 2 ^ 256 - 2⦄ inc ⦃fun _ s' => s' 0 = n + 1; fun _ => False⦄
  rejects [
    "boundary_2^256-1" => ∀ (n : Nat), ⦃fun s => s 0 = n ∧ n ≤ 2 ^ 256 - 1⦄ inc ⦃fun _ s' => s' 0 = n + 1; fun _ => False⦄,
    "boundary_lt_2^256" => ∀ (n : Nat), ⦃fun s => s 0 = n ∧ n < 2 ^ 256⦄ inc ⦃fun _ s' => s' 0 = n + 1; fun _ => False⦄,
    "revert_claimed_success" => ∀ (n : Nat), ⦃fun s => s 0 = n ∧ n = 2 ^ 256 - 1⦄ inc ⦃fun _ s' => True; fun _ => False⦄,
    "wrap_claimed" => ∀ (n : Nat), ⦃fun s => s 0 = n ∧ n ≤ 2 ^ 256 - 2⦄ inc ⦃fun _ s' => s' 0 = (n + 1) % 2 ^ 255; fun _ => False⦄ ]
  using (intros; vcgen [branch, branchSwapped, inc, transfer, transferStale, sload, sstore, revert]; all_goals (try casesm* _ ∧ _); all_goals (try dsimp only at *); all_goals (try subst_vars); all_goals sc_close)

#mutation_check "vcgen_inc_revert" :
    ∀ (n : Nat), ⦃fun s => s 0 = n ∧ n = 2 ^ 256 - 1⦄ inc ⦃fun _ _ => False; fun e => e = [0x11]⦄
  rejects [
    "wrong_revert_data" => ∀ (n : Nat), ⦃fun s => s 0 = n ∧ n = 2 ^ 256 - 1⦄ inc ⦃fun _ _ => False; fun e => e = [1]⦄,
    "boundary_2^256-2" => ∀ (n : Nat), ⦃fun s => s 0 = n ∧ n = 2 ^ 256 - 2⦄ inc ⦃fun _ _ => False; fun e => e = [0x11]⦄ ]
  using (intros; vcgen [branch, branchSwapped, inc, transfer, transferStale, sload, sstore, revert]; all_goals (try casesm* _ ∧ _); all_goals (try dsimp only at *); all_goals (try subst_vars); all_goals sc_close)

-- vcgen_transfer with sc_close: not run. sc_close's simp_all hits maxRecDepth on the transfer VCs
-- that vcgen leaves (measured; see docs/eval/h.md); vcgen_grind_transfer below covers the transfer.



#mutation_check "vcgen_grind_branch" :
    ∀ (x : Nat), ⦃fun s => True⦄ branch x ⦃fun _ s' => s' 0 = if x < 10 then 1 else 2; fun _ => False⦄
  rejects [
    "wrong_branch_spec" => ∀ (x : Nat), ⦃fun s => True⦄ branch x ⦃fun _ s' => s' 0 = if x < 10 then 2 else 1; fun _ => False⦄,
    "wrong_branch_model" => ∀ (x : Nat), ⦃fun s => True⦄ branchSwapped x ⦃fun _ s' => s' 0 = if x < 10 then 1 else 2; fun _ => False⦄,
    "boundary_lt_le" => ∀ (x : Nat), ⦃fun s => True⦄ branch x ⦃fun _ s' => s' 0 = if x ≤ 10 then 1 else 2; fun _ => False⦄ ]
  using (intros; vcgen [branch, branchSwapped, inc, transfer, transferStale, sload, sstore, revert]; all_goals grind)

#mutation_check "vcgen_grind_inc" :
    ∀ (n : Nat), ⦃fun s => s 0 = n ∧ n ≤ 2 ^ 256 - 2⦄ inc ⦃fun _ s' => s' 0 = n + 1; fun _ => False⦄
  rejects [
    "boundary_2^256-1" => ∀ (n : Nat), ⦃fun s => s 0 = n ∧ n ≤ 2 ^ 256 - 1⦄ inc ⦃fun _ s' => s' 0 = n + 1; fun _ => False⦄,
    "boundary_lt_2^256" => ∀ (n : Nat), ⦃fun s => s 0 = n ∧ n < 2 ^ 256⦄ inc ⦃fun _ s' => s' 0 = n + 1; fun _ => False⦄,
    "revert_claimed_success" => ∀ (n : Nat), ⦃fun s => s 0 = n ∧ n = 2 ^ 256 - 1⦄ inc ⦃fun _ s' => True; fun _ => False⦄,
    "wrap_claimed" => ∀ (n : Nat), ⦃fun s => s 0 = n ∧ n ≤ 2 ^ 256 - 2⦄ inc ⦃fun _ s' => s' 0 = (n + 1) % 2 ^ 255; fun _ => False⦄ ]
  using (intros; vcgen [branch, branchSwapped, inc, transfer, transferStale, sload, sstore, revert]; all_goals grind)

#mutation_check "vcgen_grind_inc_revert" :
    ∀ (n : Nat), ⦃fun s => s 0 = n ∧ n = 2 ^ 256 - 1⦄ inc ⦃fun _ _ => False; fun e => e = [0x11]⦄
  rejects [
    "wrong_revert_data" => ∀ (n : Nat), ⦃fun s => s 0 = n ∧ n = 2 ^ 256 - 1⦄ inc ⦃fun _ _ => False; fun e => e = [1]⦄,
    "boundary_2^256-2" => ∀ (n : Nat), ⦃fun s => s 0 = n ∧ n = 2 ^ 256 - 2⦄ inc ⦃fun _ _ => False; fun e => e = [0x11]⦄ ]
  using (intros; vcgen [branch, branchSwapped, inc, transfer, transferStale, sload, sstore, revert]; all_goals grind)

#mutation_check "vcgen_grind_transfer" :
    ∀ (src dst amt a b : Nat), ⦃fun s => s src = a ∧ s dst = b ∧ src < 2 ^ 256 ∧ dst < 2 ^ 256 ∧ a < 2 ^ 256 ∧ b < 2 ^ 256 ∧ amt ≤ a ∧ (src ≠ dst → b + amt < 2 ^ 256)⦄ transfer src dst amt ⦃fun _ s' => if src = dst then s' src = a else s' src = a - amt ∧ s' dst = b + amt; fun _ => False⦄
  rejects [
    "self_transfer_alias_dropped" => ∀ (src dst amt a b : Nat), ⦃fun s => s src = a ∧ s dst = b ∧ src < 2 ^ 256 ∧ dst < 2 ^ 256 ∧ a < 2 ^ 256 ∧ b < 2 ^ 256 ∧ amt ≤ a ∧ b + amt < 2 ^ 256⦄ transfer src dst amt ⦃fun _ s' => s' src = a - amt ∧ s' dst = b + amt; fun _ => False⦄,
    "self_transfer_stale_read" => ∀ (src dst amt a b : Nat), ⦃fun s => s src = a ∧ s dst = b ∧ src < 2 ^ 256 ∧ dst < 2 ^ 256 ∧ a < 2 ^ 256 ∧ b < 2 ^ 256 ∧ amt ≤ a ∧ (src ≠ dst → b + amt < 2 ^ 256)⦄ transferStale src dst amt ⦃fun _ s' => if src = dst then s' src = a else s' src = a - amt ∧ s' dst = b + amt; fun _ => False⦄,
    "revert_claimed_success" => ∀ (src dst amt a b : Nat), ⦃fun s => s src = a ∧ s dst = b ∧ src < 2 ^ 256 ∧ dst < 2 ^ 256 ∧ a < 2 ^ 256 ∧ b < 2 ^ 256 ∧ (src ≠ dst → b + amt < 2 ^ 256)⦄ transfer src dst amt ⦃fun _ s' => if src = dst then s' src = a else s' src = a - amt ∧ s' dst = b + amt; fun _ => False⦄,
    "slot_alias_mod_2^256" => ∀ (src dst amt a b : Nat), ⦃fun s => s src = a ∧ s dst = b ∧ dst < 2 ^ 256 ∧ a < 2 ^ 256 ∧ b < 2 ^ 256 ∧ amt ≤ a ∧ (src ≠ dst → b + amt < 2 ^ 256)⦄ transfer src dst amt ⦃fun _ s' => if src = dst then s' src = a else s' src = a - amt ∧ s' dst = b + amt; fun _ => False⦄ ]
  using (intros; vcgen [branch, branchSwapped, inc, transfer, transferStale, sload, sstore, revert]; all_goals grind)


end V

namespace D
def revert (d : Revert) : M Unit := StateT.lift (Except.error d)
def branch (x : Nat) : M Unit := if x < 10 then sstore 0 1 else sstore 0 2
def branchSwapped (x : Nat) : M Unit := if x < 10 then sstore 0 2 else sstore 0 1
def inc : M Unit := do
  let c ← sload 0
  if c + 1 < 2 ^ 256 then pure () else revert [0x11]
  sstore 0 (c + 1)
def transfer (src dst amt : Nat) : M Unit := do
  let bf ← sload src
  if amt ≤ bf then pure () else revert [1]
  sstore src (bf - amt)
  let bt ← sload dst
  if bt + amt < 2 ^ 256 then pure () else revert [0x11]
  sstore dst (bt + amt)
def transferStale (src dst amt : Nat) : M Unit := do
  let bf ← sload src
  let bt ← sload dst
  if amt ≤ bf then pure () else revert [1]
  if bt + amt < 2 ^ 256 then pure () else revert [0x11]
  sstore src (bf - amt)
  sstore dst (bt + amt)

open Std.Do
set_option linter.deprecated.syntax false

#mutation_check "mvcgen_branch" :
    ∀ (x : Nat), ⦃fun s => ⌜True⌝⦄ branch x ⦃⇓ _ s' => ⌜s' 0 = if x < 10 then 1 else 2⌝⦄
  rejects [
    "wrong_branch_spec" => ∀ (x : Nat), ⦃fun s => ⌜True⌝⦄ branch x ⦃⇓ _ s' => ⌜s' 0 = if x < 10 then 2 else 1⌝⦄,
    "wrong_branch_model" => ∀ (x : Nat), ⦃fun s => ⌜True⌝⦄ branchSwapped x ⦃⇓ _ s' => ⌜s' 0 = if x < 10 then 1 else 2⌝⦄,
    "boundary_lt_le" => ∀ (x : Nat), ⦃fun s => ⌜True⌝⦄ branch x ⦃⇓ _ s' => ⌜s' 0 = if x ≤ 10 then 1 else 2⌝⦄ ]
  using (intros; mvcgen [branch, branchSwapped, inc, transfer, transferStale, sload, sstore, revert]; all_goals (try casesm* _ ∧ _); all_goals (try simp (config := { zetaDelta := true }) only at *); all_goals (try dsimp only at *); all_goals (try subst_vars); all_goals sc_close)

#mutation_check "mvcgen_inc" :
    ∀ (n : Nat), ⦃fun s => ⌜s 0 = n ∧ n ≤ 2 ^ 256 - 2⌝⦄ inc ⦃⇓ _ s' => ⌜s' 0 = n + 1⌝⦄
  rejects [
    "boundary_2^256-1" => ∀ (n : Nat), ⦃fun s => ⌜s 0 = n ∧ n ≤ 2 ^ 256 - 1⌝⦄ inc ⦃⇓ _ s' => ⌜s' 0 = n + 1⌝⦄,
    "boundary_lt_2^256" => ∀ (n : Nat), ⦃fun s => ⌜s 0 = n ∧ n < 2 ^ 256⌝⦄ inc ⦃⇓ _ s' => ⌜s' 0 = n + 1⌝⦄,
    "revert_claimed_success" => ∀ (n : Nat), ⦃fun s => ⌜s 0 = n ∧ n = 2 ^ 256 - 1⌝⦄ inc ⦃⇓ _ s' => ⌜True⌝⦄,
    "wrap_claimed" => ∀ (n : Nat), ⦃fun s => ⌜s 0 = n ∧ n ≤ 2 ^ 256 - 2⌝⦄ inc ⦃⇓ _ s' => ⌜s' 0 = (n + 1) % 2 ^ 255⌝⦄ ]
  using (intros; mvcgen [branch, branchSwapped, inc, transfer, transferStale, sload, sstore, revert]; all_goals (try casesm* _ ∧ _); all_goals (try simp (config := { zetaDelta := true }) only at *); all_goals (try dsimp only at *); all_goals (try subst_vars); all_goals sc_close)

#mutation_check "mvcgen_inc_revert" :
    ∀ (n : Nat), ⦃fun s => ⌜s 0 = n ∧ n = 2 ^ 256 - 1⌝⦄ inc ⦃post⟨fun _ _ => ⌜False⌝, fun e => ⌜e = [0x11]⌝⟩⦄
  rejects [
    "wrong_revert_data" => ∀ (n : Nat), ⦃fun s => ⌜s 0 = n ∧ n = 2 ^ 256 - 1⌝⦄ inc ⦃post⟨fun _ _ => ⌜False⌝, fun e => ⌜e = [1]⌝⟩⦄,
    "boundary_2^256-2" => ∀ (n : Nat), ⦃fun s => ⌜s 0 = n ∧ n = 2 ^ 256 - 2⌝⦄ inc ⦃post⟨fun _ _ => ⌜False⌝, fun e => ⌜e = [0x11]⌝⟩⦄ ]
  using (intros; mvcgen [branch, branchSwapped, inc, transfer, transferStale, sload, sstore, revert]; all_goals (try casesm* _ ∧ _); all_goals (try simp (config := { zetaDelta := true }) only at *); all_goals (try dsimp only at *); all_goals (try subst_vars); all_goals sc_close)

-- mvcgen with sc_close on the transfer hits the same maxRecDepth; the transfer runs with grind.
#mutation_check "mvcgen_grind_transfer" :
    ∀ (src dst amt a b : Nat), ⦃fun s => ⌜s src = a ∧ s dst = b ∧ src < 2 ^ 256 ∧ dst < 2 ^ 256 ∧ a < 2 ^ 256 ∧ b < 2 ^ 256 ∧ amt ≤ a ∧ (src ≠ dst → b + amt < 2 ^ 256)⌝⦄ transfer src dst amt ⦃⇓ _ s' => ⌜if src = dst then s' src = a else s' src = a - amt ∧ s' dst = b + amt⌝⦄
  rejects [
    "self_transfer_alias_dropped" => ∀ (src dst amt a b : Nat), ⦃fun s => ⌜s src = a ∧ s dst = b ∧ src < 2 ^ 256 ∧ dst < 2 ^ 256 ∧ a < 2 ^ 256 ∧ b < 2 ^ 256 ∧ amt ≤ a ∧ b + amt < 2 ^ 256⌝⦄ transfer src dst amt ⦃⇓ _ s' => ⌜s' src = a - amt ∧ s' dst = b + amt⌝⦄,
    "self_transfer_stale_read" => ∀ (src dst amt a b : Nat), ⦃fun s => ⌜s src = a ∧ s dst = b ∧ src < 2 ^ 256 ∧ dst < 2 ^ 256 ∧ a < 2 ^ 256 ∧ b < 2 ^ 256 ∧ amt ≤ a ∧ (src ≠ dst → b + amt < 2 ^ 256)⌝⦄ transferStale src dst amt ⦃⇓ _ s' => ⌜if src = dst then s' src = a else s' src = a - amt ∧ s' dst = b + amt⌝⦄,
    "revert_claimed_success" => ∀ (src dst amt a b : Nat), ⦃fun s => ⌜s src = a ∧ s dst = b ∧ src < 2 ^ 256 ∧ dst < 2 ^ 256 ∧ a < 2 ^ 256 ∧ b < 2 ^ 256 ∧ (src ≠ dst → b + amt < 2 ^ 256)⌝⦄ transfer src dst amt ⦃⇓ _ s' => ⌜if src = dst then s' src = a else s' src = a - amt ∧ s' dst = b + amt⌝⦄,
    "slot_alias_mod_2^256" => ∀ (src dst amt a b : Nat), ⦃fun s => ⌜s src = a ∧ s dst = b ∧ dst < 2 ^ 256 ∧ a < 2 ^ 256 ∧ b < 2 ^ 256 ∧ amt ≤ a ∧ (src ≠ dst → b + amt < 2 ^ 256)⌝⦄ transfer src dst amt ⦃⇓ _ s' => ⌜if src = dst then s' src = a else s' src = a - amt ∧ s' dst = b + amt⌝⦄ ]
  using (intros; mvcgen [branch, branchSwapped, inc, transfer, transferStale, sload, sstore, revert]; all_goals (try simp (config := { zetaDelta := true }) only at *); all_goals grind)


end D

end Verify.Eval.H.StdDoMutants

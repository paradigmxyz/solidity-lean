import Verify.Abi

/-!
# Counter's `bump(n)`: a loop proved with Loom's invariant and variant rule

`bump` of `crates/verify/examples/Counter.sol` (solar), with `count` in slot 0 and `limit`
in slot 1:

    function bump(uint256 n) external {
        require(count + n <= limit, "over");
        /// @custom:invariant i <= n
        /// @custom:invariant count == old(count) + i
        /// @custom:decreases n - i
        for (uint256 i = 0; i < n; i++) { count++; }
    }

`model` is the function as a `SolM` program: the checked `count + n` of the `require` panics
with `Panic(0x11)` when it overflows, the `require` reverts with `Error("over")`, and the loop
is `whileM` over `i` with the checked `count++` in its body. The loop is given `n + 1`
iterations, more than its variant `n - i` allows, so it never runs out (`triple_whileM`).

`bump_spec` proves the annotated specification from the annotated invariant and variant with
Loom's loop rule: from storage whose `count` is a word, a call either returns with `count`
increased by `n` and every other slot unchanged, or reverts with `Error("over")` when
`count + n > limit`, or with `Panic(0x11)` when `count + n` overflows. `bump_vc` is the same
statement as the verification condition `vc` of `Verify.Basic` against the observable.
-/

namespace SolidCore.Verify.CounterBump

open SolidCore.Refinement

/-- The revert data of `require(..., msg)`: `Error(string)` with `msg`. -/
def errorString (msg : String) : List Nat :=
  let bytes := msg.toUTF8.toList.map (·.toNat)
  (EthLib.Base.natToBytes 4 0x08c379a0).map (·.toNat) ++ word 32 ++ word bytes.length ++
    bytes ++ List.replicate ((32 - bytes.length % 32) % 32) 0

/-- One iteration: the checked `count++`, then `i++`. -/
def body (i : Nat) : SolM Nat := do
  let c ← sload 0
  if c + 1 < 2 ^ 256 then pure () else revert (panic 0x11)
  sstore 0 (c + 1)
  pure (i + 1)

/-- `bump(n)` as a `SolM` program. -/
def model (n : Nat) : SolM (List Nat) := do
  let c ← sload 0
  let lim ← sload 1
  if c + n < 2 ^ 256 then pure () else revert (panic 0x11)
  if c + n ≤ lim then pure () else revert (errorString "over")
  let _ ← whileM (fun i => decide (i < n)) body (n + 1) 0
  pure []

/-- The loop's invariant, from the annotations, with what the loop must keep about the
storage: `i <= n`, `count == old(count) + i`, the other slots unchanged, and the bound the
`require` established. -/
def inv (n : Nat) (s : Storage) (i : Nat) : Assn := fun _ s' =>
  i ≤ n ∧ s' 0 = s 0 + i ∧ (∀ k, k % 2 ^ 256 ≠ 0 → s' k = s k) ∧
    s 0 + n < 2 ^ 256

/-- The annotated variant. -/
def variant (n : Nat) (i : Nat) : Nat := n - i

theorem body_step (n : Nat) (s : Storage) (i : Nat) (hi : decide (i < n) = true) :
    triple (inv n s i) (body i) (fun i' => inv n s i' ⊓ ⌜variant n i' < variant n i⌝) := by
  have hlt : i < n := by simpa using hi
  intro herr s' ⟨hle, hc, hframe, hbound⟩
  simp only [body, wp_bind, wp_sload, wp_ite, wp_pure, wp_revert, wp_sstore]
  have h1 : s' 0 + 1 < 2 ^ 256 := by omega
  simp only [h1, ite_true]
  refine ⟨⟨by omega, ?_, ?_, hbound⟩, ?_⟩
  · simp only [ite_true]
    rw [Nat.mod_eq_of_lt h1]; omega
  · intro k hk
    simp only [Nat.zero_mod, hk, ite_false]
    exact hframe k hk
  · show (⌜variant n (i + 1) < variant n i⌝ : Assn) herr _
    have hv : variant n (i + 1) < variant n i := by simp only [variant]; omega
    simp only [LE.pure, hv]; trivial

/-- `bump`'s specification, proved with Loom's loop rule from the annotated invariant and
variant. -/
theorem bump_spec (n : Nat) (s : Storage) (herr : Revert → Prop)
    (hover : s 0 + n < 2 ^ 256 → ¬ s 0 + n ≤ s 1 → herr (errorString "over"))
    (hpanic : ¬ s 0 + n < 2 ^ 256 → herr (panic 0x11)) :
    wp (model n)
      (fun _ _ s' => s' 0 = s 0 + n ∧ ∀ k, k % 2 ^ 256 ≠ 0 → s' k = s k)
      herr s := by
  simp only [model, wp_bind, wp_sload, wp_ite, wp_pure, wp_revert]
  by_cases hb : s 0 + n < 2 ^ 256
  · simp only [hb, ite_true]
    by_cases hl : s 0 + n ≤ s 1
    · simp only [hl, ite_true]
      have hloop := triple_whileM (fun i => decide (i < n)) body (inv n s) (variant n)
        (body_step n s) (n + 1) 0 (by simp [variant])
      have h0 : inv n s 0 herr s := ⟨Nat.zero_le _, by simp, fun _ _ => rfl, hb⟩
      have := wp_cons _ _ (fun (_ : Nat) => fun (_ : Revert → Prop) s' =>
          s' 0 = s 0 + n ∧ ∀ k, k % 2 ^ 256 ≠ 0 → s' k = s k) ?_ herr s (hloop herr s h0)
      · simpa [wp_pure] using this
      · intro i herr' s' ⟨⟨hle, hc, hframe, _⟩, hdone⟩
        have hni : n ≤ i := by
          by_contra hne
          have : decide (i < n) = true := by simp; omega
          simp [LE.pure, this] at hdone
        exact ⟨by rw [hc]; congr 1; omega, hframe⟩
    · simp only [hl, ite_false]; exact hover hb hl
  · simp only [hb, ite_false]; exact hpanic hb

end SolidCore.Verify.CounterBump

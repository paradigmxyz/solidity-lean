import Verify.Lifecycle.Route

/-!
# The source half of a lifecycle module

`lifeOf fuel c? ws s` is what a generated lifecycle module's `life_eq` evaluates in the kernel:
whether the contract checks and its constructor, called with `ws`, leaves exactly `s` and no
logs. `statement_of_lifeOf` composes it with the bytecode half into `Statement`.
-/

namespace Verify.Lifecycle

open SolidCore.Solidity SolidCore.Refinement

/-- Whether `c?` checks and its constructor, called with the words `ws`, leaves exactly `s` and
no logs. -/
def lifeOf (fuel : Nat) (c? : Except TypeCheck.TypeError TypeCheck.CheckedContract)
    (ws : List Nat) (s : List (Nat × Nat)) : Bool :=
  match c? with
  | .ok c => deployedAtWith fuel c (wordArgs ws) s
  | .error _ => false

/-- The lifecycle statement from the creation's deployment and the source half's check. -/
theorem statement_of_lifeOf {fuel : Nat} {c? : Except TypeCheck.TypeError TypeCheck.CheckedContract}
    {init code : ByteArray} {ws : List Nat} {s : List (Nat × Nat)}
    (hd : Deploys (initArgs init ws) code s) (h : lifeOf fuel c? ws s = true) :
    ∃ c, c? = .ok c ∧ Statement fuel c init code ws s := by
  cases c? with
  | ok c => exact ⟨c, rfl, hd, deployedAtWith_of h⟩
  | error => simp [lifeOf] at h

end Verify.Lifecycle

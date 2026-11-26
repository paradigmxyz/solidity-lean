import SolidCore.Refinement.Wide.Refines

/-!
# The shape of a checked contract, for generated modules

`shapeOf fuel c? s` is what a generated module's `shape_eq` evaluates in the kernel: the checked
contract's core, and whether its constructor leaves exactly `s` and no logs. `deployed_of_shapeOf`
turns that one evaluation into the core and `Wide.DeployedAt`.
-/

namespace SolidCore.Refinement.Generic

open SolidCore.Solidity SolidCore.Solidity.Source

/-- The core of the checked contract `c?`, and whether its constructor leaves exactly `s` and no
logs; `none` when the contract does not check. -/
def shapeOf (fuel : Nat) (c? : Except TypeCheck.TypeError TypeCheck.CheckedContract)
    (s : List (Nat × Nat)) : Option (Contract × Bool) :=
  match c? with
  | .ok c => some (c.core, Wide.deployedAt fuel c s)
  | .error _ => none

theorem deployed_of_shapeOf {fuel : Nat} {c? : Except TypeCheck.TypeError TypeCheck.CheckedContract}
    {s : List (Nat × Nat)} {core : Contract} {c : TypeCheck.CheckedContract}
    (h : shapeOf fuel c? s = some (core, true)) (hc : c? = .ok c) :
    c.core = core ∧ ∃ d, Wide.DeployedAt fuel c d s := by
  subst hc
  obtain ⟨hk, hd⟩ := Prod.mk.inj (Option.some.inj h)
  exact ⟨hk, Wide.deployedAt_of hd⟩

end SolidCore.Refinement.Generic

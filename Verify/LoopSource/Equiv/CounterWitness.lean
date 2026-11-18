import Verify.LoopSource.Equiv.CounterCtx

/-!
# Counter's bounded valid set is satisfiable

An explicit witness for `spec n K`'s valid calls, for every deployment `n` and bound `K`: the call
`bump(0)` with no value, from storage `[(1, n)]`, which covers the load of slot 1. With a context
whose caller is a 160-bit address other than the contract's own, it meets `Context.Ok` too.
-/

namespace Verify.LoopSource.Equiv.CounterWitness
open Verify.LoopSource.Equiv.CounterCtx Verify.LoopSource.MirLink

/-- **The valid-call witness**: `bump(0)` from `[(1, n)]` is valid, has no value and is a `bump` entry. -/
theorem valid_witness (n K : Nat) :
    valid n K (bumpCall [(1, n)] 0) ∧ (bumpCall [(1, n)] 0).callvalue = 0 ∧
      ∃ σ a, bumpCall [(1, n)] 0 = bumpCall σ a :=
  ⟨⟨⟨[(1, n)], 0, Nat.zero_le K, Nat.two_pow_pos 256, rfl⟩, fun _ => ⟨(1, n), List.mem_singleton_self _, rfl⟩⟩,
    rfl, [(1, n)], 0, rfl⟩

/-- **The context witness**: caller `1`, a 160-bit address other than the contract's. -/
theorem ctx_witness : ∃ ctx : SolidCore.Verify.Generic.Context, ctx.Ok :=
  ⟨⟨1⟩, by decide, by
    show (1 : Nat) ≠ SolidCore.Refinement.selfAddress
    decide⟩

end Verify.LoopSource.Equiv.CounterWitness

/-- info: 'Verify.LoopSource.Equiv.CounterWitness.valid_witness' depends on axioms: [propext] -/
#guard_msgs in #print axioms Verify.LoopSource.Equiv.CounterWitness.valid_witness

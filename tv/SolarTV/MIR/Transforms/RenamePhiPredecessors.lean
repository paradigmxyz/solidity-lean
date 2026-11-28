import SolarTV.MIR.Ops

/-! Phi selection is preserved when CFG labels are renamed injectively.
Actual cfg-simplify pairs can also remove forwarders; the pair checker expands
those paths and checks the resulting phi values against the original graph. -/

namespace SolarTV.MIR

theorem rename_phi_predecessors (rename : Nat → Nat) (injective : Function.Injective rename)
    (predecessor : Nat) (incoming : List (Nat × EvmRules.Word)) :
    phi (rename predecessor) (incoming.map (fun (block, value) => (rename block, value))) =
      phi predecessor incoming := by
  induction incoming with
  | nil => rfl
  | cons entry rest ih => simp [phi, injective.eq_iff, ih]

end SolarTV.MIR

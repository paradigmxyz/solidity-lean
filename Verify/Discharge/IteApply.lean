import Lean

/-!
# Applying a conditional array

An exported store into a nested array evaluates to a function whose value at a key is a
conditional between two functions, applied to the inner key: `(if c then f else g) x`. The
condition's instance then decides the proposition `vc_eval` started from (an equality of
`Srt.beq`), not the one `simp` rewrote it to, so no `simp` lemma over `ite` unifies with it.
`iteFunApply` matches the term's shape instead and pushes the argument in, with the proof
`ite_fun_apply` at the term's own instance; the kernel checks that instance's type up to
unfolding.
-/

namespace SolarVerify.Discharge

theorem ite_fun_apply {α : Sort u} {β : Sort v} {c : Prop} {h : Decidable c} (f g : α → β)
    (x : α) : (@ite (α → β) c h f g) x = @ite β c h (f x) (g x) := by
  cases h <;> rfl

open Lean Meta Simp in
/-- `(if c then f else g) x` to `if c then f x else g x`, at the term's own instance. -/
simproc_decl iteFunApply (@ite (_ → _) _ _ _ _ _) := fun e => do
  unless e.isAppOfArity ``ite 6 do return .continue
  let args := e.getAppArgs
  let .forallE _ α β _ ← whnfD args[0]! | return .continue
  if β.hasLooseBVars then return .continue
  let uα ← getLevel α
  let uβ ← getLevel β
  let (c, h, f, g, x) := (args[1]!, args[2]!, args[3]!, args[4]!, args[5]!)
  let pf := mkAppN (mkConst ``ite_fun_apply [uα, uβ]) #[α, β, c, h, f, g, x]
  let rhs := mkAppN (mkConst ``ite [uβ]) #[β, c, h, (mkApp f x).headBeta, (mkApp g x).headBeta]
  return .visit { expr := rhs, proof? := some pf }

end SolarVerify.Discharge

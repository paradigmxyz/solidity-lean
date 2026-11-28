import Lean

/-!
# Kernel conversion of an equation under binders

`kernel_thm h : ∀ xs, l = r` adds the theorem `h` with the proof `fun xs => Eq.refl l`, which
only the kernel checks, by its conversion of `l` and `r`: the elaborator does not unfold either
side, so a symbolic run of a program, whose terms its `whnf` takes too long to unfold, is
checked at the kernel's speed. Free variables (an oracle, a storage) stay symbolic; a mismatch is
the kernel's `declaration type mismatch`.
-/

namespace SolidCore.Refinement.Kernel

open Lean Meta Elab Command in
/-- `kernel_thm h : ∀ xs, l = r` proves the equation by the kernel's conversion alone. -/
elab "kernel_thm " n:ident " : " t:term : command => do
  let name := (← getCurrNamespace) ++ n.getId
  liftTermElabM do
    let ty ← Term.elabType t
    Term.synthesizeSyntheticMVarsNoPostponing
    let ty ← instantiateMVars ty
    let pf ← forallTelescope ty fun xs body => do
      let some (_, l, _) := body.eq? | throwError "kernel_thm: not an equation"
      mkLambdaFVars xs (← mkEqRefl l)
    addDecl (.thmDecl { name, levelParams := [], type := ty, value := pf })

end SolidCore.Refinement.Kernel

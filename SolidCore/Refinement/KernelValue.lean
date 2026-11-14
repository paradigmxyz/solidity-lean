import SolidCore.Refinement.KernelRfl

/-!
# The value of a closed computation, printed and checked by the kernel

`kernel_some v c`, for a closed definition `c : Option α`, evaluates `c` by compiled code, prints the
value inside its `some` by `α`'s `Repr`, elaborates the print as `def v : α`, and proves
`v_eq : c = some v` by `kernel_rfl` (`kernel_some v c using e₁ … eₙ` passes the `eᵢ` on). The
evaluator and the printer are untrusted: the kernel checks the equation, so a mistake in either
is a kernel error, never a wrong literal.

This is how a check of a large closed computation is split into stages, each a declaration of
its own whose result the next stage reads as a literal, so the kernel's memory for one stage is
freed before the next: the literal is computed afresh by every build, never a checked-in copy.
-/

namespace SolidCore.Refinement.Kernel

open Lean Meta Elab Command

private unsafe def evalOptStringUnsafe (e : Expr) : MetaM (Option String) :=
  evalExpr (Option String) (mkApp (mkConst ``Option [.zero]) (mkConst ``String)) e

@[implemented_by evalOptStringUnsafe]
private opaque evalOptString (e : Expr) : MetaM (Option String)

/-- Parse and elaborate a command given as text. -/
private def elabCommandText (s : String) : CommandElabM Unit := do
  match Parser.runParserCategory (← getEnv) `command s with
  | .ok cmd => elabCommand cmd
  | .error err => throwError "kernel_some: generated command does not parse: {err}"

/-- `kernel_some v c` defines `v` as the printed value of the closed `c : Option α` and proves
`v_eq : c = some v` by `kernel_rfl`; `kernel_some v c using e₁ … eₙ` passes the `eᵢ` on. -/
syntax (name := kernelSomeCmd) "kernel_some " ident ppSpace ident
  (" using" (ppSpace ident)+)? : command

@[command_elab kernelSomeCmd, inherit_doc kernelSomeCmd]
def elabKernelSome : CommandElab := fun stx => do
  let v : Ident := ⟨stx[1]⟩
  let id : Ident := ⟨stx[2]⟩
  let c ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
  let eqNames ← liftCoreM <| (identsOf stx[3]).mapM fun e =>
    realizeGlobalConstNoOverloadWithInfo e
  let printer := s!"(match _root_.{c} with | some y => some (Std.Format.pretty (repr y) 100) | none => none : Option String)"
  let printerStx ← match Parser.runParserCategory (← getEnv) `term printer with
    | .ok t => pure t
    | .error err => throwError "kernel_some: {err}"
  let (s, ty) ← liftTermElabM do
    let ty ← whnfR (← inferType (mkConst c))
    let some α := ty.app1? ``Option | throwError "kernel_some: {c} is not of an Option type"
    let e ← Term.elabTermEnsuringType printerStx none
    Term.synthesizeSyntheticMVarsNoPostponing
    let e ← instantiateMVars e
    let some s ← evalOptString e | throwError "kernel_some: {c} evaluates to none"
    let ty ← withOptions (fun o => (pp.fullNames.set o true)) <| ppExpr α
    return (s, toString ty)
  elabCommandText s!"def {v.getId} : {ty} :=\n{s}"
  let ns ← getCurrNamespace
  let usingTxt := if eqNames.isEmpty then "" else
    " using" ++ String.join (eqNames.toList.map fun e => s!" _root_.{e}")
  elabCommandText s!"kernel_rfl {v.getId.appendAfter "_eq"} _root_.{c} (some _root_.{ns ++ v.getId}){usingTxt}"

end SolidCore.Refinement.Kernel

import Lean

/-!
# Transitive axiom audit (lane H)

* `#audit_axioms_here` audits every declaration of the current file;
* `#audit_axioms_module M` audits every declaration of the imported module `M`;
* `#audit_axioms_decls [a, b]` audits the named declarations.

For each theorem (and each definition or opaque whose axioms are not just the standard ones) it
prints one line

    AXIOMS <tab> name <tab> kind <tab> statement-hash <tab> ax1,ax2,…

with the axioms the declaration depends on transitively (`Lean.collectAxioms`, what `#print axioms`
prints). The audit fails (an error) when any axiom outside `propext`, `Classical.choice`,
`Quot.sound` appears: `sorryAx`, `Lean.ofReduceBool` / `Lean.ofReduceNat` (native_decide,
bv_decide's certificate check), `Lean.trustCompiler`, or any user axiom. It also fails when a
theorem's statement or proof mentions a definition outside Init/Std/Lean that carries
`@[implemented_by]` (a project's own fast path, which only native evaluation would run; the
kernel unfolds the reference definition, and native evaluation itself shows up as Lean.ofReduceBool).
Core's `@[extern]` primitives (Nat.decLt, UInt8.toNat, ...) are not flagged: the kernel evaluates
their reference definitions.

The statement hash is `Expr.hash` of the type with universe parameters renamed by position, the
same as `#statement_hash` (Verify.Eval.H.Expected); the cold replay compares both against
a manifest.
-/

namespace Verify.Eval.H

open Lean Elab Command Meta

def standardAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

def auditHash (ci : ConstantInfo) : UInt64 :=
  let us := ci.levelParams.zipIdx.map fun (_, i) => Level.param (Name.mkSimple s!"u_{i+1}")
  (ci.type.instantiateLevelParams ci.levelParams us).consumeMData.hash

def kindOf : ConstantInfo → String
  | .thmInfo _ => "theorem" | .defnInfo _ => "def" | .opaqueInfo _ => "opaque"
  | .axiomInfo _ => "axiom" | _ => "other"

/-- Whether `n` runs code the kernel does not check when evaluated. -/
def hasTrustedImpl (env : Environment) (n : Name) : Bool :=
  (Compiler.implementedByAttr.getParam? env n).isSome &&
    !(match env.getModuleIdxFor? n with
      | some i => let m := env.header.moduleNames[i.toNat]!.getRoot
                  m == `Init || m == `Std || m == `Lean
      | none => false)

def auditDecls (names : Array Name) (label : String) : CommandElabM Unit := do
  let env ← getEnv
  let mut bad : Array String := #[]
  let mut lines : Array String := #[]
  let mut nThm : Nat := 0
  for n in names do
    let some ci := env.find? n | continue
    if n.isInternalDetail && !ci.isTheorem then continue
    match ci with
    | .thmInfo _ | .defnInfo _ | .opaqueInfo _ | .axiomInfo _ => pure ()
    | _ => continue
    let axs ← liftCoreM <| collectAxioms n
    let axs := axs.qsort (·.toString < ·.toString)
    let nonstd := axs.filter (!standardAxioms.contains ·)
    if ci.isTheorem then nThm := nThm + 1
    if ci.isTheorem || !nonstd.isEmpty then
      lines := lines.push s!"AXIOMS\t{n}\t{kindOf ci}\t{auditHash ci}\t{",".intercalate (axs.toList.map toString)}"
    if !nonstd.isEmpty then
      bad := bad.push s!"{n}: {nonstd}"
    if ci.isTheorem then
      let used := ci.type.getUsedConstants ++ (ci.value?.map (·.getUsedConstants) |>.getD #[])
      for c in used do
        if hasTrustedImpl env c then
          bad := bad.push s!"{n}: mentions {c}, which has @[implemented_by]/@[extern]"
  logInfo m!"{"\n".intercalate lines.toList}\nAUDIT\t{label}\ttheorems={nThm}\tviolations={bad.size}"
  unless bad.isEmpty do
    throwError "AXIOM AUDIT FAILED for {label}:\n{"\n".intercalate bad.toList}"

syntax (name := auditHere) "#audit_axioms_here" : command
syntax (name := auditModule) "#audit_axioms_module " ident : command
syntax (name := auditDeclsStx) "#audit_axioms_decls " "[" ident,* "]" : command

@[command_elab auditHere] def elabAuditHere : CommandElab := fun _ => do
  let env ← getEnv
  let names := env.constants.map₂.foldl (fun acc n _ => acc.push n) #[]
  auditDecls (names.qsort (·.toString < ·.toString)) env.header.mainModule.toString

@[command_elab auditModule] def elabAuditModule : CommandElab := fun stx => do
  let env ← getEnv
  let m := stx[1].getId
  let some idx := env.getModuleIdx? m | throwError "module {m} is not imported"
  let names := env.header.moduleData[idx.toNat]!.constNames
  auditDecls (names.qsort (·.toString < ·.toString)) m.toString

@[command_elab auditDeclsStx] def elabAuditDecls : CommandElab := fun stx => do
  let names ← stx[2].getSepArgs.mapM fun i => liftCoreM <| realizeGlobalConstNoOverloadWithInfo i
  auditDecls names "decls"

end Verify.Eval.H

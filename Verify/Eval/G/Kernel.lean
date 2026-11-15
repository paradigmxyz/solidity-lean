import Verify.Eval.Common.Measure

/-!
# Lane G: kernel time of a theorem with its auxiliary proofs

Common/Measure.lean's #kernel_recheck rechecks a theorem's own body only. omega and simp put
part of a proof into auxiliary declarations (_proof_i, _simp_i, _auxLemma), which that recheck
does not count, while grind's proof is inline. #kernel_recheck_all foo rechecks foo AND every
auxiliary declaration in its closure (Measure's auxClosure), each as a fresh copy added to the
kernel only, and reports the summed kernel time, so that the proofs compare on equal terms.
-/

namespace Verify.Eval.G

open Lean Elab Command Meta

syntax (name := kernelRecheckAll) "#kernel_recheck_all " ident : command

@[command_elab kernelRecheckAll] def elabKernelRecheckAll : CommandElab := fun stx => do
  let n ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo stx[1]
  let env ← getEnv
  let names := (Verify.Eval.auxClosure env n).push n
  -- Outside the timed region: toKernelEnv waits for the environment's pending asynchronous
  -- checks, which would otherwise count as this proof's kernel time.
  let kenv := env.toKernelEnv
  let mut total : Nat := 0
  for c in names do
    let some ci := env.find? c | continue
    let some v := ci.value? (allowOpaque := true) | continue
    let isProp ← liftTermElabM <| Meta.isProp ci.type
    let decl := if isProp then
        Declaration.thmDecl (mkTheoremValEx (Name.str c "recheckAll") ci.levelParams ci.type v [])
      else
        Declaration.defnDecl (mkDefinitionValEx (Name.str c "recheckAll") ci.levelParams ci.type v
          .opaque .safe [])
    let t0 ← IO.monoNanosNow
    match kenv.addDeclCore 0 100000 decl none with
    | .ok _ => total := total + ((← IO.monoNanosNow) - t0)
    | .error e => throwError "kernel_recheck_all {c}: rejected: {e.toMessageData {}}"
  logInfo m!"kernel_recheck_all {n}: ok in {total.toFloat / 1000000.0} ms over {names.size} declarations"

end Verify.Eval.G

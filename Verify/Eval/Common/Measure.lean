import Lean

/-!
# Measurements shared by the evaluation lanes

* `#proof_stats foo`: the proof term of `foo` as a tree (`Expr.size`, capped) and as a DAG
  (unique subterms by pointer after `ShareCommon`), and its heartbeats are not re-run.
* `#kernel_recheck foo`: adds a copy of `foo` (`foo._recheck`) to the kernel only, with no
  elaboration, and reports the kernel's wall time. The copy is never used afterwards.
* `#kernel_reject_check`: shows that the same path rejects an ill-typed term (`True` proved by
  `(0 : Nat)`), so a recheck that passes means the kernel accepted the term.
-/

namespace Verify.Eval

open Lean Elab Command Meta

unsafe def dagSizeImpl (e : Expr) : Nat := Id.run do
  let mut seen : Std.HashSet USize := {}
  let mut stack := [e]
  let mut n := 0
  while true do
    match stack with
    | [] => break
    | x :: rest =>
      stack := rest
      let p := ptrAddrUnsafe x
      if seen.contains p then continue
      seen := seen.insert p
      n := n + 1
      match x with
      | .app f a => stack := f :: a :: stack
      | .lam _ t b _ | .forallE _ t b _ => stack := t :: b :: stack
      | .letE _ t v b _ => stack := t :: v :: b :: stack
      | .mdata _ b | .proj _ _ b => stack := b :: stack
      | _ => pure ()
  return n

/-- The number of distinct subterms of `e` by pointer: its size as a DAG. -/
@[implemented_by dagSizeImpl] opaque dagSize (e : Expr) : Nat

/-- The size of `e` as a tree, counting at most `cap` nodes. -/
partial def treeSize (e : Expr) (cap : Nat := 10000000) : Nat := Id.run do
  let mut stack := [e]
  let mut n := 0
  while n < cap do
    match stack with
    | [] => break
    | x :: rest =>
      stack := rest
      n := n + 1
      match x with
      | .app f a => stack := f :: a :: stack
      | .lam _ t b _ | .forallE _ t b _ => stack := t :: b :: stack
      | .letE _ t v b _ => stack := t :: v :: b :: stack
      | .mdata _ b | .proj _ _ b => stack := b :: stack
      | _ => pure ()
  return n

/-- The constants `c` uses, transitively, that are auxiliary proofs it was split into
(`_proof_`, `_simp_`, `match_`, `_auxLemma`): their DAG sizes count toward its proof. -/
partial def auxClosure (env : Environment) (root : Name) : Array Name := Id.run do
  let mut seen : NameSet := {}
  let mut out := #[]
  let mut stack := [root]
  while true do
    match stack with
    | [] => break
    | n :: rest =>
      stack := rest
      if seen.contains n then continue
      seen := seen.insert n
      let some ci := env.find? n | continue
      let some v := ci.value? (allowOpaque := true) | continue
      if n != root then out := out.push n
      for c in v.getUsedConstants do
        let s := c.toString
        if (s.startsWith root.toString || (s.splitOn "_proof_").length > 1 ||
            (s.splitOn "_auxLemma").length > 1 || (s.splitOn "_simp_").length > 1) &&
            !seen.contains c then
          stack := c :: stack
  return out

syntax (name := proofStats) "#proof_stats " ident : command

@[command_elab proofStats] def elabProofStats : CommandElab := fun stx => do
  let n ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo stx[1]
  let env ← getEnv
  let some ci := env.find? n | throwError "unknown {n}"
  let some v := ci.value? (allowOpaque := true) | throwError "{n} has no value"
  let aux := auxClosure env n
  let mut dagAux := 0
  for a in aux do
    if let some v' := (env.find? a).bind (·.value? (allowOpaque := true)) then
      dagAux := dagAux + dagSize (ShareCommon.shareCommon' v')
  let shared := ShareCommon.shareCommon' v
  logInfo m!"proof_stats {n}: tree={treeSize v} dag={dagSize shared} aux_decls={aux.size} aux_dag={dagAux} type_dag={dagSize (ShareCommon.shareCommon' ci.type)}"

syntax (name := kernelRecheck) "#kernel_recheck " ident : command

@[command_elab kernelRecheck] def elabKernelRecheck : CommandElab := fun stx => do
  let n ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo stx[1]
  let env ← getEnv
  let some ci := env.find? n | throwError "unknown {n}"
  let some v := ci.value? (allowOpaque := true) | throwError "{n} has no value"
  let decl := Declaration.thmDecl (mkTheoremValEx (Name.str n "recheck") ci.levelParams ci.type v [])
  -- Build the kernel environment before the timer: toKernelEnv waits for earlier async
  -- theorem checks, which must not be counted as this declaration's kernel time.
  let kenv ← IO.lazyPure fun _ => env.toKernelEnv
  let t0 ← IO.monoNanosNow
  match kenv.addDeclCore 0 100000 decl none with
  | .ok _ =>
    let t1 ← IO.monoNanosNow
    logInfo m!"kernel_recheck {n}: ok in {(t1 - t0).toFloat / 1000000.0} ms"
  | .error e => throwError "kernel_recheck {n}: rejected: {e.toMessageData {}}"

syntax (name := kernelRejectCheck) "#kernel_reject_check" : command

@[command_elab kernelRejectCheck] def elabKernelRejectCheck : CommandElab := fun _ => do
  let env ← getEnv
  let decl := Declaration.thmDecl (mkTheoremValEx (Name.mkSimple "verifyEvalIllTypedRecheck") [] (mkConst ``True) (mkNatLit 0) [])
  match env.toKernelEnv.addDeclCore 0 100000 decl none with
  | .ok _ => throwError "kernel_reject_check: the kernel ACCEPTED an ill-typed term"
  | .error _ => logInfo m!"kernel_reject_check: ill-typed term rejected"

/-- `#timed cmd` elaborates `cmd` (a theorem, with its tactic run and its kernel check) and
reports the wall time and heartbeats it took. Kernel time alone: `#kernel_recheck`. -/
syntax (name := timedCmd) "#timed " command : command

@[command_elab timedCmd] def elabTimed : CommandElab := fun stx => do
  let h0 ← IO.getNumHeartbeats
  let t0 ← IO.monoNanosNow
  elabCommand stx[1]
  let t1 ← IO.monoNanosNow
  let h1 ← IO.getNumHeartbeats
  logInfo m!"timed: {(t1 - t0).toFloat / 1000000.0} ms, {(h1 - h0) / 1000} heartbeats (x1000)"

end Verify.Eval

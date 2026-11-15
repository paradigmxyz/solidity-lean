import Verify.Eval.E.Toy

/-!
# Lane E: whole-fixture proof statistics

#e_stats N rechecks every theorem the current file declared under namespace N in the
kernel alone (as #kernel_recheck does for one), and reports their summed kernel time, their
summed DAG size (each proof shared on its own), the DAG size of all of them shared together
(what the .olean's sharing can reach), their summed tree size (each capped at 10^7 nodes) and the number of
declarations; and #proof_stats's numbers for ns.main with the tree capped at 10^7 (Measure's
cap of 10^8 takes tens of seconds in the interpreter). A fixture split into many lemmas is then compared with a monolithic proof of the
same statement on the whole proof, not only on its last theorem.
-/

namespace Verify.Eval.E

open Lean Elab Command

/-- The DAG size of several terms shared together, by pointer after one ShareCommon pass. -/
unsafe def dagSizeManyImpl (es : Array Expr) : Nat :=
  let shared := ShareCommon.shareCommon' es
  Id.run do
    let mut seen : Std.HashSet USize := {}
    let mut stack : List Expr := shared.toList
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

@[implemented_by dagSizeManyImpl] opaque dagSizeMany (es : Array Expr) : Nat

syntax (name := eStats) "#e_stats " ident : command

@[command_elab eStats] def elabEStats : CommandElab := fun stx => do
  let ns := stx[1].getId
  let env ← getEnv
  let mut decls : Array (Name × ConstantInfo) := #[]
  for (n, ci) in env.constants.map₂.toList do
    if ns.isPrefixOf n then
      if let .thmInfo _ := ci then decls := decls.push (n, ci)
  let mut kernelNs : Nat := 0
  let mut maxNs : Nat := 0
  let mut dagSum := 0
  let mut treeSum := 0
  let mut vals : Array Expr := #[]
  for (n, ci) in decls do
    let some v := ci.value? (allowOpaque := true) | continue
    vals := vals.push v
    dagSum := dagSum + dagSize (ShareCommon.shareCommon' v)
    treeSum := treeSum + treeSize v 10000000
    let decl := Declaration.thmDecl (mkTheoremValEx (Name.str n "recheck") ci.levelParams ci.type v [])
    let t0 ← IO.monoNanosNow
    match env.toKernelEnv.addDeclCore 0 100000 decl none with
    | .ok _ =>
      let t1 ← IO.monoNanosNow
      kernelNs := kernelNs + (t1 - t0)
      maxNs := max maxNs (t1 - t0)
    | .error e => throwError "e_stats {n}: rejected: {e.toMessageData {}}"
  let mainName := ns ++ `main
  let (mainTree, mainDag) := match (env.find? mainName).bind (·.value? (allowOpaque := true)) with
    | some v => (treeSize v 10000000, dagSize (ShareCommon.shareCommon' v))
    | none => (0, 0)
  let aux := auxClosure env mainName
  let mut auxDag := 0
  for a in aux do
    if let some v' := (env.find? a).bind (·.value? (allowOpaque := true)) then
      auxDag := auxDag + dagSize (ShareCommon.shareCommon' v')
  logInfo m!"proof_stats {mainName}: tree={mainTree} dag={mainDag} aux_decls={aux.size} aux_dag={auxDag} (tree capped at 1e7)"
  logInfo m!"e_stats {ns}: decls={decls.size} kernel_ms={kernelNs.toFloat / 1000000.0} max_decl_kernel_ms={maxNs.toFloat / 1000000.0} dag_sum={dagSum} dag_union={dagSizeMany vals} tree_sum={treeSum}"

/-! ## Whole imported modules

#e_module_stats M rechecks in the kernel every theorem that the imported module M declared
(generated proofs such as Contracts.VerifyCounter.Bump), and reports their count, summed and
largest kernel time, summed DAG and tree size (tree capped at 10^7 per theorem), how many are
auxiliary (_proof_, _auxLemma, _simp_, match_) and the five slowest theorems. -/

syntax (name := eModuleStats) "#e_module_stats " ident : command

@[command_elab eModuleStats] def elabEModuleStats : CommandElab := fun stx => do
  let modName := stx[1].getId
  let env ← getEnv
  let some modIdx := env.getModuleIdx? modName | throwError "module {modName} is not imported"
  let mut n : Nat := 0
  let mut aux : Nat := 0
  let mut kernelNs : Nat := 0
  let mut dagSum : Nat := 0
  let mut treeSum : Nat := 0
  let mut slow : Array (Nat × Name × Nat × Nat) := #[]
  for (name, ci) in env.constants.map₁.toList do
    unless env.getModuleIdxFor? name == some modIdx do continue
    let .thmInfo _ := ci | continue
    let some v := ci.value? (allowOpaque := true) | continue
    n := n + 1
    let s := name.toString
    if (s.splitOn "_proof_").length > 1 || (s.splitOn "_auxLemma").length > 1 ||
        (s.splitOn "_simp_").length > 1 || (s.splitOn "match_").length > 1 then aux := aux + 1
    let d := dagSize (ShareCommon.shareCommon' v)
    let t := treeSize v 10000000
    dagSum := dagSum + d
    treeSum := treeSum + t
    let decl := Declaration.thmDecl (mkTheoremValEx (Name.str name "recheck") ci.levelParams ci.type v [])
    let t0 ← IO.monoNanosNow
    match env.toKernelEnv.addDeclCore 0 100000 decl none with
    | .ok _ =>
      let t1 ← IO.monoNanosNow
      kernelNs := kernelNs + (t1 - t0)
      slow := slow.push (t1 - t0, name, d, t)
    | .error e => throwError "e_module_stats {name}: rejected: {e.toMessageData {}}"
  let top := (slow.qsort (fun a b => a.1 > b.1)).toList.take 5
  let topMsg := ", ".intercalate (top.map fun (ns, nm, d, t) =>
    s!"{nm} {(ns.toFloat / 1000000.0)}ms dag={d} tree={t}")
  logInfo m!"e_module_stats {modName}: theorems={n} aux={aux} kernel_ms={kernelNs.toFloat / 1000000.0} dag_sum={dagSum} tree_sum={treeSum} slowest: {topMsg}"

end Verify.Eval.E

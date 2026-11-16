import Lean

/-!
Per-declaration kernel time and proof size for one compiled module.

Usage: lake env lean --run scripts/eval/acc4/Kernel.lean <Module> <out.csv>

For every constant the module itself declares that has a value (theorems, definitions,
opaque constants), the script re-adds a renamed copy to the kernel environment of the module's
own imports plus everything before it, and times that call alone: the kernel environment is
built before the timer starts. It also records the value's size as a tree (capped at 10^7) and
as a DAG after ShareCommon, and the type's DAG size. Nothing is added to any olean.
-/

open Lean

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

def treeSize (e : Expr) (cap : Nat := 10000000) : Nat := Id.run do
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

def csvq (s : String) : String := "\"" ++ s.replace "\"" "\"\"" ++ "\""

unsafe def main (args : List String) : IO UInt32 := do
  let [mod, out] := args | IO.eprintln "usage: Kernel.lean <Module> <out.csv>"; return 2
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let modName := mod.toName
  let env ← importModules #[{ module := modName }] {} (loadExts := true)
  let some idx := env.getModuleIdx? modName | IO.eprintln s!"{mod} not loaded"; return 2
  let names := env.header.moduleData[idx.toNat]!.constNames
  let kenv := env.toKernelEnv
  let h ← IO.FS.Handle.mk out .write
  h.putStrLn "module,decl,kind,kernel_ms,tree_nodes,dag_nodes,type_dag_nodes,status"
  let mut total := 0.0
  for n in names do
    let some ci := env.find? n | continue
    let kind := match ci with
      | .thmInfo _ => "theorem" | .defnInfo _ => "def" | .opaqueInfo _ => "opaque"
      | .axiomInfo _ => "axiom" | .inductInfo _ => "inductive" | .ctorInfo _ => "ctor"
      | .recInfo _ => "recursor" | .quotInfo _ => "quot"
    let some v := ci.value? (allowOpaque := true) | continue
    let nn := n ++ `_acc4_recheck
    let decl : Declaration := match ci with
      | .thmInfo t => .thmDecl { t with name := nn }
      | .defnInfo d => .defnDecl { d with name := nn }
      | .opaqueInfo o => .opaqueDecl { o with name := nn }
      | _ => .thmDecl (mkTheoremValEx nn ci.levelParams ci.type v [])
    let t0 ← IO.monoNanosNow
    let r := kenv.addDeclCore 0 1000000000 decl none
    let st ← match r with
      | .ok _ => pure "ok"
      | .error _ => pure "rejected"
    let t1 ← IO.monoNanosNow
    let ms := (t1 - t0).toFloat / 1000000.0
    total := total + ms
    let dag := dagSizeImpl (ShareCommon.shareCommon' v)
    let tdag := dagSizeImpl (ShareCommon.shareCommon' ci.type)
    h.putStrLn s!"{mod},{csvq n.toString},{kind},{ms},{treeSize v},{dag},{tdag},{st}"
  IO.eprintln s!"{mod}: {names.size} constants, kernel total {total} ms"
  return 0

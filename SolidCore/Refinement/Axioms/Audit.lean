import Lean

/-!
# Axiom audit

`#axiom_audit "out" "prefix"*` collects, with one memoized pass over the environment, the
axioms of every theorem and definition declared in a module whose name starts with one of the
prefixes, reports every declaration that depends on an axiom other than `propext`,
`Classical.choice` and `Quot.sound` (`sorryAx` and `Lean.ofReduceBool` among them), and writes
the source path of every module the importing file's environment contains to `out`, for the
closure grep in `scripts/refinement/axiom-audit.sh`. `#print axioms` stays the authority on each
headline theorem; this sweep covers the rest of their modules.
-/

namespace SolidCore.Refinement.AxiomAudit

open Lean Elab Command

/-- The constants a declaration's type and value mention (an inductive's constructors are reached
through the constructors' own names). -/
def deps (ci : ConstantInfo) : Array Name :=
  let ty := ci.type.getUsedConstants
  match ci with
  | .defnInfo v => ty ++ v.value.getUsedConstants
  | .thmInfo v => ty ++ v.value.getUsedConstants
  | .opaqueInfo v => ty ++ v.value.getUsedConstants
  | _ => ty

/-- Every reachable constant's axioms, by an iterative depth-first pass with one memo. -/
def axiomsOf (env : Environment) (roots : Array Name) : Std.HashMap Name NameSet := Id.run do
  let mut memo : Std.HashMap Name NameSet := {}
  let mut stack : Array (Name × Bool) := roots.map (·, false)
  while 0 < stack.size do
    let (n, expanded) := stack.back!
    stack := stack.pop
    if memo.contains n then continue
    let some ci := env.find? n | memo := memo.insert n {}; continue
    let ds := deps ci
    if expanded then
      let mut acc : NameSet := if ci matches .axiomInfo _ then ({} : NameSet).insert n else {}
      for d in ds do
        for a in memo.getD d {} do acc := acc.insert a
      memo := memo.insert n acc
    else
      stack := stack.push (n, true)
      for d in ds do
        if !memo.contains d then stack := stack.push (d, false)
  return memo

def allowed : List Name := [`propext, `Classical.choice, `Quot.sound]

elab "#axiom_audit " out:str prefixes:str* : command => do
  let env ← getEnv
  let ps := prefixes.toList.map (·.getString)
  let mods := env.header.moduleNames
  let inScope (n : Name) : Bool := Id.run do
    let some i := env.getModuleIdxFor? n | return false
    let m := (mods[i.toNat]!).toString
    return ps.any (m.startsWith ·)
  let targets := env.constants.map₁.fold (init := #[]) fun acc n ci =>
    if !n.isInternal && inScope n && (ci matches .thmInfo _ || ci matches .defnInfo _) then
      acc.push n else acc
  let memo := axiomsOf env targets
  let mut bad := 0
  let mut thms := 0
  for n in targets do
    if env.find? n matches some (.thmInfo _) then thms := thms + 1
    let ax := memo.getD n {}
    let extra := ax.toList.filter (!allowed.contains ·)
    if !extra.isEmpty then
      bad := bad + 1
      logInfo m!"AXIOM-VIOLATION {n}: {extra}"
  logInfo m!"axiom sweep: {targets.size} declarations ({thms} theorems) under {ps}, {bad} with axioms outside [propext, Classical.choice, Quot.sound]"
  let sp ← getSrcSearchPath
  let mut lines := #[]
  for m in mods do
    match ← sp.findModuleWithExt "lean" m with
    | some p => lines := lines.push s!"{m} {p}"
    | none => lines := lines.push s!"{m} ?"
  IO.FS.writeFile out.getString (String.intercalate "\n" lines.toList ++ "\n")
  logInfo m!"closure: {mods.size} modules written to {out.getString}"

end SolidCore.Refinement.AxiomAudit

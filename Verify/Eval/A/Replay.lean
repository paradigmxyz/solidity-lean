import Lean

/-!
# Lane A: isolated kernel replay of a built module

    lake env lean --run Verify/Eval/A/Replay.lean <Module.Name> [<Module.Name> ...]

Imports each module's environment from its .olean (no elaboration, no tactic runs) and adds
every theorem the module declares to the kernel ONLY (`Kernel.Environment.addDeclCore`, the call
`#kernel_recheck` of `Verify.Eval.Common.Measure` uses), under a fresh name `<thm>._replay` with
the theorem's saved type and value. It times each one and the total, and reports each
theorem's axioms (`collectAxioms`) and a hash of its statement (`Expr.hash` of the type, with the
body of a `stmt`-style definition the type names, so two lanes proving the same `stmt` show the
same hash).

It then shows the same path rejects ill-typed terms, so a passing replay means the kernel
accepted the terms: (1) a theorem of the module whose value is swapped for the value of a
theorem of another type, and (2) `True` proved by `(0 : Nat)`. Any accepted ill-typed term, or any
rejected saved theorem, makes it exit 1.

Output: one JSON line per theorem (`{"replay":...}`), then one `{"replay_total":...}` line per
module, then the rejection lines.
-/

open Lean

/-- `MonadEnv` on a state of the environment, to run `collectAxioms` outside `CoreM`. -/
instance : MonadEnv (StateM Environment) where
  getEnv := get
  modifyEnv := modify

def stdAxioms : List Name := [`propext, `Classical.choice, `Quot.sound]

def jsonEsc (s : String) : String := (Json.str s).compress

/-- The statement hash: the type's `Expr.hash`, mixed with the value of the definition the type
is (when it is a constant of type `Prop`, such as a fixture's `stmt`). -/
def stmtHash (env : Environment) (ty : Expr) : UInt64 :=
  match ty with
  | .const c _ => match env.find? c with
    | some (.defnInfo d) => mixHash ty.hash d.value.hash
    | _ => ty.hash
  | _ => ty.hash

def ms (t0 t1 : Nat) : Float := (t1 - t0).toFloat / 1000000.0

def replayModule (env : Environment) (mod : Name) : IO (Bool × Option TheoremVal) := do
  let some idx := env.getModuleIdx? mod | throw <| IO.userError s!"module {mod} not imported"
  let data := env.header.moduleData[idx.toNat]!
  let kenv := env.toKernelEnv
  let mut total := 0.0
  let mut count := 0
  let mut ok := true
  let mut sample : Option TheoremVal := none
  for ci in data.constants do
    let .thmInfo tv := ci | continue
    if sample.isNone then sample := some tv
    let decl := Declaration.thmDecl { tv with name := tv.name ++ `_replay }
    let t0 ← IO.monoNanosNow
    let res := kenv.addDeclCore 0 100000 decl none
    let t1 ← IO.monoNanosNow
    let axs := ((collectAxioms tv.name : StateM Environment (Array Name)).run' env).run
    let axOk := axs.all (stdAxioms.contains ·)
    let (accepted, err) ← match res with
      | .ok _ => pure (true, "")
      | .error e => do pure (false, ← (e.toMessageData {}).toString)
    unless accepted && axOk do ok := false
    total := total + ms t0 t1
    count := count + 1
    IO.println s!"\{\"replay\":{jsonEsc tv.name.toString},\"module\":{jsonEsc mod.toString},\"kernel_replay_ms\":{ms t0 t1},\"accepted\":{accepted},\"axioms\":{(Json.arr (axs.map (Json.str ·.toString))).compress},\"axioms_ok\":{axOk},\"statement_hash\":\"{(stmtHash env tv.type).toNat}\",\"error\":{jsonEsc err}}"
  IO.println s!"\{\"replay_total\":{jsonEsc mod.toString},\"theorems\":{count},\"kernel_replay_ms\":{total},\"all_ok\":{ok}}"
  return (ok, sample)

/-- Adds `decl` to the kernel and reports whether it was rejected, as it must be. -/
def expectReject (env : Environment) (label : String) (decl : Declaration) : IO Bool := do
  match env.toKernelEnv.addDeclCore 0 100000 decl none with
  | .ok _ =>
    IO.println s!"\{\"reject_check\":{jsonEsc label},\"rejected\":false}"
    return false
  | .error e =>
    let msg ← (e.toMessageData {}).toString
    IO.println s!"\{\"reject_check\":{jsonEsc label},\"rejected\":true,\"error\":{jsonEsc (msg.take 200).toString}}"
    return true

def main (args : List String) : IO UInt32 := do
  if args.isEmpty then
    IO.eprintln "usage: lake env lean --run Verify/Eval/A/Replay.lean <Module> [<Module> ...]"
    return 2
  initSearchPath (← findSysroot)
  let mods := args.map String.toName
  let t0 ← IO.monoNanosNow
  let env ← importModules (mods.map ({ module := · })).toArray {} (trustLevel := 0) (loadExts := false)
  let t1 ← IO.monoNanosNow
  IO.println s!"\{\"import_ms\":{ms t0 t1}}"
  let mut ok := true
  let mut sample : Option TheoremVal := none
  for m in mods do
    let (o, s) ← replayModule env m
    ok := ok && o
    if sample.isNone then sample := s
  -- (1) a saved theorem whose value is swapped for a proof of another statement
  if let some tv := sample then
    let other := `Nat.lt_irrefl
    let some (.thmInfo ov) := env.find? other | throw <| IO.userError "no Nat.lt_irrefl"
    let bad := Declaration.thmDecl { tv with name := tv.name ++ `_swapped, value := ov.value }
    ok := (← expectReject env s!"{tv.name} with the value of {other}" bad) && ok
  -- (2) True proved by (0 : Nat)
  let bad := Declaration.thmDecl (mkTheoremValEx `verifyEvalReplayIllTyped [] (mkConst `True) (mkNatLit 0) [])
  ok := (← expectReject env "True proved by (0 : Nat)" bad) && ok
  return if ok then 0 else 1

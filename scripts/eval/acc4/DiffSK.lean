import Lean
open Lean
/-! Where the original and Skip proofs of evm4_run first differ. -/
partial def firstDiff (a b : Expr) (path : List Nat := []) : Option (List Nat × Expr × Expr) :=
  if a == b then none else
  match a, b with
  | .app f x, .app g y => (firstDiff f g (0 :: path)).orElse fun _ => firstDiff x y (1 :: path)
  | .lam _ t x _, .lam _ u y _ | .forallE _ t x _, .forallE _ u y _ =>
      (firstDiff t u (0 :: path)).orElse fun _ => firstDiff x y (1 :: path)
  | .letE _ t v x _, .letE _ u w y _ => ((firstDiff t u (0::path)).orElse fun _ => firstDiff v w (1::path)).orElse fun _ => firstDiff x y (2::path)
  | .mdata _ x, .mdata _ y => firstDiff x y (0 :: path)
  | _, _ => some (path, a, b)
unsafe def main (_ : List String) : IO UInt32 := do
  initSearchPath (← findSysroot); enableInitializersExecution
  let env ← importModules #[{module := `flag_4ce5cf9a.Proofs.Runs.Evm4}, {module := `Skip.Runs.Evm4}] {} (loadExts := true)
  let some (.thmInfo a) := env.find? `SolarTV.Milestone.Flag4ce5cf9a.evm4_run | return 1
  let some (.thmInfo b) := env.find? `SolarTV.Milestone.Flag4ce5cf9a.SK.evm4_run | return 1
  match firstDiff a.value b.value with
  | none => IO.println "equal"
  | some (p, x, y) =>
    IO.println s!"depth {p.length}"
    IO.println s!"orig: {(toString x).take 400}"
    IO.println s!"skip: {(toString y).take 400}"
  return 0

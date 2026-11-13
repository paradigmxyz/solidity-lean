import Contracts.ArrayMax.Proofs.ArrayMax.max
import Contracts.ArrayMax.Proofs.ArrayMax.clamp
import Contracts.ArrayMax.Proofs.ArrayMaxEntry.max

/-! Fails unless every theorem under `Contracts.ArrayMax.max`, `Contracts.ArrayMax.clamp`, `Contracts.ArrayMaxEntry.max` uses no axiom but `propext`,
`Classical.choice` and `Quot.sound`, and prints how many it checked. -/

open Lean Elab Command in
#eval show CommandElabM Unit from do
  let env ← getEnv
  let roots : List Name := [`Contracts.ArrayMax.max, `Contracts.ArrayMax.clamp, `Contracts.ArrayMaxEntry.max]
  let allowed : List Name := [`propext, `Classical.choice, `Quot.sound]
  let mut n := 0
  for (name, info) in env.constants.toList do
    unless roots.any (·.isPrefixOf name) do continue
    unless info matches .thmInfo _ do continue
    let axs ← Lean.collectAxioms name
    for a in axs do
      unless allowed.contains a do throwError "{name} uses axiom {a}"
    n := n + 1
  if n == 0 then throwError "no theorems found"
  IO.println s!"ArrayMax: {n} theorems, axioms within propext, Classical.choice, Quot.sound"

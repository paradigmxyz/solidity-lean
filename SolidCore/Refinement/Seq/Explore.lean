import SolidCore.Refinement.Seq.Check

/-!
# Exploring the storages a contract reaches

`explore` computes, by breadth-first search over SolidCore alone, the storages
reachable from the deployed storage by clean calls of a contract's functions, in
the canonical form `Seq.canon` gives them, deduplicated, level by level. It
also collects every slot any reached storage writes (`Plan.keys`), the keys
`canon` then lists.

It stops at the first of: no new storages (the closure, a closed plan), or a next
level that would push the storages past `maxStates` or the calls a check of every
level runs past `budget` (an open plan, whose levels bound the length of the
sequences it covers). `scripts/refinement/gen_proof.py` runs it once per
contract through `render` and writes its result into the generated certificate.
Nothing here is trusted: `Seq.refinesSeq_of_cert` and `Seq.refinesSeqUpTo_of_cert`
re-check the certificate against both semantics.
-/

namespace SolidCore.Refinement.Seq

open SolidCore.Solidity SolidCore.Refinement.Abi

/-- What `explore` found. -/
structure Plan where
  /-- Whether the levels are closed under every clean call. -/
  closed : Bool
  /-- The storages by level, the deployed one alone at level 0. -/
  levels : List (List (List (Nat × Nat)))
  /-- Every slot a reached storage holds a word for, sorted. -/
  keys : List Nat
  /-- The clean calls from one storage. -/
  callsPer : Nat

/-- The storages one clean call of `fns` from `σ` leaves, and the slots each holds a
word for. A call SolidCore does not finish gives nothing; the check refutes it. -/
def successors (fuel : Nat) (c : TypeCheck.CheckedContract) (fns : List Fn)
    (base : List Nat) (σ : List (Nat × Nat)) : List (List (Nat × Nat) × List Nat) :=
  (calls fns [σ]).filterMap fun call =>
    match Source.result? fuel c call with
    | some r =>
      let keys := normKeys (sourceKeys r.state ++ callKeys call ++ base)
      some (canon keys base (Source.observe call r), keys)
    | none => none

/-- Breadth-first search from the deployed storage `s0`, at most `rounds` levels deep. -/
def explore (fuel : Nat) (c : TypeCheck.CheckedContract) (fns : List Fn)
    (s0 : List (Nat × Nat)) (maxStates budget rounds : Nat) : Plan := Id.run do
  let base := s0.map (·.1)
  let per := (calls fns [s0]).length
  let cap := min maxStates (budget / max per 1)
  let mut seen : Std.HashSet (List (Nat × Nat)) := Std.HashSet.emptyWithCapacity.insert s0
  let mut levels : Array (List (List (Nat × Nat))) := #[[s0]]
  let mut keys : List Nat := normKeys base
  let mut total := 1
  for _ in [0:rounds] do
    let last := levels.back!
    let mut fresh : Array (List (Nat × Nat)) := #[]
    let mut over := false
    let mut newKeys := keys
    for σ in last do
      if over then break
      for (σ', ks) in successors fuel c fns base σ do
        newKeys := ks ++ newKeys
        if !seen.contains σ' then
          seen := seen.insert σ'
          fresh := fresh.push σ'
          if total + fresh.size > cap then
            over := true
            break
    if over then
      return { closed := false, levels := levels.toList, keys, callsPer := per }
    keys := normKeys newKeys
    if fresh.isEmpty then
      return { closed := true, levels := levels.toList, keys, callsPer := per }
    total := total + fresh.size
    levels := levels.push fresh.toList
  return { closed := false, levels := levels.toList, keys, callsPer := per }

/-- The plan as text for the generator: `closed` or `open`, the calls per storage, the
keys, then one line per level after the first, storages separated by `;` and pairs
by `,` as `slot:value`. -/
def Plan.render (p : Plan) : String :=
  let pairs (σ : List (Nat × Nat)) := ",".intercalate (σ.map fun kv => s!"{kv.1}:{kv.2}")
  let lines := p.levels.drop 1 |>.map fun level => ";".intercalate (level.map pairs)
  "\n".intercalate ([if p.closed then "closed" else "open", toString p.callsPer,
    " ".intercalate (p.keys.map toString)] ++ lines.map (s!"L {·}"))

end SolidCore.Refinement.Seq

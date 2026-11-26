import Lean
open Lean

def main (args : List String) : IO Unit := do
  let [a, b] := args | throw <| IO.userError "usage: OleanDiff A.olean B.olean"
  let (da, _) ← readModuleData a
  let (db, _) ← readModuleData b
  IO.println s!"constants {da.constNames.size} vs {db.constNames.size}"
  let ma : Std.HashMap Name ConstantInfo := da.constNames.zip da.constants |>.foldl (fun m (n, c) => m.insert n c) {}
  let mb : Std.HashMap Name ConstantInfo := db.constNames.zip db.constants |>.foldl (fun m (n, c) => m.insert n c) {}
  for n in da.constNames do
    match mb.get? n with
    | none => IO.println s!"only in A: {n}"
    | some cb =>
      let ca := ma.get! n
      if ca.type != cb.type then IO.println s!"type differs: {n}"
      if ca.value? != cb.value? then IO.println s!"value differs: {n}"
  for n in db.constNames do
    if !ma.contains n then IO.println s!"only in B: {n}"
  let oa := da.constNames.toList.map toString
  let ob := db.constNames.toList.map toString
  if oa != ob then IO.println "constant order differs"
  IO.println s!"extension entries {da.entries.size} vs {db.entries.size}"
  for (ea, eb) in da.entries.zip db.entries do
    if ea.1 != eb.1 then IO.println s!"extension name order differs: {ea.1} vs {eb.1}"
    else if ea.2.size != eb.2.size then IO.println s!"extension {ea.1}: {ea.2.size} vs {eb.2.size} entries"

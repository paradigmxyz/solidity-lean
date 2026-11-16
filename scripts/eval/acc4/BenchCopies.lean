import flag_4ce5cf9a.SpecConnect
open Lean
run_meta do
  let env ← getEnv
  let pl := `Certified.flag_4ce5cf9a.Lowering.kernel.using_selector_eq
  let ps := `flag_4ce5cf9a.SpecConnect.kernel.using_selector_eq_mkIdx_eq
  let mut l : Std.HashSet String := {}
  let mut s : Array String := #[]
  for (n, _) in env.constants.toList do
    if pl.isPrefixOf n then l := l.insert ((n.replacePrefix pl .anonymous).toString)
    if ps.isPrefixOf n then s := s.push ((n.replacePrefix ps .anonymous).toString)
  let both := s.filter l.contains
  logInfo m!"Lowering using_selector_eq copies {l.size}; SpecConnect using_selector_eq_mkIdx_eq copies {s.size}; same suffix in both {both.size}"

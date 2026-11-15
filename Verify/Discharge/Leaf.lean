import Verify.Discharge.Search
import Verify.Discharge.Sat.Ground
import Verify.Discharge.Nonlinear

/-! The search's leaves (`vc_leaf`, Search.lean): besides `omega`, a goal one of whose closed
hypotheses the kernel decides to be false is closed by `vc_ground` (Sat/Ground.lean). Lean tries
the rules from the last one added, so `vc_ground` runs first and fails at once when no hypothesis
is closed; `omega` then gets the goal unchanged. -/

macro_rules | `(tactic| vc_leaf) => `(tactic| vc_ground)

namespace SolarVerify.Discharge

/-- The search's goals spell SMT-LIB's `div` and `mod` as `Int.ediv` and `Int.emod`, which
`omega` reads as atoms; these turn them back into `/` and `%`, which it understands. -/
theorem ediv_eq_div (a b : Int) : a.ediv b = a / b := rfl

theorem emod_eq_mod (a b : Int) : a.emod b = a % b := rfl

end SolarVerify.Discharge

/-! A goal with `div` or `mod` gets `omega` after `ediv_eq_div` and `emod_eq_mod`; without them
`simp` fails and the rules above take the goal unchanged. -/

/-- `omega` after reading `Int.ediv` and `Int.emod` as `/` and `%`. -/
macro "vc_div_omega" : tactic => `(tactic| (
  simp only [SolarVerify.Discharge.ediv_eq_div, SolarVerify.Discharge.emod_eq_mod] at *
  omega))

macro_rules | `(tactic| vc_leaf) => `(tactic| vc_div_omega)

/-! A goal with a product of variables or a division by one gets `omega` with the facts
`vc_nl_facts` adds (Nonlinear.lean); without such a term `vc_nl_facts` fails and the rules above
take the goal unchanged. -/

/-- `omega` with the nonlinear facts of Nonlinear.lean. -/
macro "vc_nl_omega" : tactic => `(tactic| (
  try simp only [SolarVerify.Discharge.ediv_eq_div, SolarVerify.Discharge.emod_eq_mod] at *
  vc_nl_facts
  omega))

macro_rules | `(tactic| vc_leaf) => `(tactic| vc_nl_omega)

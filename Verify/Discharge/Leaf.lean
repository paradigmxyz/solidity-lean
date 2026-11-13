import Verify.Discharge.Search
import Verify.Discharge.Sat.Ground

/-! The search's leaves (`vc_leaf`, Search.lean): besides `omega`, a goal one of whose closed
hypotheses the kernel decides to be false is closed by `vc_ground` (Sat/Ground.lean). Lean tries
the rules from the last one added, so `vc_ground` runs first and fails at once when no hypothesis
is closed; `omega` then gets the goal unchanged. -/

macro_rules | `(tactic| vc_leaf) => `(tactic| vc_ground)

import Verify.Obligation
import Verify.Discharge.Lemmas
import Verify.Discharge.Search
import Verify.Discharge.Valid
import Verify.Discharge.Sat
import Verify.Discharge.Leaf

/-! Kernel-checked certificates for exported obligations. A VC counts as discharged only when a
certificate the Lean kernel checks proves `ob.Valid` (Verify/Obligation/Vc.lean), and the proof
uses only the axioms `propext`, `Classical.choice` and `Quot.sound`. The certificate kinds are:

- `search`: `vc_valid` (`Search`, `Valid`) builds the proof itself; its leaves are `omega` and
  `vc_ground`, which decides closed hypotheses by kernel evaluation (`Sat.Ground`, `Leaf`).
- `smt`: `vc_smt` (Verify/Reconstruct, a package of its own) reconstructs a cvc5 proof step by
  step as a Lean term.
- `lean`: a theorem written for the obligation, such as one under Contracts/<Contract>/, named in
  a certificate list; its proof may check an LRAT certificate with `Sat` (`check_sound`).

The driver, Verify/Discharge/discharge.sh, states every obligation itself and applies every
check to every kind alike; see Verify/Discharge/README.md. -/

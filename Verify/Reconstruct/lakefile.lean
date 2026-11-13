import Lake
open Lake DSL

-- cvc5 proof reconstruction for exported VCs (`vc_smt`, Tactic.lean), a package of its own so
-- that building solidity-lean fetches no solver. It builds the obligation and discharge
-- modules from this repository's sources (srcDir "../..") rather than requiring the root
-- package, whose Mathlib and EVM dependencies it does not need.
require smt from git "https://github.com/ufmg-smite/lean-smt.git" @ "6b26285ece45e38fc0d21809b944522233039829"

package verify_reconstruct where
  leanOptions := #[⟨`maxHeartbeats, (200000 : Nat)⟩, ⟨`backward.do.legacy, false⟩]

@[default_target]
lean_lib VerifyReconstruct where
  srcDir := "../.."
  roots := #[`Verify.Obligation, `Verify.Discharge, `Verify.Reconstruct.Tactic]

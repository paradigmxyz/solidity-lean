# Verify/VC

VC generation: solar-verify's SMT-LIB fragment, its meaning and the bridge to SolidCore runs.
The module list and what each proves are in [../VC.lean](../VC.lean)'s header.

- Generate VCs here; discharge them in `Verify/Discharge`. Don't add proof search to this
  directory, and don't change the semantics of `Term` to make a VC easier.
- `Verify/Obligation/Smt.lean` and `Vc.lean` are hashed into frozen manifests: editing them
  means regenerating and re-checking those manifests in the same change (README, "Follow-ups").
- Symbolic normalization of terms goes through one shared simplifier, preferring
  `Lean.Meta.Sym` ([Sym/Simp.lean](https://github.com/leanprover/lean4/blob/v4.35.0/src/Lean/Meta/Sym/Simp.lean)), not a new ad hoc `simp` set.
- Decide bounded checks (`checkScript`) by kernel computation (`cbv`, `decide`), never
  `native_decide`.

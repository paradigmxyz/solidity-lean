# Lane C: a SymM backward-rule EVM stepper

Status: in progress (this file is updated as receipts land). Toolchain v4.35.0, base 6dd035dc.
All checks ran through `scripts/eval/check.sh C …` (receipts in `~/eval-receipts.jsonl`, logs in
`~/eval-logs/*-C-*.log`).

## What was built

| File | What |
| --- | --- |
| `Verify/Eval/C/gen_rules.py` → `Rules.lean` | 83 fused one-opcode rules over a code stored as one number (`NatCode.ofNat n size`): each is EthLib's rule for the opcode with `Triple.seq` already applied, concluding `Hoare .fusaka (At (ofNat n size) msg pc stack mem gas st ss rd) R` for any `R`. Premises are facts on literals (`pc + k < size`, `n >>> (8 * (size - 1 - pc)) % 256 = byte`, PUSH data as a `BitVec.ofNat` of a shift/mod), gas (`c ≤ gas`), stack room, and for jumps `walk n size size 0 d = true` plus the JUMPDEST byte. DUPk/SWAPk match explicit cons cells, so no premise indexes a list. JUMPI has three rules: `step_jumpi_zero` / `step_jumpi_taken` (a premise decides) and `step_jumpi_split` (Symex's `jumpi_split` over a NatCode: both continuations, each under its path condition). Terminal rules: REVERT of 0 bytes (`Reverted` or `Done`), STOP (`Done`), and `at_close` (reach a stated frame). |
| `Verify/Eval/C/Stepper.lean` | `evm_sym [code eqns] (using [rewrites])?`: a SymM/GrindM driver. Reads the opcode byte off the literal code number only to pick the rule; applies it with `Sym.BackwardRule.apply` (via `Grind.Goal.apply`); proves every premise (Sym.simp with `evalGround` + `simpControl` + 4 rewrite rules; assumption; kernel-evaluated `Eq.refl true` for `walk` after evaluating it in meta code; else `grind` in the goal's own state); normalizes the next frame with Sym.simp whose persistent cache is threaded through the whole run. Options: `verify.eval.c.fresh` (experiment 1 control), `eager` (refute every split child), `shareCache`, `condRewrite` (ISZERO conditional rewrites discharged by grind through `Goal.mkSymSimpDischarger`), `stats`, `debug`. |
| `Verify/Eval/C/W1.lean` | the two W1 targets, each a `def` proved by the baseline and by `evm_sym` |
| `Verify/Eval/C/Isolation.lean` | sibling-isolation negative tests (`#guard_msgs` pins the one open path) + positive controls |
| `Verify/Eval/C/gen_fixtures.py` → `Fix/*` | scaling fixtures: Straight, Shared (repeated subterms), Branch (decided + genuine splits), 16…256 opcodes; `<K><N>Stmt.lean` holds the statement once, `Base`/`Sym` prove it |
| `Verify/Eval/C/GenC1.lean` | pilot on a generated end-to-end VC (c1's dirty-argument theorem) |
| `run_fixtures.sh`, `summarize.py` | runner (one check.sh slot at a time) and summary |

## Soundness notes

* The byte read in meta code only selects a rule; the rule's own premise re-proves the byte.
* Infeasible branches are closed only by a proof: the E-graph finding the internalized path
  condition inconsistent (grind's `closeGoal` assigns a `False.elim` proof), `grind` on `False` in
  the branch's own state, or `exfalso; symex_omega` (Symex's kernel-checked bv_omega chain).
  `simpControl` only selects `ite` branches whose condition evaluates to a literal.
* `walk` premises get `Eq.refl true`, checked by the kernel by evaluation (what `decide +kernel` does).
* No `bv_decide`, `native_decide` or `sorry` in the stepper's proofs; `#print axioms` is in each file.

import Contracts.UniswapV2.PairSpec.Published
import Contracts.UniswapV2.PairSpec.SpecWrongK

/-!
# UniswapV2Pair: the binding and the negative controls

* `bound`: the export is the bytes of solar's plain compile, decided by the kernel.
* **Altered jump** (`altered_not_bound`): the bytes with the first `PUSH2 t; JUMP`/`JUMPI`
  target moved by one are not the export, so a statement over them fails at its binding, by
  mismatch (the kernel decides the inequality), never by a timeout.
* **Wrong K** (`wrongK_rejects`): the specification with swap's fee-adjusted constant-product
  clause at a fee of 4/1000 instead of 3/1000 (SpecWrongK.lean, the same export with one
  constant mutated) rejects the observable of a swap the pair performs (reserves 10000/10000,
  1000 of token0 in, 906 of token1 out: `swap(0, 906, to, "")`), which the published
  specification accepts (`swap_k_holds`).
* **Missing reserve update** (`noUpdate_rejected`): the published specification rejects the
  observable of a swap that pays 906 of token1 out but leaves the reserves as they were.

The last two are about the specification's formulas on concrete states (the one clause each
control changes or breaks); that the pair's bytecode produces the first observable, and a pair
without `_update` the second, is not proved here (the stage theorems would say so of every run).
The driver's own controls (tools/certify/final_neg.sh: a proof of the published statement does
not check against a statement with a wrong postcondition, a substituted bytecode or a dropped
premise) apply to this statement unchanged.
-/

namespace SolidCore.Spec.UniswapV2.PairSpec.Negative

open SolarTV SolidCore.Refinement SolidCore.Spec SolidCore.Spec.UniswapV2.PairSpec

/-! ## The binding and an altered jump -/

set_option maxRecDepth 100000 in
/-- The export is the bytes of the plain compile. -/
theorem bound : Bound :=
  @of_decide_eq_true _ (instDecidableEqList _ _) (by decide +kernel)

/-- The bytes with the first `PUSH2 t; JUMP` or `PUSH2 t; JUMPI` target moved by one. -/
def alterJump : List Nat → List Nat
  | 0x61 :: hi :: lo :: 0x56 :: rest => 0x61 :: hi :: ((lo + 1) % 256) :: 0x56 :: rest
  | 0x61 :: hi :: lo :: 0x57 :: rest => 0x61 :: hi :: ((lo + 1) % 256) :: 0x57 :: rest
  | b :: rest => b :: alterJump rest
  | [] => []

set_option maxRecDepth 100000 in
/-- The alteration changes the bytes. -/
theorem alterJump_changes : alterJump runtimeBytes ≠ runtimeBytes := by decide +kernel

set_option maxRecDepth 100000 in
/-- **Altered jump**: the export is not the altered bytes. -/
theorem altered_not_bound : ¬ (code.data.toList.map (·.toNat) = alterJump runtimeBytes) := by
  rw [bound]
  exact alterJump_changes.symm

/-! ## Wrong K and a missing reserve update -/

/-- swap's spec in a bundle. -/
def swapSpec (b : Bundle) : FnSpec :=
  (b.spec.specs.find? fun fs => fs.name == "UniswapV2Pair.swap").getD default

/-- Its first ensures clause: the fee-adjusted constant product. -/
def kClause (b : Bundle) : Term := (swapSpec b).ensures.headD (.lit 0)

/-- The reserves word of slot 8: `reserve0` in the low 14 bytes, `reserve1` in the next 14. -/
def reserves (r0 r1 : Nat) : Nat := r0 + r1 * 2 ^ 112

/-- A state with reserves `r0`, `r1` and nothing else in storage. -/
def st (r0 r1 : Nat) : State :=
  { storage := fun s => if s = 8 then reserves r0 r1 else 0, ghost := Ghost.zero, time := 0 }

/-- The environment of `swap(0, out1, 0x3000, "")` from reserves 10000/10000 to `post`. -/
def envOf (out1 : Nat) (post : State) : Env :=
  mkEnv { sender := 0x2000, value := 0, timestamp := 1, self := 0x1000 } [0, out1, 0x3000, 0x80] []
    (st 10000 10000) post

/-- **The published K clause holds of the swap the pair performs**: 1000 of token0 in, 906 of
token1 out, from reserves 10000/10000 to 11000/9094. -/
theorem swap_k_holds :
    SolidCore.Spec.Export.UniswapV2Pair.UniswapV2Pair.sat
      (kClause SolidCore.Spec.Export.UniswapV2Pair.UniswapV2Pair) (envOf 906 (st 11000 9094)) := by
  have hk : kClause SolidCore.Spec.Export.UniswapV2Pair.UniswapV2Pair = (SolidCore.Spec.Export.UniswapV2Pair.UniswapV2Pair.spec.specs[8]'(by decide)).ensures[0]'(by decide) := rfl
  rw [hk]
  simp [Bundle.sat, SolidCore.Spec.Export.UniswapV2Pair.UniswapV2Pair, eval, BinOp.apply, envOf, st, mkEnv, Env.cur, slotOf, reserves,
    Ty.ofBits, toWord]

/-- **Wrong K**: the mutant clause (fee 4/1000) rejects that swap. -/
theorem wrongK_rejects :
    ¬ SolidCore.Spec.Export.UniswapV2PairWrongK.UniswapV2Pair.sat
      (kClause SolidCore.Spec.Export.UniswapV2PairWrongK.UniswapV2Pair) (envOf 906 (st 11000 9094)) := by
  have hk : kClause SolidCore.Spec.Export.UniswapV2PairWrongK.UniswapV2Pair = (SolidCore.Spec.Export.UniswapV2PairWrongK.UniswapV2Pair.spec.specs[8]'(by decide)).ensures[0]'(by decide) := rfl
  rw [hk]
  simp [Bundle.sat, SolidCore.Spec.Export.UniswapV2PairWrongK.UniswapV2Pair, eval, BinOp.apply, envOf, st, mkEnv, Env.cur, slotOf, reserves,
    Ty.ofBits, toWord]

/-- **Missing reserve update**: the published K clause rejects a swap that pays 906 of token1 out
and leaves the reserves at 10000/10000. -/
theorem noUpdate_rejected :
    ¬ SolidCore.Spec.Export.UniswapV2Pair.UniswapV2Pair.sat
      (kClause SolidCore.Spec.Export.UniswapV2Pair.UniswapV2Pair) (envOf 906 (st 10000 10000)) := by
  have hk : kClause SolidCore.Spec.Export.UniswapV2Pair.UniswapV2Pair = (SolidCore.Spec.Export.UniswapV2Pair.UniswapV2Pair.spec.specs[8]'(by decide)).ensures[0]'(by decide) := rfl
  rw [hk]
  simp [Bundle.sat, SolidCore.Spec.Export.UniswapV2Pair.UniswapV2Pair, eval, BinOp.apply, envOf, st, mkEnv, Env.cur, slotOf, reserves,
    Ty.ofBits, toWord]

/-- info: 'SolidCore.Spec.UniswapV2.PairSpec.Negative.altered_not_bound' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms altered_not_bound

/-- info: 'SolidCore.Spec.UniswapV2.PairSpec.Negative.swap_k_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms swap_k_holds

/-- info: 'SolidCore.Spec.UniswapV2.PairSpec.Negative.wrongK_rejects' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms wrongK_rejects

/-- info: 'SolidCore.Spec.UniswapV2.PairSpec.Negative.noUpdate_rejected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms noUpdate_rejected

end SolidCore.Spec.UniswapV2.PairSpec.Negative


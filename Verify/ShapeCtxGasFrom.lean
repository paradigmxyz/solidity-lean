import Verify.ShapeCtxGas
import SolidCore.Refinement.Solar.AssembleCtxGasFrom

/-!
# Resources from any caller, through the checker with contexts and gas

`Shapes.Resources` speaks of `Final.Target.runWith`, one message from the fixed account
`callerAddress`. `ResourcesFrom` asks the same of every caller: for every account `a` below
`2 ^ 160` but the contract's own, every valid call and every gas from the bound `G call` on (below
`2 ^ 256`), EthLib's run of the exact bytecode from `a` (`Final.Target.runWithFrom a`) is the source's
run of the call from `a`. At `callerAddress` it gives `Resources` (`ResourcesFrom.resources`).

* `gasEdge_ofXL` is the gas edge on its own (E8): from the checker with contexts and gas on the
  exact bytecode, and the guard stage (no valid call enters a block the checker leaves unchecked),
  for every caller and every oracle whose CALLER is that caller and whose Keccak-256 is EthLib's,
  at every gas from `gasBoundL cx.base N` on the bytecode's result is the final EVM IR's result.
  Its premises are about programs only (the checker's verdict and two symbolic runs of the EVM
  IR); none of them mentions gas or EthLib's result, so the bound is not assumed.
* `resourcesFrom_ofXL` composes it with a source stage per caller (the functional edges E3 and E4,
  proved elsewhere and taken here as the named hypothesis `stage`) into `ResourcesFrom`.
-/

namespace SolidCore.Refinement.Shapes

open SolarTV SolidCore.Refinement SolidCore.Refinement.Final SolidCore.Refinement.Solar

/-- The oracle of a call from the account `a`: `oracle` with CALLER `a`. -/
def oracleFrom (a : Nat) : Machine.Oracle := { oracle with caller := BitVec.ofNat 160 a }

theorem oracleFrom_ok {a : Nat} (ha : a < 2 ^ 160) : AssembleLoop.OracleOkAt a (oracleFrom a) := by
  refine ⟨?_, oracle_ok.1.2⟩
  apply BitVec.eq_of_toNat_eq
  rw [Assemble.address_toNat ha]
  show ((BitVec.ofNat 160 a).setWidth 256).toNat = a
  rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt (by omega)]

/-- At `callerAddress` it is `oracle`'s caller. -/
theorem oracleFrom_callerAddress_ok : AssembleLoop.OracleOkAt callerAddress (oracleFrom callerAddress) :=
  oracleFrom_ok (by decide)

/-- **Resources from any caller.** -/
def ResourcesFrom (run : Nat → Call → Option Observable) (code : ByteArray) (Valid : Call → Prop)
    (G : Call → Nat) : Prop :=
  ∀ a, a < 2 ^ 160 → a ≠ selfAddress → ∀ call, Valid call → G call < 2 ^ 64 ∧
    ∀ gas, G call ≤ gas → gas < 2 ^ 256 → Final.Target.runWithFrom a gas code call = run a call

/-- At `callerAddress`, `ResourcesFrom` is `Resources`. -/
theorem ResourcesFrom.resources {S : Sem} {p : S.Prog} {code : ByteArray} {Valid : Call → Prop}
    {G : Call → Nat} {run : Nat → Call → Option Observable} (h : ResourcesFrom run code Valid G)
    (hrun : run callerAddress = S.run p) : Resources S p code Valid G := fun call hc => by
  obtain ⟨hG, hr⟩ := h callerAddress (by decide) (by decide) call hc
  refine ⟨hG, fun gas h1 h2 => ?_⟩
  rw [← hrun, ← Final.Target.runWithFrom_callerAddress]
  exact hr gas h1 h2

/-- **The gas edge from any caller.** -/
theorem gasEdge_ofXL {q : Assemble.Program} {F : List Nat} {code : ByteArray}
    {cx : AssembleCtx.CtxCert} {N : Nat} {Valid : Call → Prop}
    (asm : AssembleCtxGas.checkXL F q code cx = true) (hreads : cx.base.reads = false)
    (ends : ∀ o call, Valid call →
      (EVM.Program.run o (AssembleCtxGas.guard F q) call N).isSome = true)
    (guard_run : ∀ o call, Valid call →
      EVM.Program.run o q call N = EVM.Program.run o (AssembleCtxGas.guard F q) call N) :
    ∀ a, a < 2 ^ 160 → a ≠ selfAddress → ∀ o, AssembleLoop.OracleOkAt a o → ∀ call, Valid call →
      ∀ gas, AssembleLoop.gasBoundL cx.base N ≤ gas →
        ∃ obs, (evmirSem o).run q call = some obs ∧ Final.Target.runWithFrom a gas code call = some obs := by
  intro a ha hne o ho call hc gas hg
  obtain ⟨r, hr⟩ := Option.isSome_iff_exists.mp (ends o call hc)
  refine ⟨_, evmir_run_of_iterate ((guard_run o call hc).trans hr), ?_⟩
  exact AssembleCtxGas.forward_of_checkXLFrom asm a (Assemble.address_ne_self ha hne) o (fun _ => ho)
    (fun h => absurd h (by simp [hreads])) call N r hr hg

/-- **Resources from any caller, from a source stage per caller and the gas edge.** -/
theorem resourcesFrom_ofXL {q : Assemble.Program} {F : List Nat} {code : ByteArray}
    {cx : AssembleCtx.CtxCert} {N : Nat} {Valid : Call → Prop} {run : Nat → Call → Option Observable}
    (total : ∀ a, a < 2 ^ 160 → a ≠ selfAddress → ∀ call, Valid call → ∃ obs, run a call = some obs)
    (stage : ∀ a, a < 2 ^ 160 → a ≠ selfAddress → ∀ call, Valid call → ∀ obs, run a call = some obs →
      (evmirSem (oracleFrom a)).run q call = some obs)
    (asm : AssembleCtxGas.checkXL F q code cx = true) (hreads : cx.base.reads = false)
    (ends : ∀ o call, Valid call →
      (EVM.Program.run o (AssembleCtxGas.guard F q) call N).isSome = true)
    (guard_run : ∀ o call, Valid call →
      EVM.Program.run o q call N = EVM.Program.run o (AssembleCtxGas.guard F q) call N)
    (hG : AssembleLoop.gasBoundL cx.base N < 2 ^ 64) :
    ResourcesFrom run code Valid (fun _ => AssembleLoop.gasBoundL cx.base N) := by
  intro a ha hne call hc
  refine ⟨hG, fun gas h1 _ => ?_⟩
  obtain ⟨obs, hq, hb⟩ := gasEdge_ofXL asm hreads ends guard_run a ha hne (oracleFrom a)
    (oracleFrom_ok ha) call hc gas h1
  obtain ⟨obs0, h0⟩ := total a ha hne call hc
  have := stage a ha hne call hc obs0 h0
  rw [hq] at this
  cases this
  rw [hb, h0]

/-- info: 'SolidCore.Refinement.Shapes.resourcesFrom_ofXL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms resourcesFrom_ofXL

end SolidCore.Refinement.Shapes

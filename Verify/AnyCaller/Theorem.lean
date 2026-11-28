import SolidCore.Refinement.Generic.Value
import SolidCore.Refinement.Solar.AssembleCtxGasFrom
import SolidCore.Refinement.Keccak.TwoWords
import Verify.Generic.Expected
import Verify.AnyCaller.Context

/-!
# Generic any-caller equivalence

For every account `a < 2 ^ 160` other than the contract, every call of the scope (any function of
`fns`, any argument words, any value, any storage writing the deployed slots) and every gas from the
bound on, EthLib's run of the exact bytecode sent by `a` is SolidCore's run of the source sent by `a`:

    Final.Target.runWithFrom a gas code call = (solidCoreFrom a fuel).run c call

(`bytes_eq_source_from`), and in `Expected`'s terms, for every real context `ctx`,
`runAt ctx gas (runtimeCode bytes) call = (src.semAt ctx).run c call` (`runAt_eq_semAt`). Both sides
are observables (status, return or revert data, storage, logs).

It is proved once, not per caller: the source stage is `Generic.stageAtValueFrom` (the module checked
by `checkSym` and `checkValue ... .allSym` with the caller a symbolic word), the backend is a stage
from the module to the final EVM IR under every oracle, and the bytes are `AssembleCtxGas.checkXL`'s,
run from `a` by `forward_of_checkXLFrom`. The only oracle the proof picks is `oracleAt a` (EthLib's
Keccak-256, `CALLER` = `a`), which meets what both halves ask (`oracleAt_okAt`, `fromOk_of_okAt`).

What fails closed: a caller of 160 bits or more has no oracle at all (`not_fromOk_of_wide`), the
contract's own address is no real context (`not_ok_self`), and a module whose `CALLER` read is not the
source's `msg.sender` fails `checkSym` (Verify/AnyCaller/Tests.lean).
-/

namespace SolidCore.Verify.AnyCaller

open SolarTV SolarTV.MIR.Lowered SolidCore.Refinement SolidCore.Refinement.Solar
open SolidCore.Refinement.Generic

/-- The calls the statement covers: every function of `fns`, any argument words below `2 ^ 256`,
any value below `2 ^ 256`, from any storage that writes every slot of `s`. -/
def scope (s : List (Nat × Nat)) (fns : List Abi.Fn) (call : Call) : Prop :=
  ∃ σ v, Covers s σ ∧ fullScopeValue fns σ v call

/-- The oracle of a call sent by `a`: EthLib's Keccak-256, and `a` as `CALLER`. -/
def oracleAt (a : Nat) : Machine.Oracle :=
  { Assemble.ethOracle
      { env := fun _ _ _ => 0, result := fun _ => 0, storageAfter := fun _ _ => 0,
        transientAfter := fun _ _ => 0, keccak := fun _ => 0, caller := 0 } with
    caller := BitVec.ofNat 160 a }

/-- `oracleAt a` is what the bytecode side asks of an oracle for the caller `a`. -/
theorem oracleAt_okAt {a : Nat} (ha : a < 2 ^ 160) : AssembleLoop.OracleOkAt a (oracleAt a) := by
  refine ⟨?_, fun _ => rfl⟩
  apply BitVec.eq_of_toNat_eq
  rw [Assemble.address_toNat ha]
  show ((BitVec.ofNat 160 a).setWidth 256).toNat = a
  rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt (by omega)]

/-- What the bytecode side asks of an oracle for `a` gives what the source stage asks. -/
theorem fromOk_of_okAt {a : Nat} (ha : a < 2 ^ 160) {o : Machine.Oracle}
    (h : AssembleLoop.OracleOkAt a o) : FromOk a o where
  caller := by rw [h.1]; exact Assemble.address_toNat ha
  hash := fun x y _ _ => by rw [h.2]; exact Keccak.ethKeccak_twoWords x y

/-- **A caller of 160 bits or more fails closed**: no oracle has it as its caller, so no stage, and
no statement, is about it. -/
theorem not_fromOk_of_wide {a : Nat} (ha : 2 ^ 160 ≤ a) (o : Machine.Oracle) : ¬ FromOk a o := by
  intro h
  have hc := h.caller
  have hlt : o.caller.toNat < 2 ^ 160 := o.caller.isLt
  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_trans hlt (by decide))] at hc
  rw [hc] at hlt
  exact absurd ha (Nat.not_le.mpr hlt)

/-- **The contract's own address is no real context.** -/
theorem not_ok_self : ¬ SolidCore.Verify.Generic.Context.Ok ⟨selfAddress⟩ :=
  fun h => h.2 rfl

theorem evmir_run_of_run {o : Machine.Oracle} {q : Assemble.Program} {call : Call} {N : Nat}
    {r : Machine.Halt × Machine.State} (h : EVM.Program.run o q call N = some r) :
    (evmirSem o).run q call = some (Machine.observe call r.2 r.1) := by
  change (SolarTV.EVM.Program.layer.result o q call).map _ = _
  rw [SolarTV.EVM.Program.layer.result_of_ends ⟨N, h⟩]
  rfl

/-- **Generic any-caller equivalence.** A checked contract whose constructor leaves the storage
entries `s` and no logs, a lowered MIR module that `checkSym` and `checkValue ... .allSym` accept,
backend stages from it to the final EVM IR `q` under every oracle, and the checker with contexts and
gas on the exact bytecode give: for every account `a < 2 ^ 160` but the contract's, every call of the
scope and every gas from the bound on, EthLib's run of the bytes sent by `a` is SolidCore's run of
the source sent by `a`. -/
theorem bytes_eq_source_from {fuel mirFuel : Nat} {c : SolidCore.Solidity.TypeCheck.CheckedContract}
    {d : SolidCore.Solidity.Source.State} {s : List (Nat × Nat)} (hd : Wide.DeployedAt fuel c d s)
    {m : Module} {fns : List Abi.Fn} (hchk : checkSym fuel mirFuel c.core m fns = true)
    (hval : checkValue mirFuel c.core m fns .allSym = true) {q : Assemble.Program}
    (backend : ∀ o, Stage (moduleSem o) (evmirSem o) m q (scope s fns))
    {F : List Nat} {code : ByteArray} {cx : AssembleCtx.CtxCert} {N : Nat}
    (asm : AssembleCtxGas.checkXL F q code cx = true) (hreads : cx.base.reads = false)
    (ends : ∀ o call, scope s fns call →
      (EVM.Program.run o (AssembleCtxGas.guard F q) call N).isSome = true)
    (guard_run : ∀ o call, scope s fns call →
      EVM.Program.run o q call N = EVM.Program.run o (AssembleCtxGas.guard F q) call N) :
    ∀ a, a < 2 ^ 160 → a ≠ selfAddress → ∀ call, scope s fns call →
      ∀ gas, AssembleLoop.gasBoundL cx.base N ≤ gas →
        Final.Target.runWithFrom a gas code call = (solidCoreFrom a fuel).run c call := by
  intro a ha hne call hc gas hg
  have hok := oracleAt_okAt ha
  obtain ⟨r, hr⟩ := Option.isSome_iff_exists.mp (ends (oracleAt a) call hc)
  have hq := evmir_run_of_run ((guard_run (oracleAt a) call hc).trans hr)
  have hb := AssembleCtxGas.forward_of_checkXLFrom asm a (Assemble.address_ne_self ha hne)
    (oracleAt a) (fun _ => hok) (fun h => absurd (hreads ▸ h) (by decide)) call N r
    ((guard_run (oracleAt a) call hc).symm.trans ((guard_run (oracleAt a) call hc).trans hr)) hg
  obtain ⟨obs, h0⟩ := Option.isSome_iff_exists.mp (definedValueFrom a ha hd hchk hval call hc)
  have hm := backend (oracleAt a) call hc obs
    (stageAtValueFrom a ha (oracleAt a) (fromOk_of_okAt ha hok) hd hchk hval call hc obs h0)
  rw [hq] at hm
  cases hm
  rw [hb]
  exact h0.symm

/-- **The same in `Expected`'s terms**: in every real context, the bytes' run is the source's. -/
theorem runAt_eq_semAt (src : SolidCore.Verify.Generic.Source)
    {c : SolidCore.Solidity.TypeCheck.CheckedContract} {mirFuel : Nat}
    {d : SolidCore.Solidity.Source.State} {s : List (Nat × Nat)} (hd : Wide.DeployedAt src.fuel c d s)
    {m : Module} {fns : List Abi.Fn} (hchk : checkSym src.fuel mirFuel c.core m fns = true)
    (hval : checkValue mirFuel c.core m fns .allSym = true) {q : Assemble.Program}
    (backend : ∀ o, Stage (moduleSem o) (evmirSem o) m q (scope s fns))
    {F : List Nat} {bytes : List Nat} {cx : AssembleCtx.CtxCert} {N : Nat}
    (asm : AssembleCtxGas.checkXL F q (SolidCore.Verify.Generic.runtimeCode bytes) cx = true)
    (hreads : cx.base.reads = false)
    (ends : ∀ o call, scope s fns call →
      (EVM.Program.run o (AssembleCtxGas.guard F q) call N).isSome = true)
    (guard_run : ∀ o call, scope s fns call →
      EVM.Program.run o q call N = EVM.Program.run o (AssembleCtxGas.guard F q) call N) :
    ∀ ctx : SolidCore.Verify.Generic.Context, ctx.Ok → ∀ call, scope s fns call →
      ∀ gas, AssembleLoop.gasBoundL cx.base N ≤ gas →
        SolidCore.Verify.Generic.runAt ctx gas (SolidCore.Verify.Generic.runtimeCode bytes) call =
          (src.semAt ctx).run c call :=
  fun ctx hctx call hc gas hg =>
    bytes_eq_source_from hd hchk hval backend asm hreads ends guard_run ctx.caller hctx.1 hctx.2
      call hc gas hg

/-- info: 'SolidCore.Verify.AnyCaller.bytes_eq_source_from' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms bytes_eq_source_from

/-- info: 'SolidCore.Verify.AnyCaller.runAt_eq_semAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms runAt_eq_semAt

/-- info: 'SolidCore.Verify.AnyCaller.not_fromOk_of_wide' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms not_fromOk_of_wide

end SolidCore.Verify.AnyCaller

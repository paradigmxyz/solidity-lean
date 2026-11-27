import Verify.ShapeOpen
import SolidCore.Refinement.Generic.CallStage
import SolidCore.Refinement.Solar.AssembleCallOpen

/-!
# The open shape of a contract whose functions make one external call

A contract of the call route is certified as `Shapes.OpenFunctional` (Verify/ShapeOpen.lean): on
the valid calls, the checked source terminates in every admitted open world, and every result of its
exact bytecode in every admitted environment is the source's result in **some** admitted open world
(or a failure that changes nothing), on the valid calls `CValid` (Generic/CallStage.lean: no value, and a target argument
that is not the contract and whose low 160 bits are no address of EthLib's Fusaka precompile set,
`0x01`–`0x11` and `0x100`; nothing about its code). What the statement assumes is
named in it:

* `CallEnvOk`, **the callee-world assumption on the environment**: the other accounts are well
  formed, and on every valid call whose run succeeds, every frame of the contract's code at a
  `STATICCALL` byte whose run goes on to the run's final frame (`AssembleCallSeg.CalleesOkR`; such
  a frame is not asked to be reachable from the start) calls an address outside SolidCore's
  precompile set `0x01`–`0x0a` (`AssembleCallSeg.CalleeOk`: nothing about the code there, which
  may be empty or a delegation), or calls ECRECOVER (address 1) with no delegation there and at
  least 3000 gas passed on (`AssembleCallSeg.PreRun`): `AssembleCallOpen.CalleesRunOpen`. It does
  not say the callee has code;
* `CallWorldOk`, the source worlds: open worlds whose answers to static calls outside SolidCore's
  precompile set are shorter than `2 ^ 256` bytes (`Fits`) and that some MIR oracle agrees with (`CallsAgree`: in particular a
  static call's answer keeps the caller's storage);
* `AssembleCallPre.EcrecoverAgree`, a premise of the published statement (SolidCore's and EthLib's
  ECRECOVER agree), which the bytes edge takes.

**What the statement says of a returned word**: the world a result is explained by is existential
(`OpenFunctional.equiv`). A result of the bytecode (its status, return data, the contract's
storage and logs) is SolidCore's result in **some** admitted world (`CallWorldOk`), or a failure
that changes nothing; the statement does not say that world is the one this environment's callee
computes, so a returned word is the source's function of some admitted answer to the call, not
necessarily of the answer the actual callee in this environment gives. The bytes edge builds its
world from the run's callee frames (`RunWorld`), but the published statement keeps only
`CallWorldOk`.

`openFunctional_of_check` composes the kernel's check of the contract (`callCheck`: the type check,
no seeded accounts, a constructor that leaves nothing, and `checkC`), the stages from the first
lowered MIR to the final EVM IR, and the bytes edge (`Ctx.bytecode_run` of asm_ctx.py's module).
-/

namespace SolidCore.Refinement.Shapes
open SolarTV SolidCore.Refinement SolidCore.Refinement.Generic SolidCore.Refinement.Solar
open SolidCore.Solidity.Source EvmCompiler.Simulation

/-- **The callee-world assumption on the environment**: its accounts are well formed, and in every
successful run of a valid call, each frame of the code at a `STATICCALL` byte whose run goes on to
the final frame (reached from the run's start or not)
calls an address outside SolidCore's precompile set (`0x01`–`0x0a`, whatever code or delegation is
there, possibly none) or calls ECRECOVER priced (`AssembleCallOpen.CalleesRunOpen`). -/
def CallEnvOk (fns : List CFn) (code : ByteArray) (env : TargetEnv) : Prop :=
  env.WF ∧ ∀ gas, gas < 2 ^ 256 → ∀ call, CValid fns call →
    AssembleCallOpen.CalleesRunOpen env gas code call

/-- The source worlds of the call route: open, answering static calls outside SolidCore's
precompile set with fewer than `2 ^ 256` bytes, and agreeing with some MIR oracle. Neither the world
nor the oracle is tied to the environment: a result is explained by some such world, not
necessarily the one the environment's callee computes. -/
def CallWorldOk (W : World) : Prop :=
  W.Open ∧ AssembleCallOpen.Fits W ∧ ∃ o, CallsAgree o W

theorem cvalid_inhabited (f : CFn) (fns : List CFn) : ∃ call, CValid (f :: fns) call := by
  refine ⟨_, f, List.mem_cons_self, List.replicate f.n 0x2468, [], by simp, ?_, rfl, ?_⟩
  · intro a ha
    rw [(List.mem_replicate.mp ha).2]
    decide
  · intro j _
    by_cases hj : j < f.n
    · have : (List.replicate f.n 0x2468).getD j 0 = 0x2468 := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_replicate]; simp [hj]
      rw [this]
      decide
    · have : (List.replicate f.n 0x2468).getD j 0 = 0 := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_replicate]; simp [hj]
      rw [this]
      decide

/-- What the constructor of `c` leaves at the fuel `fuel`: no storage, no logs, no transient
storage, no adopted world. -/
def deployFactsC (fuel : Nat) (c : SolidCore.Solidity.TypeCheck.CheckedContract) : Bool :=
  match SolidCore.Solidity.TypeCheck.CheckedContract.constructWithContext? fuel c (Wide.ctxOf c)
      State.empty selfAddress 0 [] with
  | some (CallResult.returned d _) =>
    d.storage.toList.isEmpty && d.events.isEmpty && d.transient.toList.isEmpty && d.envWorld?.isNone
  | _ => false

theorem deployFactsC_of {fuel : Nat} {c : SolidCore.Solidity.TypeCheck.CheckedContract}
    (h : deployFactsC fuel c = true) :
    ∃ d, Wide.DeployedAt fuel c d [] ∧ d.transient.toList = [] ∧ d.envWorld? = none := by
  unfold deployFactsC at h
  split at h
  next d vs hc =>
    simp only [Bool.and_eq_true, List.isEmpty_iff, Option.isNone_iff_eq_none] at h
    exact ⟨d, ⟨⟨vs, hc⟩, h.1.1.1, h.1.1.2⟩, h.1.2, h.2⟩
  next => simp at h

/-- **The kernel's check of a contract of the call route**: SolidCore type checks it, it seeds no
other accounts, its constructor leaves nothing, and every function of `fns` lowers to `m` (`checkC`). -/
def callCheck (contract? : Except SolidCore.Solidity.TypeCheck.TypeError SolidCore.Solidity.TypeCheck.CheckedContract)
    (fuel mirFuel : Nat) (m : MIR.Lowered.Module) (fns : List CFn) : Bool :=
  match contract? with
  | .ok c =>
    c.core.context.accountBalances.isEmpty && c.core.context.accountCodehashes.isEmpty &&
      c.core.context.accountCodes.isEmpty && deployFactsC fuel c && checkC fuel mirFuel c.core m fns
  | .error _ => false

theorem callCheck_spec {contract? : Except SolidCore.Solidity.TypeCheck.TypeError SolidCore.Solidity.TypeCheck.CheckedContract}
    {fuel mirFuel : Nat} {m : MIR.Lowered.Module} {fns : List CFn}
    (h : callCheck contract? fuel mirFuel m fns = true) :
    ∃ c, contract? = .ok c ∧ c.core.context.accountBalances = [] ∧ c.core.context.accountCodehashes = [] ∧
      c.core.context.accountCodes = [] ∧ checkC fuel mirFuel c.core m fns = true ∧
      ∃ d, Wide.DeployedAt fuel c d [] ∧ d.transient.toList = [] ∧ d.envWorld? = none := by
  cases hc : contract? with
  | error e => simp [callCheck, hc] at h
  | ok c =>
    simp only [callCheck, hc, Bool.and_eq_true, List.isEmpty_iff] at h
    obtain ⟨⟨⟨⟨hb, hh⟩, hcc⟩, hdep⟩, hchk⟩ := h
    exact ⟨c, rfl, hb, hh, hcc, hchk, deployFactsC_of hdep⟩

/-- **SolidCore runs every valid call to an end** in a world of the call route. -/
theorem totalC (W : World) (o : SolarTV.Machine.Oracle) (hagree : CallsAgree o W) (hW : W.Open)
    (hfits : AssembleCallOpen.Fits W) {fuel mirFuel : Nat}
    {c : SolidCore.Solidity.TypeCheck.CheckedContract} {d : SolidCore.Solidity.Source.State}
    (hd : SolidCore.Refinement.Wide.DeployedAt fuel c d [])
    (hcc : c.core.context.accountCodes = []) (hcb : c.core.context.accountBalances = [])
    (hch : c.core.context.accountCodehashes = []) (hdt : d.transient.toList = []) (hde : d.envWorld? = none)
    {m : MIR.Lowered.Module} {fns : List CFn} {env : EnvFlags}
    (hchk : checkC fuel mirFuel c.core m fns env = true) :
    ∀ call, CValid fns call → (Source.runIn W fuel c call).isSome := by
  rintro _ ⟨f, hf, args, σ, hlen, hargs, rfl, htv⟩
  have hcf := List.all_eq_true.mp hchk f hf
  unfold checkCFn at hcf
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hcf
  obtain ⟨hsel, hcf⟩ := hcf
  cases hfind : c.core.findFunctionBySelector? f.sel with
  | none => simp [hfind] at hcf
  | some fn =>
  simp only [hfind, Bool.and_eq_true, decide_eq_true_eq] at hcf
  obtain ⟨hpl, hcf⟩ := hcf
  cases hT1 : eraseFnC (envOf c.core) fuel fn with
  | none => simp [hT1] at hcf
  | some T1 =>
  cases hT2 : symTreeC m f.sel f.n mirFuel env with
  | none => simp [hT1, hT2] at hcf
  | some T2 =>
  simp only [hT1, hT2, Bool.and_eq_true] at hcf
  obtain ⟨-, htg⟩ := hcf
  have hlen' : args.length = fn.params.length := by rw [hlen, hpl]
  rcases eraseFnC_cases hT1 with ⟨t, ht, rfl⟩ | ⟨ws, r, k, t, hw, hret, hrk, ht, rfl⟩
  · rw [source_runIn W hd (fun _ h => absurd h List.not_mem_nil) hsel hfind ht args hlen' hargs]
    rfl
  · have hnf : (paramGuardsC ws 0 (.call r [] fn.params.length t)).callFree = false := by
      rw [callFree_paramGuardsC]; rfl
    cases htarget : f.target with
    | none => simp [htarget, hnf] at htg
    | some j =>
    simp only [htarget, Bool.and_eq_true, decide_eq_true_eq] at htg
    obtain ⟨hj, htgt⟩ := htg
    rw [targetsArg_paramGuardsC] at htgt
    simp only [CTree.targetsArg, beq_iff_eq] at htgt
    obtain ⟨hnself, hnfus⟩ := htv j htarget
    have hnpre := kind_none_of_fusaka (Nat.mod_lt _ (by decide)) hnfus
    by_cases hclean : argsClean ws args = true
    · obtain ⟨world, request, resp, -, -, -, -, -, -, hrunC⟩ :=
        source_runC W hW (fun h world request a hans hk slot => (hagree.static h world request a hans hk slot).1)
          (fits_static hfits) hfits.1 hd hcc hcb hch hdt hde hsel hfind hw hret hrk ht (by omega) htgt args
          hlen' hargs hclean hnself hnpre σ
      rw [hrunC]
      rfl
    · have hdec : SolidCore.Solidity.Source.ABI.decodeFunctionArgs? fn (Dirty.argBytes args) = .error .empty := by
        have := decode_args hw args hlen' hargs
        rw [if_neg hclean] at this
        exact this
      rw [runIn_rejected W hd hsel hfind args hargs hdec σ]
      rfl

/-- **The open shape of a contract of the call route**, from the kernel's check of it, the stages
from its first lowered MIR to its final EVM IR, and the bytes edge in every environment. -/
theorem openFunctional_of_check
    {contract? : Except SolidCore.Solidity.TypeCheck.TypeError SolidCore.Solidity.TypeCheck.CheckedContract}
    {fuel mirFuel : Nat} {m : MIR.Lowered.Module} {f : CFn} {fns : List CFn}
    (hchk : callCheck contract? fuel mirFuel m (f :: fns) = true) {q : Assemble.Program}
    (backend : ∀ o, Stage (mirSem o) (evmirSem o) m q (CValid (f :: fns))) {code : ByteArray}
    {P : SolarTV.Machine.Oracle → Prop}
    (bytes : ∀ env : TargetEnv, env.WF → ∀ gas, gas < 2 ^ 256 → ∀ call, CValid (f :: fns) call →
      AssembleCallOpen.CalleesRunOpen env gas code call →
      ∃ (o : SolarTV.Machine.Oracle) (W : World), W.Open ∧ AssembleCallOpen.Fits W ∧
        AssembleCallOpen.RunWorld gas W ∧ CallsAgree o W ∧ P o ∧
        Final.Within (evmirSem o) (AssembleCallOpen.ethLibIn env gas) q code (· = call)) :
    ∃ c, contract? = .ok c ∧
      OpenFunctional fuel c code (CallEnvOk (f :: fns) code) CallWorldOk CallWorldOk (CValid (f :: fns))
        (fun _ _ _ => True) (fun _ _ _ => True) := by
  obtain ⟨c, hc, hcb, hch, hcc, hchkC, d, hd, hdt, hde⟩ := callCheck_spec hchk
  refine ⟨c, hc, cvalid_inhabited f fns, ?_, ?_, fun _ _ _ _ _ _ => trivial⟩
  · intro env ⟨hwf, hcro⟩ gas hg call hv obs hrun
    obtain ⟨o, W, hW, hF, -, hA, -, hwi⟩ := bytes env hwf gas hg call hv (hcro gas hg call hv)
    rcases hwi call rfl obs hrun with h | h
    · obtain ⟨obs0, h0⟩ := Option.isSome_iff_exists.mp
        (totalC W o hA hW hF hd hcc hcb hch hdt hde hchkC call hv)
      have hq := ((stageC W o hA hW hF hd hcc hcb hch hdt hde SourceAsk.off hchkC).trans (backend o))
        call hv obs0 h0
      rw [hq] at h
      cases h
      exact Or.inl ⟨W, ⟨hW, hF, o, hA⟩, h0⟩
    · exact Or.inr (Or.inl h)
  · intro W ⟨hW, hF, o, hA⟩ call hv
    obtain ⟨obs, h⟩ := Option.isSome_iff_exists.mp (totalC W o hA hW hF hd hcc hcb hch hdt hde hchkC call hv)
    exact ⟨obs, h, trivial⟩

/-- info: 'SolidCore.Refinement.Shapes.openFunctional_of_check' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms openFunctional_of_check

end SolidCore.Refinement.Shapes



import Verify.Generic.Expected
import Verify.Generic.Certificate
import Verify.Generic.CheckLFrom
import Verify.ShapeGeneric

/-!
# Any caller: the translation and the specification in every context

`Generic.Expected` quantifies over the contexts `spec.Contexts`; the existing instances cover the
default context (caller `0x2000`) only, because their stages are stated for `Source.run` and
`Final.Target.runWith`, both from `callerAddress`. This file gives the two certificate fields in
every real context (`Context.Ok`: a caller below `2 ^ 160` other than the contract), with the
same source semantics (`solidCoreFrom a`, the contract deployed by `Wide.DeployedAt` as before), the
same exact bytes, and no premise beyond the ones the default-context proof already has:

* `translationAt_ofL`: **the translation in a context** from a stage of the source sent by the
  context's caller to the final EVM IR (under an oracle family `O`), the source's totality, the final
  EVM IR's fuel and the loop checker on the exact bytecode, through `within_of_checkLFrom` and
  `forward_of_checkLFrom` (Verify/Generic/CheckLFrom.lean).
* `callerFree` / `runFrom_eq_of_callerFree`: a kernel-decidable check that SolidCore's erased tree
  of every function (with `msg.sender` the symbolic word, `eraseFnSym`) never reads the caller, and
  its consequence: on every no-value call of those functions, SolidCore's run from any caller is
  its run from `callerAddress`.
* `translationAt_callerFree` and `specProof_callerFree`: for such a contract whose bytecode reads
  neither CALLER nor KECCAK256 (the loop checker's `cert.env = false`, `cert.reads = false`), the
  default context's generic stage and specification give both fields in every context, on the calls
  without value (`genericValid0`).

Scope, stated rather than assumed: calls with a nonzero value are covered from any caller only by a
stage of their own (not provided here: the value path, `Generic.stageAtValueWith`, is stated for
`Source.run`); contracts whose functions read `msg.sender` need the symbolic stage
(`Generic.stageFrom`, `checkSym`) composed into `translationAt_ofL` with an oracle whose CALLER is
the context's; the contract's own address, block and transaction stay `Target`'s. The lifecycle
(constructor arguments, invariant establishment, reentrancy) is out of scope.
-/

namespace SolidCore.Verify.Generic

open SolarTV SolidCore.Refinement SolidCore.Refinement.Shapes SolidCore.Solidity
open SolidCore.Refinement.Solar SolidCore.Refinement.Generic

/-! ## The translation in one context -/

/-- **The translation in a context, from the loop checker.** -/
theorem translationAt_ofL {fuel : Nat} {c : TypeCheck.CheckedContract} {Valid : Call → Prop}
    {q : Assemble.Program} {code : ByteArray} {cert : Assemble.Cert} {mx : List Nat} {N : Nat}
    (O : Nat → Machine.Oracle) (asm : AssembleLoop.checkL q code cert mx = true)
    (hG : AssembleLoop.gasBoundL cert N < 2 ^ 64)
    (ho : ∀ a, cert.env = true → AssembleLoop.OracleOkAt a (O a))
    (he : ∀ a, cert.reads = true → Assemble.EnvOk (O a) ∧ Target.txEnvFrom a = Target.txEnv)
    {ctx : Context} (hctx : ctx.Ok) (inhabited : ∃ call, Valid call)
    (stage : Stage (solidCoreFrom ctx.caller fuel) (evmirSem (O ctx.caller)) c q Valid)
    (defined : Defined (solidCoreFrom ctx.caller fuel) c Valid)
    (ends : ∀ call, Valid call → (EVM.Program.run (O ctx.caller) q call N).isSome = true) :
    TranslationAt (solidCoreFrom ctx.caller fuel) c ctx code Valid
      (fun _ => AssembleLoop.gasBoundL cert N) where
  inhabited := inhabited
  equiv := by
    intro gas _ call hc obs hrun
    have hAB := Assemble.address_ne_self hctx.1 hctx.2
    rcases AssembleLoop.within_of_checkLFrom asm ctx.caller hAB (O ctx.caller) (ho ctx.caller)
      (he ctx.caller) call gas obs hrun with h | h
    · obtain ⟨obs0, hs⟩ := Option.isSome_iff_exists.mp (defined call hc)
      have hq := stage call hc obs0 hs
      rw [h] at hq
      cases hq
      exact Or.inl hs
    · exact Or.inr h
  terminates := fun call hc => by
    obtain ⟨obs, hs⟩ := Option.isSome_iff_exists.mp (defined call hc)
    exact ⟨obs, hs, trivial⟩
  resources := fun call hc => by
    refine ⟨hG, fun gas h1 _ => ?_⟩
    have hAB := Assemble.address_ne_self hctx.1 hctx.2
    obtain ⟨obs0, hs⟩ := Option.isSome_iff_exists.mp (defined call hc)
    have hq := stage call hc obs0 hs
    obtain ⟨r, hit⟩ := Option.isSome_iff_exists.mp (ends call hc)
    have hit' : Machine.iterate (EVM.Program.block (O ctx.caller) call q) N
        (0, [], Machine.State.initial call) = some r := hit
    have hres : (evmirSem (O ctx.caller)).run q call = some (Machine.observe call r.2 r.1) := by
      change (EVM.Program.layer.result (O ctx.caller) q call).map _ = _
      rw [EVM.Program.layer.result_of_ends ⟨N, hit'⟩]
      rfl
    rw [hres] at hq
    cases hq
    rw [hs]
    exact AssembleLoop.forward_of_checkLFrom asm ctx.caller hAB (O ctx.caller) (ho ctx.caller)
      (he ctx.caller) call N r hit' h1

/-- The translation with a larger gas bound, still below `2 ^ 64`. -/
theorem TranslationAt.mono_gas {S : Sem} {p : S.Prog} {ctx : Context} {code : ByteArray}
    {Valid : Call → Prop} {G G' : Call → Nat} (h : TranslationAt S p ctx code Valid G)
    (hle : ∀ call, G call ≤ G' call) (hlt : ∀ call, G' call < 2 ^ 64) :
    TranslationAt S p ctx code Valid G' where
  inhabited := h.inhabited
  equiv := h.equiv
  terminates := h.terminates
  resources := fun call hc =>
    ⟨hlt call, fun gas h1 h2 => (h.resources call hc).2 gas (Nat.le_trans (hle call) h1) h2⟩

/-! ## Contracts that never read the caller -/

/-- A word that does not mention the caller. -/
def noCallerW : WExpr → Bool
  | .lit _ | .arg _ | .init _ => true
  | .un _ a | .sinit a => noCallerW a
  | .bin _ a b | .hash a b => noCallerW a && noCallerW b
  | .sel x a b => noCallerW x && noCallerW a && noCallerW b
  | .caller => false

def noCallerO : OByte → Bool
  | .lit _ => true
  | .byteOf e _ => noCallerW e

def noCallerLog (l : Log) : Bool := l.topics.all noCallerW && l.data.all noCallerO

/-- A tree that never reads the caller. -/
def noCallerT : Tree → Bool
  | .halt _ out ws ls => out.all noCallerO && ws.all (fun kv => noCallerW kv.1 && noCallerW kv.2) &&
      ls.all noCallerLog
  | .ite x t e => noCallerW x && noCallerT t && noCallerT e

theorem evalW_caller (ρ : Val) (b : Nat) : ∀ e, noCallerW e = true →
    e.eval { ρ with caller := b } = e.eval ρ
  | .lit _, _ | .arg _, _ | .init _, _ => rfl
  | .un _ a, h => by simp only [WExpr.eval, evalW_caller ρ b a h]
  | .sinit a, h => by simp only [WExpr.eval, evalW_caller ρ b a h]
  | .bin _ a x, h => by
    simp only [noCallerW, Bool.and_eq_true] at h
    simp only [WExpr.eval, evalW_caller ρ b a h.1, evalW_caller ρ b x h.2]
  | .hash a x, h => by
    simp only [noCallerW, Bool.and_eq_true] at h
    simp only [WExpr.eval, evalW_caller ρ b a h.1, evalW_caller ρ b x h.2]
  | .sel x a y, h => by
    simp only [noCallerW, Bool.and_eq_true] at h
    simp only [WExpr.eval, evalW_caller ρ b x h.1.1, evalW_caller ρ b a h.1.2, evalW_caller ρ b y h.2]
  | .caller, h => by simp [noCallerW] at h

theorem evalO_caller (ρ : Val) (b : Nat) : ∀ o, noCallerO o = true →
    o.eval { ρ with caller := b } = o.eval ρ
  | .lit _, _ => rfl
  | .byteOf e _, h => by simp only [OByte.eval, evalW_caller ρ b e h]

theorem store_caller (ρ : Val) (b : Nat) (n : Nat) : ∀ ws : Writes,
    ws.all (fun kv => noCallerW kv.1 && noCallerW kv.2) = true →
    Writes.store { ρ with caller := b } ws n = Writes.store ρ ws n
  | [], _ => rfl
  | (k, e) :: rest, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    simp only [Writes.store, evalW_caller ρ b k h.1.1, evalW_caller ρ b e h.1.2,
      store_caller ρ b n rest h.2]

theorem evalT_caller (ρ : Val) (b : Nat) : ∀ T, noCallerT T = true →
    T.eval { ρ with caller := b } = T.eval ρ
  | .halt ok out ws ls, h => by
    simp only [noCallerT, Bool.and_eq_true, List.all_eq_true] at h
    obtain ⟨⟨ho, hw⟩, hl⟩ := h
    have hO : out.map (OByte.eval { ρ with caller := b }) = out.map (OByte.eval ρ) :=
      List.map_congr_left fun o hoo => evalO_caller ρ b o (ho o hoo)
    have hW : Writes.store { ρ with caller := b } ws = Writes.store ρ ws :=
      funext fun n => store_caller ρ b n ws (List.all_eq_true.mpr fun x hx => by simp [hw x hx])
    have hL : ls.map (Log.eval { ρ with caller := b }) = ls.map (Log.eval ρ) := by
      refine List.map_congr_left fun l hll => ?_
      have h' := hl l hll
      simp only [noCallerLog, Bool.and_eq_true, List.all_eq_true] at h'
      simp only [Log.eval]
      rw [List.map_congr_left fun e he => evalW_caller ρ b e (h'.1 e he),
        List.map_congr_left fun o hoo => evalO_caller ρ b o (h'.2 o hoo)]
    simp only [Tree.eval, hO, hW, hL]
  | .ite x t e, h => by
    simp only [noCallerT, Bool.and_eq_true] at h
    simp only [Tree.eval, evalW_caller ρ b x h.1.1, evalT_caller ρ b t h.1.2, evalT_caller ρ b e h.2]

/-- **The caller check**: every function of `fns` is found, takes its arguments, and its erased tree
with the symbolic caller never reads it. Decided by the kernel. -/
def callerFree (fuel : Nat) (core : Source.Contract) (fns : List Abi.Fn) : Bool :=
  fns.all fun f => decide (f.sel < 2 ^ 32) &&
    match core.findFunctionBySelector? f.sel with
    | none => false
    | some fn =>
      decide (fn.params.length = f.params.length) &&
        match eraseFnSym (envOf core) fuel fn with
        | some t => noCallerT t
        | none => false

/-- **SolidCore from any caller is SolidCore from `callerAddress`** on the no-value calls of a
caller-free contract. -/
theorem runFrom_eq_of_callerFree {fuel : Nat} {c : TypeCheck.CheckedContract} {d : Source.State}
    {s : List (Nat × Nat)} (hd : Wide.DeployedAt fuel c d s) {fns : List Abi.Fn}
    (hfree : callerFree fuel c.core fns = true) (a : Nat) (ha : a < 2 ^ 160) :
    ∀ call, genericValid0 fns s call → Source.runFrom a fuel c call = Source.run fuel c call := by
  rintro _ ⟨σ, hcov, f, hf, args, hlen, hargs, rfl⟩
  have hcf := List.all_eq_true.mp hfree f hf
  cases hfind : c.core.findFunctionBySelector? f.sel with
  | none => simp [hfind] at hcf
  | some fn =>
  cases ht : eraseFnSym (envOf c.core) fuel fn with
  | none => simp [hfind, ht] at hcf
  | some t =>
  simp only [hfind, ht, Bool.and_eq_true, decide_eq_true_eq] at hcf
  obtain ⟨hsel, hpl, hnc⟩ := hcf
  rw [← Source.runFrom_callerAddress,
    source_run_from a ha hd hcov hsel hfind ht args (by rw [hlen, hpl]) hargs,
    source_run_from callerAddress (by decide) hd hcov hsel hfind ht args (by rw [hlen, hpl]) hargs]
  exact congrArg (fun R => some (Res.obs R))
    (evalT_caller ⟨args, slotValue σ, solHash, callerAddress⟩ a t hnc)

theorem genericValid_of0 {fns : List Abi.Fn} {s : List (Nat × Nat)} {call : Call}
    (h : genericValid0 fns s call) : genericValid fns s call := by
  obtain ⟨σ, hcov, hfs⟩ := h
  exact ⟨σ, 0, hcov, (fullScopeValue_zero fns σ call).mpr hfs⟩

/-- **The translation in every context**, for a caller-free contract whose bytecode reads neither
CALLER nor KECCAK256: the default context's generic stage (`Generic.check`, `checkValue`), the backend
stages, the final EVM IR's fuel and the loop checker, with the caller check. -/
theorem translationAt_callerFree {fuel mirFuel : Nat} {c : TypeCheck.CheckedContract}
    {d : Source.State} {s : List (Nat × Nat)} (hd : Wide.DeployedAt fuel c d s)
    {m : MIR.Lowered.Module} {fns : List Abi.Fn} {env : Generic.EnvFlags}
    (hchk : Generic.check fuel mirFuel c.core m fns env = true)
    (hval : Generic.checkValue mirFuel c.core m fns env = true)
    (hfree : callerFree fuel c.core fns = true)
    {q : Assemble.Program} {code : ByteArray} {scope : Call → Prop} {cert : Assemble.Cert}
    {mx : List Nat} {N : Nat}
    (backend : Stage (mirSem oracle) (evmirSem oracle) m q scope)
    (hscope : ∀ call, genericValid fns s call → scope call)
    (ends : ∀ call, (EVM.Program.run oracle q call N).isSome = true)
    (asm : AssembleLoop.checkL q code cert mx = true)
    (hG : AssembleLoop.gasBoundL cert N < 2 ^ 64) (henv : cert.env = false)
    (hreads : cert.reads = false) (inhabited : ∃ call, genericValid0 fns s call)
    {ctx : Context} (hctx : ctx.Ok) :
    TranslationAt (solidCoreFrom ctx.caller fuel) c ctx code (genericValid0 fns s)
      (fun _ => AssembleLoop.gasBoundL cert N) := by
  have stage0 : Stage (solidCore fuel) (evmirSem oracle) c q (genericValid fns s) :=
    (Generic.stageAtValueWith oracle hd oracle_sourceEnvOk.ask hchk hval).trans
      (backend.mono hscope)
  have defined0 := Generic.definedAtValue hd hchk hval
  have heq := runFrom_eq_of_callerFree hd hfree ctx.caller hctx.1
  refine translationAt_ofL (fun _ => oracle) asm hG (fun _ h => by rw [henv] at h; cases h)
    (fun _ h => by rw [hreads] at h; cases h) hctx inhabited ?_ ?_ (fun call _ => ends call)
  · intro call hc obs hs
    have hs' : Source.runFrom ctx.caller fuel c call = some obs := hs
    rw [heq call hc] at hs'
    exact stage0 call (genericValid_of0 hc) obs hs'
  · intro call hc
    change (Source.runFrom ctx.caller fuel c call).isSome = true
    rw [heq call hc]
    exact defined0 call (genericValid_of0 hc)

/-- **The specification in every context**, for a caller-free contract: the default context's proof
on the no-value calls. -/
theorem specProof_callerFree {fuel : Nat} {c : TypeCheck.CheckedContract} {d : Source.State}
    {s : List (Nat × Nat)} (hd : Wide.DeployedAt fuel c d s) {fns : List Abi.Fn}
    (hfree : callerFree fuel c.core fns = true) {Allowed Post : Call → Observable → Prop}
    (h : SpecProof (solidCore fuel) c (genericValid fns s) Allowed Post)
    {ctx : Context} (hctx : ctx.Ok) :
    SpecProof (solidCoreFrom ctx.caller fuel) c (genericValid0 fns s) Allowed Post := by
  have heq := runFrom_eq_of_callerFree hd hfree ctx.caller hctx.1
  refine ⟨fun call hc obs hs => ?_, fun call hc obs hs => ?_⟩
  · have hs' : Source.runFrom ctx.caller fuel c call = some obs := hs
    rw [heq call hc] at hs'
    exact h.allowed call (genericValid_of0 hc) obs hs'
  · have hs' : Source.runFrom ctx.caller fuel c call = some obs := hs
    rw [heq call hc] at hs'
    exact h.meets call (genericValid_of0 hc) obs hs'

/-- info: 'SolidCore.Verify.Generic.translationAt_callerFree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms translationAt_callerFree

/-- info: 'SolidCore.Verify.Generic.specProof_callerFree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms specProof_callerFree

end SolidCore.Verify.Generic

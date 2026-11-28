import Verify.LoopSource.Equiv.Stage
import Verify.LoopSource.Proof.EraseLoop
import Verify.Gas.FixedFuel.Run

/-!
# Resources of a one-loop function, from the erasure, by the EVM IR's least block count

The loop's source edge (`EraseLoopStage.lean`) gives `Shapes.Equiv`. This module gives
`Shapes.Resources` and the whole `Shapes.Certified` for the same premises, by composing
refinements rather than simulating the loop's blocks: termination moves forward along a stage
(`ends_of_stage`). The source ends on every valid call (`bodyRuns_of_eraseLoop`, then
`runs_of_bodyRuns`), the source-to-EVM-IR stage carries that end to the EVM IR, and the EVM IR's
least ending block count `evmFuel` is the count the loop checker's forward theorem
(`AssembleLoop.stage_of_checkL_gas`) takes. The gas bound `gasBoundL cert (evmFuel …)` then needs
no machine-side loop argument; what is left is that it fits in 64 bits (`hfit`).

* `core`: any source semantics, a total source, a stage into the EVM IR and the loop checker.
* `resources_of_bodyRuns`, `certified_of_bodyRuns`: a one-loop function with `BodyRuns`, on any
  precondition inside the selector's calls (`hsub`), with `loop_stage`'s and `loop_equiv`'s
  premises.
* `certified_of_bodyRuns_loops`: a constant bound `gasBoundL cert (fixedFuel E B X M)`, from a
  measure bridge (`Verify.Gas.FixedFuel.Loops`) on the EVM IR, since `evmFuel` is at most every
  fuel within which the run ends (`evmFuel_le`).
* `eraseLoop_resources`, `eraseLoop_certified`, `eraseLoop_certified_loops`: the same from
  `eraseLoopStmt`, through `bodyRuns_of_eraseLoop`.

Nothing here names a contract, a selector or a file.
-/

namespace Verify.LoopSource.Equiv.LeastFuel
open SolarTV SolarTV.Machine SolarTV.MIR.Lowered SolidCore.Refinement SolidCore.Refinement.Generic
open SolidCore.Solidity.Source Verify.LoopSource.Interface Verify.LoopSource.Generic
open SolidCore.Refinement.Generic.Loop SolidCore.Refinement.Solar

open Classical in
/-- The least number of blocks within which the EVM IR ends on a call; `0` when it never ends. -/
noncomputable def evmFuel (o : Oracle) (q : Assemble.Program) (call : Call) : Nat :=
  if h : ∃ n, (EVM.Program.run o q call n).isSome then Nat.find h else 0

/-- **Core**: resources from a total source, a stage into the EVM IR and the loop checker, at the
EVM IR's own least block count, for any source semantics. -/
def CoreTarget : Prop :=
  ∀ (S : Sem) (p : S.Prog) (q : Assemble.Program) (code : ByteArray) (cert : Assemble.Cert)
    (mx : List Nat) (Valid : Call → Prop) (o : Oracle),
    AssembleLoop.checkL q code cert mx = true →
    (cert.env = true → Assemble.OracleOk o) → (cert.reads = true → Assemble.EnvOk o) →
    (∀ call, Valid call → ∃ obs, S.run p call = some obs) →
    Stage S (evmirSem o) p q Valid →
    (∀ call, Valid call → AssembleLoop.gasBoundL cert (evmFuel o q call) < 2 ^ 64) →
    Shapes.Resources S p code Valid (fun call => AssembleLoop.gasBoundL cert (evmFuel o q call))

/-- **The erasure's resources**: `loop_equiv_of_eraseLoop`'s premises, on any precondition
`Valid` inside the selector's calls whose least-fuel gas fits in 64 bits. -/
def EraseLoopTarget : Prop :=
  ∀ (fuel : Nat) (c : SolidCore.Solidity.TypeCheck.CheckedContract) (sel : Nat) (fn : FunctionDef)
    (ws : List Nat) (b : Br) (T : Tree),
    sel < 2 ^ 32 → c.core.findFunctionBySelector? sel = some fn →
    widthsOf fn.params fn.paramAbiCleanups = some ws → fn.returns.all wordBinding = true →
    eraseLoopStmt { envOf c.core with facts := argFacts ws 0 } fuel fn.body (initState fn) = some b →
    brTree fn (argFacts ws 0) b = some T →
    ∀ (C : Cut) (ev : EnvFlags) (m : Module) (le li : List (Facts × Out)),
    C.check ev m sel fn.params.length = some (le, li) →
    ∀ (L : Val → LoopRecord) (toSrc : Val → Val) (X A : Val → Prop),
    Obl L toSrc X A fn.params.length C.cases T le li →
    (∀ σ args, ArgsOk fn ws args → A ⟨args, slotValue σ, solHash, callerWord⟩) →
    ∀ (q : Assemble.Program) (code : ByteArray) (scope : Call → Prop) (cert : Assemble.Cert)
      (mx : List Nat),
    Stage (mirSem Shapes.oracle) (evmirSem Shapes.oracle) m q scope →
    (∀ call, SelCall sel fn ws call → scope call) →
    AssembleLoop.checkL q code cert mx = true →
    ∀ (Valid : Call → Prop), (∀ call, Valid call → SelCall sel fn ws call) →
    (∀ call, Valid call → AssembleLoop.gasBoundL cert (evmFuel Shapes.oracle q call) < 2 ^ 64) →
    Shapes.Resources (solidCoreRuntime fuel) c code Valid
      (fun call => AssembleLoop.gasBoundL cert (evmFuel Shapes.oracle q call))

/-- **The whole Statement**, with the same premises, an inhabited `Valid` and the tree's
`Allowed` and `Post` (`OnTree`, as `GenericLink` takes them). -/
def CertifiedTarget : Prop :=
  ∀ (fuel : Nat) (c : SolidCore.Solidity.TypeCheck.CheckedContract) (sel : Nat) (fn : FunctionDef)
    (ws : List Nat) (b : Br) (T : Tree),
    sel < 2 ^ 32 → c.core.findFunctionBySelector? sel = some fn →
    widthsOf fn.params fn.paramAbiCleanups = some ws → fn.returns.all wordBinding = true →
    eraseLoopStmt { envOf c.core with facts := argFacts ws 0 } fuel fn.body (initState fn) = some b →
    brTree fn (argFacts ws 0) b = some T →
    ∀ (C : Cut) (ev : EnvFlags) (m : Module) (le li : List (Facts × Out)),
    C.check ev m sel fn.params.length = some (le, li) →
    ∀ (L : Val → LoopRecord) (toSrc : Val → Val) (X A : Val → Prop),
    Obl L toSrc X A fn.params.length C.cases T le li →
    (∀ σ args, ArgsOk fn ws args → A ⟨args, slotValue σ, solHash, callerWord⟩) →
    ∀ (q : Assemble.Program) (code : ByteArray) (scope : Call → Prop) (cert : Assemble.Cert)
      (mx : List Nat),
    Stage (mirSem Shapes.oracle) (evmirSem Shapes.oracle) m q scope →
    (∀ call, SelCall sel fn ws call → scope call) →
    AssembleLoop.checkL q code cert mx = true →
    ∀ (Valid : Call → Prop) (Allowed Post : Call → Observable → Prop),
    (∀ call, Valid call → SelCall sel fn ws call) → (∃ call, Valid call) →
    OnTree sel fn ws T Allowed → OnTree sel fn ws T Post →
    (∀ call, Valid call → AssembleLoop.gasBoundL cert (evmFuel Shapes.oracle q call) < 2 ^ 64) →
    Shapes.Certified (solidCoreRuntime fuel) c code Valid Allowed Post
      (fun call => AssembleLoop.gasBoundL cert (evmFuel Shapes.oracle q call))

/-- **A fixed gas bound from a measure**: with a bridge of a loop record on the EVM IR
(`FixedFuel.Loops`, whose `Bridge.runs` is an induction on the record's measure) on every valid
call, the constant bound at the fixed fuel, when it fits in 64 bits. -/
def BridgeTarget : Prop :=
  ∀ (fuel : Nat) (c : SolidCore.Solidity.TypeCheck.CheckedContract) (sel : Nat) (fn : FunctionDef)
    (ws : List Nat) (b : Br) (T : Tree),
    sel < 2 ^ 32 → c.core.findFunctionBySelector? sel = some fn →
    widthsOf fn.params fn.paramAbiCleanups = some ws → fn.returns.all wordBinding = true →
    eraseLoopStmt { envOf c.core with facts := argFacts ws 0 } fuel fn.body (initState fn) = some b →
    brTree fn (argFacts ws 0) b = some T →
    ∀ (C : Cut) (ev : EnvFlags) (m : Module) (le li : List (Facts × Out)),
    C.check ev m sel fn.params.length = some (le, li) →
    ∀ (L : Val → LoopRecord) (toSrc : Val → Val) (X A : Val → Prop),
    Obl L toSrc X A fn.params.length C.cases T le li →
    (∀ σ args, ArgsOk fn ws args → A ⟨args, slotValue σ, solHash, callerWord⟩) →
    ∀ (q : Assemble.Program) (code : ByteArray) (scope : Call → Prop) (cert : Assemble.Cert)
      (mx : List Nat),
    Stage (mirSem Shapes.oracle) (evmirSem Shapes.oracle) m q scope →
    (∀ call, SelCall sel fn ws call → scope call) →
    AssembleLoop.checkL q code cert mx = true →
    ∀ (Valid : Call → Prop) (Allowed Post : Call → Observable → Prop),
    (∀ call, Valid call → SelCall sel fn ws call) → (∃ call, Valid call) →
    OnTree sel fn ws T Allowed → OnTree sel fn ws T Post →
    ∀ (R : LoopRecord) (E B Xs M : Nat),
    (∀ call, Valid call → Verify.Gas.FixedFuel.Loops (EVM.Program.block Shapes.oracle call q)
      (0, [], SolarTV.Machine.State.initial call) R E B Xs M) →
    AssembleLoop.gasBoundL cert (Verify.Gas.FixedFuel.fixedFuel E B Xs M) < 2 ^ 64 →
    Shapes.Certified (solidCoreRuntime fuel) c code Valid Allowed Post
      (fun _ => AssembleLoop.gasBoundL cert (Verify.Gas.FixedFuel.fixedFuel E B Xs M))


/-! ## The least block count -/

/-- At its least block count the EVM IR ends, when it ends at all. -/
theorem evmFuel_spec {o : Oracle} {q : Assemble.Program} {call : Call}
    (h : ∃ n r, EVM.Program.run o q call n = some r) :
    ∃ r, EVM.Program.run o q call (evmFuel o q call) = some r := by
  have h' : ∃ n, (EVM.Program.run o q call n).isSome := by
    obtain ⟨n, r, hr⟩ := h
    exact ⟨n, by rw [hr]; rfl⟩
  unfold evmFuel
  split
  · rename_i hx
    exact Option.isSome_iff_exists.mp (Nat.find_spec hx)
  · exact absurd h' ‹_›

/-- The least block count is at most every block count within which the EVM IR ends. -/
theorem evmFuel_le {o : Oracle} {q : Assemble.Program} {call : Call} {n : Nat} {r : SolarTV.Machine.Halt × SolarTV.Machine.State}
    (h : EVM.Program.run o q call n = some r) : evmFuel o q call ≤ n := by
  have hn : (EVM.Program.run o q call n).isSome := by rw [h]; rfl
  unfold evmFuel
  split
  · exact Nat.find_min' _ hn
  · exact Nat.zero_le _

/-- **Termination moves forward along a stage**: a source that ends on a valid call, and a stage
from it into the EVM IR, make the EVM IR end within some number of blocks. -/
theorem ends_of_stage {S : Sem} {p : S.Prog} {o : Oracle} {q : Assemble.Program}
    {Valid : Call → Prop} (total : ∀ call, Valid call → ∃ obs, S.run p call = some obs)
    (stage : Stage S (evmirSem o) p q Valid) {call : Call} (hc : Valid call) :
    ∃ n r, EVM.Program.run o q call n = some r := by
  obtain ⟨obs, hs⟩ := total call hc
  have he := stage call hc obs hs
  change (EVM.Program.layer.result o q call).map _ = some obs at he
  obtain ⟨r, hr, -⟩ := Option.map_eq_some_iff.mp he
  obtain ⟨n, hn⟩ := EVM.Program.layer.ends_of_result hr
  exact ⟨n, r, hn⟩

theorem gasBoundL_mono (cert : Assemble.Cert) {n n' : Nat} (h : n ≤ n') :
    AssembleLoop.gasBoundL cert n ≤ AssembleLoop.gasBoundL cert n' :=
  Nat.add_le_add_right (Nat.mul_le_mul_left 22100 (Nat.mul_le_mul_right _ h)) _

/-- A larger gas bound that still fits in 64 bits keeps the resources. -/
theorem resources_mono {S : Sem} {p : S.Prog} {code : ByteArray} {Valid : Call → Prop}
    {G G' : Call → Nat} (h : Shapes.Resources S p code Valid G)
    (hle : ∀ call, Valid call → G call ≤ G' call ∧ G' call < 2 ^ 64) :
    Shapes.Resources S p code Valid G' := fun call hc =>
  ⟨(hle call hc).2, fun gas h1 h2 => (h call hc).2 gas (Nat.le_trans (hle call hc).1 h1) h2⟩

/-- **The core**, for any source semantics. -/
theorem core : CoreTarget := by
  intro S p q code cert mx Valid o asm ho he total stage hfit
  exact Shapes.resources_of_forward total stage fun call hc => ⟨hfit call hc, fun gas hg _ obs hrun =>
    AssembleLoop.stage_of_checkL_gas asm o ho he call _ (evmFuel_spec (ends_of_stage total stage hc))
      hg obs hrun⟩

/-! ## From `BodyRuns` -/

/-- **Resources of a one-loop function from `BodyRuns`**, on any precondition inside the
selector's calls. -/
theorem resources_of_bodyRuns {fuel : Nat} {c : SolidCore.Solidity.TypeCheck.CheckedContract}
    {sel : Nat} {fn : FunctionDef} {ws : List Nat} {b : Br} {T : Tree} (hsel : sel < 2 ^ 32)
    (hfind : c.core.findFunctionBySelector? sel = some fn)
    (hw : widthsOf fn.params fn.paramAbiCleanups = some ws) (hret : fn.returns.all wordBinding = true)
    (hb : BodyRuns { envOf c.core with facts := argFacts ws 0 } fuel fn b)
    (hT : brTree fn (argFacts ws 0) b = some T)
    {C : Cut} {ev : EnvFlags} {m : Module} {le li : List (Facts × Out)}
    (hchk : C.check ev m sel fn.params.length = some (le, li))
    {L : Val → LoopRecord} {toSrc : Val → Val} {X A : Val → Prop}
    (hobl : Obl L toSrc X A fn.params.length C.cases T le li)
    (hA : ∀ σ args, ArgsOk fn ws args → A ⟨args, slotValue σ, solHash, callerWord⟩)
    {q : Assemble.Program} {code : ByteArray} {scope : Call → Prop} {cert : Assemble.Cert}
    {mx : List Nat} (backend : Stage (mirSem Shapes.oracle) (evmirSem Shapes.oracle) m q scope)
    (hscope : ∀ call, SelCall sel fn ws call → scope call)
    (asm : AssembleLoop.checkL q code cert mx = true)
    {Valid : Call → Prop} (hsub : ∀ call, Valid call → SelCall sel fn ws call)
    (hfit : ∀ call, Valid call → AssembleLoop.gasBoundL cert (evmFuel Shapes.oracle q call) < 2 ^ 64) :
    Shapes.Resources (solidCoreRuntime fuel) c code Valid
      (fun call => AssembleLoop.gasBoundL cert (evmFuel Shapes.oracle q call)) := by
  have total : ∀ call, Valid call → ∃ obs, (solidCoreRuntime fuel).run c call = some obs := by
    intro call hv
    obtain ⟨σ, args, ha, rfl⟩ := hsub call hv
    exact ⟨_, runs_of_bodyRuns hsel hfind hw hret hb hT σ ha⟩
  have stage : Stage (solidCoreRuntime fuel) (evmirSem Shapes.oracle) c q Valid :=
    ((loop_stage hsel hfind hw hret hb hT hchk hobl hA Shapes.oracle
      Shapes.oracle_sourceEnvOk.ask).trans (backend.mono hscope)).mono hsub
  exact core _ _ _ _ _ _ _ _ asm (fun _ => Shapes.oracle_ok.1) (fun _ => Shapes.oracle_ok.2) total
    stage hfit

/-- **The whole Statement of a one-loop function from `BodyRuns`.** -/
theorem certified_of_bodyRuns {fuel : Nat} {c : SolidCore.Solidity.TypeCheck.CheckedContract}
    {sel : Nat} {fn : FunctionDef} {ws : List Nat} {b : Br} {T : Tree} (hsel : sel < 2 ^ 32)
    (hfind : c.core.findFunctionBySelector? sel = some fn)
    (hw : widthsOf fn.params fn.paramAbiCleanups = some ws) (hret : fn.returns.all wordBinding = true)
    (hb : BodyRuns { envOf c.core with facts := argFacts ws 0 } fuel fn b)
    (hT : brTree fn (argFacts ws 0) b = some T)
    {C : Cut} {ev : EnvFlags} {m : Module} {le li : List (Facts × Out)}
    (hchk : C.check ev m sel fn.params.length = some (le, li))
    {L : Val → LoopRecord} {toSrc : Val → Val} {X A : Val → Prop}
    (hobl : Obl L toSrc X A fn.params.length C.cases T le li)
    (hA : ∀ σ args, ArgsOk fn ws args → A ⟨args, slotValue σ, solHash, callerWord⟩)
    {q : Assemble.Program} {code : ByteArray} {scope : Call → Prop} {cert : Assemble.Cert}
    {mx : List Nat} (backend : Stage (mirSem Shapes.oracle) (evmirSem Shapes.oracle) m q scope)
    (hscope : ∀ call, SelCall sel fn ws call → scope call)
    (asm : AssembleLoop.checkL q code cert mx = true)
    {Valid : Call → Prop} {Allowed Post : Call → Observable → Prop}
    (hsub : ∀ call, Valid call → SelCall sel fn ws call) (hinh : ∃ call, Valid call)
    (hAl : OnTree sel fn ws T Allowed) (hP : OnTree sel fn ws T Post)
    (hfit : ∀ call, Valid call → AssembleLoop.gasBoundL cert (evmFuel Shapes.oracle q call) < 2 ^ 64) :
    Shapes.Certified (solidCoreRuntime fuel) c code Valid Allowed Post
      (fun call => AssembleLoop.gasBoundL cert (evmFuel Shapes.oracle q call)) := by
  have heq := loop_equiv hsel hfind hw hret hb hT hchk hobl hA backend hscope asm
  refine ⟨hinh, fun gas hg call hv => heq gas hg call (hsub call hv), ?_, ?_,
    resources_of_bodyRuns hsel hfind hw hret hb hT hchk hobl hA backend hscope asm hsub hfit⟩
  · intro call hv
    obtain ⟨σ, args, ha, rfl⟩ := hsub call hv
    exact ⟨_, runs_of_bodyRuns hsel hfind hw hret hb hT σ ha, hAl σ args ha⟩
  · intro call hv obs hs
    obtain ⟨σ, args, ha, rfl⟩ := hsub call hv
    rw [runs_of_bodyRuns hsel hfind hw hret hb hT σ ha] at hs
    obtain rfl := Option.some.inj hs
    exact hP σ args ha

/-- **A constant gas bound from a measure bridge**, from `BodyRuns`. -/
theorem certified_of_bodyRuns_loops {fuel : Nat} {c : SolidCore.Solidity.TypeCheck.CheckedContract}
    {sel : Nat} {fn : FunctionDef} {ws : List Nat} {b : Br} {T : Tree} (hsel : sel < 2 ^ 32)
    (hfind : c.core.findFunctionBySelector? sel = some fn)
    (hw : widthsOf fn.params fn.paramAbiCleanups = some ws) (hret : fn.returns.all wordBinding = true)
    (hb : BodyRuns { envOf c.core with facts := argFacts ws 0 } fuel fn b)
    (hT : brTree fn (argFacts ws 0) b = some T)
    {C : Cut} {ev : EnvFlags} {m : Module} {le li : List (Facts × Out)}
    (hchk : C.check ev m sel fn.params.length = some (le, li))
    {L : Val → LoopRecord} {toSrc : Val → Val} {X A : Val → Prop}
    (hobl : Obl L toSrc X A fn.params.length C.cases T le li)
    (hA : ∀ σ args, ArgsOk fn ws args → A ⟨args, slotValue σ, solHash, callerWord⟩)
    {q : Assemble.Program} {code : ByteArray} {scope : Call → Prop} {cert : Assemble.Cert}
    {mx : List Nat} (backend : Stage (mirSem Shapes.oracle) (evmirSem Shapes.oracle) m q scope)
    (hscope : ∀ call, SelCall sel fn ws call → scope call)
    (asm : AssembleLoop.checkL q code cert mx = true)
    {Valid : Call → Prop} {Allowed Post : Call → Observable → Prop}
    (hsub : ∀ call, Valid call → SelCall sel fn ws call) (hinh : ∃ call, Valid call)
    (hAl : OnTree sel fn ws T Allowed) (hP : OnTree sel fn ws T Post)
    {R : LoopRecord} {E B Xs M : Nat}
    (loops : ∀ call, Valid call → Verify.Gas.FixedFuel.Loops (EVM.Program.block Shapes.oracle call q)
      (0, [], SolarTV.Machine.State.initial call) R E B Xs M)
    (hfit : AssembleLoop.gasBoundL cert (Verify.Gas.FixedFuel.fixedFuel E B Xs M) < 2 ^ 64) :
    Shapes.Certified (solidCoreRuntime fuel) c code Valid Allowed Post
      (fun _ => AssembleLoop.gasBoundL cert (Verify.Gas.FixedFuel.fixedFuel E B Xs M)) := by
  have hle : ∀ call, Valid call → AssembleLoop.gasBoundL cert (evmFuel Shapes.oracle q call) ≤
      AssembleLoop.gasBoundL cert (Verify.Gas.FixedFuel.fixedFuel E B Xs M) := fun call hv =>
    gasBoundL_mono cert (by
      obtain ⟨r, hr⟩ := Verify.Gas.FixedFuel.ends_of_loops (loops call hv)
      exact evmFuel_le hr)
  have h := certified_of_bodyRuns hsel hfind hw hret hb hT hchk hobl hA backend hscope asm hsub hinh
    hAl hP fun call hv => Nat.lt_of_le_of_lt (hle call hv) hfit
  exact ⟨h.inhabited, h.equiv, h.terminates, h.meets,
    resources_mono h.resources fun call hv => ⟨hle call hv, hfit⟩⟩

/-! ## From the erasure -/

/-- **The erasure's resources.** -/
theorem eraseLoop_resources : EraseLoopTarget := by
  intro fuel c sel fn ws b T hsel hfind hw hret h hT C ev m le li hchk L toSrc X A hobl hA q code
    scope cert mx backend hscope asm Valid hsub hfit
  exact resources_of_bodyRuns hsel hfind hw hret (bodyRuns_of_eraseLoop h) hT hchk hobl hA backend
    hscope asm hsub hfit

/-- **The erasure's whole Statement.** -/
theorem eraseLoop_certified : CertifiedTarget := by
  intro fuel c sel fn ws b T hsel hfind hw hret h hT C ev m le li hchk L toSrc X A hobl hA q code
    scope cert mx backend hscope asm Valid Allowed Post hsub hinh hAl hP hfit
  exact certified_of_bodyRuns hsel hfind hw hret (bodyRuns_of_eraseLoop h) hT hchk hobl hA backend
    hscope asm hsub hinh hAl hP hfit

/-- **The erasure's whole Statement at a constant gas bound**, from a measure bridge. -/
theorem eraseLoop_certified_loops : BridgeTarget := by
  intro fuel c sel fn ws b T hsel hfind hw hret h hT C ev m le li hchk L toSrc X A hobl hA q code
    scope cert mx backend hscope asm Valid Allowed Post hsub hinh hAl hP R E B Xs M loops hfit
  exact certified_of_bodyRuns_loops hsel hfind hw hret (bodyRuns_of_eraseLoop h) hT hchk hobl hA
    backend hscope asm hsub hinh hAl hP loops hfit

end Verify.LoopSource.Equiv.LeastFuel

/-- info: 'Verify.LoopSource.Equiv.LeastFuel.core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Verify.LoopSource.Equiv.LeastFuel.core

/-- info: 'Verify.LoopSource.Equiv.LeastFuel.resources_of_bodyRuns' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Verify.LoopSource.Equiv.LeastFuel.resources_of_bodyRuns

/-- info: 'Verify.LoopSource.Equiv.LeastFuel.certified_of_bodyRuns' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Verify.LoopSource.Equiv.LeastFuel.certified_of_bodyRuns

/-- info: 'Verify.LoopSource.Equiv.LeastFuel.certified_of_bodyRuns_loops' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Verify.LoopSource.Equiv.LeastFuel.certified_of_bodyRuns_loops

/-- info: 'Verify.LoopSource.Equiv.LeastFuel.eraseLoop_resources' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Verify.LoopSource.Equiv.LeastFuel.eraseLoop_resources

/-- info: 'Verify.LoopSource.Equiv.LeastFuel.eraseLoop_certified' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Verify.LoopSource.Equiv.LeastFuel.eraseLoop_certified

/-- info: 'Verify.LoopSource.Equiv.LeastFuel.eraseLoop_certified_loops' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Verify.LoopSource.Equiv.LeastFuel.eraseLoop_certified_loops

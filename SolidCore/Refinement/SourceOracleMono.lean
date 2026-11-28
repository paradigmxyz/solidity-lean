import SolidCore.Refinement.SourceOracle

/-!
# What the closed world shows, every open world shows

`Source.run` answers resources by their defaults and precompile calls in the semantics, and nothing
else (`closedAns`); every open world answers those the same way (`World.Open`). So a run that
finishes in the closed world finishes the same way in every open world whose account code during
the call is the contract's own context's (`runIn_of_run`): the fold takes the same answers along
the same path (`foldAns_mono`). A function whose only external calls are precompile calls
(`ecrecover` in a token's `permit`) then has, in every such open world, exactly its closed-world
outcomes wherever the closed world finishes, and a stage from `Source.run` that also finishes on
its scope is a stage from `Source.runIn W` (`stageIn_of_stage`).
-/

namespace SolidCore.Refinement

open SolidCore.Solidity SolidCore.Solidity.Source EvmCompiler.Simulation

/-- `W.ans` answers every query `closedAns` answers, the same way. -/
def ExtendsClosed (W : World) : Prop := ∀ h q a, closedAns h q = some a → W.ans h q = some a

/-- Every open world extends the closed responder. -/
theorem World.Open.extendsClosed {W : World} (hW : W.Open) : ExtendsClosed W := by
  intro h q a ha
  cases q with
  | resource r =>
    simp only [closedAns, Option.some.injEq] at ha
    rw [hW.resources, ha]
  | external world req =>
    cases req with
    | call request => exact hW.precompiles h world request a ha
    | create request => simp [closedAns] at ha

/-- A fold that finishes under `closedAns` finishes the same way under every extension. -/
theorem foldAns_mono {W : World} (hW : ExtendsClosed W) {α : Type} (t : SolI α) :
    ∀ h r, foldAns closedAns h t = some r → foldAns W.ans h t = some r := by
  induction t with
  | done r =>
    intro h r' hr
    cases r <;> simpa [foldAns] using hr
  | request q k ih =>
    intro h r hr
    simp only [foldAns] at hr ⊢
    cases hq : closedAns h q with
    | none => rw [hq] at hr; simp at hr
    | some a =>
      rw [hq] at hr
      rw [hW h q a hq]
      exact ih a _ _ hr

theorem callAns_mono {W : World} (hW : ExtendsClosed W) {fuel : Nat} {table : FunctionTable}
    {context : Context} {fn : FunctionDef} {st : Source.State} {args : List Value} {r : CallResult}
    (h : Source.callAns closedAns fuel table context fn st args = some r) :
    Source.callAns W.ans fuel table context fn st args = some r := by
  unfold Source.callAns at h ⊢
  cases ht : fn.call fuel table context st args with
  | none => rw [ht] at h; simp at h
  | some t =>
    rw [ht] at h
    simp only [Option.bind_some] at h ⊢
    exact foldAns_mono hW t [] r h

theorem callCalldata_mono {W : World} (hW : ExtendsClosed W) (fuel : Nat) (contract : Contract)
    (base : Context) (state : Source.State) (self sender value : SolidCore.Solidity.Source.Word)
    (calldata : ABI.Bytes) {x : ABI.AbiCallResult}
    (h : Source.ABI.Oracle.callCalldata closedAns fuel contract base state self sender value calldata =
      some x) :
    Source.ABI.Oracle.callCalldata W.ans fuel contract base state self sender value calldata =
      some x := by
  unfold Source.ABI.Oracle.callCalldata at h ⊢
  split at h
  · rename_i selector _
    split at h
    · rename_i function _
      split at h
      · rename_i args _
        split at h
        · rename_i hv
          simp only [hv, ↓reduceIte]
          dsimp only at h ⊢
          cases hc : Source.callAns closedAns fuel contract.table
              (ABI.Contract.callContextAtWithBase contract base self sender value calldata)
              function state args with
          | none => rw [hc] at h; simp at h
          | some r =>
            rw [hc] at h
            rw [callAns_mono hW hc]
            exact h
        · rename_i hv
          simp only [hv]
          exact h
      · exact h
    · exact h
  · exact h

/-- **A closed-world run is a run in every world that extends it**, when the account code during the
call is the contract's own context's. -/
theorem runIn_of_run {W : World} (hW : ExtendsClosed W) {fuel : Nat}
    {c : TypeCheck.CheckedContract} (hcodes : W.codes.getD c.core.context.accountCodes =
      c.core.context.accountCodes) {call : Call} {obs : Observable}
    (h : Source.run fuel c call = some obs) : Source.runIn W fuel c call = some obs := by
  rw [← Source.runIn_closed] at h
  unfold Source.runIn Source.resultIn? at h ⊢
  simp only [World.closed, Option.getD_none] at h
  simp only [hcodes]
  revert h
  split
  · intro h
    obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.mp h
    rw [callCalldata_mono hW _ _ _ _ _ _ _ _ hx]
    rfl
  · intro h; simp at h

/-- **A stage from `Source.run` that finishes on its scope is a stage from `Source.runIn W`**, for
every world that extends the closed one with the contract's own account code. -/
theorem stageIn_of_stage {W : World} (hW : ExtendsClosed W) {fuel : Nat} {B : SolarTV.Sem}
    {c : TypeCheck.CheckedContract} {q : B.Prog} {scope : Call → Prop}
    (hcodes : W.codes.getD c.core.context.accountCodes = c.core.context.accountCodes)
    (stage : SolarTV.Stage (solidCore fuel) B c q scope)
    (fin : ∀ call, scope call → (Source.run fuel c call).isSome) :
    SolarTV.Stage (solidCoreIn W fuel) B c q scope := by
  intro call hs obs hrun
  obtain ⟨obs', h'⟩ := Option.isSome_iff_exists.mp (fin call hs)
  have hin := runIn_of_run hW hcodes h'
  change Source.runIn W fuel c call = some obs at hrun
  rw [hin] at hrun
  cases hrun
  exact stage call hs obs h'

/-- info: 'SolidCore.Refinement.stageIn_of_stage' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms stageIn_of_stage

end SolidCore.Refinement

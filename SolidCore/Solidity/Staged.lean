import SolidCore.Solidity.Checked

/-!
# A contract's translation from its stages

`CheckedInput.contract_ok_of_stages`: a source unit's contract type checks and translates when the
type check returns the source, the type resolution of the checked program finds the contract,
and the raw declaration's translation by its storage and dispatch orders succeeds. Each premise is
a closed computation a contract's module checks in a declaration of its own, the last one through
the stages of `ContractDecl.toCoreFromOrders?` (its context, function groups and assembly), so
that no single kernel check holds the whole translation.
-/

namespace SolidCore.Solidity.TypeCheck

/-- A source unit's contract type checks and translates by its stages. -/
theorem CheckedInput.contract_ok_of_stages (src : SourceUnitAst) (name : Name)
    (rd : SourceContractDecl) (so dO : List SourceContractDecl)
    (hck : TypecheckedInput.checkedSourceUnit src = .ok { source := src })
    (hf : (match (CheckedProgram.fromChecked? { source := src }).bind
        (fun p => CheckedProgram.findSourceContract? p name) with
      | some d => d.name == name
      | none => false) = true)
    (hraw : Executable.SourceUnit.findContract? src name = some rd)
    (hso : Executable.ContractDecl.storageOrder? (Executable.SourceUnit.contracts src) rd = some so)
    (hdo : Executable.ContractDecl.dispatchOrder? (Executable.SourceUnit.contracts src) rd = some dO)
    (hcore : ∃ core, Executable.ContractDecl.toCoreFromOrders? (Executable.SourceUnit.contracts src)
      (Executable.SourceUnit.usingDecls src) (Executable.SourceUnit.freeFunctions src)
      (Executable.SourceUnit.freeEvents src) (Executable.SourceUnit.freeErrors src)
      (Executable.SourceUnit.freeConstants src) (Executable.SourceUnit.freeUserValueTypes src)
      (Executable.SourceUnit.freeEnums src) (Executable.SourceUnit.freeStructs src) so dO = some core) :
    ∃ c, CheckedInput.contract src name = .ok c := by
  obtain ⟨core, hcore⟩ := hcore
  cases hp : CheckedProgram.fromChecked? { source := src } with
  | none => rw [hp] at hf; cases hf
  | some p =>
    rw [hp] at hf
    cases hd : CheckedProgram.findSourceContract? p name with
    | none => simp only [Option.bind, hd] at hf; cases hf
    | some d =>
      simp only [Option.bind, hd, beq_iff_eq] at hf
      have hpc : p.checked = { source := src } := by
        unfold CheckedProgram.fromChecked? at hp
        revert hp
        cases Executable.SourceUnit.resolveSourceTypesContextual? src with
        | none => intro hp; cases hp
        | some s => intro hp; cases hp; rfl
      have hcontract : CheckedProgram.contract? p name = some { program := p, decl := d, core := core } := by
        unfold CheckedProgram.contract? CheckedProgram.toCoreContractFor?
        simp only [bind, Option.bind, hd, CheckedProgram.findRawSourceContract?, CheckedProgram.rawSource,
          CheckedProgram.rawUsingDecls, CheckedProgram.rawFreeFunctions, CheckedProgram.rawFreeEvents,
          CheckedProgram.rawFreeErrors, CheckedProgram.rawFreeConstants, CheckedProgram.rawFreeUserValueTypes,
          CheckedProgram.rawFreeEnums, CheckedProgram.rawFreeStructs, CheckedProgram.rawContracts, hpc, hf, hraw]
        unfold Executable.ContractDecl.toCoreWithBasesAndUsing?
        simp only [bind, Option.bind, hso, hdo, hcore]
      refine ⟨{ program := p, decl := d, core := core }, ?_⟩
      show (do
        let p ← (do
          let checked ← TypecheckedInput.checkedSourceUnit src
          CheckedProgram.fromChecked checked)
        CheckedProgram.contract p name) = _
      rw [hck]
      show (do let p ← CheckedProgram.fromChecked { source := src }; CheckedProgram.contract p name) = _
      unfold CheckedProgram.fromChecked
      rw [hp]
      show CheckedProgram.contract p name = _
      unfold CheckedProgram.contract
      rw [hcontract]
      rfl

/-- info: 'SolidCore.Solidity.TypeCheck.CheckedInput.contract_ok_of_stages' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CheckedInput.contract_ok_of_stages

end SolidCore.Solidity.TypeCheck

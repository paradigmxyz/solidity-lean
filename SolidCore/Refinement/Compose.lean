import SolidCore.Refinement.Statement

/-!
# Composing refinements across compiler stages

`Refines` relates a SolidCore contract to EVM bytecode in one step. A compiler
proves it in stages: Solidity to MIR, each MIR pass, MIR to EVM IR, each EVM IR
pass, and assembly. This module fixes the interface every stage's certificate
states, so that the stages compose into `Refines`.

A `Sem` is a language with a run function from a program and a `Call` to an
`Observable`, the same call and observable `Statement.lean` uses: the call data,
call value and initial storage go in; success, output bytes, logs and the final
storage function come out. `none` means the run did not finish: out of fuel,
or an error of the semantics itself.

A stage from `A` to `B` certifies `Stage A B p q scope`: on every call in
`scope` on which the source program `p` finishes, the target `q` finishes with the
same observable. Termination and fuel are each semantics' own business; a stage
only promises to preserve a finished run. `Stage.trans` composes stages, and
`refines_of_stage` turns a chain ending at EthLib into `Refines` once the source
side is known to finish on the scope.
-/

namespace SolidCore.Refinement

-- A language (Sem: programs and how one runs on a call) and a stage between two (Stage,
-- with Stage.trans) are solar's SolarTV.Sem definitions, used directly.
export SolarTV (Sem Sem.mk Stage Stage.trans)

/-- SolidCore with fixed fuel, on checked contracts. -/
def solidCore (fuel : Nat) : Sem :=
  { Prog := SolidCore.Solidity.TypeCheck.CheckedContract, run := Source.run fuel }

/-- EthLib on runtime bytecode. -/
def ethLib : Sem := { Prog := ByteArray, run := Target.run }

/-- SolidCore with fixed fuel, on checked contracts, called from the account `caller`. -/
def solidCoreFrom (caller fuel : Nat) : Sem :=
  { Prog := SolidCore.Solidity.TypeCheck.CheckedContract, run := Source.runFrom caller fuel }

/-- EthLib on runtime bytecode, called from the account `caller`. -/
def ethLibFrom (caller : Nat) : Sem := { Prog := ByteArray, run := Target.runFrom caller }

theorem solidCoreFrom_callerAddress (fuel : Nat) : solidCoreFrom callerAddress fuel = solidCore fuel :=
  rfl

theorem ethLibFrom_callerAddress : ethLibFrom callerAddress = ethLib := by
  unfold ethLibFrom ethLib
  rw [Target.runFrom_callerAddress]

/-- A chain of stages from SolidCore to EthLib gives `Refines` on the calls where
SolidCore finishes. -/
theorem refines_of_stage {fuel : Nat} {contract : SolidCore.Solidity.TypeCheck.CheckedContract}
    {code : ByteArray} {scope : Call → Prop}
    (h : Stage (solidCore fuel) ethLib contract code scope)
    (fin : ∀ call, scope call → (Source.run fuel contract call).isSome) :
    Refines fuel contract code scope := by
  intro call hc
  obtain ⟨obs, hobs⟩ := Option.isSome_iff_exists.mp (fin call hc)
  exact ⟨obs, hobs, h call hc obs hobs⟩

/-- `Refines` is a stage from SolidCore to EthLib. -/
theorem stage_of_refines {fuel : Nat} {contract : SolidCore.Solidity.TypeCheck.CheckedContract}
    {code : ByteArray} {scope : Call → Prop} (h : Refines fuel contract code scope) :
    Stage (solidCore fuel) ethLib contract code scope := by
  intro call hc obs hobs
  obtain ⟨obs', h1, h2⟩ := h call hc
  have : obs' = obs := Option.some.inj (h1.symm.trans hobs)
  exact this ▸ h2

end SolidCore.Refinement

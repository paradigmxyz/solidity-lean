import SolidCore.Refinement.Compose

/-!
# Specifications carried from SolidCore to bytecode

A specification of a contract is a precondition on the call and a postcondition on
the call and its observable. `Satisfies S p scope pre post` says that the program
`p` of the semantics `S` finishes every call in `scope` that meets `pre` with an
observable that meets `post`: total correctness, stated over the same `Call` and
`Observable` as every stage.

A stage preserves every observable a finished run gives, so it carries a specification
from its source to its target (`Satisfies.of_stage`). This gives the end-to-end form
used for verified contracts: a specification proved of SolidCore holds of the bytecode

* directly, from a proof of `Refines` (`bytecode_of_refines`), or
* through a compiler's stages (`bytecode_of_stages`): SolidCore to lowered MIR, lowered
  MIR to EVM IR, and EVM IR to bytecode. Each stage is a hypothesis named after the
  obligation that discharges it.

`C1.satisfies_bytecode` (`SolidCore.Refinement.C1.Spec`, outside the default library, since its
SolidCore side uses `native_decide`) instantiates the first form for c1 with no hypothesis left,
and `C1.satisfies_bytecode_staged` the second, with its three stages as hypotheses.
-/

namespace SolidCore.Refinement

/-- `p` finishes every call of `scope` that meets `pre`, with an observable that meets
`post`. -/
def Satisfies (S : Sem) (p : S.Prog) (scope : Call → Prop) (pre : Call → Prop)
    (post : Call → Observable → Prop) : Prop :=
  ∀ call, scope call → pre call → ∃ obs, S.run p call = some obs ∧ post call obs

/-- A stage carries a specification from its source program to its target program. -/
theorem Satisfies.of_stage {A B : Sem} {p : A.Prog} {q : B.Prog} {scope : Call → Prop}
    {pre : Call → Prop} {post : Call → Observable → Prop}
    (h : Satisfies A p scope pre post) (stage : Stage A B p q scope) :
    Satisfies B q scope pre post := by
  intro call hc hp
  obtain ⟨obs, hrun, hpost⟩ := h call hc hp
  exact ⟨obs, stage call hc obs hrun, hpost⟩

/-- A specification SolidCore satisfies holds of bytecode that refines it. -/
theorem bytecode_of_refines {fuel : Nat} {contract : SolidCore.Solidity.TypeCheck.CheckedContract}
    {code : ByteArray} {scope : Call → Prop} {pre : Call → Prop}
    {post : Call → Observable → Prop}
    (spec : Satisfies (solidCore fuel) contract scope pre post)
    (refines : Refines fuel contract code scope) :
    Satisfies ethLib code scope pre post :=
  spec.of_stage (stage_of_refines refines)

/-- A specification SolidCore satisfies holds of the bytecode a compiler produces through
lowered MIR and EVM IR, given each of its stages.

* `lowering`: SolidCore to lowered MIR, including ABI decoding and dispatch
  (`lower-abi`, `lower-dispatch`); this library's stage, not yet proved generically.
* `backend`: lowered MIR through the MIR passes, stack scheduling and the EVM IR passes;
  solar's `mir_to_evmir_certified`, from per-pass certificates.
* `assembly`: EVM IR to runtime bytecode on EthLib; solar's `AssemblyStage`. -/
theorem bytecode_of_stages {fuel : Nat} {mirSem evmirSem : Sem}
    {contract : SolidCore.Solidity.TypeCheck.CheckedContract} {mir : mirSem.Prog}
    {evmir : evmirSem.Prog} {code : ByteArray} {scope : Call → Prop} {pre : Call → Prop}
    {post : Call → Observable → Prop}
    (spec : Satisfies (solidCore fuel) contract scope pre post)
    (lowering : Stage (solidCore fuel) mirSem contract mir scope)
    (backend : Stage mirSem evmirSem mir evmir scope)
    (assembly : Stage evmirSem ethLib evmir code scope) :
    Satisfies ethLib code scope pre post :=
  spec.of_stage ((lowering.trans backend).trans assembly)

end SolidCore.Refinement

import Contracts.Reader.Core
import Contracts.Reader.Fn
import Contracts.CallFamilies.SourceFacts

/-!
# Facts of SolidCore's checked `Reader`

The kernel evaluates the type checker on `Reader`'s source once (`kernel_rfl`, with the selectors
from `Core`'s table) and compares the result with the literals the source stage uses: `read`'s
lowered body (`readFn`), no storage fields, no seeded accounts, and a constructor that leaves no
storage, logs, transient storage or adopted world (`reader_facts`).
-/

namespace SolidCore.Refinement.Reader

open SolarTV SolidCore.Refinement SolidCore.Refinement.Generic
open SolidCore.Solidity.Source EvmCompiler.Simulation
open SolidCore.Verify.VC.Reader (contract? fuel)

/-- What the constructor of `c` leaves: no storage, no logs, no transient storage, no adopted
world. -/
def deployFacts (c : SolidCore.Solidity.TypeCheck.CheckedContract) : Bool :=
  match SolidCore.Solidity.TypeCheck.CheckedContract.constructWithContext? fuel c (Wide.ctxOf c)
      State.empty selfAddress 0 [] with
  | some (CallResult.returned d _) =>
    d.storage.toList.isEmpty && d.events.isEmpty && d.transient.toList.isEmpty && d.envWorld?.isNone
  | _ => false

theorem deployFacts_of {c : SolidCore.Solidity.TypeCheck.CheckedContract} (h : deployFacts c = true) :
    ∃ d, Wide.DeployedAt fuel c d [] ∧ d.transient.toList = [] ∧ d.envWorld? = none := by
  unfold deployFacts at h
  split at h
  next d vs hc =>
    simp only [Bool.and_eq_true, List.isEmpty_iff, Option.isNone_iff_eq_none] at h
    exact ⟨d, ⟨⟨vs, hc⟩, h.1.1.1, h.1.1.2⟩, h.1.2, h.2⟩
  next => simp at h

/-- The facts of the checked `Reader` the source stage takes. -/
def readerFacts : Option (Option FunctionDef × List StorageField × Bool) :=
  match contract? with
  | .ok c => some (c.core.findFunctionBySelector? 2693245054, c.core.storageFields,
      c.core.context.accountBalances.isEmpty && c.core.context.accountCodehashes.isEmpty &&
        c.core.context.accountCodes.isEmpty && deployFacts c)
  | .error _ => none

kernel_rfl readerFacts_eq readerFacts (some (some readFn, [], true)) using SolidCore.Verify.VC.Reader.selector_eq SolidCore.Verify.VC.mkIdx_eq

theorem reader_facts : ∃ c, contract? = .ok c ∧
    c.core.findFunctionBySelector? 2693245054 = some readFn ∧
    c.core.storageFields = [] ∧
    c.core.context.accountBalances = [] ∧ c.core.context.accountCodehashes = [] ∧
    c.core.context.accountCodes = [] ∧
    ∃ d, Wide.DeployedAt fuel c d [] ∧ d.transient.toList = [] ∧ d.envWorld? = none := by
  have h := readerFacts_eq
  unfold readerFacts at h
  split at h
  next c hc =>
    simp only [Option.some.injEq, Prod.mk.injEq, Bool.and_eq_true, List.isEmpty_iff] at h
    obtain ⟨h1, h3, ⟨⟨hb, hh⟩, hcc⟩, hdep⟩ := h
    exact ⟨c, hc, h1, h3, hb, hh, hcc, deployFacts_of hdep⟩
  next => simp at h

/-- info: 'SolidCore.Refinement.Reader.reader_facts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms reader_facts

end SolidCore.Refinement.Reader

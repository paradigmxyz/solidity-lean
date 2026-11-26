import Verify.SourceText.Grammar
import Verify.Generic.Expected
import Verify.ShapeBundle
import Verify.ShapeSpecExport
import Verify.ShapeGeneric
import SolidCore.Solidity.Shared.PrecompileCrypto

/-!
# The source-text bridge: from a file's bytes to the one expected theorem

`read` (Verify/SourceText/Grammar.lean) gives G0's reading of a source file's bytes. This module
makes the generic expected theorem's inputs from a reading. The construction is the same for
every contract, with no name, hash or shape dispatch:

* `Reading.source r fuel`: SolidCore's source of the reading's unit and contract;
* `Reading.spec r gas`: the default context, one entry per ABI function (sorted by signature),
  the valid calls of the reading's ABI and constructor storage, and the statuses and
  postcondition of the reading's spec bundle.

It then states, of the bytes alone, `SourceStatement bytes fuel gas rt`: the bytes read under G0,
and the expected theorem holds of their reading at the runtime bytes `rt`.

`statement_of_agree` is the only way in. It takes a certified `Expected src spec rt`, proved
elsewhere, and a reading equal to that certificate's `src` and `spec`, and it only transports
the theorem: a generic transport conditional on `Expected`, which it takes as a premise and
does not prove. Each instance discharges that premise with a proved certificate; Flag's instance
does so with the record's `Final.final`. No LedgerRelay instance exists. `bytecode_meets` is the property this gives on the
exact bytes, for every valid call: from the gas bound up, the run ends, a call whose
succeeds-if conditions hold succeeds, and the result meets every ensures condition (row P).

What a reading's agreement shows and what it does not: a kernel check that the importer's AST
and the spec exporter's bundle equal G0's reading of these bytes means the statement is about
the text, through G0. It does not show that G0's parse and desugaring are Solidity's meaning:
G0 is the trusted reference frontend for statements made this way (README.md).
-/

namespace SolidCore.Verify.SourceText

open SolidCore.Refinement SolidCore.Refinement.Shapes SolidCore.Verify.Generic

/-- SolidCore's source of a reading, at a fuel. -/
def Reading.source (r : Reading) (fuel : Nat) : Source := ⟨r.unit, r.contract, fuel⟩

/-- The ABI functions of a reading. -/
def Reading.fns (r : Reading) : List Abi.Fn := r.abi.map (·.2)

/-- The specification of a reading: the default context, its ABI's entries, its valid calls,
and its bundle's allowed statuses and postcondition, under the gas bound `gas`. -/
def Reading.spec (r : Reading) (gas : Nat) : Spec where
  Contexts ctx := ctx = Context.default
  entries := r.abi.map fun e => (e.1, fun _ call => genericValid [e.2] r.storage call)
  Valid _ := genericValid r.fns r.storage
  Allowed _ := bundleAllowed r.bundle ctxOfCall
  Post _ := bundlePost r.bundle ctxOfCall idStep
  gas _ := fun _ => gas
  assumptions := []

/-- The sha256 of a file's bytes. -/
def digest (bytes : List Nat) : List Nat := SolidCore.Solidity.Shared.Crypto.sha256Bytes bytes

/-- **The source-text statement**: the bytes read under G0, and the expected theorem of their
reading holds at the runtime bytes `rt`. -/
def SourceStatement (bytes : List Nat) (fuel gas : Nat) (rt : List Nat) : Prop :=
  ∃ r, read bytes = some r ∧ Expected (r.source fuel) (r.spec gas) rt

/-- **The bridge**: a certified expected theorem whose source and specification are a reading's
is the source-text statement of the bytes read. -/
theorem statement_of_agree {bytes : List Nat} {r : Reading} {fuel gas : Nat} {rt : List Nat}
    {src : Source} {spec : Spec} (hread : read bytes = some r) (hsrc : r.source fuel = src)
    (hspec : r.spec gas = spec) (h : Expected src spec rt) : SourceStatement bytes fuel gas rt :=
  ⟨r, hread, hsrc ▸ hspec ▸ h⟩

/-- **Row P: the specification on the exact bytes.** For every valid call of a reading's ABI,
from the gas bound up, the runtime bytes return a result; a call that meets a function spec's
precondition and its succeeds-if conditions succeeds; and the result meets every ensures
condition of the reading's bundle. -/
theorem bytecode_meets {bytes : List Nat} {fuel gas : Nat} {rt : List Nat}
    (h : SourceStatement bytes fuel gas rt) :
    ∃ r, read bytes = some r ∧ ∀ call, genericValid r.fns r.storage call →
      ∀ g, gas ≤ g → g < 2 ^ 256 → ∃ obs,
        runAt Context.default g (runtimeCode rt) call = some obs ∧
        (∀ fs ∈ r.bundle.spec.specs, ∀ (args : List Int) (pre : SolidCore.Spec.State),
          SolidCore.Spec.Pre r.bundle fs (ctxOfCall call) pre call args → fs.succeedsIf ≠ [] →
          r.bundle.satAll fs.succeedsIf (SolidCore.Spec.mkEnv (ctxOfCall call) args [] pre pre) →
          obs.success = true) ∧
        bundlePost r.bundle ctxOfCall idStep call obs := by
  obtain ⟨r, hr, he⟩ := h
  refine ⟨r, hr, fun call hc g hg hg' => ?_⟩
  have ha : (r.spec gas).Assumed := fun A hA => by simp [Reading.spec] at hA
  obtain ⟨-, hrun⟩ := he.bytecode_total ha (ctx := Context.default) rfl call hc
  obtain ⟨obs, hobs, hal, hpost⟩ := hrun g hg hg'
  exact ⟨obs, hobs, fun fs hfs args pre hpre hne hs => Or.elim hal id (absurd hs <| · fs hfs args pre hpre hne), hpost⟩

end SolidCore.Verify.SourceText

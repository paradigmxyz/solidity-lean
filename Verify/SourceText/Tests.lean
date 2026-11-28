import Verify.SourceText.Bridge
import Verify.SourceText.Cases.Selectors
import Verify.SourceText.Cases.LedgerRelay
import Verify.SourceText.Cases.LedgerRelayBody
import Verify.SourceText.Cases.LedgerRelaySpec
import Verify.SourceText.Cases.LedgerRelayName
import Verify.SourceText.Cases.LedgerRelayCaller
import Verify.SourceText.Cases.LedgerRelayStorage
import Verify.SourceText.Cases.LedgerRelayRequire
import Verify.SourceText.Cases.LedgerRelaySwap
import Verify.SourceText.Cases.LedgerRelayAlpha
import Verify.SourceText.Cases.LedgerRelayLayout
import Verify.SourceText.Cases.Flag
import Verify.SourceText.Cases.FlagBody
import Verify.SourceText.Cases.FlagSpec
import Verify.SourceText.Cases.FlagName
import Verify.SourceText.Cases.FlagCaller
import Verify.SourceText.Cases.FlagStorage
import Verify.SourceText.Cases.FlagRequire

/-!
# G0's tests: the same reader on two independent sources and their mutations

Every check here is the kernel's (`kernel_rfl`, with the selectors by the checked table of
`Cases.Selectors`, or `decide +kernel`); the only axioms are Lean's (`check.sh` prints them).

* **Agreement** (`*_agrees`): G0's reading of a case's bytes is the upstream frontend's reading of
  the same bytes (`Cases.<case>.upstream`: solc's AST through the importer, solar-verify's
  spec export, solc's ABI). The originals, the alpha-renamed and the reformatted LedgerRelay, and
  the body, spec, name and swap mutations, each against its own upstream reading.
* **Fail closed** (`*_closed`): G0 reads the caller, storage-initializer and require mutations as
  `none`, though the upstream frontend accepts all three.
* **Rejection by reading** (`spec_rejects`, `name_rejects`): the spec and name mutations parse, and
  their reading is not the frozen original's: the ensures' literals differ (spec), the ABI
  signatures differ (name). Never by the bytes' hash.
* **Rejection by run** (body, swap): in `TestRuns.lean`, by the kernel: each run is SolidCore's
  `Source.run`, evaluated with `Verify.VC.mkIdx_eq`, with Lean's three axioms.
* **Not here**: no check that a mutation's run breaks the original's ensures (`¬ HoldsFn`).
  A spec property on the exact bytecode exists only where a proved certificate does: Flag's,
  through `statement_of_agree` (Instances/Flag.lean). For LedgerRelay it is NOT RUN, since no
  certificate of it exists.
-/
namespace SolidCore.Verify.SourceText.Tests

open SolidCore.Refinement SolidCore.Refinement.Shapes SolidCore.Verify.SourceText

/-! ## What a reading does -/

/-- `reads h b v` proves `h : read b = v` in the kernel (`kernel_rfl`, through the definition
`h_read` and its equation `h_read_eq`), with the selectors by the table of `Cases.Selectors`. -/
local macro "reads " h:ident ppSpace b:term:max ppSpace v:term:max : command => do
  let c := Lean.mkIdent (h.getId.appendAfter "_read")
  let e := Lean.mkIdent (h.getId.appendAfter "_read_eq")
  return ⟨Lean.mkNullNode #[
    ← `(def $c := read $b),
    ← `(kernel_rfl $e $c $v using SolidCore.Verify.SourceText.Cases.Selectors.selector_eq),
    ← `(theorem $h : read $b = $v := $e)]⟩

/-- The ABI signatures of a reading. -/
def sigs (r : Reading) : List String := r.abi.map (·.1)

/-- The integer literals of a term, left to right, to depth `n`. The walk is the same for every
term; it stops at a depth bound and skips constructors it does not enter. -/
def lits : Nat → SolidCore.Spec.Term → List Int
  | 0, _ => []
  | _ + 1, .lit v => [v]
  | n + 1, .old e => lits n e
  | n + 1, .un _ e => lits n e
  | n + 1, .bin _ a b => lits n a ++ lits n b
  | n + 1, .ite c a b => lits n c ++ lits n a ++ lits n b
  | n + 1, .load _ o _ _ => lits n o
  | _, _ => []

/-- The ensures literals of every function spec of a reading. `SolidCore.Spec.Term` has no
decidable equality, so a spec mutation is told apart by these: equal readings have equal
literals. -/
def ensuresLits (r : Reading) : List (List Int) :=
  r.bundle.spec.specs.map fun fs => (fs.ensures.map (lits 64)).flatten

/-- A mutation whose bytes read as `u` parses, and is rejected against `u'` when some function of
readings tells `u` and `u'` apart. -/
theorem rejects_of {α : Type} {b : List Nat} {u u' : Reading} (f : Reading → α)
    (ha : read b = some u) (hne : f u ≠ f u') : (read b).isSome ∧ read b ≠ some u' := by
  rw [ha]
  exact ⟨rfl, fun h => hne (by cases Option.some.inj h; rfl)⟩

/-! ## LedgerRelay -/

namespace Ledger

open Cases

reads original_agrees LedgerRelay.bytes (some LedgerRelay.upstream)

/-- The record digest of the frozen bytes, sha256 8c89354e…2f6d. -/
def frozenDigest : List Nat := [0x8c, 0x89, 0x35, 0x4e, 0x56, 0xfc, 0x9a, 0xa4, 0x53, 0xca, 0xa8, 0x48,
  0x52, 0x59, 0x2a, 0xbe, 0x87, 0xcc, 0x73, 0xe3, 0xff, 0x1a, 0x64, 0xda, 0x8a, 0x37, 0x44, 0x18,
  0x95, 0x38, 0x2f, 0x6d]
theorem digest_eq : digest LedgerRelay.bytes = frozenDigest := by decide +kernel

reads alpha_agrees LedgerRelayAlpha.bytes (some LedgerRelayAlpha.upstream)
reads layout_agrees LedgerRelayLayout.bytes (some LedgerRelayLayout.upstream)
reads body_agrees LedgerRelayBody.bytes (some LedgerRelayBody.upstream)
reads spec_agrees LedgerRelaySpec.bytes (some LedgerRelaySpec.upstream)
reads name_agrees LedgerRelayName.bytes (some LedgerRelayName.upstream)
reads swap_agrees LedgerRelaySwap.bytes (some LedgerRelaySwap.upstream)

def readCaller := read LedgerRelayCaller.bytes
kernel_rfl readCaller_eq readCaller none using Cases.Selectors.selector_eq
theorem caller_closed : read LedgerRelayCaller.bytes = none := readCaller_eq

reads storage_closed LedgerRelayStorage.bytes none
reads require_closed LedgerRelayRequire.bytes none

/-! ### Rejection: each mutation parses, and its reading is not the original's -/

def nameSigs := (read LedgerRelayName.bytes).map sigs
kernel_rfl nameSigs_eq nameSigs (some ["left()", "relay(uint256)", "right()", "setPairs(uint256,uint256)", "stamp()"]) using Cases.Selectors.selector_eq

theorem name_rejects : (read LedgerRelayName.bytes).isSome ∧ read LedgerRelayName.bytes ≠ some LedgerRelay.upstream :=
  rejects_of sigs name_agrees (by decide +kernel)

theorem spec_rejects : (read LedgerRelaySpec.bytes).isSome ∧ read LedgerRelaySpec.bytes ≠ some LedgerRelay.upstream :=
  rejects_of ensuresLits spec_agrees (by decide +kernel)

end Ledger

/-! ## Flag (the record's source) -/

namespace FlagCases

open Cases

reads original_agrees Flag.bytes (some Flag.upstream)
reads body_agrees FlagBody.bytes (some FlagBody.upstream)
reads spec_agrees FlagSpec.bytes (some FlagSpec.upstream)
reads name_agrees FlagName.bytes (some FlagName.upstream)
reads caller_closed FlagCaller.bytes none
reads storage_closed FlagStorage.bytes none
reads require_closed FlagRequire.bytes none

theorem spec_rejects : (read FlagSpec.bytes).isSome ∧ read FlagSpec.bytes ≠ some Flag.upstream :=
  rejects_of ensuresLits spec_agrees (by decide +kernel)

def nameSigs := (read FlagName.bytes).map sigs
kernel_rfl nameSigs_eq nameSigs (some ["lower()", "raised()", "raises(uint256)", "value()"]) using Cases.Selectors.selector_eq

theorem name_rejects : (read FlagName.bytes).isSome ∧ read FlagName.bytes ≠ some Flag.upstream :=
  rejects_of sigs name_agrees (by decide +kernel)

end FlagCases

end SolidCore.Verify.SourceText.Tests

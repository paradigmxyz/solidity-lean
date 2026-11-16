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
  `Source.run` through `run_eq_runTree` (Run.lean), with Lean's three axioms.
* **Not here**: no check that a mutation's run breaks the original's ensures (`¬ HoldsFn`).
  A spec property on the exact bytecode exists only where a proved certificate does: Flag's,
  through `statement_of_agree` (Instances/Flag.lean). For LedgerRelay it is NOT RUN, since no
  certificate of it exists.
-/
namespace SolidCore.Verify.SourceText.Tests

open SolidCore.Refinement SolidCore.Refinement.Shapes SolidCore.Verify.SourceText

/-! ## What a reading does -/

/-- The ABI signatures of a reading. -/
def sigs (o : Option Reading) : Option (List String) := o.map (·.abi.map (·.1))

/-! ## LedgerRelay -/

namespace Ledger

open Cases

def read0 := read LedgerRelay.bytes
kernel_rfl read0_eq read0 (some LedgerRelay.upstream) using Cases.Selectors.selector_eq
theorem original_agrees : read LedgerRelay.bytes = some LedgerRelay.upstream := read0_eq

/-- The record digest of the frozen bytes, sha256 8c89354e…2f6d. -/
def frozenDigest : List Nat := [0x8c, 0x89, 0x35, 0x4e, 0x56, 0xfc, 0x9a, 0xa4, 0x53, 0xca, 0xa8, 0x48,
  0x52, 0x59, 0x2a, 0xbe, 0x87, 0xcc, 0x73, 0xe3, 0xff, 0x1a, 0x64, 0xda, 0x8a, 0x37, 0x44, 0x18,
  0x95, 0x38, 0x2f, 0x6d]
theorem digest_eq : digest LedgerRelay.bytes = frozenDigest := by decide +kernel

def readAlpha := read LedgerRelayAlpha.bytes
kernel_rfl readAlpha_eq readAlpha (some LedgerRelayAlpha.upstream) using Cases.Selectors.selector_eq
theorem alpha_agrees : read LedgerRelayAlpha.bytes = some LedgerRelayAlpha.upstream := readAlpha_eq

def readLayout := read LedgerRelayLayout.bytes
kernel_rfl readLayout_eq readLayout (some LedgerRelayLayout.upstream) using Cases.Selectors.selector_eq
theorem layout_agrees : read LedgerRelayLayout.bytes = some LedgerRelayLayout.upstream := readLayout_eq

def readBody := read LedgerRelayBody.bytes
kernel_rfl readBody_eq readBody (some LedgerRelayBody.upstream) using Cases.Selectors.selector_eq
theorem body_agrees : read LedgerRelayBody.bytes = some LedgerRelayBody.upstream := readBody_eq

def readSpec := read LedgerRelaySpec.bytes
kernel_rfl readSpec_eq readSpec (some LedgerRelaySpec.upstream) using Cases.Selectors.selector_eq
theorem spec_agrees : read LedgerRelaySpec.bytes = some LedgerRelaySpec.upstream := readSpec_eq

def readName := read LedgerRelayName.bytes
kernel_rfl readName_eq readName (some LedgerRelayName.upstream) using Cases.Selectors.selector_eq
theorem name_agrees : read LedgerRelayName.bytes = some LedgerRelayName.upstream := readName_eq

def readSwap := read LedgerRelaySwap.bytes
kernel_rfl readSwap_eq readSwap (some LedgerRelaySwap.upstream) using Cases.Selectors.selector_eq
theorem swap_agrees : read LedgerRelaySwap.bytes = some LedgerRelaySwap.upstream := readSwap_eq

def readCaller := read LedgerRelayCaller.bytes
kernel_rfl readCaller_eq readCaller none using Cases.Selectors.selector_eq
theorem caller_closed : read LedgerRelayCaller.bytes = none := readCaller_eq

def readStorage := read LedgerRelayStorage.bytes
kernel_rfl readStorage_eq readStorage none using Cases.Selectors.selector_eq
theorem storage_closed : read LedgerRelayStorage.bytes = none := readStorage_eq

def readRequire := read LedgerRelayRequire.bytes
kernel_rfl readRequire_eq readRequire none using Cases.Selectors.selector_eq
theorem require_closed : read LedgerRelayRequire.bytes = none := readRequire_eq

/-! ### Rejection: each mutation parses, and its reading is not the original's -/

def nameSigs := sigs (read LedgerRelayName.bytes)
kernel_rfl nameSigs_eq nameSigs (some ["left()", "relay(uint256)", "right()", "setPairs(uint256,uint256)", "stamp()"]) using Cases.Selectors.selector_eq
def origSigs := sigs (some LedgerRelay.upstream)
kernel_rfl origSigs_eq origSigs (some ["left()", "relay(uint256)", "right()", "setPair(uint256,uint256)", "stamp()"])

theorem name_rejects : (read LedgerRelayName.bytes).isSome ∧ read LedgerRelayName.bytes ≠ some LedgerRelay.upstream := by
  refine ⟨by rw [name_agrees]; rfl, fun h => ?_⟩
  have h1 := nameSigs_eq
  unfold nameSigs at h1
  rw [h, ← origSigs.eq_def, origSigs_eq] at h1
  simp at h1

end Ledger

/-! ## Spec rejection: the literals of the ensures

`SolidCore.Spec.Term` has no decidable equality, so a spec mutation is told apart by the integer
literals of each function spec's ensures, in order: equal readings have equal literals. The walk
is the same for every term; it stops at a depth bound and skips constructors it does not enter. -/

/-- The integer literals of a term, left to right, to depth `n`. -/
def lits : Nat → SolidCore.Spec.Term → List Int
  | 0, _ => []
  | _ + 1, .lit v => [v]
  | n + 1, .old e => lits n e
  | n + 1, .un _ e => lits n e
  | n + 1, .bin _ a b => lits n a ++ lits n b
  | n + 1, .ite c a b => lits n c ++ lits n a ++ lits n b
  | n + 1, .load _ o _ _ => lits n o
  | _, _ => []

/-- The ensures literals of every function spec of a reading. -/
def ensuresLits (o : Option Reading) : Option (List (List Int)) :=
  o.map fun r => r.bundle.spec.specs.map fun fs => (fs.ensures.map (lits 64)).flatten

theorem ne_of_ensuresLits {o : Option Reading} {r : Reading} (h : ensuresLits o ≠ ensuresLits (some r)) :
    o ≠ some r := fun he => h (he ▸ rfl)

namespace Ledger

open Cases

def specText := ensuresLits (read LedgerRelaySpec.bytes)
def origText := ensuresLits (some LedgerRelay.upstream)

theorem spec_rejects : (read LedgerRelaySpec.bytes).isSome ∧ read LedgerRelaySpec.bytes ≠ some LedgerRelay.upstream := by
  refine ⟨by rw [spec_agrees]; rfl, ne_of_ensuresLits ?_⟩
  show specText ≠ origText
  decide +kernel

end Ledger

/-! ## Flag (the record's source) -/

namespace FlagCases

open Cases

def read0 := read Flag.bytes
kernel_rfl read0_eq read0 (some Flag.upstream) using Cases.Selectors.selector_eq
theorem original_agrees : read Flag.bytes = some Flag.upstream := read0_eq

def readBody := read FlagBody.bytes
kernel_rfl readBody_eq readBody (some FlagBody.upstream) using Cases.Selectors.selector_eq
theorem body_agrees : read FlagBody.bytes = some FlagBody.upstream := readBody_eq

def readSpec := read FlagSpec.bytes
kernel_rfl readSpec_eq readSpec (some FlagSpec.upstream) using Cases.Selectors.selector_eq
theorem spec_agrees : read FlagSpec.bytes = some FlagSpec.upstream := readSpec_eq

def readName := read FlagName.bytes
kernel_rfl readName_eq readName (some FlagName.upstream) using Cases.Selectors.selector_eq
theorem name_agrees : read FlagName.bytes = some FlagName.upstream := readName_eq

def readCaller := read FlagCaller.bytes
kernel_rfl readCaller_eq readCaller none using Cases.Selectors.selector_eq
theorem caller_closed : read FlagCaller.bytes = none := readCaller_eq

def readStorage := read FlagStorage.bytes
kernel_rfl readStorage_eq readStorage none using Cases.Selectors.selector_eq
theorem storage_closed : read FlagStorage.bytes = none := readStorage_eq

def readRequire := read FlagRequire.bytes
kernel_rfl readRequire_eq readRequire none using Cases.Selectors.selector_eq
theorem require_closed : read FlagRequire.bytes = none := readRequire_eq

def specText := ensuresLits (read FlagSpec.bytes)
def origText := ensuresLits (some Flag.upstream)

theorem spec_rejects : (read FlagSpec.bytes).isSome ∧ read FlagSpec.bytes ≠ some Flag.upstream := by
  refine ⟨by rw [spec_agrees]; rfl, ne_of_ensuresLits ?_⟩
  show specText ≠ origText
  decide +kernel

def nameSigs := sigs (read FlagName.bytes)
kernel_rfl nameSigs_eq nameSigs (some ["lower()", "raised()", "raises(uint256)", "value()"]) using Cases.Selectors.selector_eq
def origSigs := sigs (some Flag.upstream)
kernel_rfl origSigs_eq origSigs (some ["lower()", "raise(uint256)", "raised()", "value()"])

theorem name_rejects : (read FlagName.bytes).isSome ∧ read FlagName.bytes ≠ some Flag.upstream := by
  refine ⟨by rw [name_agrees]; rfl, fun h => ?_⟩
  have h1 := nameSigs_eq
  unfold nameSigs at h1
  rw [h, ← origSigs.eq_def, origSigs_eq] at h1
  simp at h1

end FlagCases

end SolidCore.Verify.SourceText.Tests

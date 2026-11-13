import SolidCore.Spec.Contract
import SolidCore.Spec.Ghost

/-!
# solar-verify's trusted base, as named hypotheses

solar-verify's ✔ is a claim of its own (crates/verify/README.md, "Trusted base"), checked by
Rust code and SMT solvers rather than by Lean's kernel. This module states that claim as one
proposition about the spec's meaning (`Verdict`), with every assumption of its model a separate,
named field of `Assumptions`, so that a theorem that rests on it says so in its statement and
never through an axiom. `spec_of_verdict` is the final theorem: the verdict on the source
semantics, and a kernel-checked refinement from the source to the bytecode, give the spec of the
bytecode on the calls where the assumptions hold. A spec proved of SolidCore in Lean instead
(`SolidCore.Spec.Solar.C4`) needs none of this.

The items, in the README's order, and where each one is in the statement:

1. "The parser, the encoding in `src/vc.rs` and `src/vc/yul.rs`, and the solvers": `Verdict`
   itself. This includes that solar-verify's model of a function with its ghost code is a program
   whose erasure is the function SolidCore runs; erasure itself is proved, not trusted
   (`SolidCore.Spec.Ghost.spec_of_erased`), on a core language with solar-verify's discipline.
2. "`@custom:assume`, `@custom:trusted` and interface ensures": `Assumptions.assumptionsHold`.
3. "No `delegatecall` into the contract": `Assumptions.noDelegatecall`. It matters across calls:
   the storage a call starts from is the one the previous call left.
4. "`keccak256` is injective and its results lie in `[2^128, 2^256)`": `Assumptions.keccakSeparated`,
   per call. Stated for all inputs it is false (keccak256 maps unboundedly many inputs to 2^256
   words, and some 64-byte input almost surely hashes below 2^128), and a false hypothesis would
   make every theorem that takes it vacuous; per call it says only that the hashes this call
   computes are separated, which is what the encoding uses.
5. "Raw storage slots that assembly reaches are disjoint from the declared state variables, and
   assembly is memory-safe": `Assumptions.asmSlotsDisjoint`, `Assumptions.asmMemorySafe`.
6. "A library named `Math` with a `mulDiv` ... is summarized as OpenZeppelin's": `Assumptions.mulDiv`.
7. "A high-level call to a view or pure function answers as a function of its target, its
   arguments and the state it can read": `Assumptions.viewCalls`.

Two more obligations come from giving specs a meaning, and are checked rather than trusted: every
spec function call resolves and nests within the exported fuel (`Bundle.WF`, by the kernel's
evaluation), and an opaque spec function's body stays in its return type's range, the range
solar-verify assumes of it (`OpaqueInRange`, proved per contract).
-/

namespace SolidCore.Spec

open SolarTV

/-- The per-call and global assumptions of solar-verify's model (items 2 to 7 above). Each is a
proposition supplied by whoever states the theorem; `Assumptions.none` assumes nothing. -/
structure Assumptions where
  /-- Item 2: on this call, every `@custom:assume` holds where it is assumed, every
  `@custom:trusted` function meets its contract, and every external callee meets its interface's
  ensures. -/
  assumptionsHold : Call → Prop
  /-- Item 3: no account changes the contract's storage except through its own functions. -/
  noDelegatecall : Prop
  /-- Item 4, per call: the keccak256 images this call computes are distinct for distinct
  preimages and at least `2 ^ 128`. -/
  keccakSeparated : Call → Prop
  /-- Item 5: on this call, the raw slots inline assembly reaches are none of the declared
  variables' slots. -/
  asmSlotsDisjoint : Call → Prop
  /-- Item 5: on this call, inline assembly is memory-safe. -/
  asmMemorySafe : Call → Prop
  /-- Item 6: a library `Math.mulDiv` without specs computes OpenZeppelin's `Math.mulDiv`. -/
  mulDiv : Prop
  /-- Item 7: view and pure calls answer as a function of their target, arguments and the state
  they can read. -/
  viewCalls : Prop

/-- Every assumption, on one call. -/
def Assumptions.On (A : Assumptions) (call : Call) : Prop :=
  A.assumptionsHold call ∧ A.noDelegatecall ∧ A.keccakSeparated call ∧ A.asmSlotsDisjoint call ∧
    A.asmMemorySafe call ∧ A.mulDiv ∧ A.viewCalls

/-- No assumption at all: the case of a contract without assumes, trusted functions, external
calls, mappings, assembly or `Math.mulDiv`, or of a spec proved in Lean. -/
def Assumptions.none : Assumptions :=
  ⟨fun _ => True, True, fun _ => True, fun _ => True, fun _ => True, True, True⟩

theorem Assumptions.none_on (call : Call) : Assumptions.none.On call := by
  simp [Assumptions.On, Assumptions.none]

/-- Item 1, **solar-verify's verdict**: its ✔ on every function of the bundle means the spec
holds of the source program `p` in `S` on the calls of the scope where the assumptions hold. This
is the trusted claim; nothing in Lean proves it. -/
def Verdict (S : Sem) (p : S.Prog) (scope : Call → Prop) (b : Bundle) (ctxOf : Call → Ctx)
    (step : GhostStep) (A : Assumptions) : Prop :=
  Holds S p (fun call => scope call ∧ A.On call) b ctxOf step

/-! ## The final theorem -/

/-- **The spec of the bytecode, from solar-verify's verdict.** A kernel-checked stage from the
source semantics `S` to the target `T` (for SolidCore and EthLib, a certified translation of the
contract to its bytecode), and solar-verify's verdict on the source (trusted, item 1), give the
spec of the target on every call of the scope where the assumptions (items 2 to 7) hold. The
bundle's well-formedness and the opaque functions' ranges are hypotheses checked per contract. -/
theorem spec_of_verdict {S T : Sem} {p : S.Prog} {q : T.Prog} {scope : Call → Prop} {b : Bundle}
    {ctxOf : Call → Ctx} {step : GhostStep} {A : Assumptions}
    (_wf : b.WF = true) (_opaque : OpaqueInRange b)
    (verdict : Verdict S p scope b ctxOf step A) (stage : Stage S T p q scope) :
    Holds T q (fun call => scope call ∧ A.On call) b ctxOf step :=
  verdict.of_stage (Stage.mono stage fun _ h => h.1)

end SolidCore.Spec

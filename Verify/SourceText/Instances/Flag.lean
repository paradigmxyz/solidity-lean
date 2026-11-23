import Verify.SourceText.Bridge
import flag_4ce5cf9a.Final

/-!
# Flag (rc2-acc5-flag) through G0

The exact bytes of `Certified/flag_4ce5cf9a/flag_4ce5cf9a.sol` as certified (716 bytes, sha256
4ce5cf9a87520dc956a1e7366d5f646a07739832e44a3d8dec2eb656deb6388d; its frozen copy is
Cases/Flag.sol, pinned by CASES.sha256). Four kernel facts and one proved certificate:

* `digest_eq`: the kernel's sha256 of the bytes is the record's source digest (binding);
* `read_eq`: G0 reads the bytes to the importer's AST (`Src.importedSourceUnit`), the contract
  name, the ABI of the stages (`Lowering.fn0` to `fn3`, Solar's hints checked here against G0's own
  signatures and Keccak selectors), the spec exporter's bundle and the constructor's storage
  (agreement);
* `source_eq` and `spec_eq`: the generic constructors on that reading are the certificate's
  `src` and `spec`, by definition;
* `Final.final`: the certificate itself, proved by the record's modules, not assumed.

`flag_source_text` is then the source-text statement of the bytes, and `flag_bytecode_meets` row P.
-/

namespace SolidCore.Verify.SourceText.Flag

open SolidCore.Verify.SourceText Certified.flag_4ce5cf9a

/-- The certified source file's bytes. -/
def bytes : List Nat := [
  47, 47, 32, 83, 80, 68, 88, 45, 76, 105, 99, 101, 110, 115, 101, 45, 73, 100, 101, 110, 116, 105, 102, 105,
  101, 114, 58, 32, 77, 73, 84, 10, 112, 114, 97, 103, 109, 97, 32, 115, 111, 108, 105, 100, 105, 116, 121, 32,
  94, 48, 46, 56, 46, 50, 48, 59, 10, 10, 47, 47, 47, 32, 72, 101, 108, 100, 45, 111, 117, 116, 32, 112,
  111, 115, 105, 116, 105, 118, 101, 32, 40, 110, 111, 32, 104, 97, 110, 100, 45, 119, 114, 105, 116, 116, 101, 110,
  32, 112, 114, 111, 111, 102, 115, 41, 32, 105, 110, 115, 105, 100, 101, 32, 116, 104, 101, 32, 100, 114, 105, 118,
  101, 114, 39, 115, 32, 101, 110, 118, 101, 108, 111, 112, 101, 32, 97, 116, 32, 98, 99, 54, 100, 97, 54, 49,
  98, 32, 47, 10, 47, 47, 47, 32, 52, 52, 53, 55, 50, 99, 49, 53, 58, 32, 110, 111, 32, 99, 111, 110,
  115, 116, 114, 117, 99, 116, 111, 114, 44, 32, 108, 111, 111, 112, 44, 32, 109, 97, 112, 112, 105, 110, 103, 44,
  32, 99, 104, 101, 99, 107, 101, 100, 32, 97, 114, 105, 116, 104, 109, 101, 116, 105, 99, 44, 32, 114, 101, 97,
  115, 111, 110, 32, 115, 116, 114, 105, 110, 103, 32, 111, 114, 32, 105, 110, 116, 101, 114, 110, 97, 108, 32, 99,
  97, 108, 108, 59, 10, 47, 47, 47, 32, 101, 118, 101, 114, 121, 32, 115, 116, 97, 116, 101, 45, 99, 104, 97,
  110, 103, 105, 110, 103, 32, 102, 117, 110, 99, 116, 105, 111, 110, 32, 115, 116, 97, 116, 101, 115, 32, 119, 104,
  101, 110, 32, 105, 116, 32, 115, 117, 99, 99, 101, 101, 100, 115, 46, 10, 99, 111, 110, 116, 114, 97, 99, 116,
  32, 70, 108, 97, 103, 32, 123, 10, 32, 32, 32, 32, 117, 105, 110, 116, 50, 53, 54, 32, 112, 117, 98, 108,
  105, 99, 32, 118, 97, 108, 117, 101, 59, 10, 32, 32, 32, 32, 117, 105, 110, 116, 50, 53, 54, 32, 112, 117,
  98, 108, 105, 99, 32, 114, 97, 105, 115, 101, 100, 59, 10, 10, 32, 32, 32, 32, 47, 47, 47, 32, 64, 99,
  117, 115, 116, 111, 109, 58, 115, 117, 99, 99, 101, 101, 100, 115, 45, 105, 102, 32, 109, 115, 103, 46, 118, 97,
  108, 117, 101, 32, 61, 61, 32, 48, 10, 32, 32, 32, 32, 47, 47, 47, 32, 64, 99, 117, 115, 116, 111, 109,
  58, 101, 110, 115, 117, 114, 101, 115, 32, 118, 97, 108, 117, 101, 32, 61, 61, 32, 118, 32, 38, 38, 32, 114,
  97, 105, 115, 101, 100, 32, 61, 61, 32, 49, 10, 32, 32, 32, 32, 102, 117, 110, 99, 116, 105, 111, 110, 32,
  114, 97, 105, 115, 101, 40, 117, 105, 110, 116, 50, 53, 54, 32, 118, 41, 32, 101, 120, 116, 101, 114, 110, 97,
  108, 32, 123, 10, 32, 32, 32, 32, 32, 32, 32, 32, 118, 97, 108, 117, 101, 32, 61, 32, 118, 59, 10, 32,
  32, 32, 32, 32, 32, 32, 32, 114, 97, 105, 115, 101, 100, 32, 61, 32, 49, 59, 10, 32, 32, 32, 32, 125,
  10, 10, 32, 32, 32, 32, 47, 47, 47, 32, 64, 99, 117, 115, 116, 111, 109, 58, 115, 117, 99, 99, 101, 101,
  100, 115, 45, 105, 102, 32, 109, 115, 103, 46, 118, 97, 108, 117, 101, 32, 61, 61, 32, 48, 10, 32, 32, 32,
  32, 47, 47, 47, 32, 64, 99, 117, 115, 116, 111, 109, 58, 101, 110, 115, 117, 114, 101, 115, 32, 114, 97, 105,
  115, 101, 100, 32, 61, 61, 32, 48, 32, 38, 38, 32, 118, 97, 108, 117, 101, 32, 61, 61, 32, 111, 108, 100,
  40, 118, 97, 108, 117, 101, 41, 10, 32, 32, 32, 32, 102, 117, 110, 99, 116, 105, 111, 110, 32, 108, 111, 119,
  101, 114, 40, 41, 32, 101, 120, 116, 101, 114, 110, 97, 108, 32, 123, 10, 32, 32, 32, 32, 32, 32, 32, 32,
  114, 97, 105, 115, 101, 100, 32, 61, 32, 48, 59, 10, 32, 32, 32, 32, 125, 10, 125, 10]

/-- The record's source digest, `4ce5cf9a…388d`. -/
def recordDigest : List Nat := [0x4c, 0xe5, 0xcf, 0x9a, 0x87, 0x52, 0x0d, 0xc9, 0x56, 0xa1, 0xe7, 0x36, 0x6d, 0x5f, 0x64, 0x6a, 0x07, 0x73, 0x98, 0x32, 0xe4, 0x4a, 0x3d, 0x8d, 0xec, 0x2e, 0xb6, 0x56, 0xde, 0xb6, 0x38, 0x8d]

theorem digest_eq : digest bytes = recordDigest := by decide +kernel

/-- G0's reading of the bytes. -/
def reading? : Option Reading := read bytes

/-- The reading, from the certificate's own modules. -/
def certified : Reading :=
  { unit := Src.importedSourceUnit, contract := "Flag",
    abi := [("lower()", Lowering.fn0), ("raise(uint256)", Lowering.fn1),
            ("raised()", Lowering.fn2), ("value()", Lowering.fn3)],
    bundle := gen.Flag.Spec.Flag, storage := Lowering.storageLit }

kernel_rfl read_eq reading? (some certified) using Lowering.selector_eq

theorem source_eq : certified.source Lowering.fuel = Final.src := rfl

theorem spec_eq : certified.spec 3580203 = Final.spec := rfl

/-- **Flag's source-text statement**: its exact bytes read under G0, and the expected theorem of
their reading at the runtime bytes the pinned solar emitted. -/
theorem flag_source_text : SourceStatement bytes Lowering.fuel 3580203 Final.runtimeBytes :=
  statement_of_agree read_eq source_eq spec_eq Final.final.2

/-- Row P on Flag's exact bytes, from the proved certificate. -/
theorem flag_bytecode_meets :
    ∀ call, SolidCore.Refinement.Shapes.genericValid certified.fns certified.storage call →
      ∀ g, 3580203 ≤ g → g < 2 ^ 256 → ∃ obs,
        SolidCore.Verify.Generic.runAt SolidCore.Verify.Generic.Context.default g
          (SolidCore.Verify.Generic.runtimeCode Final.runtimeBytes) call = some obs ∧
        (∀ fs ∈ certified.bundle.spec.specs, ∀ (args : List Int) (pre : SolidCore.Spec.State),
          SolidCore.Spec.Pre certified.bundle fs (SolidCore.Refinement.Shapes.ctxOfCall call) pre call args →
          fs.succeedsIf ≠ [] →
          certified.bundle.satAll fs.succeedsIf
            (SolidCore.Spec.mkEnv (SolidCore.Refinement.Shapes.ctxOfCall call) args [] pre pre) →
          obs.success = true) ∧
        SolidCore.Refinement.Shapes.bundlePost certified.bundle SolidCore.Refinement.Shapes.ctxOfCall
          SolidCore.Refinement.Shapes.idStep call obs := by
  obtain ⟨r, hr, h⟩ := bytecode_meets flag_source_text
  have hr' : r = certified := Option.some.inj (hr.symm.trans read_eq)
  subst hr'
  exact h

end SolidCore.Verify.SourceText.Flag

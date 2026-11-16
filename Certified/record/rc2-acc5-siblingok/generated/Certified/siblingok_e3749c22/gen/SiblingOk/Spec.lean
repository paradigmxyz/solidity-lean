import Verify.Spec.Contract

/-!
Specs of `Certified/siblingok_e3749c22/siblingok_e3749c22.sol`, exported by solar-verify 0.3.0 with `--emit-lean-spec`.
Generated: do not edit.
-/

namespace Certified.siblingok_e3749c22.gen.SiblingOk.Spec

open SolidCore.Spec

/-- What the specs were exported from and are about. -/
def manifest : Manifest :=
  { source := "Certified/siblingok_e3749c22/siblingok_e3749c22.sol",
    sourceSha256 := "e3749c22494d07461b2074268882227824a84765f8afc21de6bf4da56a61ca47",
    compiler := "",
    options := [],
    bytecodeSha256 := "" }

/-- The specs of `SiblingOk`. -/
def SiblingOk : Bundle where
  fuel := 0
  spec :=
  { name := "SiblingOk",
    fns := [
    ],
    invariants := [
    ],
    ghosts := [],
    specs := [
    { name := "SiblingOk.set",
      selector := 0x60fe47b1,
      params := [(.uint 256)],
      rets := [],
      payable := false,
      requires := [],
      ensures := [
        (.bin .and (.bin .implies (.bin .le (.arg 0) (.lit 5)) (.bin .eq (.load (.slot 0) (.lit 0) 32 (.uint 256)) (.lit 2))) (.bin .implies (.bin .gt (.arg 0) (.lit 5)) (.bin .eq (.load (.slot 0) (.lit 0) 32 (.uint 256)) (.lit 1))))],
      succeedsIf := [
        (.bin .eq (.env .value) (.lit 0))] }] }

/-- Every spec function call resolves and nests within the fuel. -/
theorem SiblingOk_wf : SiblingOk.WF = true := by decide +kernel

/-- Trusted-base items these specs' proofs rely on beyond the verdict
(`SolidCore.Spec.Assumptions`). -/
def trusted : List String := []

end Certified.siblingok_e3749c22.gen.SiblingOk.Spec

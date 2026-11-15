import Verify.Spec.Contract

/-!
Specs of `Certified/flatwrong_853494c2/flatwrong_853494c2.sol`, exported by solar-verify 0.3.0 with `--emit-lean-spec`.
Generated: do not edit.
-/

namespace Certified.flatwrong_853494c2.gen.FlatWrong.Spec

open SolidCore.Spec

/-- What the specs were exported from and are about. -/
def manifest : Manifest :=
  { source := "Certified/flatwrong_853494c2/flatwrong_853494c2.sol",
    sourceSha256 := "853494c293c5dafce262aba9938695ad55f17354bdb76389f6a093dbabf3337c",
    compiler := "",
    options := [],
    bytecodeSha256 := "" }

/-- The specs of `FlatWrong`. -/
def FlatWrong : Bundle where
  fuel := 0
  spec :=
  { name := "FlatWrong",
    fns := [
    ],
    invariants := [
    ],
    ghosts := [],
    specs := [
    { name := "FlatWrong.clear",
      selector := 0x52efea6e,
      params := [],
      rets := [],
      payable := false,
      requires := [],
      ensures := [
        (.bin .eq (.load (.slot 0) (.lit 0) 32 (.uint 256)) (.lit 1))],
      succeedsIf := [
        (.bin .eq (.env .value) (.lit 0))] }] }

/-- Every spec function call resolves and nests within the fuel. -/
theorem FlatWrong_wf : FlatWrong.WF = true := by decide +kernel

/-- Trusted-base items these specs' proofs rely on beyond the verdict
(`SolidCore.Spec.Assumptions`). -/
def trusted : List String := []

end Certified.flatwrong_853494c2.gen.FlatWrong.Spec

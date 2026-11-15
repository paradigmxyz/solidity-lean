import Verify.Spec.Contract

/-!
Specs of `Certified/succwrong_35a6234e/succwrong_35a6234e.sol`, exported by solar-verify 0.3.0 with `--emit-lean-spec`.
Generated: do not edit.
-/

namespace Certified.succwrong_35a6234e.gen.SuccWrong.Spec

open SolidCore.Spec

/-- What the specs were exported from and are about. -/
def manifest : Manifest :=
  { source := "Certified/succwrong_35a6234e/succwrong_35a6234e.sol",
    sourceSha256 := "35a6234e6469f28c29c08fce8b92d8b59decd8b760e5ce51a55a5e2c48e1ce13",
    compiler := "",
    options := [],
    bytecodeSha256 := "" }

/-- The specs of `SuccWrong`. -/
def SuccWrong : Bundle where
  fuel := 0
  spec :=
  { name := "SuccWrong",
    fns := [
    ],
    invariants := [
    ],
    ghosts := [],
    specs := [
    { name := "SuccWrong.set",
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
theorem SuccWrong_wf : SuccWrong.WF = true := by decide +kernel

/-- Trusted-base items these specs' proofs rely on beyond the verdict
(`SolidCore.Spec.Assumptions`). -/
def trusted : List String := []

end Certified.succwrong_35a6234e.gen.SuccWrong.Spec

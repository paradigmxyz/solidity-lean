import Verify.Spec.Contract

/-!
Specs of `Certified/flatsuccwrong_4bba9054/flatsuccwrong_4bba9054.sol`, exported by solar-verify 0.3.0 with `--emit-lean-spec`.
Generated: do not edit.
-/

namespace Certified.flatsuccwrong_4bba9054.gen.FlatSuccWrong.Spec

open SolidCore.Spec

/-- What the specs were exported from and are about. -/
def manifest : Manifest :=
  { source := "Certified/flatsuccwrong_4bba9054/flatsuccwrong_4bba9054.sol",
    sourceSha256 := "4bba9054d55323c22a293e4082d625f48c0cba2a0791193d4a0105562aacb02a",
    compiler := "",
    options := [],
    bytecodeSha256 := "" }

/-- The specs of `FlatSuccWrong`. -/
def FlatSuccWrong : Bundle where
  fuel := 0
  spec :=
  { name := "FlatSuccWrong",
    fns := [
    ],
    invariants := [
    ],
    ghosts := [],
    specs := [
    { name := "FlatSuccWrong.halt",
      selector := 0x5ed7ca5b,
      params := [],
      rets := [],
      payable := false,
      requires := [],
      ensures := [
        (.bin .eq (.load (.slot 0) (.lit 0) 32 (.uint 256)) (.old (.load (.slot 0) (.lit 0) 32 (.uint 256))))],
      succeedsIf := [
        (.bin .eq (.env .value) (.lit 0))] }] }

/-- Every spec function call resolves and nests within the fuel. -/
theorem FlatSuccWrong_wf : FlatSuccWrong.WF = true := by decide +kernel

/-- Trusted-base items these specs' proofs rely on beyond the verdict
(`SolidCore.Spec.Assumptions`). -/
def trusted : List String := []

end Certified.flatsuccwrong_4bba9054.gen.FlatSuccWrong.Spec

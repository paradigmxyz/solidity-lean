import Verify.Spec.Contract

/-!
Specs of `Verify/SourceText/Cases/FlagSpec.sol`, exported by solar-verify 0.3.0 with `--emit-lean-spec`.
Generated: do not edit.
-/

namespace SolidCore.Verify.SourceText.Cases.FlagSpec.Spec

open SolidCore.Spec

/-- What the specs were exported from and are about. -/
def manifest : Manifest :=
  { source := "Verify/SourceText/Cases/FlagSpec.sol",
    sourceSha256 := "57717a1a0ac8a296b691becb3f50491b767702187de23d50fa93f571f86860f0",
    compiler := "",
    options := [],
    bytecodeSha256 := "" }

/-- The specs of `Flag`. -/
def Flag : Bundle where
  fuel := 0
  spec :=
  { name := "Flag",
    fns := [
    ],
    invariants := [
    ],
    ghosts := [],
    specs := [
    { name := "Flag.raise",
      selector := 0x004f4803,
      params := [(.uint 256)],
      rets := [],
      payable := false,
      requires := [],
      ensures := [
        (.bin .and (.bin .eq (.load (.slot 0) (.lit 0) 32 (.uint 256)) (.arg 0)) (.bin .eq (.load (.slot 1) (.lit 0) 32 (.uint 256)) (.lit 2)))],
      succeedsIf := [
        (.bin .eq (.env .value) (.lit 0))] },
    { name := "Flag.lower",
      selector := 0xb951486d,
      params := [],
      rets := [],
      payable := false,
      requires := [],
      ensures := [
        (.bin .and (.bin .eq (.load (.slot 1) (.lit 0) 32 (.uint 256)) (.lit 0)) (.bin .eq (.load (.slot 0) (.lit 0) 32 (.uint 256)) (.old (.load (.slot 0) (.lit 0) 32 (.uint 256)))))],
      succeedsIf := [
        (.bin .eq (.env .value) (.lit 0))] }] }

/-- Every spec function call resolves and nests within the fuel. -/
theorem Flag_wf : Flag.WF = true := by decide +kernel

/-- Trusted-base items these specs' proofs rely on beyond the verdict
(`SolidCore.Spec.Assumptions`). -/
def trusted : List String := []

end SolidCore.Verify.SourceText.Cases.FlagSpec.Spec

import Verify.Spec.Contract

/-!
Specs of `Verify/SourceText/Cases/LedgerRelayAlpha.sol`, exported by solar-verify 0.3.0 with `--emit-lean-spec`.
Generated: do not edit.
-/

namespace SolidCore.Verify.SourceText.Cases.LedgerRelayAlpha.Spec

open SolidCore.Spec

/-- What the specs were exported from and are about. -/
def manifest : Manifest :=
  { source := "Verify/SourceText/Cases/LedgerRelayAlpha.sol",
    sourceSha256 := "91ab3d81f5e1f8eae7da1cd3d85c39c0dc2544ff14c939f36a86fb5b1bda56a3",
    compiler := "",
    options := [],
    bytecodeSha256 := "" }

/-- The specs of `PairBridge`. -/
def PairBridge : Bundle where
  fuel := 0
  spec :=
  { name := "PairBridge",
    fns := [
    ],
    invariants := [
    ],
    ghosts := [],
    specs := [
    { name := "PairBridge.store",
      selector := 0x6ed28ed0,
      params := [(.uint 256), (.uint 256)],
      rets := [],
      payable := false,
      requires := [],
      ensures := [
        (.bin .and (.bin .and (.bin .eq (.load (.slot 0) (.lit 0) 32 (.uint 256)) (.arg 0)) (.bin .eq (.load (.slot 1) (.lit 0) 32 (.uint 256)) (.arg 1))) (.bin .eq (.load (.slot 2) (.lit 0) 32 (.uint 256)) (.lit 17)))],
      succeedsIf := [
        (.bin .eq (.env .value) (.lit 0))] },
    { name := "PairBridge.shift",
      selector := 0x8c1ae5d1,
      params := [(.uint 256)],
      rets := [],
      payable := false,
      requires := [],
      ensures := [
        (.bin .and (.bin .and (.bin .eq (.load (.slot 0) (.lit 0) 32 (.uint 256)) (.old (.load (.slot 1) (.lit 0) 32 (.uint 256)))) (.bin .eq (.load (.slot 1) (.lit 0) 32 (.uint 256)) (.arg 0))) (.bin .eq (.load (.slot 2) (.lit 0) 32 (.uint 256)) (.lit 3)))],
      succeedsIf := [
        (.bin .eq (.env .value) (.lit 0))] }] }

/-- Every spec function call resolves and nests within the fuel. -/
theorem PairBridge_wf : PairBridge.WF = true := by decide +kernel

/-- Trusted-base items these specs' proofs rely on beyond the verdict
(`SolidCore.Spec.Assumptions`). -/
def trusted : List String := []

end SolidCore.Verify.SourceText.Cases.LedgerRelayAlpha.Spec

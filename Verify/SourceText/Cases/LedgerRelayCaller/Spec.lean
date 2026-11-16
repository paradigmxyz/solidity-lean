import Verify.Spec.Contract

/-!
Specs of `Verify/SourceText/Cases/LedgerRelayCaller.sol`, exported by solar-verify 0.3.0 with `--emit-lean-spec`.
Generated: do not edit.
-/

namespace SolidCore.Verify.SourceText.Cases.LedgerRelayCaller.Spec

open SolidCore.Spec

/-- What the specs were exported from and are about. -/
def manifest : Manifest :=
  { source := "Verify/SourceText/Cases/LedgerRelayCaller.sol",
    sourceSha256 := "507767487ae7430488c32192f066b57b8659a8b60dd4e1999c5f330a63d532a6",
    compiler := "",
    options := [],
    bytecodeSha256 := "" }

/-- The specs of `LedgerRelay`. -/
def LedgerRelay : Bundle where
  fuel := 0
  spec :=
  { name := "LedgerRelay",
    fns := [
    ],
    invariants := [
    ],
    ghosts := [],
    specs := [
    { name := "LedgerRelay.setPair",
      selector := 0xbfbee59f,
      params := [(.uint 256), (.uint 256)],
      rets := [],
      payable := false,
      requires := [],
      ensures := [
        (.bin .and (.bin .and (.bin .eq (.load (.slot 0) (.lit 0) 32 (.uint 256)) (.arg 0)) (.bin .eq (.load (.slot 1) (.lit 0) 32 (.uint 256)) (.arg 1))) (.bin .eq (.load (.slot 2) (.lit 0) 32 (.uint 256)) (.lit 17)))],
      succeedsIf := [
        (.bin .eq (.env .sender) (.lit 0))] },
    { name := "LedgerRelay.relay",
      selector := 0xbe0d56d2,
      params := [(.uint 256)],
      rets := [],
      payable := false,
      requires := [],
      ensures := [
        (.bin .and (.bin .and (.bin .eq (.load (.slot 0) (.lit 0) 32 (.uint 256)) (.old (.load (.slot 1) (.lit 0) 32 (.uint 256)))) (.bin .eq (.load (.slot 1) (.lit 0) 32 (.uint 256)) (.arg 0))) (.bin .eq (.load (.slot 2) (.lit 0) 32 (.uint 256)) (.lit 3)))],
      succeedsIf := [
        (.bin .eq (.env .value) (.lit 0))] }] }

/-- Every spec function call resolves and nests within the fuel. -/
theorem LedgerRelay_wf : LedgerRelay.WF = true := by decide +kernel

/-- Trusted-base items these specs' proofs rely on beyond the verdict
(`SolidCore.Spec.Assumptions`). -/
def trusted : List String := []

end SolidCore.Verify.SourceText.Cases.LedgerRelayCaller.Spec

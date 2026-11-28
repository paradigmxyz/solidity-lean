import Verify.Spec.Contract

/-!
Specs of `scripts/verify/keccak/TokenSpecCollide.sol`, exported by solar-verify 0.3.0 with `--emit-lean-spec`.
Generated: do not edit.
-/

namespace SolidCore.Spec.Export.TokenSpecCollide

open SolidCore.Spec

/-- What the specs were exported from and are about. -/
def manifest : Manifest :=
  { source := "scripts/verify/keccak/TokenSpecCollide.sol",
    sourceSha256 := "ca9f9157c21b7e8648a21a62dc7c848c2a32482d7bdac6a794f649028cd1a1a9",
    compiler := "",
    options := [],
    bytecodeSha256 := "" }

/-- The specs of `Token`. -/
def Token : Bundle where
  fuel := 0
  spec :=
  { name := "Token",
    fns := [
    ],
    invariants := [
    (.bin .eq (.load (.slot 1) (.lit 0) 32 (.uint 256)) (.ghost "sumBalances" []))],
    ghosts := ["sumBalances"],
    specs := [
    { name := "Token.mint",
      selector := 0x40c10f19,
      params := [.address, (.uint 256)],
      rets := [],
      payable := false,
      requires := [],
      ensures := [
        (.bin .eq (.load (.entry (.slot 0) (.arg 0)) (.lit 0) 32 (.uint 256)) (.bin .add (.old (.load (.entry (.slot 0) (.arg 0)) (.lit 0) 32 (.uint 256))) (.arg 1))),
        (.bin .eq (.load (.slot 1) (.lit 0) 32 (.uint 256)) (.bin .add (.old (.load (.slot 1) (.lit 0) 32 (.uint 256))) (.arg 1))),
        (.all "a" .address (.bin .implies (.bin .ne (.var "a") (.arg 0)) (.bin .eq (.load (.entry (.slot 0) (.var "a")) (.lit 0) 32 (.uint 256)) (.old (.load (.entry (.slot 0) (.var "a")) (.lit 0) 32 (.uint 256))))))],
      succeedsIf := [] },
    { name := "Token.transfer",
      selector := 0xa9059cbb,
      params := [.address, (.uint 256)],
      rets := [.bool],
      payable := false,
      requires := [],
      ensures := [
        (.bin .implies (.bin .ne (.env .sender) (.arg 0)) (.bin .eq (.load (.entry (.slot 0) (.env .sender)) (.lit 0) 32 (.uint 256)) (.bin .sub (.old (.load (.entry (.slot 0) (.env .sender)) (.lit 0) 32 (.uint 256))) (.arg 1)))),
        (.bin .implies (.bin .ne (.env .sender) (.arg 0)) (.bin .eq (.load (.entry (.slot 0) (.arg 0)) (.lit 0) 32 (.uint 256)) (.bin .add (.old (.load (.entry (.slot 0) (.env .sender)) (.lit 0) 32 (.uint 256))) (.arg 1)))),
        (.all "a" .address (.bin .implies (.bin .and (.bin .ne (.var "a") (.env .sender)) (.bin .ne (.var "a") (.arg 0))) (.bin .eq (.load (.entry (.slot 0) (.var "a")) (.lit 0) 32 (.uint 256)) (.old (.load (.entry (.slot 0) (.var "a")) (.lit 0) 32 (.uint 256)))))),
        (.bin .eq (.load (.slot 1) (.lit 0) 32 (.uint 256)) (.old (.load (.slot 1) (.lit 0) 32 (.uint 256))))],
      succeedsIf := [] },
    { name := "Token.burn",
      selector := 0x42966c68,
      params := [(.uint 256)],
      rets := [],
      payable := false,
      requires := [],
      ensures := [
        (.bin .eq (.load (.entry (.slot 0) (.env .sender)) (.lit 0) 32 (.uint 256)) (.bin .sub (.old (.load (.entry (.slot 0) (.env .sender)) (.lit 0) 32 (.uint 256))) (.arg 0)))],
      succeedsIf := [] }] }

/-- Every spec function call resolves and nests within the fuel. -/
theorem Token_wf : Token.WF = true := by decide +kernel

/-- Trusted-base items these specs' proofs rely on beyond the verdict
(`SolidCore.Spec.Assumptions`). -/
def trusted : List String := []

end SolidCore.Spec.Export.TokenSpecCollide

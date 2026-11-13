import SolidCore.Spec.Contract

/-!
Specs of `scripts/refinement/spec/c4.sol`, exported by solar-verify 0.3.0 with `--emit-lean-spec`.
Generated: do not edit.
-/

namespace SolidCore.Spec.Export.C4

open SolidCore.Spec

/-- What the specs were exported from and are about. -/
def manifest : Manifest :=
  { source := "scripts/refinement/spec/c4.sol",
    sourceSha256 := "f6a3a1d0280a07e6f5697b57489f426936b41078de11390f18fe62a313a495c9",
    compiler := "solar 0.3.0-dev+commit.9688f215",
    options := [],
    bytecodeSha256 := "8a21bc207d9dd8be48d921a717eda3ecb7e5bfcb5397850bc3d64a29037fac47" }

/-- The specs of `Main`. -/
def Main : Bundle where
  fuel := 0
  spec :=
  { name := "Main",
    fns := [
    ],
    invariants := [
    ],
    ghosts := [],
    specs := [
    { name := "Main.add",
      selector := 0x02067e6a,
      params := [(.uint 8)],
      rets := [(.uint 8)],
      payable := false,
      requires := [],
      ensures := [
        (.bin .eq (.ret 0) (.bin .add (.old (.load (.slot 0) (.lit 0) 1 (.uint 8))) (.arg 0))),
        (.bin .eq (.load (.slot 0) (.lit 0) 1 (.uint 8)) (.bin .add (.old (.load (.slot 0) (.lit 0) 1 (.uint 8))) (.arg 0))),
        (.bin .eq (.load (.slot 0) (.lit 1) 1 (.uint 8)) (.bin .bxor (.old (.load (.slot 0) (.lit 1) 1 (.uint 8))) (.arg 0)))],
      succeedsIf := [
        (.bin .lt (.bin .add (.load (.slot 0) (.lit 0) 1 (.uint 8)) (.arg 0)) (.lit 256))] }] }

/-- Every spec function call resolves and nests within the fuel. -/
theorem Main_wf : Main.WF = true := by decide +kernel

/-- Trusted-base items these specs' proofs rely on beyond the verdict
(`SolidCore.Spec.Assumptions`). -/
def trusted : List String := []

end SolidCore.Spec.Export.C4

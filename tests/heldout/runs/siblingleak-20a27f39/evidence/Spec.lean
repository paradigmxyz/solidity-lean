import Verify.Spec.Contract

/-!
Specs of `Certified/siblingleak_7e2f4c33/siblingleak_7e2f4c33.sol`, exported by solar-verify 0.3.0 with `--emit-lean-spec`.
Generated: do not edit.
-/

namespace Certified.siblingleak_7e2f4c33.gen.SiblingLeak.Spec

open SolidCore.Spec

/-- What the specs were exported from and are about. -/
def manifest : Manifest :=
  { source := "Certified/siblingleak_7e2f4c33/siblingleak_7e2f4c33.sol",
    sourceSha256 := "7e2f4c33f69309afa5ba3464dd1eb172b5b81fe33cf98d9bc61d3a45e4b1eef2",
    compiler := "",
    options := [],
    bytecodeSha256 := "" }

/-- The specs of `SiblingLeak`. -/
def SiblingLeak : Bundle where
  fuel := 0
  spec :=
  { name := "SiblingLeak",
    fns := [
    ],
    invariants := [
    ],
    ghosts := [],
    specs := [
    { name := "SiblingLeak.set",
      selector := 0x60fe47b1,
      params := [(.uint 256)],
      rets := [],
      payable := false,
      requires := [],
      ensures := [
        (.bin .implies (.bin .le (.arg 0) (.lit 5)) (.bin .eq (.load (.slot 0) (.lit 0) 32 (.uint 256)) (.lit 1)))],
      succeedsIf := [
        (.bin .eq (.env .value) (.lit 0))] }] }

/-- Every spec function call resolves and nests within the fuel. -/
theorem SiblingLeak_wf : SiblingLeak.WF = true := by decide +kernel

/-- Trusted-base items these specs' proofs rely on beyond the verdict
(`SolidCore.Spec.Assumptions`). -/
def trusted : List String := []

end Certified.siblingleak_7e2f4c33.gen.SiblingLeak.Spec

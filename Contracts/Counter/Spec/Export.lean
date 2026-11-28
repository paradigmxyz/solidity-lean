import Verify.Spec.Contract

/-!
Specs of `scripts/verify/CounterMilestone.sol`, exported by solar-verify 0.3.0 with `--emit-lean-spec`.
Generated: do not edit.
-/

namespace SolidCore.Spec.Export.Counter

open SolidCore.Spec

/-- What the specs were exported from and are about. -/
def manifest : Manifest :=
  { source := "scripts/verify/CounterMilestone.sol",
    sourceSha256 := "6ed83fe1a6c41fb109c6a880ed372b37ca1d895b9bde4bb5f202461289706da9",
    compiler := "0.8.38+commit.1134e61f.solar.0.3.0-dev",
    options := [],
    bytecodeSha256 := "daed21b0c790bb2c08bcf999c9ebc6fea950c213ea0a799418552aa14c18f6ec" }

/-- The specs of `Counter`. -/
def Counter : Bundle where
  fuel := 0
  spec :=
  { name := "Counter",
    fns := [
    ],
    invariants := [
    ],
    ghosts := [],
    specs := [
    { name := "Counter.inc",
      selector := 0x812600df,
      params := [(.uint 256)],
      rets := [],
      payable := false,
      requires := [],
      ensures := [
        (.bin .eq (.load (.slot 0) (.lit 0) 32 (.uint 256)) (.bin .add (.old (.load (.slot 0) (.lit 0) 32 (.uint 256))) (.arg 0)))],
      succeedsIf := [] }] }

/-- Every spec function call resolves and nests within the fuel. -/
theorem Counter_wf : Counter.WF = true := by decide +kernel

/-- Trusted-base items these specs' proofs rely on beyond the verdict
(`SolidCore.Spec.Assumptions`). -/
def trusted : List String := []

end SolidCore.Spec.Export.Counter

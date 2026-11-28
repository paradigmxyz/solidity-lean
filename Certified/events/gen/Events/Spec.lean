import Verify.Spec.Contract

/-!
Specs of `Certified/events/events.sol`, exported by solar-verify 0.3.0 with `--emit-lean-spec`.
Generated: do not edit.
-/

namespace Certified.events.gen.Events.Spec

open SolidCore.Spec

/-- What the specs were exported from and are about. -/
def manifest : Manifest :=
  { source := "Certified/events/events.sol",
    sourceSha256 := "c935cf243f303a252e4ee0bb10c9c75130eef92ca6c4a954830e67af9a939214",
    compiler := "",
    options := [],
    bytecodeSha256 := "" }

/-- The specs of `Events`. -/
def Events : Bundle where
  fuel := 0
  spec :=
  { name := "Events",
    fns := [
    ],
    invariants := [
    ],
    ghosts := [],
    specs := [
    { name := "Events.transfer",
      selector := 0x0cf79e0a,
      params := [(.uint 256), (.uint 256)],
      rets := [],
      payable := false,
      requires := [],
      ensures := [],
      succeedsIf := [
        (.bin .eq (.env .value) (.lit 0))] }] }

/-- Every spec function call resolves and nests within the fuel. -/
theorem Events_wf : Events.WF = true := by decide +kernel

/-- Trusted-base items these specs' proofs rely on beyond the verdict
(`SolidCore.Spec.Assumptions`). -/
def trusted : List String := []

end Certified.events.gen.Events.Spec

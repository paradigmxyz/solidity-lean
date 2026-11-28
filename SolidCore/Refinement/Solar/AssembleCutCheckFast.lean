import SolidCore.Refinement.Solar.AssembleFast
import SolidCore.Refinement.Solar.AssembleCut

/-!
# The checker with memory at any offset, in the form the kernel evaluates fast

`AssembleCut.checkC` walks the bytes with `walk`, which reads the code by index, and checks the
labels apart. `checkCS` walks the code's suffixes (`walkS`, linear in the code) and leaves the
labels' check to the walk (`labelsValid_of_walk`), as `AssembleLoop.checkLS` does for `checkL`
(Solar/AssembleCheckFast.lean). A generated execution module proves its checker run with one
kernel evaluation of the `S` form:

    theorem check_ok : checkC p code cert maxs = true := checkC_of_checkCS (by decide +kernel)
-/

namespace SolidCore.Refinement.Solar.AssembleCut

open SolidCore.Refinement.Solar.Assemble

/-- `checkC` with the walk on the code's suffixes and without the labels' check. -/
def checkCS (p : Assemble.Program) (code : ByteArray) (c : Cert) (mx : List Nat) : Bool :=
  walkS c.offset (bytesOf code) 0 (lower p c) && blocksOkC p c mx 0 p.blocks &&
    decide (c.need 0 = 0) && decide (c.top % 32 = 0) && decide (c.top ≤ 2 ^ 200) &&
    decide (code.size < 2 ^ 32) && !c.calls && !c.creates

theorem checkC_of_checkCS {p : Assemble.Program} {code : ByteArray} {c : Cert} {mx : List Nat}
    (h : checkCS p code c mx = true) : checkC p code c mx = true := by
  have hw := walkS_drop (bytesOf code) c.offset (lower p c) 0 (Nat.zero_le _)
  rw [List.drop_zero] at hw
  simp only [checkCS, hw, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨hwalk, hb⟩, h0⟩, h32⟩, htop⟩, hsize⟩, hcalls⟩, hcreates⟩ := h
  simp only [checkC, hwalk, hb, labelsValid_of_walk hwalk, h0, h32, htop, hsize, hcalls, hcreates,
    Bool.and_self]

end SolidCore.Refinement.Solar.AssembleCut

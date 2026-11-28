import SolidCore.Refinement.Solar.AssembleLoop
import SolidCore.Refinement.Solar.AssembleFast
import SolidCore.Refinement.Solar.AssembleCtxGas

/-!
# The loop checkers, in the form the kernel evaluates fast

`checkL` and `AssembleCtxGas.checkXL` walk the bytes with `walk`, which reads the code by index,
and check the labels apart. Their `S` forms walk the code's suffixes (`walkS`, linear in the code)
and leave the labels' check to the walk (`labelsValid_of_walk`). A generated certificate module
proves its checker run with one kernel evaluation of the `S` form:

    theorem check_ok : checkL p code cert maxs = true := checkL_of_checkLS (by decide +kernel)
-/

namespace SolidCore.Refinement.Solar

open Assemble

namespace AssembleLoop

/-- `checkL` with the walk on the code's suffixes and without the labels' check. -/
def checkLS (p : Program) (code : ByteArray) (c : Cert) (mx : List Nat) : Bool :=
  walkS c.offset (bytesOf code) 0 (lower p c) && blocksOkL p c mx 0 p.blocks &&
    decide (c.need 0 = 0) && decide (c.top % 32 = 0) && decide (c.top ≤ 2 ^ 32) &&
    decide (code.size < 2 ^ 32)

theorem checkL_of_checkLS {p : Program} {code : ByteArray} {c : Cert} {mx : List Nat}
    (h : checkLS p code c mx = true) : checkL p code c mx = true := by
  have hw := walkS_drop (bytesOf code) c.offset (lower p c) 0 (Nat.zero_le _)
  rw [List.drop_zero] at hw
  simp only [checkLS, hw, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨hwalk, hb⟩, h0⟩, h32⟩, htop⟩, hsize⟩ := h
  simp only [checkL, hwalk, hb, labelsValid_of_walk hwalk, h0, h32, htop, hsize, Bool.and_self]

end AssembleLoop

namespace AssembleCtxGas

/-- `checkXL` with the walk on the code's suffixes and without the labels' check. -/
def checkXLS (F : List Nat) (p : Program) (code : ByteArray) (cx : AssembleCtx.CtxCert) : Bool :=
  walkS cx.base.offset (bytesOf code) 0 (lower p cx.base) &&
    decide (cx.base.top % 32 = 0) && decide (cx.base.top ≤ 2 ^ 32) && decide (code.size < 2 ^ 32) &&
    decide (0 < cx.count 0) && decide ((cx.at 0 0).need = 0) && !F.contains 0 &&
    blocksXL F p cx 0 p.blocks

theorem checkXL_of_checkXLS {F : List Nat} {p : Program} {code : ByteArray}
    {cx : AssembleCtx.CtxCert} (h : checkXLS F p code cx = true) : checkXL F p code cx = true := by
  have hw := walkS_drop (bytesOf code) cx.base.offset (lower p cx.base) 0 (Nat.zero_le _)
  rw [List.drop_zero] at hw
  simp only [checkXLS, hw, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨hwalk, h32⟩, htop⟩, hsize⟩, hcount⟩, hneed⟩, hF⟩, hb⟩ := h
  simp only [checkXL, hwalk, labelsValid_of_walk hwalk, h32, htop, hsize, hcount, hneed, hF, hb,
    Bool.and_self]

end AssembleCtxGas

end SolidCore.Refinement.Solar

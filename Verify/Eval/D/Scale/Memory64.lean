import Verify.Eval.D.Bridge
import Verify.Eval.Common.Measure

/-! Lane D on lane A's fixture Memory64: the definitions of Verify/Eval/A/Fixtures/Memory64.lean copied
verbatim by scripts/eval/gen_d_scale.py (sha256 prefix 7ba622ada8bdbaa4), stmt proved with vcgen. -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option experimental.vcgen true
set_option grind.warning false
set_option Elab.async false

namespace Verify.Eval.D.Scale.Memory64

open SolidCore.Verify SolidCore.Verify.Eval.D
open scoped Std.WP

open SolidCore.Verify

def model : SolM (List Nat) := do
  let x ← sload 0
  sstore 100 (x + 0)
  sstore 101 (x + 1)
  sstore 102 (x + 2)
  sstore 103 (x + 3)
  sstore 104 (x + 4)
  sstore 105 (x + 5)
  sstore 106 (x + 6)
  sstore 107 (x + 7)
  sstore 108 (x + 8)
  sstore 109 (x + 9)
  sstore 110 (x + 10)
  sstore 111 (x + 11)
  sstore 112 (x + 12)
  sstore 113 (x + 13)
  sstore 114 (x + 14)
  sstore 115 (x + 15)
  sstore 116 (x + 16)
  sstore 117 (x + 17)
  sstore 118 (x + 18)
  sstore 119 (x + 19)
  sstore 120 (x + 20)
  sstore 121 (x + 21)
  sstore 122 (x + 22)
  sstore 123 (x + 23)
  sstore 124 (x + 24)
  sstore 125 (x + 25)
  sstore 126 (x + 26)
  sstore 127 (x + 27)
  sstore 128 (x + 28)
  sstore 129 (x + 29)
  sstore 130 (x + 30)
  let r0 ← sload 100
  let r1 ← sload 101
  let r2 ← sload 102
  let r3 ← sload 103
  let r4 ← sload 104
  let r5 ← sload 105
  let r6 ← sload 106
  let r7 ← sload 107
  let r8 ← sload 108
  let r9 ← sload 109
  let r10 ← sload 110
  let r11 ← sload 111
  let r12 ← sload 112
  let r13 ← sload 113
  let r14 ← sload 114
  let r15 ← sload 115
  let r16 ← sload 116
  let r17 ← sload 117
  let r18 ← sload 118
  let r19 ← sload 119
  let r20 ← sload 120
  let r21 ← sload 121
  let r22 ← sload 122
  let r23 ← sload 123
  let r24 ← sload 124
  let r25 ← sload 125
  let r26 ← sload 126
  let r27 ← sload 127
  let r28 ← sload 128
  let r29 ← sload 129
  let r30 ← sload 130
  pure [r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30]

def stmt : Prop :=
  ∀ (s : Storage) (herr : Revert → Prop),
    wp model (fun out _ _ => out = [(s 0 + 0) % 2 ^ 256, (s 0 + 1) % 2 ^ 256, (s 0 + 2) % 2 ^ 256, (s 0 + 3) % 2 ^ 256, (s 0 + 4) % 2 ^ 256, (s 0 + 5) % 2 ^ 256, (s 0 + 6) % 2 ^ 256, (s 0 + 7) % 2 ^ 256, (s 0 + 8) % 2 ^ 256, (s 0 + 9) % 2 ^ 256, (s 0 + 10) % 2 ^ 256, (s 0 + 11) % 2 ^ 256, (s 0 + 12) % 2 ^ 256, (s 0 + 13) % 2 ^ 256, (s 0 + 14) % 2 ^ 256, (s 0 + 15) % 2 ^ 256, (s 0 + 16) % 2 ^ 256, (s 0 + 17) % 2 ^ 256, (s 0 + 18) % 2 ^ 256, (s 0 + 19) % 2 ^ 256, (s 0 + 20) % 2 ^ 256, (s 0 + 21) % 2 ^ 256, (s 0 + 22) % 2 ^ 256, (s 0 + 23) % 2 ^ 256, (s 0 + 24) % 2 ^ 256, (s 0 + 25) % 2 ^ 256, (s 0 + 26) % 2 ^ 256, (s 0 + 27) % 2 ^ 256, (s 0 + 28) % 2 ^ 256, (s 0 + 29) % 2 ^ 256, (s 0 + 30) % 2 ^ 256]) herr s

#timed theorem vcgen_new : stmt := by
  unfold stmt
  intro s herr
  intros
  refine loom_wp_of_triple_pt ?_
  vcgen [model] with finish

end Verify.Eval.D.Scale.Memory64

#print axioms Verify.Eval.D.Scale.Memory64.vcgen_new
#proof_stats Verify.Eval.D.Scale.Memory64.vcgen_new
#kernel_recheck Verify.Eval.D.Scale.Memory64.vcgen_new

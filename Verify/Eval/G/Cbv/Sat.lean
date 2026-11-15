import Verify.Discharge.Sat
import Verify.Eval.G.Kernel
import Verify.Eval.G.Shared

/-!
# Lane G: cbv against decide on bounded SAT-checker leaves

The small statements of Verify/Discharge/test/sat/Sat.lean (one LRAT step checked, three bad
steps refused) and its two vc_ground leaves, each proved by decide (elaborator evaluation, then
the kernel), decide +kernel (kernel only), decide_cbv and cbv (Lean 4.35's proof-producing
call-by-value evaluation, Sym.Simp based), on the identical statement, with the elaboration time
including the kernel check (g_time), the kernel time of the proof and its auxiliary declarations
(#kernel_recheck_all), the proof size (#proof_stats) and the axioms. The whole-proof LRAT
evaluation (b8_check) is left out on purpose, and the SAT checker is untouched.

Negatives, unchanged in meaning: a step that does not check and a flipped hint must not be
provable as checking by any of the variants (fail_if_success), and vc_ground's true hypothesis
must not refute.
-/

open SolarVerify.Sat

set_option maxRecDepth 100000

g_time "s1 decide" in
theorem s1_decide : SolarVerify.Sat.check [[2], [3]] (.step ⟨3, [], [1, 2]⟩) = true := by decide
#kernel_recheck_all s1_decide
#proof_stats s1_decide
#print axioms s1_decide

g_time "s1 kernel" in
theorem s1_kernel : SolarVerify.Sat.check [[2], [3]] (.step ⟨3, [], [1, 2]⟩) = true := by decide +kernel
#kernel_recheck_all s1_kernel
#proof_stats s1_kernel
#print axioms s1_kernel

g_time "s1 dcbv" in
theorem s1_dcbv : SolarVerify.Sat.check [[2], [3]] (.step ⟨3, [], [1, 2]⟩) = true := by decide_cbv
#kernel_recheck_all s1_dcbv
#proof_stats s1_dcbv
#print axioms s1_dcbv

g_time "s1 cbv" in
theorem s1_cbv : SolarVerify.Sat.check [[2], [3]] (.step ⟨3, [], [1, 2]⟩) = true := by cbv
#kernel_recheck_all s1_cbv
#proof_stats s1_cbv
#print axioms s1_cbv

g_time "s2 decide" in
theorem s2_decide : SolarVerify.Sat.check [[2], [4]] (.step ⟨3, [], [1, 2]⟩) = false := by decide
#kernel_recheck_all s2_decide
#proof_stats s2_decide
#print axioms s2_decide

g_time "s2 kernel" in
theorem s2_kernel : SolarVerify.Sat.check [[2], [4]] (.step ⟨3, [], [1, 2]⟩) = false := by decide +kernel
#kernel_recheck_all s2_kernel
#proof_stats s2_kernel
#print axioms s2_kernel

g_time "s2 dcbv" in
theorem s2_dcbv : SolarVerify.Sat.check [[2], [4]] (.step ⟨3, [], [1, 2]⟩) = false := by decide_cbv
#kernel_recheck_all s2_dcbv
#proof_stats s2_dcbv
#print axioms s2_dcbv

g_time "s2 cbv" in
theorem s2_cbv : SolarVerify.Sat.check [[2], [4]] (.step ⟨3, [], [1, 2]⟩) = false := by cbv
#kernel_recheck_all s2_cbv
#proof_stats s2_cbv
#print axioms s2_cbv

g_time "s3 decide" in
theorem s3_decide : SolarVerify.Sat.check [[2], [3]] (.step ⟨3, [], [1, 7]⟩) = false := by decide
#kernel_recheck_all s3_decide
#proof_stats s3_decide
#print axioms s3_decide

g_time "s3 kernel" in
theorem s3_kernel : SolarVerify.Sat.check [[2], [3]] (.step ⟨3, [], [1, 7]⟩) = false := by decide +kernel
#kernel_recheck_all s3_kernel
#proof_stats s3_kernel
#print axioms s3_kernel

g_time "s3 dcbv" in
theorem s3_dcbv : SolarVerify.Sat.check [[2], [3]] (.step ⟨3, [], [1, 7]⟩) = false := by decide_cbv
#kernel_recheck_all s3_dcbv
#proof_stats s3_dcbv
#print axioms s3_dcbv

g_time "s3 cbv" in
theorem s3_cbv : SolarVerify.Sat.check [[2], [3]] (.step ⟨3, [], [1, 7]⟩) = false := by cbv
#kernel_recheck_all s3_cbv
#proof_stats s3_cbv
#print axioms s3_cbv

g_time "s4 decide" in
theorem s4_decide : SolarVerify.Sat.check [[2, 4], [3]] (.step ⟨3, [4], [1, 2]⟩) = false := by decide
#kernel_recheck_all s4_decide
#proof_stats s4_decide
#print axioms s4_decide

g_time "s4 kernel" in
theorem s4_kernel : SolarVerify.Sat.check [[2, 4], [3]] (.step ⟨3, [4], [1, 2]⟩) = false := by decide +kernel
#kernel_recheck_all s4_kernel
#proof_stats s4_kernel
#print axioms s4_kernel

g_time "s4 dcbv" in
theorem s4_dcbv : SolarVerify.Sat.check [[2, 4], [3]] (.step ⟨3, [4], [1, 2]⟩) = false := by decide_cbv
#kernel_recheck_all s4_dcbv
#proof_stats s4_dcbv
#print axioms s4_dcbv

g_time "s4 cbv" in
theorem s4_cbv : SolarVerify.Sat.check [[2, 4], [3]] (.step ⟨3, [4], [1, 2]⟩) = false := by cbv
#kernel_recheck_all s4_cbv
#proof_stats s4_cbv
#print axioms s4_cbv

g_time "g1 vc_ground" in
theorem g1_vc_ground (h : ¬ ((511#256 &&& 255#256).toNat = 255)) : False := by vc_ground
#kernel_recheck_all g1_vc_ground
#proof_stats g1_vc_ground
#print axioms g1_vc_ground

g_time "g1 decide" in
theorem g1_decide (h : ¬ ((511#256 &&& 255#256).toNat = 255)) : False := by exact absurd h (by decide)
#kernel_recheck_all g1_decide
#proof_stats g1_decide
#print axioms g1_decide

g_time "g1 kernel" in
theorem g1_kernel (h : ¬ ((511#256 &&& 255#256).toNat = 255)) : False := by exact absurd h (by decide +kernel)
#kernel_recheck_all g1_kernel
#proof_stats g1_kernel
#print axioms g1_kernel

g_time "g1 dcbv" in
theorem g1_dcbv (h : ¬ ((511#256 &&& 255#256).toNat = 255)) : False := by exact absurd h (by decide_cbv)
#kernel_recheck_all g1_dcbv
#proof_stats g1_dcbv
#print axioms g1_dcbv

g_time "g2 vc_ground" in
theorem g2_vc_ground (h : (0xff#8 - (1#8 ||| 2#8 ||| 4#8)) &&& 0x05#8 ≠ 0#8) : False := by vc_ground
#kernel_recheck_all g2_vc_ground
#proof_stats g2_vc_ground
#print axioms g2_vc_ground

g_time "g2 decide" in
theorem g2_decide (h : (0xff#8 - (1#8 ||| 2#8 ||| 4#8)) &&& 0x05#8 ≠ 0#8) : False := by exact absurd h (by decide)
#kernel_recheck_all g2_decide
#proof_stats g2_decide
#print axioms g2_decide

g_time "g2 kernel" in
theorem g2_kernel (h : (0xff#8 - (1#8 ||| 2#8 ||| 4#8)) &&& 0x05#8 ≠ 0#8) : False := by exact absurd h (by decide +kernel)
#kernel_recheck_all g2_kernel
#proof_stats g2_kernel
#print axioms g2_kernel

g_time "g2 dcbv" in
theorem g2_dcbv (h : (0xff#8 - (1#8 ||| 2#8 ||| 4#8)) &&& 0x05#8 ≠ 0#8) : False := by exact absurd h (by decide_cbv)
#kernel_recheck_all g2_dcbv
#proof_stats g2_dcbv
#print axioms g2_dcbv

/-! Negatives: every variant must fail. -/
-- satisfiable clauses: the step must not check (decide)
example : True := by
  fail_if_success have : SolarVerify.Sat.check [[2], [4]] (.step ⟨3, [], [1, 2]⟩) = true := by decide
  trivial
-- satisfiable clauses: the step must not check (kernel)
example : True := by
  fail_if_success have : SolarVerify.Sat.check [[2], [4]] (.step ⟨3, [], [1, 2]⟩) = true := by decide +kernel
  trivial
-- satisfiable clauses: the step must not check (dcbv)
example : True := by
  fail_if_success have : SolarVerify.Sat.check [[2], [4]] (.step ⟨3, [], [1, 2]⟩) = true := by decide_cbv
  trivial
-- satisfiable clauses: the step must not check (cbv)
example : True := by
  fail_if_success have : SolarVerify.Sat.check [[2], [4]] (.step ⟨3, [], [1, 2]⟩) = true := by cbv
  trivial
-- a hint naming no clause (decide)
example : True := by
  fail_if_success have : SolarVerify.Sat.check [[2], [3]] (.step ⟨3, [], [1, 7]⟩) = true := by decide
  trivial
-- a hint naming no clause (kernel)
example : True := by
  fail_if_success have : SolarVerify.Sat.check [[2], [3]] (.step ⟨3, [], [1, 7]⟩) = true := by decide +kernel
  trivial
-- a hint naming no clause (dcbv)
example : True := by
  fail_if_success have : SolarVerify.Sat.check [[2], [3]] (.step ⟨3, [], [1, 7]⟩) = true := by decide_cbv
  trivial
-- a hint naming no clause (cbv)
example : True := by
  fail_if_success have : SolarVerify.Sat.check [[2], [3]] (.step ⟨3, [], [1, 7]⟩) = true := by cbv
  trivial
-- no empty clause (decide)
example : True := by
  fail_if_success have : SolarVerify.Sat.check [[2, 4], [3]] (.step ⟨3, [4], [1, 2]⟩) = true := by decide
  trivial
-- no empty clause (kernel)
example : True := by
  fail_if_success have : SolarVerify.Sat.check [[2, 4], [3]] (.step ⟨3, [4], [1, 2]⟩) = true := by decide +kernel
  trivial
-- no empty clause (dcbv)
example : True := by
  fail_if_success have : SolarVerify.Sat.check [[2, 4], [3]] (.step ⟨3, [4], [1, 2]⟩) = true := by decide_cbv
  trivial
-- no empty clause (cbv)
example : True := by
  fail_if_success have : SolarVerify.Sat.check [[2, 4], [3]] (.step ⟨3, [4], [1, 2]⟩) = true := by cbv
  trivial
-- a true closed hypothesis gives no contradiction
example (h : (511#256 &&& 255#256).toNat = 255) : True := by
  fail_if_success have : False := by vc_ground
  trivial
-- a true closed hypothesis gives no contradiction
example (h : (511#256 &&& 255#256).toNat = 255) : True := by
  fail_if_success have : False := by exact absurd h (by decide_cbv)
  trivial
-- a true closed hypothesis gives no contradiction
example (h : (511#256 &&& 255#256).toNat = 255) : True := by
  fail_if_success have : False := by exact absurd h (by decide +kernel)
  trivial

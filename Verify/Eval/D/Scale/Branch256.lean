import Verify.Eval.D.Bridge
import Verify.Eval.Common.Measure

/-! Lane D on lane A's fixture Branch256: the definitions of Verify/Eval/A/Fixtures/Branch256.lean copied
verbatim by scripts/eval/gen_d_scale.py (sha256 prefix 1817e272a81ddbb9), stmt proved with vcgen. -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option experimental.vcgen true
set_option grind.warning false
set_option Elab.async false

namespace Verify.Eval.D.Scale.Branch256

open SolidCore.Verify SolidCore.Verify.Eval.D
open scoped Std.WP

open SolidCore.Verify

def model : SolM Unit := do
  let v0 ← sload 0
  if v0 < 2 ^ 255 then pure () else revert [0]
  sstore 1000 (v0 + v0)
  let v1 ← sload 1
  if v1 < 2 ^ 255 then pure () else revert [1]
  sstore 1001 (v1 + v1)
  let v2 ← sload 2
  if v2 < 2 ^ 255 then pure () else revert [2]
  sstore 1002 (v2 + v2)
  let v3 ← sload 3
  if v3 < 2 ^ 255 then pure () else revert [3]
  sstore 1003 (v3 + v3)
  let v4 ← sload 4
  if v4 < 2 ^ 255 then pure () else revert [4]
  sstore 1004 (v4 + v4)
  let v5 ← sload 5
  if v5 < 2 ^ 255 then pure () else revert [5]
  sstore 1005 (v5 + v5)
  let v6 ← sload 6
  if v6 < 2 ^ 255 then pure () else revert [6]
  sstore 1006 (v6 + v6)
  let v7 ← sload 7
  if v7 < 2 ^ 255 then pure () else revert [7]
  sstore 1007 (v7 + v7)
  let v8 ← sload 8
  if v8 < 2 ^ 255 then pure () else revert [8]
  sstore 1008 (v8 + v8)
  let v9 ← sload 9
  if v9 < 2 ^ 255 then pure () else revert [9]
  sstore 1009 (v9 + v9)
  let v10 ← sload 10
  if v10 < 2 ^ 255 then pure () else revert [10]
  sstore 1010 (v10 + v10)
  let v11 ← sload 11
  if v11 < 2 ^ 255 then pure () else revert [11]
  sstore 1011 (v11 + v11)
  let v12 ← sload 12
  if v12 < 2 ^ 255 then pure () else revert [12]
  sstore 1012 (v12 + v12)
  let v13 ← sload 13
  if v13 < 2 ^ 255 then pure () else revert [13]
  sstore 1013 (v13 + v13)
  let v14 ← sload 14
  if v14 < 2 ^ 255 then pure () else revert [14]
  sstore 1014 (v14 + v14)
  let v15 ← sload 15
  if v15 < 2 ^ 255 then pure () else revert [15]
  sstore 1015 (v15 + v15)
  let v16 ← sload 16
  if v16 < 2 ^ 255 then pure () else revert [16]
  sstore 1016 (v16 + v16)
  let v17 ← sload 17
  if v17 < 2 ^ 255 then pure () else revert [17]
  sstore 1017 (v17 + v17)
  let v18 ← sload 18
  if v18 < 2 ^ 255 then pure () else revert [18]
  sstore 1018 (v18 + v18)
  let v19 ← sload 19
  if v19 < 2 ^ 255 then pure () else revert [19]
  sstore 1019 (v19 + v19)
  let v20 ← sload 20
  if v20 < 2 ^ 255 then pure () else revert [20]
  sstore 1020 (v20 + v20)
  let v21 ← sload 21
  if v21 < 2 ^ 255 then pure () else revert [21]
  sstore 1021 (v21 + v21)
  let v22 ← sload 22
  if v22 < 2 ^ 255 then pure () else revert [22]
  sstore 1022 (v22 + v22)
  let v23 ← sload 23
  if v23 < 2 ^ 255 then pure () else revert [23]
  sstore 1023 (v23 + v23)
  let v24 ← sload 24
  if v24 < 2 ^ 255 then pure () else revert [24]
  sstore 1024 (v24 + v24)
  let v25 ← sload 25
  if v25 < 2 ^ 255 then pure () else revert [25]
  sstore 1025 (v25 + v25)
  let v26 ← sload 26
  if v26 < 2 ^ 255 then pure () else revert [26]
  sstore 1026 (v26 + v26)
  let v27 ← sload 27
  if v27 < 2 ^ 255 then pure () else revert [27]
  sstore 1027 (v27 + v27)
  let v28 ← sload 28
  if v28 < 2 ^ 255 then pure () else revert [28]
  sstore 1028 (v28 + v28)
  let v29 ← sload 29
  if v29 < 2 ^ 255 then pure () else revert [29]
  sstore 1029 (v29 + v29)
  let v30 ← sload 30
  if v30 < 2 ^ 255 then pure () else revert [30]
  sstore 1030 (v30 + v30)
  let v31 ← sload 31
  if v31 < 2 ^ 255 then pure () else revert [31]
  sstore 1031 (v31 + v31)
  let v32 ← sload 32
  if v32 < 2 ^ 255 then pure () else revert [32]
  sstore 1032 (v32 + v32)
  let v33 ← sload 33
  if v33 < 2 ^ 255 then pure () else revert [33]
  sstore 1033 (v33 + v33)
  let v34 ← sload 34
  if v34 < 2 ^ 255 then pure () else revert [34]
  sstore 1034 (v34 + v34)
  let v35 ← sload 35
  if v35 < 2 ^ 255 then pure () else revert [35]
  sstore 1035 (v35 + v35)
  let v36 ← sload 36
  if v36 < 2 ^ 255 then pure () else revert [36]
  sstore 1036 (v36 + v36)
  let v37 ← sload 37
  if v37 < 2 ^ 255 then pure () else revert [37]
  sstore 1037 (v37 + v37)
  let v38 ← sload 38
  if v38 < 2 ^ 255 then pure () else revert [38]
  sstore 1038 (v38 + v38)
  let v39 ← sload 39
  if v39 < 2 ^ 255 then pure () else revert [39]
  sstore 1039 (v39 + v39)
  let v40 ← sload 40
  if v40 < 2 ^ 255 then pure () else revert [40]
  sstore 1040 (v40 + v40)
  let v41 ← sload 41
  if v41 < 2 ^ 255 then pure () else revert [41]
  sstore 1041 (v41 + v41)
  let v42 ← sload 42
  if v42 < 2 ^ 255 then pure () else revert [42]
  sstore 1042 (v42 + v42)
  let v43 ← sload 43
  if v43 < 2 ^ 255 then pure () else revert [43]
  sstore 1043 (v43 + v43)
  let v44 ← sload 44
  if v44 < 2 ^ 255 then pure () else revert [44]
  sstore 1044 (v44 + v44)
  let v45 ← sload 45
  if v45 < 2 ^ 255 then pure () else revert [45]
  sstore 1045 (v45 + v45)
  let v46 ← sload 46
  if v46 < 2 ^ 255 then pure () else revert [46]
  sstore 1046 (v46 + v46)
  let v47 ← sload 47
  if v47 < 2 ^ 255 then pure () else revert [47]
  sstore 1047 (v47 + v47)
  let v48 ← sload 48
  if v48 < 2 ^ 255 then pure () else revert [48]
  sstore 1048 (v48 + v48)
  let v49 ← sload 49
  if v49 < 2 ^ 255 then pure () else revert [49]
  sstore 1049 (v49 + v49)
  let v50 ← sload 50
  if v50 < 2 ^ 255 then pure () else revert [50]
  sstore 1050 (v50 + v50)
  let v51 ← sload 51
  if v51 < 2 ^ 255 then pure () else revert [51]
  sstore 1051 (v51 + v51)
  let v52 ← sload 52
  if v52 < 2 ^ 255 then pure () else revert [52]
  sstore 1052 (v52 + v52)
  let v53 ← sload 53
  if v53 < 2 ^ 255 then pure () else revert [53]
  sstore 1053 (v53 + v53)
  let v54 ← sload 54
  if v54 < 2 ^ 255 then pure () else revert [54]
  sstore 1054 (v54 + v54)
  let v55 ← sload 55
  if v55 < 2 ^ 255 then pure () else revert [55]
  sstore 1055 (v55 + v55)
  let v56 ← sload 56
  if v56 < 2 ^ 255 then pure () else revert [56]
  sstore 1056 (v56 + v56)
  let v57 ← sload 57
  if v57 < 2 ^ 255 then pure () else revert [57]
  sstore 1057 (v57 + v57)
  let v58 ← sload 58
  if v58 < 2 ^ 255 then pure () else revert [58]
  sstore 1058 (v58 + v58)
  let v59 ← sload 59
  if v59 < 2 ^ 255 then pure () else revert [59]
  sstore 1059 (v59 + v59)
  let v60 ← sload 60
  if v60 < 2 ^ 255 then pure () else revert [60]
  sstore 1060 (v60 + v60)
  let v61 ← sload 61
  if v61 < 2 ^ 255 then pure () else revert [61]
  sstore 1061 (v61 + v61)
  let v62 ← sload 62
  if v62 < 2 ^ 255 then pure () else revert [62]
  sstore 1062 (v62 + v62)
  let v63 ← sload 63
  if v63 < 2 ^ 255 then pure () else revert [63]
  sstore 1063 (v63 + v63)
  let v64 ← sload 64
  if v64 < 2 ^ 255 then pure () else revert [64]
  sstore 1064 (v64 + v64)
  let v65 ← sload 65
  if v65 < 2 ^ 255 then pure () else revert [65]
  sstore 1065 (v65 + v65)
  let v66 ← sload 66
  if v66 < 2 ^ 255 then pure () else revert [66]
  sstore 1066 (v66 + v66)
  let v67 ← sload 67
  if v67 < 2 ^ 255 then pure () else revert [67]
  sstore 1067 (v67 + v67)
  let v68 ← sload 68
  if v68 < 2 ^ 255 then pure () else revert [68]
  sstore 1068 (v68 + v68)
  let v69 ← sload 69
  if v69 < 2 ^ 255 then pure () else revert [69]
  sstore 1069 (v69 + v69)
  let v70 ← sload 70
  if v70 < 2 ^ 255 then pure () else revert [70]
  sstore 1070 (v70 + v70)
  let v71 ← sload 71
  if v71 < 2 ^ 255 then pure () else revert [71]
  sstore 1071 (v71 + v71)
  let v72 ← sload 72
  if v72 < 2 ^ 255 then pure () else revert [72]
  sstore 1072 (v72 + v72)
  let v73 ← sload 73
  if v73 < 2 ^ 255 then pure () else revert [73]
  sstore 1073 (v73 + v73)
  let v74 ← sload 74
  if v74 < 2 ^ 255 then pure () else revert [74]
  sstore 1074 (v74 + v74)
  let v75 ← sload 75
  if v75 < 2 ^ 255 then pure () else revert [75]
  sstore 1075 (v75 + v75)
  let v76 ← sload 76
  if v76 < 2 ^ 255 then pure () else revert [76]
  sstore 1076 (v76 + v76)
  let v77 ← sload 77
  if v77 < 2 ^ 255 then pure () else revert [77]
  sstore 1077 (v77 + v77)
  let v78 ← sload 78
  if v78 < 2 ^ 255 then pure () else revert [78]
  sstore 1078 (v78 + v78)
  let v79 ← sload 79
  if v79 < 2 ^ 255 then pure () else revert [79]
  sstore 1079 (v79 + v79)
  let v80 ← sload 80
  if v80 < 2 ^ 255 then pure () else revert [80]
  sstore 1080 (v80 + v80)
  let v81 ← sload 81
  if v81 < 2 ^ 255 then pure () else revert [81]
  sstore 1081 (v81 + v81)
  let v82 ← sload 82
  if v82 < 2 ^ 255 then pure () else revert [82]
  sstore 1082 (v82 + v82)
  let v83 ← sload 83
  if v83 < 2 ^ 255 then pure () else revert [83]
  sstore 1083 (v83 + v83)
  let v84 ← sload 84
  if v84 < 2 ^ 255 then pure () else revert [84]
  sstore 1084 (v84 + v84)

def stmt : Prop :=
  ∀ (s : Storage) (herr : Revert → Prop), (∀ e, herr e) →
    wp model (fun _ _ s' =>
      s' 1000 = 2 * s 0 ∧
      s' 1001 = 2 * s 1 ∧
      s' 1002 = 2 * s 2 ∧
      s' 1003 = 2 * s 3 ∧
      s' 1004 = 2 * s 4 ∧
      s' 1005 = 2 * s 5 ∧
      s' 1006 = 2 * s 6 ∧
      s' 1007 = 2 * s 7 ∧
      s' 1008 = 2 * s 8 ∧
      s' 1009 = 2 * s 9 ∧
      s' 1010 = 2 * s 10 ∧
      s' 1011 = 2 * s 11 ∧
      s' 1012 = 2 * s 12 ∧
      s' 1013 = 2 * s 13 ∧
      s' 1014 = 2 * s 14 ∧
      s' 1015 = 2 * s 15 ∧
      s' 1016 = 2 * s 16 ∧
      s' 1017 = 2 * s 17 ∧
      s' 1018 = 2 * s 18 ∧
      s' 1019 = 2 * s 19 ∧
      s' 1020 = 2 * s 20 ∧
      s' 1021 = 2 * s 21 ∧
      s' 1022 = 2 * s 22 ∧
      s' 1023 = 2 * s 23 ∧
      s' 1024 = 2 * s 24 ∧
      s' 1025 = 2 * s 25 ∧
      s' 1026 = 2 * s 26 ∧
      s' 1027 = 2 * s 27 ∧
      s' 1028 = 2 * s 28 ∧
      s' 1029 = 2 * s 29 ∧
      s' 1030 = 2 * s 30 ∧
      s' 1031 = 2 * s 31 ∧
      s' 1032 = 2 * s 32 ∧
      s' 1033 = 2 * s 33 ∧
      s' 1034 = 2 * s 34 ∧
      s' 1035 = 2 * s 35 ∧
      s' 1036 = 2 * s 36 ∧
      s' 1037 = 2 * s 37 ∧
      s' 1038 = 2 * s 38 ∧
      s' 1039 = 2 * s 39 ∧
      s' 1040 = 2 * s 40 ∧
      s' 1041 = 2 * s 41 ∧
      s' 1042 = 2 * s 42 ∧
      s' 1043 = 2 * s 43 ∧
      s' 1044 = 2 * s 44 ∧
      s' 1045 = 2 * s 45 ∧
      s' 1046 = 2 * s 46 ∧
      s' 1047 = 2 * s 47 ∧
      s' 1048 = 2 * s 48 ∧
      s' 1049 = 2 * s 49 ∧
      s' 1050 = 2 * s 50 ∧
      s' 1051 = 2 * s 51 ∧
      s' 1052 = 2 * s 52 ∧
      s' 1053 = 2 * s 53 ∧
      s' 1054 = 2 * s 54 ∧
      s' 1055 = 2 * s 55 ∧
      s' 1056 = 2 * s 56 ∧
      s' 1057 = 2 * s 57 ∧
      s' 1058 = 2 * s 58 ∧
      s' 1059 = 2 * s 59 ∧
      s' 1060 = 2 * s 60 ∧
      s' 1061 = 2 * s 61 ∧
      s' 1062 = 2 * s 62 ∧
      s' 1063 = 2 * s 63 ∧
      s' 1064 = 2 * s 64 ∧
      s' 1065 = 2 * s 65 ∧
      s' 1066 = 2 * s 66 ∧
      s' 1067 = 2 * s 67 ∧
      s' 1068 = 2 * s 68 ∧
      s' 1069 = 2 * s 69 ∧
      s' 1070 = 2 * s 70 ∧
      s' 1071 = 2 * s 71 ∧
      s' 1072 = 2 * s 72 ∧
      s' 1073 = 2 * s 73 ∧
      s' 1074 = 2 * s 74 ∧
      s' 1075 = 2 * s 75 ∧
      s' 1076 = 2 * s 76 ∧
      s' 1077 = 2 * s 77 ∧
      s' 1078 = 2 * s 78 ∧
      s' 1079 = 2 * s 79 ∧
      s' 1080 = 2 * s 80 ∧
      s' 1081 = 2 * s 81 ∧
      s' 1082 = 2 * s 82 ∧
      s' 1083 = 2 * s 83 ∧
      s' 1084 = 2 * s 84) herr s

#timed theorem vcgen_new : stmt := by
  unfold stmt
  intro s herr
  intros
  refine loom_wp_of_triple_pt ?_
  vcgen [model] with finish

end Verify.Eval.D.Scale.Branch256

#print axioms Verify.Eval.D.Scale.Branch256.vcgen_new
#proof_stats Verify.Eval.D.Scale.Branch256.vcgen_new
#kernel_recheck Verify.Eval.D.Scale.Branch256.vcgen_new

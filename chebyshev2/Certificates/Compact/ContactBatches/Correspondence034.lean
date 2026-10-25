import chebyshev2.Certificates.Compact.ContactBatches.Batch034
import chebyshev2.Certificates.Compact.ContactCoverage
import chebyshev2.Certificates.Compact.ReferenceTrajectoryIndex

/-!
Article: chebyshev2, Section 4.1.
Correspondence034.
Use: `chebyshev2.Certificates.Compact.ContactValues.validBlock34` feeds
`chebyshev2.Certificates.Compact.ContactValues.all_valid` (all valid).
Proof chain: `chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement` —
chebyshev2, Theorem 1.2, factor 1.000013; Unconditional uniform gain comparison with the retained
numerical factor.
-/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 0
set_option maxRecDepth 200000
namespace chebyshev2.Certificates.Compact.ContactValues
theorem valid1088 : ValidPanel panel1088 := ⟨modelCheck1088,residualCheck1088,
  ReferenceTrajectory.leftBlock64_subset (List.mem_of_getElem? (show ReferenceResiduals.block64[1]?=some panel1088.left from rfl)),
  ReferenceTrajectory.rightBlock89_subset (List.mem_of_getElem? (show ReferenceResiduals.block89[6]?=some panel1088.right from rfl))⟩
theorem valid1089 : ValidPanel panel1089 := ⟨modelCheck1089,residualCheck1089,
  ReferenceTrajectory.leftBlock64_subset (List.mem_of_getElem? (show ReferenceResiduals.block64[2]?=some panel1089.left from rfl)),
  ReferenceTrajectory.rightBlock89_subset (List.mem_of_getElem? (show ReferenceResiduals.block89[5]?=some panel1089.right from rfl))⟩
theorem valid1090 : ValidPanel panel1090 := ⟨modelCheck1090,residualCheck1090,
  ReferenceTrajectory.leftBlock64_subset (List.mem_of_getElem? (show ReferenceResiduals.block64[3]?=some panel1090.left from rfl)),
  ReferenceTrajectory.rightBlock89_subset (List.mem_of_getElem? (show ReferenceResiduals.block89[4]?=some panel1090.right from rfl))⟩
theorem valid1091 : ValidPanel panel1091 := ⟨modelCheck1091,residualCheck1091,
  ReferenceTrajectory.leftBlock64_subset (List.mem_of_getElem? (show ReferenceResiduals.block64[4]?=some panel1091.left from rfl)),
  ReferenceTrajectory.rightBlock89_subset (List.mem_of_getElem? (show ReferenceResiduals.block89[3]?=some panel1091.right from rfl))⟩
theorem valid1092 : ValidPanel panel1092 := ⟨modelCheck1092,residualCheck1092,
  ReferenceTrajectory.leftBlock64_subset (List.mem_of_getElem? (show ReferenceResiduals.block64[5]?=some panel1092.left from rfl)),
  ReferenceTrajectory.rightBlock89_subset (List.mem_of_getElem? (show ReferenceResiduals.block89[2]?=some panel1092.right from rfl))⟩
theorem valid1093 : ValidPanel panel1093 := ⟨modelCheck1093,residualCheck1093,
  ReferenceTrajectory.leftBlock64_subset (List.mem_of_getElem? (show ReferenceResiduals.block64[6]?=some panel1093.left from rfl)),
  ReferenceTrajectory.rightBlock89_subset (List.mem_of_getElem? (show ReferenceResiduals.block89[1]?=some panel1093.right from rfl))⟩
theorem valid1094 : ValidPanel panel1094 := ⟨modelCheck1094,residualCheck1094,
  ReferenceTrajectory.leftBlock64_subset (List.mem_of_getElem? (show ReferenceResiduals.block64[7]?=some panel1094.left from rfl)),
  ReferenceTrajectory.rightBlock89_subset (List.mem_of_getElem? (show ReferenceResiduals.block89[0]?=some panel1094.right from rfl))⟩
theorem valid1095 : ValidPanel panel1095 := ⟨modelCheck1095,residualCheck1095,
  ReferenceTrajectory.leftBlock64_subset (List.mem_of_getElem? (show ReferenceResiduals.block64[8]?=some panel1095.left from rfl)),
  ReferenceTrajectory.rightBlock88_subset (List.mem_of_getElem? (show ReferenceResiduals.block88[15]?=some panel1095.right from rfl))⟩
theorem valid1096 : ValidPanel panel1096 := ⟨modelCheck1096,residualCheck1096,
  ReferenceTrajectory.leftBlock64_subset (List.mem_of_getElem? (show ReferenceResiduals.block64[9]?=some panel1096.left from rfl)),
  ReferenceTrajectory.rightBlock88_subset (List.mem_of_getElem? (show ReferenceResiduals.block88[14]?=some panel1096.right from rfl))⟩
theorem valid1097 : ValidPanel panel1097 := ⟨modelCheck1097,residualCheck1097,
  ReferenceTrajectory.leftBlock64_subset (List.mem_of_getElem? (show ReferenceResiduals.block64[10]?=some panel1097.left from rfl)),
  ReferenceTrajectory.rightBlock88_subset (List.mem_of_getElem? (show ReferenceResiduals.block88[13]?=some panel1097.right from rfl))⟩
theorem valid1098 : ValidPanel panel1098 := ⟨modelCheck1098,residualCheck1098,
  ReferenceTrajectory.leftBlock64_subset (List.mem_of_getElem? (show ReferenceResiduals.block64[11]?=some panel1098.left from rfl)),
  ReferenceTrajectory.rightBlock88_subset (List.mem_of_getElem? (show ReferenceResiduals.block88[12]?=some panel1098.right from rfl))⟩
theorem valid1099 : ValidPanel panel1099 := ⟨modelCheck1099,residualCheck1099,
  ReferenceTrajectory.leftBlock64_subset (List.mem_of_getElem? (show ReferenceResiduals.block64[12]?=some panel1099.left from rfl)),
  ReferenceTrajectory.rightBlock88_subset (List.mem_of_getElem? (show ReferenceResiduals.block88[11]?=some panel1099.right from rfl))⟩
theorem valid1100 : ValidPanel panel1100 := ⟨modelCheck1100,residualCheck1100,
  ReferenceTrajectory.leftBlock64_subset (List.mem_of_getElem? (show ReferenceResiduals.block64[13]?=some panel1100.left from rfl)),
  ReferenceTrajectory.rightBlock88_subset (List.mem_of_getElem? (show ReferenceResiduals.block88[10]?=some panel1100.right from rfl))⟩
theorem valid1101 : ValidPanel panel1101 := ⟨modelCheck1101,residualCheck1101,
  ReferenceTrajectory.leftBlock64_subset (List.mem_of_getElem? (show ReferenceResiduals.block64[14]?=some panel1101.left from rfl)),
  ReferenceTrajectory.rightBlock88_subset (List.mem_of_getElem? (show ReferenceResiduals.block88[9]?=some panel1101.right from rfl))⟩
theorem valid1102 : ValidPanel panel1102 := ⟨modelCheck1102,residualCheck1102,
  ReferenceTrajectory.leftBlock64_subset (List.mem_of_getElem? (show ReferenceResiduals.block64[15]?=some panel1102.left from rfl)),
  ReferenceTrajectory.rightBlock88_subset (List.mem_of_getElem? (show ReferenceResiduals.block88[8]?=some panel1102.right from rfl))⟩
theorem valid1103 : ValidPanel panel1103 := ⟨modelCheck1103,residualCheck1103,
  ReferenceTrajectory.leftBlock65_subset (List.mem_of_getElem? (show ReferenceResiduals.block65[0]?=some panel1103.left from rfl)),
  ReferenceTrajectory.rightBlock88_subset (List.mem_of_getElem? (show ReferenceResiduals.block88[7]?=some panel1103.right from rfl))⟩
theorem valid1104 : ValidPanel panel1104 := ⟨modelCheck1104,residualCheck1104,
  ReferenceTrajectory.leftBlock65_subset (List.mem_of_getElem? (show ReferenceResiduals.block65[1]?=some panel1104.left from rfl)),
  ReferenceTrajectory.rightBlock88_subset (List.mem_of_getElem? (show ReferenceResiduals.block88[6]?=some panel1104.right from rfl))⟩
theorem valid1105 : ValidPanel panel1105 := ⟨modelCheck1105,residualCheck1105,
  ReferenceTrajectory.leftBlock65_subset (List.mem_of_getElem? (show ReferenceResiduals.block65[2]?=some panel1105.left from rfl)),
  ReferenceTrajectory.rightBlock88_subset (List.mem_of_getElem? (show ReferenceResiduals.block88[5]?=some panel1105.right from rfl))⟩
theorem valid1106 : ValidPanel panel1106 := ⟨modelCheck1106,residualCheck1106,
  ReferenceTrajectory.leftBlock65_subset (List.mem_of_getElem? (show ReferenceResiduals.block65[3]?=some panel1106.left from rfl)),
  ReferenceTrajectory.rightBlock88_subset (List.mem_of_getElem? (show ReferenceResiduals.block88[4]?=some panel1106.right from rfl))⟩
theorem valid1107 : ValidPanel panel1107 := ⟨modelCheck1107,residualCheck1107,
  ReferenceTrajectory.leftBlock65_subset (List.mem_of_getElem? (show ReferenceResiduals.block65[4]?=some panel1107.left from rfl)),
  ReferenceTrajectory.rightBlock88_subset (List.mem_of_getElem? (show ReferenceResiduals.block88[3]?=some panel1107.right from rfl))⟩
theorem valid1108 : ValidPanel panel1108 := ⟨modelCheck1108,residualCheck1108,
  ReferenceTrajectory.leftBlock65_subset (List.mem_of_getElem? (show ReferenceResiduals.block65[5]?=some panel1108.left from rfl)),
  ReferenceTrajectory.rightBlock88_subset (List.mem_of_getElem? (show ReferenceResiduals.block88[2]?=some panel1108.right from rfl))⟩
theorem valid1109 : ValidPanel panel1109 := ⟨modelCheck1109,residualCheck1109,
  ReferenceTrajectory.leftBlock65_subset (List.mem_of_getElem? (show ReferenceResiduals.block65[6]?=some panel1109.left from rfl)),
  ReferenceTrajectory.rightBlock88_subset (List.mem_of_getElem? (show ReferenceResiduals.block88[1]?=some panel1109.right from rfl))⟩
theorem valid1110 : ValidPanel panel1110 := ⟨modelCheck1110,residualCheck1110,
  ReferenceTrajectory.leftBlock65_subset (List.mem_of_getElem? (show ReferenceResiduals.block65[7]?=some panel1110.left from rfl)),
  ReferenceTrajectory.rightBlock88_subset (List.mem_of_getElem? (show ReferenceResiduals.block88[0]?=some panel1110.right from rfl))⟩
theorem valid1111 : ValidPanel panel1111 := ⟨modelCheck1111,residualCheck1111,
  ReferenceTrajectory.leftBlock65_subset (List.mem_of_getElem? (show ReferenceResiduals.block65[8]?=some panel1111.left from rfl)),
  ReferenceTrajectory.rightBlock87_subset (List.mem_of_getElem? (show ReferenceResiduals.block87[15]?=some panel1111.right from rfl))⟩
theorem valid1112 : ValidPanel panel1112 := ⟨modelCheck1112,residualCheck1112,
  ReferenceTrajectory.leftBlock65_subset (List.mem_of_getElem? (show ReferenceResiduals.block65[9]?=some panel1112.left from rfl)),
  ReferenceTrajectory.rightBlock87_subset (List.mem_of_getElem? (show ReferenceResiduals.block87[14]?=some panel1112.right from rfl))⟩
theorem valid1113 : ValidPanel panel1113 := ⟨modelCheck1113,residualCheck1113,
  ReferenceTrajectory.leftBlock65_subset (List.mem_of_getElem? (show ReferenceResiduals.block65[10]?=some panel1113.left from rfl)),
  ReferenceTrajectory.rightBlock87_subset (List.mem_of_getElem? (show ReferenceResiduals.block87[13]?=some panel1113.right from rfl))⟩
theorem valid1114 : ValidPanel panel1114 := ⟨modelCheck1114,residualCheck1114,
  ReferenceTrajectory.leftBlock65_subset (List.mem_of_getElem? (show ReferenceResiduals.block65[11]?=some panel1114.left from rfl)),
  ReferenceTrajectory.rightBlock87_subset (List.mem_of_getElem? (show ReferenceResiduals.block87[12]?=some panel1114.right from rfl))⟩
theorem valid1115 : ValidPanel panel1115 := ⟨modelCheck1115,residualCheck1115,
  ReferenceTrajectory.leftBlock65_subset (List.mem_of_getElem? (show ReferenceResiduals.block65[12]?=some panel1115.left from rfl)),
  ReferenceTrajectory.rightBlock87_subset (List.mem_of_getElem? (show ReferenceResiduals.block87[11]?=some panel1115.right from rfl))⟩
theorem valid1116 : ValidPanel panel1116 := ⟨modelCheck1116,residualCheck1116,
  ReferenceTrajectory.leftBlock65_subset (List.mem_of_getElem? (show ReferenceResiduals.block65[13]?=some panel1116.left from rfl)),
  ReferenceTrajectory.rightBlock87_subset (List.mem_of_getElem? (show ReferenceResiduals.block87[10]?=some panel1116.right from rfl))⟩
theorem valid1117 : ValidPanel panel1117 := ⟨modelCheck1117,residualCheck1117,
  ReferenceTrajectory.leftBlock65_subset (List.mem_of_getElem? (show ReferenceResiduals.block65[14]?=some panel1117.left from rfl)),
  ReferenceTrajectory.rightBlock87_subset (List.mem_of_getElem? (show ReferenceResiduals.block87[9]?=some panel1117.right from rfl))⟩
theorem valid1118 : ValidPanel panel1118 := ⟨modelCheck1118,residualCheck1118,
  ReferenceTrajectory.leftBlock65_subset (List.mem_of_getElem? (show ReferenceResiduals.block65[15]?=some panel1118.left from rfl)),
  ReferenceTrajectory.rightBlock87_subset (List.mem_of_getElem? (show ReferenceResiduals.block87[8]?=some panel1118.right from rfl))⟩
theorem valid1119 : ValidPanel panel1119 := ⟨modelCheck1119,residualCheck1119,
  ReferenceTrajectory.leftBlock66_subset (List.mem_of_getElem? (show ReferenceResiduals.block66[0]?=some panel1119.left from rfl)),
  ReferenceTrajectory.rightBlock87_subset (List.mem_of_getElem? (show ReferenceResiduals.block87[7]?=some panel1119.right from rfl))⟩
theorem validBlock34 : ∀ p∈block34,ValidPanel p := by
  simp only [block34,List.forall_mem_cons]
  exact ⟨valid1088,⟨valid1089,⟨valid1090,⟨valid1091,⟨valid1092,⟨valid1093,⟨valid1094,⟨valid1095,⟨valid1096,⟨valid1097,⟨valid1098,⟨valid1099,⟨valid1100,⟨valid1101,⟨valid1102,⟨valid1103,⟨valid1104,⟨valid1105,⟨valid1106,⟨valid1107,⟨valid1108,⟨valid1109,⟨valid1110,⟨valid1111,⟨valid1112,⟨valid1113,⟨valid1114,⟨valid1115,⟨valid1116,⟨valid1117,⟨valid1118,⟨valid1119,(by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end chebyshev2.Certificates.Compact.ContactValues

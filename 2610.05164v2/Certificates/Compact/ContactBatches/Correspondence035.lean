import «2610.05164v2».Certificates.Compact.ContactBatches.Batch035
import «2610.05164v2».Certificates.Compact.ContactCoverage
import «2610.05164v2».Certificates.Compact.ReferenceTrajectoryIndex

/-!
Article: 2610.05164v2, Section 4.1.
Correspondence035.
Use: `«2610.05164v2».Certificates.Compact.ContactValues.validBlock35` feeds
`«2610.05164v2».Certificates.Compact.ContactValues.all_valid` (all valid).
Proof chain: `«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement` —
2610.05164v2, Theorem 1.2, factor 1.000013; Unconditional uniform gain comparison with the retained
numerical factor.
-/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 0
set_option maxRecDepth 200000
namespace «2610.05164v2».Certificates.Compact.ContactValues
theorem valid1120 : ValidPanel panel1120 := ⟨modelCheck1120,residualCheck1120,
  ReferenceTrajectory.leftBlock66_subset (List.mem_of_getElem? (show ReferenceResiduals.block66[1]?=some panel1120.left from rfl)),
  ReferenceTrajectory.rightBlock87_subset (List.mem_of_getElem? (show ReferenceResiduals.block87[6]?=some panel1120.right from rfl))⟩
theorem valid1121 : ValidPanel panel1121 := ⟨modelCheck1121,residualCheck1121,
  ReferenceTrajectory.leftBlock66_subset (List.mem_of_getElem? (show ReferenceResiduals.block66[2]?=some panel1121.left from rfl)),
  ReferenceTrajectory.rightBlock87_subset (List.mem_of_getElem? (show ReferenceResiduals.block87[5]?=some panel1121.right from rfl))⟩
theorem valid1122 : ValidPanel panel1122 := ⟨modelCheck1122,residualCheck1122,
  ReferenceTrajectory.leftBlock66_subset (List.mem_of_getElem? (show ReferenceResiduals.block66[3]?=some panel1122.left from rfl)),
  ReferenceTrajectory.rightBlock87_subset (List.mem_of_getElem? (show ReferenceResiduals.block87[4]?=some panel1122.right from rfl))⟩
theorem valid1123 : ValidPanel panel1123 := ⟨modelCheck1123,residualCheck1123,
  ReferenceTrajectory.leftBlock66_subset (List.mem_of_getElem? (show ReferenceResiduals.block66[4]?=some panel1123.left from rfl)),
  ReferenceTrajectory.rightBlock87_subset (List.mem_of_getElem? (show ReferenceResiduals.block87[3]?=some panel1123.right from rfl))⟩
theorem valid1124 : ValidPanel panel1124 := ⟨modelCheck1124,residualCheck1124,
  ReferenceTrajectory.leftBlock66_subset (List.mem_of_getElem? (show ReferenceResiduals.block66[5]?=some panel1124.left from rfl)),
  ReferenceTrajectory.rightBlock87_subset (List.mem_of_getElem? (show ReferenceResiduals.block87[2]?=some panel1124.right from rfl))⟩
theorem valid1125 : ValidPanel panel1125 := ⟨modelCheck1125,residualCheck1125,
  ReferenceTrajectory.leftBlock66_subset (List.mem_of_getElem? (show ReferenceResiduals.block66[6]?=some panel1125.left from rfl)),
  ReferenceTrajectory.rightBlock87_subset (List.mem_of_getElem? (show ReferenceResiduals.block87[1]?=some panel1125.right from rfl))⟩
theorem valid1126 : ValidPanel panel1126 := ⟨modelCheck1126,residualCheck1126,
  ReferenceTrajectory.leftBlock66_subset (List.mem_of_getElem? (show ReferenceResiduals.block66[7]?=some panel1126.left from rfl)),
  ReferenceTrajectory.rightBlock87_subset (List.mem_of_getElem? (show ReferenceResiduals.block87[0]?=some panel1126.right from rfl))⟩
theorem valid1127 : ValidPanel panel1127 := ⟨modelCheck1127,residualCheck1127,
  ReferenceTrajectory.leftBlock66_subset (List.mem_of_getElem? (show ReferenceResiduals.block66[8]?=some panel1127.left from rfl)),
  ReferenceTrajectory.rightBlock86_subset (List.mem_of_getElem? (show ReferenceResiduals.block86[15]?=some panel1127.right from rfl))⟩
theorem valid1128 : ValidPanel panel1128 := ⟨modelCheck1128,residualCheck1128,
  ReferenceTrajectory.leftBlock66_subset (List.mem_of_getElem? (show ReferenceResiduals.block66[9]?=some panel1128.left from rfl)),
  ReferenceTrajectory.rightBlock86_subset (List.mem_of_getElem? (show ReferenceResiduals.block86[14]?=some panel1128.right from rfl))⟩
theorem valid1129 : ValidPanel panel1129 := ⟨modelCheck1129,residualCheck1129,
  ReferenceTrajectory.leftBlock66_subset (List.mem_of_getElem? (show ReferenceResiduals.block66[10]?=some panel1129.left from rfl)),
  ReferenceTrajectory.rightBlock86_subset (List.mem_of_getElem? (show ReferenceResiduals.block86[13]?=some panel1129.right from rfl))⟩
theorem valid1130 : ValidPanel panel1130 := ⟨modelCheck1130,residualCheck1130,
  ReferenceTrajectory.leftBlock66_subset (List.mem_of_getElem? (show ReferenceResiduals.block66[11]?=some panel1130.left from rfl)),
  ReferenceTrajectory.rightBlock86_subset (List.mem_of_getElem? (show ReferenceResiduals.block86[12]?=some panel1130.right from rfl))⟩
theorem valid1131 : ValidPanel panel1131 := ⟨modelCheck1131,residualCheck1131,
  ReferenceTrajectory.leftBlock66_subset (List.mem_of_getElem? (show ReferenceResiduals.block66[12]?=some panel1131.left from rfl)),
  ReferenceTrajectory.rightBlock86_subset (List.mem_of_getElem? (show ReferenceResiduals.block86[11]?=some panel1131.right from rfl))⟩
theorem valid1132 : ValidPanel panel1132 := ⟨modelCheck1132,residualCheck1132,
  ReferenceTrajectory.leftBlock66_subset (List.mem_of_getElem? (show ReferenceResiduals.block66[13]?=some panel1132.left from rfl)),
  ReferenceTrajectory.rightBlock86_subset (List.mem_of_getElem? (show ReferenceResiduals.block86[10]?=some panel1132.right from rfl))⟩
theorem valid1133 : ValidPanel panel1133 := ⟨modelCheck1133,residualCheck1133,
  ReferenceTrajectory.leftBlock66_subset (List.mem_of_getElem? (show ReferenceResiduals.block66[14]?=some panel1133.left from rfl)),
  ReferenceTrajectory.rightBlock86_subset (List.mem_of_getElem? (show ReferenceResiduals.block86[9]?=some panel1133.right from rfl))⟩
theorem valid1134 : ValidPanel panel1134 := ⟨modelCheck1134,residualCheck1134,
  ReferenceTrajectory.leftBlock66_subset (List.mem_of_getElem? (show ReferenceResiduals.block66[15]?=some panel1134.left from rfl)),
  ReferenceTrajectory.rightBlock86_subset (List.mem_of_getElem? (show ReferenceResiduals.block86[8]?=some panel1134.right from rfl))⟩
theorem valid1135 : ValidPanel panel1135 := ⟨modelCheck1135,residualCheck1135,
  ReferenceTrajectory.leftBlock67_subset (List.mem_of_getElem? (show ReferenceResiduals.block67[0]?=some panel1135.left from rfl)),
  ReferenceTrajectory.rightBlock86_subset (List.mem_of_getElem? (show ReferenceResiduals.block86[7]?=some panel1135.right from rfl))⟩
theorem valid1136 : ValidPanel panel1136 := ⟨modelCheck1136,residualCheck1136,
  ReferenceTrajectory.leftBlock67_subset (List.mem_of_getElem? (show ReferenceResiduals.block67[1]?=some panel1136.left from rfl)),
  ReferenceTrajectory.rightBlock86_subset (List.mem_of_getElem? (show ReferenceResiduals.block86[6]?=some panel1136.right from rfl))⟩
theorem valid1137 : ValidPanel panel1137 := ⟨modelCheck1137,residualCheck1137,
  ReferenceTrajectory.leftBlock67_subset (List.mem_of_getElem? (show ReferenceResiduals.block67[2]?=some panel1137.left from rfl)),
  ReferenceTrajectory.rightBlock86_subset (List.mem_of_getElem? (show ReferenceResiduals.block86[5]?=some panel1137.right from rfl))⟩
theorem valid1138 : ValidPanel panel1138 := ⟨modelCheck1138,residualCheck1138,
  ReferenceTrajectory.leftBlock67_subset (List.mem_of_getElem? (show ReferenceResiduals.block67[3]?=some panel1138.left from rfl)),
  ReferenceTrajectory.rightBlock86_subset (List.mem_of_getElem? (show ReferenceResiduals.block86[4]?=some panel1138.right from rfl))⟩
theorem valid1139 : ValidPanel panel1139 := ⟨modelCheck1139,residualCheck1139,
  ReferenceTrajectory.leftBlock67_subset (List.mem_of_getElem? (show ReferenceResiduals.block67[4]?=some panel1139.left from rfl)),
  ReferenceTrajectory.rightBlock86_subset (List.mem_of_getElem? (show ReferenceResiduals.block86[3]?=some panel1139.right from rfl))⟩
theorem valid1140 : ValidPanel panel1140 := ⟨modelCheck1140,residualCheck1140,
  ReferenceTrajectory.leftBlock67_subset (List.mem_of_getElem? (show ReferenceResiduals.block67[5]?=some panel1140.left from rfl)),
  ReferenceTrajectory.rightBlock86_subset (List.mem_of_getElem? (show ReferenceResiduals.block86[2]?=some panel1140.right from rfl))⟩
theorem valid1141 : ValidPanel panel1141 := ⟨modelCheck1141,residualCheck1141,
  ReferenceTrajectory.leftBlock67_subset (List.mem_of_getElem? (show ReferenceResiduals.block67[6]?=some panel1141.left from rfl)),
  ReferenceTrajectory.rightBlock86_subset (List.mem_of_getElem? (show ReferenceResiduals.block86[1]?=some panel1141.right from rfl))⟩
theorem valid1142 : ValidPanel panel1142 := ⟨modelCheck1142,residualCheck1142,
  ReferenceTrajectory.leftBlock67_subset (List.mem_of_getElem? (show ReferenceResiduals.block67[7]?=some panel1142.left from rfl)),
  ReferenceTrajectory.rightBlock86_subset (List.mem_of_getElem? (show ReferenceResiduals.block86[0]?=some panel1142.right from rfl))⟩
theorem valid1143 : ValidPanel panel1143 := ⟨modelCheck1143,residualCheck1143,
  ReferenceTrajectory.leftBlock67_subset (List.mem_of_getElem? (show ReferenceResiduals.block67[8]?=some panel1143.left from rfl)),
  ReferenceTrajectory.rightBlock85_subset (List.mem_of_getElem? (show ReferenceResiduals.block85[15]?=some panel1143.right from rfl))⟩
theorem valid1144 : ValidPanel panel1144 := ⟨modelCheck1144,residualCheck1144,
  ReferenceTrajectory.leftBlock67_subset (List.mem_of_getElem? (show ReferenceResiduals.block67[9]?=some panel1144.left from rfl)),
  ReferenceTrajectory.rightBlock85_subset (List.mem_of_getElem? (show ReferenceResiduals.block85[14]?=some panel1144.right from rfl))⟩
theorem valid1145 : ValidPanel panel1145 := ⟨modelCheck1145,residualCheck1145,
  ReferenceTrajectory.leftBlock67_subset (List.mem_of_getElem? (show ReferenceResiduals.block67[10]?=some panel1145.left from rfl)),
  ReferenceTrajectory.rightBlock85_subset (List.mem_of_getElem? (show ReferenceResiduals.block85[13]?=some panel1145.right from rfl))⟩
theorem valid1146 : ValidPanel panel1146 := ⟨modelCheck1146,residualCheck1146,
  ReferenceTrajectory.leftBlock67_subset (List.mem_of_getElem? (show ReferenceResiduals.block67[11]?=some panel1146.left from rfl)),
  ReferenceTrajectory.rightBlock85_subset (List.mem_of_getElem? (show ReferenceResiduals.block85[12]?=some panel1146.right from rfl))⟩
theorem valid1147 : ValidPanel panel1147 := ⟨modelCheck1147,residualCheck1147,
  ReferenceTrajectory.leftBlock67_subset (List.mem_of_getElem? (show ReferenceResiduals.block67[12]?=some panel1147.left from rfl)),
  ReferenceTrajectory.rightBlock85_subset (List.mem_of_getElem? (show ReferenceResiduals.block85[11]?=some panel1147.right from rfl))⟩
theorem valid1148 : ValidPanel panel1148 := ⟨modelCheck1148,residualCheck1148,
  ReferenceTrajectory.leftBlock67_subset (List.mem_of_getElem? (show ReferenceResiduals.block67[13]?=some panel1148.left from rfl)),
  ReferenceTrajectory.rightBlock85_subset (List.mem_of_getElem? (show ReferenceResiduals.block85[10]?=some panel1148.right from rfl))⟩
theorem valid1149 : ValidPanel panel1149 := ⟨modelCheck1149,residualCheck1149,
  ReferenceTrajectory.leftBlock67_subset (List.mem_of_getElem? (show ReferenceResiduals.block67[14]?=some panel1149.left from rfl)),
  ReferenceTrajectory.rightBlock85_subset (List.mem_of_getElem? (show ReferenceResiduals.block85[9]?=some panel1149.right from rfl))⟩
theorem valid1150 : ValidPanel panel1150 := ⟨modelCheck1150,residualCheck1150,
  ReferenceTrajectory.leftBlock67_subset (List.mem_of_getElem? (show ReferenceResiduals.block67[15]?=some panel1150.left from rfl)),
  ReferenceTrajectory.rightBlock85_subset (List.mem_of_getElem? (show ReferenceResiduals.block85[8]?=some panel1150.right from rfl))⟩
theorem valid1151 : ValidPanel panel1151 := ⟨modelCheck1151,residualCheck1151,
  ReferenceTrajectory.leftBlock68_subset (List.mem_of_getElem? (show ReferenceResiduals.block68[0]?=some panel1151.left from rfl)),
  ReferenceTrajectory.rightBlock85_subset (List.mem_of_getElem? (show ReferenceResiduals.block85[7]?=some panel1151.right from rfl))⟩
theorem validBlock35 : ∀ p∈block35,ValidPanel p := by
  simp only [block35,List.forall_mem_cons]
  exact ⟨valid1120,⟨valid1121,⟨valid1122,⟨valid1123,⟨valid1124,⟨valid1125,⟨valid1126,⟨valid1127,⟨valid1128,⟨valid1129,⟨valid1130,⟨valid1131,⟨valid1132,⟨valid1133,⟨valid1134,⟨valid1135,⟨valid1136,⟨valid1137,⟨valid1138,⟨valid1139,⟨valid1140,⟨valid1141,⟨valid1142,⟨valid1143,⟨valid1144,⟨valid1145,⟨valid1146,⟨valid1147,⟨valid1148,⟨valid1149,⟨valid1150,⟨valid1151,(by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end «2610.05164v2».Certificates.Compact.ContactValues

import chebyshev2.Certificates.Compact.ContactBatches.Batch037
import chebyshev2.Certificates.Compact.ContactCoverage
import chebyshev2.Certificates.Compact.ReferenceTrajectoryIndex

/-!
Article: chebyshev2, Section 4.1.
Correspondence037.
Use: `chebyshev2.Certificates.Compact.ContactValues.validBlock37` feeds
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
theorem valid1184 : ValidPanel panel1184 := ⟨modelCheck1184,residualCheck1184,
  ReferenceTrajectory.leftBlock70_subset (List.mem_of_getElem? (show ReferenceResiduals.block70[1]?=some panel1184.left from rfl)),
  ReferenceTrajectory.rightBlock83_subset (List.mem_of_getElem? (show ReferenceResiduals.block83[6]?=some panel1184.right from rfl))⟩
theorem valid1185 : ValidPanel panel1185 := ⟨modelCheck1185,residualCheck1185,
  ReferenceTrajectory.leftBlock70_subset (List.mem_of_getElem? (show ReferenceResiduals.block70[2]?=some panel1185.left from rfl)),
  ReferenceTrajectory.rightBlock83_subset (List.mem_of_getElem? (show ReferenceResiduals.block83[5]?=some panel1185.right from rfl))⟩
theorem valid1186 : ValidPanel panel1186 := ⟨modelCheck1186,residualCheck1186,
  ReferenceTrajectory.leftBlock70_subset (List.mem_of_getElem? (show ReferenceResiduals.block70[3]?=some panel1186.left from rfl)),
  ReferenceTrajectory.rightBlock83_subset (List.mem_of_getElem? (show ReferenceResiduals.block83[4]?=some panel1186.right from rfl))⟩
theorem valid1187 : ValidPanel panel1187 := ⟨modelCheck1187,residualCheck1187,
  ReferenceTrajectory.leftBlock70_subset (List.mem_of_getElem? (show ReferenceResiduals.block70[4]?=some panel1187.left from rfl)),
  ReferenceTrajectory.rightBlock83_subset (List.mem_of_getElem? (show ReferenceResiduals.block83[3]?=some panel1187.right from rfl))⟩
theorem valid1188 : ValidPanel panel1188 := ⟨modelCheck1188,residualCheck1188,
  ReferenceTrajectory.leftBlock70_subset (List.mem_of_getElem? (show ReferenceResiduals.block70[5]?=some panel1188.left from rfl)),
  ReferenceTrajectory.rightBlock83_subset (List.mem_of_getElem? (show ReferenceResiduals.block83[2]?=some panel1188.right from rfl))⟩
theorem valid1189 : ValidPanel panel1189 := ⟨modelCheck1189,residualCheck1189,
  ReferenceTrajectory.leftBlock70_subset (List.mem_of_getElem? (show ReferenceResiduals.block70[6]?=some panel1189.left from rfl)),
  ReferenceTrajectory.rightBlock83_subset (List.mem_of_getElem? (show ReferenceResiduals.block83[1]?=some panel1189.right from rfl))⟩
theorem valid1190 : ValidPanel panel1190 := ⟨modelCheck1190,residualCheck1190,
  ReferenceTrajectory.leftBlock70_subset (List.mem_of_getElem? (show ReferenceResiduals.block70[7]?=some panel1190.left from rfl)),
  ReferenceTrajectory.rightBlock83_subset (List.mem_of_getElem? (show ReferenceResiduals.block83[0]?=some panel1190.right from rfl))⟩
theorem valid1191 : ValidPanel panel1191 := ⟨modelCheck1191,residualCheck1191,
  ReferenceTrajectory.leftBlock70_subset (List.mem_of_getElem? (show ReferenceResiduals.block70[8]?=some panel1191.left from rfl)),
  ReferenceTrajectory.rightBlock82_subset (List.mem_of_getElem? (show ReferenceResiduals.block82[15]?=some panel1191.right from rfl))⟩
theorem valid1192 : ValidPanel panel1192 := ⟨modelCheck1192,residualCheck1192,
  ReferenceTrajectory.leftBlock70_subset (List.mem_of_getElem? (show ReferenceResiduals.block70[9]?=some panel1192.left from rfl)),
  ReferenceTrajectory.rightBlock82_subset (List.mem_of_getElem? (show ReferenceResiduals.block82[14]?=some panel1192.right from rfl))⟩
theorem valid1193 : ValidPanel panel1193 := ⟨modelCheck1193,residualCheck1193,
  ReferenceTrajectory.leftBlock70_subset (List.mem_of_getElem? (show ReferenceResiduals.block70[10]?=some panel1193.left from rfl)),
  ReferenceTrajectory.rightBlock82_subset (List.mem_of_getElem? (show ReferenceResiduals.block82[13]?=some panel1193.right from rfl))⟩
theorem valid1194 : ValidPanel panel1194 := ⟨modelCheck1194,residualCheck1194,
  ReferenceTrajectory.leftBlock70_subset (List.mem_of_getElem? (show ReferenceResiduals.block70[11]?=some panel1194.left from rfl)),
  ReferenceTrajectory.rightBlock82_subset (List.mem_of_getElem? (show ReferenceResiduals.block82[12]?=some panel1194.right from rfl))⟩
theorem valid1195 : ValidPanel panel1195 := ⟨modelCheck1195,residualCheck1195,
  ReferenceTrajectory.leftBlock70_subset (List.mem_of_getElem? (show ReferenceResiduals.block70[12]?=some panel1195.left from rfl)),
  ReferenceTrajectory.rightBlock82_subset (List.mem_of_getElem? (show ReferenceResiduals.block82[11]?=some panel1195.right from rfl))⟩
theorem valid1196 : ValidPanel panel1196 := ⟨modelCheck1196,residualCheck1196,
  ReferenceTrajectory.leftBlock70_subset (List.mem_of_getElem? (show ReferenceResiduals.block70[13]?=some panel1196.left from rfl)),
  ReferenceTrajectory.rightBlock82_subset (List.mem_of_getElem? (show ReferenceResiduals.block82[10]?=some panel1196.right from rfl))⟩
theorem valid1197 : ValidPanel panel1197 := ⟨modelCheck1197,residualCheck1197,
  ReferenceTrajectory.leftBlock70_subset (List.mem_of_getElem? (show ReferenceResiduals.block70[14]?=some panel1197.left from rfl)),
  ReferenceTrajectory.rightBlock82_subset (List.mem_of_getElem? (show ReferenceResiduals.block82[9]?=some panel1197.right from rfl))⟩
theorem valid1198 : ValidPanel panel1198 := ⟨modelCheck1198,residualCheck1198,
  ReferenceTrajectory.leftBlock70_subset (List.mem_of_getElem? (show ReferenceResiduals.block70[15]?=some panel1198.left from rfl)),
  ReferenceTrajectory.rightBlock82_subset (List.mem_of_getElem? (show ReferenceResiduals.block82[8]?=some panel1198.right from rfl))⟩
theorem valid1199 : ValidPanel panel1199 := ⟨modelCheck1199,residualCheck1199,
  ReferenceTrajectory.leftBlock71_subset (List.mem_of_getElem? (show ReferenceResiduals.block71[0]?=some panel1199.left from rfl)),
  ReferenceTrajectory.rightBlock82_subset (List.mem_of_getElem? (show ReferenceResiduals.block82[7]?=some panel1199.right from rfl))⟩
theorem valid1200 : ValidPanel panel1200 := ⟨modelCheck1200,residualCheck1200,
  ReferenceTrajectory.leftBlock71_subset (List.mem_of_getElem? (show ReferenceResiduals.block71[1]?=some panel1200.left from rfl)),
  ReferenceTrajectory.rightBlock82_subset (List.mem_of_getElem? (show ReferenceResiduals.block82[6]?=some panel1200.right from rfl))⟩
theorem valid1201 : ValidPanel panel1201 := ⟨modelCheck1201,residualCheck1201,
  ReferenceTrajectory.leftBlock71_subset (List.mem_of_getElem? (show ReferenceResiduals.block71[2]?=some panel1201.left from rfl)),
  ReferenceTrajectory.rightBlock82_subset (List.mem_of_getElem? (show ReferenceResiduals.block82[5]?=some panel1201.right from rfl))⟩
theorem valid1202 : ValidPanel panel1202 := ⟨modelCheck1202,residualCheck1202,
  ReferenceTrajectory.leftBlock71_subset (List.mem_of_getElem? (show ReferenceResiduals.block71[3]?=some panel1202.left from rfl)),
  ReferenceTrajectory.rightBlock82_subset (List.mem_of_getElem? (show ReferenceResiduals.block82[4]?=some panel1202.right from rfl))⟩
theorem valid1203 : ValidPanel panel1203 := ⟨modelCheck1203,residualCheck1203,
  ReferenceTrajectory.leftBlock71_subset (List.mem_of_getElem? (show ReferenceResiduals.block71[4]?=some panel1203.left from rfl)),
  ReferenceTrajectory.rightBlock82_subset (List.mem_of_getElem? (show ReferenceResiduals.block82[3]?=some panel1203.right from rfl))⟩
theorem valid1204 : ValidPanel panel1204 := ⟨modelCheck1204,residualCheck1204,
  ReferenceTrajectory.leftBlock71_subset (List.mem_of_getElem? (show ReferenceResiduals.block71[5]?=some panel1204.left from rfl)),
  ReferenceTrajectory.rightBlock82_subset (List.mem_of_getElem? (show ReferenceResiduals.block82[2]?=some panel1204.right from rfl))⟩
theorem valid1205 : ValidPanel panel1205 := ⟨modelCheck1205,residualCheck1205,
  ReferenceTrajectory.leftBlock71_subset (List.mem_of_getElem? (show ReferenceResiduals.block71[6]?=some panel1205.left from rfl)),
  ReferenceTrajectory.rightBlock82_subset (List.mem_of_getElem? (show ReferenceResiduals.block82[1]?=some panel1205.right from rfl))⟩
theorem valid1206 : ValidPanel panel1206 := ⟨modelCheck1206,residualCheck1206,
  ReferenceTrajectory.leftBlock71_subset (List.mem_of_getElem? (show ReferenceResiduals.block71[7]?=some panel1206.left from rfl)),
  ReferenceTrajectory.rightBlock82_subset (List.mem_of_getElem? (show ReferenceResiduals.block82[0]?=some panel1206.right from rfl))⟩
theorem valid1207 : ValidPanel panel1207 := ⟨modelCheck1207,residualCheck1207,
  ReferenceTrajectory.leftBlock71_subset (List.mem_of_getElem? (show ReferenceResiduals.block71[8]?=some panel1207.left from rfl)),
  ReferenceTrajectory.rightBlock81_subset (List.mem_of_getElem? (show ReferenceResiduals.block81[15]?=some panel1207.right from rfl))⟩
theorem valid1208 : ValidPanel panel1208 := ⟨modelCheck1208,residualCheck1208,
  ReferenceTrajectory.leftBlock71_subset (List.mem_of_getElem? (show ReferenceResiduals.block71[9]?=some panel1208.left from rfl)),
  ReferenceTrajectory.rightBlock81_subset (List.mem_of_getElem? (show ReferenceResiduals.block81[14]?=some panel1208.right from rfl))⟩
theorem valid1209 : ValidPanel panel1209 := ⟨modelCheck1209,residualCheck1209,
  ReferenceTrajectory.leftBlock71_subset (List.mem_of_getElem? (show ReferenceResiduals.block71[10]?=some panel1209.left from rfl)),
  ReferenceTrajectory.rightBlock81_subset (List.mem_of_getElem? (show ReferenceResiduals.block81[13]?=some panel1209.right from rfl))⟩
theorem valid1210 : ValidPanel panel1210 := ⟨modelCheck1210,residualCheck1210,
  ReferenceTrajectory.leftBlock71_subset (List.mem_of_getElem? (show ReferenceResiduals.block71[11]?=some panel1210.left from rfl)),
  ReferenceTrajectory.rightBlock81_subset (List.mem_of_getElem? (show ReferenceResiduals.block81[12]?=some panel1210.right from rfl))⟩
theorem valid1211 : ValidPanel panel1211 := ⟨modelCheck1211,residualCheck1211,
  ReferenceTrajectory.leftBlock71_subset (List.mem_of_getElem? (show ReferenceResiduals.block71[12]?=some panel1211.left from rfl)),
  ReferenceTrajectory.rightBlock81_subset (List.mem_of_getElem? (show ReferenceResiduals.block81[11]?=some panel1211.right from rfl))⟩
theorem valid1212 : ValidPanel panel1212 := ⟨modelCheck1212,residualCheck1212,
  ReferenceTrajectory.leftBlock71_subset (List.mem_of_getElem? (show ReferenceResiduals.block71[13]?=some panel1212.left from rfl)),
  ReferenceTrajectory.rightBlock81_subset (List.mem_of_getElem? (show ReferenceResiduals.block81[10]?=some panel1212.right from rfl))⟩
theorem valid1213 : ValidPanel panel1213 := ⟨modelCheck1213,residualCheck1213,
  ReferenceTrajectory.leftBlock71_subset (List.mem_of_getElem? (show ReferenceResiduals.block71[14]?=some panel1213.left from rfl)),
  ReferenceTrajectory.rightBlock81_subset (List.mem_of_getElem? (show ReferenceResiduals.block81[9]?=some panel1213.right from rfl))⟩
theorem valid1214 : ValidPanel panel1214 := ⟨modelCheck1214,residualCheck1214,
  ReferenceTrajectory.leftBlock71_subset (List.mem_of_getElem? (show ReferenceResiduals.block71[15]?=some panel1214.left from rfl)),
  ReferenceTrajectory.rightBlock81_subset (List.mem_of_getElem? (show ReferenceResiduals.block81[8]?=some panel1214.right from rfl))⟩
theorem valid1215 : ValidPanel panel1215 := ⟨modelCheck1215,residualCheck1215,
  ReferenceTrajectory.leftBlock72_subset (List.mem_of_getElem? (show ReferenceResiduals.block72[0]?=some panel1215.left from rfl)),
  ReferenceTrajectory.rightBlock81_subset (List.mem_of_getElem? (show ReferenceResiduals.block81[7]?=some panel1215.right from rfl))⟩
theorem validBlock37 : ∀ p∈block37,ValidPanel p := by
  simp only [block37,List.forall_mem_cons]
  exact ⟨valid1184,⟨valid1185,⟨valid1186,⟨valid1187,⟨valid1188,⟨valid1189,⟨valid1190,⟨valid1191,⟨valid1192,⟨valid1193,⟨valid1194,⟨valid1195,⟨valid1196,⟨valid1197,⟨valid1198,⟨valid1199,⟨valid1200,⟨valid1201,⟨valid1202,⟨valid1203,⟨valid1204,⟨valid1205,⟨valid1206,⟨valid1207,⟨valid1208,⟨valid1209,⟨valid1210,⟨valid1211,⟨valid1212,⟨valid1213,⟨valid1214,⟨valid1215,(by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end chebyshev2.Certificates.Compact.ContactValues

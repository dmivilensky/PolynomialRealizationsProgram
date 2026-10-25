import chebyshev2.Certificates.Compact.ContactBatches.Batch038
import chebyshev2.Certificates.Compact.ContactCoverage
import chebyshev2.Certificates.Compact.ReferenceTrajectoryIndex

/-!
Article: chebyshev2, Section 4.1.
Correspondence038.
Use: `chebyshev2.Certificates.Compact.ContactValues.validBlock38` feeds
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
theorem valid1216 : ValidPanel panel1216 := ⟨modelCheck1216,residualCheck1216,
  ReferenceTrajectory.leftBlock72_subset (List.mem_of_getElem? (show ReferenceResiduals.block72[1]?=some panel1216.left from rfl)),
  ReferenceTrajectory.rightBlock81_subset (List.mem_of_getElem? (show ReferenceResiduals.block81[6]?=some panel1216.right from rfl))⟩
theorem valid1217 : ValidPanel panel1217 := ⟨modelCheck1217,residualCheck1217,
  ReferenceTrajectory.leftBlock72_subset (List.mem_of_getElem? (show ReferenceResiduals.block72[2]?=some panel1217.left from rfl)),
  ReferenceTrajectory.rightBlock81_subset (List.mem_of_getElem? (show ReferenceResiduals.block81[5]?=some panel1217.right from rfl))⟩
theorem valid1218 : ValidPanel panel1218 := ⟨modelCheck1218,residualCheck1218,
  ReferenceTrajectory.leftBlock72_subset (List.mem_of_getElem? (show ReferenceResiduals.block72[3]?=some panel1218.left from rfl)),
  ReferenceTrajectory.rightBlock81_subset (List.mem_of_getElem? (show ReferenceResiduals.block81[4]?=some panel1218.right from rfl))⟩
theorem valid1219 : ValidPanel panel1219 := ⟨modelCheck1219,residualCheck1219,
  ReferenceTrajectory.leftBlock72_subset (List.mem_of_getElem? (show ReferenceResiduals.block72[4]?=some panel1219.left from rfl)),
  ReferenceTrajectory.rightBlock81_subset (List.mem_of_getElem? (show ReferenceResiduals.block81[3]?=some panel1219.right from rfl))⟩
theorem valid1220 : ValidPanel panel1220 := ⟨modelCheck1220,residualCheck1220,
  ReferenceTrajectory.leftBlock72_subset (List.mem_of_getElem? (show ReferenceResiduals.block72[5]?=some panel1220.left from rfl)),
  ReferenceTrajectory.rightBlock81_subset (List.mem_of_getElem? (show ReferenceResiduals.block81[2]?=some panel1220.right from rfl))⟩
theorem valid1221 : ValidPanel panel1221 := ⟨modelCheck1221,residualCheck1221,
  ReferenceTrajectory.leftBlock72_subset (List.mem_of_getElem? (show ReferenceResiduals.block72[6]?=some panel1221.left from rfl)),
  ReferenceTrajectory.rightBlock81_subset (List.mem_of_getElem? (show ReferenceResiduals.block81[1]?=some panel1221.right from rfl))⟩
theorem valid1222 : ValidPanel panel1222 := ⟨modelCheck1222,residualCheck1222,
  ReferenceTrajectory.leftBlock72_subset (List.mem_of_getElem? (show ReferenceResiduals.block72[7]?=some panel1222.left from rfl)),
  ReferenceTrajectory.rightBlock81_subset (List.mem_of_getElem? (show ReferenceResiduals.block81[0]?=some panel1222.right from rfl))⟩
theorem valid1223 : ValidPanel panel1223 := ⟨modelCheck1223,residualCheck1223,
  ReferenceTrajectory.leftBlock72_subset (List.mem_of_getElem? (show ReferenceResiduals.block72[8]?=some panel1223.left from rfl)),
  ReferenceTrajectory.rightBlock80_subset (List.mem_of_getElem? (show ReferenceResiduals.block80[15]?=some panel1223.right from rfl))⟩
theorem valid1224 : ValidPanel panel1224 := ⟨modelCheck1224,residualCheck1224,
  ReferenceTrajectory.leftBlock72_subset (List.mem_of_getElem? (show ReferenceResiduals.block72[9]?=some panel1224.left from rfl)),
  ReferenceTrajectory.rightBlock80_subset (List.mem_of_getElem? (show ReferenceResiduals.block80[14]?=some panel1224.right from rfl))⟩
theorem valid1225 : ValidPanel panel1225 := ⟨modelCheck1225,residualCheck1225,
  ReferenceTrajectory.leftBlock72_subset (List.mem_of_getElem? (show ReferenceResiduals.block72[10]?=some panel1225.left from rfl)),
  ReferenceTrajectory.rightBlock80_subset (List.mem_of_getElem? (show ReferenceResiduals.block80[13]?=some panel1225.right from rfl))⟩
theorem valid1226 : ValidPanel panel1226 := ⟨modelCheck1226,residualCheck1226,
  ReferenceTrajectory.leftBlock72_subset (List.mem_of_getElem? (show ReferenceResiduals.block72[11]?=some panel1226.left from rfl)),
  ReferenceTrajectory.rightBlock80_subset (List.mem_of_getElem? (show ReferenceResiduals.block80[12]?=some panel1226.right from rfl))⟩
theorem valid1227 : ValidPanel panel1227 := ⟨modelCheck1227,residualCheck1227,
  ReferenceTrajectory.leftBlock72_subset (List.mem_of_getElem? (show ReferenceResiduals.block72[12]?=some panel1227.left from rfl)),
  ReferenceTrajectory.rightBlock80_subset (List.mem_of_getElem? (show ReferenceResiduals.block80[11]?=some panel1227.right from rfl))⟩
theorem valid1228 : ValidPanel panel1228 := ⟨modelCheck1228,residualCheck1228,
  ReferenceTrajectory.leftBlock72_subset (List.mem_of_getElem? (show ReferenceResiduals.block72[13]?=some panel1228.left from rfl)),
  ReferenceTrajectory.rightBlock80_subset (List.mem_of_getElem? (show ReferenceResiduals.block80[10]?=some panel1228.right from rfl))⟩
theorem valid1229 : ValidPanel panel1229 := ⟨modelCheck1229,residualCheck1229,
  ReferenceTrajectory.leftBlock72_subset (List.mem_of_getElem? (show ReferenceResiduals.block72[14]?=some panel1229.left from rfl)),
  ReferenceTrajectory.rightBlock80_subset (List.mem_of_getElem? (show ReferenceResiduals.block80[9]?=some panel1229.right from rfl))⟩
theorem valid1230 : ValidPanel panel1230 := ⟨modelCheck1230,residualCheck1230,
  ReferenceTrajectory.leftBlock72_subset (List.mem_of_getElem? (show ReferenceResiduals.block72[15]?=some panel1230.left from rfl)),
  ReferenceTrajectory.rightBlock80_subset (List.mem_of_getElem? (show ReferenceResiduals.block80[8]?=some panel1230.right from rfl))⟩
theorem valid1231 : ValidPanel panel1231 := ⟨modelCheck1231,residualCheck1231,
  ReferenceTrajectory.leftBlock73_subset (List.mem_of_getElem? (show ReferenceResiduals.block73[0]?=some panel1231.left from rfl)),
  ReferenceTrajectory.rightBlock80_subset (List.mem_of_getElem? (show ReferenceResiduals.block80[7]?=some panel1231.right from rfl))⟩
theorem valid1232 : ValidPanel panel1232 := ⟨modelCheck1232,residualCheck1232,
  ReferenceTrajectory.leftBlock73_subset (List.mem_of_getElem? (show ReferenceResiduals.block73[1]?=some panel1232.left from rfl)),
  ReferenceTrajectory.rightBlock80_subset (List.mem_of_getElem? (show ReferenceResiduals.block80[6]?=some panel1232.right from rfl))⟩
theorem valid1233 : ValidPanel panel1233 := ⟨modelCheck1233,residualCheck1233,
  ReferenceTrajectory.leftBlock73_subset (List.mem_of_getElem? (show ReferenceResiduals.block73[2]?=some panel1233.left from rfl)),
  ReferenceTrajectory.rightBlock80_subset (List.mem_of_getElem? (show ReferenceResiduals.block80[5]?=some panel1233.right from rfl))⟩
theorem valid1234 : ValidPanel panel1234 := ⟨modelCheck1234,residualCheck1234,
  ReferenceTrajectory.leftBlock73_subset (List.mem_of_getElem? (show ReferenceResiduals.block73[3]?=some panel1234.left from rfl)),
  ReferenceTrajectory.rightBlock80_subset (List.mem_of_getElem? (show ReferenceResiduals.block80[4]?=some panel1234.right from rfl))⟩
theorem valid1235 : ValidPanel panel1235 := ⟨modelCheck1235,residualCheck1235,
  ReferenceTrajectory.leftBlock73_subset (List.mem_of_getElem? (show ReferenceResiduals.block73[4]?=some panel1235.left from rfl)),
  ReferenceTrajectory.rightBlock80_subset (List.mem_of_getElem? (show ReferenceResiduals.block80[3]?=some panel1235.right from rfl))⟩
theorem valid1236 : ValidPanel panel1236 := ⟨modelCheck1236,residualCheck1236,
  ReferenceTrajectory.leftBlock73_subset (List.mem_of_getElem? (show ReferenceResiduals.block73[5]?=some panel1236.left from rfl)),
  ReferenceTrajectory.rightBlock80_subset (List.mem_of_getElem? (show ReferenceResiduals.block80[2]?=some panel1236.right from rfl))⟩
theorem valid1237 : ValidPanel panel1237 := ⟨modelCheck1237,residualCheck1237,
  ReferenceTrajectory.leftBlock73_subset (List.mem_of_getElem? (show ReferenceResiduals.block73[6]?=some panel1237.left from rfl)),
  ReferenceTrajectory.rightBlock80_subset (List.mem_of_getElem? (show ReferenceResiduals.block80[1]?=some panel1237.right from rfl))⟩
theorem valid1238 : ValidPanel panel1238 := ⟨modelCheck1238,residualCheck1238,
  ReferenceTrajectory.leftBlock73_subset (List.mem_of_getElem? (show ReferenceResiduals.block73[7]?=some panel1238.left from rfl)),
  ReferenceTrajectory.rightBlock80_subset (List.mem_of_getElem? (show ReferenceResiduals.block80[0]?=some panel1238.right from rfl))⟩
theorem valid1239 : ValidPanel panel1239 := ⟨modelCheck1239,residualCheck1239,
  ReferenceTrajectory.leftBlock73_subset (List.mem_of_getElem? (show ReferenceResiduals.block73[8]?=some panel1239.left from rfl)),
  ReferenceTrajectory.rightBlock79_subset (List.mem_of_getElem? (show ReferenceResiduals.block79[15]?=some panel1239.right from rfl))⟩
theorem valid1240 : ValidPanel panel1240 := ⟨modelCheck1240,residualCheck1240,
  ReferenceTrajectory.leftBlock73_subset (List.mem_of_getElem? (show ReferenceResiduals.block73[9]?=some panel1240.left from rfl)),
  ReferenceTrajectory.rightBlock79_subset (List.mem_of_getElem? (show ReferenceResiduals.block79[14]?=some panel1240.right from rfl))⟩
theorem valid1241 : ValidPanel panel1241 := ⟨modelCheck1241,residualCheck1241,
  ReferenceTrajectory.leftBlock73_subset (List.mem_of_getElem? (show ReferenceResiduals.block73[10]?=some panel1241.left from rfl)),
  ReferenceTrajectory.rightBlock79_subset (List.mem_of_getElem? (show ReferenceResiduals.block79[13]?=some panel1241.right from rfl))⟩
theorem valid1242 : ValidPanel panel1242 := ⟨modelCheck1242,residualCheck1242,
  ReferenceTrajectory.leftBlock73_subset (List.mem_of_getElem? (show ReferenceResiduals.block73[11]?=some panel1242.left from rfl)),
  ReferenceTrajectory.rightBlock79_subset (List.mem_of_getElem? (show ReferenceResiduals.block79[12]?=some panel1242.right from rfl))⟩
theorem valid1243 : ValidPanel panel1243 := ⟨modelCheck1243,residualCheck1243,
  ReferenceTrajectory.leftBlock73_subset (List.mem_of_getElem? (show ReferenceResiduals.block73[12]?=some panel1243.left from rfl)),
  ReferenceTrajectory.rightBlock79_subset (List.mem_of_getElem? (show ReferenceResiduals.block79[11]?=some panel1243.right from rfl))⟩
theorem valid1244 : ValidPanel panel1244 := ⟨modelCheck1244,residualCheck1244,
  ReferenceTrajectory.leftBlock73_subset (List.mem_of_getElem? (show ReferenceResiduals.block73[13]?=some panel1244.left from rfl)),
  ReferenceTrajectory.rightBlock79_subset (List.mem_of_getElem? (show ReferenceResiduals.block79[10]?=some panel1244.right from rfl))⟩
theorem valid1245 : ValidPanel panel1245 := ⟨modelCheck1245,residualCheck1245,
  ReferenceTrajectory.leftBlock73_subset (List.mem_of_getElem? (show ReferenceResiduals.block73[14]?=some panel1245.left from rfl)),
  ReferenceTrajectory.rightBlock79_subset (List.mem_of_getElem? (show ReferenceResiduals.block79[9]?=some panel1245.right from rfl))⟩
theorem valid1246 : ValidPanel panel1246 := ⟨modelCheck1246,residualCheck1246,
  ReferenceTrajectory.leftBlock73_subset (List.mem_of_getElem? (show ReferenceResiduals.block73[15]?=some panel1246.left from rfl)),
  ReferenceTrajectory.rightBlock79_subset (List.mem_of_getElem? (show ReferenceResiduals.block79[8]?=some panel1246.right from rfl))⟩
theorem valid1247 : ValidPanel panel1247 := ⟨modelCheck1247,residualCheck1247,
  ReferenceTrajectory.leftBlock74_subset (List.mem_of_getElem? (show ReferenceResiduals.block74[0]?=some panel1247.left from rfl)),
  ReferenceTrajectory.rightBlock79_subset (List.mem_of_getElem? (show ReferenceResiduals.block79[7]?=some panel1247.right from rfl))⟩
theorem validBlock38 : ∀ p∈block38,ValidPanel p := by
  simp only [block38,List.forall_mem_cons]
  exact ⟨valid1216,⟨valid1217,⟨valid1218,⟨valid1219,⟨valid1220,⟨valid1221,⟨valid1222,⟨valid1223,⟨valid1224,⟨valid1225,⟨valid1226,⟨valid1227,⟨valid1228,⟨valid1229,⟨valid1230,⟨valid1231,⟨valid1232,⟨valid1233,⟨valid1234,⟨valid1235,⟨valid1236,⟨valid1237,⟨valid1238,⟨valid1239,⟨valid1240,⟨valid1241,⟨valid1242,⟨valid1243,⟨valid1244,⟨valid1245,⟨valid1246,⟨valid1247,(by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end chebyshev2.Certificates.Compact.ContactValues

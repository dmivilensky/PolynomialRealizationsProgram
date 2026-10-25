import chebyshev2.Certificates.Compact.ContactBatches.Batch039
import chebyshev2.Certificates.Compact.ContactCoverage
import chebyshev2.Certificates.Compact.ReferenceTrajectoryIndex

/-!
Article: chebyshev2, Section 4.1.
Correspondence039.
Use: `chebyshev2.Certificates.Compact.ContactValues.validBlock39` feeds
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
theorem valid1248 : ValidPanel panel1248 := ⟨modelCheck1248,residualCheck1248,
  ReferenceTrajectory.leftBlock74_subset (List.mem_of_getElem? (show ReferenceResiduals.block74[1]?=some panel1248.left from rfl)),
  ReferenceTrajectory.rightBlock79_subset (List.mem_of_getElem? (show ReferenceResiduals.block79[6]?=some panel1248.right from rfl))⟩
theorem valid1249 : ValidPanel panel1249 := ⟨modelCheck1249,residualCheck1249,
  ReferenceTrajectory.leftBlock74_subset (List.mem_of_getElem? (show ReferenceResiduals.block74[2]?=some panel1249.left from rfl)),
  ReferenceTrajectory.rightBlock79_subset (List.mem_of_getElem? (show ReferenceResiduals.block79[5]?=some panel1249.right from rfl))⟩
theorem valid1250 : ValidPanel panel1250 := ⟨modelCheck1250,residualCheck1250,
  ReferenceTrajectory.leftBlock74_subset (List.mem_of_getElem? (show ReferenceResiduals.block74[3]?=some panel1250.left from rfl)),
  ReferenceTrajectory.rightBlock79_subset (List.mem_of_getElem? (show ReferenceResiduals.block79[4]?=some panel1250.right from rfl))⟩
theorem valid1251 : ValidPanel panel1251 := ⟨modelCheck1251,residualCheck1251,
  ReferenceTrajectory.leftBlock74_subset (List.mem_of_getElem? (show ReferenceResiduals.block74[4]?=some panel1251.left from rfl)),
  ReferenceTrajectory.rightBlock79_subset (List.mem_of_getElem? (show ReferenceResiduals.block79[3]?=some panel1251.right from rfl))⟩
theorem valid1252 : ValidPanel panel1252 := ⟨modelCheck1252,residualCheck1252,
  ReferenceTrajectory.leftBlock74_subset (List.mem_of_getElem? (show ReferenceResiduals.block74[5]?=some panel1252.left from rfl)),
  ReferenceTrajectory.rightBlock79_subset (List.mem_of_getElem? (show ReferenceResiduals.block79[2]?=some panel1252.right from rfl))⟩
theorem valid1253 : ValidPanel panel1253 := ⟨modelCheck1253,residualCheck1253,
  ReferenceTrajectory.leftBlock74_subset (List.mem_of_getElem? (show ReferenceResiduals.block74[6]?=some panel1253.left from rfl)),
  ReferenceTrajectory.rightBlock79_subset (List.mem_of_getElem? (show ReferenceResiduals.block79[1]?=some panel1253.right from rfl))⟩
theorem valid1254 : ValidPanel panel1254 := ⟨modelCheck1254,residualCheck1254,
  ReferenceTrajectory.leftBlock74_subset (List.mem_of_getElem? (show ReferenceResiduals.block74[7]?=some panel1254.left from rfl)),
  ReferenceTrajectory.rightBlock79_subset (List.mem_of_getElem? (show ReferenceResiduals.block79[0]?=some panel1254.right from rfl))⟩
theorem valid1255 : ValidPanel panel1255 := ⟨modelCheck1255,residualCheck1255,
  ReferenceTrajectory.leftBlock74_subset (List.mem_of_getElem? (show ReferenceResiduals.block74[8]?=some panel1255.left from rfl)),
  ReferenceTrajectory.rightBlock78_subset (List.mem_of_getElem? (show ReferenceResiduals.block78[15]?=some panel1255.right from rfl))⟩
theorem valid1256 : ValidPanel panel1256 := ⟨modelCheck1256,residualCheck1256,
  ReferenceTrajectory.leftBlock74_subset (List.mem_of_getElem? (show ReferenceResiduals.block74[9]?=some panel1256.left from rfl)),
  ReferenceTrajectory.rightBlock78_subset (List.mem_of_getElem? (show ReferenceResiduals.block78[14]?=some panel1256.right from rfl))⟩
theorem valid1257 : ValidPanel panel1257 := ⟨modelCheck1257,residualCheck1257,
  ReferenceTrajectory.leftBlock74_subset (List.mem_of_getElem? (show ReferenceResiduals.block74[10]?=some panel1257.left from rfl)),
  ReferenceTrajectory.rightBlock78_subset (List.mem_of_getElem? (show ReferenceResiduals.block78[13]?=some panel1257.right from rfl))⟩
theorem valid1258 : ValidPanel panel1258 := ⟨modelCheck1258,residualCheck1258,
  ReferenceTrajectory.leftBlock74_subset (List.mem_of_getElem? (show ReferenceResiduals.block74[11]?=some panel1258.left from rfl)),
  ReferenceTrajectory.rightBlock78_subset (List.mem_of_getElem? (show ReferenceResiduals.block78[12]?=some panel1258.right from rfl))⟩
theorem valid1259 : ValidPanel panel1259 := ⟨modelCheck1259,residualCheck1259,
  ReferenceTrajectory.leftBlock74_subset (List.mem_of_getElem? (show ReferenceResiduals.block74[12]?=some panel1259.left from rfl)),
  ReferenceTrajectory.rightBlock78_subset (List.mem_of_getElem? (show ReferenceResiduals.block78[11]?=some panel1259.right from rfl))⟩
theorem valid1260 : ValidPanel panel1260 := ⟨modelCheck1260,residualCheck1260,
  ReferenceTrajectory.leftBlock74_subset (List.mem_of_getElem? (show ReferenceResiduals.block74[13]?=some panel1260.left from rfl)),
  ReferenceTrajectory.rightBlock78_subset (List.mem_of_getElem? (show ReferenceResiduals.block78[10]?=some panel1260.right from rfl))⟩
theorem valid1261 : ValidPanel panel1261 := ⟨modelCheck1261,residualCheck1261,
  ReferenceTrajectory.leftBlock74_subset (List.mem_of_getElem? (show ReferenceResiduals.block74[14]?=some panel1261.left from rfl)),
  ReferenceTrajectory.rightBlock78_subset (List.mem_of_getElem? (show ReferenceResiduals.block78[9]?=some panel1261.right from rfl))⟩
theorem valid1262 : ValidPanel panel1262 := ⟨modelCheck1262,residualCheck1262,
  ReferenceTrajectory.leftBlock74_subset (List.mem_of_getElem? (show ReferenceResiduals.block74[15]?=some panel1262.left from rfl)),
  ReferenceTrajectory.rightBlock78_subset (List.mem_of_getElem? (show ReferenceResiduals.block78[8]?=some panel1262.right from rfl))⟩
theorem valid1263 : ValidPanel panel1263 := ⟨modelCheck1263,residualCheck1263,
  ReferenceTrajectory.leftBlock75_subset (List.mem_of_getElem? (show ReferenceResiduals.block75[0]?=some panel1263.left from rfl)),
  ReferenceTrajectory.rightBlock78_subset (List.mem_of_getElem? (show ReferenceResiduals.block78[7]?=some panel1263.right from rfl))⟩
theorem valid1264 : ValidPanel panel1264 := ⟨modelCheck1264,residualCheck1264,
  ReferenceTrajectory.leftBlock75_subset (List.mem_of_getElem? (show ReferenceResiduals.block75[1]?=some panel1264.left from rfl)),
  ReferenceTrajectory.rightBlock78_subset (List.mem_of_getElem? (show ReferenceResiduals.block78[6]?=some panel1264.right from rfl))⟩
theorem valid1265 : ValidPanel panel1265 := ⟨modelCheck1265,residualCheck1265,
  ReferenceTrajectory.leftBlock75_subset (List.mem_of_getElem? (show ReferenceResiduals.block75[2]?=some panel1265.left from rfl)),
  ReferenceTrajectory.rightBlock78_subset (List.mem_of_getElem? (show ReferenceResiduals.block78[5]?=some panel1265.right from rfl))⟩
theorem valid1266 : ValidPanel panel1266 := ⟨modelCheck1266,residualCheck1266,
  ReferenceTrajectory.leftBlock75_subset (List.mem_of_getElem? (show ReferenceResiduals.block75[3]?=some panel1266.left from rfl)),
  ReferenceTrajectory.rightBlock78_subset (List.mem_of_getElem? (show ReferenceResiduals.block78[4]?=some panel1266.right from rfl))⟩
theorem valid1267 : ValidPanel panel1267 := ⟨modelCheck1267,residualCheck1267,
  ReferenceTrajectory.leftBlock75_subset (List.mem_of_getElem? (show ReferenceResiduals.block75[4]?=some panel1267.left from rfl)),
  ReferenceTrajectory.rightBlock78_subset (List.mem_of_getElem? (show ReferenceResiduals.block78[3]?=some panel1267.right from rfl))⟩
theorem valid1268 : ValidPanel panel1268 := ⟨modelCheck1268,residualCheck1268,
  ReferenceTrajectory.leftBlock75_subset (List.mem_of_getElem? (show ReferenceResiduals.block75[5]?=some panel1268.left from rfl)),
  ReferenceTrajectory.rightBlock78_subset (List.mem_of_getElem? (show ReferenceResiduals.block78[2]?=some panel1268.right from rfl))⟩
theorem valid1269 : ValidPanel panel1269 := ⟨modelCheck1269,residualCheck1269,
  ReferenceTrajectory.leftBlock75_subset (List.mem_of_getElem? (show ReferenceResiduals.block75[6]?=some panel1269.left from rfl)),
  ReferenceTrajectory.rightBlock78_subset (List.mem_of_getElem? (show ReferenceResiduals.block78[1]?=some panel1269.right from rfl))⟩
theorem valid1270 : ValidPanel panel1270 := ⟨modelCheck1270,residualCheck1270,
  ReferenceTrajectory.leftBlock75_subset (List.mem_of_getElem? (show ReferenceResiduals.block75[7]?=some panel1270.left from rfl)),
  ReferenceTrajectory.rightBlock78_subset (List.mem_of_getElem? (show ReferenceResiduals.block78[0]?=some panel1270.right from rfl))⟩
theorem valid1271 : ValidPanel panel1271 := ⟨modelCheck1271,residualCheck1271,
  ReferenceTrajectory.leftBlock75_subset (List.mem_of_getElem? (show ReferenceResiduals.block75[8]?=some panel1271.left from rfl)),
  ReferenceTrajectory.rightBlock77_subset (List.mem_of_getElem? (show ReferenceResiduals.block77[15]?=some panel1271.right from rfl))⟩
theorem valid1272 : ValidPanel panel1272 := ⟨modelCheck1272,residualCheck1272,
  ReferenceTrajectory.leftBlock75_subset (List.mem_of_getElem? (show ReferenceResiduals.block75[9]?=some panel1272.left from rfl)),
  ReferenceTrajectory.rightBlock77_subset (List.mem_of_getElem? (show ReferenceResiduals.block77[14]?=some panel1272.right from rfl))⟩
theorem valid1273 : ValidPanel panel1273 := ⟨modelCheck1273,residualCheck1273,
  ReferenceTrajectory.leftBlock75_subset (List.mem_of_getElem? (show ReferenceResiduals.block75[10]?=some panel1273.left from rfl)),
  ReferenceTrajectory.rightBlock77_subset (List.mem_of_getElem? (show ReferenceResiduals.block77[13]?=some panel1273.right from rfl))⟩
theorem valid1274 : ValidPanel panel1274 := ⟨modelCheck1274,residualCheck1274,
  ReferenceTrajectory.leftBlock75_subset (List.mem_of_getElem? (show ReferenceResiduals.block75[11]?=some panel1274.left from rfl)),
  ReferenceTrajectory.rightBlock77_subset (List.mem_of_getElem? (show ReferenceResiduals.block77[12]?=some panel1274.right from rfl))⟩
theorem valid1275 : ValidPanel panel1275 := ⟨modelCheck1275,residualCheck1275,
  ReferenceTrajectory.leftBlock75_subset (List.mem_of_getElem? (show ReferenceResiduals.block75[12]?=some panel1275.left from rfl)),
  ReferenceTrajectory.rightBlock77_subset (List.mem_of_getElem? (show ReferenceResiduals.block77[11]?=some panel1275.right from rfl))⟩
theorem valid1276 : ValidPanel panel1276 := ⟨modelCheck1276,residualCheck1276,
  ReferenceTrajectory.leftBlock75_subset (List.mem_of_getElem? (show ReferenceResiduals.block75[13]?=some panel1276.left from rfl)),
  ReferenceTrajectory.rightBlock77_subset (List.mem_of_getElem? (show ReferenceResiduals.block77[10]?=some panel1276.right from rfl))⟩
theorem valid1277 : ValidPanel panel1277 := ⟨modelCheck1277,residualCheck1277,
  ReferenceTrajectory.leftBlock75_subset (List.mem_of_getElem? (show ReferenceResiduals.block75[14]?=some panel1277.left from rfl)),
  ReferenceTrajectory.rightBlock77_subset (List.mem_of_getElem? (show ReferenceResiduals.block77[9]?=some panel1277.right from rfl))⟩
theorem valid1278 : ValidPanel panel1278 := ⟨modelCheck1278,residualCheck1278,
  ReferenceTrajectory.leftBlock75_subset (List.mem_of_getElem? (show ReferenceResiduals.block75[15]?=some panel1278.left from rfl)),
  ReferenceTrajectory.rightBlock77_subset (List.mem_of_getElem? (show ReferenceResiduals.block77[8]?=some panel1278.right from rfl))⟩
theorem valid1279 : ValidPanel panel1279 := ⟨modelCheck1279,residualCheck1279,
  ReferenceTrajectory.leftBlock76_subset (List.mem_of_getElem? (show (ReferenceResiduals.block76.take 12)[0]?=some panel1279.left from rfl)),
  ReferenceTrajectory.rightBlock77_subset (List.mem_of_getElem? (show ReferenceResiduals.block77[7]?=some panel1279.right from rfl))⟩
theorem validBlock39 : ∀ p∈block39,ValidPanel p := by
  simp only [block39,List.forall_mem_cons]
  exact ⟨valid1248,⟨valid1249,⟨valid1250,⟨valid1251,⟨valid1252,⟨valid1253,⟨valid1254,⟨valid1255,⟨valid1256,⟨valid1257,⟨valid1258,⟨valid1259,⟨valid1260,⟨valid1261,⟨valid1262,⟨valid1263,⟨valid1264,⟨valid1265,⟨valid1266,⟨valid1267,⟨valid1268,⟨valid1269,⟨valid1270,⟨valid1271,⟨valid1272,⟨valid1273,⟨valid1274,⟨valid1275,⟨valid1276,⟨valid1277,⟨valid1278,⟨valid1279,(by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end chebyshev2.Certificates.Compact.ContactValues

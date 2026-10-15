import «2610.05164v2».Certificates.Compact.ContactBatches.Batch040
import «2610.05164v2».Certificates.Compact.ContactCoverage
import «2610.05164v2».Certificates.Compact.ReferenceTrajectoryIndex

/-!
Article: 2610.05164v2, Section 4.1.
Correspondence040.
Use: `«2610.05164v2».Certificates.Compact.ContactValues.validBlock40` feeds
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
theorem valid1280 : ValidPanel panel1280 := ⟨modelCheck1280,residualCheck1280,
  ReferenceTrajectory.leftBlock76_subset (List.mem_of_getElem? (show (ReferenceResiduals.block76.take 12)[1]?=some panel1280.left from rfl)),
  ReferenceTrajectory.rightBlock77_subset (List.mem_of_getElem? (show ReferenceResiduals.block77[6]?=some panel1280.right from rfl))⟩
theorem valid1281 : ValidPanel panel1281 := ⟨modelCheck1281,residualCheck1281,
  ReferenceTrajectory.leftBlock76_subset (List.mem_of_getElem? (show (ReferenceResiduals.block76.take 12)[2]?=some panel1281.left from rfl)),
  ReferenceTrajectory.rightBlock77_subset (List.mem_of_getElem? (show ReferenceResiduals.block77[5]?=some panel1281.right from rfl))⟩
theorem valid1282 : ValidPanel panel1282 := ⟨modelCheck1282,residualCheck1282,
  ReferenceTrajectory.leftBlock76_subset (List.mem_of_getElem? (show (ReferenceResiduals.block76.take 12)[3]?=some panel1282.left from rfl)),
  ReferenceTrajectory.rightBlock77_subset (List.mem_of_getElem? (show ReferenceResiduals.block77[4]?=some panel1282.right from rfl))⟩
theorem valid1283 : ValidPanel panel1283 := ⟨modelCheck1283,residualCheck1283,
  ReferenceTrajectory.leftBlock76_subset (List.mem_of_getElem? (show (ReferenceResiduals.block76.take 12)[4]?=some panel1283.left from rfl)),
  ReferenceTrajectory.rightBlock77_subset (List.mem_of_getElem? (show ReferenceResiduals.block77[3]?=some panel1283.right from rfl))⟩
theorem valid1284 : ValidPanel panel1284 := ⟨modelCheck1284,residualCheck1284,
  ReferenceTrajectory.leftBlock76_subset (List.mem_of_getElem? (show (ReferenceResiduals.block76.take 12)[5]?=some panel1284.left from rfl)),
  ReferenceTrajectory.rightBlock77_subset (List.mem_of_getElem? (show ReferenceResiduals.block77[2]?=some panel1284.right from rfl))⟩
theorem valid1285 : ValidPanel panel1285 := ⟨modelCheck1285,residualCheck1285,
  ReferenceTrajectory.leftBlock76_subset (List.mem_of_getElem? (show (ReferenceResiduals.block76.take 12)[6]?=some panel1285.left from rfl)),
  ReferenceTrajectory.rightBlock77_subset (List.mem_of_getElem? (show ReferenceResiduals.block77[1]?=some panel1285.right from rfl))⟩
theorem valid1286 : ValidPanel panel1286 := ⟨modelCheck1286,residualCheck1286,
  ReferenceTrajectory.leftBlock76_subset (List.mem_of_getElem? (show (ReferenceResiduals.block76.take 12)[7]?=some panel1286.left from rfl)),
  ReferenceTrajectory.rightBlock77_subset (List.mem_of_getElem? (show ReferenceResiduals.block77[0]?=some panel1286.right from rfl))⟩
theorem valid1287 : ValidPanel panel1287 := ⟨modelCheck1287,residualCheck1287,
  ReferenceTrajectory.leftBlock76_subset (List.mem_of_getElem? (show (ReferenceResiduals.block76.take 12)[8]?=some panel1287.left from rfl)),
  ReferenceTrajectory.rightBlock76_subset (List.mem_of_getElem? (show (ReferenceResiduals.block76.drop 12)[3]?=some panel1287.right from rfl))⟩
theorem valid1288 : ValidPanel panel1288 := ⟨modelCheck1288,residualCheck1288,
  ReferenceTrajectory.leftBlock76_subset (List.mem_of_getElem? (show (ReferenceResiduals.block76.take 12)[9]?=some panel1288.left from rfl)),
  ReferenceTrajectory.rightBlock76_subset (List.mem_of_getElem? (show (ReferenceResiduals.block76.drop 12)[2]?=some panel1288.right from rfl))⟩
theorem valid1289 : ValidPanel panel1289 := ⟨modelCheck1289,residualCheck1289,
  ReferenceTrajectory.leftBlock76_subset (List.mem_of_getElem? (show (ReferenceResiduals.block76.take 12)[10]?=some panel1289.left from rfl)),
  ReferenceTrajectory.rightBlock76_subset (List.mem_of_getElem? (show (ReferenceResiduals.block76.drop 12)[1]?=some panel1289.right from rfl))⟩
theorem valid1290 : ValidPanel panel1290 := ⟨modelCheck1290,residualCheck1290,
  ReferenceTrajectory.leftBlock76_subset (List.mem_of_getElem? (show (ReferenceResiduals.block76.take 12)[11]?=some panel1290.left from rfl)),
  ReferenceTrajectory.rightBlock76_subset (List.mem_of_getElem? (show (ReferenceResiduals.block76.drop 12)[0]?=some panel1290.right from rfl))⟩
theorem validBlock40 : ∀ p∈block40,ValidPanel p := by
  simp only [block40,List.forall_mem_cons]
  exact ⟨valid1280,⟨valid1281,⟨valid1282,⟨valid1283,⟨valid1284,⟨valid1285,⟨valid1286,⟨valid1287,⟨valid1288,⟨valid1289,⟨valid1290,(by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end «2610.05164v2».Certificates.Compact.ContactValues

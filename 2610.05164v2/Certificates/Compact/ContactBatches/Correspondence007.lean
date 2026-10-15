import «2610.05164v2».Certificates.Compact.ContactBatches.Batch007
import «2610.05164v2».Certificates.Compact.ContactCoverage
import «2610.05164v2».Certificates.Compact.ReferenceTrajectoryIndex

/-!
Article: 2610.05164v2, Section 4.1.
Correspondence007.
Use: `«2610.05164v2».Certificates.Compact.ContactValues.validBlock7` feeds
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
theorem valid224 : ValidPanel panel224 := ⟨modelCheck224,residualCheck224,
  ReferenceTrajectory.leftBlock11_subset (List.mem_of_getElem? (show ReferenceResiduals.block11[0]?=some panel224.left from rfl)),
  ReferenceTrajectory.rightBlock143_subset (List.mem_of_getElem? (show ReferenceResiduals.block143[6]?=some panel224.right from rfl))⟩
theorem valid225 : ValidPanel panel225 := ⟨modelCheck225,residualCheck225,
  ReferenceTrajectory.leftBlock11_subset (List.mem_of_getElem? (show ReferenceResiduals.block11[1]?=some panel225.left from rfl)),
  ReferenceTrajectory.rightBlock143_subset (List.mem_of_getElem? (show ReferenceResiduals.block143[5]?=some panel225.right from rfl))⟩
theorem valid226 : ValidPanel panel226 := ⟨modelCheck226,residualCheck226,
  ReferenceTrajectory.leftBlock11_subset (List.mem_of_getElem? (show ReferenceResiduals.block11[2]?=some panel226.left from rfl)),
  ReferenceTrajectory.rightBlock143_subset (List.mem_of_getElem? (show ReferenceResiduals.block143[4]?=some panel226.right from rfl))⟩
theorem valid227 : ValidPanel panel227 := ⟨modelCheck227,residualCheck227,
  ReferenceTrajectory.leftBlock11_subset (List.mem_of_getElem? (show ReferenceResiduals.block11[3]?=some panel227.left from rfl)),
  ReferenceTrajectory.rightBlock143_subset (List.mem_of_getElem? (show ReferenceResiduals.block143[3]?=some panel227.right from rfl))⟩
theorem valid228 : ValidPanel panel228 := ⟨modelCheck228,residualCheck228,
  ReferenceTrajectory.leftBlock11_subset (List.mem_of_getElem? (show ReferenceResiduals.block11[4]?=some panel228.left from rfl)),
  ReferenceTrajectory.rightBlock143_subset (List.mem_of_getElem? (show ReferenceResiduals.block143[2]?=some panel228.right from rfl))⟩
theorem valid229 : ValidPanel panel229 := ⟨modelCheck229,residualCheck229,
  ReferenceTrajectory.leftBlock11_subset (List.mem_of_getElem? (show ReferenceResiduals.block11[5]?=some panel229.left from rfl)),
  ReferenceTrajectory.rightBlock143_subset (List.mem_of_getElem? (show ReferenceResiduals.block143[1]?=some panel229.right from rfl))⟩
theorem valid230 : ValidPanel panel230 := ⟨modelCheck230,residualCheck230,
  ReferenceTrajectory.leftBlock11_subset (List.mem_of_getElem? (show ReferenceResiduals.block11[6]?=some panel230.left from rfl)),
  ReferenceTrajectory.rightBlock143_subset (List.mem_of_getElem? (show ReferenceResiduals.block143[0]?=some panel230.right from rfl))⟩
theorem valid231 : ValidPanel panel231 := ⟨modelCheck231,residualCheck231,
  ReferenceTrajectory.leftBlock11_subset (List.mem_of_getElem? (show ReferenceResiduals.block11[7]?=some panel231.left from rfl)),
  ReferenceTrajectory.rightBlock142_subset (List.mem_of_getElem? (show ReferenceResiduals.block142[15]?=some panel231.right from rfl))⟩
theorem valid232 : ValidPanel panel232 := ⟨modelCheck232,residualCheck232,
  ReferenceTrajectory.leftBlock11_subset (List.mem_of_getElem? (show ReferenceResiduals.block11[8]?=some panel232.left from rfl)),
  ReferenceTrajectory.rightBlock142_subset (List.mem_of_getElem? (show ReferenceResiduals.block142[14]?=some panel232.right from rfl))⟩
theorem valid233 : ValidPanel panel233 := ⟨modelCheck233,residualCheck233,
  ReferenceTrajectory.leftBlock11_subset (List.mem_of_getElem? (show ReferenceResiduals.block11[9]?=some panel233.left from rfl)),
  ReferenceTrajectory.rightBlock142_subset (List.mem_of_getElem? (show ReferenceResiduals.block142[13]?=some panel233.right from rfl))⟩
theorem valid234 : ValidPanel panel234 := ⟨modelCheck234,residualCheck234,
  ReferenceTrajectory.leftBlock11_subset (List.mem_of_getElem? (show ReferenceResiduals.block11[10]?=some panel234.left from rfl)),
  ReferenceTrajectory.rightBlock142_subset (List.mem_of_getElem? (show ReferenceResiduals.block142[12]?=some panel234.right from rfl))⟩
theorem valid235 : ValidPanel panel235 := ⟨modelCheck235,residualCheck235,
  ReferenceTrajectory.leftBlock11_subset (List.mem_of_getElem? (show ReferenceResiduals.block11[11]?=some panel235.left from rfl)),
  ReferenceTrajectory.rightBlock142_subset (List.mem_of_getElem? (show ReferenceResiduals.block142[11]?=some panel235.right from rfl))⟩
theorem valid236 : ValidPanel panel236 := ⟨modelCheck236,residualCheck236,
  ReferenceTrajectory.leftBlock11_subset (List.mem_of_getElem? (show ReferenceResiduals.block11[12]?=some panel236.left from rfl)),
  ReferenceTrajectory.rightBlock142_subset (List.mem_of_getElem? (show ReferenceResiduals.block142[10]?=some panel236.right from rfl))⟩
theorem valid237 : ValidPanel panel237 := ⟨modelCheck237,residualCheck237,
  ReferenceTrajectory.leftBlock11_subset (List.mem_of_getElem? (show ReferenceResiduals.block11[13]?=some panel237.left from rfl)),
  ReferenceTrajectory.rightBlock142_subset (List.mem_of_getElem? (show ReferenceResiduals.block142[9]?=some panel237.right from rfl))⟩
theorem valid238 : ValidPanel panel238 := ⟨modelCheck238,residualCheck238,
  ReferenceTrajectory.leftBlock11_subset (List.mem_of_getElem? (show ReferenceResiduals.block11[14]?=some panel238.left from rfl)),
  ReferenceTrajectory.rightBlock142_subset (List.mem_of_getElem? (show ReferenceResiduals.block142[8]?=some panel238.right from rfl))⟩
theorem valid239 : ValidPanel panel239 := ⟨modelCheck239,residualCheck239,
  ReferenceTrajectory.leftBlock11_subset (List.mem_of_getElem? (show ReferenceResiduals.block11[15]?=some panel239.left from rfl)),
  ReferenceTrajectory.rightBlock142_subset (List.mem_of_getElem? (show ReferenceResiduals.block142[7]?=some panel239.right from rfl))⟩
theorem valid240 : ValidPanel panel240 := ⟨modelCheck240,residualCheck240,
  ReferenceTrajectory.leftBlock12_subset (List.mem_of_getElem? (show ReferenceResiduals.block12[0]?=some panel240.left from rfl)),
  ReferenceTrajectory.rightBlock142_subset (List.mem_of_getElem? (show ReferenceResiduals.block142[6]?=some panel240.right from rfl))⟩
theorem valid241 : ValidPanel panel241 := ⟨modelCheck241,residualCheck241,
  ReferenceTrajectory.leftBlock12_subset (List.mem_of_getElem? (show ReferenceResiduals.block12[1]?=some panel241.left from rfl)),
  ReferenceTrajectory.rightBlock142_subset (List.mem_of_getElem? (show ReferenceResiduals.block142[5]?=some panel241.right from rfl))⟩
theorem valid242 : ValidPanel panel242 := ⟨modelCheck242,residualCheck242,
  ReferenceTrajectory.leftBlock12_subset (List.mem_of_getElem? (show ReferenceResiduals.block12[2]?=some panel242.left from rfl)),
  ReferenceTrajectory.rightBlock142_subset (List.mem_of_getElem? (show ReferenceResiduals.block142[4]?=some panel242.right from rfl))⟩
theorem valid243 : ValidPanel panel243 := ⟨modelCheck243,residualCheck243,
  ReferenceTrajectory.leftBlock12_subset (List.mem_of_getElem? (show ReferenceResiduals.block12[3]?=some panel243.left from rfl)),
  ReferenceTrajectory.rightBlock142_subset (List.mem_of_getElem? (show ReferenceResiduals.block142[3]?=some panel243.right from rfl))⟩
theorem valid244 : ValidPanel panel244 := ⟨modelCheck244,residualCheck244,
  ReferenceTrajectory.leftBlock12_subset (List.mem_of_getElem? (show ReferenceResiduals.block12[4]?=some panel244.left from rfl)),
  ReferenceTrajectory.rightBlock142_subset (List.mem_of_getElem? (show ReferenceResiduals.block142[2]?=some panel244.right from rfl))⟩
theorem valid245 : ValidPanel panel245 := ⟨modelCheck245,residualCheck245,
  ReferenceTrajectory.leftBlock12_subset (List.mem_of_getElem? (show ReferenceResiduals.block12[5]?=some panel245.left from rfl)),
  ReferenceTrajectory.rightBlock142_subset (List.mem_of_getElem? (show ReferenceResiduals.block142[1]?=some panel245.right from rfl))⟩
theorem valid246 : ValidPanel panel246 := ⟨modelCheck246,residualCheck246,
  ReferenceTrajectory.leftBlock12_subset (List.mem_of_getElem? (show ReferenceResiduals.block12[6]?=some panel246.left from rfl)),
  ReferenceTrajectory.rightBlock142_subset (List.mem_of_getElem? (show ReferenceResiduals.block142[0]?=some panel246.right from rfl))⟩
theorem valid247 : ValidPanel panel247 := ⟨modelCheck247,residualCheck247,
  ReferenceTrajectory.leftBlock12_subset (List.mem_of_getElem? (show ReferenceResiduals.block12[7]?=some panel247.left from rfl)),
  ReferenceTrajectory.rightBlock141_subset (List.mem_of_getElem? (show ReferenceResiduals.block141[15]?=some panel247.right from rfl))⟩
theorem valid248 : ValidPanel panel248 := ⟨modelCheck248,residualCheck248,
  ReferenceTrajectory.leftBlock12_subset (List.mem_of_getElem? (show ReferenceResiduals.block12[8]?=some panel248.left from rfl)),
  ReferenceTrajectory.rightBlock141_subset (List.mem_of_getElem? (show ReferenceResiduals.block141[14]?=some panel248.right from rfl))⟩
theorem valid249 : ValidPanel panel249 := ⟨modelCheck249,residualCheck249,
  ReferenceTrajectory.leftBlock12_subset (List.mem_of_getElem? (show ReferenceResiduals.block12[9]?=some panel249.left from rfl)),
  ReferenceTrajectory.rightBlock141_subset (List.mem_of_getElem? (show ReferenceResiduals.block141[13]?=some panel249.right from rfl))⟩
theorem valid250 : ValidPanel panel250 := ⟨modelCheck250,residualCheck250,
  ReferenceTrajectory.leftBlock12_subset (List.mem_of_getElem? (show ReferenceResiduals.block12[10]?=some panel250.left from rfl)),
  ReferenceTrajectory.rightBlock141_subset (List.mem_of_getElem? (show ReferenceResiduals.block141[12]?=some panel250.right from rfl))⟩
theorem valid251 : ValidPanel panel251 := ⟨modelCheck251,residualCheck251,
  ReferenceTrajectory.leftBlock12_subset (List.mem_of_getElem? (show ReferenceResiduals.block12[11]?=some panel251.left from rfl)),
  ReferenceTrajectory.rightBlock141_subset (List.mem_of_getElem? (show ReferenceResiduals.block141[11]?=some panel251.right from rfl))⟩
theorem valid252 : ValidPanel panel252 := ⟨modelCheck252,residualCheck252,
  ReferenceTrajectory.leftBlock12_subset (List.mem_of_getElem? (show ReferenceResiduals.block12[12]?=some panel252.left from rfl)),
  ReferenceTrajectory.rightBlock141_subset (List.mem_of_getElem? (show ReferenceResiduals.block141[10]?=some panel252.right from rfl))⟩
theorem valid253 : ValidPanel panel253 := ⟨modelCheck253,residualCheck253,
  ReferenceTrajectory.leftBlock12_subset (List.mem_of_getElem? (show ReferenceResiduals.block12[13]?=some panel253.left from rfl)),
  ReferenceTrajectory.rightBlock141_subset (List.mem_of_getElem? (show ReferenceResiduals.block141[9]?=some panel253.right from rfl))⟩
theorem valid254 : ValidPanel panel254 := ⟨modelCheck254,residualCheck254,
  ReferenceTrajectory.leftBlock12_subset (List.mem_of_getElem? (show ReferenceResiduals.block12[14]?=some panel254.left from rfl)),
  ReferenceTrajectory.rightBlock141_subset (List.mem_of_getElem? (show ReferenceResiduals.block141[8]?=some panel254.right from rfl))⟩
theorem valid255 : ValidPanel panel255 := ⟨modelCheck255,residualCheck255,
  ReferenceTrajectory.leftBlock12_subset (List.mem_of_getElem? (show ReferenceResiduals.block12[15]?=some panel255.left from rfl)),
  ReferenceTrajectory.rightBlock141_subset (List.mem_of_getElem? (show ReferenceResiduals.block141[7]?=some panel255.right from rfl))⟩
theorem validBlock7 : ∀ p∈block7,ValidPanel p := by
  simp only [block7,List.forall_mem_cons]
  exact ⟨valid224,⟨valid225,⟨valid226,⟨valid227,⟨valid228,⟨valid229,⟨valid230,⟨valid231,⟨valid232,⟨valid233,⟨valid234,⟨valid235,⟨valid236,⟨valid237,⟨valid238,⟨valid239,⟨valid240,⟨valid241,⟨valid242,⟨valid243,⟨valid244,⟨valid245,⟨valid246,⟨valid247,⟨valid248,⟨valid249,⟨valid250,⟨valid251,⟨valid252,⟨valid253,⟨valid254,⟨valid255,(by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end «2610.05164v2».Certificates.Compact.ContactValues

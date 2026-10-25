import chebyshev2.Certificates.Compact.ContactBatches.Batch012
import chebyshev2.Certificates.Compact.ContactCoverage
import chebyshev2.Certificates.Compact.ReferenceTrajectoryIndex

/-!
Article: chebyshev2, Section 4.1.
Correspondence012.
Use: `chebyshev2.Certificates.Compact.ContactValues.validBlock12` feeds
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
theorem valid384 : ValidPanel panel384 := ⟨modelCheck384,residualCheck384,
  ReferenceTrajectory.leftBlock21_subset (List.mem_of_getElem? (show ReferenceResiduals.block21[0]?=some panel384.left from rfl)),
  ReferenceTrajectory.rightBlock133_subset (List.mem_of_getElem? (show ReferenceResiduals.block133[6]?=some panel384.right from rfl))⟩
theorem valid385 : ValidPanel panel385 := ⟨modelCheck385,residualCheck385,
  ReferenceTrajectory.leftBlock21_subset (List.mem_of_getElem? (show ReferenceResiduals.block21[1]?=some panel385.left from rfl)),
  ReferenceTrajectory.rightBlock133_subset (List.mem_of_getElem? (show ReferenceResiduals.block133[5]?=some panel385.right from rfl))⟩
theorem valid386 : ValidPanel panel386 := ⟨modelCheck386,residualCheck386,
  ReferenceTrajectory.leftBlock21_subset (List.mem_of_getElem? (show ReferenceResiduals.block21[2]?=some panel386.left from rfl)),
  ReferenceTrajectory.rightBlock133_subset (List.mem_of_getElem? (show ReferenceResiduals.block133[4]?=some panel386.right from rfl))⟩
theorem valid387 : ValidPanel panel387 := ⟨modelCheck387,residualCheck387,
  ReferenceTrajectory.leftBlock21_subset (List.mem_of_getElem? (show ReferenceResiduals.block21[3]?=some panel387.left from rfl)),
  ReferenceTrajectory.rightBlock133_subset (List.mem_of_getElem? (show ReferenceResiduals.block133[3]?=some panel387.right from rfl))⟩
theorem valid388 : ValidPanel panel388 := ⟨modelCheck388,residualCheck388,
  ReferenceTrajectory.leftBlock21_subset (List.mem_of_getElem? (show ReferenceResiduals.block21[4]?=some panel388.left from rfl)),
  ReferenceTrajectory.rightBlock133_subset (List.mem_of_getElem? (show ReferenceResiduals.block133[2]?=some panel388.right from rfl))⟩
theorem valid389 : ValidPanel panel389 := ⟨modelCheck389,residualCheck389,
  ReferenceTrajectory.leftBlock21_subset (List.mem_of_getElem? (show ReferenceResiduals.block21[5]?=some panel389.left from rfl)),
  ReferenceTrajectory.rightBlock133_subset (List.mem_of_getElem? (show ReferenceResiduals.block133[1]?=some panel389.right from rfl))⟩
theorem valid390 : ValidPanel panel390 := ⟨modelCheck390,residualCheck390,
  ReferenceTrajectory.leftBlock21_subset (List.mem_of_getElem? (show ReferenceResiduals.block21[6]?=some panel390.left from rfl)),
  ReferenceTrajectory.rightBlock133_subset (List.mem_of_getElem? (show ReferenceResiduals.block133[0]?=some panel390.right from rfl))⟩
theorem valid391 : ValidPanel panel391 := ⟨modelCheck391,residualCheck391,
  ReferenceTrajectory.leftBlock21_subset (List.mem_of_getElem? (show ReferenceResiduals.block21[7]?=some panel391.left from rfl)),
  ReferenceTrajectory.rightBlock132_subset (List.mem_of_getElem? (show ReferenceResiduals.block132[15]?=some panel391.right from rfl))⟩
theorem valid392 : ValidPanel panel392 := ⟨modelCheck392,residualCheck392,
  ReferenceTrajectory.leftBlock21_subset (List.mem_of_getElem? (show ReferenceResiduals.block21[8]?=some panel392.left from rfl)),
  ReferenceTrajectory.rightBlock132_subset (List.mem_of_getElem? (show ReferenceResiduals.block132[14]?=some panel392.right from rfl))⟩
theorem valid393 : ValidPanel panel393 := ⟨modelCheck393,residualCheck393,
  ReferenceTrajectory.leftBlock21_subset (List.mem_of_getElem? (show ReferenceResiduals.block21[9]?=some panel393.left from rfl)),
  ReferenceTrajectory.rightBlock132_subset (List.mem_of_getElem? (show ReferenceResiduals.block132[13]?=some panel393.right from rfl))⟩
theorem valid394 : ValidPanel panel394 := ⟨modelCheck394,residualCheck394,
  ReferenceTrajectory.leftBlock21_subset (List.mem_of_getElem? (show ReferenceResiduals.block21[10]?=some panel394.left from rfl)),
  ReferenceTrajectory.rightBlock132_subset (List.mem_of_getElem? (show ReferenceResiduals.block132[12]?=some panel394.right from rfl))⟩
theorem valid395 : ValidPanel panel395 := ⟨modelCheck395,residualCheck395,
  ReferenceTrajectory.leftBlock21_subset (List.mem_of_getElem? (show ReferenceResiduals.block21[11]?=some panel395.left from rfl)),
  ReferenceTrajectory.rightBlock132_subset (List.mem_of_getElem? (show ReferenceResiduals.block132[11]?=some panel395.right from rfl))⟩
theorem valid396 : ValidPanel panel396 := ⟨modelCheck396,residualCheck396,
  ReferenceTrajectory.leftBlock21_subset (List.mem_of_getElem? (show ReferenceResiduals.block21[12]?=some panel396.left from rfl)),
  ReferenceTrajectory.rightBlock132_subset (List.mem_of_getElem? (show ReferenceResiduals.block132[10]?=some panel396.right from rfl))⟩
theorem valid397 : ValidPanel panel397 := ⟨modelCheck397,residualCheck397,
  ReferenceTrajectory.leftBlock21_subset (List.mem_of_getElem? (show ReferenceResiduals.block21[13]?=some panel397.left from rfl)),
  ReferenceTrajectory.rightBlock132_subset (List.mem_of_getElem? (show ReferenceResiduals.block132[9]?=some panel397.right from rfl))⟩
theorem valid398 : ValidPanel panel398 := ⟨modelCheck398,residualCheck398,
  ReferenceTrajectory.leftBlock21_subset (List.mem_of_getElem? (show ReferenceResiduals.block21[14]?=some panel398.left from rfl)),
  ReferenceTrajectory.rightBlock132_subset (List.mem_of_getElem? (show ReferenceResiduals.block132[8]?=some panel398.right from rfl))⟩
theorem valid399 : ValidPanel panel399 := ⟨modelCheck399,residualCheck399,
  ReferenceTrajectory.leftBlock21_subset (List.mem_of_getElem? (show ReferenceResiduals.block21[15]?=some panel399.left from rfl)),
  ReferenceTrajectory.rightBlock132_subset (List.mem_of_getElem? (show ReferenceResiduals.block132[7]?=some panel399.right from rfl))⟩
theorem valid400 : ValidPanel panel400 := ⟨modelCheck400,residualCheck400,
  ReferenceTrajectory.leftBlock22_subset (List.mem_of_getElem? (show ReferenceResiduals.block22[0]?=some panel400.left from rfl)),
  ReferenceTrajectory.rightBlock132_subset (List.mem_of_getElem? (show ReferenceResiduals.block132[6]?=some panel400.right from rfl))⟩
theorem valid401 : ValidPanel panel401 := ⟨modelCheck401,residualCheck401,
  ReferenceTrajectory.leftBlock22_subset (List.mem_of_getElem? (show ReferenceResiduals.block22[1]?=some panel401.left from rfl)),
  ReferenceTrajectory.rightBlock132_subset (List.mem_of_getElem? (show ReferenceResiduals.block132[5]?=some panel401.right from rfl))⟩
theorem valid402 : ValidPanel panel402 := ⟨modelCheck402,residualCheck402,
  ReferenceTrajectory.leftBlock22_subset (List.mem_of_getElem? (show ReferenceResiduals.block22[2]?=some panel402.left from rfl)),
  ReferenceTrajectory.rightBlock132_subset (List.mem_of_getElem? (show ReferenceResiduals.block132[4]?=some panel402.right from rfl))⟩
theorem valid403 : ValidPanel panel403 := ⟨modelCheck403,residualCheck403,
  ReferenceTrajectory.leftBlock22_subset (List.mem_of_getElem? (show ReferenceResiduals.block22[3]?=some panel403.left from rfl)),
  ReferenceTrajectory.rightBlock132_subset (List.mem_of_getElem? (show ReferenceResiduals.block132[3]?=some panel403.right from rfl))⟩
theorem valid404 : ValidPanel panel404 := ⟨modelCheck404,residualCheck404,
  ReferenceTrajectory.leftBlock22_subset (List.mem_of_getElem? (show ReferenceResiduals.block22[4]?=some panel404.left from rfl)),
  ReferenceTrajectory.rightBlock132_subset (List.mem_of_getElem? (show ReferenceResiduals.block132[2]?=some panel404.right from rfl))⟩
theorem valid405 : ValidPanel panel405 := ⟨modelCheck405,residualCheck405,
  ReferenceTrajectory.leftBlock22_subset (List.mem_of_getElem? (show ReferenceResiduals.block22[5]?=some panel405.left from rfl)),
  ReferenceTrajectory.rightBlock132_subset (List.mem_of_getElem? (show ReferenceResiduals.block132[1]?=some panel405.right from rfl))⟩
theorem valid406 : ValidPanel panel406 := ⟨modelCheck406,residualCheck406,
  ReferenceTrajectory.leftBlock22_subset (List.mem_of_getElem? (show ReferenceResiduals.block22[6]?=some panel406.left from rfl)),
  ReferenceTrajectory.rightBlock132_subset (List.mem_of_getElem? (show ReferenceResiduals.block132[0]?=some panel406.right from rfl))⟩
theorem valid407 : ValidPanel panel407 := ⟨modelCheck407,residualCheck407,
  ReferenceTrajectory.leftBlock22_subset (List.mem_of_getElem? (show ReferenceResiduals.block22[7]?=some panel407.left from rfl)),
  ReferenceTrajectory.rightBlock131_subset (List.mem_of_getElem? (show ReferenceResiduals.block131[15]?=some panel407.right from rfl))⟩
theorem valid408 : ValidPanel panel408 := ⟨modelCheck408,residualCheck408,
  ReferenceTrajectory.leftBlock22_subset (List.mem_of_getElem? (show ReferenceResiduals.block22[8]?=some panel408.left from rfl)),
  ReferenceTrajectory.rightBlock131_subset (List.mem_of_getElem? (show ReferenceResiduals.block131[14]?=some panel408.right from rfl))⟩
theorem valid409 : ValidPanel panel409 := ⟨modelCheck409,residualCheck409,
  ReferenceTrajectory.leftBlock22_subset (List.mem_of_getElem? (show ReferenceResiduals.block22[9]?=some panel409.left from rfl)),
  ReferenceTrajectory.rightBlock131_subset (List.mem_of_getElem? (show ReferenceResiduals.block131[13]?=some panel409.right from rfl))⟩
theorem valid410 : ValidPanel panel410 := ⟨modelCheck410,residualCheck410,
  ReferenceTrajectory.leftBlock22_subset (List.mem_of_getElem? (show ReferenceResiduals.block22[10]?=some panel410.left from rfl)),
  ReferenceTrajectory.rightBlock131_subset (List.mem_of_getElem? (show ReferenceResiduals.block131[12]?=some panel410.right from rfl))⟩
theorem valid411 : ValidPanel panel411 := ⟨modelCheck411,residualCheck411,
  ReferenceTrajectory.leftBlock22_subset (List.mem_of_getElem? (show ReferenceResiduals.block22[11]?=some panel411.left from rfl)),
  ReferenceTrajectory.rightBlock131_subset (List.mem_of_getElem? (show ReferenceResiduals.block131[11]?=some panel411.right from rfl))⟩
theorem valid412 : ValidPanel panel412 := ⟨modelCheck412,residualCheck412,
  ReferenceTrajectory.leftBlock22_subset (List.mem_of_getElem? (show ReferenceResiduals.block22[12]?=some panel412.left from rfl)),
  ReferenceTrajectory.rightBlock131_subset (List.mem_of_getElem? (show ReferenceResiduals.block131[10]?=some panel412.right from rfl))⟩
theorem valid413 : ValidPanel panel413 := ⟨modelCheck413,residualCheck413,
  ReferenceTrajectory.leftBlock22_subset (List.mem_of_getElem? (show ReferenceResiduals.block22[13]?=some panel413.left from rfl)),
  ReferenceTrajectory.rightBlock131_subset (List.mem_of_getElem? (show ReferenceResiduals.block131[9]?=some panel413.right from rfl))⟩
theorem valid414 : ValidPanel panel414 := ⟨modelCheck414,residualCheck414,
  ReferenceTrajectory.leftBlock22_subset (List.mem_of_getElem? (show ReferenceResiduals.block22[14]?=some panel414.left from rfl)),
  ReferenceTrajectory.rightBlock131_subset (List.mem_of_getElem? (show ReferenceResiduals.block131[8]?=some panel414.right from rfl))⟩
theorem valid415 : ValidPanel panel415 := ⟨modelCheck415,residualCheck415,
  ReferenceTrajectory.leftBlock22_subset (List.mem_of_getElem? (show ReferenceResiduals.block22[15]?=some panel415.left from rfl)),
  ReferenceTrajectory.rightBlock131_subset (List.mem_of_getElem? (show ReferenceResiduals.block131[7]?=some panel415.right from rfl))⟩
theorem validBlock12 : ∀ p∈block12,ValidPanel p := by
  simp only [block12,List.forall_mem_cons]
  exact ⟨valid384,⟨valid385,⟨valid386,⟨valid387,⟨valid388,⟨valid389,⟨valid390,⟨valid391,⟨valid392,⟨valid393,⟨valid394,⟨valid395,⟨valid396,⟨valid397,⟨valid398,⟨valid399,⟨valid400,⟨valid401,⟨valid402,⟨valid403,⟨valid404,⟨valid405,⟨valid406,⟨valid407,⟨valid408,⟨valid409,⟨valid410,⟨valid411,⟨valid412,⟨valid413,⟨valid414,⟨valid415,(by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end chebyshev2.Certificates.Compact.ContactValues

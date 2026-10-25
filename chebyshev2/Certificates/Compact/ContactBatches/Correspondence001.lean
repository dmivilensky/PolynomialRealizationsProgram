import chebyshev2.Certificates.Compact.ContactBatches.Batch001
import chebyshev2.Certificates.Compact.ContactCoverage
import chebyshev2.Certificates.Compact.ReferenceTrajectoryIndex

/-!
Article: chebyshev2, Section 4.1.
Correspondence001.
Use: `chebyshev2.Certificates.Compact.ContactValues.validBlock1` feeds
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
theorem valid32 : ValidPanel panel32 := ⟨modelCheck32,residualCheck32,
  ReferenceTrajectory.leftBlock1_subset (List.mem_of_getElem? (show ReferenceResiduals.block1[15]?=some panel32.left from rfl)),
  ReferenceTrajectory.rightBlock155_subset (List.mem_of_getElem? (show ReferenceResiduals.block155[6]?=some panel32.right from rfl))⟩
theorem valid33 : ValidPanel panel33 := ⟨modelCheck33,residualCheck33,
  ReferenceTrajectory.leftBlock2_subset (List.mem_of_getElem? (show ReferenceResiduals.block2[0]?=some panel33.left from rfl)),
  ReferenceTrajectory.rightBlock155_subset (List.mem_of_getElem? (show ReferenceResiduals.block155[5]?=some panel33.right from rfl))⟩
theorem valid34 : ValidPanel panel34 := ⟨modelCheck34,residualCheck34,
  ReferenceTrajectory.leftBlock2_subset (List.mem_of_getElem? (show ReferenceResiduals.block2[1]?=some panel34.left from rfl)),
  ReferenceTrajectory.rightBlock155_subset (List.mem_of_getElem? (show ReferenceResiduals.block155[4]?=some panel34.right from rfl))⟩
theorem valid35 : ValidPanel panel35 := ⟨modelCheck35,residualCheck35,
  ReferenceTrajectory.leftBlock2_subset (List.mem_of_getElem? (show ReferenceResiduals.block2[2]?=some panel35.left from rfl)),
  ReferenceTrajectory.rightBlock155_subset (List.mem_of_getElem? (show ReferenceResiduals.block155[3]?=some panel35.right from rfl))⟩
theorem valid36 : ValidPanel panel36 := ⟨modelCheck36,residualCheck36,
  ReferenceTrajectory.leftBlock2_subset (List.mem_of_getElem? (show ReferenceResiduals.block2[3]?=some panel36.left from rfl)),
  ReferenceTrajectory.rightBlock155_subset (List.mem_of_getElem? (show ReferenceResiduals.block155[2]?=some panel36.right from rfl))⟩
theorem valid37 : ValidPanel panel37 := ⟨modelCheck37,residualCheck37,
  ReferenceTrajectory.leftBlock2_subset (List.mem_of_getElem? (show ReferenceResiduals.block2[4]?=some panel37.left from rfl)),
  ReferenceTrajectory.rightBlock155_subset (List.mem_of_getElem? (show ReferenceResiduals.block155[1]?=some panel37.right from rfl))⟩
theorem valid38 : ValidPanel panel38 := ⟨modelCheck38,residualCheck38,
  ReferenceTrajectory.leftBlock2_subset (List.mem_of_getElem? (show ReferenceResiduals.block2[4]?=some panel38.left from rfl)),
  ReferenceTrajectory.rightBlock155_subset (List.mem_of_getElem? (show ReferenceResiduals.block155[0]?=some panel38.right from rfl))⟩
theorem valid39 : ValidPanel panel39 := ⟨modelCheck39,residualCheck39,
  ReferenceTrajectory.leftBlock2_subset (List.mem_of_getElem? (show ReferenceResiduals.block2[5]?=some panel39.left from rfl)),
  ReferenceTrajectory.rightBlock154_subset (List.mem_of_getElem? (show ReferenceResiduals.block154[15]?=some panel39.right from rfl))⟩
theorem valid40 : ValidPanel panel40 := ⟨modelCheck40,residualCheck40,
  ReferenceTrajectory.leftBlock2_subset (List.mem_of_getElem? (show ReferenceResiduals.block2[5]?=some panel40.left from rfl)),
  ReferenceTrajectory.rightBlock154_subset (List.mem_of_getElem? (show ReferenceResiduals.block154[14]?=some panel40.right from rfl))⟩
theorem valid41 : ValidPanel panel41 := ⟨modelCheck41,residualCheck41,
  ReferenceTrajectory.leftBlock2_subset (List.mem_of_getElem? (show ReferenceResiduals.block2[6]?=some panel41.left from rfl)),
  ReferenceTrajectory.rightBlock154_subset (List.mem_of_getElem? (show ReferenceResiduals.block154[13]?=some panel41.right from rfl))⟩
theorem valid42 : ValidPanel panel42 := ⟨modelCheck42,residualCheck42,
  ReferenceTrajectory.leftBlock2_subset (List.mem_of_getElem? (show ReferenceResiduals.block2[6]?=some panel42.left from rfl)),
  ReferenceTrajectory.rightBlock154_subset (List.mem_of_getElem? (show ReferenceResiduals.block154[12]?=some panel42.right from rfl))⟩
theorem valid43 : ValidPanel panel43 := ⟨modelCheck43,residualCheck43,
  ReferenceTrajectory.leftBlock2_subset (List.mem_of_getElem? (show ReferenceResiduals.block2[7]?=some panel43.left from rfl)),
  ReferenceTrajectory.rightBlock154_subset (List.mem_of_getElem? (show ReferenceResiduals.block154[11]?=some panel43.right from rfl))⟩
theorem valid44 : ValidPanel panel44 := ⟨modelCheck44,residualCheck44,
  ReferenceTrajectory.leftBlock2_subset (List.mem_of_getElem? (show ReferenceResiduals.block2[7]?=some panel44.left from rfl)),
  ReferenceTrajectory.rightBlock154_subset (List.mem_of_getElem? (show ReferenceResiduals.block154[10]?=some panel44.right from rfl))⟩
theorem valid45 : ValidPanel panel45 := ⟨modelCheck45,residualCheck45,
  ReferenceTrajectory.leftBlock2_subset (List.mem_of_getElem? (show ReferenceResiduals.block2[8]?=some panel45.left from rfl)),
  ReferenceTrajectory.rightBlock154_subset (List.mem_of_getElem? (show ReferenceResiduals.block154[9]?=some panel45.right from rfl))⟩
theorem valid46 : ValidPanel panel46 := ⟨modelCheck46,residualCheck46,
  ReferenceTrajectory.leftBlock2_subset (List.mem_of_getElem? (show ReferenceResiduals.block2[8]?=some panel46.left from rfl)),
  ReferenceTrajectory.rightBlock154_subset (List.mem_of_getElem? (show ReferenceResiduals.block154[8]?=some panel46.right from rfl))⟩
theorem valid47 : ValidPanel panel47 := ⟨modelCheck47,residualCheck47,
  ReferenceTrajectory.leftBlock2_subset (List.mem_of_getElem? (show ReferenceResiduals.block2[9]?=some panel47.left from rfl)),
  ReferenceTrajectory.rightBlock154_subset (List.mem_of_getElem? (show ReferenceResiduals.block154[7]?=some panel47.right from rfl))⟩
theorem valid48 : ValidPanel panel48 := ⟨modelCheck48,residualCheck48,
  ReferenceTrajectory.leftBlock2_subset (List.mem_of_getElem? (show ReferenceResiduals.block2[9]?=some panel48.left from rfl)),
  ReferenceTrajectory.rightBlock154_subset (List.mem_of_getElem? (show ReferenceResiduals.block154[6]?=some panel48.right from rfl))⟩
theorem valid49 : ValidPanel panel49 := ⟨modelCheck49,residualCheck49,
  ReferenceTrajectory.leftBlock2_subset (List.mem_of_getElem? (show ReferenceResiduals.block2[10]?=some panel49.left from rfl)),
  ReferenceTrajectory.rightBlock154_subset (List.mem_of_getElem? (show ReferenceResiduals.block154[5]?=some panel49.right from rfl))⟩
theorem valid50 : ValidPanel panel50 := ⟨modelCheck50,residualCheck50,
  ReferenceTrajectory.leftBlock2_subset (List.mem_of_getElem? (show ReferenceResiduals.block2[10]?=some panel50.left from rfl)),
  ReferenceTrajectory.rightBlock154_subset (List.mem_of_getElem? (show ReferenceResiduals.block154[4]?=some panel50.right from rfl))⟩
theorem valid51 : ValidPanel panel51 := ⟨modelCheck51,residualCheck51,
  ReferenceTrajectory.leftBlock2_subset (List.mem_of_getElem? (show ReferenceResiduals.block2[11]?=some panel51.left from rfl)),
  ReferenceTrajectory.rightBlock154_subset (List.mem_of_getElem? (show ReferenceResiduals.block154[3]?=some panel51.right from rfl))⟩
theorem valid52 : ValidPanel panel52 := ⟨modelCheck52,residualCheck52,
  ReferenceTrajectory.leftBlock2_subset (List.mem_of_getElem? (show ReferenceResiduals.block2[11]?=some panel52.left from rfl)),
  ReferenceTrajectory.rightBlock154_subset (List.mem_of_getElem? (show ReferenceResiduals.block154[2]?=some panel52.right from rfl))⟩
theorem valid53 : ValidPanel panel53 := ⟨modelCheck53,residualCheck53,
  ReferenceTrajectory.leftBlock2_subset (List.mem_of_getElem? (show ReferenceResiduals.block2[12]?=some panel53.left from rfl)),
  ReferenceTrajectory.rightBlock154_subset (List.mem_of_getElem? (show ReferenceResiduals.block154[1]?=some panel53.right from rfl))⟩
theorem valid54 : ValidPanel panel54 := ⟨modelCheck54,residualCheck54,
  ReferenceTrajectory.leftBlock2_subset (List.mem_of_getElem? (show ReferenceResiduals.block2[12]?=some panel54.left from rfl)),
  ReferenceTrajectory.rightBlock154_subset (List.mem_of_getElem? (show ReferenceResiduals.block154[0]?=some panel54.right from rfl))⟩
theorem valid55 : ValidPanel panel55 := ⟨modelCheck55,residualCheck55,
  ReferenceTrajectory.leftBlock2_subset (List.mem_of_getElem? (show ReferenceResiduals.block2[13]?=some panel55.left from rfl)),
  ReferenceTrajectory.rightBlock153_subset (List.mem_of_getElem? (show ReferenceResiduals.block153[15]?=some panel55.right from rfl))⟩
theorem valid56 : ValidPanel panel56 := ⟨modelCheck56,residualCheck56,
  ReferenceTrajectory.leftBlock2_subset (List.mem_of_getElem? (show ReferenceResiduals.block2[13]?=some panel56.left from rfl)),
  ReferenceTrajectory.rightBlock153_subset (List.mem_of_getElem? (show ReferenceResiduals.block153[14]?=some panel56.right from rfl))⟩
theorem valid57 : ValidPanel panel57 := ⟨modelCheck57,residualCheck57,
  ReferenceTrajectory.leftBlock2_subset (List.mem_of_getElem? (show ReferenceResiduals.block2[14]?=some panel57.left from rfl)),
  ReferenceTrajectory.rightBlock153_subset (List.mem_of_getElem? (show ReferenceResiduals.block153[13]?=some panel57.right from rfl))⟩
theorem valid58 : ValidPanel panel58 := ⟨modelCheck58,residualCheck58,
  ReferenceTrajectory.leftBlock2_subset (List.mem_of_getElem? (show ReferenceResiduals.block2[14]?=some panel58.left from rfl)),
  ReferenceTrajectory.rightBlock153_subset (List.mem_of_getElem? (show ReferenceResiduals.block153[12]?=some panel58.right from rfl))⟩
theorem valid59 : ValidPanel panel59 := ⟨modelCheck59,residualCheck59,
  ReferenceTrajectory.leftBlock2_subset (List.mem_of_getElem? (show ReferenceResiduals.block2[15]?=some panel59.left from rfl)),
  ReferenceTrajectory.rightBlock153_subset (List.mem_of_getElem? (show ReferenceResiduals.block153[11]?=some panel59.right from rfl))⟩
theorem valid60 : ValidPanel panel60 := ⟨modelCheck60,residualCheck60,
  ReferenceTrajectory.leftBlock2_subset (List.mem_of_getElem? (show ReferenceResiduals.block2[15]?=some panel60.left from rfl)),
  ReferenceTrajectory.rightBlock153_subset (List.mem_of_getElem? (show ReferenceResiduals.block153[10]?=some panel60.right from rfl))⟩
theorem valid61 : ValidPanel panel61 := ⟨modelCheck61,residualCheck61,
  ReferenceTrajectory.leftBlock3_subset (List.mem_of_getElem? (show ReferenceResiduals.block3[0]?=some panel61.left from rfl)),
  ReferenceTrajectory.rightBlock153_subset (List.mem_of_getElem? (show ReferenceResiduals.block153[9]?=some panel61.right from rfl))⟩
theorem valid62 : ValidPanel panel62 := ⟨modelCheck62,residualCheck62,
  ReferenceTrajectory.leftBlock3_subset (List.mem_of_getElem? (show ReferenceResiduals.block3[0]?=some panel62.left from rfl)),
  ReferenceTrajectory.rightBlock153_subset (List.mem_of_getElem? (show ReferenceResiduals.block153[8]?=some panel62.right from rfl))⟩
theorem valid63 : ValidPanel panel63 := ⟨modelCheck63,residualCheck63,
  ReferenceTrajectory.leftBlock3_subset (List.mem_of_getElem? (show ReferenceResiduals.block3[1]?=some panel63.left from rfl)),
  ReferenceTrajectory.rightBlock153_subset (List.mem_of_getElem? (show ReferenceResiduals.block153[7]?=some panel63.right from rfl))⟩
theorem validBlock1 : ∀ p∈block1,ValidPanel p := by
  simp only [block1,List.forall_mem_cons]
  exact ⟨valid32,⟨valid33,⟨valid34,⟨valid35,⟨valid36,⟨valid37,⟨valid38,⟨valid39,⟨valid40,⟨valid41,⟨valid42,⟨valid43,⟨valid44,⟨valid45,⟨valid46,⟨valid47,⟨valid48,⟨valid49,⟨valid50,⟨valid51,⟨valid52,⟨valid53,⟨valid54,⟨valid55,⟨valid56,⟨valid57,⟨valid58,⟨valid59,⟨valid60,⟨valid61,⟨valid62,⟨valid63,(by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end chebyshev2.Certificates.Compact.ContactValues

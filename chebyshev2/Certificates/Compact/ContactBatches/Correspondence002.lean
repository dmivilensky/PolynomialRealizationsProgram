import chebyshev2.Certificates.Compact.ContactBatches.Batch002
import chebyshev2.Certificates.Compact.ContactCoverage
import chebyshev2.Certificates.Compact.ReferenceTrajectoryIndex

/-!
Article: chebyshev2, Section 4.1.
Correspondence002.
Use: `chebyshev2.Certificates.Compact.ContactValues.validBlock2` feeds
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
theorem valid64 : ValidPanel panel64 := ⟨modelCheck64,residualCheck64,
  ReferenceTrajectory.leftBlock3_subset (List.mem_of_getElem? (show ReferenceResiduals.block3[1]?=some panel64.left from rfl)),
  ReferenceTrajectory.rightBlock153_subset (List.mem_of_getElem? (show ReferenceResiduals.block153[6]?=some panel64.right from rfl))⟩
theorem valid65 : ValidPanel panel65 := ⟨modelCheck65,residualCheck65,
  ReferenceTrajectory.leftBlock3_subset (List.mem_of_getElem? (show ReferenceResiduals.block3[2]?=some panel65.left from rfl)),
  ReferenceTrajectory.rightBlock153_subset (List.mem_of_getElem? (show ReferenceResiduals.block153[5]?=some panel65.right from rfl))⟩
theorem valid66 : ValidPanel panel66 := ⟨modelCheck66,residualCheck66,
  ReferenceTrajectory.leftBlock3_subset (List.mem_of_getElem? (show ReferenceResiduals.block3[2]?=some panel66.left from rfl)),
  ReferenceTrajectory.rightBlock153_subset (List.mem_of_getElem? (show ReferenceResiduals.block153[4]?=some panel66.right from rfl))⟩
theorem valid67 : ValidPanel panel67 := ⟨modelCheck67,residualCheck67,
  ReferenceTrajectory.leftBlock3_subset (List.mem_of_getElem? (show ReferenceResiduals.block3[3]?=some panel67.left from rfl)),
  ReferenceTrajectory.rightBlock153_subset (List.mem_of_getElem? (show ReferenceResiduals.block153[3]?=some panel67.right from rfl))⟩
theorem valid68 : ValidPanel panel68 := ⟨modelCheck68,residualCheck68,
  ReferenceTrajectory.leftBlock3_subset (List.mem_of_getElem? (show ReferenceResiduals.block3[3]?=some panel68.left from rfl)),
  ReferenceTrajectory.rightBlock153_subset (List.mem_of_getElem? (show ReferenceResiduals.block153[2]?=some panel68.right from rfl))⟩
theorem valid69 : ValidPanel panel69 := ⟨modelCheck69,residualCheck69,
  ReferenceTrajectory.leftBlock3_subset (List.mem_of_getElem? (show ReferenceResiduals.block3[4]?=some panel69.left from rfl)),
  ReferenceTrajectory.rightBlock153_subset (List.mem_of_getElem? (show ReferenceResiduals.block153[1]?=some panel69.right from rfl))⟩
theorem valid70 : ValidPanel panel70 := ⟨modelCheck70,residualCheck70,
  ReferenceTrajectory.leftBlock3_subset (List.mem_of_getElem? (show ReferenceResiduals.block3[4]?=some panel70.left from rfl)),
  ReferenceTrajectory.rightBlock153_subset (List.mem_of_getElem? (show ReferenceResiduals.block153[0]?=some panel70.right from rfl))⟩
theorem valid71 : ValidPanel panel71 := ⟨modelCheck71,residualCheck71,
  ReferenceTrajectory.leftBlock3_subset (List.mem_of_getElem? (show ReferenceResiduals.block3[5]?=some panel71.left from rfl)),
  ReferenceTrajectory.rightBlock152_subset (List.mem_of_getElem? (show ReferenceResiduals.block152[15]?=some panel71.right from rfl))⟩
theorem valid72 : ValidPanel panel72 := ⟨modelCheck72,residualCheck72,
  ReferenceTrajectory.leftBlock3_subset (List.mem_of_getElem? (show ReferenceResiduals.block3[5]?=some panel72.left from rfl)),
  ReferenceTrajectory.rightBlock152_subset (List.mem_of_getElem? (show ReferenceResiduals.block152[14]?=some panel72.right from rfl))⟩
theorem valid73 : ValidPanel panel73 := ⟨modelCheck73,residualCheck73,
  ReferenceTrajectory.leftBlock3_subset (List.mem_of_getElem? (show ReferenceResiduals.block3[6]?=some panel73.left from rfl)),
  ReferenceTrajectory.rightBlock152_subset (List.mem_of_getElem? (show ReferenceResiduals.block152[13]?=some panel73.right from rfl))⟩
theorem valid74 : ValidPanel panel74 := ⟨modelCheck74,residualCheck74,
  ReferenceTrajectory.leftBlock3_subset (List.mem_of_getElem? (show ReferenceResiduals.block3[6]?=some panel74.left from rfl)),
  ReferenceTrajectory.rightBlock152_subset (List.mem_of_getElem? (show ReferenceResiduals.block152[12]?=some panel74.right from rfl))⟩
theorem valid75 : ValidPanel panel75 := ⟨modelCheck75,residualCheck75,
  ReferenceTrajectory.leftBlock3_subset (List.mem_of_getElem? (show ReferenceResiduals.block3[7]?=some panel75.left from rfl)),
  ReferenceTrajectory.rightBlock152_subset (List.mem_of_getElem? (show ReferenceResiduals.block152[11]?=some panel75.right from rfl))⟩
theorem valid76 : ValidPanel panel76 := ⟨modelCheck76,residualCheck76,
  ReferenceTrajectory.leftBlock3_subset (List.mem_of_getElem? (show ReferenceResiduals.block3[7]?=some panel76.left from rfl)),
  ReferenceTrajectory.rightBlock152_subset (List.mem_of_getElem? (show ReferenceResiduals.block152[10]?=some panel76.right from rfl))⟩
theorem valid77 : ValidPanel panel77 := ⟨modelCheck77,residualCheck77,
  ReferenceTrajectory.leftBlock3_subset (List.mem_of_getElem? (show ReferenceResiduals.block3[8]?=some panel77.left from rfl)),
  ReferenceTrajectory.rightBlock152_subset (List.mem_of_getElem? (show ReferenceResiduals.block152[9]?=some panel77.right from rfl))⟩
theorem valid78 : ValidPanel panel78 := ⟨modelCheck78,residualCheck78,
  ReferenceTrajectory.leftBlock3_subset (List.mem_of_getElem? (show ReferenceResiduals.block3[8]?=some panel78.left from rfl)),
  ReferenceTrajectory.rightBlock152_subset (List.mem_of_getElem? (show ReferenceResiduals.block152[8]?=some panel78.right from rfl))⟩
theorem valid79 : ValidPanel panel79 := ⟨modelCheck79,residualCheck79,
  ReferenceTrajectory.leftBlock3_subset (List.mem_of_getElem? (show ReferenceResiduals.block3[9]?=some panel79.left from rfl)),
  ReferenceTrajectory.rightBlock152_subset (List.mem_of_getElem? (show ReferenceResiduals.block152[7]?=some panel79.right from rfl))⟩
theorem valid80 : ValidPanel panel80 := ⟨modelCheck80,residualCheck80,
  ReferenceTrajectory.leftBlock3_subset (List.mem_of_getElem? (show ReferenceResiduals.block3[9]?=some panel80.left from rfl)),
  ReferenceTrajectory.rightBlock152_subset (List.mem_of_getElem? (show ReferenceResiduals.block152[6]?=some panel80.right from rfl))⟩
theorem valid81 : ValidPanel panel81 := ⟨modelCheck81,residualCheck81,
  ReferenceTrajectory.leftBlock3_subset (List.mem_of_getElem? (show ReferenceResiduals.block3[10]?=some panel81.left from rfl)),
  ReferenceTrajectory.rightBlock152_subset (List.mem_of_getElem? (show ReferenceResiduals.block152[5]?=some panel81.right from rfl))⟩
theorem valid82 : ValidPanel panel82 := ⟨modelCheck82,residualCheck82,
  ReferenceTrajectory.leftBlock3_subset (List.mem_of_getElem? (show ReferenceResiduals.block3[10]?=some panel82.left from rfl)),
  ReferenceTrajectory.rightBlock152_subset (List.mem_of_getElem? (show ReferenceResiduals.block152[4]?=some panel82.right from rfl))⟩
theorem valid83 : ValidPanel panel83 := ⟨modelCheck83,residualCheck83,
  ReferenceTrajectory.leftBlock3_subset (List.mem_of_getElem? (show ReferenceResiduals.block3[11]?=some panel83.left from rfl)),
  ReferenceTrajectory.rightBlock152_subset (List.mem_of_getElem? (show ReferenceResiduals.block152[3]?=some panel83.right from rfl))⟩
theorem valid84 : ValidPanel panel84 := ⟨modelCheck84,residualCheck84,
  ReferenceTrajectory.leftBlock3_subset (List.mem_of_getElem? (show ReferenceResiduals.block3[11]?=some panel84.left from rfl)),
  ReferenceTrajectory.rightBlock152_subset (List.mem_of_getElem? (show ReferenceResiduals.block152[2]?=some panel84.right from rfl))⟩
theorem valid85 : ValidPanel panel85 := ⟨modelCheck85,residualCheck85,
  ReferenceTrajectory.leftBlock3_subset (List.mem_of_getElem? (show ReferenceResiduals.block3[12]?=some panel85.left from rfl)),
  ReferenceTrajectory.rightBlock152_subset (List.mem_of_getElem? (show ReferenceResiduals.block152[1]?=some panel85.right from rfl))⟩
theorem valid86 : ValidPanel panel86 := ⟨modelCheck86,residualCheck86,
  ReferenceTrajectory.leftBlock3_subset (List.mem_of_getElem? (show ReferenceResiduals.block3[12]?=some panel86.left from rfl)),
  ReferenceTrajectory.rightBlock152_subset (List.mem_of_getElem? (show ReferenceResiduals.block152[0]?=some panel86.right from rfl))⟩
theorem valid87 : ValidPanel panel87 := ⟨modelCheck87,residualCheck87,
  ReferenceTrajectory.leftBlock3_subset (List.mem_of_getElem? (show ReferenceResiduals.block3[13]?=some panel87.left from rfl)),
  ReferenceTrajectory.rightBlock151_subset (List.mem_of_getElem? (show ReferenceResiduals.block151[15]?=some panel87.right from rfl))⟩
theorem valid88 : ValidPanel panel88 := ⟨modelCheck88,residualCheck88,
  ReferenceTrajectory.leftBlock3_subset (List.mem_of_getElem? (show ReferenceResiduals.block3[13]?=some panel88.left from rfl)),
  ReferenceTrajectory.rightBlock151_subset (List.mem_of_getElem? (show ReferenceResiduals.block151[14]?=some panel88.right from rfl))⟩
theorem valid89 : ValidPanel panel89 := ⟨modelCheck89,residualCheck89,
  ReferenceTrajectory.leftBlock3_subset (List.mem_of_getElem? (show ReferenceResiduals.block3[14]?=some panel89.left from rfl)),
  ReferenceTrajectory.rightBlock151_subset (List.mem_of_getElem? (show ReferenceResiduals.block151[13]?=some panel89.right from rfl))⟩
theorem valid90 : ValidPanel panel90 := ⟨modelCheck90,residualCheck90,
  ReferenceTrajectory.leftBlock3_subset (List.mem_of_getElem? (show ReferenceResiduals.block3[14]?=some panel90.left from rfl)),
  ReferenceTrajectory.rightBlock151_subset (List.mem_of_getElem? (show ReferenceResiduals.block151[12]?=some panel90.right from rfl))⟩
theorem valid91 : ValidPanel panel91 := ⟨modelCheck91,residualCheck91,
  ReferenceTrajectory.leftBlock3_subset (List.mem_of_getElem? (show ReferenceResiduals.block3[15]?=some panel91.left from rfl)),
  ReferenceTrajectory.rightBlock151_subset (List.mem_of_getElem? (show ReferenceResiduals.block151[11]?=some panel91.right from rfl))⟩
theorem valid92 : ValidPanel panel92 := ⟨modelCheck92,residualCheck92,
  ReferenceTrajectory.leftBlock3_subset (List.mem_of_getElem? (show ReferenceResiduals.block3[15]?=some panel92.left from rfl)),
  ReferenceTrajectory.rightBlock151_subset (List.mem_of_getElem? (show ReferenceResiduals.block151[10]?=some panel92.right from rfl))⟩
theorem valid93 : ValidPanel panel93 := ⟨modelCheck93,residualCheck93,
  ReferenceTrajectory.leftBlock4_subset (List.mem_of_getElem? (show ReferenceResiduals.block4[0]?=some panel93.left from rfl)),
  ReferenceTrajectory.rightBlock151_subset (List.mem_of_getElem? (show ReferenceResiduals.block151[9]?=some panel93.right from rfl))⟩
theorem valid94 : ValidPanel panel94 := ⟨modelCheck94,residualCheck94,
  ReferenceTrajectory.leftBlock4_subset (List.mem_of_getElem? (show ReferenceResiduals.block4[0]?=some panel94.left from rfl)),
  ReferenceTrajectory.rightBlock151_subset (List.mem_of_getElem? (show ReferenceResiduals.block151[8]?=some panel94.right from rfl))⟩
theorem valid95 : ValidPanel panel95 := ⟨modelCheck95,residualCheck95,
  ReferenceTrajectory.leftBlock4_subset (List.mem_of_getElem? (show ReferenceResiduals.block4[1]?=some panel95.left from rfl)),
  ReferenceTrajectory.rightBlock151_subset (List.mem_of_getElem? (show ReferenceResiduals.block151[7]?=some panel95.right from rfl))⟩
theorem validBlock2 : ∀ p∈block2,ValidPanel p := by
  simp only [block2,List.forall_mem_cons]
  exact ⟨valid64,⟨valid65,⟨valid66,⟨valid67,⟨valid68,⟨valid69,⟨valid70,⟨valid71,⟨valid72,⟨valid73,⟨valid74,⟨valid75,⟨valid76,⟨valid77,⟨valid78,⟨valid79,⟨valid80,⟨valid81,⟨valid82,⟨valid83,⟨valid84,⟨valid85,⟨valid86,⟨valid87,⟨valid88,⟨valid89,⟨valid90,⟨valid91,⟨valid92,⟨valid93,⟨valid94,⟨valid95,(by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end chebyshev2.Certificates.Compact.ContactValues

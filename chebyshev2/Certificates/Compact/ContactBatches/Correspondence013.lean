import chebyshev2.Certificates.Compact.ContactBatches.Batch013
import chebyshev2.Certificates.Compact.ContactCoverage
import chebyshev2.Certificates.Compact.ReferenceTrajectoryIndex

/-!
Article: chebyshev2, Section 4.1.
Correspondence013.
Use: `chebyshev2.Certificates.Compact.ContactValues.validBlock13` feeds
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
theorem valid416 : ValidPanel panel416 := ⟨modelCheck416,residualCheck416,
  ReferenceTrajectory.leftBlock23_subset (List.mem_of_getElem? (show ReferenceResiduals.block23[0]?=some panel416.left from rfl)),
  ReferenceTrajectory.rightBlock131_subset (List.mem_of_getElem? (show ReferenceResiduals.block131[6]?=some panel416.right from rfl))⟩
theorem valid417 : ValidPanel panel417 := ⟨modelCheck417,residualCheck417,
  ReferenceTrajectory.leftBlock23_subset (List.mem_of_getElem? (show ReferenceResiduals.block23[1]?=some panel417.left from rfl)),
  ReferenceTrajectory.rightBlock131_subset (List.mem_of_getElem? (show ReferenceResiduals.block131[5]?=some panel417.right from rfl))⟩
theorem valid418 : ValidPanel panel418 := ⟨modelCheck418,residualCheck418,
  ReferenceTrajectory.leftBlock23_subset (List.mem_of_getElem? (show ReferenceResiduals.block23[2]?=some panel418.left from rfl)),
  ReferenceTrajectory.rightBlock131_subset (List.mem_of_getElem? (show ReferenceResiduals.block131[4]?=some panel418.right from rfl))⟩
theorem valid419 : ValidPanel panel419 := ⟨modelCheck419,residualCheck419,
  ReferenceTrajectory.leftBlock23_subset (List.mem_of_getElem? (show ReferenceResiduals.block23[3]?=some panel419.left from rfl)),
  ReferenceTrajectory.rightBlock131_subset (List.mem_of_getElem? (show ReferenceResiduals.block131[3]?=some panel419.right from rfl))⟩
theorem valid420 : ValidPanel panel420 := ⟨modelCheck420,residualCheck420,
  ReferenceTrajectory.leftBlock23_subset (List.mem_of_getElem? (show ReferenceResiduals.block23[4]?=some panel420.left from rfl)),
  ReferenceTrajectory.rightBlock131_subset (List.mem_of_getElem? (show ReferenceResiduals.block131[2]?=some panel420.right from rfl))⟩
theorem valid421 : ValidPanel panel421 := ⟨modelCheck421,residualCheck421,
  ReferenceTrajectory.leftBlock23_subset (List.mem_of_getElem? (show ReferenceResiduals.block23[5]?=some panel421.left from rfl)),
  ReferenceTrajectory.rightBlock131_subset (List.mem_of_getElem? (show ReferenceResiduals.block131[1]?=some panel421.right from rfl))⟩
theorem valid422 : ValidPanel panel422 := ⟨modelCheck422,residualCheck422,
  ReferenceTrajectory.leftBlock23_subset (List.mem_of_getElem? (show ReferenceResiduals.block23[6]?=some panel422.left from rfl)),
  ReferenceTrajectory.rightBlock131_subset (List.mem_of_getElem? (show ReferenceResiduals.block131[0]?=some panel422.right from rfl))⟩
theorem valid423 : ValidPanel panel423 := ⟨modelCheck423,residualCheck423,
  ReferenceTrajectory.leftBlock23_subset (List.mem_of_getElem? (show ReferenceResiduals.block23[7]?=some panel423.left from rfl)),
  ReferenceTrajectory.rightBlock130_subset (List.mem_of_getElem? (show ReferenceResiduals.block130[15]?=some panel423.right from rfl))⟩
theorem valid424 : ValidPanel panel424 := ⟨modelCheck424,residualCheck424,
  ReferenceTrajectory.leftBlock23_subset (List.mem_of_getElem? (show ReferenceResiduals.block23[8]?=some panel424.left from rfl)),
  ReferenceTrajectory.rightBlock130_subset (List.mem_of_getElem? (show ReferenceResiduals.block130[14]?=some panel424.right from rfl))⟩
theorem valid425 : ValidPanel panel425 := ⟨modelCheck425,residualCheck425,
  ReferenceTrajectory.leftBlock23_subset (List.mem_of_getElem? (show ReferenceResiduals.block23[9]?=some panel425.left from rfl)),
  ReferenceTrajectory.rightBlock130_subset (List.mem_of_getElem? (show ReferenceResiduals.block130[13]?=some panel425.right from rfl))⟩
theorem valid426 : ValidPanel panel426 := ⟨modelCheck426,residualCheck426,
  ReferenceTrajectory.leftBlock23_subset (List.mem_of_getElem? (show ReferenceResiduals.block23[10]?=some panel426.left from rfl)),
  ReferenceTrajectory.rightBlock130_subset (List.mem_of_getElem? (show ReferenceResiduals.block130[12]?=some panel426.right from rfl))⟩
theorem valid427 : ValidPanel panel427 := ⟨modelCheck427,residualCheck427,
  ReferenceTrajectory.leftBlock23_subset (List.mem_of_getElem? (show ReferenceResiduals.block23[11]?=some panel427.left from rfl)),
  ReferenceTrajectory.rightBlock130_subset (List.mem_of_getElem? (show ReferenceResiduals.block130[11]?=some panel427.right from rfl))⟩
theorem valid428 : ValidPanel panel428 := ⟨modelCheck428,residualCheck428,
  ReferenceTrajectory.leftBlock23_subset (List.mem_of_getElem? (show ReferenceResiduals.block23[12]?=some panel428.left from rfl)),
  ReferenceTrajectory.rightBlock130_subset (List.mem_of_getElem? (show ReferenceResiduals.block130[10]?=some panel428.right from rfl))⟩
theorem valid429 : ValidPanel panel429 := ⟨modelCheck429,residualCheck429,
  ReferenceTrajectory.leftBlock23_subset (List.mem_of_getElem? (show ReferenceResiduals.block23[13]?=some panel429.left from rfl)),
  ReferenceTrajectory.rightBlock130_subset (List.mem_of_getElem? (show ReferenceResiduals.block130[9]?=some panel429.right from rfl))⟩
theorem valid430 : ValidPanel panel430 := ⟨modelCheck430,residualCheck430,
  ReferenceTrajectory.leftBlock23_subset (List.mem_of_getElem? (show ReferenceResiduals.block23[14]?=some panel430.left from rfl)),
  ReferenceTrajectory.rightBlock130_subset (List.mem_of_getElem? (show ReferenceResiduals.block130[8]?=some panel430.right from rfl))⟩
theorem valid431 : ValidPanel panel431 := ⟨modelCheck431,residualCheck431,
  ReferenceTrajectory.leftBlock23_subset (List.mem_of_getElem? (show ReferenceResiduals.block23[15]?=some panel431.left from rfl)),
  ReferenceTrajectory.rightBlock130_subset (List.mem_of_getElem? (show ReferenceResiduals.block130[7]?=some panel431.right from rfl))⟩
theorem valid432 : ValidPanel panel432 := ⟨modelCheck432,residualCheck432,
  ReferenceTrajectory.leftBlock24_subset (List.mem_of_getElem? (show ReferenceResiduals.block24[0]?=some panel432.left from rfl)),
  ReferenceTrajectory.rightBlock130_subset (List.mem_of_getElem? (show ReferenceResiduals.block130[6]?=some panel432.right from rfl))⟩
theorem valid433 : ValidPanel panel433 := ⟨modelCheck433,residualCheck433,
  ReferenceTrajectory.leftBlock24_subset (List.mem_of_getElem? (show ReferenceResiduals.block24[1]?=some panel433.left from rfl)),
  ReferenceTrajectory.rightBlock130_subset (List.mem_of_getElem? (show ReferenceResiduals.block130[5]?=some panel433.right from rfl))⟩
theorem valid434 : ValidPanel panel434 := ⟨modelCheck434,residualCheck434,
  ReferenceTrajectory.leftBlock24_subset (List.mem_of_getElem? (show ReferenceResiduals.block24[2]?=some panel434.left from rfl)),
  ReferenceTrajectory.rightBlock130_subset (List.mem_of_getElem? (show ReferenceResiduals.block130[4]?=some panel434.right from rfl))⟩
theorem valid435 : ValidPanel panel435 := ⟨modelCheck435,residualCheck435,
  ReferenceTrajectory.leftBlock24_subset (List.mem_of_getElem? (show ReferenceResiduals.block24[3]?=some panel435.left from rfl)),
  ReferenceTrajectory.rightBlock130_subset (List.mem_of_getElem? (show ReferenceResiduals.block130[3]?=some panel435.right from rfl))⟩
theorem valid436 : ValidPanel panel436 := ⟨modelCheck436,residualCheck436,
  ReferenceTrajectory.leftBlock24_subset (List.mem_of_getElem? (show ReferenceResiduals.block24[4]?=some panel436.left from rfl)),
  ReferenceTrajectory.rightBlock130_subset (List.mem_of_getElem? (show ReferenceResiduals.block130[2]?=some panel436.right from rfl))⟩
theorem valid437 : ValidPanel panel437 := ⟨modelCheck437,residualCheck437,
  ReferenceTrajectory.leftBlock24_subset (List.mem_of_getElem? (show ReferenceResiduals.block24[5]?=some panel437.left from rfl)),
  ReferenceTrajectory.rightBlock130_subset (List.mem_of_getElem? (show ReferenceResiduals.block130[1]?=some panel437.right from rfl))⟩
theorem valid438 : ValidPanel panel438 := ⟨modelCheck438,residualCheck438,
  ReferenceTrajectory.leftBlock24_subset (List.mem_of_getElem? (show ReferenceResiduals.block24[6]?=some panel438.left from rfl)),
  ReferenceTrajectory.rightBlock130_subset (List.mem_of_getElem? (show ReferenceResiduals.block130[0]?=some panel438.right from rfl))⟩
theorem valid439 : ValidPanel panel439 := ⟨modelCheck439,residualCheck439,
  ReferenceTrajectory.leftBlock24_subset (List.mem_of_getElem? (show ReferenceResiduals.block24[7]?=some panel439.left from rfl)),
  ReferenceTrajectory.rightBlock129_subset (List.mem_of_getElem? (show ReferenceResiduals.block129[15]?=some panel439.right from rfl))⟩
theorem valid440 : ValidPanel panel440 := ⟨modelCheck440,residualCheck440,
  ReferenceTrajectory.leftBlock24_subset (List.mem_of_getElem? (show ReferenceResiduals.block24[8]?=some panel440.left from rfl)),
  ReferenceTrajectory.rightBlock129_subset (List.mem_of_getElem? (show ReferenceResiduals.block129[14]?=some panel440.right from rfl))⟩
theorem valid441 : ValidPanel panel441 := ⟨modelCheck441,residualCheck441,
  ReferenceTrajectory.leftBlock24_subset (List.mem_of_getElem? (show ReferenceResiduals.block24[9]?=some panel441.left from rfl)),
  ReferenceTrajectory.rightBlock129_subset (List.mem_of_getElem? (show ReferenceResiduals.block129[13]?=some panel441.right from rfl))⟩
theorem valid442 : ValidPanel panel442 := ⟨modelCheck442,residualCheck442,
  ReferenceTrajectory.leftBlock24_subset (List.mem_of_getElem? (show ReferenceResiduals.block24[10]?=some panel442.left from rfl)),
  ReferenceTrajectory.rightBlock129_subset (List.mem_of_getElem? (show ReferenceResiduals.block129[12]?=some panel442.right from rfl))⟩
theorem valid443 : ValidPanel panel443 := ⟨modelCheck443,residualCheck443,
  ReferenceTrajectory.leftBlock24_subset (List.mem_of_getElem? (show ReferenceResiduals.block24[11]?=some panel443.left from rfl)),
  ReferenceTrajectory.rightBlock129_subset (List.mem_of_getElem? (show ReferenceResiduals.block129[11]?=some panel443.right from rfl))⟩
theorem valid444 : ValidPanel panel444 := ⟨modelCheck444,residualCheck444,
  ReferenceTrajectory.leftBlock24_subset (List.mem_of_getElem? (show ReferenceResiduals.block24[12]?=some panel444.left from rfl)),
  ReferenceTrajectory.rightBlock129_subset (List.mem_of_getElem? (show ReferenceResiduals.block129[10]?=some panel444.right from rfl))⟩
theorem valid445 : ValidPanel panel445 := ⟨modelCheck445,residualCheck445,
  ReferenceTrajectory.leftBlock24_subset (List.mem_of_getElem? (show ReferenceResiduals.block24[13]?=some panel445.left from rfl)),
  ReferenceTrajectory.rightBlock129_subset (List.mem_of_getElem? (show ReferenceResiduals.block129[9]?=some panel445.right from rfl))⟩
theorem valid446 : ValidPanel panel446 := ⟨modelCheck446,residualCheck446,
  ReferenceTrajectory.leftBlock24_subset (List.mem_of_getElem? (show ReferenceResiduals.block24[14]?=some panel446.left from rfl)),
  ReferenceTrajectory.rightBlock129_subset (List.mem_of_getElem? (show ReferenceResiduals.block129[8]?=some panel446.right from rfl))⟩
theorem valid447 : ValidPanel panel447 := ⟨modelCheck447,residualCheck447,
  ReferenceTrajectory.leftBlock24_subset (List.mem_of_getElem? (show ReferenceResiduals.block24[15]?=some panel447.left from rfl)),
  ReferenceTrajectory.rightBlock129_subset (List.mem_of_getElem? (show ReferenceResiduals.block129[7]?=some panel447.right from rfl))⟩
theorem validBlock13 : ∀ p∈block13,ValidPanel p := by
  simp only [block13,List.forall_mem_cons]
  exact ⟨valid416,⟨valid417,⟨valid418,⟨valid419,⟨valid420,⟨valid421,⟨valid422,⟨valid423,⟨valid424,⟨valid425,⟨valid426,⟨valid427,⟨valid428,⟨valid429,⟨valid430,⟨valid431,⟨valid432,⟨valid433,⟨valid434,⟨valid435,⟨valid436,⟨valid437,⟨valid438,⟨valid439,⟨valid440,⟨valid441,⟨valid442,⟨valid443,⟨valid444,⟨valid445,⟨valid446,⟨valid447,(by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end chebyshev2.Certificates.Compact.ContactValues

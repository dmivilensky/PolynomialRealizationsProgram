import chebyshev2.Certificates.Compact.ContactBatches.Batch018
import chebyshev2.Certificates.Compact.ContactCoverage
import chebyshev2.Certificates.Compact.ReferenceTrajectoryIndex

/-!
Article: chebyshev2, Section 4.1.
Correspondence018.
Use: `chebyshev2.Certificates.Compact.ContactValues.validBlock18` feeds
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
theorem valid576 : ValidPanel panel576 := ⟨modelCheck576,residualCheck576,
  ReferenceTrajectory.leftBlock33_subset (List.mem_of_getElem? (show ReferenceResiduals.block33[0]?=some panel576.left from rfl)),
  ReferenceTrajectory.rightBlock121_subset (List.mem_of_getElem? (show ReferenceResiduals.block121[6]?=some panel576.right from rfl))⟩
theorem valid577 : ValidPanel panel577 := ⟨modelCheck577,residualCheck577,
  ReferenceTrajectory.leftBlock33_subset (List.mem_of_getElem? (show ReferenceResiduals.block33[1]?=some panel577.left from rfl)),
  ReferenceTrajectory.rightBlock121_subset (List.mem_of_getElem? (show ReferenceResiduals.block121[5]?=some panel577.right from rfl))⟩
theorem valid578 : ValidPanel panel578 := ⟨modelCheck578,residualCheck578,
  ReferenceTrajectory.leftBlock33_subset (List.mem_of_getElem? (show ReferenceResiduals.block33[2]?=some panel578.left from rfl)),
  ReferenceTrajectory.rightBlock121_subset (List.mem_of_getElem? (show ReferenceResiduals.block121[4]?=some panel578.right from rfl))⟩
theorem valid579 : ValidPanel panel579 := ⟨modelCheck579,residualCheck579,
  ReferenceTrajectory.leftBlock33_subset (List.mem_of_getElem? (show ReferenceResiduals.block33[3]?=some panel579.left from rfl)),
  ReferenceTrajectory.rightBlock121_subset (List.mem_of_getElem? (show ReferenceResiduals.block121[3]?=some panel579.right from rfl))⟩
theorem valid580 : ValidPanel panel580 := ⟨modelCheck580,residualCheck580,
  ReferenceTrajectory.leftBlock33_subset (List.mem_of_getElem? (show ReferenceResiduals.block33[4]?=some panel580.left from rfl)),
  ReferenceTrajectory.rightBlock121_subset (List.mem_of_getElem? (show ReferenceResiduals.block121[2]?=some panel580.right from rfl))⟩
theorem valid581 : ValidPanel panel581 := ⟨modelCheck581,residualCheck581,
  ReferenceTrajectory.leftBlock33_subset (List.mem_of_getElem? (show ReferenceResiduals.block33[5]?=some panel581.left from rfl)),
  ReferenceTrajectory.rightBlock121_subset (List.mem_of_getElem? (show ReferenceResiduals.block121[1]?=some panel581.right from rfl))⟩
theorem valid582 : ValidPanel panel582 := ⟨modelCheck582,residualCheck582,
  ReferenceTrajectory.leftBlock33_subset (List.mem_of_getElem? (show ReferenceResiduals.block33[6]?=some panel582.left from rfl)),
  ReferenceTrajectory.rightBlock121_subset (List.mem_of_getElem? (show ReferenceResiduals.block121[0]?=some panel582.right from rfl))⟩
theorem valid583 : ValidPanel panel583 := ⟨modelCheck583,residualCheck583,
  ReferenceTrajectory.leftBlock33_subset (List.mem_of_getElem? (show ReferenceResiduals.block33[7]?=some panel583.left from rfl)),
  ReferenceTrajectory.rightBlock120_subset (List.mem_of_getElem? (show ReferenceResiduals.block120[15]?=some panel583.right from rfl))⟩
theorem valid584 : ValidPanel panel584 := ⟨modelCheck584,residualCheck584,
  ReferenceTrajectory.leftBlock33_subset (List.mem_of_getElem? (show ReferenceResiduals.block33[8]?=some panel584.left from rfl)),
  ReferenceTrajectory.rightBlock120_subset (List.mem_of_getElem? (show ReferenceResiduals.block120[14]?=some panel584.right from rfl))⟩
theorem valid585 : ValidPanel panel585 := ⟨modelCheck585,residualCheck585,
  ReferenceTrajectory.leftBlock33_subset (List.mem_of_getElem? (show ReferenceResiduals.block33[9]?=some panel585.left from rfl)),
  ReferenceTrajectory.rightBlock120_subset (List.mem_of_getElem? (show ReferenceResiduals.block120[13]?=some panel585.right from rfl))⟩
theorem valid586 : ValidPanel panel586 := ⟨modelCheck586,residualCheck586,
  ReferenceTrajectory.leftBlock33_subset (List.mem_of_getElem? (show ReferenceResiduals.block33[10]?=some panel586.left from rfl)),
  ReferenceTrajectory.rightBlock120_subset (List.mem_of_getElem? (show ReferenceResiduals.block120[12]?=some panel586.right from rfl))⟩
theorem valid587 : ValidPanel panel587 := ⟨modelCheck587,residualCheck587,
  ReferenceTrajectory.leftBlock33_subset (List.mem_of_getElem? (show ReferenceResiduals.block33[11]?=some panel587.left from rfl)),
  ReferenceTrajectory.rightBlock120_subset (List.mem_of_getElem? (show ReferenceResiduals.block120[11]?=some panel587.right from rfl))⟩
theorem valid588 : ValidPanel panel588 := ⟨modelCheck588,residualCheck588,
  ReferenceTrajectory.leftBlock33_subset (List.mem_of_getElem? (show ReferenceResiduals.block33[12]?=some panel588.left from rfl)),
  ReferenceTrajectory.rightBlock120_subset (List.mem_of_getElem? (show ReferenceResiduals.block120[10]?=some panel588.right from rfl))⟩
theorem valid589 : ValidPanel panel589 := ⟨modelCheck589,residualCheck589,
  ReferenceTrajectory.leftBlock33_subset (List.mem_of_getElem? (show ReferenceResiduals.block33[13]?=some panel589.left from rfl)),
  ReferenceTrajectory.rightBlock120_subset (List.mem_of_getElem? (show ReferenceResiduals.block120[9]?=some panel589.right from rfl))⟩
theorem valid590 : ValidPanel panel590 := ⟨modelCheck590,residualCheck590,
  ReferenceTrajectory.leftBlock33_subset (List.mem_of_getElem? (show ReferenceResiduals.block33[14]?=some panel590.left from rfl)),
  ReferenceTrajectory.rightBlock120_subset (List.mem_of_getElem? (show ReferenceResiduals.block120[8]?=some panel590.right from rfl))⟩
theorem valid591 : ValidPanel panel591 := ⟨modelCheck591,residualCheck591,
  ReferenceTrajectory.leftBlock33_subset (List.mem_of_getElem? (show ReferenceResiduals.block33[15]?=some panel591.left from rfl)),
  ReferenceTrajectory.rightBlock120_subset (List.mem_of_getElem? (show ReferenceResiduals.block120[7]?=some panel591.right from rfl))⟩
theorem valid592 : ValidPanel panel592 := ⟨modelCheck592,residualCheck592,
  ReferenceTrajectory.leftBlock34_subset (List.mem_of_getElem? (show ReferenceResiduals.block34[0]?=some panel592.left from rfl)),
  ReferenceTrajectory.rightBlock120_subset (List.mem_of_getElem? (show ReferenceResiduals.block120[6]?=some panel592.right from rfl))⟩
theorem valid593 : ValidPanel panel593 := ⟨modelCheck593,residualCheck593,
  ReferenceTrajectory.leftBlock34_subset (List.mem_of_getElem? (show ReferenceResiduals.block34[1]?=some panel593.left from rfl)),
  ReferenceTrajectory.rightBlock120_subset (List.mem_of_getElem? (show ReferenceResiduals.block120[5]?=some panel593.right from rfl))⟩
theorem valid594 : ValidPanel panel594 := ⟨modelCheck594,residualCheck594,
  ReferenceTrajectory.leftBlock34_subset (List.mem_of_getElem? (show ReferenceResiduals.block34[2]?=some panel594.left from rfl)),
  ReferenceTrajectory.rightBlock120_subset (List.mem_of_getElem? (show ReferenceResiduals.block120[4]?=some panel594.right from rfl))⟩
theorem valid595 : ValidPanel panel595 := ⟨modelCheck595,residualCheck595,
  ReferenceTrajectory.leftBlock34_subset (List.mem_of_getElem? (show ReferenceResiduals.block34[3]?=some panel595.left from rfl)),
  ReferenceTrajectory.rightBlock120_subset (List.mem_of_getElem? (show ReferenceResiduals.block120[3]?=some panel595.right from rfl))⟩
theorem valid596 : ValidPanel panel596 := ⟨modelCheck596,residualCheck596,
  ReferenceTrajectory.leftBlock34_subset (List.mem_of_getElem? (show ReferenceResiduals.block34[4]?=some panel596.left from rfl)),
  ReferenceTrajectory.rightBlock120_subset (List.mem_of_getElem? (show ReferenceResiduals.block120[2]?=some panel596.right from rfl))⟩
theorem valid597 : ValidPanel panel597 := ⟨modelCheck597,residualCheck597,
  ReferenceTrajectory.leftBlock34_subset (List.mem_of_getElem? (show ReferenceResiduals.block34[5]?=some panel597.left from rfl)),
  ReferenceTrajectory.rightBlock120_subset (List.mem_of_getElem? (show ReferenceResiduals.block120[1]?=some panel597.right from rfl))⟩
theorem valid598 : ValidPanel panel598 := ⟨modelCheck598,residualCheck598,
  ReferenceTrajectory.leftBlock34_subset (List.mem_of_getElem? (show ReferenceResiduals.block34[6]?=some panel598.left from rfl)),
  ReferenceTrajectory.rightBlock120_subset (List.mem_of_getElem? (show ReferenceResiduals.block120[0]?=some panel598.right from rfl))⟩
theorem valid599 : ValidPanel panel599 := ⟨modelCheck599,residualCheck599,
  ReferenceTrajectory.leftBlock34_subset (List.mem_of_getElem? (show ReferenceResiduals.block34[7]?=some panel599.left from rfl)),
  ReferenceTrajectory.rightBlock119_subset (List.mem_of_getElem? (show ReferenceResiduals.block119[15]?=some panel599.right from rfl))⟩
theorem valid600 : ValidPanel panel600 := ⟨modelCheck600,residualCheck600,
  ReferenceTrajectory.leftBlock34_subset (List.mem_of_getElem? (show ReferenceResiduals.block34[8]?=some panel600.left from rfl)),
  ReferenceTrajectory.rightBlock119_subset (List.mem_of_getElem? (show ReferenceResiduals.block119[14]?=some panel600.right from rfl))⟩
theorem valid601 : ValidPanel panel601 := ⟨modelCheck601,residualCheck601,
  ReferenceTrajectory.leftBlock34_subset (List.mem_of_getElem? (show ReferenceResiduals.block34[9]?=some panel601.left from rfl)),
  ReferenceTrajectory.rightBlock119_subset (List.mem_of_getElem? (show ReferenceResiduals.block119[13]?=some panel601.right from rfl))⟩
theorem valid602 : ValidPanel panel602 := ⟨modelCheck602,residualCheck602,
  ReferenceTrajectory.leftBlock34_subset (List.mem_of_getElem? (show ReferenceResiduals.block34[10]?=some panel602.left from rfl)),
  ReferenceTrajectory.rightBlock119_subset (List.mem_of_getElem? (show ReferenceResiduals.block119[12]?=some panel602.right from rfl))⟩
theorem valid603 : ValidPanel panel603 := ⟨modelCheck603,residualCheck603,
  ReferenceTrajectory.leftBlock34_subset (List.mem_of_getElem? (show ReferenceResiduals.block34[11]?=some panel603.left from rfl)),
  ReferenceTrajectory.rightBlock119_subset (List.mem_of_getElem? (show ReferenceResiduals.block119[11]?=some panel603.right from rfl))⟩
theorem valid604 : ValidPanel panel604 := ⟨modelCheck604,residualCheck604,
  ReferenceTrajectory.leftBlock34_subset (List.mem_of_getElem? (show ReferenceResiduals.block34[12]?=some panel604.left from rfl)),
  ReferenceTrajectory.rightBlock119_subset (List.mem_of_getElem? (show ReferenceResiduals.block119[10]?=some panel604.right from rfl))⟩
theorem valid605 : ValidPanel panel605 := ⟨modelCheck605,residualCheck605,
  ReferenceTrajectory.leftBlock34_subset (List.mem_of_getElem? (show ReferenceResiduals.block34[13]?=some panel605.left from rfl)),
  ReferenceTrajectory.rightBlock119_subset (List.mem_of_getElem? (show ReferenceResiduals.block119[9]?=some panel605.right from rfl))⟩
theorem valid606 : ValidPanel panel606 := ⟨modelCheck606,residualCheck606,
  ReferenceTrajectory.leftBlock34_subset (List.mem_of_getElem? (show ReferenceResiduals.block34[14]?=some panel606.left from rfl)),
  ReferenceTrajectory.rightBlock119_subset (List.mem_of_getElem? (show ReferenceResiduals.block119[8]?=some panel606.right from rfl))⟩
theorem valid607 : ValidPanel panel607 := ⟨modelCheck607,residualCheck607,
  ReferenceTrajectory.leftBlock34_subset (List.mem_of_getElem? (show ReferenceResiduals.block34[15]?=some panel607.left from rfl)),
  ReferenceTrajectory.rightBlock119_subset (List.mem_of_getElem? (show ReferenceResiduals.block119[7]?=some panel607.right from rfl))⟩
theorem validBlock18 : ∀ p∈block18,ValidPanel p := by
  simp only [block18,List.forall_mem_cons]
  exact ⟨valid576,⟨valid577,⟨valid578,⟨valid579,⟨valid580,⟨valid581,⟨valid582,⟨valid583,⟨valid584,⟨valid585,⟨valid586,⟨valid587,⟨valid588,⟨valid589,⟨valid590,⟨valid591,⟨valid592,⟨valid593,⟨valid594,⟨valid595,⟨valid596,⟨valid597,⟨valid598,⟨valid599,⟨valid600,⟨valid601,⟨valid602,⟨valid603,⟨valid604,⟨valid605,⟨valid606,⟨valid607,(by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end chebyshev2.Certificates.Compact.ContactValues

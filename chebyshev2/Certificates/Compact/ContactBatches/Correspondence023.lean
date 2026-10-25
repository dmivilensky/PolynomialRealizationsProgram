import chebyshev2.Certificates.Compact.ContactBatches.Batch023
import chebyshev2.Certificates.Compact.ContactCoverage
import chebyshev2.Certificates.Compact.ReferenceTrajectoryIndex

/-!
Article: chebyshev2, Section 4.1.
Correspondence023.
Use: `chebyshev2.Certificates.Compact.ContactValues.validBlock23` feeds
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
theorem valid736 : ValidPanel panel736 := ⟨modelCheck736,residualCheck736,
  ReferenceTrajectory.leftBlock43_subset (List.mem_of_getElem? (show ReferenceResiduals.block43[0]?=some panel736.left from rfl)),
  ReferenceTrajectory.rightBlock111_subset (List.mem_of_getElem? (show ReferenceResiduals.block111[6]?=some panel736.right from rfl))⟩
theorem valid737 : ValidPanel panel737 := ⟨modelCheck737,residualCheck737,
  ReferenceTrajectory.leftBlock43_subset (List.mem_of_getElem? (show ReferenceResiduals.block43[1]?=some panel737.left from rfl)),
  ReferenceTrajectory.rightBlock111_subset (List.mem_of_getElem? (show ReferenceResiduals.block111[5]?=some panel737.right from rfl))⟩
theorem valid738 : ValidPanel panel738 := ⟨modelCheck738,residualCheck738,
  ReferenceTrajectory.leftBlock43_subset (List.mem_of_getElem? (show ReferenceResiduals.block43[2]?=some panel738.left from rfl)),
  ReferenceTrajectory.rightBlock111_subset (List.mem_of_getElem? (show ReferenceResiduals.block111[4]?=some panel738.right from rfl))⟩
theorem valid739 : ValidPanel panel739 := ⟨modelCheck739,residualCheck739,
  ReferenceTrajectory.leftBlock43_subset (List.mem_of_getElem? (show ReferenceResiduals.block43[3]?=some panel739.left from rfl)),
  ReferenceTrajectory.rightBlock111_subset (List.mem_of_getElem? (show ReferenceResiduals.block111[3]?=some panel739.right from rfl))⟩
theorem valid740 : ValidPanel panel740 := ⟨modelCheck740,residualCheck740,
  ReferenceTrajectory.leftBlock43_subset (List.mem_of_getElem? (show ReferenceResiduals.block43[4]?=some panel740.left from rfl)),
  ReferenceTrajectory.rightBlock111_subset (List.mem_of_getElem? (show ReferenceResiduals.block111[2]?=some panel740.right from rfl))⟩
theorem valid741 : ValidPanel panel741 := ⟨modelCheck741,residualCheck741,
  ReferenceTrajectory.leftBlock43_subset (List.mem_of_getElem? (show ReferenceResiduals.block43[5]?=some panel741.left from rfl)),
  ReferenceTrajectory.rightBlock111_subset (List.mem_of_getElem? (show ReferenceResiduals.block111[1]?=some panel741.right from rfl))⟩
theorem valid742 : ValidPanel panel742 := ⟨modelCheck742,residualCheck742,
  ReferenceTrajectory.leftBlock43_subset (List.mem_of_getElem? (show ReferenceResiduals.block43[6]?=some panel742.left from rfl)),
  ReferenceTrajectory.rightBlock111_subset (List.mem_of_getElem? (show ReferenceResiduals.block111[0]?=some panel742.right from rfl))⟩
theorem valid743 : ValidPanel panel743 := ⟨modelCheck743,residualCheck743,
  ReferenceTrajectory.leftBlock43_subset (List.mem_of_getElem? (show ReferenceResiduals.block43[7]?=some panel743.left from rfl)),
  ReferenceTrajectory.rightBlock110_subset (List.mem_of_getElem? (show ReferenceResiduals.block110[15]?=some panel743.right from rfl))⟩
theorem valid744 : ValidPanel panel744 := ⟨modelCheck744,residualCheck744,
  ReferenceTrajectory.leftBlock43_subset (List.mem_of_getElem? (show ReferenceResiduals.block43[8]?=some panel744.left from rfl)),
  ReferenceTrajectory.rightBlock110_subset (List.mem_of_getElem? (show ReferenceResiduals.block110[14]?=some panel744.right from rfl))⟩
theorem valid745 : ValidPanel panel745 := ⟨modelCheck745,residualCheck745,
  ReferenceTrajectory.leftBlock43_subset (List.mem_of_getElem? (show ReferenceResiduals.block43[9]?=some panel745.left from rfl)),
  ReferenceTrajectory.rightBlock110_subset (List.mem_of_getElem? (show ReferenceResiduals.block110[13]?=some panel745.right from rfl))⟩
theorem valid746 : ValidPanel panel746 := ⟨modelCheck746,residualCheck746,
  ReferenceTrajectory.leftBlock43_subset (List.mem_of_getElem? (show ReferenceResiduals.block43[10]?=some panel746.left from rfl)),
  ReferenceTrajectory.rightBlock110_subset (List.mem_of_getElem? (show ReferenceResiduals.block110[12]?=some panel746.right from rfl))⟩
theorem valid747 : ValidPanel panel747 := ⟨modelCheck747,residualCheck747,
  ReferenceTrajectory.leftBlock43_subset (List.mem_of_getElem? (show ReferenceResiduals.block43[11]?=some panel747.left from rfl)),
  ReferenceTrajectory.rightBlock110_subset (List.mem_of_getElem? (show ReferenceResiduals.block110[11]?=some panel747.right from rfl))⟩
theorem valid748 : ValidPanel panel748 := ⟨modelCheck748,residualCheck748,
  ReferenceTrajectory.leftBlock43_subset (List.mem_of_getElem? (show ReferenceResiduals.block43[12]?=some panel748.left from rfl)),
  ReferenceTrajectory.rightBlock110_subset (List.mem_of_getElem? (show ReferenceResiduals.block110[10]?=some panel748.right from rfl))⟩
theorem valid749 : ValidPanel panel749 := ⟨modelCheck749,residualCheck749,
  ReferenceTrajectory.leftBlock43_subset (List.mem_of_getElem? (show ReferenceResiduals.block43[13]?=some panel749.left from rfl)),
  ReferenceTrajectory.rightBlock110_subset (List.mem_of_getElem? (show ReferenceResiduals.block110[9]?=some panel749.right from rfl))⟩
theorem valid750 : ValidPanel panel750 := ⟨modelCheck750,residualCheck750,
  ReferenceTrajectory.leftBlock43_subset (List.mem_of_getElem? (show ReferenceResiduals.block43[14]?=some panel750.left from rfl)),
  ReferenceTrajectory.rightBlock110_subset (List.mem_of_getElem? (show ReferenceResiduals.block110[8]?=some panel750.right from rfl))⟩
theorem valid751 : ValidPanel panel751 := ⟨modelCheck751,residualCheck751,
  ReferenceTrajectory.leftBlock43_subset (List.mem_of_getElem? (show ReferenceResiduals.block43[15]?=some panel751.left from rfl)),
  ReferenceTrajectory.rightBlock110_subset (List.mem_of_getElem? (show ReferenceResiduals.block110[7]?=some panel751.right from rfl))⟩
theorem valid752 : ValidPanel panel752 := ⟨modelCheck752,residualCheck752,
  ReferenceTrajectory.leftBlock44_subset (List.mem_of_getElem? (show ReferenceResiduals.block44[0]?=some panel752.left from rfl)),
  ReferenceTrajectory.rightBlock110_subset (List.mem_of_getElem? (show ReferenceResiduals.block110[6]?=some panel752.right from rfl))⟩
theorem valid753 : ValidPanel panel753 := ⟨modelCheck753,residualCheck753,
  ReferenceTrajectory.leftBlock44_subset (List.mem_of_getElem? (show ReferenceResiduals.block44[1]?=some panel753.left from rfl)),
  ReferenceTrajectory.rightBlock110_subset (List.mem_of_getElem? (show ReferenceResiduals.block110[5]?=some panel753.right from rfl))⟩
theorem valid754 : ValidPanel panel754 := ⟨modelCheck754,residualCheck754,
  ReferenceTrajectory.leftBlock44_subset (List.mem_of_getElem? (show ReferenceResiduals.block44[2]?=some panel754.left from rfl)),
  ReferenceTrajectory.rightBlock110_subset (List.mem_of_getElem? (show ReferenceResiduals.block110[4]?=some panel754.right from rfl))⟩
theorem valid755 : ValidPanel panel755 := ⟨modelCheck755,residualCheck755,
  ReferenceTrajectory.leftBlock44_subset (List.mem_of_getElem? (show ReferenceResiduals.block44[3]?=some panel755.left from rfl)),
  ReferenceTrajectory.rightBlock110_subset (List.mem_of_getElem? (show ReferenceResiduals.block110[3]?=some panel755.right from rfl))⟩
theorem valid756 : ValidPanel panel756 := ⟨modelCheck756,residualCheck756,
  ReferenceTrajectory.leftBlock44_subset (List.mem_of_getElem? (show ReferenceResiduals.block44[4]?=some panel756.left from rfl)),
  ReferenceTrajectory.rightBlock110_subset (List.mem_of_getElem? (show ReferenceResiduals.block110[2]?=some panel756.right from rfl))⟩
theorem valid757 : ValidPanel panel757 := ⟨modelCheck757,residualCheck757,
  ReferenceTrajectory.leftBlock44_subset (List.mem_of_getElem? (show ReferenceResiduals.block44[5]?=some panel757.left from rfl)),
  ReferenceTrajectory.rightBlock110_subset (List.mem_of_getElem? (show ReferenceResiduals.block110[1]?=some panel757.right from rfl))⟩
theorem valid758 : ValidPanel panel758 := ⟨modelCheck758,residualCheck758,
  ReferenceTrajectory.leftBlock44_subset (List.mem_of_getElem? (show ReferenceResiduals.block44[6]?=some panel758.left from rfl)),
  ReferenceTrajectory.rightBlock110_subset (List.mem_of_getElem? (show ReferenceResiduals.block110[0]?=some panel758.right from rfl))⟩
theorem valid759 : ValidPanel panel759 := ⟨modelCheck759,residualCheck759,
  ReferenceTrajectory.leftBlock44_subset (List.mem_of_getElem? (show ReferenceResiduals.block44[7]?=some panel759.left from rfl)),
  ReferenceTrajectory.rightBlock109_subset (List.mem_of_getElem? (show ReferenceResiduals.block109[15]?=some panel759.right from rfl))⟩
theorem valid760 : ValidPanel panel760 := ⟨modelCheck760,residualCheck760,
  ReferenceTrajectory.leftBlock44_subset (List.mem_of_getElem? (show ReferenceResiduals.block44[8]?=some panel760.left from rfl)),
  ReferenceTrajectory.rightBlock109_subset (List.mem_of_getElem? (show ReferenceResiduals.block109[14]?=some panel760.right from rfl))⟩
theorem valid761 : ValidPanel panel761 := ⟨modelCheck761,residualCheck761,
  ReferenceTrajectory.leftBlock44_subset (List.mem_of_getElem? (show ReferenceResiduals.block44[9]?=some panel761.left from rfl)),
  ReferenceTrajectory.rightBlock109_subset (List.mem_of_getElem? (show ReferenceResiduals.block109[13]?=some panel761.right from rfl))⟩
theorem valid762 : ValidPanel panel762 := ⟨modelCheck762,residualCheck762,
  ReferenceTrajectory.leftBlock44_subset (List.mem_of_getElem? (show ReferenceResiduals.block44[10]?=some panel762.left from rfl)),
  ReferenceTrajectory.rightBlock109_subset (List.mem_of_getElem? (show ReferenceResiduals.block109[12]?=some panel762.right from rfl))⟩
theorem valid763 : ValidPanel panel763 := ⟨modelCheck763,residualCheck763,
  ReferenceTrajectory.leftBlock44_subset (List.mem_of_getElem? (show ReferenceResiduals.block44[11]?=some panel763.left from rfl)),
  ReferenceTrajectory.rightBlock109_subset (List.mem_of_getElem? (show ReferenceResiduals.block109[11]?=some panel763.right from rfl))⟩
theorem valid764 : ValidPanel panel764 := ⟨modelCheck764,residualCheck764,
  ReferenceTrajectory.leftBlock44_subset (List.mem_of_getElem? (show ReferenceResiduals.block44[12]?=some panel764.left from rfl)),
  ReferenceTrajectory.rightBlock109_subset (List.mem_of_getElem? (show ReferenceResiduals.block109[10]?=some panel764.right from rfl))⟩
theorem valid765 : ValidPanel panel765 := ⟨modelCheck765,residualCheck765,
  ReferenceTrajectory.leftBlock44_subset (List.mem_of_getElem? (show ReferenceResiduals.block44[13]?=some panel765.left from rfl)),
  ReferenceTrajectory.rightBlock109_subset (List.mem_of_getElem? (show ReferenceResiduals.block109[9]?=some panel765.right from rfl))⟩
theorem valid766 : ValidPanel panel766 := ⟨modelCheck766,residualCheck766,
  ReferenceTrajectory.leftBlock44_subset (List.mem_of_getElem? (show ReferenceResiduals.block44[14]?=some panel766.left from rfl)),
  ReferenceTrajectory.rightBlock109_subset (List.mem_of_getElem? (show ReferenceResiduals.block109[8]?=some panel766.right from rfl))⟩
theorem valid767 : ValidPanel panel767 := ⟨modelCheck767,residualCheck767,
  ReferenceTrajectory.leftBlock44_subset (List.mem_of_getElem? (show ReferenceResiduals.block44[15]?=some panel767.left from rfl)),
  ReferenceTrajectory.rightBlock109_subset (List.mem_of_getElem? (show ReferenceResiduals.block109[7]?=some panel767.right from rfl))⟩
theorem validBlock23 : ∀ p∈block23,ValidPanel p := by
  simp only [block23,List.forall_mem_cons]
  exact ⟨valid736,⟨valid737,⟨valid738,⟨valid739,⟨valid740,⟨valid741,⟨valid742,⟨valid743,⟨valid744,⟨valid745,⟨valid746,⟨valid747,⟨valid748,⟨valid749,⟨valid750,⟨valid751,⟨valid752,⟨valid753,⟨valid754,⟨valid755,⟨valid756,⟨valid757,⟨valid758,⟨valid759,⟨valid760,⟨valid761,⟨valid762,⟨valid763,⟨valid764,⟨valid765,⟨valid766,⟨valid767,(by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end chebyshev2.Certificates.Compact.ContactValues

import chebyshev2.Certificates.Compact.ContactBatches.Batch022
import chebyshev2.Certificates.Compact.ContactCoverage
import chebyshev2.Certificates.Compact.ReferenceTrajectoryIndex

/-!
Article: chebyshev2, Section 4.1.
Correspondence022.
Use: `chebyshev2.Certificates.Compact.ContactValues.validBlock22` feeds
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
theorem valid704 : ValidPanel panel704 := ⟨modelCheck704,residualCheck704,
  ReferenceTrajectory.leftBlock41_subset (List.mem_of_getElem? (show ReferenceResiduals.block41[0]?=some panel704.left from rfl)),
  ReferenceTrajectory.rightBlock113_subset (List.mem_of_getElem? (show ReferenceResiduals.block113[6]?=some panel704.right from rfl))⟩
theorem valid705 : ValidPanel panel705 := ⟨modelCheck705,residualCheck705,
  ReferenceTrajectory.leftBlock41_subset (List.mem_of_getElem? (show ReferenceResiduals.block41[1]?=some panel705.left from rfl)),
  ReferenceTrajectory.rightBlock113_subset (List.mem_of_getElem? (show ReferenceResiduals.block113[5]?=some panel705.right from rfl))⟩
theorem valid706 : ValidPanel panel706 := ⟨modelCheck706,residualCheck706,
  ReferenceTrajectory.leftBlock41_subset (List.mem_of_getElem? (show ReferenceResiduals.block41[2]?=some panel706.left from rfl)),
  ReferenceTrajectory.rightBlock113_subset (List.mem_of_getElem? (show ReferenceResiduals.block113[4]?=some panel706.right from rfl))⟩
theorem valid707 : ValidPanel panel707 := ⟨modelCheck707,residualCheck707,
  ReferenceTrajectory.leftBlock41_subset (List.mem_of_getElem? (show ReferenceResiduals.block41[3]?=some panel707.left from rfl)),
  ReferenceTrajectory.rightBlock113_subset (List.mem_of_getElem? (show ReferenceResiduals.block113[3]?=some panel707.right from rfl))⟩
theorem valid708 : ValidPanel panel708 := ⟨modelCheck708,residualCheck708,
  ReferenceTrajectory.leftBlock41_subset (List.mem_of_getElem? (show ReferenceResiduals.block41[4]?=some panel708.left from rfl)),
  ReferenceTrajectory.rightBlock113_subset (List.mem_of_getElem? (show ReferenceResiduals.block113[2]?=some panel708.right from rfl))⟩
theorem valid709 : ValidPanel panel709 := ⟨modelCheck709,residualCheck709,
  ReferenceTrajectory.leftBlock41_subset (List.mem_of_getElem? (show ReferenceResiduals.block41[5]?=some panel709.left from rfl)),
  ReferenceTrajectory.rightBlock113_subset (List.mem_of_getElem? (show ReferenceResiduals.block113[1]?=some panel709.right from rfl))⟩
theorem valid710 : ValidPanel panel710 := ⟨modelCheck710,residualCheck710,
  ReferenceTrajectory.leftBlock41_subset (List.mem_of_getElem? (show ReferenceResiduals.block41[6]?=some panel710.left from rfl)),
  ReferenceTrajectory.rightBlock113_subset (List.mem_of_getElem? (show ReferenceResiduals.block113[0]?=some panel710.right from rfl))⟩
theorem valid711 : ValidPanel panel711 := ⟨modelCheck711,residualCheck711,
  ReferenceTrajectory.leftBlock41_subset (List.mem_of_getElem? (show ReferenceResiduals.block41[7]?=some panel711.left from rfl)),
  ReferenceTrajectory.rightBlock112_subset (List.mem_of_getElem? (show ReferenceResiduals.block112[15]?=some panel711.right from rfl))⟩
theorem valid712 : ValidPanel panel712 := ⟨modelCheck712,residualCheck712,
  ReferenceTrajectory.leftBlock41_subset (List.mem_of_getElem? (show ReferenceResiduals.block41[8]?=some panel712.left from rfl)),
  ReferenceTrajectory.rightBlock112_subset (List.mem_of_getElem? (show ReferenceResiduals.block112[14]?=some panel712.right from rfl))⟩
theorem valid713 : ValidPanel panel713 := ⟨modelCheck713,residualCheck713,
  ReferenceTrajectory.leftBlock41_subset (List.mem_of_getElem? (show ReferenceResiduals.block41[9]?=some panel713.left from rfl)),
  ReferenceTrajectory.rightBlock112_subset (List.mem_of_getElem? (show ReferenceResiduals.block112[13]?=some panel713.right from rfl))⟩
theorem valid714 : ValidPanel panel714 := ⟨modelCheck714,residualCheck714,
  ReferenceTrajectory.leftBlock41_subset (List.mem_of_getElem? (show ReferenceResiduals.block41[10]?=some panel714.left from rfl)),
  ReferenceTrajectory.rightBlock112_subset (List.mem_of_getElem? (show ReferenceResiduals.block112[12]?=some panel714.right from rfl))⟩
theorem valid715 : ValidPanel panel715 := ⟨modelCheck715,residualCheck715,
  ReferenceTrajectory.leftBlock41_subset (List.mem_of_getElem? (show ReferenceResiduals.block41[11]?=some panel715.left from rfl)),
  ReferenceTrajectory.rightBlock112_subset (List.mem_of_getElem? (show ReferenceResiduals.block112[11]?=some panel715.right from rfl))⟩
theorem valid716 : ValidPanel panel716 := ⟨modelCheck716,residualCheck716,
  ReferenceTrajectory.leftBlock41_subset (List.mem_of_getElem? (show ReferenceResiduals.block41[12]?=some panel716.left from rfl)),
  ReferenceTrajectory.rightBlock112_subset (List.mem_of_getElem? (show ReferenceResiduals.block112[10]?=some panel716.right from rfl))⟩
theorem valid717 : ValidPanel panel717 := ⟨modelCheck717,residualCheck717,
  ReferenceTrajectory.leftBlock41_subset (List.mem_of_getElem? (show ReferenceResiduals.block41[13]?=some panel717.left from rfl)),
  ReferenceTrajectory.rightBlock112_subset (List.mem_of_getElem? (show ReferenceResiduals.block112[9]?=some panel717.right from rfl))⟩
theorem valid718 : ValidPanel panel718 := ⟨modelCheck718,residualCheck718,
  ReferenceTrajectory.leftBlock41_subset (List.mem_of_getElem? (show ReferenceResiduals.block41[14]?=some panel718.left from rfl)),
  ReferenceTrajectory.rightBlock112_subset (List.mem_of_getElem? (show ReferenceResiduals.block112[8]?=some panel718.right from rfl))⟩
theorem valid719 : ValidPanel panel719 := ⟨modelCheck719,residualCheck719,
  ReferenceTrajectory.leftBlock41_subset (List.mem_of_getElem? (show ReferenceResiduals.block41[15]?=some panel719.left from rfl)),
  ReferenceTrajectory.rightBlock112_subset (List.mem_of_getElem? (show ReferenceResiduals.block112[7]?=some panel719.right from rfl))⟩
theorem valid720 : ValidPanel panel720 := ⟨modelCheck720,residualCheck720,
  ReferenceTrajectory.leftBlock42_subset (List.mem_of_getElem? (show ReferenceResiduals.block42[0]?=some panel720.left from rfl)),
  ReferenceTrajectory.rightBlock112_subset (List.mem_of_getElem? (show ReferenceResiduals.block112[6]?=some panel720.right from rfl))⟩
theorem valid721 : ValidPanel panel721 := ⟨modelCheck721,residualCheck721,
  ReferenceTrajectory.leftBlock42_subset (List.mem_of_getElem? (show ReferenceResiduals.block42[1]?=some panel721.left from rfl)),
  ReferenceTrajectory.rightBlock112_subset (List.mem_of_getElem? (show ReferenceResiduals.block112[5]?=some panel721.right from rfl))⟩
theorem valid722 : ValidPanel panel722 := ⟨modelCheck722,residualCheck722,
  ReferenceTrajectory.leftBlock42_subset (List.mem_of_getElem? (show ReferenceResiduals.block42[2]?=some panel722.left from rfl)),
  ReferenceTrajectory.rightBlock112_subset (List.mem_of_getElem? (show ReferenceResiduals.block112[4]?=some panel722.right from rfl))⟩
theorem valid723 : ValidPanel panel723 := ⟨modelCheck723,residualCheck723,
  ReferenceTrajectory.leftBlock42_subset (List.mem_of_getElem? (show ReferenceResiduals.block42[3]?=some panel723.left from rfl)),
  ReferenceTrajectory.rightBlock112_subset (List.mem_of_getElem? (show ReferenceResiduals.block112[3]?=some panel723.right from rfl))⟩
theorem valid724 : ValidPanel panel724 := ⟨modelCheck724,residualCheck724,
  ReferenceTrajectory.leftBlock42_subset (List.mem_of_getElem? (show ReferenceResiduals.block42[4]?=some panel724.left from rfl)),
  ReferenceTrajectory.rightBlock112_subset (List.mem_of_getElem? (show ReferenceResiduals.block112[2]?=some panel724.right from rfl))⟩
theorem valid725 : ValidPanel panel725 := ⟨modelCheck725,residualCheck725,
  ReferenceTrajectory.leftBlock42_subset (List.mem_of_getElem? (show ReferenceResiduals.block42[5]?=some panel725.left from rfl)),
  ReferenceTrajectory.rightBlock112_subset (List.mem_of_getElem? (show ReferenceResiduals.block112[1]?=some panel725.right from rfl))⟩
theorem valid726 : ValidPanel panel726 := ⟨modelCheck726,residualCheck726,
  ReferenceTrajectory.leftBlock42_subset (List.mem_of_getElem? (show ReferenceResiduals.block42[6]?=some panel726.left from rfl)),
  ReferenceTrajectory.rightBlock112_subset (List.mem_of_getElem? (show ReferenceResiduals.block112[0]?=some panel726.right from rfl))⟩
theorem valid727 : ValidPanel panel727 := ⟨modelCheck727,residualCheck727,
  ReferenceTrajectory.leftBlock42_subset (List.mem_of_getElem? (show ReferenceResiduals.block42[7]?=some panel727.left from rfl)),
  ReferenceTrajectory.rightBlock111_subset (List.mem_of_getElem? (show ReferenceResiduals.block111[15]?=some panel727.right from rfl))⟩
theorem valid728 : ValidPanel panel728 := ⟨modelCheck728,residualCheck728,
  ReferenceTrajectory.leftBlock42_subset (List.mem_of_getElem? (show ReferenceResiduals.block42[8]?=some panel728.left from rfl)),
  ReferenceTrajectory.rightBlock111_subset (List.mem_of_getElem? (show ReferenceResiduals.block111[14]?=some panel728.right from rfl))⟩
theorem valid729 : ValidPanel panel729 := ⟨modelCheck729,residualCheck729,
  ReferenceTrajectory.leftBlock42_subset (List.mem_of_getElem? (show ReferenceResiduals.block42[9]?=some panel729.left from rfl)),
  ReferenceTrajectory.rightBlock111_subset (List.mem_of_getElem? (show ReferenceResiduals.block111[13]?=some panel729.right from rfl))⟩
theorem valid730 : ValidPanel panel730 := ⟨modelCheck730,residualCheck730,
  ReferenceTrajectory.leftBlock42_subset (List.mem_of_getElem? (show ReferenceResiduals.block42[10]?=some panel730.left from rfl)),
  ReferenceTrajectory.rightBlock111_subset (List.mem_of_getElem? (show ReferenceResiduals.block111[12]?=some panel730.right from rfl))⟩
theorem valid731 : ValidPanel panel731 := ⟨modelCheck731,residualCheck731,
  ReferenceTrajectory.leftBlock42_subset (List.mem_of_getElem? (show ReferenceResiduals.block42[11]?=some panel731.left from rfl)),
  ReferenceTrajectory.rightBlock111_subset (List.mem_of_getElem? (show ReferenceResiduals.block111[11]?=some panel731.right from rfl))⟩
theorem valid732 : ValidPanel panel732 := ⟨modelCheck732,residualCheck732,
  ReferenceTrajectory.leftBlock42_subset (List.mem_of_getElem? (show ReferenceResiduals.block42[12]?=some panel732.left from rfl)),
  ReferenceTrajectory.rightBlock111_subset (List.mem_of_getElem? (show ReferenceResiduals.block111[10]?=some panel732.right from rfl))⟩
theorem valid733 : ValidPanel panel733 := ⟨modelCheck733,residualCheck733,
  ReferenceTrajectory.leftBlock42_subset (List.mem_of_getElem? (show ReferenceResiduals.block42[13]?=some panel733.left from rfl)),
  ReferenceTrajectory.rightBlock111_subset (List.mem_of_getElem? (show ReferenceResiduals.block111[9]?=some panel733.right from rfl))⟩
theorem valid734 : ValidPanel panel734 := ⟨modelCheck734,residualCheck734,
  ReferenceTrajectory.leftBlock42_subset (List.mem_of_getElem? (show ReferenceResiduals.block42[14]?=some panel734.left from rfl)),
  ReferenceTrajectory.rightBlock111_subset (List.mem_of_getElem? (show ReferenceResiduals.block111[8]?=some panel734.right from rfl))⟩
theorem valid735 : ValidPanel panel735 := ⟨modelCheck735,residualCheck735,
  ReferenceTrajectory.leftBlock42_subset (List.mem_of_getElem? (show ReferenceResiduals.block42[15]?=some panel735.left from rfl)),
  ReferenceTrajectory.rightBlock111_subset (List.mem_of_getElem? (show ReferenceResiduals.block111[7]?=some panel735.right from rfl))⟩
theorem validBlock22 : ∀ p∈block22,ValidPanel p := by
  simp only [block22,List.forall_mem_cons]
  exact ⟨valid704,⟨valid705,⟨valid706,⟨valid707,⟨valid708,⟨valid709,⟨valid710,⟨valid711,⟨valid712,⟨valid713,⟨valid714,⟨valid715,⟨valid716,⟨valid717,⟨valid718,⟨valid719,⟨valid720,⟨valid721,⟨valid722,⟨valid723,⟨valid724,⟨valid725,⟨valid726,⟨valid727,⟨valid728,⟨valid729,⟨valid730,⟨valid731,⟨valid732,⟨valid733,⟨valid734,⟨valid735,(by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end chebyshev2.Certificates.Compact.ContactValues

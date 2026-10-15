import «2610.05164v2».Certificates.Compact.ContactBatches.Batch026
import «2610.05164v2».Certificates.Compact.ContactCoverage
import «2610.05164v2».Certificates.Compact.ReferenceTrajectoryIndex

/-!
Article: 2610.05164v2, Section 4.1.
Correspondence026.
Use: `«2610.05164v2».Certificates.Compact.ContactValues.validBlock26` feeds
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
theorem valid832 : ValidPanel panel832 := ⟨modelCheck832,residualCheck832,
  ReferenceTrajectory.leftBlock49_subset (List.mem_of_getElem? (show ReferenceResiduals.block49[0]?=some panel832.left from rfl)),
  ReferenceTrajectory.rightBlock105_subset (List.mem_of_getElem? (show ReferenceResiduals.block105[6]?=some panel832.right from rfl))⟩
theorem valid833 : ValidPanel panel833 := ⟨modelCheck833,residualCheck833,
  ReferenceTrajectory.leftBlock49_subset (List.mem_of_getElem? (show ReferenceResiduals.block49[1]?=some panel833.left from rfl)),
  ReferenceTrajectory.rightBlock105_subset (List.mem_of_getElem? (show ReferenceResiduals.block105[5]?=some panel833.right from rfl))⟩
theorem valid834 : ValidPanel panel834 := ⟨modelCheck834,residualCheck834,
  ReferenceTrajectory.leftBlock49_subset (List.mem_of_getElem? (show ReferenceResiduals.block49[2]?=some panel834.left from rfl)),
  ReferenceTrajectory.rightBlock105_subset (List.mem_of_getElem? (show ReferenceResiduals.block105[4]?=some panel834.right from rfl))⟩
theorem valid835 : ValidPanel panel835 := ⟨modelCheck835,residualCheck835,
  ReferenceTrajectory.leftBlock49_subset (List.mem_of_getElem? (show ReferenceResiduals.block49[3]?=some panel835.left from rfl)),
  ReferenceTrajectory.rightBlock105_subset (List.mem_of_getElem? (show ReferenceResiduals.block105[3]?=some panel835.right from rfl))⟩
theorem valid836 : ValidPanel panel836 := ⟨modelCheck836,residualCheck836,
  ReferenceTrajectory.leftBlock49_subset (List.mem_of_getElem? (show ReferenceResiduals.block49[4]?=some panel836.left from rfl)),
  ReferenceTrajectory.rightBlock105_subset (List.mem_of_getElem? (show ReferenceResiduals.block105[2]?=some panel836.right from rfl))⟩
theorem valid837 : ValidPanel panel837 := ⟨modelCheck837,residualCheck837,
  ReferenceTrajectory.leftBlock49_subset (List.mem_of_getElem? (show ReferenceResiduals.block49[5]?=some panel837.left from rfl)),
  ReferenceTrajectory.rightBlock105_subset (List.mem_of_getElem? (show ReferenceResiduals.block105[1]?=some panel837.right from rfl))⟩
theorem valid838 : ValidPanel panel838 := ⟨modelCheck838,residualCheck838,
  ReferenceTrajectory.leftBlock49_subset (List.mem_of_getElem? (show ReferenceResiduals.block49[6]?=some panel838.left from rfl)),
  ReferenceTrajectory.rightBlock105_subset (List.mem_of_getElem? (show ReferenceResiduals.block105[0]?=some panel838.right from rfl))⟩
theorem valid839 : ValidPanel panel839 := ⟨modelCheck839,residualCheck839,
  ReferenceTrajectory.leftBlock49_subset (List.mem_of_getElem? (show ReferenceResiduals.block49[7]?=some panel839.left from rfl)),
  ReferenceTrajectory.rightBlock104_subset (List.mem_of_getElem? (show ReferenceResiduals.block104[15]?=some panel839.right from rfl))⟩
theorem valid840 : ValidPanel panel840 := ⟨modelCheck840,residualCheck840,
  ReferenceTrajectory.leftBlock49_subset (List.mem_of_getElem? (show ReferenceResiduals.block49[8]?=some panel840.left from rfl)),
  ReferenceTrajectory.rightBlock104_subset (List.mem_of_getElem? (show ReferenceResiduals.block104[14]?=some panel840.right from rfl))⟩
theorem valid841 : ValidPanel panel841 := ⟨modelCheck841,residualCheck841,
  ReferenceTrajectory.leftBlock49_subset (List.mem_of_getElem? (show ReferenceResiduals.block49[9]?=some panel841.left from rfl)),
  ReferenceTrajectory.rightBlock104_subset (List.mem_of_getElem? (show ReferenceResiduals.block104[13]?=some panel841.right from rfl))⟩
theorem valid842 : ValidPanel panel842 := ⟨modelCheck842,residualCheck842,
  ReferenceTrajectory.leftBlock49_subset (List.mem_of_getElem? (show ReferenceResiduals.block49[10]?=some panel842.left from rfl)),
  ReferenceTrajectory.rightBlock104_subset (List.mem_of_getElem? (show ReferenceResiduals.block104[12]?=some panel842.right from rfl))⟩
theorem valid843 : ValidPanel panel843 := ⟨modelCheck843,residualCheck843,
  ReferenceTrajectory.leftBlock49_subset (List.mem_of_getElem? (show ReferenceResiduals.block49[11]?=some panel843.left from rfl)),
  ReferenceTrajectory.rightBlock104_subset (List.mem_of_getElem? (show ReferenceResiduals.block104[11]?=some panel843.right from rfl))⟩
theorem valid844 : ValidPanel panel844 := ⟨modelCheck844,residualCheck844,
  ReferenceTrajectory.leftBlock49_subset (List.mem_of_getElem? (show ReferenceResiduals.block49[12]?=some panel844.left from rfl)),
  ReferenceTrajectory.rightBlock104_subset (List.mem_of_getElem? (show ReferenceResiduals.block104[10]?=some panel844.right from rfl))⟩
theorem valid845 : ValidPanel panel845 := ⟨modelCheck845,residualCheck845,
  ReferenceTrajectory.leftBlock49_subset (List.mem_of_getElem? (show ReferenceResiduals.block49[13]?=some panel845.left from rfl)),
  ReferenceTrajectory.rightBlock104_subset (List.mem_of_getElem? (show ReferenceResiduals.block104[9]?=some panel845.right from rfl))⟩
theorem valid846 : ValidPanel panel846 := ⟨modelCheck846,residualCheck846,
  ReferenceTrajectory.leftBlock49_subset (List.mem_of_getElem? (show ReferenceResiduals.block49[14]?=some panel846.left from rfl)),
  ReferenceTrajectory.rightBlock104_subset (List.mem_of_getElem? (show ReferenceResiduals.block104[8]?=some panel846.right from rfl))⟩
theorem valid847 : ValidPanel panel847 := ⟨modelCheck847,residualCheck847,
  ReferenceTrajectory.leftBlock49_subset (List.mem_of_getElem? (show ReferenceResiduals.block49[15]?=some panel847.left from rfl)),
  ReferenceTrajectory.rightBlock104_subset (List.mem_of_getElem? (show ReferenceResiduals.block104[7]?=some panel847.right from rfl))⟩
theorem valid848 : ValidPanel panel848 := ⟨modelCheck848,residualCheck848,
  ReferenceTrajectory.leftBlock50_subset (List.mem_of_getElem? (show ReferenceResiduals.block50[0]?=some panel848.left from rfl)),
  ReferenceTrajectory.rightBlock104_subset (List.mem_of_getElem? (show ReferenceResiduals.block104[6]?=some panel848.right from rfl))⟩
theorem valid849 : ValidPanel panel849 := ⟨modelCheck849,residualCheck849,
  ReferenceTrajectory.leftBlock50_subset (List.mem_of_getElem? (show ReferenceResiduals.block50[1]?=some panel849.left from rfl)),
  ReferenceTrajectory.rightBlock104_subset (List.mem_of_getElem? (show ReferenceResiduals.block104[5]?=some panel849.right from rfl))⟩
theorem valid850 : ValidPanel panel850 := ⟨modelCheck850,residualCheck850,
  ReferenceTrajectory.leftBlock50_subset (List.mem_of_getElem? (show ReferenceResiduals.block50[2]?=some panel850.left from rfl)),
  ReferenceTrajectory.rightBlock104_subset (List.mem_of_getElem? (show ReferenceResiduals.block104[4]?=some panel850.right from rfl))⟩
theorem valid851 : ValidPanel panel851 := ⟨modelCheck851,residualCheck851,
  ReferenceTrajectory.leftBlock50_subset (List.mem_of_getElem? (show ReferenceResiduals.block50[3]?=some panel851.left from rfl)),
  ReferenceTrajectory.rightBlock104_subset (List.mem_of_getElem? (show ReferenceResiduals.block104[3]?=some panel851.right from rfl))⟩
theorem valid852 : ValidPanel panel852 := ⟨modelCheck852,residualCheck852,
  ReferenceTrajectory.leftBlock50_subset (List.mem_of_getElem? (show ReferenceResiduals.block50[3]?=some panel852.left from rfl)),
  ReferenceTrajectory.rightBlock104_subset (List.mem_of_getElem? (show ReferenceResiduals.block104[2]?=some panel852.right from rfl))⟩
theorem valid853 : ValidPanel panel853 := ⟨modelCheck853,residualCheck853,
  ReferenceTrajectory.leftBlock50_subset (List.mem_of_getElem? (show ReferenceResiduals.block50[4]?=some panel853.left from rfl)),
  ReferenceTrajectory.rightBlock104_subset (List.mem_of_getElem? (show ReferenceResiduals.block104[1]?=some panel853.right from rfl))⟩
theorem valid854 : ValidPanel panel854 := ⟨modelCheck854,residualCheck854,
  ReferenceTrajectory.leftBlock50_subset (List.mem_of_getElem? (show ReferenceResiduals.block50[4]?=some panel854.left from rfl)),
  ReferenceTrajectory.rightBlock104_subset (List.mem_of_getElem? (show ReferenceResiduals.block104[0]?=some panel854.right from rfl))⟩
theorem valid855 : ValidPanel panel855 := ⟨modelCheck855,residualCheck855,
  ReferenceTrajectory.leftBlock50_subset (List.mem_of_getElem? (show ReferenceResiduals.block50[5]?=some panel855.left from rfl)),
  ReferenceTrajectory.rightBlock103_subset (List.mem_of_getElem? (show ReferenceResiduals.block103[15]?=some panel855.right from rfl))⟩
theorem valid856 : ValidPanel panel856 := ⟨modelCheck856,residualCheck856,
  ReferenceTrajectory.leftBlock50_subset (List.mem_of_getElem? (show ReferenceResiduals.block50[5]?=some panel856.left from rfl)),
  ReferenceTrajectory.rightBlock103_subset (List.mem_of_getElem? (show ReferenceResiduals.block103[14]?=some panel856.right from rfl))⟩
theorem valid857 : ValidPanel panel857 := ⟨modelCheck857,residualCheck857,
  ReferenceTrajectory.leftBlock50_subset (List.mem_of_getElem? (show ReferenceResiduals.block50[6]?=some panel857.left from rfl)),
  ReferenceTrajectory.rightBlock103_subset (List.mem_of_getElem? (show ReferenceResiduals.block103[13]?=some panel857.right from rfl))⟩
theorem valid858 : ValidPanel panel858 := ⟨modelCheck858,residualCheck858,
  ReferenceTrajectory.leftBlock50_subset (List.mem_of_getElem? (show ReferenceResiduals.block50[6]?=some panel858.left from rfl)),
  ReferenceTrajectory.rightBlock103_subset (List.mem_of_getElem? (show ReferenceResiduals.block103[12]?=some panel858.right from rfl))⟩
theorem valid859 : ValidPanel panel859 := ⟨modelCheck859,residualCheck859,
  ReferenceTrajectory.leftBlock50_subset (List.mem_of_getElem? (show ReferenceResiduals.block50[7]?=some panel859.left from rfl)),
  ReferenceTrajectory.rightBlock103_subset (List.mem_of_getElem? (show ReferenceResiduals.block103[11]?=some panel859.right from rfl))⟩
theorem valid860 : ValidPanel panel860 := ⟨modelCheck860,residualCheck860,
  ReferenceTrajectory.leftBlock50_subset (List.mem_of_getElem? (show ReferenceResiduals.block50[7]?=some panel860.left from rfl)),
  ReferenceTrajectory.rightBlock103_subset (List.mem_of_getElem? (show ReferenceResiduals.block103[10]?=some panel860.right from rfl))⟩
theorem valid861 : ValidPanel panel861 := ⟨modelCheck861,residualCheck861,
  ReferenceTrajectory.leftBlock50_subset (List.mem_of_getElem? (show ReferenceResiduals.block50[8]?=some panel861.left from rfl)),
  ReferenceTrajectory.rightBlock103_subset (List.mem_of_getElem? (show ReferenceResiduals.block103[9]?=some panel861.right from rfl))⟩
theorem valid862 : ValidPanel panel862 := ⟨modelCheck862,residualCheck862,
  ReferenceTrajectory.leftBlock50_subset (List.mem_of_getElem? (show ReferenceResiduals.block50[8]?=some panel862.left from rfl)),
  ReferenceTrajectory.rightBlock103_subset (List.mem_of_getElem? (show ReferenceResiduals.block103[8]?=some panel862.right from rfl))⟩
theorem valid863 : ValidPanel panel863 := ⟨modelCheck863,residualCheck863,
  ReferenceTrajectory.leftBlock50_subset (List.mem_of_getElem? (show ReferenceResiduals.block50[9]?=some panel863.left from rfl)),
  ReferenceTrajectory.rightBlock103_subset (List.mem_of_getElem? (show ReferenceResiduals.block103[7]?=some panel863.right from rfl))⟩
theorem validBlock26 : ∀ p∈block26,ValidPanel p := by
  simp only [block26,List.forall_mem_cons]
  exact ⟨valid832,⟨valid833,⟨valid834,⟨valid835,⟨valid836,⟨valid837,⟨valid838,⟨valid839,⟨valid840,⟨valid841,⟨valid842,⟨valid843,⟨valid844,⟨valid845,⟨valid846,⟨valid847,⟨valid848,⟨valid849,⟨valid850,⟨valid851,⟨valid852,⟨valid853,⟨valid854,⟨valid855,⟨valid856,⟨valid857,⟨valid858,⟨valid859,⟨valid860,⟨valid861,⟨valid862,⟨valid863,(by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end «2610.05164v2».Certificates.Compact.ContactValues

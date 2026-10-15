import «2610.05164v2».Certificates.Compact.ContactBatches.Batch025
import «2610.05164v2».Certificates.Compact.ContactCoverage
import «2610.05164v2».Certificates.Compact.ReferenceTrajectoryIndex

/-!
Article: 2610.05164v2, Section 4.1.
Correspondence025.
Use: `«2610.05164v2».Certificates.Compact.ContactValues.validBlock25` feeds
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
theorem valid800 : ValidPanel panel800 := ⟨modelCheck800,residualCheck800,
  ReferenceTrajectory.leftBlock47_subset (List.mem_of_getElem? (show ReferenceResiduals.block47[0]?=some panel800.left from rfl)),
  ReferenceTrajectory.rightBlock107_subset (List.mem_of_getElem? (show ReferenceResiduals.block107[6]?=some panel800.right from rfl))⟩
theorem valid801 : ValidPanel panel801 := ⟨modelCheck801,residualCheck801,
  ReferenceTrajectory.leftBlock47_subset (List.mem_of_getElem? (show ReferenceResiduals.block47[1]?=some panel801.left from rfl)),
  ReferenceTrajectory.rightBlock107_subset (List.mem_of_getElem? (show ReferenceResiduals.block107[5]?=some panel801.right from rfl))⟩
theorem valid802 : ValidPanel panel802 := ⟨modelCheck802,residualCheck802,
  ReferenceTrajectory.leftBlock47_subset (List.mem_of_getElem? (show ReferenceResiduals.block47[2]?=some panel802.left from rfl)),
  ReferenceTrajectory.rightBlock107_subset (List.mem_of_getElem? (show ReferenceResiduals.block107[4]?=some panel802.right from rfl))⟩
theorem valid803 : ValidPanel panel803 := ⟨modelCheck803,residualCheck803,
  ReferenceTrajectory.leftBlock47_subset (List.mem_of_getElem? (show ReferenceResiduals.block47[3]?=some panel803.left from rfl)),
  ReferenceTrajectory.rightBlock107_subset (List.mem_of_getElem? (show ReferenceResiduals.block107[3]?=some panel803.right from rfl))⟩
theorem valid804 : ValidPanel panel804 := ⟨modelCheck804,residualCheck804,
  ReferenceTrajectory.leftBlock47_subset (List.mem_of_getElem? (show ReferenceResiduals.block47[4]?=some panel804.left from rfl)),
  ReferenceTrajectory.rightBlock107_subset (List.mem_of_getElem? (show ReferenceResiduals.block107[2]?=some panel804.right from rfl))⟩
theorem valid805 : ValidPanel panel805 := ⟨modelCheck805,residualCheck805,
  ReferenceTrajectory.leftBlock47_subset (List.mem_of_getElem? (show ReferenceResiduals.block47[5]?=some panel805.left from rfl)),
  ReferenceTrajectory.rightBlock107_subset (List.mem_of_getElem? (show ReferenceResiduals.block107[1]?=some panel805.right from rfl))⟩
theorem valid806 : ValidPanel panel806 := ⟨modelCheck806,residualCheck806,
  ReferenceTrajectory.leftBlock47_subset (List.mem_of_getElem? (show ReferenceResiduals.block47[6]?=some panel806.left from rfl)),
  ReferenceTrajectory.rightBlock107_subset (List.mem_of_getElem? (show ReferenceResiduals.block107[0]?=some panel806.right from rfl))⟩
theorem valid807 : ValidPanel panel807 := ⟨modelCheck807,residualCheck807,
  ReferenceTrajectory.leftBlock47_subset (List.mem_of_getElem? (show ReferenceResiduals.block47[7]?=some panel807.left from rfl)),
  ReferenceTrajectory.rightBlock106_subset (List.mem_of_getElem? (show ReferenceResiduals.block106[15]?=some panel807.right from rfl))⟩
theorem valid808 : ValidPanel panel808 := ⟨modelCheck808,residualCheck808,
  ReferenceTrajectory.leftBlock47_subset (List.mem_of_getElem? (show ReferenceResiduals.block47[8]?=some panel808.left from rfl)),
  ReferenceTrajectory.rightBlock106_subset (List.mem_of_getElem? (show ReferenceResiduals.block106[14]?=some panel808.right from rfl))⟩
theorem valid809 : ValidPanel panel809 := ⟨modelCheck809,residualCheck809,
  ReferenceTrajectory.leftBlock47_subset (List.mem_of_getElem? (show ReferenceResiduals.block47[9]?=some panel809.left from rfl)),
  ReferenceTrajectory.rightBlock106_subset (List.mem_of_getElem? (show ReferenceResiduals.block106[13]?=some panel809.right from rfl))⟩
theorem valid810 : ValidPanel panel810 := ⟨modelCheck810,residualCheck810,
  ReferenceTrajectory.leftBlock47_subset (List.mem_of_getElem? (show ReferenceResiduals.block47[10]?=some panel810.left from rfl)),
  ReferenceTrajectory.rightBlock106_subset (List.mem_of_getElem? (show ReferenceResiduals.block106[12]?=some panel810.right from rfl))⟩
theorem valid811 : ValidPanel panel811 := ⟨modelCheck811,residualCheck811,
  ReferenceTrajectory.leftBlock47_subset (List.mem_of_getElem? (show ReferenceResiduals.block47[11]?=some panel811.left from rfl)),
  ReferenceTrajectory.rightBlock106_subset (List.mem_of_getElem? (show ReferenceResiduals.block106[11]?=some panel811.right from rfl))⟩
theorem valid812 : ValidPanel panel812 := ⟨modelCheck812,residualCheck812,
  ReferenceTrajectory.leftBlock47_subset (List.mem_of_getElem? (show ReferenceResiduals.block47[12]?=some panel812.left from rfl)),
  ReferenceTrajectory.rightBlock106_subset (List.mem_of_getElem? (show ReferenceResiduals.block106[10]?=some panel812.right from rfl))⟩
theorem valid813 : ValidPanel panel813 := ⟨modelCheck813,residualCheck813,
  ReferenceTrajectory.leftBlock47_subset (List.mem_of_getElem? (show ReferenceResiduals.block47[13]?=some panel813.left from rfl)),
  ReferenceTrajectory.rightBlock106_subset (List.mem_of_getElem? (show ReferenceResiduals.block106[9]?=some panel813.right from rfl))⟩
theorem valid814 : ValidPanel panel814 := ⟨modelCheck814,residualCheck814,
  ReferenceTrajectory.leftBlock47_subset (List.mem_of_getElem? (show ReferenceResiduals.block47[14]?=some panel814.left from rfl)),
  ReferenceTrajectory.rightBlock106_subset (List.mem_of_getElem? (show ReferenceResiduals.block106[8]?=some panel814.right from rfl))⟩
theorem valid815 : ValidPanel panel815 := ⟨modelCheck815,residualCheck815,
  ReferenceTrajectory.leftBlock47_subset (List.mem_of_getElem? (show ReferenceResiduals.block47[15]?=some panel815.left from rfl)),
  ReferenceTrajectory.rightBlock106_subset (List.mem_of_getElem? (show ReferenceResiduals.block106[7]?=some panel815.right from rfl))⟩
theorem valid816 : ValidPanel panel816 := ⟨modelCheck816,residualCheck816,
  ReferenceTrajectory.leftBlock48_subset (List.mem_of_getElem? (show ReferenceResiduals.block48[0]?=some panel816.left from rfl)),
  ReferenceTrajectory.rightBlock106_subset (List.mem_of_getElem? (show ReferenceResiduals.block106[6]?=some panel816.right from rfl))⟩
theorem valid817 : ValidPanel panel817 := ⟨modelCheck817,residualCheck817,
  ReferenceTrajectory.leftBlock48_subset (List.mem_of_getElem? (show ReferenceResiduals.block48[1]?=some panel817.left from rfl)),
  ReferenceTrajectory.rightBlock106_subset (List.mem_of_getElem? (show ReferenceResiduals.block106[5]?=some panel817.right from rfl))⟩
theorem valid818 : ValidPanel panel818 := ⟨modelCheck818,residualCheck818,
  ReferenceTrajectory.leftBlock48_subset (List.mem_of_getElem? (show ReferenceResiduals.block48[2]?=some panel818.left from rfl)),
  ReferenceTrajectory.rightBlock106_subset (List.mem_of_getElem? (show ReferenceResiduals.block106[4]?=some panel818.right from rfl))⟩
theorem valid819 : ValidPanel panel819 := ⟨modelCheck819,residualCheck819,
  ReferenceTrajectory.leftBlock48_subset (List.mem_of_getElem? (show ReferenceResiduals.block48[3]?=some panel819.left from rfl)),
  ReferenceTrajectory.rightBlock106_subset (List.mem_of_getElem? (show ReferenceResiduals.block106[3]?=some panel819.right from rfl))⟩
theorem valid820 : ValidPanel panel820 := ⟨modelCheck820,residualCheck820,
  ReferenceTrajectory.leftBlock48_subset (List.mem_of_getElem? (show ReferenceResiduals.block48[4]?=some panel820.left from rfl)),
  ReferenceTrajectory.rightBlock106_subset (List.mem_of_getElem? (show ReferenceResiduals.block106[2]?=some panel820.right from rfl))⟩
theorem valid821 : ValidPanel panel821 := ⟨modelCheck821,residualCheck821,
  ReferenceTrajectory.leftBlock48_subset (List.mem_of_getElem? (show ReferenceResiduals.block48[5]?=some panel821.left from rfl)),
  ReferenceTrajectory.rightBlock106_subset (List.mem_of_getElem? (show ReferenceResiduals.block106[1]?=some panel821.right from rfl))⟩
theorem valid822 : ValidPanel panel822 := ⟨modelCheck822,residualCheck822,
  ReferenceTrajectory.leftBlock48_subset (List.mem_of_getElem? (show ReferenceResiduals.block48[6]?=some panel822.left from rfl)),
  ReferenceTrajectory.rightBlock106_subset (List.mem_of_getElem? (show ReferenceResiduals.block106[0]?=some panel822.right from rfl))⟩
theorem valid823 : ValidPanel panel823 := ⟨modelCheck823,residualCheck823,
  ReferenceTrajectory.leftBlock48_subset (List.mem_of_getElem? (show ReferenceResiduals.block48[7]?=some panel823.left from rfl)),
  ReferenceTrajectory.rightBlock105_subset (List.mem_of_getElem? (show ReferenceResiduals.block105[15]?=some panel823.right from rfl))⟩
theorem valid824 : ValidPanel panel824 := ⟨modelCheck824,residualCheck824,
  ReferenceTrajectory.leftBlock48_subset (List.mem_of_getElem? (show ReferenceResiduals.block48[8]?=some panel824.left from rfl)),
  ReferenceTrajectory.rightBlock105_subset (List.mem_of_getElem? (show ReferenceResiduals.block105[14]?=some panel824.right from rfl))⟩
theorem valid825 : ValidPanel panel825 := ⟨modelCheck825,residualCheck825,
  ReferenceTrajectory.leftBlock48_subset (List.mem_of_getElem? (show ReferenceResiduals.block48[9]?=some panel825.left from rfl)),
  ReferenceTrajectory.rightBlock105_subset (List.mem_of_getElem? (show ReferenceResiduals.block105[13]?=some panel825.right from rfl))⟩
theorem valid826 : ValidPanel panel826 := ⟨modelCheck826,residualCheck826,
  ReferenceTrajectory.leftBlock48_subset (List.mem_of_getElem? (show ReferenceResiduals.block48[10]?=some panel826.left from rfl)),
  ReferenceTrajectory.rightBlock105_subset (List.mem_of_getElem? (show ReferenceResiduals.block105[12]?=some panel826.right from rfl))⟩
theorem valid827 : ValidPanel panel827 := ⟨modelCheck827,residualCheck827,
  ReferenceTrajectory.leftBlock48_subset (List.mem_of_getElem? (show ReferenceResiduals.block48[11]?=some panel827.left from rfl)),
  ReferenceTrajectory.rightBlock105_subset (List.mem_of_getElem? (show ReferenceResiduals.block105[11]?=some panel827.right from rfl))⟩
theorem valid828 : ValidPanel panel828 := ⟨modelCheck828,residualCheck828,
  ReferenceTrajectory.leftBlock48_subset (List.mem_of_getElem? (show ReferenceResiduals.block48[12]?=some panel828.left from rfl)),
  ReferenceTrajectory.rightBlock105_subset (List.mem_of_getElem? (show ReferenceResiduals.block105[10]?=some panel828.right from rfl))⟩
theorem valid829 : ValidPanel panel829 := ⟨modelCheck829,residualCheck829,
  ReferenceTrajectory.leftBlock48_subset (List.mem_of_getElem? (show ReferenceResiduals.block48[13]?=some panel829.left from rfl)),
  ReferenceTrajectory.rightBlock105_subset (List.mem_of_getElem? (show ReferenceResiduals.block105[9]?=some panel829.right from rfl))⟩
theorem valid830 : ValidPanel panel830 := ⟨modelCheck830,residualCheck830,
  ReferenceTrajectory.leftBlock48_subset (List.mem_of_getElem? (show ReferenceResiduals.block48[14]?=some panel830.left from rfl)),
  ReferenceTrajectory.rightBlock105_subset (List.mem_of_getElem? (show ReferenceResiduals.block105[8]?=some panel830.right from rfl))⟩
theorem valid831 : ValidPanel panel831 := ⟨modelCheck831,residualCheck831,
  ReferenceTrajectory.leftBlock48_subset (List.mem_of_getElem? (show ReferenceResiduals.block48[15]?=some panel831.left from rfl)),
  ReferenceTrajectory.rightBlock105_subset (List.mem_of_getElem? (show ReferenceResiduals.block105[7]?=some panel831.right from rfl))⟩
theorem validBlock25 : ∀ p∈block25,ValidPanel p := by
  simp only [block25,List.forall_mem_cons]
  exact ⟨valid800,⟨valid801,⟨valid802,⟨valid803,⟨valid804,⟨valid805,⟨valid806,⟨valid807,⟨valid808,⟨valid809,⟨valid810,⟨valid811,⟨valid812,⟨valid813,⟨valid814,⟨valid815,⟨valid816,⟨valid817,⟨valid818,⟨valid819,⟨valid820,⟨valid821,⟨valid822,⟨valid823,⟨valid824,⟨valid825,⟨valid826,⟨valid827,⟨valid828,⟨valid829,⟨valid830,⟨valid831,(by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end «2610.05164v2».Certificates.Compact.ContactValues

import chebyshev2.Certificates.Compact.ContactBatches.Batch027
import chebyshev2.Certificates.Compact.ContactCoverage
import chebyshev2.Certificates.Compact.ReferenceTrajectoryIndex

/-!
Article: chebyshev2, Section 4.1.
Correspondence027.
Use: `chebyshev2.Certificates.Compact.ContactValues.validBlock27` feeds
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
theorem valid864 : ValidPanel panel864 := ⟨modelCheck864,residualCheck864,
  ReferenceTrajectory.leftBlock50_subset (List.mem_of_getElem? (show ReferenceResiduals.block50[9]?=some panel864.left from rfl)),
  ReferenceTrajectory.rightBlock103_subset (List.mem_of_getElem? (show ReferenceResiduals.block103[6]?=some panel864.right from rfl))⟩
theorem valid865 : ValidPanel panel865 := ⟨modelCheck865,residualCheck865,
  ReferenceTrajectory.leftBlock50_subset (List.mem_of_getElem? (show ReferenceResiduals.block50[10]?=some panel865.left from rfl)),
  ReferenceTrajectory.rightBlock103_subset (List.mem_of_getElem? (show ReferenceResiduals.block103[5]?=some panel865.right from rfl))⟩
theorem valid866 : ValidPanel panel866 := ⟨modelCheck866,residualCheck866,
  ReferenceTrajectory.leftBlock50_subset (List.mem_of_getElem? (show ReferenceResiduals.block50[10]?=some panel866.left from rfl)),
  ReferenceTrajectory.rightBlock103_subset (List.mem_of_getElem? (show ReferenceResiduals.block103[4]?=some panel866.right from rfl))⟩
theorem valid867 : ValidPanel panel867 := ⟨modelCheck867,residualCheck867,
  ReferenceTrajectory.leftBlock50_subset (List.mem_of_getElem? (show ReferenceResiduals.block50[11]?=some panel867.left from rfl)),
  ReferenceTrajectory.rightBlock103_subset (List.mem_of_getElem? (show ReferenceResiduals.block103[3]?=some panel867.right from rfl))⟩
theorem valid868 : ValidPanel panel868 := ⟨modelCheck868,residualCheck868,
  ReferenceTrajectory.leftBlock50_subset (List.mem_of_getElem? (show ReferenceResiduals.block50[11]?=some panel868.left from rfl)),
  ReferenceTrajectory.rightBlock103_subset (List.mem_of_getElem? (show ReferenceResiduals.block103[2]?=some panel868.right from rfl))⟩
theorem valid869 : ValidPanel panel869 := ⟨modelCheck869,residualCheck869,
  ReferenceTrajectory.leftBlock50_subset (List.mem_of_getElem? (show ReferenceResiduals.block50[12]?=some panel869.left from rfl)),
  ReferenceTrajectory.rightBlock103_subset (List.mem_of_getElem? (show ReferenceResiduals.block103[1]?=some panel869.right from rfl))⟩
theorem valid870 : ValidPanel panel870 := ⟨modelCheck870,residualCheck870,
  ReferenceTrajectory.leftBlock50_subset (List.mem_of_getElem? (show ReferenceResiduals.block50[12]?=some panel870.left from rfl)),
  ReferenceTrajectory.rightBlock103_subset (List.mem_of_getElem? (show ReferenceResiduals.block103[0]?=some panel870.right from rfl))⟩
theorem valid871 : ValidPanel panel871 := ⟨modelCheck871,residualCheck871,
  ReferenceTrajectory.leftBlock50_subset (List.mem_of_getElem? (show ReferenceResiduals.block50[13]?=some panel871.left from rfl)),
  ReferenceTrajectory.rightBlock102_subset (List.mem_of_getElem? (show ReferenceResiduals.block102[15]?=some panel871.right from rfl))⟩
theorem valid872 : ValidPanel panel872 := ⟨modelCheck872,residualCheck872,
  ReferenceTrajectory.leftBlock50_subset (List.mem_of_getElem? (show ReferenceResiduals.block50[13]?=some panel872.left from rfl)),
  ReferenceTrajectory.rightBlock102_subset (List.mem_of_getElem? (show ReferenceResiduals.block102[14]?=some panel872.right from rfl))⟩
theorem valid873 : ValidPanel panel873 := ⟨modelCheck873,residualCheck873,
  ReferenceTrajectory.leftBlock50_subset (List.mem_of_getElem? (show ReferenceResiduals.block50[14]?=some panel873.left from rfl)),
  ReferenceTrajectory.rightBlock102_subset (List.mem_of_getElem? (show ReferenceResiduals.block102[13]?=some panel873.right from rfl))⟩
theorem valid874 : ValidPanel panel874 := ⟨modelCheck874,residualCheck874,
  ReferenceTrajectory.leftBlock50_subset (List.mem_of_getElem? (show ReferenceResiduals.block50[14]?=some panel874.left from rfl)),
  ReferenceTrajectory.rightBlock102_subset (List.mem_of_getElem? (show ReferenceResiduals.block102[12]?=some panel874.right from rfl))⟩
theorem valid875 : ValidPanel panel875 := ⟨modelCheck875,residualCheck875,
  ReferenceTrajectory.leftBlock50_subset (List.mem_of_getElem? (show ReferenceResiduals.block50[15]?=some panel875.left from rfl)),
  ReferenceTrajectory.rightBlock102_subset (List.mem_of_getElem? (show ReferenceResiduals.block102[11]?=some panel875.right from rfl))⟩
theorem valid876 : ValidPanel panel876 := ⟨modelCheck876,residualCheck876,
  ReferenceTrajectory.leftBlock50_subset (List.mem_of_getElem? (show ReferenceResiduals.block50[15]?=some panel876.left from rfl)),
  ReferenceTrajectory.rightBlock102_subset (List.mem_of_getElem? (show ReferenceResiduals.block102[10]?=some panel876.right from rfl))⟩
theorem valid877 : ValidPanel panel877 := ⟨modelCheck877,residualCheck877,
  ReferenceTrajectory.leftBlock51_subset (List.mem_of_getElem? (show ReferenceResiduals.block51[0]?=some panel877.left from rfl)),
  ReferenceTrajectory.rightBlock102_subset (List.mem_of_getElem? (show ReferenceResiduals.block102[9]?=some panel877.right from rfl))⟩
theorem valid878 : ValidPanel panel878 := ⟨modelCheck878,residualCheck878,
  ReferenceTrajectory.leftBlock51_subset (List.mem_of_getElem? (show ReferenceResiduals.block51[0]?=some panel878.left from rfl)),
  ReferenceTrajectory.rightBlock102_subset (List.mem_of_getElem? (show ReferenceResiduals.block102[8]?=some panel878.right from rfl))⟩
theorem valid879 : ValidPanel panel879 := ⟨modelCheck879,residualCheck879,
  ReferenceTrajectory.leftBlock51_subset (List.mem_of_getElem? (show ReferenceResiduals.block51[1]?=some panel879.left from rfl)),
  ReferenceTrajectory.rightBlock102_subset (List.mem_of_getElem? (show ReferenceResiduals.block102[7]?=some panel879.right from rfl))⟩
theorem valid880 : ValidPanel panel880 := ⟨modelCheck880,residualCheck880,
  ReferenceTrajectory.leftBlock51_subset (List.mem_of_getElem? (show ReferenceResiduals.block51[1]?=some panel880.left from rfl)),
  ReferenceTrajectory.rightBlock102_subset (List.mem_of_getElem? (show ReferenceResiduals.block102[6]?=some panel880.right from rfl))⟩
theorem valid881 : ValidPanel panel881 := ⟨modelCheck881,residualCheck881,
  ReferenceTrajectory.leftBlock51_subset (List.mem_of_getElem? (show ReferenceResiduals.block51[2]?=some panel881.left from rfl)),
  ReferenceTrajectory.rightBlock102_subset (List.mem_of_getElem? (show ReferenceResiduals.block102[5]?=some panel881.right from rfl))⟩
theorem valid882 : ValidPanel panel882 := ⟨modelCheck882,residualCheck882,
  ReferenceTrajectory.leftBlock51_subset (List.mem_of_getElem? (show ReferenceResiduals.block51[3]?=some panel882.left from rfl)),
  ReferenceTrajectory.rightBlock102_subset (List.mem_of_getElem? (show ReferenceResiduals.block102[4]?=some panel882.right from rfl))⟩
theorem valid883 : ValidPanel panel883 := ⟨modelCheck883,residualCheck883,
  ReferenceTrajectory.leftBlock51_subset (List.mem_of_getElem? (show ReferenceResiduals.block51[4]?=some panel883.left from rfl)),
  ReferenceTrajectory.rightBlock102_subset (List.mem_of_getElem? (show ReferenceResiduals.block102[3]?=some panel883.right from rfl))⟩
theorem valid884 : ValidPanel panel884 := ⟨modelCheck884,residualCheck884,
  ReferenceTrajectory.leftBlock51_subset (List.mem_of_getElem? (show ReferenceResiduals.block51[5]?=some panel884.left from rfl)),
  ReferenceTrajectory.rightBlock102_subset (List.mem_of_getElem? (show ReferenceResiduals.block102[2]?=some panel884.right from rfl))⟩
theorem valid885 : ValidPanel panel885 := ⟨modelCheck885,residualCheck885,
  ReferenceTrajectory.leftBlock51_subset (List.mem_of_getElem? (show ReferenceResiduals.block51[6]?=some panel885.left from rfl)),
  ReferenceTrajectory.rightBlock102_subset (List.mem_of_getElem? (show ReferenceResiduals.block102[1]?=some panel885.right from rfl))⟩
theorem valid886 : ValidPanel panel886 := ⟨modelCheck886,residualCheck886,
  ReferenceTrajectory.leftBlock51_subset (List.mem_of_getElem? (show ReferenceResiduals.block51[7]?=some panel886.left from rfl)),
  ReferenceTrajectory.rightBlock102_subset (List.mem_of_getElem? (show ReferenceResiduals.block102[0]?=some panel886.right from rfl))⟩
theorem valid887 : ValidPanel panel887 := ⟨modelCheck887,residualCheck887,
  ReferenceTrajectory.leftBlock51_subset (List.mem_of_getElem? (show ReferenceResiduals.block51[8]?=some panel887.left from rfl)),
  ReferenceTrajectory.rightBlock101_subset (List.mem_of_getElem? (show ReferenceResiduals.block101[15]?=some panel887.right from rfl))⟩
theorem valid888 : ValidPanel panel888 := ⟨modelCheck888,residualCheck888,
  ReferenceTrajectory.leftBlock51_subset (List.mem_of_getElem? (show ReferenceResiduals.block51[9]?=some panel888.left from rfl)),
  ReferenceTrajectory.rightBlock101_subset (List.mem_of_getElem? (show ReferenceResiduals.block101[14]?=some panel888.right from rfl))⟩
theorem valid889 : ValidPanel panel889 := ⟨modelCheck889,residualCheck889,
  ReferenceTrajectory.leftBlock51_subset (List.mem_of_getElem? (show ReferenceResiduals.block51[10]?=some panel889.left from rfl)),
  ReferenceTrajectory.rightBlock101_subset (List.mem_of_getElem? (show ReferenceResiduals.block101[13]?=some panel889.right from rfl))⟩
theorem valid890 : ValidPanel panel890 := ⟨modelCheck890,residualCheck890,
  ReferenceTrajectory.leftBlock51_subset (List.mem_of_getElem? (show ReferenceResiduals.block51[11]?=some panel890.left from rfl)),
  ReferenceTrajectory.rightBlock101_subset (List.mem_of_getElem? (show ReferenceResiduals.block101[12]?=some panel890.right from rfl))⟩
theorem valid891 : ValidPanel panel891 := ⟨modelCheck891,residualCheck891,
  ReferenceTrajectory.leftBlock51_subset (List.mem_of_getElem? (show ReferenceResiduals.block51[12]?=some panel891.left from rfl)),
  ReferenceTrajectory.rightBlock101_subset (List.mem_of_getElem? (show ReferenceResiduals.block101[11]?=some panel891.right from rfl))⟩
theorem valid892 : ValidPanel panel892 := ⟨modelCheck892,residualCheck892,
  ReferenceTrajectory.leftBlock51_subset (List.mem_of_getElem? (show ReferenceResiduals.block51[13]?=some panel892.left from rfl)),
  ReferenceTrajectory.rightBlock101_subset (List.mem_of_getElem? (show ReferenceResiduals.block101[10]?=some panel892.right from rfl))⟩
theorem valid893 : ValidPanel panel893 := ⟨modelCheck893,residualCheck893,
  ReferenceTrajectory.leftBlock51_subset (List.mem_of_getElem? (show ReferenceResiduals.block51[14]?=some panel893.left from rfl)),
  ReferenceTrajectory.rightBlock101_subset (List.mem_of_getElem? (show ReferenceResiduals.block101[9]?=some panel893.right from rfl))⟩
theorem valid894 : ValidPanel panel894 := ⟨modelCheck894,residualCheck894,
  ReferenceTrajectory.leftBlock51_subset (List.mem_of_getElem? (show ReferenceResiduals.block51[15]?=some panel894.left from rfl)),
  ReferenceTrajectory.rightBlock101_subset (List.mem_of_getElem? (show ReferenceResiduals.block101[8]?=some panel894.right from rfl))⟩
theorem valid895 : ValidPanel panel895 := ⟨modelCheck895,residualCheck895,
  ReferenceTrajectory.leftBlock52_subset (List.mem_of_getElem? (show ReferenceResiduals.block52[0]?=some panel895.left from rfl)),
  ReferenceTrajectory.rightBlock101_subset (List.mem_of_getElem? (show ReferenceResiduals.block101[7]?=some panel895.right from rfl))⟩
theorem validBlock27 : ∀ p∈block27,ValidPanel p := by
  simp only [block27,List.forall_mem_cons]
  exact ⟨valid864,⟨valid865,⟨valid866,⟨valid867,⟨valid868,⟨valid869,⟨valid870,⟨valid871,⟨valid872,⟨valid873,⟨valid874,⟨valid875,⟨valid876,⟨valid877,⟨valid878,⟨valid879,⟨valid880,⟨valid881,⟨valid882,⟨valid883,⟨valid884,⟨valid885,⟨valid886,⟨valid887,⟨valid888,⟨valid889,⟨valid890,⟨valid891,⟨valid892,⟨valid893,⟨valid894,⟨valid895,(by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end chebyshev2.Certificates.Compact.ContactValues

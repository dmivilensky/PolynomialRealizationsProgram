import chebyshev2.Certificates.Compact.ContactBatches.Batch032
import chebyshev2.Certificates.Compact.ContactCoverage
import chebyshev2.Certificates.Compact.ReferenceTrajectoryIndex

/-!
Article: chebyshev2, Section 4.1.
Correspondence032.
Use: `chebyshev2.Certificates.Compact.ContactValues.validBlock32` feeds
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
theorem valid1024 : ValidPanel panel1024 := ⟨modelCheck1024,residualCheck1024,
  ReferenceTrajectory.leftBlock60_subset (List.mem_of_getElem? (show ReferenceResiduals.block60[1]?=some panel1024.left from rfl)),
  ReferenceTrajectory.rightBlock93_subset (List.mem_of_getElem? (show ReferenceResiduals.block93[6]?=some panel1024.right from rfl))⟩
theorem valid1025 : ValidPanel panel1025 := ⟨modelCheck1025,residualCheck1025,
  ReferenceTrajectory.leftBlock60_subset (List.mem_of_getElem? (show ReferenceResiduals.block60[2]?=some panel1025.left from rfl)),
  ReferenceTrajectory.rightBlock93_subset (List.mem_of_getElem? (show ReferenceResiduals.block93[5]?=some panel1025.right from rfl))⟩
theorem valid1026 : ValidPanel panel1026 := ⟨modelCheck1026,residualCheck1026,
  ReferenceTrajectory.leftBlock60_subset (List.mem_of_getElem? (show ReferenceResiduals.block60[3]?=some panel1026.left from rfl)),
  ReferenceTrajectory.rightBlock93_subset (List.mem_of_getElem? (show ReferenceResiduals.block93[4]?=some panel1026.right from rfl))⟩
theorem valid1027 : ValidPanel panel1027 := ⟨modelCheck1027,residualCheck1027,
  ReferenceTrajectory.leftBlock60_subset (List.mem_of_getElem? (show ReferenceResiduals.block60[4]?=some panel1027.left from rfl)),
  ReferenceTrajectory.rightBlock93_subset (List.mem_of_getElem? (show ReferenceResiduals.block93[3]?=some panel1027.right from rfl))⟩
theorem valid1028 : ValidPanel panel1028 := ⟨modelCheck1028,residualCheck1028,
  ReferenceTrajectory.leftBlock60_subset (List.mem_of_getElem? (show ReferenceResiduals.block60[5]?=some panel1028.left from rfl)),
  ReferenceTrajectory.rightBlock93_subset (List.mem_of_getElem? (show ReferenceResiduals.block93[2]?=some panel1028.right from rfl))⟩
theorem valid1029 : ValidPanel panel1029 := ⟨modelCheck1029,residualCheck1029,
  ReferenceTrajectory.leftBlock60_subset (List.mem_of_getElem? (show ReferenceResiduals.block60[6]?=some panel1029.left from rfl)),
  ReferenceTrajectory.rightBlock93_subset (List.mem_of_getElem? (show ReferenceResiduals.block93[1]?=some panel1029.right from rfl))⟩
theorem valid1030 : ValidPanel panel1030 := ⟨modelCheck1030,residualCheck1030,
  ReferenceTrajectory.leftBlock60_subset (List.mem_of_getElem? (show ReferenceResiduals.block60[7]?=some panel1030.left from rfl)),
  ReferenceTrajectory.rightBlock93_subset (List.mem_of_getElem? (show ReferenceResiduals.block93[0]?=some panel1030.right from rfl))⟩
theorem valid1031 : ValidPanel panel1031 := ⟨modelCheck1031,residualCheck1031,
  ReferenceTrajectory.leftBlock60_subset (List.mem_of_getElem? (show ReferenceResiduals.block60[8]?=some panel1031.left from rfl)),
  ReferenceTrajectory.rightBlock92_subset (List.mem_of_getElem? (show ReferenceResiduals.block92[15]?=some panel1031.right from rfl))⟩
theorem valid1032 : ValidPanel panel1032 := ⟨modelCheck1032,residualCheck1032,
  ReferenceTrajectory.leftBlock60_subset (List.mem_of_getElem? (show ReferenceResiduals.block60[9]?=some panel1032.left from rfl)),
  ReferenceTrajectory.rightBlock92_subset (List.mem_of_getElem? (show ReferenceResiduals.block92[14]?=some panel1032.right from rfl))⟩
theorem valid1033 : ValidPanel panel1033 := ⟨modelCheck1033,residualCheck1033,
  ReferenceTrajectory.leftBlock60_subset (List.mem_of_getElem? (show ReferenceResiduals.block60[10]?=some panel1033.left from rfl)),
  ReferenceTrajectory.rightBlock92_subset (List.mem_of_getElem? (show ReferenceResiduals.block92[13]?=some panel1033.right from rfl))⟩
theorem valid1034 : ValidPanel panel1034 := ⟨modelCheck1034,residualCheck1034,
  ReferenceTrajectory.leftBlock60_subset (List.mem_of_getElem? (show ReferenceResiduals.block60[11]?=some panel1034.left from rfl)),
  ReferenceTrajectory.rightBlock92_subset (List.mem_of_getElem? (show ReferenceResiduals.block92[12]?=some panel1034.right from rfl))⟩
theorem valid1035 : ValidPanel panel1035 := ⟨modelCheck1035,residualCheck1035,
  ReferenceTrajectory.leftBlock60_subset (List.mem_of_getElem? (show ReferenceResiduals.block60[12]?=some panel1035.left from rfl)),
  ReferenceTrajectory.rightBlock92_subset (List.mem_of_getElem? (show ReferenceResiduals.block92[11]?=some panel1035.right from rfl))⟩
theorem valid1036 : ValidPanel panel1036 := ⟨modelCheck1036,residualCheck1036,
  ReferenceTrajectory.leftBlock60_subset (List.mem_of_getElem? (show ReferenceResiduals.block60[13]?=some panel1036.left from rfl)),
  ReferenceTrajectory.rightBlock92_subset (List.mem_of_getElem? (show ReferenceResiduals.block92[10]?=some panel1036.right from rfl))⟩
theorem valid1037 : ValidPanel panel1037 := ⟨modelCheck1037,residualCheck1037,
  ReferenceTrajectory.leftBlock60_subset (List.mem_of_getElem? (show ReferenceResiduals.block60[14]?=some panel1037.left from rfl)),
  ReferenceTrajectory.rightBlock92_subset (List.mem_of_getElem? (show ReferenceResiduals.block92[9]?=some panel1037.right from rfl))⟩
theorem valid1038 : ValidPanel panel1038 := ⟨modelCheck1038,residualCheck1038,
  ReferenceTrajectory.leftBlock60_subset (List.mem_of_getElem? (show ReferenceResiduals.block60[15]?=some panel1038.left from rfl)),
  ReferenceTrajectory.rightBlock92_subset (List.mem_of_getElem? (show ReferenceResiduals.block92[8]?=some panel1038.right from rfl))⟩
theorem valid1039 : ValidPanel panel1039 := ⟨modelCheck1039,residualCheck1039,
  ReferenceTrajectory.leftBlock61_subset (List.mem_of_getElem? (show ReferenceResiduals.block61[0]?=some panel1039.left from rfl)),
  ReferenceTrajectory.rightBlock92_subset (List.mem_of_getElem? (show ReferenceResiduals.block92[7]?=some panel1039.right from rfl))⟩
theorem valid1040 : ValidPanel panel1040 := ⟨modelCheck1040,residualCheck1040,
  ReferenceTrajectory.leftBlock61_subset (List.mem_of_getElem? (show ReferenceResiduals.block61[1]?=some panel1040.left from rfl)),
  ReferenceTrajectory.rightBlock92_subset (List.mem_of_getElem? (show ReferenceResiduals.block92[6]?=some panel1040.right from rfl))⟩
theorem valid1041 : ValidPanel panel1041 := ⟨modelCheck1041,residualCheck1041,
  ReferenceTrajectory.leftBlock61_subset (List.mem_of_getElem? (show ReferenceResiduals.block61[2]?=some panel1041.left from rfl)),
  ReferenceTrajectory.rightBlock92_subset (List.mem_of_getElem? (show ReferenceResiduals.block92[5]?=some panel1041.right from rfl))⟩
theorem valid1042 : ValidPanel panel1042 := ⟨modelCheck1042,residualCheck1042,
  ReferenceTrajectory.leftBlock61_subset (List.mem_of_getElem? (show ReferenceResiduals.block61[3]?=some panel1042.left from rfl)),
  ReferenceTrajectory.rightBlock92_subset (List.mem_of_getElem? (show ReferenceResiduals.block92[4]?=some panel1042.right from rfl))⟩
theorem valid1043 : ValidPanel panel1043 := ⟨modelCheck1043,residualCheck1043,
  ReferenceTrajectory.leftBlock61_subset (List.mem_of_getElem? (show ReferenceResiduals.block61[4]?=some panel1043.left from rfl)),
  ReferenceTrajectory.rightBlock92_subset (List.mem_of_getElem? (show ReferenceResiduals.block92[3]?=some panel1043.right from rfl))⟩
theorem valid1044 : ValidPanel panel1044 := ⟨modelCheck1044,residualCheck1044,
  ReferenceTrajectory.leftBlock61_subset (List.mem_of_getElem? (show ReferenceResiduals.block61[5]?=some panel1044.left from rfl)),
  ReferenceTrajectory.rightBlock92_subset (List.mem_of_getElem? (show ReferenceResiduals.block92[2]?=some panel1044.right from rfl))⟩
theorem valid1045 : ValidPanel panel1045 := ⟨modelCheck1045,residualCheck1045,
  ReferenceTrajectory.leftBlock61_subset (List.mem_of_getElem? (show ReferenceResiduals.block61[6]?=some panel1045.left from rfl)),
  ReferenceTrajectory.rightBlock92_subset (List.mem_of_getElem? (show ReferenceResiduals.block92[1]?=some panel1045.right from rfl))⟩
theorem valid1046 : ValidPanel panel1046 := ⟨modelCheck1046,residualCheck1046,
  ReferenceTrajectory.leftBlock61_subset (List.mem_of_getElem? (show ReferenceResiduals.block61[7]?=some panel1046.left from rfl)),
  ReferenceTrajectory.rightBlock92_subset (List.mem_of_getElem? (show ReferenceResiduals.block92[0]?=some panel1046.right from rfl))⟩
theorem valid1047 : ValidPanel panel1047 := ⟨modelCheck1047,residualCheck1047,
  ReferenceTrajectory.leftBlock61_subset (List.mem_of_getElem? (show ReferenceResiduals.block61[8]?=some panel1047.left from rfl)),
  ReferenceTrajectory.rightBlock91_subset (List.mem_of_getElem? (show ReferenceResiduals.block91[15]?=some panel1047.right from rfl))⟩
theorem valid1048 : ValidPanel panel1048 := ⟨modelCheck1048,residualCheck1048,
  ReferenceTrajectory.leftBlock61_subset (List.mem_of_getElem? (show ReferenceResiduals.block61[9]?=some panel1048.left from rfl)),
  ReferenceTrajectory.rightBlock91_subset (List.mem_of_getElem? (show ReferenceResiduals.block91[14]?=some panel1048.right from rfl))⟩
theorem valid1049 : ValidPanel panel1049 := ⟨modelCheck1049,residualCheck1049,
  ReferenceTrajectory.leftBlock61_subset (List.mem_of_getElem? (show ReferenceResiduals.block61[10]?=some panel1049.left from rfl)),
  ReferenceTrajectory.rightBlock91_subset (List.mem_of_getElem? (show ReferenceResiduals.block91[13]?=some panel1049.right from rfl))⟩
theorem valid1050 : ValidPanel panel1050 := ⟨modelCheck1050,residualCheck1050,
  ReferenceTrajectory.leftBlock61_subset (List.mem_of_getElem? (show ReferenceResiduals.block61[11]?=some panel1050.left from rfl)),
  ReferenceTrajectory.rightBlock91_subset (List.mem_of_getElem? (show ReferenceResiduals.block91[12]?=some panel1050.right from rfl))⟩
theorem valid1051 : ValidPanel panel1051 := ⟨modelCheck1051,residualCheck1051,
  ReferenceTrajectory.leftBlock61_subset (List.mem_of_getElem? (show ReferenceResiduals.block61[12]?=some panel1051.left from rfl)),
  ReferenceTrajectory.rightBlock91_subset (List.mem_of_getElem? (show ReferenceResiduals.block91[11]?=some panel1051.right from rfl))⟩
theorem valid1052 : ValidPanel panel1052 := ⟨modelCheck1052,residualCheck1052,
  ReferenceTrajectory.leftBlock61_subset (List.mem_of_getElem? (show ReferenceResiduals.block61[13]?=some panel1052.left from rfl)),
  ReferenceTrajectory.rightBlock91_subset (List.mem_of_getElem? (show ReferenceResiduals.block91[10]?=some panel1052.right from rfl))⟩
theorem valid1053 : ValidPanel panel1053 := ⟨modelCheck1053,residualCheck1053,
  ReferenceTrajectory.leftBlock61_subset (List.mem_of_getElem? (show ReferenceResiduals.block61[14]?=some panel1053.left from rfl)),
  ReferenceTrajectory.rightBlock91_subset (List.mem_of_getElem? (show ReferenceResiduals.block91[9]?=some panel1053.right from rfl))⟩
theorem valid1054 : ValidPanel panel1054 := ⟨modelCheck1054,residualCheck1054,
  ReferenceTrajectory.leftBlock61_subset (List.mem_of_getElem? (show ReferenceResiduals.block61[15]?=some panel1054.left from rfl)),
  ReferenceTrajectory.rightBlock91_subset (List.mem_of_getElem? (show ReferenceResiduals.block91[8]?=some panel1054.right from rfl))⟩
theorem valid1055 : ValidPanel panel1055 := ⟨modelCheck1055,residualCheck1055,
  ReferenceTrajectory.leftBlock62_subset (List.mem_of_getElem? (show ReferenceResiduals.block62[0]?=some panel1055.left from rfl)),
  ReferenceTrajectory.rightBlock91_subset (List.mem_of_getElem? (show ReferenceResiduals.block91[7]?=some panel1055.right from rfl))⟩
theorem validBlock32 : ∀ p∈block32,ValidPanel p := by
  simp only [block32,List.forall_mem_cons]
  exact ⟨valid1024,⟨valid1025,⟨valid1026,⟨valid1027,⟨valid1028,⟨valid1029,⟨valid1030,⟨valid1031,⟨valid1032,⟨valid1033,⟨valid1034,⟨valid1035,⟨valid1036,⟨valid1037,⟨valid1038,⟨valid1039,⟨valid1040,⟨valid1041,⟨valid1042,⟨valid1043,⟨valid1044,⟨valid1045,⟨valid1046,⟨valid1047,⟨valid1048,⟨valid1049,⟨valid1050,⟨valid1051,⟨valid1052,⟨valid1053,⟨valid1054,⟨valid1055,(by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end chebyshev2.Certificates.Compact.ContactValues

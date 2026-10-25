import chebyshev2.Certificates.Compact.AmplitudeBatches.Batch032
import chebyshev2.Certificates.Compact.ContactBatches.Correspondence032
import chebyshev2.Certificates.Compact.AmplitudeProof

/-!
Article: chebyshev2, Section 4.1.
Correspondence032.
Use: `chebyshev2.Certificates.Compact.AmplitudeValues.validBlock32` feeds
`chebyshev2.Certificates.Compact.AmplitudeValues.all_valid` (all valid).
Proof chain: `chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement` —
chebyshev2, Theorem 1.2, factor 1.000013; Unconditional uniform gain comparison with the retained
numerical factor.
-/
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 200000
set_option maxHeartbeats 0
namespace chebyshev2.Certificates.Compact.AmplitudeValues
open chebyshev2.Numerics.IntegerCertificate
theorem valid1024 : ValidPanel panel1024 := ⟨check1024,ContactValues.valid1024⟩
theorem valid1025 : ValidPanel panel1025 := ⟨check1025,ContactValues.valid1025⟩
theorem valid1026 : ValidPanel panel1026 := ⟨check1026,ContactValues.valid1026⟩
theorem valid1027 : ValidPanel panel1027 := ⟨check1027,ContactValues.valid1027⟩
theorem valid1028 : ValidPanel panel1028 := ⟨check1028,ContactValues.valid1028⟩
theorem valid1029 : ValidPanel panel1029 := ⟨check1029,ContactValues.valid1029⟩
theorem valid1030 : ValidPanel panel1030 := ⟨check1030,ContactValues.valid1030⟩
theorem valid1031 : ValidPanel panel1031 := ⟨check1031,ContactValues.valid1031⟩
theorem valid1032 : ValidPanel panel1032 := ⟨check1032,ContactValues.valid1032⟩
theorem valid1033 : ValidPanel panel1033 := ⟨check1033,ContactValues.valid1033⟩
theorem valid1034 : ValidPanel panel1034 := ⟨check1034,ContactValues.valid1034⟩
theorem valid1035 : ValidPanel panel1035 := ⟨check1035,ContactValues.valid1035⟩
theorem valid1036 : ValidPanel panel1036 := ⟨check1036,ContactValues.valid1036⟩
theorem valid1037 : ValidPanel panel1037 := ⟨check1037,ContactValues.valid1037⟩
theorem valid1038 : ValidPanel panel1038 := ⟨check1038,ContactValues.valid1038⟩
theorem valid1039 : ValidPanel panel1039 := ⟨check1039,ContactValues.valid1039⟩
theorem valid1040 : ValidPanel panel1040 := ⟨check1040,ContactValues.valid1040⟩
theorem valid1041 : ValidPanel panel1041 := ⟨check1041,ContactValues.valid1041⟩
theorem valid1042 : ValidPanel panel1042 := ⟨check1042,ContactValues.valid1042⟩
theorem valid1043 : ValidPanel panel1043 := ⟨check1043,ContactValues.valid1043⟩
theorem valid1044 : ValidPanel panel1044 := ⟨check1044,ContactValues.valid1044⟩
theorem valid1045 : ValidPanel panel1045 := ⟨check1045,ContactValues.valid1045⟩
theorem valid1046 : ValidPanel panel1046 := ⟨check1046,ContactValues.valid1046⟩
theorem valid1047 : ValidPanel panel1047 := ⟨check1047,ContactValues.valid1047⟩
theorem valid1048 : ValidPanel panel1048 := ⟨check1048,ContactValues.valid1048⟩
theorem valid1049 : ValidPanel panel1049 := ⟨check1049,ContactValues.valid1049⟩
theorem valid1050 : ValidPanel panel1050 := ⟨check1050,ContactValues.valid1050⟩
theorem valid1051 : ValidPanel panel1051 := ⟨check1051,ContactValues.valid1051⟩
theorem valid1052 : ValidPanel panel1052 := ⟨check1052,ContactValues.valid1052⟩
theorem valid1053 : ValidPanel panel1053 := ⟨check1053,ContactValues.valid1053⟩
theorem valid1054 : ValidPanel panel1054 := ⟨check1054,ContactValues.valid1054⟩
theorem valid1055 : ValidPanel panel1055 := ⟨check1055,ContactValues.valid1055⟩
theorem validBlock32 : ∀ p∈block32,ValidPanel p := by
  simp only [block32,List.forall_mem_cons]
  exact ⟨valid1024,⟨valid1025,⟨valid1026,⟨valid1027,⟨valid1028,⟨valid1029,⟨valid1030,⟨valid1031,⟨valid1032,⟨valid1033,⟨valid1034,⟨valid1035,⟨valid1036,⟨valid1037,⟨valid1038,⟨valid1039,⟨valid1040,⟨valid1041,⟨valid1042,⟨valid1043,⟨valid1044,⟨valid1045,⟨valid1046,⟨valid1047,⟨valid1048,⟨valid1049,⟨valid1050,⟨valid1051,⟨valid1052,⟨valid1053,⟨valid1054,⟨valid1055,(by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end chebyshev2.Certificates.Compact.AmplitudeValues

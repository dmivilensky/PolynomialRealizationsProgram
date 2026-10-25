import chebyshev2.Certificates.Compact.AmplitudeBatches.Batch033
import chebyshev2.Certificates.Compact.ContactBatches.Correspondence033
import chebyshev2.Certificates.Compact.AmplitudeProof

/-!
Article: chebyshev2, Section 4.1.
Correspondence033.
Use: `chebyshev2.Certificates.Compact.AmplitudeValues.validBlock33` feeds
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
theorem valid1056 : ValidPanel panel1056 := ⟨check1056,ContactValues.valid1056⟩
theorem valid1057 : ValidPanel panel1057 := ⟨check1057,ContactValues.valid1057⟩
theorem valid1058 : ValidPanel panel1058 := ⟨check1058,ContactValues.valid1058⟩
theorem valid1059 : ValidPanel panel1059 := ⟨check1059,ContactValues.valid1059⟩
theorem valid1060 : ValidPanel panel1060 := ⟨check1060,ContactValues.valid1060⟩
theorem valid1061 : ValidPanel panel1061 := ⟨check1061,ContactValues.valid1061⟩
theorem valid1062 : ValidPanel panel1062 := ⟨check1062,ContactValues.valid1062⟩
theorem valid1063 : ValidPanel panel1063 := ⟨check1063,ContactValues.valid1063⟩
theorem valid1064 : ValidPanel panel1064 := ⟨check1064,ContactValues.valid1064⟩
theorem valid1065 : ValidPanel panel1065 := ⟨check1065,ContactValues.valid1065⟩
theorem valid1066 : ValidPanel panel1066 := ⟨check1066,ContactValues.valid1066⟩
theorem valid1067 : ValidPanel panel1067 := ⟨check1067,ContactValues.valid1067⟩
theorem valid1068 : ValidPanel panel1068 := ⟨check1068,ContactValues.valid1068⟩
theorem valid1069 : ValidPanel panel1069 := ⟨check1069,ContactValues.valid1069⟩
theorem valid1070 : ValidPanel panel1070 := ⟨check1070,ContactValues.valid1070⟩
theorem valid1071 : ValidPanel panel1071 := ⟨check1071,ContactValues.valid1071⟩
theorem valid1072 : ValidPanel panel1072 := ⟨check1072,ContactValues.valid1072⟩
theorem valid1073 : ValidPanel panel1073 := ⟨check1073,ContactValues.valid1073⟩
theorem valid1074 : ValidPanel panel1074 := ⟨check1074,ContactValues.valid1074⟩
theorem valid1075 : ValidPanel panel1075 := ⟨check1075,ContactValues.valid1075⟩
theorem valid1076 : ValidPanel panel1076 := ⟨check1076,ContactValues.valid1076⟩
theorem valid1077 : ValidPanel panel1077 := ⟨check1077,ContactValues.valid1077⟩
theorem valid1078 : ValidPanel panel1078 := ⟨check1078,ContactValues.valid1078⟩
theorem valid1079 : ValidPanel panel1079 := ⟨check1079,ContactValues.valid1079⟩
theorem valid1080 : ValidPanel panel1080 := ⟨check1080,ContactValues.valid1080⟩
theorem valid1081 : ValidPanel panel1081 := ⟨check1081,ContactValues.valid1081⟩
theorem valid1082 : ValidPanel panel1082 := ⟨check1082,ContactValues.valid1082⟩
theorem valid1083 : ValidPanel panel1083 := ⟨check1083,ContactValues.valid1083⟩
theorem valid1084 : ValidPanel panel1084 := ⟨check1084,ContactValues.valid1084⟩
theorem valid1085 : ValidPanel panel1085 := ⟨check1085,ContactValues.valid1085⟩
theorem valid1086 : ValidPanel panel1086 := ⟨check1086,ContactValues.valid1086⟩
theorem valid1087 : ValidPanel panel1087 := ⟨check1087,ContactValues.valid1087⟩
theorem validBlock33 : ∀ p∈block33,ValidPanel p := by
  simp only [block33,List.forall_mem_cons]
  exact ⟨valid1056,⟨valid1057,⟨valid1058,⟨valid1059,⟨valid1060,⟨valid1061,⟨valid1062,⟨valid1063,⟨valid1064,⟨valid1065,⟨valid1066,⟨valid1067,⟨valid1068,⟨valid1069,⟨valid1070,⟨valid1071,⟨valid1072,⟨valid1073,⟨valid1074,⟨valid1075,⟨valid1076,⟨valid1077,⟨valid1078,⟨valid1079,⟨valid1080,⟨valid1081,⟨valid1082,⟨valid1083,⟨valid1084,⟨valid1085,⟨valid1086,⟨valid1087,(by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end chebyshev2.Certificates.Compact.AmplitudeValues

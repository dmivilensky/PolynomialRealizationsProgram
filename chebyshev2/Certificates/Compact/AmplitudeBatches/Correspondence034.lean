import chebyshev2.Certificates.Compact.AmplitudeBatches.Batch034
import chebyshev2.Certificates.Compact.ContactBatches.Correspondence034
import chebyshev2.Certificates.Compact.AmplitudeProof

/-!
Article: chebyshev2, Section 4.1.
Correspondence034.
Use: `chebyshev2.Certificates.Compact.AmplitudeValues.validBlock34` feeds
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
theorem valid1088 : ValidPanel panel1088 := ⟨check1088,ContactValues.valid1088⟩
theorem valid1089 : ValidPanel panel1089 := ⟨check1089,ContactValues.valid1089⟩
theorem valid1090 : ValidPanel panel1090 := ⟨check1090,ContactValues.valid1090⟩
theorem valid1091 : ValidPanel panel1091 := ⟨check1091,ContactValues.valid1091⟩
theorem valid1092 : ValidPanel panel1092 := ⟨check1092,ContactValues.valid1092⟩
theorem valid1093 : ValidPanel panel1093 := ⟨check1093,ContactValues.valid1093⟩
theorem valid1094 : ValidPanel panel1094 := ⟨check1094,ContactValues.valid1094⟩
theorem valid1095 : ValidPanel panel1095 := ⟨check1095,ContactValues.valid1095⟩
theorem valid1096 : ValidPanel panel1096 := ⟨check1096,ContactValues.valid1096⟩
theorem valid1097 : ValidPanel panel1097 := ⟨check1097,ContactValues.valid1097⟩
theorem valid1098 : ValidPanel panel1098 := ⟨check1098,ContactValues.valid1098⟩
theorem valid1099 : ValidPanel panel1099 := ⟨check1099,ContactValues.valid1099⟩
theorem valid1100 : ValidPanel panel1100 := ⟨check1100,ContactValues.valid1100⟩
theorem valid1101 : ValidPanel panel1101 := ⟨check1101,ContactValues.valid1101⟩
theorem valid1102 : ValidPanel panel1102 := ⟨check1102,ContactValues.valid1102⟩
theorem valid1103 : ValidPanel panel1103 := ⟨check1103,ContactValues.valid1103⟩
theorem valid1104 : ValidPanel panel1104 := ⟨check1104,ContactValues.valid1104⟩
theorem valid1105 : ValidPanel panel1105 := ⟨check1105,ContactValues.valid1105⟩
theorem valid1106 : ValidPanel panel1106 := ⟨check1106,ContactValues.valid1106⟩
theorem valid1107 : ValidPanel panel1107 := ⟨check1107,ContactValues.valid1107⟩
theorem valid1108 : ValidPanel panel1108 := ⟨check1108,ContactValues.valid1108⟩
theorem valid1109 : ValidPanel panel1109 := ⟨check1109,ContactValues.valid1109⟩
theorem valid1110 : ValidPanel panel1110 := ⟨check1110,ContactValues.valid1110⟩
theorem valid1111 : ValidPanel panel1111 := ⟨check1111,ContactValues.valid1111⟩
theorem valid1112 : ValidPanel panel1112 := ⟨check1112,ContactValues.valid1112⟩
theorem valid1113 : ValidPanel panel1113 := ⟨check1113,ContactValues.valid1113⟩
theorem valid1114 : ValidPanel panel1114 := ⟨check1114,ContactValues.valid1114⟩
theorem valid1115 : ValidPanel panel1115 := ⟨check1115,ContactValues.valid1115⟩
theorem valid1116 : ValidPanel panel1116 := ⟨check1116,ContactValues.valid1116⟩
theorem valid1117 : ValidPanel panel1117 := ⟨check1117,ContactValues.valid1117⟩
theorem valid1118 : ValidPanel panel1118 := ⟨check1118,ContactValues.valid1118⟩
theorem valid1119 : ValidPanel panel1119 := ⟨check1119,ContactValues.valid1119⟩
theorem validBlock34 : ∀ p∈block34,ValidPanel p := by
  simp only [block34,List.forall_mem_cons]
  exact ⟨valid1088,⟨valid1089,⟨valid1090,⟨valid1091,⟨valid1092,⟨valid1093,⟨valid1094,⟨valid1095,⟨valid1096,⟨valid1097,⟨valid1098,⟨valid1099,⟨valid1100,⟨valid1101,⟨valid1102,⟨valid1103,⟨valid1104,⟨valid1105,⟨valid1106,⟨valid1107,⟨valid1108,⟨valid1109,⟨valid1110,⟨valid1111,⟨valid1112,⟨valid1113,⟨valid1114,⟨valid1115,⟨valid1116,⟨valid1117,⟨valid1118,⟨valid1119,(by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end chebyshev2.Certificates.Compact.AmplitudeValues

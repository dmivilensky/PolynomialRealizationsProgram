import chebyshev2.Certificates.Compact.AmplitudeBatches.Batch035
import chebyshev2.Certificates.Compact.ContactBatches.Correspondence035
import chebyshev2.Certificates.Compact.AmplitudeProof

/-!
Article: chebyshev2, Section 4.1.
Correspondence035.
Use: `chebyshev2.Certificates.Compact.AmplitudeValues.validBlock35` feeds
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
theorem valid1120 : ValidPanel panel1120 := ⟨check1120,ContactValues.valid1120⟩
theorem valid1121 : ValidPanel panel1121 := ⟨check1121,ContactValues.valid1121⟩
theorem valid1122 : ValidPanel panel1122 := ⟨check1122,ContactValues.valid1122⟩
theorem valid1123 : ValidPanel panel1123 := ⟨check1123,ContactValues.valid1123⟩
theorem valid1124 : ValidPanel panel1124 := ⟨check1124,ContactValues.valid1124⟩
theorem valid1125 : ValidPanel panel1125 := ⟨check1125,ContactValues.valid1125⟩
theorem valid1126 : ValidPanel panel1126 := ⟨check1126,ContactValues.valid1126⟩
theorem valid1127 : ValidPanel panel1127 := ⟨check1127,ContactValues.valid1127⟩
theorem valid1128 : ValidPanel panel1128 := ⟨check1128,ContactValues.valid1128⟩
theorem valid1129 : ValidPanel panel1129 := ⟨check1129,ContactValues.valid1129⟩
theorem valid1130 : ValidPanel panel1130 := ⟨check1130,ContactValues.valid1130⟩
theorem valid1131 : ValidPanel panel1131 := ⟨check1131,ContactValues.valid1131⟩
theorem valid1132 : ValidPanel panel1132 := ⟨check1132,ContactValues.valid1132⟩
theorem valid1133 : ValidPanel panel1133 := ⟨check1133,ContactValues.valid1133⟩
theorem valid1134 : ValidPanel panel1134 := ⟨check1134,ContactValues.valid1134⟩
theorem valid1135 : ValidPanel panel1135 := ⟨check1135,ContactValues.valid1135⟩
theorem valid1136 : ValidPanel panel1136 := ⟨check1136,ContactValues.valid1136⟩
theorem valid1137 : ValidPanel panel1137 := ⟨check1137,ContactValues.valid1137⟩
theorem valid1138 : ValidPanel panel1138 := ⟨check1138,ContactValues.valid1138⟩
theorem valid1139 : ValidPanel panel1139 := ⟨check1139,ContactValues.valid1139⟩
theorem valid1140 : ValidPanel panel1140 := ⟨check1140,ContactValues.valid1140⟩
theorem valid1141 : ValidPanel panel1141 := ⟨check1141,ContactValues.valid1141⟩
theorem valid1142 : ValidPanel panel1142 := ⟨check1142,ContactValues.valid1142⟩
theorem valid1143 : ValidPanel panel1143 := ⟨check1143,ContactValues.valid1143⟩
theorem valid1144 : ValidPanel panel1144 := ⟨check1144,ContactValues.valid1144⟩
theorem valid1145 : ValidPanel panel1145 := ⟨check1145,ContactValues.valid1145⟩
theorem valid1146 : ValidPanel panel1146 := ⟨check1146,ContactValues.valid1146⟩
theorem valid1147 : ValidPanel panel1147 := ⟨check1147,ContactValues.valid1147⟩
theorem valid1148 : ValidPanel panel1148 := ⟨check1148,ContactValues.valid1148⟩
theorem valid1149 : ValidPanel panel1149 := ⟨check1149,ContactValues.valid1149⟩
theorem valid1150 : ValidPanel panel1150 := ⟨check1150,ContactValues.valid1150⟩
theorem valid1151 : ValidPanel panel1151 := ⟨check1151,ContactValues.valid1151⟩
theorem validBlock35 : ∀ p∈block35,ValidPanel p := by
  simp only [block35,List.forall_mem_cons]
  exact ⟨valid1120,⟨valid1121,⟨valid1122,⟨valid1123,⟨valid1124,⟨valid1125,⟨valid1126,⟨valid1127,⟨valid1128,⟨valid1129,⟨valid1130,⟨valid1131,⟨valid1132,⟨valid1133,⟨valid1134,⟨valid1135,⟨valid1136,⟨valid1137,⟨valid1138,⟨valid1139,⟨valid1140,⟨valid1141,⟨valid1142,⟨valid1143,⟨valid1144,⟨valid1145,⟨valid1146,⟨valid1147,⟨valid1148,⟨valid1149,⟨valid1150,⟨valid1151,(by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end chebyshev2.Certificates.Compact.AmplitudeValues

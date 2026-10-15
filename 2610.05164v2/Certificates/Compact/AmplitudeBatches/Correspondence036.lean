import «2610.05164v2».Certificates.Compact.AmplitudeBatches.Batch036
import «2610.05164v2».Certificates.Compact.ContactBatches.Correspondence036
import «2610.05164v2».Certificates.Compact.AmplitudeProof

/-!
Article: 2610.05164v2, Section 4.1.
Correspondence036.
Use: `«2610.05164v2».Certificates.Compact.AmplitudeValues.validBlock36` feeds
`«2610.05164v2».Certificates.Compact.AmplitudeValues.all_valid` (all valid).
Proof chain: `«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement` —
2610.05164v2, Theorem 1.2, factor 1.000013; Unconditional uniform gain comparison with the retained
numerical factor.
-/
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 200000
set_option maxHeartbeats 0
namespace «2610.05164v2».Certificates.Compact.AmplitudeValues
open «2610.05164v2».Numerics.IntegerCertificate
theorem valid1152 : ValidPanel panel1152 := ⟨check1152,ContactValues.valid1152⟩
theorem valid1153 : ValidPanel panel1153 := ⟨check1153,ContactValues.valid1153⟩
theorem valid1154 : ValidPanel panel1154 := ⟨check1154,ContactValues.valid1154⟩
theorem valid1155 : ValidPanel panel1155 := ⟨check1155,ContactValues.valid1155⟩
theorem valid1156 : ValidPanel panel1156 := ⟨check1156,ContactValues.valid1156⟩
theorem valid1157 : ValidPanel panel1157 := ⟨check1157,ContactValues.valid1157⟩
theorem valid1158 : ValidPanel panel1158 := ⟨check1158,ContactValues.valid1158⟩
theorem valid1159 : ValidPanel panel1159 := ⟨check1159,ContactValues.valid1159⟩
theorem valid1160 : ValidPanel panel1160 := ⟨check1160,ContactValues.valid1160⟩
theorem valid1161 : ValidPanel panel1161 := ⟨check1161,ContactValues.valid1161⟩
theorem valid1162 : ValidPanel panel1162 := ⟨check1162,ContactValues.valid1162⟩
theorem valid1163 : ValidPanel panel1163 := ⟨check1163,ContactValues.valid1163⟩
theorem valid1164 : ValidPanel panel1164 := ⟨check1164,ContactValues.valid1164⟩
theorem valid1165 : ValidPanel panel1165 := ⟨check1165,ContactValues.valid1165⟩
theorem valid1166 : ValidPanel panel1166 := ⟨check1166,ContactValues.valid1166⟩
theorem valid1167 : ValidPanel panel1167 := ⟨check1167,ContactValues.valid1167⟩
theorem valid1168 : ValidPanel panel1168 := ⟨check1168,ContactValues.valid1168⟩
theorem valid1169 : ValidPanel panel1169 := ⟨check1169,ContactValues.valid1169⟩
theorem valid1170 : ValidPanel panel1170 := ⟨check1170,ContactValues.valid1170⟩
theorem valid1171 : ValidPanel panel1171 := ⟨check1171,ContactValues.valid1171⟩
theorem valid1172 : ValidPanel panel1172 := ⟨check1172,ContactValues.valid1172⟩
theorem valid1173 : ValidPanel panel1173 := ⟨check1173,ContactValues.valid1173⟩
theorem valid1174 : ValidPanel panel1174 := ⟨check1174,ContactValues.valid1174⟩
theorem valid1175 : ValidPanel panel1175 := ⟨check1175,ContactValues.valid1175⟩
theorem valid1176 : ValidPanel panel1176 := ⟨check1176,ContactValues.valid1176⟩
theorem valid1177 : ValidPanel panel1177 := ⟨check1177,ContactValues.valid1177⟩
theorem valid1178 : ValidPanel panel1178 := ⟨check1178,ContactValues.valid1178⟩
theorem valid1179 : ValidPanel panel1179 := ⟨check1179,ContactValues.valid1179⟩
theorem valid1180 : ValidPanel panel1180 := ⟨check1180,ContactValues.valid1180⟩
theorem valid1181 : ValidPanel panel1181 := ⟨check1181,ContactValues.valid1181⟩
theorem valid1182 : ValidPanel panel1182 := ⟨check1182,ContactValues.valid1182⟩
theorem valid1183 : ValidPanel panel1183 := ⟨check1183,ContactValues.valid1183⟩
theorem validBlock36 : ∀ p∈block36,ValidPanel p := by
  simp only [block36,List.forall_mem_cons]
  exact ⟨valid1152,⟨valid1153,⟨valid1154,⟨valid1155,⟨valid1156,⟨valid1157,⟨valid1158,⟨valid1159,⟨valid1160,⟨valid1161,⟨valid1162,⟨valid1163,⟨valid1164,⟨valid1165,⟨valid1166,⟨valid1167,⟨valid1168,⟨valid1169,⟨valid1170,⟨valid1171,⟨valid1172,⟨valid1173,⟨valid1174,⟨valid1175,⟨valid1176,⟨valid1177,⟨valid1178,⟨valid1179,⟨valid1180,⟨valid1181,⟨valid1182,⟨valid1183,(by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end «2610.05164v2».Certificates.Compact.AmplitudeValues

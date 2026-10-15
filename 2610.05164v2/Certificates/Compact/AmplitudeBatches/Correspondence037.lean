import «2610.05164v2».Certificates.Compact.AmplitudeBatches.Batch037
import «2610.05164v2».Certificates.Compact.ContactBatches.Correspondence037
import «2610.05164v2».Certificates.Compact.AmplitudeProof

/-!
Article: 2610.05164v2, Section 4.1.
Correspondence037.
Use: `«2610.05164v2».Certificates.Compact.AmplitudeValues.validBlock37` feeds
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
theorem valid1184 : ValidPanel panel1184 := ⟨check1184,ContactValues.valid1184⟩
theorem valid1185 : ValidPanel panel1185 := ⟨check1185,ContactValues.valid1185⟩
theorem valid1186 : ValidPanel panel1186 := ⟨check1186,ContactValues.valid1186⟩
theorem valid1187 : ValidPanel panel1187 := ⟨check1187,ContactValues.valid1187⟩
theorem valid1188 : ValidPanel panel1188 := ⟨check1188,ContactValues.valid1188⟩
theorem valid1189 : ValidPanel panel1189 := ⟨check1189,ContactValues.valid1189⟩
theorem valid1190 : ValidPanel panel1190 := ⟨check1190,ContactValues.valid1190⟩
theorem valid1191 : ValidPanel panel1191 := ⟨check1191,ContactValues.valid1191⟩
theorem valid1192 : ValidPanel panel1192 := ⟨check1192,ContactValues.valid1192⟩
theorem valid1193 : ValidPanel panel1193 := ⟨check1193,ContactValues.valid1193⟩
theorem valid1194 : ValidPanel panel1194 := ⟨check1194,ContactValues.valid1194⟩
theorem valid1195 : ValidPanel panel1195 := ⟨check1195,ContactValues.valid1195⟩
theorem valid1196 : ValidPanel panel1196 := ⟨check1196,ContactValues.valid1196⟩
theorem valid1197 : ValidPanel panel1197 := ⟨check1197,ContactValues.valid1197⟩
theorem valid1198 : ValidPanel panel1198 := ⟨check1198,ContactValues.valid1198⟩
theorem valid1199 : ValidPanel panel1199 := ⟨check1199,ContactValues.valid1199⟩
theorem valid1200 : ValidPanel panel1200 := ⟨check1200,ContactValues.valid1200⟩
theorem valid1201 : ValidPanel panel1201 := ⟨check1201,ContactValues.valid1201⟩
theorem valid1202 : ValidPanel panel1202 := ⟨check1202,ContactValues.valid1202⟩
theorem valid1203 : ValidPanel panel1203 := ⟨check1203,ContactValues.valid1203⟩
theorem valid1204 : ValidPanel panel1204 := ⟨check1204,ContactValues.valid1204⟩
theorem valid1205 : ValidPanel panel1205 := ⟨check1205,ContactValues.valid1205⟩
theorem valid1206 : ValidPanel panel1206 := ⟨check1206,ContactValues.valid1206⟩
theorem valid1207 : ValidPanel panel1207 := ⟨check1207,ContactValues.valid1207⟩
theorem valid1208 : ValidPanel panel1208 := ⟨check1208,ContactValues.valid1208⟩
theorem valid1209 : ValidPanel panel1209 := ⟨check1209,ContactValues.valid1209⟩
theorem valid1210 : ValidPanel panel1210 := ⟨check1210,ContactValues.valid1210⟩
theorem valid1211 : ValidPanel panel1211 := ⟨check1211,ContactValues.valid1211⟩
theorem valid1212 : ValidPanel panel1212 := ⟨check1212,ContactValues.valid1212⟩
theorem valid1213 : ValidPanel panel1213 := ⟨check1213,ContactValues.valid1213⟩
theorem valid1214 : ValidPanel panel1214 := ⟨check1214,ContactValues.valid1214⟩
theorem valid1215 : ValidPanel panel1215 := ⟨check1215,ContactValues.valid1215⟩
theorem validBlock37 : ∀ p∈block37,ValidPanel p := by
  simp only [block37,List.forall_mem_cons]
  exact ⟨valid1184,⟨valid1185,⟨valid1186,⟨valid1187,⟨valid1188,⟨valid1189,⟨valid1190,⟨valid1191,⟨valid1192,⟨valid1193,⟨valid1194,⟨valid1195,⟨valid1196,⟨valid1197,⟨valid1198,⟨valid1199,⟨valid1200,⟨valid1201,⟨valid1202,⟨valid1203,⟨valid1204,⟨valid1205,⟨valid1206,⟨valid1207,⟨valid1208,⟨valid1209,⟨valid1210,⟨valid1211,⟨valid1212,⟨valid1213,⟨valid1214,⟨valid1215,(by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end «2610.05164v2».Certificates.Compact.AmplitudeValues

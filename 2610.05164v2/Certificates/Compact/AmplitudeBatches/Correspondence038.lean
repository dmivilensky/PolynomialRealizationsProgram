import «2610.05164v2».Certificates.Compact.AmplitudeBatches.Batch038
import «2610.05164v2».Certificates.Compact.ContactBatches.Correspondence038
import «2610.05164v2».Certificates.Compact.AmplitudeProof

/-!
Article: 2610.05164v2, Section 4.1.
Correspondence038.
Use: `«2610.05164v2».Certificates.Compact.AmplitudeValues.validBlock38` feeds
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
theorem valid1216 : ValidPanel panel1216 := ⟨check1216,ContactValues.valid1216⟩
theorem valid1217 : ValidPanel panel1217 := ⟨check1217,ContactValues.valid1217⟩
theorem valid1218 : ValidPanel panel1218 := ⟨check1218,ContactValues.valid1218⟩
theorem valid1219 : ValidPanel panel1219 := ⟨check1219,ContactValues.valid1219⟩
theorem valid1220 : ValidPanel panel1220 := ⟨check1220,ContactValues.valid1220⟩
theorem valid1221 : ValidPanel panel1221 := ⟨check1221,ContactValues.valid1221⟩
theorem valid1222 : ValidPanel panel1222 := ⟨check1222,ContactValues.valid1222⟩
theorem valid1223 : ValidPanel panel1223 := ⟨check1223,ContactValues.valid1223⟩
theorem valid1224 : ValidPanel panel1224 := ⟨check1224,ContactValues.valid1224⟩
theorem valid1225 : ValidPanel panel1225 := ⟨check1225,ContactValues.valid1225⟩
theorem valid1226 : ValidPanel panel1226 := ⟨check1226,ContactValues.valid1226⟩
theorem valid1227 : ValidPanel panel1227 := ⟨check1227,ContactValues.valid1227⟩
theorem valid1228 : ValidPanel panel1228 := ⟨check1228,ContactValues.valid1228⟩
theorem valid1229 : ValidPanel panel1229 := ⟨check1229,ContactValues.valid1229⟩
theorem valid1230 : ValidPanel panel1230 := ⟨check1230,ContactValues.valid1230⟩
theorem valid1231 : ValidPanel panel1231 := ⟨check1231,ContactValues.valid1231⟩
theorem valid1232 : ValidPanel panel1232 := ⟨check1232,ContactValues.valid1232⟩
theorem valid1233 : ValidPanel panel1233 := ⟨check1233,ContactValues.valid1233⟩
theorem valid1234 : ValidPanel panel1234 := ⟨check1234,ContactValues.valid1234⟩
theorem valid1235 : ValidPanel panel1235 := ⟨check1235,ContactValues.valid1235⟩
theorem valid1236 : ValidPanel panel1236 := ⟨check1236,ContactValues.valid1236⟩
theorem valid1237 : ValidPanel panel1237 := ⟨check1237,ContactValues.valid1237⟩
theorem valid1238 : ValidPanel panel1238 := ⟨check1238,ContactValues.valid1238⟩
theorem valid1239 : ValidPanel panel1239 := ⟨check1239,ContactValues.valid1239⟩
theorem valid1240 : ValidPanel panel1240 := ⟨check1240,ContactValues.valid1240⟩
theorem valid1241 : ValidPanel panel1241 := ⟨check1241,ContactValues.valid1241⟩
theorem valid1242 : ValidPanel panel1242 := ⟨check1242,ContactValues.valid1242⟩
theorem valid1243 : ValidPanel panel1243 := ⟨check1243,ContactValues.valid1243⟩
theorem valid1244 : ValidPanel panel1244 := ⟨check1244,ContactValues.valid1244⟩
theorem valid1245 : ValidPanel panel1245 := ⟨check1245,ContactValues.valid1245⟩
theorem valid1246 : ValidPanel panel1246 := ⟨check1246,ContactValues.valid1246⟩
theorem valid1247 : ValidPanel panel1247 := ⟨check1247,ContactValues.valid1247⟩
theorem validBlock38 : ∀ p∈block38,ValidPanel p := by
  simp only [block38,List.forall_mem_cons]
  exact ⟨valid1216,⟨valid1217,⟨valid1218,⟨valid1219,⟨valid1220,⟨valid1221,⟨valid1222,⟨valid1223,⟨valid1224,⟨valid1225,⟨valid1226,⟨valid1227,⟨valid1228,⟨valid1229,⟨valid1230,⟨valid1231,⟨valid1232,⟨valid1233,⟨valid1234,⟨valid1235,⟨valid1236,⟨valid1237,⟨valid1238,⟨valid1239,⟨valid1240,⟨valid1241,⟨valid1242,⟨valid1243,⟨valid1244,⟨valid1245,⟨valid1246,⟨valid1247,(by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end «2610.05164v2».Certificates.Compact.AmplitudeValues

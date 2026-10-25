import chebyshev2.Certificates.Compact.AmplitudeBatches.Batch039
import chebyshev2.Certificates.Compact.ContactBatches.Correspondence039
import chebyshev2.Certificates.Compact.AmplitudeProof

/-!
Article: chebyshev2, Section 4.1.
Correspondence039.
Use: `chebyshev2.Certificates.Compact.AmplitudeValues.validBlock39` feeds
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
theorem valid1248 : ValidPanel panel1248 := ⟨check1248,ContactValues.valid1248⟩
theorem valid1249 : ValidPanel panel1249 := ⟨check1249,ContactValues.valid1249⟩
theorem valid1250 : ValidPanel panel1250 := ⟨check1250,ContactValues.valid1250⟩
theorem valid1251 : ValidPanel panel1251 := ⟨check1251,ContactValues.valid1251⟩
theorem valid1252 : ValidPanel panel1252 := ⟨check1252,ContactValues.valid1252⟩
theorem valid1253 : ValidPanel panel1253 := ⟨check1253,ContactValues.valid1253⟩
theorem valid1254 : ValidPanel panel1254 := ⟨check1254,ContactValues.valid1254⟩
theorem valid1255 : ValidPanel panel1255 := ⟨check1255,ContactValues.valid1255⟩
theorem valid1256 : ValidPanel panel1256 := ⟨check1256,ContactValues.valid1256⟩
theorem valid1257 : ValidPanel panel1257 := ⟨check1257,ContactValues.valid1257⟩
theorem valid1258 : ValidPanel panel1258 := ⟨check1258,ContactValues.valid1258⟩
theorem valid1259 : ValidPanel panel1259 := ⟨check1259,ContactValues.valid1259⟩
theorem valid1260 : ValidPanel panel1260 := ⟨check1260,ContactValues.valid1260⟩
theorem valid1261 : ValidPanel panel1261 := ⟨check1261,ContactValues.valid1261⟩
theorem valid1262 : ValidPanel panel1262 := ⟨check1262,ContactValues.valid1262⟩
theorem valid1263 : ValidPanel panel1263 := ⟨check1263,ContactValues.valid1263⟩
theorem valid1264 : ValidPanel panel1264 := ⟨check1264,ContactValues.valid1264⟩
theorem valid1265 : ValidPanel panel1265 := ⟨check1265,ContactValues.valid1265⟩
theorem valid1266 : ValidPanel panel1266 := ⟨check1266,ContactValues.valid1266⟩
theorem valid1267 : ValidPanel panel1267 := ⟨check1267,ContactValues.valid1267⟩
theorem valid1268 : ValidPanel panel1268 := ⟨check1268,ContactValues.valid1268⟩
theorem valid1269 : ValidPanel panel1269 := ⟨check1269,ContactValues.valid1269⟩
theorem valid1270 : ValidPanel panel1270 := ⟨check1270,ContactValues.valid1270⟩
theorem valid1271 : ValidPanel panel1271 := ⟨check1271,ContactValues.valid1271⟩
theorem valid1272 : ValidPanel panel1272 := ⟨check1272,ContactValues.valid1272⟩
theorem valid1273 : ValidPanel panel1273 := ⟨check1273,ContactValues.valid1273⟩
theorem valid1274 : ValidPanel panel1274 := ⟨check1274,ContactValues.valid1274⟩
theorem valid1275 : ValidPanel panel1275 := ⟨check1275,ContactValues.valid1275⟩
theorem valid1276 : ValidPanel panel1276 := ⟨check1276,ContactValues.valid1276⟩
theorem valid1277 : ValidPanel panel1277 := ⟨check1277,ContactValues.valid1277⟩
theorem valid1278 : ValidPanel panel1278 := ⟨check1278,ContactValues.valid1278⟩
theorem valid1279 : ValidPanel panel1279 := ⟨check1279,ContactValues.valid1279⟩
theorem validBlock39 : ∀ p∈block39,ValidPanel p := by
  simp only [block39,List.forall_mem_cons]
  exact ⟨valid1248,⟨valid1249,⟨valid1250,⟨valid1251,⟨valid1252,⟨valid1253,⟨valid1254,⟨valid1255,⟨valid1256,⟨valid1257,⟨valid1258,⟨valid1259,⟨valid1260,⟨valid1261,⟨valid1262,⟨valid1263,⟨valid1264,⟨valid1265,⟨valid1266,⟨valid1267,⟨valid1268,⟨valid1269,⟨valid1270,⟨valid1271,⟨valid1272,⟨valid1273,⟨valid1274,⟨valid1275,⟨valid1276,⟨valid1277,⟨valid1278,⟨valid1279,(by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end chebyshev2.Certificates.Compact.AmplitudeValues

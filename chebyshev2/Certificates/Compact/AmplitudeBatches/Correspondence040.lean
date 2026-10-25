import chebyshev2.Certificates.Compact.AmplitudeBatches.Batch040
import chebyshev2.Certificates.Compact.ContactBatches.Correspondence040
import chebyshev2.Certificates.Compact.AmplitudeProof

/-!
Article: chebyshev2, Section 4.1.
Correspondence040.
Use: `chebyshev2.Certificates.Compact.AmplitudeValues.validBlock40` feeds
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
theorem valid1280 : ValidPanel panel1280 := ⟨check1280,ContactValues.valid1280⟩
theorem valid1281 : ValidPanel panel1281 := ⟨check1281,ContactValues.valid1281⟩
theorem valid1282 : ValidPanel panel1282 := ⟨check1282,ContactValues.valid1282⟩
theorem valid1283 : ValidPanel panel1283 := ⟨check1283,ContactValues.valid1283⟩
theorem valid1284 : ValidPanel panel1284 := ⟨check1284,ContactValues.valid1284⟩
theorem valid1285 : ValidPanel panel1285 := ⟨check1285,ContactValues.valid1285⟩
theorem valid1286 : ValidPanel panel1286 := ⟨check1286,ContactValues.valid1286⟩
theorem valid1287 : ValidPanel panel1287 := ⟨check1287,ContactValues.valid1287⟩
theorem valid1288 : ValidPanel panel1288 := ⟨check1288,ContactValues.valid1288⟩
theorem valid1289 : ValidPanel panel1289 := ⟨check1289,ContactValues.valid1289⟩
theorem valid1290 : ValidPanel panel1290 := ⟨check1290,ContactValues.valid1290⟩
theorem validBlock40 : ∀ p∈block40,ValidPanel p := by
  simp only [block40,List.forall_mem_cons]
  exact ⟨valid1280,⟨valid1281,⟨valid1282,⟨valid1283,⟨valid1284,⟨valid1285,⟨valid1286,⟨valid1287,⟨valid1288,⟨valid1289,⟨valid1290,(by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end chebyshev2.Certificates.Compact.AmplitudeValues

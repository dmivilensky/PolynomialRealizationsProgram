import chebyshev2.Certificates.Compact.AmplitudeBatches.Batch008
import chebyshev2.Certificates.Compact.ContactBatches.Correspondence008
import chebyshev2.Certificates.Compact.AmplitudeProof

/-!
Article: chebyshev2, Section 4.1.
Correspondence008.
Use: `chebyshev2.Certificates.Compact.AmplitudeValues.validBlock8` feeds
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
theorem valid256 : ValidPanel panel256 := ⟨check256,ContactValues.valid256⟩
theorem valid257 : ValidPanel panel257 := ⟨check257,ContactValues.valid257⟩
theorem valid258 : ValidPanel panel258 := ⟨check258,ContactValues.valid258⟩
theorem valid259 : ValidPanel panel259 := ⟨check259,ContactValues.valid259⟩
theorem valid260 : ValidPanel panel260 := ⟨check260,ContactValues.valid260⟩
theorem valid261 : ValidPanel panel261 := ⟨check261,ContactValues.valid261⟩
theorem valid262 : ValidPanel panel262 := ⟨check262,ContactValues.valid262⟩
theorem valid263 : ValidPanel panel263 := ⟨check263,ContactValues.valid263⟩
theorem valid264 : ValidPanel panel264 := ⟨check264,ContactValues.valid264⟩
theorem valid265 : ValidPanel panel265 := ⟨check265,ContactValues.valid265⟩
theorem valid266 : ValidPanel panel266 := ⟨check266,ContactValues.valid266⟩
theorem valid267 : ValidPanel panel267 := ⟨check267,ContactValues.valid267⟩
theorem valid268 : ValidPanel panel268 := ⟨check268,ContactValues.valid268⟩
theorem valid269 : ValidPanel panel269 := ⟨check269,ContactValues.valid269⟩
theorem valid270 : ValidPanel panel270 := ⟨check270,ContactValues.valid270⟩
theorem valid271 : ValidPanel panel271 := ⟨check271,ContactValues.valid271⟩
theorem valid272 : ValidPanel panel272 := ⟨check272,ContactValues.valid272⟩
theorem valid273 : ValidPanel panel273 := ⟨check273,ContactValues.valid273⟩
theorem valid274 : ValidPanel panel274 := ⟨check274,ContactValues.valid274⟩
theorem valid275 : ValidPanel panel275 := ⟨check275,ContactValues.valid275⟩
theorem valid276 : ValidPanel panel276 := ⟨check276,ContactValues.valid276⟩
theorem valid277 : ValidPanel panel277 := ⟨check277,ContactValues.valid277⟩
theorem valid278 : ValidPanel panel278 := ⟨check278,ContactValues.valid278⟩
theorem valid279 : ValidPanel panel279 := ⟨check279,ContactValues.valid279⟩
theorem valid280 : ValidPanel panel280 := ⟨check280,ContactValues.valid280⟩
theorem valid281 : ValidPanel panel281 := ⟨check281,ContactValues.valid281⟩
theorem valid282 : ValidPanel panel282 := ⟨check282,ContactValues.valid282⟩
theorem valid283 : ValidPanel panel283 := ⟨check283,ContactValues.valid283⟩
theorem valid284 : ValidPanel panel284 := ⟨check284,ContactValues.valid284⟩
theorem valid285 : ValidPanel panel285 := ⟨check285,ContactValues.valid285⟩
theorem valid286 : ValidPanel panel286 := ⟨check286,ContactValues.valid286⟩
theorem valid287 : ValidPanel panel287 := ⟨check287,ContactValues.valid287⟩
theorem validBlock8 : ∀ p∈block8,ValidPanel p := by
  simp only [block8,List.forall_mem_cons]
  exact ⟨valid256,⟨valid257,⟨valid258,⟨valid259,⟨valid260,⟨valid261,⟨valid262,⟨valid263,⟨valid264,⟨valid265,⟨valid266,⟨valid267,⟨valid268,⟨valid269,⟨valid270,⟨valid271,⟨valid272,⟨valid273,⟨valid274,⟨valid275,⟨valid276,⟨valid277,⟨valid278,⟨valid279,⟨valid280,⟨valid281,⟨valid282,⟨valid283,⟨valid284,⟨valid285,⟨valid286,⟨valid287,(by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end chebyshev2.Certificates.Compact.AmplitudeValues

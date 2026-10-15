import «2610.05164v2».Certificates.Compact.AmplitudeBatches.Batch007
import «2610.05164v2».Certificates.Compact.ContactBatches.Correspondence007
import «2610.05164v2».Certificates.Compact.AmplitudeProof

/-!
Article: 2610.05164v2, Section 4.1.
Correspondence007.
Use: `«2610.05164v2».Certificates.Compact.AmplitudeValues.validBlock7` feeds
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
theorem valid224 : ValidPanel panel224 := ⟨check224,ContactValues.valid224⟩
theorem valid225 : ValidPanel panel225 := ⟨check225,ContactValues.valid225⟩
theorem valid226 : ValidPanel panel226 := ⟨check226,ContactValues.valid226⟩
theorem valid227 : ValidPanel panel227 := ⟨check227,ContactValues.valid227⟩
theorem valid228 : ValidPanel panel228 := ⟨check228,ContactValues.valid228⟩
theorem valid229 : ValidPanel panel229 := ⟨check229,ContactValues.valid229⟩
theorem valid230 : ValidPanel panel230 := ⟨check230,ContactValues.valid230⟩
theorem valid231 : ValidPanel panel231 := ⟨check231,ContactValues.valid231⟩
theorem valid232 : ValidPanel panel232 := ⟨check232,ContactValues.valid232⟩
theorem valid233 : ValidPanel panel233 := ⟨check233,ContactValues.valid233⟩
theorem valid234 : ValidPanel panel234 := ⟨check234,ContactValues.valid234⟩
theorem valid235 : ValidPanel panel235 := ⟨check235,ContactValues.valid235⟩
theorem valid236 : ValidPanel panel236 := ⟨check236,ContactValues.valid236⟩
theorem valid237 : ValidPanel panel237 := ⟨check237,ContactValues.valid237⟩
theorem valid238 : ValidPanel panel238 := ⟨check238,ContactValues.valid238⟩
theorem valid239 : ValidPanel panel239 := ⟨check239,ContactValues.valid239⟩
theorem valid240 : ValidPanel panel240 := ⟨check240,ContactValues.valid240⟩
theorem valid241 : ValidPanel panel241 := ⟨check241,ContactValues.valid241⟩
theorem valid242 : ValidPanel panel242 := ⟨check242,ContactValues.valid242⟩
theorem valid243 : ValidPanel panel243 := ⟨check243,ContactValues.valid243⟩
theorem valid244 : ValidPanel panel244 := ⟨check244,ContactValues.valid244⟩
theorem valid245 : ValidPanel panel245 := ⟨check245,ContactValues.valid245⟩
theorem valid246 : ValidPanel panel246 := ⟨check246,ContactValues.valid246⟩
theorem valid247 : ValidPanel panel247 := ⟨check247,ContactValues.valid247⟩
theorem valid248 : ValidPanel panel248 := ⟨check248,ContactValues.valid248⟩
theorem valid249 : ValidPanel panel249 := ⟨check249,ContactValues.valid249⟩
theorem valid250 : ValidPanel panel250 := ⟨check250,ContactValues.valid250⟩
theorem valid251 : ValidPanel panel251 := ⟨check251,ContactValues.valid251⟩
theorem valid252 : ValidPanel panel252 := ⟨check252,ContactValues.valid252⟩
theorem valid253 : ValidPanel panel253 := ⟨check253,ContactValues.valid253⟩
theorem valid254 : ValidPanel panel254 := ⟨check254,ContactValues.valid254⟩
theorem valid255 : ValidPanel panel255 := ⟨check255,ContactValues.valid255⟩
theorem validBlock7 : ∀ p∈block7,ValidPanel p := by
  simp only [block7,List.forall_mem_cons]
  exact ⟨valid224,⟨valid225,⟨valid226,⟨valid227,⟨valid228,⟨valid229,⟨valid230,⟨valid231,⟨valid232,⟨valid233,⟨valid234,⟨valid235,⟨valid236,⟨valid237,⟨valid238,⟨valid239,⟨valid240,⟨valid241,⟨valid242,⟨valid243,⟨valid244,⟨valid245,⟨valid246,⟨valid247,⟨valid248,⟨valid249,⟨valid250,⟨valid251,⟨valid252,⟨valid253,⟨valid254,⟨valid255,(by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end «2610.05164v2».Certificates.Compact.AmplitudeValues

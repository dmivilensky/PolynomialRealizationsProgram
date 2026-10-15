import «2610.05164v2».Certificates.Compact.AmplitudeBatches.Batch011
import «2610.05164v2».Certificates.Compact.ContactBatches.Correspondence011
import «2610.05164v2».Certificates.Compact.AmplitudeProof

/-!
Article: 2610.05164v2, Section 4.1.
Correspondence011.
Use: `«2610.05164v2».Certificates.Compact.AmplitudeValues.validBlock11` feeds
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
theorem valid352 : ValidPanel panel352 := ⟨check352,ContactValues.valid352⟩
theorem valid353 : ValidPanel panel353 := ⟨check353,ContactValues.valid353⟩
theorem valid354 : ValidPanel panel354 := ⟨check354,ContactValues.valid354⟩
theorem valid355 : ValidPanel panel355 := ⟨check355,ContactValues.valid355⟩
theorem valid356 : ValidPanel panel356 := ⟨check356,ContactValues.valid356⟩
theorem valid357 : ValidPanel panel357 := ⟨check357,ContactValues.valid357⟩
theorem valid358 : ValidPanel panel358 := ⟨check358,ContactValues.valid358⟩
theorem valid359 : ValidPanel panel359 := ⟨check359,ContactValues.valid359⟩
theorem valid360 : ValidPanel panel360 := ⟨check360,ContactValues.valid360⟩
theorem valid361 : ValidPanel panel361 := ⟨check361,ContactValues.valid361⟩
theorem valid362 : ValidPanel panel362 := ⟨check362,ContactValues.valid362⟩
theorem valid363 : ValidPanel panel363 := ⟨check363,ContactValues.valid363⟩
theorem valid364 : ValidPanel panel364 := ⟨check364,ContactValues.valid364⟩
theorem valid365 : ValidPanel panel365 := ⟨check365,ContactValues.valid365⟩
theorem valid366 : ValidPanel panel366 := ⟨check366,ContactValues.valid366⟩
theorem valid367 : ValidPanel panel367 := ⟨check367,ContactValues.valid367⟩
theorem valid368 : ValidPanel panel368 := ⟨check368,ContactValues.valid368⟩
theorem valid369 : ValidPanel panel369 := ⟨check369,ContactValues.valid369⟩
theorem valid370 : ValidPanel panel370 := ⟨check370,ContactValues.valid370⟩
theorem valid371 : ValidPanel panel371 := ⟨check371,ContactValues.valid371⟩
theorem valid372 : ValidPanel panel372 := ⟨check372,ContactValues.valid372⟩
theorem valid373 : ValidPanel panel373 := ⟨check373,ContactValues.valid373⟩
theorem valid374 : ValidPanel panel374 := ⟨check374,ContactValues.valid374⟩
theorem valid375 : ValidPanel panel375 := ⟨check375,ContactValues.valid375⟩
theorem valid376 : ValidPanel panel376 := ⟨check376,ContactValues.valid376⟩
theorem valid377 : ValidPanel panel377 := ⟨check377,ContactValues.valid377⟩
theorem valid378 : ValidPanel panel378 := ⟨check378,ContactValues.valid378⟩
theorem valid379 : ValidPanel panel379 := ⟨check379,ContactValues.valid379⟩
theorem valid380 : ValidPanel panel380 := ⟨check380,ContactValues.valid380⟩
theorem valid381 : ValidPanel panel381 := ⟨check381,ContactValues.valid381⟩
theorem valid382 : ValidPanel panel382 := ⟨check382,ContactValues.valid382⟩
theorem valid383 : ValidPanel panel383 := ⟨check383,ContactValues.valid383⟩
theorem validBlock11 : ∀ p∈block11,ValidPanel p := by
  simp only [block11,List.forall_mem_cons]
  exact ⟨valid352,⟨valid353,⟨valid354,⟨valid355,⟨valid356,⟨valid357,⟨valid358,⟨valid359,⟨valid360,⟨valid361,⟨valid362,⟨valid363,⟨valid364,⟨valid365,⟨valid366,⟨valid367,⟨valid368,⟨valid369,⟨valid370,⟨valid371,⟨valid372,⟨valid373,⟨valid374,⟨valid375,⟨valid376,⟨valid377,⟨valid378,⟨valid379,⟨valid380,⟨valid381,⟨valid382,⟨valid383,(by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end «2610.05164v2».Certificates.Compact.AmplitudeValues

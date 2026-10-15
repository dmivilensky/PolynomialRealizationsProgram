import «2610.05164v2».Certificates.Compact.AmplitudeBatches.Batch014
import «2610.05164v2».Certificates.Compact.ContactBatches.Correspondence014
import «2610.05164v2».Certificates.Compact.AmplitudeProof

/-!
Article: 2610.05164v2, Section 4.1.
Correspondence014.
Use: `«2610.05164v2».Certificates.Compact.AmplitudeValues.validBlock14` feeds
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
theorem valid448 : ValidPanel panel448 := ⟨check448,ContactValues.valid448⟩
theorem valid449 : ValidPanel panel449 := ⟨check449,ContactValues.valid449⟩
theorem valid450 : ValidPanel panel450 := ⟨check450,ContactValues.valid450⟩
theorem valid451 : ValidPanel panel451 := ⟨check451,ContactValues.valid451⟩
theorem valid452 : ValidPanel panel452 := ⟨check452,ContactValues.valid452⟩
theorem valid453 : ValidPanel panel453 := ⟨check453,ContactValues.valid453⟩
theorem valid454 : ValidPanel panel454 := ⟨check454,ContactValues.valid454⟩
theorem valid455 : ValidPanel panel455 := ⟨check455,ContactValues.valid455⟩
theorem valid456 : ValidPanel panel456 := ⟨check456,ContactValues.valid456⟩
theorem valid457 : ValidPanel panel457 := ⟨check457,ContactValues.valid457⟩
theorem valid458 : ValidPanel panel458 := ⟨check458,ContactValues.valid458⟩
theorem valid459 : ValidPanel panel459 := ⟨check459,ContactValues.valid459⟩
theorem valid460 : ValidPanel panel460 := ⟨check460,ContactValues.valid460⟩
theorem valid461 : ValidPanel panel461 := ⟨check461,ContactValues.valid461⟩
theorem valid462 : ValidPanel panel462 := ⟨check462,ContactValues.valid462⟩
theorem valid463 : ValidPanel panel463 := ⟨check463,ContactValues.valid463⟩
theorem valid464 : ValidPanel panel464 := ⟨check464,ContactValues.valid464⟩
theorem valid465 : ValidPanel panel465 := ⟨check465,ContactValues.valid465⟩
theorem valid466 : ValidPanel panel466 := ⟨check466,ContactValues.valid466⟩
theorem valid467 : ValidPanel panel467 := ⟨check467,ContactValues.valid467⟩
theorem valid468 : ValidPanel panel468 := ⟨check468,ContactValues.valid468⟩
theorem valid469 : ValidPanel panel469 := ⟨check469,ContactValues.valid469⟩
theorem valid470 : ValidPanel panel470 := ⟨check470,ContactValues.valid470⟩
theorem valid471 : ValidPanel panel471 := ⟨check471,ContactValues.valid471⟩
theorem valid472 : ValidPanel panel472 := ⟨check472,ContactValues.valid472⟩
theorem valid473 : ValidPanel panel473 := ⟨check473,ContactValues.valid473⟩
theorem valid474 : ValidPanel panel474 := ⟨check474,ContactValues.valid474⟩
theorem valid475 : ValidPanel panel475 := ⟨check475,ContactValues.valid475⟩
theorem valid476 : ValidPanel panel476 := ⟨check476,ContactValues.valid476⟩
theorem valid477 : ValidPanel panel477 := ⟨check477,ContactValues.valid477⟩
theorem valid478 : ValidPanel panel478 := ⟨check478,ContactValues.valid478⟩
theorem valid479 : ValidPanel panel479 := ⟨check479,ContactValues.valid479⟩
theorem validBlock14 : ∀ p∈block14,ValidPanel p := by
  simp only [block14,List.forall_mem_cons]
  exact ⟨valid448,⟨valid449,⟨valid450,⟨valid451,⟨valid452,⟨valid453,⟨valid454,⟨valid455,⟨valid456,⟨valid457,⟨valid458,⟨valid459,⟨valid460,⟨valid461,⟨valid462,⟨valid463,⟨valid464,⟨valid465,⟨valid466,⟨valid467,⟨valid468,⟨valid469,⟨valid470,⟨valid471,⟨valid472,⟨valid473,⟨valid474,⟨valid475,⟨valid476,⟨valid477,⟨valid478,⟨valid479,(by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end «2610.05164v2».Certificates.Compact.AmplitudeValues

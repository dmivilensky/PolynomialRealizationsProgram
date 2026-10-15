import «2610.05164v2».Certificates.Compact.AmplitudeBatches.Batch012
import «2610.05164v2».Certificates.Compact.ContactBatches.Correspondence012
import «2610.05164v2».Certificates.Compact.AmplitudeProof

/-!
Article: 2610.05164v2, Section 4.1.
Correspondence012.
Use: `«2610.05164v2».Certificates.Compact.AmplitudeValues.validBlock12` feeds
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
theorem valid384 : ValidPanel panel384 := ⟨check384,ContactValues.valid384⟩
theorem valid385 : ValidPanel panel385 := ⟨check385,ContactValues.valid385⟩
theorem valid386 : ValidPanel panel386 := ⟨check386,ContactValues.valid386⟩
theorem valid387 : ValidPanel panel387 := ⟨check387,ContactValues.valid387⟩
theorem valid388 : ValidPanel panel388 := ⟨check388,ContactValues.valid388⟩
theorem valid389 : ValidPanel panel389 := ⟨check389,ContactValues.valid389⟩
theorem valid390 : ValidPanel panel390 := ⟨check390,ContactValues.valid390⟩
theorem valid391 : ValidPanel panel391 := ⟨check391,ContactValues.valid391⟩
theorem valid392 : ValidPanel panel392 := ⟨check392,ContactValues.valid392⟩
theorem valid393 : ValidPanel panel393 := ⟨check393,ContactValues.valid393⟩
theorem valid394 : ValidPanel panel394 := ⟨check394,ContactValues.valid394⟩
theorem valid395 : ValidPanel panel395 := ⟨check395,ContactValues.valid395⟩
theorem valid396 : ValidPanel panel396 := ⟨check396,ContactValues.valid396⟩
theorem valid397 : ValidPanel panel397 := ⟨check397,ContactValues.valid397⟩
theorem valid398 : ValidPanel panel398 := ⟨check398,ContactValues.valid398⟩
theorem valid399 : ValidPanel panel399 := ⟨check399,ContactValues.valid399⟩
theorem valid400 : ValidPanel panel400 := ⟨check400,ContactValues.valid400⟩
theorem valid401 : ValidPanel panel401 := ⟨check401,ContactValues.valid401⟩
theorem valid402 : ValidPanel panel402 := ⟨check402,ContactValues.valid402⟩
theorem valid403 : ValidPanel panel403 := ⟨check403,ContactValues.valid403⟩
theorem valid404 : ValidPanel panel404 := ⟨check404,ContactValues.valid404⟩
theorem valid405 : ValidPanel panel405 := ⟨check405,ContactValues.valid405⟩
theorem valid406 : ValidPanel panel406 := ⟨check406,ContactValues.valid406⟩
theorem valid407 : ValidPanel panel407 := ⟨check407,ContactValues.valid407⟩
theorem valid408 : ValidPanel panel408 := ⟨check408,ContactValues.valid408⟩
theorem valid409 : ValidPanel panel409 := ⟨check409,ContactValues.valid409⟩
theorem valid410 : ValidPanel panel410 := ⟨check410,ContactValues.valid410⟩
theorem valid411 : ValidPanel panel411 := ⟨check411,ContactValues.valid411⟩
theorem valid412 : ValidPanel panel412 := ⟨check412,ContactValues.valid412⟩
theorem valid413 : ValidPanel panel413 := ⟨check413,ContactValues.valid413⟩
theorem valid414 : ValidPanel panel414 := ⟨check414,ContactValues.valid414⟩
theorem valid415 : ValidPanel panel415 := ⟨check415,ContactValues.valid415⟩
theorem validBlock12 : ∀ p∈block12,ValidPanel p := by
  simp only [block12,List.forall_mem_cons]
  exact ⟨valid384,⟨valid385,⟨valid386,⟨valid387,⟨valid388,⟨valid389,⟨valid390,⟨valid391,⟨valid392,⟨valid393,⟨valid394,⟨valid395,⟨valid396,⟨valid397,⟨valid398,⟨valid399,⟨valid400,⟨valid401,⟨valid402,⟨valid403,⟨valid404,⟨valid405,⟨valid406,⟨valid407,⟨valid408,⟨valid409,⟨valid410,⟨valid411,⟨valid412,⟨valid413,⟨valid414,⟨valid415,(by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end «2610.05164v2».Certificates.Compact.AmplitudeValues

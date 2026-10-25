import chebyshev2.Certificates.Compact.AmplitudeBatches.Batch015
import chebyshev2.Certificates.Compact.ContactBatches.Correspondence015
import chebyshev2.Certificates.Compact.AmplitudeProof

/-!
Article: chebyshev2, Section 4.1.
Correspondence015.
Use: `chebyshev2.Certificates.Compact.AmplitudeValues.validBlock15` feeds
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
theorem valid480 : ValidPanel panel480 := ⟨check480,ContactValues.valid480⟩
theorem valid481 : ValidPanel panel481 := ⟨check481,ContactValues.valid481⟩
theorem valid482 : ValidPanel panel482 := ⟨check482,ContactValues.valid482⟩
theorem valid483 : ValidPanel panel483 := ⟨check483,ContactValues.valid483⟩
theorem valid484 : ValidPanel panel484 := ⟨check484,ContactValues.valid484⟩
theorem valid485 : ValidPanel panel485 := ⟨check485,ContactValues.valid485⟩
theorem valid486 : ValidPanel panel486 := ⟨check486,ContactValues.valid486⟩
theorem valid487 : ValidPanel panel487 := ⟨check487,ContactValues.valid487⟩
theorem valid488 : ValidPanel panel488 := ⟨check488,ContactValues.valid488⟩
theorem valid489 : ValidPanel panel489 := ⟨check489,ContactValues.valid489⟩
theorem valid490 : ValidPanel panel490 := ⟨check490,ContactValues.valid490⟩
theorem valid491 : ValidPanel panel491 := ⟨check491,ContactValues.valid491⟩
theorem valid492 : ValidPanel panel492 := ⟨check492,ContactValues.valid492⟩
theorem valid493 : ValidPanel panel493 := ⟨check493,ContactValues.valid493⟩
theorem valid494 : ValidPanel panel494 := ⟨check494,ContactValues.valid494⟩
theorem valid495 : ValidPanel panel495 := ⟨check495,ContactValues.valid495⟩
theorem valid496 : ValidPanel panel496 := ⟨check496,ContactValues.valid496⟩
theorem valid497 : ValidPanel panel497 := ⟨check497,ContactValues.valid497⟩
theorem valid498 : ValidPanel panel498 := ⟨check498,ContactValues.valid498⟩
theorem valid499 : ValidPanel panel499 := ⟨check499,ContactValues.valid499⟩
theorem valid500 : ValidPanel panel500 := ⟨check500,ContactValues.valid500⟩
theorem valid501 : ValidPanel panel501 := ⟨check501,ContactValues.valid501⟩
theorem valid502 : ValidPanel panel502 := ⟨check502,ContactValues.valid502⟩
theorem valid503 : ValidPanel panel503 := ⟨check503,ContactValues.valid503⟩
theorem valid504 : ValidPanel panel504 := ⟨check504,ContactValues.valid504⟩
theorem valid505 : ValidPanel panel505 := ⟨check505,ContactValues.valid505⟩
theorem valid506 : ValidPanel panel506 := ⟨check506,ContactValues.valid506⟩
theorem valid507 : ValidPanel panel507 := ⟨check507,ContactValues.valid507⟩
theorem valid508 : ValidPanel panel508 := ⟨check508,ContactValues.valid508⟩
theorem valid509 : ValidPanel panel509 := ⟨check509,ContactValues.valid509⟩
theorem valid510 : ValidPanel panel510 := ⟨check510,ContactValues.valid510⟩
theorem valid511 : ValidPanel panel511 := ⟨check511,ContactValues.valid511⟩
theorem validBlock15 : ∀ p∈block15,ValidPanel p := by
  simp only [block15,List.forall_mem_cons]
  exact ⟨valid480,⟨valid481,⟨valid482,⟨valid483,⟨valid484,⟨valid485,⟨valid486,⟨valid487,⟨valid488,⟨valid489,⟨valid490,⟨valid491,⟨valid492,⟨valid493,⟨valid494,⟨valid495,⟨valid496,⟨valid497,⟨valid498,⟨valid499,⟨valid500,⟨valid501,⟨valid502,⟨valid503,⟨valid504,⟨valid505,⟨valid506,⟨valid507,⟨valid508,⟨valid509,⟨valid510,⟨valid511,(by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end chebyshev2.Certificates.Compact.AmplitudeValues

import chebyshev2.Certificates.Compact.AmplitudeBatches.Batch016
import chebyshev2.Certificates.Compact.ContactBatches.Correspondence016
import chebyshev2.Certificates.Compact.AmplitudeProof

/-!
Article: chebyshev2, Section 4.1.
Correspondence016.
Use: `chebyshev2.Certificates.Compact.AmplitudeValues.validBlock16` feeds
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
theorem valid512 : ValidPanel panel512 := ⟨check512,ContactValues.valid512⟩
theorem valid513 : ValidPanel panel513 := ⟨check513,ContactValues.valid513⟩
theorem valid514 : ValidPanel panel514 := ⟨check514,ContactValues.valid514⟩
theorem valid515 : ValidPanel panel515 := ⟨check515,ContactValues.valid515⟩
theorem valid516 : ValidPanel panel516 := ⟨check516,ContactValues.valid516⟩
theorem valid517 : ValidPanel panel517 := ⟨check517,ContactValues.valid517⟩
theorem valid518 : ValidPanel panel518 := ⟨check518,ContactValues.valid518⟩
theorem valid519 : ValidPanel panel519 := ⟨check519,ContactValues.valid519⟩
theorem valid520 : ValidPanel panel520 := ⟨check520,ContactValues.valid520⟩
theorem valid521 : ValidPanel panel521 := ⟨check521,ContactValues.valid521⟩
theorem valid522 : ValidPanel panel522 := ⟨check522,ContactValues.valid522⟩
theorem valid523 : ValidPanel panel523 := ⟨check523,ContactValues.valid523⟩
theorem valid524 : ValidPanel panel524 := ⟨check524,ContactValues.valid524⟩
theorem valid525 : ValidPanel panel525 := ⟨check525,ContactValues.valid525⟩
theorem valid526 : ValidPanel panel526 := ⟨check526,ContactValues.valid526⟩
theorem valid527 : ValidPanel panel527 := ⟨check527,ContactValues.valid527⟩
theorem valid528 : ValidPanel panel528 := ⟨check528,ContactValues.valid528⟩
theorem valid529 : ValidPanel panel529 := ⟨check529,ContactValues.valid529⟩
theorem valid530 : ValidPanel panel530 := ⟨check530,ContactValues.valid530⟩
theorem valid531 : ValidPanel panel531 := ⟨check531,ContactValues.valid531⟩
theorem valid532 : ValidPanel panel532 := ⟨check532,ContactValues.valid532⟩
theorem valid533 : ValidPanel panel533 := ⟨check533,ContactValues.valid533⟩
theorem valid534 : ValidPanel panel534 := ⟨check534,ContactValues.valid534⟩
theorem valid535 : ValidPanel panel535 := ⟨check535,ContactValues.valid535⟩
theorem valid536 : ValidPanel panel536 := ⟨check536,ContactValues.valid536⟩
theorem valid537 : ValidPanel panel537 := ⟨check537,ContactValues.valid537⟩
theorem valid538 : ValidPanel panel538 := ⟨check538,ContactValues.valid538⟩
theorem valid539 : ValidPanel panel539 := ⟨check539,ContactValues.valid539⟩
theorem valid540 : ValidPanel panel540 := ⟨check540,ContactValues.valid540⟩
theorem valid541 : ValidPanel panel541 := ⟨check541,ContactValues.valid541⟩
theorem valid542 : ValidPanel panel542 := ⟨check542,ContactValues.valid542⟩
theorem valid543 : ValidPanel panel543 := ⟨check543,ContactValues.valid543⟩
theorem validBlock16 : ∀ p∈block16,ValidPanel p := by
  simp only [block16,List.forall_mem_cons]
  exact ⟨valid512,⟨valid513,⟨valid514,⟨valid515,⟨valid516,⟨valid517,⟨valid518,⟨valid519,⟨valid520,⟨valid521,⟨valid522,⟨valid523,⟨valid524,⟨valid525,⟨valid526,⟨valid527,⟨valid528,⟨valid529,⟨valid530,⟨valid531,⟨valid532,⟨valid533,⟨valid534,⟨valid535,⟨valid536,⟨valid537,⟨valid538,⟨valid539,⟨valid540,⟨valid541,⟨valid542,⟨valid543,(by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end chebyshev2.Certificates.Compact.AmplitudeValues

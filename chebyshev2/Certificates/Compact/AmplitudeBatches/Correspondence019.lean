import chebyshev2.Certificates.Compact.AmplitudeBatches.Batch019
import chebyshev2.Certificates.Compact.ContactBatches.Correspondence019
import chebyshev2.Certificates.Compact.AmplitudeProof

/-!
Article: chebyshev2, Section 4.1.
Correspondence019.
Use: `chebyshev2.Certificates.Compact.AmplitudeValues.validBlock19` feeds
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
theorem valid608 : ValidPanel panel608 := ⟨check608,ContactValues.valid608⟩
theorem valid609 : ValidPanel panel609 := ⟨check609,ContactValues.valid609⟩
theorem valid610 : ValidPanel panel610 := ⟨check610,ContactValues.valid610⟩
theorem valid611 : ValidPanel panel611 := ⟨check611,ContactValues.valid611⟩
theorem valid612 : ValidPanel panel612 := ⟨check612,ContactValues.valid612⟩
theorem valid613 : ValidPanel panel613 := ⟨check613,ContactValues.valid613⟩
theorem valid614 : ValidPanel panel614 := ⟨check614,ContactValues.valid614⟩
theorem valid615 : ValidPanel panel615 := ⟨check615,ContactValues.valid615⟩
theorem valid616 : ValidPanel panel616 := ⟨check616,ContactValues.valid616⟩
theorem valid617 : ValidPanel panel617 := ⟨check617,ContactValues.valid617⟩
theorem valid618 : ValidPanel panel618 := ⟨check618,ContactValues.valid618⟩
theorem valid619 : ValidPanel panel619 := ⟨check619,ContactValues.valid619⟩
theorem valid620 : ValidPanel panel620 := ⟨check620,ContactValues.valid620⟩
theorem valid621 : ValidPanel panel621 := ⟨check621,ContactValues.valid621⟩
theorem valid622 : ValidPanel panel622 := ⟨check622,ContactValues.valid622⟩
theorem valid623 : ValidPanel panel623 := ⟨check623,ContactValues.valid623⟩
theorem valid624 : ValidPanel panel624 := ⟨check624,ContactValues.valid624⟩
theorem valid625 : ValidPanel panel625 := ⟨check625,ContactValues.valid625⟩
theorem valid626 : ValidPanel panel626 := ⟨check626,ContactValues.valid626⟩
theorem valid627 : ValidPanel panel627 := ⟨check627,ContactValues.valid627⟩
theorem valid628 : ValidPanel panel628 := ⟨check628,ContactValues.valid628⟩
theorem valid629 : ValidPanel panel629 := ⟨check629,ContactValues.valid629⟩
theorem valid630 : ValidPanel panel630 := ⟨check630,ContactValues.valid630⟩
theorem valid631 : ValidPanel panel631 := ⟨check631,ContactValues.valid631⟩
theorem valid632 : ValidPanel panel632 := ⟨check632,ContactValues.valid632⟩
theorem valid633 : ValidPanel panel633 := ⟨check633,ContactValues.valid633⟩
theorem valid634 : ValidPanel panel634 := ⟨check634,ContactValues.valid634⟩
theorem valid635 : ValidPanel panel635 := ⟨check635,ContactValues.valid635⟩
theorem valid636 : ValidPanel panel636 := ⟨check636,ContactValues.valid636⟩
theorem valid637 : ValidPanel panel637 := ⟨check637,ContactValues.valid637⟩
theorem valid638 : ValidPanel panel638 := ⟨check638,ContactValues.valid638⟩
theorem valid639 : ValidPanel panel639 := ⟨check639,ContactValues.valid639⟩
theorem validBlock19 : ∀ p∈block19,ValidPanel p := by
  simp only [block19,List.forall_mem_cons]
  exact ⟨valid608,⟨valid609,⟨valid610,⟨valid611,⟨valid612,⟨valid613,⟨valid614,⟨valid615,⟨valid616,⟨valid617,⟨valid618,⟨valid619,⟨valid620,⟨valid621,⟨valid622,⟨valid623,⟨valid624,⟨valid625,⟨valid626,⟨valid627,⟨valid628,⟨valid629,⟨valid630,⟨valid631,⟨valid632,⟨valid633,⟨valid634,⟨valid635,⟨valid636,⟨valid637,⟨valid638,⟨valid639,(by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end chebyshev2.Certificates.Compact.AmplitudeValues

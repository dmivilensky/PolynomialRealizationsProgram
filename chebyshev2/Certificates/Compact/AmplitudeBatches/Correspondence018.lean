import chebyshev2.Certificates.Compact.AmplitudeBatches.Batch018
import chebyshev2.Certificates.Compact.ContactBatches.Correspondence018
import chebyshev2.Certificates.Compact.AmplitudeProof

/-!
Article: chebyshev2, Section 4.1.
Correspondence018.
Use: `chebyshev2.Certificates.Compact.AmplitudeValues.validBlock18` feeds
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
theorem valid576 : ValidPanel panel576 := ⟨check576,ContactValues.valid576⟩
theorem valid577 : ValidPanel panel577 := ⟨check577,ContactValues.valid577⟩
theorem valid578 : ValidPanel panel578 := ⟨check578,ContactValues.valid578⟩
theorem valid579 : ValidPanel panel579 := ⟨check579,ContactValues.valid579⟩
theorem valid580 : ValidPanel panel580 := ⟨check580,ContactValues.valid580⟩
theorem valid581 : ValidPanel panel581 := ⟨check581,ContactValues.valid581⟩
theorem valid582 : ValidPanel panel582 := ⟨check582,ContactValues.valid582⟩
theorem valid583 : ValidPanel panel583 := ⟨check583,ContactValues.valid583⟩
theorem valid584 : ValidPanel panel584 := ⟨check584,ContactValues.valid584⟩
theorem valid585 : ValidPanel panel585 := ⟨check585,ContactValues.valid585⟩
theorem valid586 : ValidPanel panel586 := ⟨check586,ContactValues.valid586⟩
theorem valid587 : ValidPanel panel587 := ⟨check587,ContactValues.valid587⟩
theorem valid588 : ValidPanel panel588 := ⟨check588,ContactValues.valid588⟩
theorem valid589 : ValidPanel panel589 := ⟨check589,ContactValues.valid589⟩
theorem valid590 : ValidPanel panel590 := ⟨check590,ContactValues.valid590⟩
theorem valid591 : ValidPanel panel591 := ⟨check591,ContactValues.valid591⟩
theorem valid592 : ValidPanel panel592 := ⟨check592,ContactValues.valid592⟩
theorem valid593 : ValidPanel panel593 := ⟨check593,ContactValues.valid593⟩
theorem valid594 : ValidPanel panel594 := ⟨check594,ContactValues.valid594⟩
theorem valid595 : ValidPanel panel595 := ⟨check595,ContactValues.valid595⟩
theorem valid596 : ValidPanel panel596 := ⟨check596,ContactValues.valid596⟩
theorem valid597 : ValidPanel panel597 := ⟨check597,ContactValues.valid597⟩
theorem valid598 : ValidPanel panel598 := ⟨check598,ContactValues.valid598⟩
theorem valid599 : ValidPanel panel599 := ⟨check599,ContactValues.valid599⟩
theorem valid600 : ValidPanel panel600 := ⟨check600,ContactValues.valid600⟩
theorem valid601 : ValidPanel panel601 := ⟨check601,ContactValues.valid601⟩
theorem valid602 : ValidPanel panel602 := ⟨check602,ContactValues.valid602⟩
theorem valid603 : ValidPanel panel603 := ⟨check603,ContactValues.valid603⟩
theorem valid604 : ValidPanel panel604 := ⟨check604,ContactValues.valid604⟩
theorem valid605 : ValidPanel panel605 := ⟨check605,ContactValues.valid605⟩
theorem valid606 : ValidPanel panel606 := ⟨check606,ContactValues.valid606⟩
theorem valid607 : ValidPanel panel607 := ⟨check607,ContactValues.valid607⟩
theorem validBlock18 : ∀ p∈block18,ValidPanel p := by
  simp only [block18,List.forall_mem_cons]
  exact ⟨valid576,⟨valid577,⟨valid578,⟨valid579,⟨valid580,⟨valid581,⟨valid582,⟨valid583,⟨valid584,⟨valid585,⟨valid586,⟨valid587,⟨valid588,⟨valid589,⟨valid590,⟨valid591,⟨valid592,⟨valid593,⟨valid594,⟨valid595,⟨valid596,⟨valid597,⟨valid598,⟨valid599,⟨valid600,⟨valid601,⟨valid602,⟨valid603,⟨valid604,⟨valid605,⟨valid606,⟨valid607,(by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end chebyshev2.Certificates.Compact.AmplitudeValues

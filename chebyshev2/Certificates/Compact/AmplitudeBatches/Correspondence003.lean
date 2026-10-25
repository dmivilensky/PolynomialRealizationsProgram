import chebyshev2.Certificates.Compact.AmplitudeBatches.Batch003
import chebyshev2.Certificates.Compact.ContactBatches.Correspondence003
import chebyshev2.Certificates.Compact.AmplitudeProof

/-!
Article: chebyshev2, Section 4.1.
Correspondence003.
Use: `chebyshev2.Certificates.Compact.AmplitudeValues.validBlock3` feeds
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
theorem valid96 : ValidPanel panel96 := ⟨check96,ContactValues.valid96⟩
theorem valid97 : ValidPanel panel97 := ⟨check97,ContactValues.valid97⟩
theorem valid98 : ValidPanel panel98 := ⟨check98,ContactValues.valid98⟩
theorem valid99 : ValidPanel panel99 := ⟨check99,ContactValues.valid99⟩
theorem valid100 : ValidPanel panel100 := ⟨check100,ContactValues.valid100⟩
theorem valid101 : ValidPanel panel101 := ⟨check101,ContactValues.valid101⟩
theorem valid102 : ValidPanel panel102 := ⟨check102,ContactValues.valid102⟩
theorem valid103 : ValidPanel panel103 := ⟨check103,ContactValues.valid103⟩
theorem valid104 : ValidPanel panel104 := ⟨check104,ContactValues.valid104⟩
theorem valid105 : ValidPanel panel105 := ⟨check105,ContactValues.valid105⟩
theorem valid106 : ValidPanel panel106 := ⟨check106,ContactValues.valid106⟩
theorem valid107 : ValidPanel panel107 := ⟨check107,ContactValues.valid107⟩
theorem valid108 : ValidPanel panel108 := ⟨check108,ContactValues.valid108⟩
theorem valid109 : ValidPanel panel109 := ⟨check109,ContactValues.valid109⟩
theorem valid110 : ValidPanel panel110 := ⟨check110,ContactValues.valid110⟩
theorem valid111 : ValidPanel panel111 := ⟨check111,ContactValues.valid111⟩
theorem valid112 : ValidPanel panel112 := ⟨check112,ContactValues.valid112⟩
theorem valid113 : ValidPanel panel113 := ⟨check113,ContactValues.valid113⟩
theorem valid114 : ValidPanel panel114 := ⟨check114,ContactValues.valid114⟩
theorem valid115 : ValidPanel panel115 := ⟨check115,ContactValues.valid115⟩
theorem valid116 : ValidPanel panel116 := ⟨check116,ContactValues.valid116⟩
theorem valid117 : ValidPanel panel117 := ⟨check117,ContactValues.valid117⟩
theorem valid118 : ValidPanel panel118 := ⟨check118,ContactValues.valid118⟩
theorem valid119 : ValidPanel panel119 := ⟨check119,ContactValues.valid119⟩
theorem valid120 : ValidPanel panel120 := ⟨check120,ContactValues.valid120⟩
theorem valid121 : ValidPanel panel121 := ⟨check121,ContactValues.valid121⟩
theorem valid122 : ValidPanel panel122 := ⟨check122,ContactValues.valid122⟩
theorem valid123 : ValidPanel panel123 := ⟨check123,ContactValues.valid123⟩
theorem valid124 : ValidPanel panel124 := ⟨check124,ContactValues.valid124⟩
theorem valid125 : ValidPanel panel125 := ⟨check125,ContactValues.valid125⟩
theorem valid126 : ValidPanel panel126 := ⟨check126,ContactValues.valid126⟩
theorem valid127 : ValidPanel panel127 := ⟨check127,ContactValues.valid127⟩
theorem validBlock3 : ∀ p∈block3,ValidPanel p := by
  simp only [block3,List.forall_mem_cons]
  exact ⟨valid96,⟨valid97,⟨valid98,⟨valid99,⟨valid100,⟨valid101,⟨valid102,⟨valid103,⟨valid104,⟨valid105,⟨valid106,⟨valid107,⟨valid108,⟨valid109,⟨valid110,⟨valid111,⟨valid112,⟨valid113,⟨valid114,⟨valid115,⟨valid116,⟨valid117,⟨valid118,⟨valid119,⟨valid120,⟨valid121,⟨valid122,⟨valid123,⟨valid124,⟨valid125,⟨valid126,⟨valid127,(by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end chebyshev2.Certificates.Compact.AmplitudeValues

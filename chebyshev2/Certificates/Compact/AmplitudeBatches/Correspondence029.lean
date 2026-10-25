import chebyshev2.Certificates.Compact.AmplitudeBatches.Batch029
import chebyshev2.Certificates.Compact.ContactBatches.Correspondence029
import chebyshev2.Certificates.Compact.AmplitudeProof

/-!
Article: chebyshev2, Section 4.1.
Correspondence029.
Use: `chebyshev2.Certificates.Compact.AmplitudeValues.validBlock29` feeds
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
theorem valid928 : ValidPanel panel928 := ⟨check928,ContactValues.valid928⟩
theorem valid929 : ValidPanel panel929 := ⟨check929,ContactValues.valid929⟩
theorem valid930 : ValidPanel panel930 := ⟨check930,ContactValues.valid930⟩
theorem valid931 : ValidPanel panel931 := ⟨check931,ContactValues.valid931⟩
theorem valid932 : ValidPanel panel932 := ⟨check932,ContactValues.valid932⟩
theorem valid933 : ValidPanel panel933 := ⟨check933,ContactValues.valid933⟩
theorem valid934 : ValidPanel panel934 := ⟨check934,ContactValues.valid934⟩
theorem valid935 : ValidPanel panel935 := ⟨check935,ContactValues.valid935⟩
theorem valid936 : ValidPanel panel936 := ⟨check936,ContactValues.valid936⟩
theorem valid937 : ValidPanel panel937 := ⟨check937,ContactValues.valid937⟩
theorem valid938 : ValidPanel panel938 := ⟨check938,ContactValues.valid938⟩
theorem valid939 : ValidPanel panel939 := ⟨check939,ContactValues.valid939⟩
theorem valid940 : ValidPanel panel940 := ⟨check940,ContactValues.valid940⟩
theorem valid941 : ValidPanel panel941 := ⟨check941,ContactValues.valid941⟩
theorem valid942 : ValidPanel panel942 := ⟨check942,ContactValues.valid942⟩
theorem valid943 : ValidPanel panel943 := ⟨check943,ContactValues.valid943⟩
theorem valid944 : ValidPanel panel944 := ⟨check944,ContactValues.valid944⟩
theorem valid945 : ValidPanel panel945 := ⟨check945,ContactValues.valid945⟩
theorem valid946 : ValidPanel panel946 := ⟨check946,ContactValues.valid946⟩
theorem valid947 : ValidPanel panel947 := ⟨check947,ContactValues.valid947⟩
theorem valid948 : ValidPanel panel948 := ⟨check948,ContactValues.valid948⟩
theorem valid949 : ValidPanel panel949 := ⟨check949,ContactValues.valid949⟩
theorem valid950 : ValidPanel panel950 := ⟨check950,ContactValues.valid950⟩
theorem valid951 : ValidPanel panel951 := ⟨check951,ContactValues.valid951⟩
theorem valid952 : ValidPanel panel952 := ⟨check952,ContactValues.valid952⟩
theorem valid953 : ValidPanel panel953 := ⟨check953,ContactValues.valid953⟩
theorem valid954 : ValidPanel panel954 := ⟨check954,ContactValues.valid954⟩
theorem valid955 : ValidPanel panel955 := ⟨check955,ContactValues.valid955⟩
theorem valid956 : ValidPanel panel956 := ⟨check956,ContactValues.valid956⟩
theorem valid957 : ValidPanel panel957 := ⟨check957,ContactValues.valid957⟩
theorem valid958 : ValidPanel panel958 := ⟨check958,ContactValues.valid958⟩
theorem valid959 : ValidPanel panel959 := ⟨check959,ContactValues.valid959⟩
theorem validBlock29 : ∀ p∈block29,ValidPanel p := by
  simp only [block29,List.forall_mem_cons]
  exact ⟨valid928,⟨valid929,⟨valid930,⟨valid931,⟨valid932,⟨valid933,⟨valid934,⟨valid935,⟨valid936,⟨valid937,⟨valid938,⟨valid939,⟨valid940,⟨valid941,⟨valid942,⟨valid943,⟨valid944,⟨valid945,⟨valid946,⟨valid947,⟨valid948,⟨valid949,⟨valid950,⟨valid951,⟨valid952,⟨valid953,⟨valid954,⟨valid955,⟨valid956,⟨valid957,⟨valid958,⟨valid959,(by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end chebyshev2.Certificates.Compact.AmplitudeValues

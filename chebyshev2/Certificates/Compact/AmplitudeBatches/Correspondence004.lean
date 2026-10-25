import chebyshev2.Certificates.Compact.AmplitudeBatches.Batch004
import chebyshev2.Certificates.Compact.ContactBatches.Correspondence004
import chebyshev2.Certificates.Compact.AmplitudeProof

/-!
Article: chebyshev2, Section 4.1.
Correspondence004.
Use: `chebyshev2.Certificates.Compact.AmplitudeValues.validBlock4` feeds
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
theorem valid128 : ValidPanel panel128 := ⟨check128,ContactValues.valid128⟩
theorem valid129 : ValidPanel panel129 := ⟨check129,ContactValues.valid129⟩
theorem valid130 : ValidPanel panel130 := ⟨check130,ContactValues.valid130⟩
theorem valid131 : ValidPanel panel131 := ⟨check131,ContactValues.valid131⟩
theorem valid132 : ValidPanel panel132 := ⟨check132,ContactValues.valid132⟩
theorem valid133 : ValidPanel panel133 := ⟨check133,ContactValues.valid133⟩
theorem valid134 : ValidPanel panel134 := ⟨check134,ContactValues.valid134⟩
theorem valid135 : ValidPanel panel135 := ⟨check135,ContactValues.valid135⟩
theorem valid136 : ValidPanel panel136 := ⟨check136,ContactValues.valid136⟩
theorem valid137 : ValidPanel panel137 := ⟨check137,ContactValues.valid137⟩
theorem valid138 : ValidPanel panel138 := ⟨check138,ContactValues.valid138⟩
theorem valid139 : ValidPanel panel139 := ⟨check139,ContactValues.valid139⟩
theorem valid140 : ValidPanel panel140 := ⟨check140,ContactValues.valid140⟩
theorem valid141 : ValidPanel panel141 := ⟨check141,ContactValues.valid141⟩
theorem valid142 : ValidPanel panel142 := ⟨check142,ContactValues.valid142⟩
theorem valid143 : ValidPanel panel143 := ⟨check143,ContactValues.valid143⟩
theorem valid144 : ValidPanel panel144 := ⟨check144,ContactValues.valid144⟩
theorem valid145 : ValidPanel panel145 := ⟨check145,ContactValues.valid145⟩
theorem valid146 : ValidPanel panel146 := ⟨check146,ContactValues.valid146⟩
theorem valid147 : ValidPanel panel147 := ⟨check147,ContactValues.valid147⟩
theorem valid148 : ValidPanel panel148 := ⟨check148,ContactValues.valid148⟩
theorem valid149 : ValidPanel panel149 := ⟨check149,ContactValues.valid149⟩
theorem valid150 : ValidPanel panel150 := ⟨check150,ContactValues.valid150⟩
theorem valid151 : ValidPanel panel151 := ⟨check151,ContactValues.valid151⟩
theorem valid152 : ValidPanel panel152 := ⟨check152,ContactValues.valid152⟩
theorem valid153 : ValidPanel panel153 := ⟨check153,ContactValues.valid153⟩
theorem valid154 : ValidPanel panel154 := ⟨check154,ContactValues.valid154⟩
theorem valid155 : ValidPanel panel155 := ⟨check155,ContactValues.valid155⟩
theorem valid156 : ValidPanel panel156 := ⟨check156,ContactValues.valid156⟩
theorem valid157 : ValidPanel panel157 := ⟨check157,ContactValues.valid157⟩
theorem valid158 : ValidPanel panel158 := ⟨check158,ContactValues.valid158⟩
theorem valid159 : ValidPanel panel159 := ⟨check159,ContactValues.valid159⟩
theorem validBlock4 : ∀ p∈block4,ValidPanel p := by
  simp only [block4,List.forall_mem_cons]
  exact ⟨valid128,⟨valid129,⟨valid130,⟨valid131,⟨valid132,⟨valid133,⟨valid134,⟨valid135,⟨valid136,⟨valid137,⟨valid138,⟨valid139,⟨valid140,⟨valid141,⟨valid142,⟨valid143,⟨valid144,⟨valid145,⟨valid146,⟨valid147,⟨valid148,⟨valid149,⟨valid150,⟨valid151,⟨valid152,⟨valid153,⟨valid154,⟨valid155,⟨valid156,⟨valid157,⟨valid158,⟨valid159,(by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end chebyshev2.Certificates.Compact.AmplitudeValues

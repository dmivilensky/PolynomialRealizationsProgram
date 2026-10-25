import chebyshev2.Certificates.Compact.AmplitudeBatches.Batch006
import chebyshev2.Certificates.Compact.ContactBatches.Correspondence006
import chebyshev2.Certificates.Compact.AmplitudeProof

/-!
Article: chebyshev2, Section 4.1.
Correspondence006.
Use: `chebyshev2.Certificates.Compact.AmplitudeValues.validBlock6` feeds
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
theorem valid192 : ValidPanel panel192 := ⟨check192,ContactValues.valid192⟩
theorem valid193 : ValidPanel panel193 := ⟨check193,ContactValues.valid193⟩
theorem valid194 : ValidPanel panel194 := ⟨check194,ContactValues.valid194⟩
theorem valid195 : ValidPanel panel195 := ⟨check195,ContactValues.valid195⟩
theorem valid196 : ValidPanel panel196 := ⟨check196,ContactValues.valid196⟩
theorem valid197 : ValidPanel panel197 := ⟨check197,ContactValues.valid197⟩
theorem valid198 : ValidPanel panel198 := ⟨check198,ContactValues.valid198⟩
theorem valid199 : ValidPanel panel199 := ⟨check199,ContactValues.valid199⟩
theorem valid200 : ValidPanel panel200 := ⟨check200,ContactValues.valid200⟩
theorem valid201 : ValidPanel panel201 := ⟨check201,ContactValues.valid201⟩
theorem valid202 : ValidPanel panel202 := ⟨check202,ContactValues.valid202⟩
theorem valid203 : ValidPanel panel203 := ⟨check203,ContactValues.valid203⟩
theorem valid204 : ValidPanel panel204 := ⟨check204,ContactValues.valid204⟩
theorem valid205 : ValidPanel panel205 := ⟨check205,ContactValues.valid205⟩
theorem valid206 : ValidPanel panel206 := ⟨check206,ContactValues.valid206⟩
theorem valid207 : ValidPanel panel207 := ⟨check207,ContactValues.valid207⟩
theorem valid208 : ValidPanel panel208 := ⟨check208,ContactValues.valid208⟩
theorem valid209 : ValidPanel panel209 := ⟨check209,ContactValues.valid209⟩
theorem valid210 : ValidPanel panel210 := ⟨check210,ContactValues.valid210⟩
theorem valid211 : ValidPanel panel211 := ⟨check211,ContactValues.valid211⟩
theorem valid212 : ValidPanel panel212 := ⟨check212,ContactValues.valid212⟩
theorem valid213 : ValidPanel panel213 := ⟨check213,ContactValues.valid213⟩
theorem valid214 : ValidPanel panel214 := ⟨check214,ContactValues.valid214⟩
theorem valid215 : ValidPanel panel215 := ⟨check215,ContactValues.valid215⟩
theorem valid216 : ValidPanel panel216 := ⟨check216,ContactValues.valid216⟩
theorem valid217 : ValidPanel panel217 := ⟨check217,ContactValues.valid217⟩
theorem valid218 : ValidPanel panel218 := ⟨check218,ContactValues.valid218⟩
theorem valid219 : ValidPanel panel219 := ⟨check219,ContactValues.valid219⟩
theorem valid220 : ValidPanel panel220 := ⟨check220,ContactValues.valid220⟩
theorem valid221 : ValidPanel panel221 := ⟨check221,ContactValues.valid221⟩
theorem valid222 : ValidPanel panel222 := ⟨check222,ContactValues.valid222⟩
theorem valid223 : ValidPanel panel223 := ⟨check223,ContactValues.valid223⟩
theorem validBlock6 : ∀ p∈block6,ValidPanel p := by
  simp only [block6,List.forall_mem_cons]
  exact ⟨valid192,⟨valid193,⟨valid194,⟨valid195,⟨valid196,⟨valid197,⟨valid198,⟨valid199,⟨valid200,⟨valid201,⟨valid202,⟨valid203,⟨valid204,⟨valid205,⟨valid206,⟨valid207,⟨valid208,⟨valid209,⟨valid210,⟨valid211,⟨valid212,⟨valid213,⟨valid214,⟨valid215,⟨valid216,⟨valid217,⟨valid218,⟨valid219,⟨valid220,⟨valid221,⟨valid222,⟨valid223,(by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end chebyshev2.Certificates.Compact.AmplitudeValues

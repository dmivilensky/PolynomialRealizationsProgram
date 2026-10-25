import chebyshev2.Certificates.Compact.AmplitudeBatches.Batch000
import chebyshev2.Certificates.Compact.ContactBatches.Correspondence000
import chebyshev2.Certificates.Compact.AmplitudeProof

/-!
Article: chebyshev2, Section 4.1.
Correspondence000.
Use: `chebyshev2.Certificates.Compact.AmplitudeValues.validBlock0` feeds
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
theorem valid0 : ValidPanel panel0 := ⟨check0,ContactValues.valid0⟩
theorem valid1 : ValidPanel panel1 := ⟨check1,ContactValues.valid1⟩
theorem valid2 : ValidPanel panel2 := ⟨check2,ContactValues.valid2⟩
theorem valid3 : ValidPanel panel3 := ⟨check3,ContactValues.valid3⟩
theorem valid4 : ValidPanel panel4 := ⟨check4,ContactValues.valid4⟩
theorem valid5 : ValidPanel panel5 := ⟨check5,ContactValues.valid5⟩
theorem valid6 : ValidPanel panel6 := ⟨check6,ContactValues.valid6⟩
theorem valid7 : ValidPanel panel7 := ⟨check7,ContactValues.valid7⟩
theorem valid8 : ValidPanel panel8 := ⟨check8,ContactValues.valid8⟩
theorem valid9 : ValidPanel panel9 := ⟨check9,ContactValues.valid9⟩
theorem valid10 : ValidPanel panel10 := ⟨check10,ContactValues.valid10⟩
theorem valid11 : ValidPanel panel11 := ⟨check11,ContactValues.valid11⟩
theorem valid12 : ValidPanel panel12 := ⟨check12,ContactValues.valid12⟩
theorem valid13 : ValidPanel panel13 := ⟨check13,ContactValues.valid13⟩
theorem valid14 : ValidPanel panel14 := ⟨check14,ContactValues.valid14⟩
theorem valid15 : ValidPanel panel15 := ⟨check15,ContactValues.valid15⟩
theorem valid16 : ValidPanel panel16 := ⟨check16,ContactValues.valid16⟩
theorem valid17 : ValidPanel panel17 := ⟨check17,ContactValues.valid17⟩
theorem valid18 : ValidPanel panel18 := ⟨check18,ContactValues.valid18⟩
theorem valid19 : ValidPanel panel19 := ⟨check19,ContactValues.valid19⟩
theorem valid20 : ValidPanel panel20 := ⟨check20,ContactValues.valid20⟩
theorem valid21 : ValidPanel panel21 := ⟨check21,ContactValues.valid21⟩
theorem valid22 : ValidPanel panel22 := ⟨check22,ContactValues.valid22⟩
theorem valid23 : ValidPanel panel23 := ⟨check23,ContactValues.valid23⟩
theorem valid24 : ValidPanel panel24 := ⟨check24,ContactValues.valid24⟩
theorem valid25 : ValidPanel panel25 := ⟨check25,ContactValues.valid25⟩
theorem valid26 : ValidPanel panel26 := ⟨check26,ContactValues.valid26⟩
theorem valid27 : ValidPanel panel27 := ⟨check27,ContactValues.valid27⟩
theorem valid28 : ValidPanel panel28 := ⟨check28,ContactValues.valid28⟩
theorem valid29 : ValidPanel panel29 := ⟨check29,ContactValues.valid29⟩
theorem valid30 : ValidPanel panel30 := ⟨check30,ContactValues.valid30⟩
theorem valid31 : ValidPanel panel31 := ⟨check31,ContactValues.valid31⟩
theorem validBlock0 : ∀ p∈block0,ValidPanel p := by
  simp only [block0,List.forall_mem_cons]
  exact ⟨valid0,⟨valid1,⟨valid2,⟨valid3,⟨valid4,⟨valid5,⟨valid6,⟨valid7,⟨valid8,⟨valid9,⟨valid10,⟨valid11,⟨valid12,⟨valid13,⟨valid14,⟨valid15,⟨valid16,⟨valid17,⟨valid18,⟨valid19,⟨valid20,⟨valid21,⟨valid22,⟨valid23,⟨valid24,⟨valid25,⟨valid26,⟨valid27,⟨valid28,⟨valid29,⟨valid30,⟨valid31,(by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end chebyshev2.Certificates.Compact.AmplitudeValues

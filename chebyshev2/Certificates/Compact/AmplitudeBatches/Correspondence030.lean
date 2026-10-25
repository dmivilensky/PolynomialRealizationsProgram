import chebyshev2.Certificates.Compact.AmplitudeBatches.Batch030
import chebyshev2.Certificates.Compact.ContactBatches.Correspondence030
import chebyshev2.Certificates.Compact.AmplitudeProof

/-!
Article: chebyshev2, Section 4.1.
Correspondence030.
Use: `chebyshev2.Certificates.Compact.AmplitudeValues.validBlock30` feeds
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
theorem valid960 : ValidPanel panel960 := ⟨check960,ContactValues.valid960⟩
theorem valid961 : ValidPanel panel961 := ⟨check961,ContactValues.valid961⟩
theorem valid962 : ValidPanel panel962 := ⟨check962,ContactValues.valid962⟩
theorem valid963 : ValidPanel panel963 := ⟨check963,ContactValues.valid963⟩
theorem valid964 : ValidPanel panel964 := ⟨check964,ContactValues.valid964⟩
theorem valid965 : ValidPanel panel965 := ⟨check965,ContactValues.valid965⟩
theorem valid966 : ValidPanel panel966 := ⟨check966,ContactValues.valid966⟩
theorem valid967 : ValidPanel panel967 := ⟨check967,ContactValues.valid967⟩
theorem valid968 : ValidPanel panel968 := ⟨check968,ContactValues.valid968⟩
theorem valid969 : ValidPanel panel969 := ⟨check969,ContactValues.valid969⟩
theorem valid970 : ValidPanel panel970 := ⟨check970,ContactValues.valid970⟩
theorem valid971 : ValidPanel panel971 := ⟨check971,ContactValues.valid971⟩
theorem valid972 : ValidPanel panel972 := ⟨check972,ContactValues.valid972⟩
theorem valid973 : ValidPanel panel973 := ⟨check973,ContactValues.valid973⟩
theorem valid974 : ValidPanel panel974 := ⟨check974,ContactValues.valid974⟩
theorem valid975 : ValidPanel panel975 := ⟨check975,ContactValues.valid975⟩
theorem valid976 : ValidPanel panel976 := ⟨check976,ContactValues.valid976⟩
theorem valid977 : ValidPanel panel977 := ⟨check977,ContactValues.valid977⟩
theorem valid978 : ValidPanel panel978 := ⟨check978,ContactValues.valid978⟩
theorem valid979 : ValidPanel panel979 := ⟨check979,ContactValues.valid979⟩
theorem valid980 : ValidPanel panel980 := ⟨check980,ContactValues.valid980⟩
theorem valid981 : ValidPanel panel981 := ⟨check981,ContactValues.valid981⟩
theorem valid982 : ValidPanel panel982 := ⟨check982,ContactValues.valid982⟩
theorem valid983 : ValidPanel panel983 := ⟨check983,ContactValues.valid983⟩
theorem valid984 : ValidPanel panel984 := ⟨check984,ContactValues.valid984⟩
theorem valid985 : ValidPanel panel985 := ⟨check985,ContactValues.valid985⟩
theorem valid986 : ValidPanel panel986 := ⟨check986,ContactValues.valid986⟩
theorem valid987 : ValidPanel panel987 := ⟨check987,ContactValues.valid987⟩
theorem valid988 : ValidPanel panel988 := ⟨check988,ContactValues.valid988⟩
theorem valid989 : ValidPanel panel989 := ⟨check989,ContactValues.valid989⟩
theorem valid990 : ValidPanel panel990 := ⟨check990,ContactValues.valid990⟩
theorem valid991 : ValidPanel panel991 := ⟨check991,ContactValues.valid991⟩
theorem validBlock30 : ∀ p∈block30,ValidPanel p := by
  simp only [block30,List.forall_mem_cons]
  exact ⟨valid960,⟨valid961,⟨valid962,⟨valid963,⟨valid964,⟨valid965,⟨valid966,⟨valid967,⟨valid968,⟨valid969,⟨valid970,⟨valid971,⟨valid972,⟨valid973,⟨valid974,⟨valid975,⟨valid976,⟨valid977,⟨valid978,⟨valid979,⟨valid980,⟨valid981,⟨valid982,⟨valid983,⟨valid984,⟨valid985,⟨valid986,⟨valid987,⟨valid988,⟨valid989,⟨valid990,⟨valid991,(by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end chebyshev2.Certificates.Compact.AmplitudeValues

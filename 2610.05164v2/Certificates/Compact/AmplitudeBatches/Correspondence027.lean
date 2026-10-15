import «2610.05164v2».Certificates.Compact.AmplitudeBatches.Batch027
import «2610.05164v2».Certificates.Compact.ContactBatches.Correspondence027
import «2610.05164v2».Certificates.Compact.AmplitudeProof

/-!
Article: 2610.05164v2, Section 4.1.
Correspondence027.
Use: `«2610.05164v2».Certificates.Compact.AmplitudeValues.validBlock27` feeds
`«2610.05164v2».Certificates.Compact.AmplitudeValues.all_valid` (all valid).
Proof chain: `«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement` —
2610.05164v2, Theorem 1.2, factor 1.000013; Unconditional uniform gain comparison with the retained
numerical factor.
-/
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 200000
set_option maxHeartbeats 0
namespace «2610.05164v2».Certificates.Compact.AmplitudeValues
open «2610.05164v2».Numerics.IntegerCertificate
theorem valid864 : ValidPanel panel864 := ⟨check864,ContactValues.valid864⟩
theorem valid865 : ValidPanel panel865 := ⟨check865,ContactValues.valid865⟩
theorem valid866 : ValidPanel panel866 := ⟨check866,ContactValues.valid866⟩
theorem valid867 : ValidPanel panel867 := ⟨check867,ContactValues.valid867⟩
theorem valid868 : ValidPanel panel868 := ⟨check868,ContactValues.valid868⟩
theorem valid869 : ValidPanel panel869 := ⟨check869,ContactValues.valid869⟩
theorem valid870 : ValidPanel panel870 := ⟨check870,ContactValues.valid870⟩
theorem valid871 : ValidPanel panel871 := ⟨check871,ContactValues.valid871⟩
theorem valid872 : ValidPanel panel872 := ⟨check872,ContactValues.valid872⟩
theorem valid873 : ValidPanel panel873 := ⟨check873,ContactValues.valid873⟩
theorem valid874 : ValidPanel panel874 := ⟨check874,ContactValues.valid874⟩
theorem valid875 : ValidPanel panel875 := ⟨check875,ContactValues.valid875⟩
theorem valid876 : ValidPanel panel876 := ⟨check876,ContactValues.valid876⟩
theorem valid877 : ValidPanel panel877 := ⟨check877,ContactValues.valid877⟩
theorem valid878 : ValidPanel panel878 := ⟨check878,ContactValues.valid878⟩
theorem valid879 : ValidPanel panel879 := ⟨check879,ContactValues.valid879⟩
theorem valid880 : ValidPanel panel880 := ⟨check880,ContactValues.valid880⟩
theorem valid881 : ValidPanel panel881 := ⟨check881,ContactValues.valid881⟩
theorem valid882 : ValidPanel panel882 := ⟨check882,ContactValues.valid882⟩
theorem valid883 : ValidPanel panel883 := ⟨check883,ContactValues.valid883⟩
theorem valid884 : ValidPanel panel884 := ⟨check884,ContactValues.valid884⟩
theorem valid885 : ValidPanel panel885 := ⟨check885,ContactValues.valid885⟩
theorem valid886 : ValidPanel panel886 := ⟨check886,ContactValues.valid886⟩
theorem valid887 : ValidPanel panel887 := ⟨check887,ContactValues.valid887⟩
theorem valid888 : ValidPanel panel888 := ⟨check888,ContactValues.valid888⟩
theorem valid889 : ValidPanel panel889 := ⟨check889,ContactValues.valid889⟩
theorem valid890 : ValidPanel panel890 := ⟨check890,ContactValues.valid890⟩
theorem valid891 : ValidPanel panel891 := ⟨check891,ContactValues.valid891⟩
theorem valid892 : ValidPanel panel892 := ⟨check892,ContactValues.valid892⟩
theorem valid893 : ValidPanel panel893 := ⟨check893,ContactValues.valid893⟩
theorem valid894 : ValidPanel panel894 := ⟨check894,ContactValues.valid894⟩
theorem valid895 : ValidPanel panel895 := ⟨check895,ContactValues.valid895⟩
theorem validBlock27 : ∀ p∈block27,ValidPanel p := by
  simp only [block27,List.forall_mem_cons]
  exact ⟨valid864,⟨valid865,⟨valid866,⟨valid867,⟨valid868,⟨valid869,⟨valid870,⟨valid871,⟨valid872,⟨valid873,⟨valid874,⟨valid875,⟨valid876,⟨valid877,⟨valid878,⟨valid879,⟨valid880,⟨valid881,⟨valid882,⟨valid883,⟨valid884,⟨valid885,⟨valid886,⟨valid887,⟨valid888,⟨valid889,⟨valid890,⟨valid891,⟨valid892,⟨valid893,⟨valid894,⟨valid895,(by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end «2610.05164v2».Certificates.Compact.AmplitudeValues

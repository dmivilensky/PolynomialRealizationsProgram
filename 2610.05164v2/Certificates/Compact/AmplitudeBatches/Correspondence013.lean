import «2610.05164v2».Certificates.Compact.AmplitudeBatches.Batch013
import «2610.05164v2».Certificates.Compact.ContactBatches.Correspondence013
import «2610.05164v2».Certificates.Compact.AmplitudeProof

/-!
Article: 2610.05164v2, Section 4.1.
Correspondence013.
Use: `«2610.05164v2».Certificates.Compact.AmplitudeValues.validBlock13` feeds
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
theorem valid416 : ValidPanel panel416 := ⟨check416,ContactValues.valid416⟩
theorem valid417 : ValidPanel panel417 := ⟨check417,ContactValues.valid417⟩
theorem valid418 : ValidPanel panel418 := ⟨check418,ContactValues.valid418⟩
theorem valid419 : ValidPanel panel419 := ⟨check419,ContactValues.valid419⟩
theorem valid420 : ValidPanel panel420 := ⟨check420,ContactValues.valid420⟩
theorem valid421 : ValidPanel panel421 := ⟨check421,ContactValues.valid421⟩
theorem valid422 : ValidPanel panel422 := ⟨check422,ContactValues.valid422⟩
theorem valid423 : ValidPanel panel423 := ⟨check423,ContactValues.valid423⟩
theorem valid424 : ValidPanel panel424 := ⟨check424,ContactValues.valid424⟩
theorem valid425 : ValidPanel panel425 := ⟨check425,ContactValues.valid425⟩
theorem valid426 : ValidPanel panel426 := ⟨check426,ContactValues.valid426⟩
theorem valid427 : ValidPanel panel427 := ⟨check427,ContactValues.valid427⟩
theorem valid428 : ValidPanel panel428 := ⟨check428,ContactValues.valid428⟩
theorem valid429 : ValidPanel panel429 := ⟨check429,ContactValues.valid429⟩
theorem valid430 : ValidPanel panel430 := ⟨check430,ContactValues.valid430⟩
theorem valid431 : ValidPanel panel431 := ⟨check431,ContactValues.valid431⟩
theorem valid432 : ValidPanel panel432 := ⟨check432,ContactValues.valid432⟩
theorem valid433 : ValidPanel panel433 := ⟨check433,ContactValues.valid433⟩
theorem valid434 : ValidPanel panel434 := ⟨check434,ContactValues.valid434⟩
theorem valid435 : ValidPanel panel435 := ⟨check435,ContactValues.valid435⟩
theorem valid436 : ValidPanel panel436 := ⟨check436,ContactValues.valid436⟩
theorem valid437 : ValidPanel panel437 := ⟨check437,ContactValues.valid437⟩
theorem valid438 : ValidPanel panel438 := ⟨check438,ContactValues.valid438⟩
theorem valid439 : ValidPanel panel439 := ⟨check439,ContactValues.valid439⟩
theorem valid440 : ValidPanel panel440 := ⟨check440,ContactValues.valid440⟩
theorem valid441 : ValidPanel panel441 := ⟨check441,ContactValues.valid441⟩
theorem valid442 : ValidPanel panel442 := ⟨check442,ContactValues.valid442⟩
theorem valid443 : ValidPanel panel443 := ⟨check443,ContactValues.valid443⟩
theorem valid444 : ValidPanel panel444 := ⟨check444,ContactValues.valid444⟩
theorem valid445 : ValidPanel panel445 := ⟨check445,ContactValues.valid445⟩
theorem valid446 : ValidPanel panel446 := ⟨check446,ContactValues.valid446⟩
theorem valid447 : ValidPanel panel447 := ⟨check447,ContactValues.valid447⟩
theorem validBlock13 : ∀ p∈block13,ValidPanel p := by
  simp only [block13,List.forall_mem_cons]
  exact ⟨valid416,⟨valid417,⟨valid418,⟨valid419,⟨valid420,⟨valid421,⟨valid422,⟨valid423,⟨valid424,⟨valid425,⟨valid426,⟨valid427,⟨valid428,⟨valid429,⟨valid430,⟨valid431,⟨valid432,⟨valid433,⟨valid434,⟨valid435,⟨valid436,⟨valid437,⟨valid438,⟨valid439,⟨valid440,⟨valid441,⟨valid442,⟨valid443,⟨valid444,⟨valid445,⟨valid446,⟨valid447,(by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end «2610.05164v2».Certificates.Compact.AmplitudeValues

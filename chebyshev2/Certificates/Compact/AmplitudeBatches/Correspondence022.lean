import chebyshev2.Certificates.Compact.AmplitudeBatches.Batch022
import chebyshev2.Certificates.Compact.ContactBatches.Correspondence022
import chebyshev2.Certificates.Compact.AmplitudeProof

/-!
Article: chebyshev2, Section 4.1.
Correspondence022.
Use: `chebyshev2.Certificates.Compact.AmplitudeValues.validBlock22` feeds
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
theorem valid704 : ValidPanel panel704 := ⟨check704,ContactValues.valid704⟩
theorem valid705 : ValidPanel panel705 := ⟨check705,ContactValues.valid705⟩
theorem valid706 : ValidPanel panel706 := ⟨check706,ContactValues.valid706⟩
theorem valid707 : ValidPanel panel707 := ⟨check707,ContactValues.valid707⟩
theorem valid708 : ValidPanel panel708 := ⟨check708,ContactValues.valid708⟩
theorem valid709 : ValidPanel panel709 := ⟨check709,ContactValues.valid709⟩
theorem valid710 : ValidPanel panel710 := ⟨check710,ContactValues.valid710⟩
theorem valid711 : ValidPanel panel711 := ⟨check711,ContactValues.valid711⟩
theorem valid712 : ValidPanel panel712 := ⟨check712,ContactValues.valid712⟩
theorem valid713 : ValidPanel panel713 := ⟨check713,ContactValues.valid713⟩
theorem valid714 : ValidPanel panel714 := ⟨check714,ContactValues.valid714⟩
theorem valid715 : ValidPanel panel715 := ⟨check715,ContactValues.valid715⟩
theorem valid716 : ValidPanel panel716 := ⟨check716,ContactValues.valid716⟩
theorem valid717 : ValidPanel panel717 := ⟨check717,ContactValues.valid717⟩
theorem valid718 : ValidPanel panel718 := ⟨check718,ContactValues.valid718⟩
theorem valid719 : ValidPanel panel719 := ⟨check719,ContactValues.valid719⟩
theorem valid720 : ValidPanel panel720 := ⟨check720,ContactValues.valid720⟩
theorem valid721 : ValidPanel panel721 := ⟨check721,ContactValues.valid721⟩
theorem valid722 : ValidPanel panel722 := ⟨check722,ContactValues.valid722⟩
theorem valid723 : ValidPanel panel723 := ⟨check723,ContactValues.valid723⟩
theorem valid724 : ValidPanel panel724 := ⟨check724,ContactValues.valid724⟩
theorem valid725 : ValidPanel panel725 := ⟨check725,ContactValues.valid725⟩
theorem valid726 : ValidPanel panel726 := ⟨check726,ContactValues.valid726⟩
theorem valid727 : ValidPanel panel727 := ⟨check727,ContactValues.valid727⟩
theorem valid728 : ValidPanel panel728 := ⟨check728,ContactValues.valid728⟩
theorem valid729 : ValidPanel panel729 := ⟨check729,ContactValues.valid729⟩
theorem valid730 : ValidPanel panel730 := ⟨check730,ContactValues.valid730⟩
theorem valid731 : ValidPanel panel731 := ⟨check731,ContactValues.valid731⟩
theorem valid732 : ValidPanel panel732 := ⟨check732,ContactValues.valid732⟩
theorem valid733 : ValidPanel panel733 := ⟨check733,ContactValues.valid733⟩
theorem valid734 : ValidPanel panel734 := ⟨check734,ContactValues.valid734⟩
theorem valid735 : ValidPanel panel735 := ⟨check735,ContactValues.valid735⟩
theorem validBlock22 : ∀ p∈block22,ValidPanel p := by
  simp only [block22,List.forall_mem_cons]
  exact ⟨valid704,⟨valid705,⟨valid706,⟨valid707,⟨valid708,⟨valid709,⟨valid710,⟨valid711,⟨valid712,⟨valid713,⟨valid714,⟨valid715,⟨valid716,⟨valid717,⟨valid718,⟨valid719,⟨valid720,⟨valid721,⟨valid722,⟨valid723,⟨valid724,⟨valid725,⟨valid726,⟨valid727,⟨valid728,⟨valid729,⟨valid730,⟨valid731,⟨valid732,⟨valid733,⟨valid734,⟨valid735,(by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end chebyshev2.Certificates.Compact.AmplitudeValues

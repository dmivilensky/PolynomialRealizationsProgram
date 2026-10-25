import chebyshev2.Certificates.Compact.AmplitudeBatches.Batch026
import chebyshev2.Certificates.Compact.ContactBatches.Correspondence026
import chebyshev2.Certificates.Compact.AmplitudeProof

/-!
Article: chebyshev2, Section 4.1.
Correspondence026.
Use: `chebyshev2.Certificates.Compact.AmplitudeValues.validBlock26` feeds
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
theorem valid832 : ValidPanel panel832 := ⟨check832,ContactValues.valid832⟩
theorem valid833 : ValidPanel panel833 := ⟨check833,ContactValues.valid833⟩
theorem valid834 : ValidPanel panel834 := ⟨check834,ContactValues.valid834⟩
theorem valid835 : ValidPanel panel835 := ⟨check835,ContactValues.valid835⟩
theorem valid836 : ValidPanel panel836 := ⟨check836,ContactValues.valid836⟩
theorem valid837 : ValidPanel panel837 := ⟨check837,ContactValues.valid837⟩
theorem valid838 : ValidPanel panel838 := ⟨check838,ContactValues.valid838⟩
theorem valid839 : ValidPanel panel839 := ⟨check839,ContactValues.valid839⟩
theorem valid840 : ValidPanel panel840 := ⟨check840,ContactValues.valid840⟩
theorem valid841 : ValidPanel panel841 := ⟨check841,ContactValues.valid841⟩
theorem valid842 : ValidPanel panel842 := ⟨check842,ContactValues.valid842⟩
theorem valid843 : ValidPanel panel843 := ⟨check843,ContactValues.valid843⟩
theorem valid844 : ValidPanel panel844 := ⟨check844,ContactValues.valid844⟩
theorem valid845 : ValidPanel panel845 := ⟨check845,ContactValues.valid845⟩
theorem valid846 : ValidPanel panel846 := ⟨check846,ContactValues.valid846⟩
theorem valid847 : ValidPanel panel847 := ⟨check847,ContactValues.valid847⟩
theorem valid848 : ValidPanel panel848 := ⟨check848,ContactValues.valid848⟩
theorem valid849 : ValidPanel panel849 := ⟨check849,ContactValues.valid849⟩
theorem valid850 : ValidPanel panel850 := ⟨check850,ContactValues.valid850⟩
theorem valid851 : ValidPanel panel851 := ⟨check851,ContactValues.valid851⟩
theorem valid852 : ValidPanel panel852 := ⟨check852,ContactValues.valid852⟩
theorem valid853 : ValidPanel panel853 := ⟨check853,ContactValues.valid853⟩
theorem valid854 : ValidPanel panel854 := ⟨check854,ContactValues.valid854⟩
theorem valid855 : ValidPanel panel855 := ⟨check855,ContactValues.valid855⟩
theorem valid856 : ValidPanel panel856 := ⟨check856,ContactValues.valid856⟩
theorem valid857 : ValidPanel panel857 := ⟨check857,ContactValues.valid857⟩
theorem valid858 : ValidPanel panel858 := ⟨check858,ContactValues.valid858⟩
theorem valid859 : ValidPanel panel859 := ⟨check859,ContactValues.valid859⟩
theorem valid860 : ValidPanel panel860 := ⟨check860,ContactValues.valid860⟩
theorem valid861 : ValidPanel panel861 := ⟨check861,ContactValues.valid861⟩
theorem valid862 : ValidPanel panel862 := ⟨check862,ContactValues.valid862⟩
theorem valid863 : ValidPanel panel863 := ⟨check863,ContactValues.valid863⟩
theorem validBlock26 : ∀ p∈block26,ValidPanel p := by
  simp only [block26,List.forall_mem_cons]
  exact ⟨valid832,⟨valid833,⟨valid834,⟨valid835,⟨valid836,⟨valid837,⟨valid838,⟨valid839,⟨valid840,⟨valid841,⟨valid842,⟨valid843,⟨valid844,⟨valid845,⟨valid846,⟨valid847,⟨valid848,⟨valid849,⟨valid850,⟨valid851,⟨valid852,⟨valid853,⟨valid854,⟨valid855,⟨valid856,⟨valid857,⟨valid858,⟨valid859,⟨valid860,⟨valid861,⟨valid862,⟨valid863,(by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end chebyshev2.Certificates.Compact.AmplitudeValues

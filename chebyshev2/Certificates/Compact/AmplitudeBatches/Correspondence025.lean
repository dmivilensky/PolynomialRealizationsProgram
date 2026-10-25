import chebyshev2.Certificates.Compact.AmplitudeBatches.Batch025
import chebyshev2.Certificates.Compact.ContactBatches.Correspondence025
import chebyshev2.Certificates.Compact.AmplitudeProof

/-!
Article: chebyshev2, Section 4.1.
Correspondence025.
Use: `chebyshev2.Certificates.Compact.AmplitudeValues.validBlock25` feeds
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
theorem valid800 : ValidPanel panel800 := ⟨check800,ContactValues.valid800⟩
theorem valid801 : ValidPanel panel801 := ⟨check801,ContactValues.valid801⟩
theorem valid802 : ValidPanel panel802 := ⟨check802,ContactValues.valid802⟩
theorem valid803 : ValidPanel panel803 := ⟨check803,ContactValues.valid803⟩
theorem valid804 : ValidPanel panel804 := ⟨check804,ContactValues.valid804⟩
theorem valid805 : ValidPanel panel805 := ⟨check805,ContactValues.valid805⟩
theorem valid806 : ValidPanel panel806 := ⟨check806,ContactValues.valid806⟩
theorem valid807 : ValidPanel panel807 := ⟨check807,ContactValues.valid807⟩
theorem valid808 : ValidPanel panel808 := ⟨check808,ContactValues.valid808⟩
theorem valid809 : ValidPanel panel809 := ⟨check809,ContactValues.valid809⟩
theorem valid810 : ValidPanel panel810 := ⟨check810,ContactValues.valid810⟩
theorem valid811 : ValidPanel panel811 := ⟨check811,ContactValues.valid811⟩
theorem valid812 : ValidPanel panel812 := ⟨check812,ContactValues.valid812⟩
theorem valid813 : ValidPanel panel813 := ⟨check813,ContactValues.valid813⟩
theorem valid814 : ValidPanel panel814 := ⟨check814,ContactValues.valid814⟩
theorem valid815 : ValidPanel panel815 := ⟨check815,ContactValues.valid815⟩
theorem valid816 : ValidPanel panel816 := ⟨check816,ContactValues.valid816⟩
theorem valid817 : ValidPanel panel817 := ⟨check817,ContactValues.valid817⟩
theorem valid818 : ValidPanel panel818 := ⟨check818,ContactValues.valid818⟩
theorem valid819 : ValidPanel panel819 := ⟨check819,ContactValues.valid819⟩
theorem valid820 : ValidPanel panel820 := ⟨check820,ContactValues.valid820⟩
theorem valid821 : ValidPanel panel821 := ⟨check821,ContactValues.valid821⟩
theorem valid822 : ValidPanel panel822 := ⟨check822,ContactValues.valid822⟩
theorem valid823 : ValidPanel panel823 := ⟨check823,ContactValues.valid823⟩
theorem valid824 : ValidPanel panel824 := ⟨check824,ContactValues.valid824⟩
theorem valid825 : ValidPanel panel825 := ⟨check825,ContactValues.valid825⟩
theorem valid826 : ValidPanel panel826 := ⟨check826,ContactValues.valid826⟩
theorem valid827 : ValidPanel panel827 := ⟨check827,ContactValues.valid827⟩
theorem valid828 : ValidPanel panel828 := ⟨check828,ContactValues.valid828⟩
theorem valid829 : ValidPanel panel829 := ⟨check829,ContactValues.valid829⟩
theorem valid830 : ValidPanel panel830 := ⟨check830,ContactValues.valid830⟩
theorem valid831 : ValidPanel panel831 := ⟨check831,ContactValues.valid831⟩
theorem validBlock25 : ∀ p∈block25,ValidPanel p := by
  simp only [block25,List.forall_mem_cons]
  exact ⟨valid800,⟨valid801,⟨valid802,⟨valid803,⟨valid804,⟨valid805,⟨valid806,⟨valid807,⟨valid808,⟨valid809,⟨valid810,⟨valid811,⟨valid812,⟨valid813,⟨valid814,⟨valid815,⟨valid816,⟨valid817,⟨valid818,⟨valid819,⟨valid820,⟨valid821,⟨valid822,⟨valid823,⟨valid824,⟨valid825,⟨valid826,⟨valid827,⟨valid828,⟨valid829,⟨valid830,⟨valid831,(by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end chebyshev2.Certificates.Compact.AmplitudeValues

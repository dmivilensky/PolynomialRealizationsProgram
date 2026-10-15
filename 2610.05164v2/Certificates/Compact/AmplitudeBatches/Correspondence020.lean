import «2610.05164v2».Certificates.Compact.AmplitudeBatches.Batch020
import «2610.05164v2».Certificates.Compact.ContactBatches.Correspondence020
import «2610.05164v2».Certificates.Compact.AmplitudeProof

/-!
Article: 2610.05164v2, Section 4.1.
Correspondence020.
Use: `«2610.05164v2».Certificates.Compact.AmplitudeValues.validBlock20` feeds
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
theorem valid640 : ValidPanel panel640 := ⟨check640,ContactValues.valid640⟩
theorem valid641 : ValidPanel panel641 := ⟨check641,ContactValues.valid641⟩
theorem valid642 : ValidPanel panel642 := ⟨check642,ContactValues.valid642⟩
theorem valid643 : ValidPanel panel643 := ⟨check643,ContactValues.valid643⟩
theorem valid644 : ValidPanel panel644 := ⟨check644,ContactValues.valid644⟩
theorem valid645 : ValidPanel panel645 := ⟨check645,ContactValues.valid645⟩
theorem valid646 : ValidPanel panel646 := ⟨check646,ContactValues.valid646⟩
theorem valid647 : ValidPanel panel647 := ⟨check647,ContactValues.valid647⟩
theorem valid648 : ValidPanel panel648 := ⟨check648,ContactValues.valid648⟩
theorem valid649 : ValidPanel panel649 := ⟨check649,ContactValues.valid649⟩
theorem valid650 : ValidPanel panel650 := ⟨check650,ContactValues.valid650⟩
theorem valid651 : ValidPanel panel651 := ⟨check651,ContactValues.valid651⟩
theorem valid652 : ValidPanel panel652 := ⟨check652,ContactValues.valid652⟩
theorem valid653 : ValidPanel panel653 := ⟨check653,ContactValues.valid653⟩
theorem valid654 : ValidPanel panel654 := ⟨check654,ContactValues.valid654⟩
theorem valid655 : ValidPanel panel655 := ⟨check655,ContactValues.valid655⟩
theorem valid656 : ValidPanel panel656 := ⟨check656,ContactValues.valid656⟩
theorem valid657 : ValidPanel panel657 := ⟨check657,ContactValues.valid657⟩
theorem valid658 : ValidPanel panel658 := ⟨check658,ContactValues.valid658⟩
theorem valid659 : ValidPanel panel659 := ⟨check659,ContactValues.valid659⟩
theorem valid660 : ValidPanel panel660 := ⟨check660,ContactValues.valid660⟩
theorem valid661 : ValidPanel panel661 := ⟨check661,ContactValues.valid661⟩
theorem valid662 : ValidPanel panel662 := ⟨check662,ContactValues.valid662⟩
theorem valid663 : ValidPanel panel663 := ⟨check663,ContactValues.valid663⟩
theorem valid664 : ValidPanel panel664 := ⟨check664,ContactValues.valid664⟩
theorem valid665 : ValidPanel panel665 := ⟨check665,ContactValues.valid665⟩
theorem valid666 : ValidPanel panel666 := ⟨check666,ContactValues.valid666⟩
theorem valid667 : ValidPanel panel667 := ⟨check667,ContactValues.valid667⟩
theorem valid668 : ValidPanel panel668 := ⟨check668,ContactValues.valid668⟩
theorem valid669 : ValidPanel panel669 := ⟨check669,ContactValues.valid669⟩
theorem valid670 : ValidPanel panel670 := ⟨check670,ContactValues.valid670⟩
theorem valid671 : ValidPanel panel671 := ⟨check671,ContactValues.valid671⟩
theorem validBlock20 : ∀ p∈block20,ValidPanel p := by
  simp only [block20,List.forall_mem_cons]
  exact ⟨valid640,⟨valid641,⟨valid642,⟨valid643,⟨valid644,⟨valid645,⟨valid646,⟨valid647,⟨valid648,⟨valid649,⟨valid650,⟨valid651,⟨valid652,⟨valid653,⟨valid654,⟨valid655,⟨valid656,⟨valid657,⟨valid658,⟨valid659,⟨valid660,⟨valid661,⟨valid662,⟨valid663,⟨valid664,⟨valid665,⟨valid666,⟨valid667,⟨valid668,⟨valid669,⟨valid670,⟨valid671,(by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end «2610.05164v2».Certificates.Compact.AmplitudeValues

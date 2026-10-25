import chebyshev2.Certificates.Compact.AmplitudeBatches.Batch023
import chebyshev2.Certificates.Compact.ContactBatches.Correspondence023
import chebyshev2.Certificates.Compact.AmplitudeProof

/-!
Article: chebyshev2, Section 4.1.
Correspondence023.
Use: `chebyshev2.Certificates.Compact.AmplitudeValues.validBlock23` feeds
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
theorem valid736 : ValidPanel panel736 := ⟨check736,ContactValues.valid736⟩
theorem valid737 : ValidPanel panel737 := ⟨check737,ContactValues.valid737⟩
theorem valid738 : ValidPanel panel738 := ⟨check738,ContactValues.valid738⟩
theorem valid739 : ValidPanel panel739 := ⟨check739,ContactValues.valid739⟩
theorem valid740 : ValidPanel panel740 := ⟨check740,ContactValues.valid740⟩
theorem valid741 : ValidPanel panel741 := ⟨check741,ContactValues.valid741⟩
theorem valid742 : ValidPanel panel742 := ⟨check742,ContactValues.valid742⟩
theorem valid743 : ValidPanel panel743 := ⟨check743,ContactValues.valid743⟩
theorem valid744 : ValidPanel panel744 := ⟨check744,ContactValues.valid744⟩
theorem valid745 : ValidPanel panel745 := ⟨check745,ContactValues.valid745⟩
theorem valid746 : ValidPanel panel746 := ⟨check746,ContactValues.valid746⟩
theorem valid747 : ValidPanel panel747 := ⟨check747,ContactValues.valid747⟩
theorem valid748 : ValidPanel panel748 := ⟨check748,ContactValues.valid748⟩
theorem valid749 : ValidPanel panel749 := ⟨check749,ContactValues.valid749⟩
theorem valid750 : ValidPanel panel750 := ⟨check750,ContactValues.valid750⟩
theorem valid751 : ValidPanel panel751 := ⟨check751,ContactValues.valid751⟩
theorem valid752 : ValidPanel panel752 := ⟨check752,ContactValues.valid752⟩
theorem valid753 : ValidPanel panel753 := ⟨check753,ContactValues.valid753⟩
theorem valid754 : ValidPanel panel754 := ⟨check754,ContactValues.valid754⟩
theorem valid755 : ValidPanel panel755 := ⟨check755,ContactValues.valid755⟩
theorem valid756 : ValidPanel panel756 := ⟨check756,ContactValues.valid756⟩
theorem valid757 : ValidPanel panel757 := ⟨check757,ContactValues.valid757⟩
theorem valid758 : ValidPanel panel758 := ⟨check758,ContactValues.valid758⟩
theorem valid759 : ValidPanel panel759 := ⟨check759,ContactValues.valid759⟩
theorem valid760 : ValidPanel panel760 := ⟨check760,ContactValues.valid760⟩
theorem valid761 : ValidPanel panel761 := ⟨check761,ContactValues.valid761⟩
theorem valid762 : ValidPanel panel762 := ⟨check762,ContactValues.valid762⟩
theorem valid763 : ValidPanel panel763 := ⟨check763,ContactValues.valid763⟩
theorem valid764 : ValidPanel panel764 := ⟨check764,ContactValues.valid764⟩
theorem valid765 : ValidPanel panel765 := ⟨check765,ContactValues.valid765⟩
theorem valid766 : ValidPanel panel766 := ⟨check766,ContactValues.valid766⟩
theorem valid767 : ValidPanel panel767 := ⟨check767,ContactValues.valid767⟩
theorem validBlock23 : ∀ p∈block23,ValidPanel p := by
  simp only [block23,List.forall_mem_cons]
  exact ⟨valid736,⟨valid737,⟨valid738,⟨valid739,⟨valid740,⟨valid741,⟨valid742,⟨valid743,⟨valid744,⟨valid745,⟨valid746,⟨valid747,⟨valid748,⟨valid749,⟨valid750,⟨valid751,⟨valid752,⟨valid753,⟨valid754,⟨valid755,⟨valid756,⟨valid757,⟨valid758,⟨valid759,⟨valid760,⟨valid761,⟨valid762,⟨valid763,⟨valid764,⟨valid765,⟨valid766,⟨valid767,(by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end chebyshev2.Certificates.Compact.AmplitudeValues

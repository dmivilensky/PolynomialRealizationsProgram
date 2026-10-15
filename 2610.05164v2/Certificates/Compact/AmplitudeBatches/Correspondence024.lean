import «2610.05164v2».Certificates.Compact.AmplitudeBatches.Batch024
import «2610.05164v2».Certificates.Compact.ContactBatches.Correspondence024
import «2610.05164v2».Certificates.Compact.AmplitudeProof

/-!
Article: 2610.05164v2, Section 4.1.
Correspondence024.
Use: `«2610.05164v2».Certificates.Compact.AmplitudeValues.validBlock24` feeds
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
theorem valid768 : ValidPanel panel768 := ⟨check768,ContactValues.valid768⟩
theorem valid769 : ValidPanel panel769 := ⟨check769,ContactValues.valid769⟩
theorem valid770 : ValidPanel panel770 := ⟨check770,ContactValues.valid770⟩
theorem valid771 : ValidPanel panel771 := ⟨check771,ContactValues.valid771⟩
theorem valid772 : ValidPanel panel772 := ⟨check772,ContactValues.valid772⟩
theorem valid773 : ValidPanel panel773 := ⟨check773,ContactValues.valid773⟩
theorem valid774 : ValidPanel panel774 := ⟨check774,ContactValues.valid774⟩
theorem valid775 : ValidPanel panel775 := ⟨check775,ContactValues.valid775⟩
theorem valid776 : ValidPanel panel776 := ⟨check776,ContactValues.valid776⟩
theorem valid777 : ValidPanel panel777 := ⟨check777,ContactValues.valid777⟩
theorem valid778 : ValidPanel panel778 := ⟨check778,ContactValues.valid778⟩
theorem valid779 : ValidPanel panel779 := ⟨check779,ContactValues.valid779⟩
theorem valid780 : ValidPanel panel780 := ⟨check780,ContactValues.valid780⟩
theorem valid781 : ValidPanel panel781 := ⟨check781,ContactValues.valid781⟩
theorem valid782 : ValidPanel panel782 := ⟨check782,ContactValues.valid782⟩
theorem valid783 : ValidPanel panel783 := ⟨check783,ContactValues.valid783⟩
theorem valid784 : ValidPanel panel784 := ⟨check784,ContactValues.valid784⟩
theorem valid785 : ValidPanel panel785 := ⟨check785,ContactValues.valid785⟩
theorem valid786 : ValidPanel panel786 := ⟨check786,ContactValues.valid786⟩
theorem valid787 : ValidPanel panel787 := ⟨check787,ContactValues.valid787⟩
theorem valid788 : ValidPanel panel788 := ⟨check788,ContactValues.valid788⟩
theorem valid789 : ValidPanel panel789 := ⟨check789,ContactValues.valid789⟩
theorem valid790 : ValidPanel panel790 := ⟨check790,ContactValues.valid790⟩
theorem valid791 : ValidPanel panel791 := ⟨check791,ContactValues.valid791⟩
theorem valid792 : ValidPanel panel792 := ⟨check792,ContactValues.valid792⟩
theorem valid793 : ValidPanel panel793 := ⟨check793,ContactValues.valid793⟩
theorem valid794 : ValidPanel panel794 := ⟨check794,ContactValues.valid794⟩
theorem valid795 : ValidPanel panel795 := ⟨check795,ContactValues.valid795⟩
theorem valid796 : ValidPanel panel796 := ⟨check796,ContactValues.valid796⟩
theorem valid797 : ValidPanel panel797 := ⟨check797,ContactValues.valid797⟩
theorem valid798 : ValidPanel panel798 := ⟨check798,ContactValues.valid798⟩
theorem valid799 : ValidPanel panel799 := ⟨check799,ContactValues.valid799⟩
theorem validBlock24 : ∀ p∈block24,ValidPanel p := by
  simp only [block24,List.forall_mem_cons]
  exact ⟨valid768,⟨valid769,⟨valid770,⟨valid771,⟨valid772,⟨valid773,⟨valid774,⟨valid775,⟨valid776,⟨valid777,⟨valid778,⟨valid779,⟨valid780,⟨valid781,⟨valid782,⟨valid783,⟨valid784,⟨valid785,⟨valid786,⟨valid787,⟨valid788,⟨valid789,⟨valid790,⟨valid791,⟨valid792,⟨valid793,⟨valid794,⟨valid795,⟨valid796,⟨valid797,⟨valid798,⟨valid799,(by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end «2610.05164v2».Certificates.Compact.AmplitudeValues

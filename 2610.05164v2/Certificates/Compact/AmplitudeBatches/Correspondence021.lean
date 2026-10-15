import «2610.05164v2».Certificates.Compact.AmplitudeBatches.Batch021
import «2610.05164v2».Certificates.Compact.ContactBatches.Correspondence021
import «2610.05164v2».Certificates.Compact.AmplitudeProof

/-!
Article: 2610.05164v2, Section 4.1.
Correspondence021.
Use: `«2610.05164v2».Certificates.Compact.AmplitudeValues.validBlock21` feeds
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
theorem valid672 : ValidPanel panel672 := ⟨check672,ContactValues.valid672⟩
theorem valid673 : ValidPanel panel673 := ⟨check673,ContactValues.valid673⟩
theorem valid674 : ValidPanel panel674 := ⟨check674,ContactValues.valid674⟩
theorem valid675 : ValidPanel panel675 := ⟨check675,ContactValues.valid675⟩
theorem valid676 : ValidPanel panel676 := ⟨check676,ContactValues.valid676⟩
theorem valid677 : ValidPanel panel677 := ⟨check677,ContactValues.valid677⟩
theorem valid678 : ValidPanel panel678 := ⟨check678,ContactValues.valid678⟩
theorem valid679 : ValidPanel panel679 := ⟨check679,ContactValues.valid679⟩
theorem valid680 : ValidPanel panel680 := ⟨check680,ContactValues.valid680⟩
theorem valid681 : ValidPanel panel681 := ⟨check681,ContactValues.valid681⟩
theorem valid682 : ValidPanel panel682 := ⟨check682,ContactValues.valid682⟩
theorem valid683 : ValidPanel panel683 := ⟨check683,ContactValues.valid683⟩
theorem valid684 : ValidPanel panel684 := ⟨check684,ContactValues.valid684⟩
theorem valid685 : ValidPanel panel685 := ⟨check685,ContactValues.valid685⟩
theorem valid686 : ValidPanel panel686 := ⟨check686,ContactValues.valid686⟩
theorem valid687 : ValidPanel panel687 := ⟨check687,ContactValues.valid687⟩
theorem valid688 : ValidPanel panel688 := ⟨check688,ContactValues.valid688⟩
theorem valid689 : ValidPanel panel689 := ⟨check689,ContactValues.valid689⟩
theorem valid690 : ValidPanel panel690 := ⟨check690,ContactValues.valid690⟩
theorem valid691 : ValidPanel panel691 := ⟨check691,ContactValues.valid691⟩
theorem valid692 : ValidPanel panel692 := ⟨check692,ContactValues.valid692⟩
theorem valid693 : ValidPanel panel693 := ⟨check693,ContactValues.valid693⟩
theorem valid694 : ValidPanel panel694 := ⟨check694,ContactValues.valid694⟩
theorem valid695 : ValidPanel panel695 := ⟨check695,ContactValues.valid695⟩
theorem valid696 : ValidPanel panel696 := ⟨check696,ContactValues.valid696⟩
theorem valid697 : ValidPanel panel697 := ⟨check697,ContactValues.valid697⟩
theorem valid698 : ValidPanel panel698 := ⟨check698,ContactValues.valid698⟩
theorem valid699 : ValidPanel panel699 := ⟨check699,ContactValues.valid699⟩
theorem valid700 : ValidPanel panel700 := ⟨check700,ContactValues.valid700⟩
theorem valid701 : ValidPanel panel701 := ⟨check701,ContactValues.valid701⟩
theorem valid702 : ValidPanel panel702 := ⟨check702,ContactValues.valid702⟩
theorem valid703 : ValidPanel panel703 := ⟨check703,ContactValues.valid703⟩
theorem validBlock21 : ∀ p∈block21,ValidPanel p := by
  simp only [block21,List.forall_mem_cons]
  exact ⟨valid672,⟨valid673,⟨valid674,⟨valid675,⟨valid676,⟨valid677,⟨valid678,⟨valid679,⟨valid680,⟨valid681,⟨valid682,⟨valid683,⟨valid684,⟨valid685,⟨valid686,⟨valid687,⟨valid688,⟨valid689,⟨valid690,⟨valid691,⟨valid692,⟨valid693,⟨valid694,⟨valid695,⟨valid696,⟨valid697,⟨valid698,⟨valid699,⟨valid700,⟨valid701,⟨valid702,⟨valid703,(by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end «2610.05164v2».Certificates.Compact.AmplitudeValues

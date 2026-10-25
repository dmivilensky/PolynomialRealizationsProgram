import chebyshev2.Certificates.Compact.ContactBatches.Batch021
import chebyshev2.Certificates.Compact.ContactCoverage
import chebyshev2.Certificates.Compact.ReferenceTrajectoryIndex

/-!
Article: chebyshev2, Section 4.1.
Correspondence021.
Use: `chebyshev2.Certificates.Compact.ContactValues.validBlock21` feeds
`chebyshev2.Certificates.Compact.ContactValues.all_valid` (all valid).
Proof chain: `chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement` —
chebyshev2, Theorem 1.2, factor 1.000013; Unconditional uniform gain comparison with the retained
numerical factor.
-/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 0
set_option maxRecDepth 200000
namespace chebyshev2.Certificates.Compact.ContactValues
theorem valid672 : ValidPanel panel672 := ⟨modelCheck672,residualCheck672,
  ReferenceTrajectory.leftBlock39_subset (List.mem_of_getElem? (show ReferenceResiduals.block39[0]?=some panel672.left from rfl)),
  ReferenceTrajectory.rightBlock115_subset (List.mem_of_getElem? (show ReferenceResiduals.block115[6]?=some panel672.right from rfl))⟩
theorem valid673 : ValidPanel panel673 := ⟨modelCheck673,residualCheck673,
  ReferenceTrajectory.leftBlock39_subset (List.mem_of_getElem? (show ReferenceResiduals.block39[1]?=some panel673.left from rfl)),
  ReferenceTrajectory.rightBlock115_subset (List.mem_of_getElem? (show ReferenceResiduals.block115[5]?=some panel673.right from rfl))⟩
theorem valid674 : ValidPanel panel674 := ⟨modelCheck674,residualCheck674,
  ReferenceTrajectory.leftBlock39_subset (List.mem_of_getElem? (show ReferenceResiduals.block39[2]?=some panel674.left from rfl)),
  ReferenceTrajectory.rightBlock115_subset (List.mem_of_getElem? (show ReferenceResiduals.block115[4]?=some panel674.right from rfl))⟩
theorem valid675 : ValidPanel panel675 := ⟨modelCheck675,residualCheck675,
  ReferenceTrajectory.leftBlock39_subset (List.mem_of_getElem? (show ReferenceResiduals.block39[3]?=some panel675.left from rfl)),
  ReferenceTrajectory.rightBlock115_subset (List.mem_of_getElem? (show ReferenceResiduals.block115[3]?=some panel675.right from rfl))⟩
theorem valid676 : ValidPanel panel676 := ⟨modelCheck676,residualCheck676,
  ReferenceTrajectory.leftBlock39_subset (List.mem_of_getElem? (show ReferenceResiduals.block39[4]?=some panel676.left from rfl)),
  ReferenceTrajectory.rightBlock115_subset (List.mem_of_getElem? (show ReferenceResiduals.block115[2]?=some panel676.right from rfl))⟩
theorem valid677 : ValidPanel panel677 := ⟨modelCheck677,residualCheck677,
  ReferenceTrajectory.leftBlock39_subset (List.mem_of_getElem? (show ReferenceResiduals.block39[5]?=some panel677.left from rfl)),
  ReferenceTrajectory.rightBlock115_subset (List.mem_of_getElem? (show ReferenceResiduals.block115[1]?=some panel677.right from rfl))⟩
theorem valid678 : ValidPanel panel678 := ⟨modelCheck678,residualCheck678,
  ReferenceTrajectory.leftBlock39_subset (List.mem_of_getElem? (show ReferenceResiduals.block39[6]?=some panel678.left from rfl)),
  ReferenceTrajectory.rightBlock115_subset (List.mem_of_getElem? (show ReferenceResiduals.block115[0]?=some panel678.right from rfl))⟩
theorem valid679 : ValidPanel panel679 := ⟨modelCheck679,residualCheck679,
  ReferenceTrajectory.leftBlock39_subset (List.mem_of_getElem? (show ReferenceResiduals.block39[7]?=some panel679.left from rfl)),
  ReferenceTrajectory.rightBlock114_subset (List.mem_of_getElem? (show ReferenceResiduals.block114[15]?=some panel679.right from rfl))⟩
theorem valid680 : ValidPanel panel680 := ⟨modelCheck680,residualCheck680,
  ReferenceTrajectory.leftBlock39_subset (List.mem_of_getElem? (show ReferenceResiduals.block39[8]?=some panel680.left from rfl)),
  ReferenceTrajectory.rightBlock114_subset (List.mem_of_getElem? (show ReferenceResiduals.block114[14]?=some panel680.right from rfl))⟩
theorem valid681 : ValidPanel panel681 := ⟨modelCheck681,residualCheck681,
  ReferenceTrajectory.leftBlock39_subset (List.mem_of_getElem? (show ReferenceResiduals.block39[9]?=some panel681.left from rfl)),
  ReferenceTrajectory.rightBlock114_subset (List.mem_of_getElem? (show ReferenceResiduals.block114[13]?=some panel681.right from rfl))⟩
theorem valid682 : ValidPanel panel682 := ⟨modelCheck682,residualCheck682,
  ReferenceTrajectory.leftBlock39_subset (List.mem_of_getElem? (show ReferenceResiduals.block39[10]?=some panel682.left from rfl)),
  ReferenceTrajectory.rightBlock114_subset (List.mem_of_getElem? (show ReferenceResiduals.block114[12]?=some panel682.right from rfl))⟩
theorem valid683 : ValidPanel panel683 := ⟨modelCheck683,residualCheck683,
  ReferenceTrajectory.leftBlock39_subset (List.mem_of_getElem? (show ReferenceResiduals.block39[11]?=some panel683.left from rfl)),
  ReferenceTrajectory.rightBlock114_subset (List.mem_of_getElem? (show ReferenceResiduals.block114[11]?=some panel683.right from rfl))⟩
theorem valid684 : ValidPanel panel684 := ⟨modelCheck684,residualCheck684,
  ReferenceTrajectory.leftBlock39_subset (List.mem_of_getElem? (show ReferenceResiduals.block39[12]?=some panel684.left from rfl)),
  ReferenceTrajectory.rightBlock114_subset (List.mem_of_getElem? (show ReferenceResiduals.block114[10]?=some panel684.right from rfl))⟩
theorem valid685 : ValidPanel panel685 := ⟨modelCheck685,residualCheck685,
  ReferenceTrajectory.leftBlock39_subset (List.mem_of_getElem? (show ReferenceResiduals.block39[13]?=some panel685.left from rfl)),
  ReferenceTrajectory.rightBlock114_subset (List.mem_of_getElem? (show ReferenceResiduals.block114[9]?=some panel685.right from rfl))⟩
theorem valid686 : ValidPanel panel686 := ⟨modelCheck686,residualCheck686,
  ReferenceTrajectory.leftBlock39_subset (List.mem_of_getElem? (show ReferenceResiduals.block39[14]?=some panel686.left from rfl)),
  ReferenceTrajectory.rightBlock114_subset (List.mem_of_getElem? (show ReferenceResiduals.block114[8]?=some panel686.right from rfl))⟩
theorem valid687 : ValidPanel panel687 := ⟨modelCheck687,residualCheck687,
  ReferenceTrajectory.leftBlock39_subset (List.mem_of_getElem? (show ReferenceResiduals.block39[15]?=some panel687.left from rfl)),
  ReferenceTrajectory.rightBlock114_subset (List.mem_of_getElem? (show ReferenceResiduals.block114[7]?=some panel687.right from rfl))⟩
theorem valid688 : ValidPanel panel688 := ⟨modelCheck688,residualCheck688,
  ReferenceTrajectory.leftBlock40_subset (List.mem_of_getElem? (show ReferenceResiduals.block40[0]?=some panel688.left from rfl)),
  ReferenceTrajectory.rightBlock114_subset (List.mem_of_getElem? (show ReferenceResiduals.block114[6]?=some panel688.right from rfl))⟩
theorem valid689 : ValidPanel panel689 := ⟨modelCheck689,residualCheck689,
  ReferenceTrajectory.leftBlock40_subset (List.mem_of_getElem? (show ReferenceResiduals.block40[1]?=some panel689.left from rfl)),
  ReferenceTrajectory.rightBlock114_subset (List.mem_of_getElem? (show ReferenceResiduals.block114[5]?=some panel689.right from rfl))⟩
theorem valid690 : ValidPanel panel690 := ⟨modelCheck690,residualCheck690,
  ReferenceTrajectory.leftBlock40_subset (List.mem_of_getElem? (show ReferenceResiduals.block40[2]?=some panel690.left from rfl)),
  ReferenceTrajectory.rightBlock114_subset (List.mem_of_getElem? (show ReferenceResiduals.block114[4]?=some panel690.right from rfl))⟩
theorem valid691 : ValidPanel panel691 := ⟨modelCheck691,residualCheck691,
  ReferenceTrajectory.leftBlock40_subset (List.mem_of_getElem? (show ReferenceResiduals.block40[3]?=some panel691.left from rfl)),
  ReferenceTrajectory.rightBlock114_subset (List.mem_of_getElem? (show ReferenceResiduals.block114[3]?=some panel691.right from rfl))⟩
theorem valid692 : ValidPanel panel692 := ⟨modelCheck692,residualCheck692,
  ReferenceTrajectory.leftBlock40_subset (List.mem_of_getElem? (show ReferenceResiduals.block40[4]?=some panel692.left from rfl)),
  ReferenceTrajectory.rightBlock114_subset (List.mem_of_getElem? (show ReferenceResiduals.block114[2]?=some panel692.right from rfl))⟩
theorem valid693 : ValidPanel panel693 := ⟨modelCheck693,residualCheck693,
  ReferenceTrajectory.leftBlock40_subset (List.mem_of_getElem? (show ReferenceResiduals.block40[5]?=some panel693.left from rfl)),
  ReferenceTrajectory.rightBlock114_subset (List.mem_of_getElem? (show ReferenceResiduals.block114[1]?=some panel693.right from rfl))⟩
theorem valid694 : ValidPanel panel694 := ⟨modelCheck694,residualCheck694,
  ReferenceTrajectory.leftBlock40_subset (List.mem_of_getElem? (show ReferenceResiduals.block40[6]?=some panel694.left from rfl)),
  ReferenceTrajectory.rightBlock114_subset (List.mem_of_getElem? (show ReferenceResiduals.block114[0]?=some panel694.right from rfl))⟩
theorem valid695 : ValidPanel panel695 := ⟨modelCheck695,residualCheck695,
  ReferenceTrajectory.leftBlock40_subset (List.mem_of_getElem? (show ReferenceResiduals.block40[7]?=some panel695.left from rfl)),
  ReferenceTrajectory.rightBlock113_subset (List.mem_of_getElem? (show ReferenceResiduals.block113[15]?=some panel695.right from rfl))⟩
theorem valid696 : ValidPanel panel696 := ⟨modelCheck696,residualCheck696,
  ReferenceTrajectory.leftBlock40_subset (List.mem_of_getElem? (show ReferenceResiduals.block40[8]?=some panel696.left from rfl)),
  ReferenceTrajectory.rightBlock113_subset (List.mem_of_getElem? (show ReferenceResiduals.block113[14]?=some panel696.right from rfl))⟩
theorem valid697 : ValidPanel panel697 := ⟨modelCheck697,residualCheck697,
  ReferenceTrajectory.leftBlock40_subset (List.mem_of_getElem? (show ReferenceResiduals.block40[9]?=some panel697.left from rfl)),
  ReferenceTrajectory.rightBlock113_subset (List.mem_of_getElem? (show ReferenceResiduals.block113[13]?=some panel697.right from rfl))⟩
theorem valid698 : ValidPanel panel698 := ⟨modelCheck698,residualCheck698,
  ReferenceTrajectory.leftBlock40_subset (List.mem_of_getElem? (show ReferenceResiduals.block40[10]?=some panel698.left from rfl)),
  ReferenceTrajectory.rightBlock113_subset (List.mem_of_getElem? (show ReferenceResiduals.block113[12]?=some panel698.right from rfl))⟩
theorem valid699 : ValidPanel panel699 := ⟨modelCheck699,residualCheck699,
  ReferenceTrajectory.leftBlock40_subset (List.mem_of_getElem? (show ReferenceResiduals.block40[11]?=some panel699.left from rfl)),
  ReferenceTrajectory.rightBlock113_subset (List.mem_of_getElem? (show ReferenceResiduals.block113[11]?=some panel699.right from rfl))⟩
theorem valid700 : ValidPanel panel700 := ⟨modelCheck700,residualCheck700,
  ReferenceTrajectory.leftBlock40_subset (List.mem_of_getElem? (show ReferenceResiduals.block40[12]?=some panel700.left from rfl)),
  ReferenceTrajectory.rightBlock113_subset (List.mem_of_getElem? (show ReferenceResiduals.block113[10]?=some panel700.right from rfl))⟩
theorem valid701 : ValidPanel panel701 := ⟨modelCheck701,residualCheck701,
  ReferenceTrajectory.leftBlock40_subset (List.mem_of_getElem? (show ReferenceResiduals.block40[13]?=some panel701.left from rfl)),
  ReferenceTrajectory.rightBlock113_subset (List.mem_of_getElem? (show ReferenceResiduals.block113[9]?=some panel701.right from rfl))⟩
theorem valid702 : ValidPanel panel702 := ⟨modelCheck702,residualCheck702,
  ReferenceTrajectory.leftBlock40_subset (List.mem_of_getElem? (show ReferenceResiduals.block40[14]?=some panel702.left from rfl)),
  ReferenceTrajectory.rightBlock113_subset (List.mem_of_getElem? (show ReferenceResiduals.block113[8]?=some panel702.right from rfl))⟩
theorem valid703 : ValidPanel panel703 := ⟨modelCheck703,residualCheck703,
  ReferenceTrajectory.leftBlock40_subset (List.mem_of_getElem? (show ReferenceResiduals.block40[15]?=some panel703.left from rfl)),
  ReferenceTrajectory.rightBlock113_subset (List.mem_of_getElem? (show ReferenceResiduals.block113[7]?=some panel703.right from rfl))⟩
theorem validBlock21 : ∀ p∈block21,ValidPanel p := by
  simp only [block21,List.forall_mem_cons]
  exact ⟨valid672,⟨valid673,⟨valid674,⟨valid675,⟨valid676,⟨valid677,⟨valid678,⟨valid679,⟨valid680,⟨valid681,⟨valid682,⟨valid683,⟨valid684,⟨valid685,⟨valid686,⟨valid687,⟨valid688,⟨valid689,⟨valid690,⟨valid691,⟨valid692,⟨valid693,⟨valid694,⟨valid695,⟨valid696,⟨valid697,⟨valid698,⟨valid699,⟨valid700,⟨valid701,⟨valid702,⟨valid703,(by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end chebyshev2.Certificates.Compact.ContactValues

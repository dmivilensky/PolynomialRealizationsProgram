import chebyshev2.Certificates.Compact.ContactBatches.Batch024
import chebyshev2.Certificates.Compact.ContactCoverage
import chebyshev2.Certificates.Compact.ReferenceTrajectoryIndex

/-!
Article: chebyshev2, Section 4.1.
Correspondence024.
Use: `chebyshev2.Certificates.Compact.ContactValues.validBlock24` feeds
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
theorem valid768 : ValidPanel panel768 := ⟨modelCheck768,residualCheck768,
  ReferenceTrajectory.leftBlock45_subset (List.mem_of_getElem? (show ReferenceResiduals.block45[0]?=some panel768.left from rfl)),
  ReferenceTrajectory.rightBlock109_subset (List.mem_of_getElem? (show ReferenceResiduals.block109[6]?=some panel768.right from rfl))⟩
theorem valid769 : ValidPanel panel769 := ⟨modelCheck769,residualCheck769,
  ReferenceTrajectory.leftBlock45_subset (List.mem_of_getElem? (show ReferenceResiduals.block45[1]?=some panel769.left from rfl)),
  ReferenceTrajectory.rightBlock109_subset (List.mem_of_getElem? (show ReferenceResiduals.block109[5]?=some panel769.right from rfl))⟩
theorem valid770 : ValidPanel panel770 := ⟨modelCheck770,residualCheck770,
  ReferenceTrajectory.leftBlock45_subset (List.mem_of_getElem? (show ReferenceResiduals.block45[2]?=some panel770.left from rfl)),
  ReferenceTrajectory.rightBlock109_subset (List.mem_of_getElem? (show ReferenceResiduals.block109[4]?=some panel770.right from rfl))⟩
theorem valid771 : ValidPanel panel771 := ⟨modelCheck771,residualCheck771,
  ReferenceTrajectory.leftBlock45_subset (List.mem_of_getElem? (show ReferenceResiduals.block45[3]?=some panel771.left from rfl)),
  ReferenceTrajectory.rightBlock109_subset (List.mem_of_getElem? (show ReferenceResiduals.block109[3]?=some panel771.right from rfl))⟩
theorem valid772 : ValidPanel panel772 := ⟨modelCheck772,residualCheck772,
  ReferenceTrajectory.leftBlock45_subset (List.mem_of_getElem? (show ReferenceResiduals.block45[4]?=some panel772.left from rfl)),
  ReferenceTrajectory.rightBlock109_subset (List.mem_of_getElem? (show ReferenceResiduals.block109[2]?=some panel772.right from rfl))⟩
theorem valid773 : ValidPanel panel773 := ⟨modelCheck773,residualCheck773,
  ReferenceTrajectory.leftBlock45_subset (List.mem_of_getElem? (show ReferenceResiduals.block45[5]?=some panel773.left from rfl)),
  ReferenceTrajectory.rightBlock109_subset (List.mem_of_getElem? (show ReferenceResiduals.block109[1]?=some panel773.right from rfl))⟩
theorem valid774 : ValidPanel panel774 := ⟨modelCheck774,residualCheck774,
  ReferenceTrajectory.leftBlock45_subset (List.mem_of_getElem? (show ReferenceResiduals.block45[6]?=some panel774.left from rfl)),
  ReferenceTrajectory.rightBlock109_subset (List.mem_of_getElem? (show ReferenceResiduals.block109[0]?=some panel774.right from rfl))⟩
theorem valid775 : ValidPanel panel775 := ⟨modelCheck775,residualCheck775,
  ReferenceTrajectory.leftBlock45_subset (List.mem_of_getElem? (show ReferenceResiduals.block45[7]?=some panel775.left from rfl)),
  ReferenceTrajectory.rightBlock108_subset (List.mem_of_getElem? (show ReferenceResiduals.block108[15]?=some panel775.right from rfl))⟩
theorem valid776 : ValidPanel panel776 := ⟨modelCheck776,residualCheck776,
  ReferenceTrajectory.leftBlock45_subset (List.mem_of_getElem? (show ReferenceResiduals.block45[8]?=some panel776.left from rfl)),
  ReferenceTrajectory.rightBlock108_subset (List.mem_of_getElem? (show ReferenceResiduals.block108[14]?=some panel776.right from rfl))⟩
theorem valid777 : ValidPanel panel777 := ⟨modelCheck777,residualCheck777,
  ReferenceTrajectory.leftBlock45_subset (List.mem_of_getElem? (show ReferenceResiduals.block45[9]?=some panel777.left from rfl)),
  ReferenceTrajectory.rightBlock108_subset (List.mem_of_getElem? (show ReferenceResiduals.block108[13]?=some panel777.right from rfl))⟩
theorem valid778 : ValidPanel panel778 := ⟨modelCheck778,residualCheck778,
  ReferenceTrajectory.leftBlock45_subset (List.mem_of_getElem? (show ReferenceResiduals.block45[10]?=some panel778.left from rfl)),
  ReferenceTrajectory.rightBlock108_subset (List.mem_of_getElem? (show ReferenceResiduals.block108[12]?=some panel778.right from rfl))⟩
theorem valid779 : ValidPanel panel779 := ⟨modelCheck779,residualCheck779,
  ReferenceTrajectory.leftBlock45_subset (List.mem_of_getElem? (show ReferenceResiduals.block45[11]?=some panel779.left from rfl)),
  ReferenceTrajectory.rightBlock108_subset (List.mem_of_getElem? (show ReferenceResiduals.block108[11]?=some panel779.right from rfl))⟩
theorem valid780 : ValidPanel panel780 := ⟨modelCheck780,residualCheck780,
  ReferenceTrajectory.leftBlock45_subset (List.mem_of_getElem? (show ReferenceResiduals.block45[12]?=some panel780.left from rfl)),
  ReferenceTrajectory.rightBlock108_subset (List.mem_of_getElem? (show ReferenceResiduals.block108[10]?=some panel780.right from rfl))⟩
theorem valid781 : ValidPanel panel781 := ⟨modelCheck781,residualCheck781,
  ReferenceTrajectory.leftBlock45_subset (List.mem_of_getElem? (show ReferenceResiduals.block45[13]?=some panel781.left from rfl)),
  ReferenceTrajectory.rightBlock108_subset (List.mem_of_getElem? (show ReferenceResiduals.block108[9]?=some panel781.right from rfl))⟩
theorem valid782 : ValidPanel panel782 := ⟨modelCheck782,residualCheck782,
  ReferenceTrajectory.leftBlock45_subset (List.mem_of_getElem? (show ReferenceResiduals.block45[14]?=some panel782.left from rfl)),
  ReferenceTrajectory.rightBlock108_subset (List.mem_of_getElem? (show ReferenceResiduals.block108[8]?=some panel782.right from rfl))⟩
theorem valid783 : ValidPanel panel783 := ⟨modelCheck783,residualCheck783,
  ReferenceTrajectory.leftBlock45_subset (List.mem_of_getElem? (show ReferenceResiduals.block45[15]?=some panel783.left from rfl)),
  ReferenceTrajectory.rightBlock108_subset (List.mem_of_getElem? (show ReferenceResiduals.block108[7]?=some panel783.right from rfl))⟩
theorem valid784 : ValidPanel panel784 := ⟨modelCheck784,residualCheck784,
  ReferenceTrajectory.leftBlock46_subset (List.mem_of_getElem? (show ReferenceResiduals.block46[0]?=some panel784.left from rfl)),
  ReferenceTrajectory.rightBlock108_subset (List.mem_of_getElem? (show ReferenceResiduals.block108[6]?=some panel784.right from rfl))⟩
theorem valid785 : ValidPanel panel785 := ⟨modelCheck785,residualCheck785,
  ReferenceTrajectory.leftBlock46_subset (List.mem_of_getElem? (show ReferenceResiduals.block46[1]?=some panel785.left from rfl)),
  ReferenceTrajectory.rightBlock108_subset (List.mem_of_getElem? (show ReferenceResiduals.block108[5]?=some panel785.right from rfl))⟩
theorem valid786 : ValidPanel panel786 := ⟨modelCheck786,residualCheck786,
  ReferenceTrajectory.leftBlock46_subset (List.mem_of_getElem? (show ReferenceResiduals.block46[2]?=some panel786.left from rfl)),
  ReferenceTrajectory.rightBlock108_subset (List.mem_of_getElem? (show ReferenceResiduals.block108[4]?=some panel786.right from rfl))⟩
theorem valid787 : ValidPanel panel787 := ⟨modelCheck787,residualCheck787,
  ReferenceTrajectory.leftBlock46_subset (List.mem_of_getElem? (show ReferenceResiduals.block46[3]?=some panel787.left from rfl)),
  ReferenceTrajectory.rightBlock108_subset (List.mem_of_getElem? (show ReferenceResiduals.block108[3]?=some panel787.right from rfl))⟩
theorem valid788 : ValidPanel panel788 := ⟨modelCheck788,residualCheck788,
  ReferenceTrajectory.leftBlock46_subset (List.mem_of_getElem? (show ReferenceResiduals.block46[4]?=some panel788.left from rfl)),
  ReferenceTrajectory.rightBlock108_subset (List.mem_of_getElem? (show ReferenceResiduals.block108[2]?=some panel788.right from rfl))⟩
theorem valid789 : ValidPanel panel789 := ⟨modelCheck789,residualCheck789,
  ReferenceTrajectory.leftBlock46_subset (List.mem_of_getElem? (show ReferenceResiduals.block46[5]?=some panel789.left from rfl)),
  ReferenceTrajectory.rightBlock108_subset (List.mem_of_getElem? (show ReferenceResiduals.block108[1]?=some panel789.right from rfl))⟩
theorem valid790 : ValidPanel panel790 := ⟨modelCheck790,residualCheck790,
  ReferenceTrajectory.leftBlock46_subset (List.mem_of_getElem? (show ReferenceResiduals.block46[6]?=some panel790.left from rfl)),
  ReferenceTrajectory.rightBlock108_subset (List.mem_of_getElem? (show ReferenceResiduals.block108[0]?=some panel790.right from rfl))⟩
theorem valid791 : ValidPanel panel791 := ⟨modelCheck791,residualCheck791,
  ReferenceTrajectory.leftBlock46_subset (List.mem_of_getElem? (show ReferenceResiduals.block46[7]?=some panel791.left from rfl)),
  ReferenceTrajectory.rightBlock107_subset (List.mem_of_getElem? (show ReferenceResiduals.block107[15]?=some panel791.right from rfl))⟩
theorem valid792 : ValidPanel panel792 := ⟨modelCheck792,residualCheck792,
  ReferenceTrajectory.leftBlock46_subset (List.mem_of_getElem? (show ReferenceResiduals.block46[8]?=some panel792.left from rfl)),
  ReferenceTrajectory.rightBlock107_subset (List.mem_of_getElem? (show ReferenceResiduals.block107[14]?=some panel792.right from rfl))⟩
theorem valid793 : ValidPanel panel793 := ⟨modelCheck793,residualCheck793,
  ReferenceTrajectory.leftBlock46_subset (List.mem_of_getElem? (show ReferenceResiduals.block46[9]?=some panel793.left from rfl)),
  ReferenceTrajectory.rightBlock107_subset (List.mem_of_getElem? (show ReferenceResiduals.block107[13]?=some panel793.right from rfl))⟩
theorem valid794 : ValidPanel panel794 := ⟨modelCheck794,residualCheck794,
  ReferenceTrajectory.leftBlock46_subset (List.mem_of_getElem? (show ReferenceResiduals.block46[10]?=some panel794.left from rfl)),
  ReferenceTrajectory.rightBlock107_subset (List.mem_of_getElem? (show ReferenceResiduals.block107[12]?=some panel794.right from rfl))⟩
theorem valid795 : ValidPanel panel795 := ⟨modelCheck795,residualCheck795,
  ReferenceTrajectory.leftBlock46_subset (List.mem_of_getElem? (show ReferenceResiduals.block46[11]?=some panel795.left from rfl)),
  ReferenceTrajectory.rightBlock107_subset (List.mem_of_getElem? (show ReferenceResiduals.block107[11]?=some panel795.right from rfl))⟩
theorem valid796 : ValidPanel panel796 := ⟨modelCheck796,residualCheck796,
  ReferenceTrajectory.leftBlock46_subset (List.mem_of_getElem? (show ReferenceResiduals.block46[12]?=some panel796.left from rfl)),
  ReferenceTrajectory.rightBlock107_subset (List.mem_of_getElem? (show ReferenceResiduals.block107[10]?=some panel796.right from rfl))⟩
theorem valid797 : ValidPanel panel797 := ⟨modelCheck797,residualCheck797,
  ReferenceTrajectory.leftBlock46_subset (List.mem_of_getElem? (show ReferenceResiduals.block46[13]?=some panel797.left from rfl)),
  ReferenceTrajectory.rightBlock107_subset (List.mem_of_getElem? (show ReferenceResiduals.block107[9]?=some panel797.right from rfl))⟩
theorem valid798 : ValidPanel panel798 := ⟨modelCheck798,residualCheck798,
  ReferenceTrajectory.leftBlock46_subset (List.mem_of_getElem? (show ReferenceResiduals.block46[14]?=some panel798.left from rfl)),
  ReferenceTrajectory.rightBlock107_subset (List.mem_of_getElem? (show ReferenceResiduals.block107[8]?=some panel798.right from rfl))⟩
theorem valid799 : ValidPanel panel799 := ⟨modelCheck799,residualCheck799,
  ReferenceTrajectory.leftBlock46_subset (List.mem_of_getElem? (show ReferenceResiduals.block46[15]?=some panel799.left from rfl)),
  ReferenceTrajectory.rightBlock107_subset (List.mem_of_getElem? (show ReferenceResiduals.block107[7]?=some panel799.right from rfl))⟩
theorem validBlock24 : ∀ p∈block24,ValidPanel p := by
  simp only [block24,List.forall_mem_cons]
  exact ⟨valid768,⟨valid769,⟨valid770,⟨valid771,⟨valid772,⟨valid773,⟨valid774,⟨valid775,⟨valid776,⟨valid777,⟨valid778,⟨valid779,⟨valid780,⟨valid781,⟨valid782,⟨valid783,⟨valid784,⟨valid785,⟨valid786,⟨valid787,⟨valid788,⟨valid789,⟨valid790,⟨valid791,⟨valid792,⟨valid793,⟨valid794,⟨valid795,⟨valid796,⟨valid797,⟨valid798,⟨valid799,(by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end chebyshev2.Certificates.Compact.ContactValues

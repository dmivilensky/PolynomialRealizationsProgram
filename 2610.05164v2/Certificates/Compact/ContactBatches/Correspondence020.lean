import «2610.05164v2».Certificates.Compact.ContactBatches.Batch020
import «2610.05164v2».Certificates.Compact.ContactCoverage
import «2610.05164v2».Certificates.Compact.ReferenceTrajectoryIndex

/-!
Article: 2610.05164v2, Section 4.1.
Correspondence020.
Use: `«2610.05164v2».Certificates.Compact.ContactValues.validBlock20` feeds
`«2610.05164v2».Certificates.Compact.ContactValues.all_valid` (all valid).
Proof chain: `«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement` —
2610.05164v2, Theorem 1.2, factor 1.000013; Unconditional uniform gain comparison with the retained
numerical factor.
-/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 0
set_option maxRecDepth 200000
namespace «2610.05164v2».Certificates.Compact.ContactValues
theorem valid640 : ValidPanel panel640 := ⟨modelCheck640,residualCheck640,
  ReferenceTrajectory.leftBlock37_subset (List.mem_of_getElem? (show ReferenceResiduals.block37[0]?=some panel640.left from rfl)),
  ReferenceTrajectory.rightBlock117_subset (List.mem_of_getElem? (show ReferenceResiduals.block117[6]?=some panel640.right from rfl))⟩
theorem valid641 : ValidPanel panel641 := ⟨modelCheck641,residualCheck641,
  ReferenceTrajectory.leftBlock37_subset (List.mem_of_getElem? (show ReferenceResiduals.block37[1]?=some panel641.left from rfl)),
  ReferenceTrajectory.rightBlock117_subset (List.mem_of_getElem? (show ReferenceResiduals.block117[5]?=some panel641.right from rfl))⟩
theorem valid642 : ValidPanel panel642 := ⟨modelCheck642,residualCheck642,
  ReferenceTrajectory.leftBlock37_subset (List.mem_of_getElem? (show ReferenceResiduals.block37[2]?=some panel642.left from rfl)),
  ReferenceTrajectory.rightBlock117_subset (List.mem_of_getElem? (show ReferenceResiduals.block117[4]?=some panel642.right from rfl))⟩
theorem valid643 : ValidPanel panel643 := ⟨modelCheck643,residualCheck643,
  ReferenceTrajectory.leftBlock37_subset (List.mem_of_getElem? (show ReferenceResiduals.block37[3]?=some panel643.left from rfl)),
  ReferenceTrajectory.rightBlock117_subset (List.mem_of_getElem? (show ReferenceResiduals.block117[3]?=some panel643.right from rfl))⟩
theorem valid644 : ValidPanel panel644 := ⟨modelCheck644,residualCheck644,
  ReferenceTrajectory.leftBlock37_subset (List.mem_of_getElem? (show ReferenceResiduals.block37[4]?=some panel644.left from rfl)),
  ReferenceTrajectory.rightBlock117_subset (List.mem_of_getElem? (show ReferenceResiduals.block117[2]?=some panel644.right from rfl))⟩
theorem valid645 : ValidPanel panel645 := ⟨modelCheck645,residualCheck645,
  ReferenceTrajectory.leftBlock37_subset (List.mem_of_getElem? (show ReferenceResiduals.block37[5]?=some panel645.left from rfl)),
  ReferenceTrajectory.rightBlock117_subset (List.mem_of_getElem? (show ReferenceResiduals.block117[1]?=some panel645.right from rfl))⟩
theorem valid646 : ValidPanel panel646 := ⟨modelCheck646,residualCheck646,
  ReferenceTrajectory.leftBlock37_subset (List.mem_of_getElem? (show ReferenceResiduals.block37[6]?=some panel646.left from rfl)),
  ReferenceTrajectory.rightBlock117_subset (List.mem_of_getElem? (show ReferenceResiduals.block117[0]?=some panel646.right from rfl))⟩
theorem valid647 : ValidPanel panel647 := ⟨modelCheck647,residualCheck647,
  ReferenceTrajectory.leftBlock37_subset (List.mem_of_getElem? (show ReferenceResiduals.block37[7]?=some panel647.left from rfl)),
  ReferenceTrajectory.rightBlock116_subset (List.mem_of_getElem? (show ReferenceResiduals.block116[15]?=some panel647.right from rfl))⟩
theorem valid648 : ValidPanel panel648 := ⟨modelCheck648,residualCheck648,
  ReferenceTrajectory.leftBlock37_subset (List.mem_of_getElem? (show ReferenceResiduals.block37[8]?=some panel648.left from rfl)),
  ReferenceTrajectory.rightBlock116_subset (List.mem_of_getElem? (show ReferenceResiduals.block116[14]?=some panel648.right from rfl))⟩
theorem valid649 : ValidPanel panel649 := ⟨modelCheck649,residualCheck649,
  ReferenceTrajectory.leftBlock37_subset (List.mem_of_getElem? (show ReferenceResiduals.block37[9]?=some panel649.left from rfl)),
  ReferenceTrajectory.rightBlock116_subset (List.mem_of_getElem? (show ReferenceResiduals.block116[13]?=some panel649.right from rfl))⟩
theorem valid650 : ValidPanel panel650 := ⟨modelCheck650,residualCheck650,
  ReferenceTrajectory.leftBlock37_subset (List.mem_of_getElem? (show ReferenceResiduals.block37[10]?=some panel650.left from rfl)),
  ReferenceTrajectory.rightBlock116_subset (List.mem_of_getElem? (show ReferenceResiduals.block116[12]?=some panel650.right from rfl))⟩
theorem valid651 : ValidPanel panel651 := ⟨modelCheck651,residualCheck651,
  ReferenceTrajectory.leftBlock37_subset (List.mem_of_getElem? (show ReferenceResiduals.block37[11]?=some panel651.left from rfl)),
  ReferenceTrajectory.rightBlock116_subset (List.mem_of_getElem? (show ReferenceResiduals.block116[11]?=some panel651.right from rfl))⟩
theorem valid652 : ValidPanel panel652 := ⟨modelCheck652,residualCheck652,
  ReferenceTrajectory.leftBlock37_subset (List.mem_of_getElem? (show ReferenceResiduals.block37[12]?=some panel652.left from rfl)),
  ReferenceTrajectory.rightBlock116_subset (List.mem_of_getElem? (show ReferenceResiduals.block116[10]?=some panel652.right from rfl))⟩
theorem valid653 : ValidPanel panel653 := ⟨modelCheck653,residualCheck653,
  ReferenceTrajectory.leftBlock37_subset (List.mem_of_getElem? (show ReferenceResiduals.block37[13]?=some panel653.left from rfl)),
  ReferenceTrajectory.rightBlock116_subset (List.mem_of_getElem? (show ReferenceResiduals.block116[9]?=some panel653.right from rfl))⟩
theorem valid654 : ValidPanel panel654 := ⟨modelCheck654,residualCheck654,
  ReferenceTrajectory.leftBlock37_subset (List.mem_of_getElem? (show ReferenceResiduals.block37[14]?=some panel654.left from rfl)),
  ReferenceTrajectory.rightBlock116_subset (List.mem_of_getElem? (show ReferenceResiduals.block116[8]?=some panel654.right from rfl))⟩
theorem valid655 : ValidPanel panel655 := ⟨modelCheck655,residualCheck655,
  ReferenceTrajectory.leftBlock37_subset (List.mem_of_getElem? (show ReferenceResiduals.block37[15]?=some panel655.left from rfl)),
  ReferenceTrajectory.rightBlock116_subset (List.mem_of_getElem? (show ReferenceResiduals.block116[7]?=some panel655.right from rfl))⟩
theorem valid656 : ValidPanel panel656 := ⟨modelCheck656,residualCheck656,
  ReferenceTrajectory.leftBlock38_subset (List.mem_of_getElem? (show ReferenceResiduals.block38[0]?=some panel656.left from rfl)),
  ReferenceTrajectory.rightBlock116_subset (List.mem_of_getElem? (show ReferenceResiduals.block116[6]?=some panel656.right from rfl))⟩
theorem valid657 : ValidPanel panel657 := ⟨modelCheck657,residualCheck657,
  ReferenceTrajectory.leftBlock38_subset (List.mem_of_getElem? (show ReferenceResiduals.block38[1]?=some panel657.left from rfl)),
  ReferenceTrajectory.rightBlock116_subset (List.mem_of_getElem? (show ReferenceResiduals.block116[5]?=some panel657.right from rfl))⟩
theorem valid658 : ValidPanel panel658 := ⟨modelCheck658,residualCheck658,
  ReferenceTrajectory.leftBlock38_subset (List.mem_of_getElem? (show ReferenceResiduals.block38[2]?=some panel658.left from rfl)),
  ReferenceTrajectory.rightBlock116_subset (List.mem_of_getElem? (show ReferenceResiduals.block116[4]?=some panel658.right from rfl))⟩
theorem valid659 : ValidPanel panel659 := ⟨modelCheck659,residualCheck659,
  ReferenceTrajectory.leftBlock38_subset (List.mem_of_getElem? (show ReferenceResiduals.block38[3]?=some panel659.left from rfl)),
  ReferenceTrajectory.rightBlock116_subset (List.mem_of_getElem? (show ReferenceResiduals.block116[3]?=some panel659.right from rfl))⟩
theorem valid660 : ValidPanel panel660 := ⟨modelCheck660,residualCheck660,
  ReferenceTrajectory.leftBlock38_subset (List.mem_of_getElem? (show ReferenceResiduals.block38[4]?=some panel660.left from rfl)),
  ReferenceTrajectory.rightBlock116_subset (List.mem_of_getElem? (show ReferenceResiduals.block116[2]?=some panel660.right from rfl))⟩
theorem valid661 : ValidPanel panel661 := ⟨modelCheck661,residualCheck661,
  ReferenceTrajectory.leftBlock38_subset (List.mem_of_getElem? (show ReferenceResiduals.block38[5]?=some panel661.left from rfl)),
  ReferenceTrajectory.rightBlock116_subset (List.mem_of_getElem? (show ReferenceResiduals.block116[1]?=some panel661.right from rfl))⟩
theorem valid662 : ValidPanel panel662 := ⟨modelCheck662,residualCheck662,
  ReferenceTrajectory.leftBlock38_subset (List.mem_of_getElem? (show ReferenceResiduals.block38[6]?=some panel662.left from rfl)),
  ReferenceTrajectory.rightBlock116_subset (List.mem_of_getElem? (show ReferenceResiduals.block116[0]?=some panel662.right from rfl))⟩
theorem valid663 : ValidPanel panel663 := ⟨modelCheck663,residualCheck663,
  ReferenceTrajectory.leftBlock38_subset (List.mem_of_getElem? (show ReferenceResiduals.block38[7]?=some panel663.left from rfl)),
  ReferenceTrajectory.rightBlock115_subset (List.mem_of_getElem? (show ReferenceResiduals.block115[15]?=some panel663.right from rfl))⟩
theorem valid664 : ValidPanel panel664 := ⟨modelCheck664,residualCheck664,
  ReferenceTrajectory.leftBlock38_subset (List.mem_of_getElem? (show ReferenceResiduals.block38[8]?=some panel664.left from rfl)),
  ReferenceTrajectory.rightBlock115_subset (List.mem_of_getElem? (show ReferenceResiduals.block115[14]?=some panel664.right from rfl))⟩
theorem valid665 : ValidPanel panel665 := ⟨modelCheck665,residualCheck665,
  ReferenceTrajectory.leftBlock38_subset (List.mem_of_getElem? (show ReferenceResiduals.block38[9]?=some panel665.left from rfl)),
  ReferenceTrajectory.rightBlock115_subset (List.mem_of_getElem? (show ReferenceResiduals.block115[13]?=some panel665.right from rfl))⟩
theorem valid666 : ValidPanel panel666 := ⟨modelCheck666,residualCheck666,
  ReferenceTrajectory.leftBlock38_subset (List.mem_of_getElem? (show ReferenceResiduals.block38[10]?=some panel666.left from rfl)),
  ReferenceTrajectory.rightBlock115_subset (List.mem_of_getElem? (show ReferenceResiduals.block115[12]?=some panel666.right from rfl))⟩
theorem valid667 : ValidPanel panel667 := ⟨modelCheck667,residualCheck667,
  ReferenceTrajectory.leftBlock38_subset (List.mem_of_getElem? (show ReferenceResiduals.block38[11]?=some panel667.left from rfl)),
  ReferenceTrajectory.rightBlock115_subset (List.mem_of_getElem? (show ReferenceResiduals.block115[11]?=some panel667.right from rfl))⟩
theorem valid668 : ValidPanel panel668 := ⟨modelCheck668,residualCheck668,
  ReferenceTrajectory.leftBlock38_subset (List.mem_of_getElem? (show ReferenceResiduals.block38[12]?=some panel668.left from rfl)),
  ReferenceTrajectory.rightBlock115_subset (List.mem_of_getElem? (show ReferenceResiduals.block115[10]?=some panel668.right from rfl))⟩
theorem valid669 : ValidPanel panel669 := ⟨modelCheck669,residualCheck669,
  ReferenceTrajectory.leftBlock38_subset (List.mem_of_getElem? (show ReferenceResiduals.block38[13]?=some panel669.left from rfl)),
  ReferenceTrajectory.rightBlock115_subset (List.mem_of_getElem? (show ReferenceResiduals.block115[9]?=some panel669.right from rfl))⟩
theorem valid670 : ValidPanel panel670 := ⟨modelCheck670,residualCheck670,
  ReferenceTrajectory.leftBlock38_subset (List.mem_of_getElem? (show ReferenceResiduals.block38[14]?=some panel670.left from rfl)),
  ReferenceTrajectory.rightBlock115_subset (List.mem_of_getElem? (show ReferenceResiduals.block115[8]?=some panel670.right from rfl))⟩
theorem valid671 : ValidPanel panel671 := ⟨modelCheck671,residualCheck671,
  ReferenceTrajectory.leftBlock38_subset (List.mem_of_getElem? (show ReferenceResiduals.block38[15]?=some panel671.left from rfl)),
  ReferenceTrajectory.rightBlock115_subset (List.mem_of_getElem? (show ReferenceResiduals.block115[7]?=some panel671.right from rfl))⟩
theorem validBlock20 : ∀ p∈block20,ValidPanel p := by
  simp only [block20,List.forall_mem_cons]
  exact ⟨valid640,⟨valid641,⟨valid642,⟨valid643,⟨valid644,⟨valid645,⟨valid646,⟨valid647,⟨valid648,⟨valid649,⟨valid650,⟨valid651,⟨valid652,⟨valid653,⟨valid654,⟨valid655,⟨valid656,⟨valid657,⟨valid658,⟨valid659,⟨valid660,⟨valid661,⟨valid662,⟨valid663,⟨valid664,⟨valid665,⟨valid666,⟨valid667,⟨valid668,⟨valid669,⟨valid670,⟨valid671,(by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end «2610.05164v2».Certificates.Compact.ContactValues

import chebyshev2.Certificates.Compact.ContactBatches.Batch019
import chebyshev2.Certificates.Compact.ContactCoverage
import chebyshev2.Certificates.Compact.ReferenceTrajectoryIndex

/-!
Article: chebyshev2, Section 4.1.
Correspondence019.
Use: `chebyshev2.Certificates.Compact.ContactValues.validBlock19` feeds
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
theorem valid608 : ValidPanel panel608 := ⟨modelCheck608,residualCheck608,
  ReferenceTrajectory.leftBlock35_subset (List.mem_of_getElem? (show ReferenceResiduals.block35[0]?=some panel608.left from rfl)),
  ReferenceTrajectory.rightBlock119_subset (List.mem_of_getElem? (show ReferenceResiduals.block119[6]?=some panel608.right from rfl))⟩
theorem valid609 : ValidPanel panel609 := ⟨modelCheck609,residualCheck609,
  ReferenceTrajectory.leftBlock35_subset (List.mem_of_getElem? (show ReferenceResiduals.block35[1]?=some panel609.left from rfl)),
  ReferenceTrajectory.rightBlock119_subset (List.mem_of_getElem? (show ReferenceResiduals.block119[5]?=some panel609.right from rfl))⟩
theorem valid610 : ValidPanel panel610 := ⟨modelCheck610,residualCheck610,
  ReferenceTrajectory.leftBlock35_subset (List.mem_of_getElem? (show ReferenceResiduals.block35[2]?=some panel610.left from rfl)),
  ReferenceTrajectory.rightBlock119_subset (List.mem_of_getElem? (show ReferenceResiduals.block119[4]?=some panel610.right from rfl))⟩
theorem valid611 : ValidPanel panel611 := ⟨modelCheck611,residualCheck611,
  ReferenceTrajectory.leftBlock35_subset (List.mem_of_getElem? (show ReferenceResiduals.block35[3]?=some panel611.left from rfl)),
  ReferenceTrajectory.rightBlock119_subset (List.mem_of_getElem? (show ReferenceResiduals.block119[3]?=some panel611.right from rfl))⟩
theorem valid612 : ValidPanel panel612 := ⟨modelCheck612,residualCheck612,
  ReferenceTrajectory.leftBlock35_subset (List.mem_of_getElem? (show ReferenceResiduals.block35[4]?=some panel612.left from rfl)),
  ReferenceTrajectory.rightBlock119_subset (List.mem_of_getElem? (show ReferenceResiduals.block119[2]?=some panel612.right from rfl))⟩
theorem valid613 : ValidPanel panel613 := ⟨modelCheck613,residualCheck613,
  ReferenceTrajectory.leftBlock35_subset (List.mem_of_getElem? (show ReferenceResiduals.block35[5]?=some panel613.left from rfl)),
  ReferenceTrajectory.rightBlock119_subset (List.mem_of_getElem? (show ReferenceResiduals.block119[1]?=some panel613.right from rfl))⟩
theorem valid614 : ValidPanel panel614 := ⟨modelCheck614,residualCheck614,
  ReferenceTrajectory.leftBlock35_subset (List.mem_of_getElem? (show ReferenceResiduals.block35[6]?=some panel614.left from rfl)),
  ReferenceTrajectory.rightBlock119_subset (List.mem_of_getElem? (show ReferenceResiduals.block119[0]?=some panel614.right from rfl))⟩
theorem valid615 : ValidPanel panel615 := ⟨modelCheck615,residualCheck615,
  ReferenceTrajectory.leftBlock35_subset (List.mem_of_getElem? (show ReferenceResiduals.block35[7]?=some panel615.left from rfl)),
  ReferenceTrajectory.rightBlock118_subset (List.mem_of_getElem? (show ReferenceResiduals.block118[15]?=some panel615.right from rfl))⟩
theorem valid616 : ValidPanel panel616 := ⟨modelCheck616,residualCheck616,
  ReferenceTrajectory.leftBlock35_subset (List.mem_of_getElem? (show ReferenceResiduals.block35[8]?=some panel616.left from rfl)),
  ReferenceTrajectory.rightBlock118_subset (List.mem_of_getElem? (show ReferenceResiduals.block118[14]?=some panel616.right from rfl))⟩
theorem valid617 : ValidPanel panel617 := ⟨modelCheck617,residualCheck617,
  ReferenceTrajectory.leftBlock35_subset (List.mem_of_getElem? (show ReferenceResiduals.block35[9]?=some panel617.left from rfl)),
  ReferenceTrajectory.rightBlock118_subset (List.mem_of_getElem? (show ReferenceResiduals.block118[13]?=some panel617.right from rfl))⟩
theorem valid618 : ValidPanel panel618 := ⟨modelCheck618,residualCheck618,
  ReferenceTrajectory.leftBlock35_subset (List.mem_of_getElem? (show ReferenceResiduals.block35[10]?=some panel618.left from rfl)),
  ReferenceTrajectory.rightBlock118_subset (List.mem_of_getElem? (show ReferenceResiduals.block118[12]?=some panel618.right from rfl))⟩
theorem valid619 : ValidPanel panel619 := ⟨modelCheck619,residualCheck619,
  ReferenceTrajectory.leftBlock35_subset (List.mem_of_getElem? (show ReferenceResiduals.block35[11]?=some panel619.left from rfl)),
  ReferenceTrajectory.rightBlock118_subset (List.mem_of_getElem? (show ReferenceResiduals.block118[11]?=some panel619.right from rfl))⟩
theorem valid620 : ValidPanel panel620 := ⟨modelCheck620,residualCheck620,
  ReferenceTrajectory.leftBlock35_subset (List.mem_of_getElem? (show ReferenceResiduals.block35[12]?=some panel620.left from rfl)),
  ReferenceTrajectory.rightBlock118_subset (List.mem_of_getElem? (show ReferenceResiduals.block118[10]?=some panel620.right from rfl))⟩
theorem valid621 : ValidPanel panel621 := ⟨modelCheck621,residualCheck621,
  ReferenceTrajectory.leftBlock35_subset (List.mem_of_getElem? (show ReferenceResiduals.block35[13]?=some panel621.left from rfl)),
  ReferenceTrajectory.rightBlock118_subset (List.mem_of_getElem? (show ReferenceResiduals.block118[9]?=some panel621.right from rfl))⟩
theorem valid622 : ValidPanel panel622 := ⟨modelCheck622,residualCheck622,
  ReferenceTrajectory.leftBlock35_subset (List.mem_of_getElem? (show ReferenceResiduals.block35[14]?=some panel622.left from rfl)),
  ReferenceTrajectory.rightBlock118_subset (List.mem_of_getElem? (show ReferenceResiduals.block118[8]?=some panel622.right from rfl))⟩
theorem valid623 : ValidPanel panel623 := ⟨modelCheck623,residualCheck623,
  ReferenceTrajectory.leftBlock35_subset (List.mem_of_getElem? (show ReferenceResiduals.block35[15]?=some panel623.left from rfl)),
  ReferenceTrajectory.rightBlock118_subset (List.mem_of_getElem? (show ReferenceResiduals.block118[7]?=some panel623.right from rfl))⟩
theorem valid624 : ValidPanel panel624 := ⟨modelCheck624,residualCheck624,
  ReferenceTrajectory.leftBlock36_subset (List.mem_of_getElem? (show ReferenceResiduals.block36[0]?=some panel624.left from rfl)),
  ReferenceTrajectory.rightBlock118_subset (List.mem_of_getElem? (show ReferenceResiduals.block118[6]?=some panel624.right from rfl))⟩
theorem valid625 : ValidPanel panel625 := ⟨modelCheck625,residualCheck625,
  ReferenceTrajectory.leftBlock36_subset (List.mem_of_getElem? (show ReferenceResiduals.block36[1]?=some panel625.left from rfl)),
  ReferenceTrajectory.rightBlock118_subset (List.mem_of_getElem? (show ReferenceResiduals.block118[5]?=some panel625.right from rfl))⟩
theorem valid626 : ValidPanel panel626 := ⟨modelCheck626,residualCheck626,
  ReferenceTrajectory.leftBlock36_subset (List.mem_of_getElem? (show ReferenceResiduals.block36[2]?=some panel626.left from rfl)),
  ReferenceTrajectory.rightBlock118_subset (List.mem_of_getElem? (show ReferenceResiduals.block118[4]?=some panel626.right from rfl))⟩
theorem valid627 : ValidPanel panel627 := ⟨modelCheck627,residualCheck627,
  ReferenceTrajectory.leftBlock36_subset (List.mem_of_getElem? (show ReferenceResiduals.block36[3]?=some panel627.left from rfl)),
  ReferenceTrajectory.rightBlock118_subset (List.mem_of_getElem? (show ReferenceResiduals.block118[3]?=some panel627.right from rfl))⟩
theorem valid628 : ValidPanel panel628 := ⟨modelCheck628,residualCheck628,
  ReferenceTrajectory.leftBlock36_subset (List.mem_of_getElem? (show ReferenceResiduals.block36[4]?=some panel628.left from rfl)),
  ReferenceTrajectory.rightBlock118_subset (List.mem_of_getElem? (show ReferenceResiduals.block118[2]?=some panel628.right from rfl))⟩
theorem valid629 : ValidPanel panel629 := ⟨modelCheck629,residualCheck629,
  ReferenceTrajectory.leftBlock36_subset (List.mem_of_getElem? (show ReferenceResiduals.block36[5]?=some panel629.left from rfl)),
  ReferenceTrajectory.rightBlock118_subset (List.mem_of_getElem? (show ReferenceResiduals.block118[1]?=some panel629.right from rfl))⟩
theorem valid630 : ValidPanel panel630 := ⟨modelCheck630,residualCheck630,
  ReferenceTrajectory.leftBlock36_subset (List.mem_of_getElem? (show ReferenceResiduals.block36[6]?=some panel630.left from rfl)),
  ReferenceTrajectory.rightBlock118_subset (List.mem_of_getElem? (show ReferenceResiduals.block118[0]?=some panel630.right from rfl))⟩
theorem valid631 : ValidPanel panel631 := ⟨modelCheck631,residualCheck631,
  ReferenceTrajectory.leftBlock36_subset (List.mem_of_getElem? (show ReferenceResiduals.block36[7]?=some panel631.left from rfl)),
  ReferenceTrajectory.rightBlock117_subset (List.mem_of_getElem? (show ReferenceResiduals.block117[15]?=some panel631.right from rfl))⟩
theorem valid632 : ValidPanel panel632 := ⟨modelCheck632,residualCheck632,
  ReferenceTrajectory.leftBlock36_subset (List.mem_of_getElem? (show ReferenceResiduals.block36[8]?=some panel632.left from rfl)),
  ReferenceTrajectory.rightBlock117_subset (List.mem_of_getElem? (show ReferenceResiduals.block117[14]?=some panel632.right from rfl))⟩
theorem valid633 : ValidPanel panel633 := ⟨modelCheck633,residualCheck633,
  ReferenceTrajectory.leftBlock36_subset (List.mem_of_getElem? (show ReferenceResiduals.block36[9]?=some panel633.left from rfl)),
  ReferenceTrajectory.rightBlock117_subset (List.mem_of_getElem? (show ReferenceResiduals.block117[13]?=some panel633.right from rfl))⟩
theorem valid634 : ValidPanel panel634 := ⟨modelCheck634,residualCheck634,
  ReferenceTrajectory.leftBlock36_subset (List.mem_of_getElem? (show ReferenceResiduals.block36[10]?=some panel634.left from rfl)),
  ReferenceTrajectory.rightBlock117_subset (List.mem_of_getElem? (show ReferenceResiduals.block117[12]?=some panel634.right from rfl))⟩
theorem valid635 : ValidPanel panel635 := ⟨modelCheck635,residualCheck635,
  ReferenceTrajectory.leftBlock36_subset (List.mem_of_getElem? (show ReferenceResiduals.block36[11]?=some panel635.left from rfl)),
  ReferenceTrajectory.rightBlock117_subset (List.mem_of_getElem? (show ReferenceResiduals.block117[11]?=some panel635.right from rfl))⟩
theorem valid636 : ValidPanel panel636 := ⟨modelCheck636,residualCheck636,
  ReferenceTrajectory.leftBlock36_subset (List.mem_of_getElem? (show ReferenceResiduals.block36[12]?=some panel636.left from rfl)),
  ReferenceTrajectory.rightBlock117_subset (List.mem_of_getElem? (show ReferenceResiduals.block117[10]?=some panel636.right from rfl))⟩
theorem valid637 : ValidPanel panel637 := ⟨modelCheck637,residualCheck637,
  ReferenceTrajectory.leftBlock36_subset (List.mem_of_getElem? (show ReferenceResiduals.block36[13]?=some panel637.left from rfl)),
  ReferenceTrajectory.rightBlock117_subset (List.mem_of_getElem? (show ReferenceResiduals.block117[9]?=some panel637.right from rfl))⟩
theorem valid638 : ValidPanel panel638 := ⟨modelCheck638,residualCheck638,
  ReferenceTrajectory.leftBlock36_subset (List.mem_of_getElem? (show ReferenceResiduals.block36[14]?=some panel638.left from rfl)),
  ReferenceTrajectory.rightBlock117_subset (List.mem_of_getElem? (show ReferenceResiduals.block117[8]?=some panel638.right from rfl))⟩
theorem valid639 : ValidPanel panel639 := ⟨modelCheck639,residualCheck639,
  ReferenceTrajectory.leftBlock36_subset (List.mem_of_getElem? (show ReferenceResiduals.block36[15]?=some panel639.left from rfl)),
  ReferenceTrajectory.rightBlock117_subset (List.mem_of_getElem? (show ReferenceResiduals.block117[7]?=some panel639.right from rfl))⟩
theorem validBlock19 : ∀ p∈block19,ValidPanel p := by
  simp only [block19,List.forall_mem_cons]
  exact ⟨valid608,⟨valid609,⟨valid610,⟨valid611,⟨valid612,⟨valid613,⟨valid614,⟨valid615,⟨valid616,⟨valid617,⟨valid618,⟨valid619,⟨valid620,⟨valid621,⟨valid622,⟨valid623,⟨valid624,⟨valid625,⟨valid626,⟨valid627,⟨valid628,⟨valid629,⟨valid630,⟨valid631,⟨valid632,⟨valid633,⟨valid634,⟨valid635,⟨valid636,⟨valid637,⟨valid638,⟨valid639,(by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end chebyshev2.Certificates.Compact.ContactValues

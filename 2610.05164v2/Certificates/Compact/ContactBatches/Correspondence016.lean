import «2610.05164v2».Certificates.Compact.ContactBatches.Batch016
import «2610.05164v2».Certificates.Compact.ContactCoverage
import «2610.05164v2».Certificates.Compact.ReferenceTrajectoryIndex

/-!
Article: 2610.05164v2, Section 4.1.
Correspondence016.
Use: `«2610.05164v2».Certificates.Compact.ContactValues.validBlock16` feeds
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
theorem valid512 : ValidPanel panel512 := ⟨modelCheck512,residualCheck512,
  ReferenceTrajectory.leftBlock29_subset (List.mem_of_getElem? (show ReferenceResiduals.block29[0]?=some panel512.left from rfl)),
  ReferenceTrajectory.rightBlock125_subset (List.mem_of_getElem? (show ReferenceResiduals.block125[6]?=some panel512.right from rfl))⟩
theorem valid513 : ValidPanel panel513 := ⟨modelCheck513,residualCheck513,
  ReferenceTrajectory.leftBlock29_subset (List.mem_of_getElem? (show ReferenceResiduals.block29[1]?=some panel513.left from rfl)),
  ReferenceTrajectory.rightBlock125_subset (List.mem_of_getElem? (show ReferenceResiduals.block125[5]?=some panel513.right from rfl))⟩
theorem valid514 : ValidPanel panel514 := ⟨modelCheck514,residualCheck514,
  ReferenceTrajectory.leftBlock29_subset (List.mem_of_getElem? (show ReferenceResiduals.block29[2]?=some panel514.left from rfl)),
  ReferenceTrajectory.rightBlock125_subset (List.mem_of_getElem? (show ReferenceResiduals.block125[4]?=some panel514.right from rfl))⟩
theorem valid515 : ValidPanel panel515 := ⟨modelCheck515,residualCheck515,
  ReferenceTrajectory.leftBlock29_subset (List.mem_of_getElem? (show ReferenceResiduals.block29[3]?=some panel515.left from rfl)),
  ReferenceTrajectory.rightBlock125_subset (List.mem_of_getElem? (show ReferenceResiduals.block125[3]?=some panel515.right from rfl))⟩
theorem valid516 : ValidPanel panel516 := ⟨modelCheck516,residualCheck516,
  ReferenceTrajectory.leftBlock29_subset (List.mem_of_getElem? (show ReferenceResiduals.block29[4]?=some panel516.left from rfl)),
  ReferenceTrajectory.rightBlock125_subset (List.mem_of_getElem? (show ReferenceResiduals.block125[2]?=some panel516.right from rfl))⟩
theorem valid517 : ValidPanel panel517 := ⟨modelCheck517,residualCheck517,
  ReferenceTrajectory.leftBlock29_subset (List.mem_of_getElem? (show ReferenceResiduals.block29[5]?=some panel517.left from rfl)),
  ReferenceTrajectory.rightBlock125_subset (List.mem_of_getElem? (show ReferenceResiduals.block125[1]?=some panel517.right from rfl))⟩
theorem valid518 : ValidPanel panel518 := ⟨modelCheck518,residualCheck518,
  ReferenceTrajectory.leftBlock29_subset (List.mem_of_getElem? (show ReferenceResiduals.block29[6]?=some panel518.left from rfl)),
  ReferenceTrajectory.rightBlock125_subset (List.mem_of_getElem? (show ReferenceResiduals.block125[0]?=some panel518.right from rfl))⟩
theorem valid519 : ValidPanel panel519 := ⟨modelCheck519,residualCheck519,
  ReferenceTrajectory.leftBlock29_subset (List.mem_of_getElem? (show ReferenceResiduals.block29[7]?=some panel519.left from rfl)),
  ReferenceTrajectory.rightBlock124_subset (List.mem_of_getElem? (show ReferenceResiduals.block124[15]?=some panel519.right from rfl))⟩
theorem valid520 : ValidPanel panel520 := ⟨modelCheck520,residualCheck520,
  ReferenceTrajectory.leftBlock29_subset (List.mem_of_getElem? (show ReferenceResiduals.block29[8]?=some panel520.left from rfl)),
  ReferenceTrajectory.rightBlock124_subset (List.mem_of_getElem? (show ReferenceResiduals.block124[14]?=some panel520.right from rfl))⟩
theorem valid521 : ValidPanel panel521 := ⟨modelCheck521,residualCheck521,
  ReferenceTrajectory.leftBlock29_subset (List.mem_of_getElem? (show ReferenceResiduals.block29[9]?=some panel521.left from rfl)),
  ReferenceTrajectory.rightBlock124_subset (List.mem_of_getElem? (show ReferenceResiduals.block124[13]?=some panel521.right from rfl))⟩
theorem valid522 : ValidPanel panel522 := ⟨modelCheck522,residualCheck522,
  ReferenceTrajectory.leftBlock29_subset (List.mem_of_getElem? (show ReferenceResiduals.block29[10]?=some panel522.left from rfl)),
  ReferenceTrajectory.rightBlock124_subset (List.mem_of_getElem? (show ReferenceResiduals.block124[12]?=some panel522.right from rfl))⟩
theorem valid523 : ValidPanel panel523 := ⟨modelCheck523,residualCheck523,
  ReferenceTrajectory.leftBlock29_subset (List.mem_of_getElem? (show ReferenceResiduals.block29[11]?=some panel523.left from rfl)),
  ReferenceTrajectory.rightBlock124_subset (List.mem_of_getElem? (show ReferenceResiduals.block124[11]?=some panel523.right from rfl))⟩
theorem valid524 : ValidPanel panel524 := ⟨modelCheck524,residualCheck524,
  ReferenceTrajectory.leftBlock29_subset (List.mem_of_getElem? (show ReferenceResiduals.block29[12]?=some panel524.left from rfl)),
  ReferenceTrajectory.rightBlock124_subset (List.mem_of_getElem? (show ReferenceResiduals.block124[10]?=some panel524.right from rfl))⟩
theorem valid525 : ValidPanel panel525 := ⟨modelCheck525,residualCheck525,
  ReferenceTrajectory.leftBlock29_subset (List.mem_of_getElem? (show ReferenceResiduals.block29[13]?=some panel525.left from rfl)),
  ReferenceTrajectory.rightBlock124_subset (List.mem_of_getElem? (show ReferenceResiduals.block124[9]?=some panel525.right from rfl))⟩
theorem valid526 : ValidPanel panel526 := ⟨modelCheck526,residualCheck526,
  ReferenceTrajectory.leftBlock29_subset (List.mem_of_getElem? (show ReferenceResiduals.block29[14]?=some panel526.left from rfl)),
  ReferenceTrajectory.rightBlock124_subset (List.mem_of_getElem? (show ReferenceResiduals.block124[8]?=some panel526.right from rfl))⟩
theorem valid527 : ValidPanel panel527 := ⟨modelCheck527,residualCheck527,
  ReferenceTrajectory.leftBlock29_subset (List.mem_of_getElem? (show ReferenceResiduals.block29[15]?=some panel527.left from rfl)),
  ReferenceTrajectory.rightBlock124_subset (List.mem_of_getElem? (show ReferenceResiduals.block124[7]?=some panel527.right from rfl))⟩
theorem valid528 : ValidPanel panel528 := ⟨modelCheck528,residualCheck528,
  ReferenceTrajectory.leftBlock30_subset (List.mem_of_getElem? (show ReferenceResiduals.block30[0]?=some panel528.left from rfl)),
  ReferenceTrajectory.rightBlock124_subset (List.mem_of_getElem? (show ReferenceResiduals.block124[6]?=some panel528.right from rfl))⟩
theorem valid529 : ValidPanel panel529 := ⟨modelCheck529,residualCheck529,
  ReferenceTrajectory.leftBlock30_subset (List.mem_of_getElem? (show ReferenceResiduals.block30[1]?=some panel529.left from rfl)),
  ReferenceTrajectory.rightBlock124_subset (List.mem_of_getElem? (show ReferenceResiduals.block124[5]?=some panel529.right from rfl))⟩
theorem valid530 : ValidPanel panel530 := ⟨modelCheck530,residualCheck530,
  ReferenceTrajectory.leftBlock30_subset (List.mem_of_getElem? (show ReferenceResiduals.block30[2]?=some panel530.left from rfl)),
  ReferenceTrajectory.rightBlock124_subset (List.mem_of_getElem? (show ReferenceResiduals.block124[4]?=some panel530.right from rfl))⟩
theorem valid531 : ValidPanel panel531 := ⟨modelCheck531,residualCheck531,
  ReferenceTrajectory.leftBlock30_subset (List.mem_of_getElem? (show ReferenceResiduals.block30[3]?=some panel531.left from rfl)),
  ReferenceTrajectory.rightBlock124_subset (List.mem_of_getElem? (show ReferenceResiduals.block124[3]?=some panel531.right from rfl))⟩
theorem valid532 : ValidPanel panel532 := ⟨modelCheck532,residualCheck532,
  ReferenceTrajectory.leftBlock30_subset (List.mem_of_getElem? (show ReferenceResiduals.block30[4]?=some panel532.left from rfl)),
  ReferenceTrajectory.rightBlock124_subset (List.mem_of_getElem? (show ReferenceResiduals.block124[2]?=some panel532.right from rfl))⟩
theorem valid533 : ValidPanel panel533 := ⟨modelCheck533,residualCheck533,
  ReferenceTrajectory.leftBlock30_subset (List.mem_of_getElem? (show ReferenceResiduals.block30[5]?=some panel533.left from rfl)),
  ReferenceTrajectory.rightBlock124_subset (List.mem_of_getElem? (show ReferenceResiduals.block124[1]?=some panel533.right from rfl))⟩
theorem valid534 : ValidPanel panel534 := ⟨modelCheck534,residualCheck534,
  ReferenceTrajectory.leftBlock30_subset (List.mem_of_getElem? (show ReferenceResiduals.block30[6]?=some panel534.left from rfl)),
  ReferenceTrajectory.rightBlock124_subset (List.mem_of_getElem? (show ReferenceResiduals.block124[0]?=some panel534.right from rfl))⟩
theorem valid535 : ValidPanel panel535 := ⟨modelCheck535,residualCheck535,
  ReferenceTrajectory.leftBlock30_subset (List.mem_of_getElem? (show ReferenceResiduals.block30[7]?=some panel535.left from rfl)),
  ReferenceTrajectory.rightBlock123_subset (List.mem_of_getElem? (show ReferenceResiduals.block123[15]?=some panel535.right from rfl))⟩
theorem valid536 : ValidPanel panel536 := ⟨modelCheck536,residualCheck536,
  ReferenceTrajectory.leftBlock30_subset (List.mem_of_getElem? (show ReferenceResiduals.block30[8]?=some panel536.left from rfl)),
  ReferenceTrajectory.rightBlock123_subset (List.mem_of_getElem? (show ReferenceResiduals.block123[14]?=some panel536.right from rfl))⟩
theorem valid537 : ValidPanel panel537 := ⟨modelCheck537,residualCheck537,
  ReferenceTrajectory.leftBlock30_subset (List.mem_of_getElem? (show ReferenceResiduals.block30[9]?=some panel537.left from rfl)),
  ReferenceTrajectory.rightBlock123_subset (List.mem_of_getElem? (show ReferenceResiduals.block123[13]?=some panel537.right from rfl))⟩
theorem valid538 : ValidPanel panel538 := ⟨modelCheck538,residualCheck538,
  ReferenceTrajectory.leftBlock30_subset (List.mem_of_getElem? (show ReferenceResiduals.block30[10]?=some panel538.left from rfl)),
  ReferenceTrajectory.rightBlock123_subset (List.mem_of_getElem? (show ReferenceResiduals.block123[12]?=some panel538.right from rfl))⟩
theorem valid539 : ValidPanel panel539 := ⟨modelCheck539,residualCheck539,
  ReferenceTrajectory.leftBlock30_subset (List.mem_of_getElem? (show ReferenceResiduals.block30[11]?=some panel539.left from rfl)),
  ReferenceTrajectory.rightBlock123_subset (List.mem_of_getElem? (show ReferenceResiduals.block123[11]?=some panel539.right from rfl))⟩
theorem valid540 : ValidPanel panel540 := ⟨modelCheck540,residualCheck540,
  ReferenceTrajectory.leftBlock30_subset (List.mem_of_getElem? (show ReferenceResiduals.block30[12]?=some panel540.left from rfl)),
  ReferenceTrajectory.rightBlock123_subset (List.mem_of_getElem? (show ReferenceResiduals.block123[10]?=some panel540.right from rfl))⟩
theorem valid541 : ValidPanel panel541 := ⟨modelCheck541,residualCheck541,
  ReferenceTrajectory.leftBlock30_subset (List.mem_of_getElem? (show ReferenceResiduals.block30[13]?=some panel541.left from rfl)),
  ReferenceTrajectory.rightBlock123_subset (List.mem_of_getElem? (show ReferenceResiduals.block123[9]?=some panel541.right from rfl))⟩
theorem valid542 : ValidPanel panel542 := ⟨modelCheck542,residualCheck542,
  ReferenceTrajectory.leftBlock30_subset (List.mem_of_getElem? (show ReferenceResiduals.block30[14]?=some panel542.left from rfl)),
  ReferenceTrajectory.rightBlock123_subset (List.mem_of_getElem? (show ReferenceResiduals.block123[8]?=some panel542.right from rfl))⟩
theorem valid543 : ValidPanel panel543 := ⟨modelCheck543,residualCheck543,
  ReferenceTrajectory.leftBlock30_subset (List.mem_of_getElem? (show ReferenceResiduals.block30[15]?=some panel543.left from rfl)),
  ReferenceTrajectory.rightBlock123_subset (List.mem_of_getElem? (show ReferenceResiduals.block123[7]?=some panel543.right from rfl))⟩
theorem validBlock16 : ∀ p∈block16,ValidPanel p := by
  simp only [block16,List.forall_mem_cons]
  exact ⟨valid512,⟨valid513,⟨valid514,⟨valid515,⟨valid516,⟨valid517,⟨valid518,⟨valid519,⟨valid520,⟨valid521,⟨valid522,⟨valid523,⟨valid524,⟨valid525,⟨valid526,⟨valid527,⟨valid528,⟨valid529,⟨valid530,⟨valid531,⟨valid532,⟨valid533,⟨valid534,⟨valid535,⟨valid536,⟨valid537,⟨valid538,⟨valid539,⟨valid540,⟨valid541,⟨valid542,⟨valid543,(by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end «2610.05164v2».Certificates.Compact.ContactValues

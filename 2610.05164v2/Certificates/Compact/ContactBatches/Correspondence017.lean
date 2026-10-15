import «2610.05164v2».Certificates.Compact.ContactBatches.Batch017
import «2610.05164v2».Certificates.Compact.ContactCoverage
import «2610.05164v2».Certificates.Compact.ReferenceTrajectoryIndex

/-!
Article: 2610.05164v2, Section 4.1.
Correspondence017.
Use: `«2610.05164v2».Certificates.Compact.ContactValues.validBlock17` feeds
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
theorem valid544 : ValidPanel panel544 := ⟨modelCheck544,residualCheck544,
  ReferenceTrajectory.leftBlock31_subset (List.mem_of_getElem? (show ReferenceResiduals.block31[0]?=some panel544.left from rfl)),
  ReferenceTrajectory.rightBlock123_subset (List.mem_of_getElem? (show ReferenceResiduals.block123[6]?=some panel544.right from rfl))⟩
theorem valid545 : ValidPanel panel545 := ⟨modelCheck545,residualCheck545,
  ReferenceTrajectory.leftBlock31_subset (List.mem_of_getElem? (show ReferenceResiduals.block31[1]?=some panel545.left from rfl)),
  ReferenceTrajectory.rightBlock123_subset (List.mem_of_getElem? (show ReferenceResiduals.block123[5]?=some panel545.right from rfl))⟩
theorem valid546 : ValidPanel panel546 := ⟨modelCheck546,residualCheck546,
  ReferenceTrajectory.leftBlock31_subset (List.mem_of_getElem? (show ReferenceResiduals.block31[2]?=some panel546.left from rfl)),
  ReferenceTrajectory.rightBlock123_subset (List.mem_of_getElem? (show ReferenceResiduals.block123[4]?=some panel546.right from rfl))⟩
theorem valid547 : ValidPanel panel547 := ⟨modelCheck547,residualCheck547,
  ReferenceTrajectory.leftBlock31_subset (List.mem_of_getElem? (show ReferenceResiduals.block31[3]?=some panel547.left from rfl)),
  ReferenceTrajectory.rightBlock123_subset (List.mem_of_getElem? (show ReferenceResiduals.block123[3]?=some panel547.right from rfl))⟩
theorem valid548 : ValidPanel panel548 := ⟨modelCheck548,residualCheck548,
  ReferenceTrajectory.leftBlock31_subset (List.mem_of_getElem? (show ReferenceResiduals.block31[4]?=some panel548.left from rfl)),
  ReferenceTrajectory.rightBlock123_subset (List.mem_of_getElem? (show ReferenceResiduals.block123[2]?=some panel548.right from rfl))⟩
theorem valid549 : ValidPanel panel549 := ⟨modelCheck549,residualCheck549,
  ReferenceTrajectory.leftBlock31_subset (List.mem_of_getElem? (show ReferenceResiduals.block31[5]?=some panel549.left from rfl)),
  ReferenceTrajectory.rightBlock123_subset (List.mem_of_getElem? (show ReferenceResiduals.block123[1]?=some panel549.right from rfl))⟩
theorem valid550 : ValidPanel panel550 := ⟨modelCheck550,residualCheck550,
  ReferenceTrajectory.leftBlock31_subset (List.mem_of_getElem? (show ReferenceResiduals.block31[6]?=some panel550.left from rfl)),
  ReferenceTrajectory.rightBlock123_subset (List.mem_of_getElem? (show ReferenceResiduals.block123[0]?=some panel550.right from rfl))⟩
theorem valid551 : ValidPanel panel551 := ⟨modelCheck551,residualCheck551,
  ReferenceTrajectory.leftBlock31_subset (List.mem_of_getElem? (show ReferenceResiduals.block31[7]?=some panel551.left from rfl)),
  ReferenceTrajectory.rightBlock122_subset (List.mem_of_getElem? (show ReferenceResiduals.block122[15]?=some panel551.right from rfl))⟩
theorem valid552 : ValidPanel panel552 := ⟨modelCheck552,residualCheck552,
  ReferenceTrajectory.leftBlock31_subset (List.mem_of_getElem? (show ReferenceResiduals.block31[8]?=some panel552.left from rfl)),
  ReferenceTrajectory.rightBlock122_subset (List.mem_of_getElem? (show ReferenceResiduals.block122[14]?=some panel552.right from rfl))⟩
theorem valid553 : ValidPanel panel553 := ⟨modelCheck553,residualCheck553,
  ReferenceTrajectory.leftBlock31_subset (List.mem_of_getElem? (show ReferenceResiduals.block31[9]?=some panel553.left from rfl)),
  ReferenceTrajectory.rightBlock122_subset (List.mem_of_getElem? (show ReferenceResiduals.block122[13]?=some panel553.right from rfl))⟩
theorem valid554 : ValidPanel panel554 := ⟨modelCheck554,residualCheck554,
  ReferenceTrajectory.leftBlock31_subset (List.mem_of_getElem? (show ReferenceResiduals.block31[10]?=some panel554.left from rfl)),
  ReferenceTrajectory.rightBlock122_subset (List.mem_of_getElem? (show ReferenceResiduals.block122[12]?=some panel554.right from rfl))⟩
theorem valid555 : ValidPanel panel555 := ⟨modelCheck555,residualCheck555,
  ReferenceTrajectory.leftBlock31_subset (List.mem_of_getElem? (show ReferenceResiduals.block31[11]?=some panel555.left from rfl)),
  ReferenceTrajectory.rightBlock122_subset (List.mem_of_getElem? (show ReferenceResiduals.block122[11]?=some panel555.right from rfl))⟩
theorem valid556 : ValidPanel panel556 := ⟨modelCheck556,residualCheck556,
  ReferenceTrajectory.leftBlock31_subset (List.mem_of_getElem? (show ReferenceResiduals.block31[12]?=some panel556.left from rfl)),
  ReferenceTrajectory.rightBlock122_subset (List.mem_of_getElem? (show ReferenceResiduals.block122[10]?=some panel556.right from rfl))⟩
theorem valid557 : ValidPanel panel557 := ⟨modelCheck557,residualCheck557,
  ReferenceTrajectory.leftBlock31_subset (List.mem_of_getElem? (show ReferenceResiduals.block31[13]?=some panel557.left from rfl)),
  ReferenceTrajectory.rightBlock122_subset (List.mem_of_getElem? (show ReferenceResiduals.block122[9]?=some panel557.right from rfl))⟩
theorem valid558 : ValidPanel panel558 := ⟨modelCheck558,residualCheck558,
  ReferenceTrajectory.leftBlock31_subset (List.mem_of_getElem? (show ReferenceResiduals.block31[14]?=some panel558.left from rfl)),
  ReferenceTrajectory.rightBlock122_subset (List.mem_of_getElem? (show ReferenceResiduals.block122[8]?=some panel558.right from rfl))⟩
theorem valid559 : ValidPanel panel559 := ⟨modelCheck559,residualCheck559,
  ReferenceTrajectory.leftBlock31_subset (List.mem_of_getElem? (show ReferenceResiduals.block31[15]?=some panel559.left from rfl)),
  ReferenceTrajectory.rightBlock122_subset (List.mem_of_getElem? (show ReferenceResiduals.block122[7]?=some panel559.right from rfl))⟩
theorem valid560 : ValidPanel panel560 := ⟨modelCheck560,residualCheck560,
  ReferenceTrajectory.leftBlock32_subset (List.mem_of_getElem? (show ReferenceResiduals.block32[0]?=some panel560.left from rfl)),
  ReferenceTrajectory.rightBlock122_subset (List.mem_of_getElem? (show ReferenceResiduals.block122[6]?=some panel560.right from rfl))⟩
theorem valid561 : ValidPanel panel561 := ⟨modelCheck561,residualCheck561,
  ReferenceTrajectory.leftBlock32_subset (List.mem_of_getElem? (show ReferenceResiduals.block32[1]?=some panel561.left from rfl)),
  ReferenceTrajectory.rightBlock122_subset (List.mem_of_getElem? (show ReferenceResiduals.block122[5]?=some panel561.right from rfl))⟩
theorem valid562 : ValidPanel panel562 := ⟨modelCheck562,residualCheck562,
  ReferenceTrajectory.leftBlock32_subset (List.mem_of_getElem? (show ReferenceResiduals.block32[2]?=some panel562.left from rfl)),
  ReferenceTrajectory.rightBlock122_subset (List.mem_of_getElem? (show ReferenceResiduals.block122[4]?=some panel562.right from rfl))⟩
theorem valid563 : ValidPanel panel563 := ⟨modelCheck563,residualCheck563,
  ReferenceTrajectory.leftBlock32_subset (List.mem_of_getElem? (show ReferenceResiduals.block32[3]?=some panel563.left from rfl)),
  ReferenceTrajectory.rightBlock122_subset (List.mem_of_getElem? (show ReferenceResiduals.block122[3]?=some panel563.right from rfl))⟩
theorem valid564 : ValidPanel panel564 := ⟨modelCheck564,residualCheck564,
  ReferenceTrajectory.leftBlock32_subset (List.mem_of_getElem? (show ReferenceResiduals.block32[4]?=some panel564.left from rfl)),
  ReferenceTrajectory.rightBlock122_subset (List.mem_of_getElem? (show ReferenceResiduals.block122[2]?=some panel564.right from rfl))⟩
theorem valid565 : ValidPanel panel565 := ⟨modelCheck565,residualCheck565,
  ReferenceTrajectory.leftBlock32_subset (List.mem_of_getElem? (show ReferenceResiduals.block32[5]?=some panel565.left from rfl)),
  ReferenceTrajectory.rightBlock122_subset (List.mem_of_getElem? (show ReferenceResiduals.block122[1]?=some panel565.right from rfl))⟩
theorem valid566 : ValidPanel panel566 := ⟨modelCheck566,residualCheck566,
  ReferenceTrajectory.leftBlock32_subset (List.mem_of_getElem? (show ReferenceResiduals.block32[6]?=some panel566.left from rfl)),
  ReferenceTrajectory.rightBlock122_subset (List.mem_of_getElem? (show ReferenceResiduals.block122[0]?=some panel566.right from rfl))⟩
theorem valid567 : ValidPanel panel567 := ⟨modelCheck567,residualCheck567,
  ReferenceTrajectory.leftBlock32_subset (List.mem_of_getElem? (show ReferenceResiduals.block32[7]?=some panel567.left from rfl)),
  ReferenceTrajectory.rightBlock121_subset (List.mem_of_getElem? (show ReferenceResiduals.block121[15]?=some panel567.right from rfl))⟩
theorem valid568 : ValidPanel panel568 := ⟨modelCheck568,residualCheck568,
  ReferenceTrajectory.leftBlock32_subset (List.mem_of_getElem? (show ReferenceResiduals.block32[8]?=some panel568.left from rfl)),
  ReferenceTrajectory.rightBlock121_subset (List.mem_of_getElem? (show ReferenceResiduals.block121[14]?=some panel568.right from rfl))⟩
theorem valid569 : ValidPanel panel569 := ⟨modelCheck569,residualCheck569,
  ReferenceTrajectory.leftBlock32_subset (List.mem_of_getElem? (show ReferenceResiduals.block32[9]?=some panel569.left from rfl)),
  ReferenceTrajectory.rightBlock121_subset (List.mem_of_getElem? (show ReferenceResiduals.block121[13]?=some panel569.right from rfl))⟩
theorem valid570 : ValidPanel panel570 := ⟨modelCheck570,residualCheck570,
  ReferenceTrajectory.leftBlock32_subset (List.mem_of_getElem? (show ReferenceResiduals.block32[10]?=some panel570.left from rfl)),
  ReferenceTrajectory.rightBlock121_subset (List.mem_of_getElem? (show ReferenceResiduals.block121[12]?=some panel570.right from rfl))⟩
theorem valid571 : ValidPanel panel571 := ⟨modelCheck571,residualCheck571,
  ReferenceTrajectory.leftBlock32_subset (List.mem_of_getElem? (show ReferenceResiduals.block32[11]?=some panel571.left from rfl)),
  ReferenceTrajectory.rightBlock121_subset (List.mem_of_getElem? (show ReferenceResiduals.block121[11]?=some panel571.right from rfl))⟩
theorem valid572 : ValidPanel panel572 := ⟨modelCheck572,residualCheck572,
  ReferenceTrajectory.leftBlock32_subset (List.mem_of_getElem? (show ReferenceResiduals.block32[12]?=some panel572.left from rfl)),
  ReferenceTrajectory.rightBlock121_subset (List.mem_of_getElem? (show ReferenceResiduals.block121[10]?=some panel572.right from rfl))⟩
theorem valid573 : ValidPanel panel573 := ⟨modelCheck573,residualCheck573,
  ReferenceTrajectory.leftBlock32_subset (List.mem_of_getElem? (show ReferenceResiduals.block32[13]?=some panel573.left from rfl)),
  ReferenceTrajectory.rightBlock121_subset (List.mem_of_getElem? (show ReferenceResiduals.block121[9]?=some panel573.right from rfl))⟩
theorem valid574 : ValidPanel panel574 := ⟨modelCheck574,residualCheck574,
  ReferenceTrajectory.leftBlock32_subset (List.mem_of_getElem? (show ReferenceResiduals.block32[14]?=some panel574.left from rfl)),
  ReferenceTrajectory.rightBlock121_subset (List.mem_of_getElem? (show ReferenceResiduals.block121[8]?=some panel574.right from rfl))⟩
theorem valid575 : ValidPanel panel575 := ⟨modelCheck575,residualCheck575,
  ReferenceTrajectory.leftBlock32_subset (List.mem_of_getElem? (show ReferenceResiduals.block32[15]?=some panel575.left from rfl)),
  ReferenceTrajectory.rightBlock121_subset (List.mem_of_getElem? (show ReferenceResiduals.block121[7]?=some panel575.right from rfl))⟩
theorem validBlock17 : ∀ p∈block17,ValidPanel p := by
  simp only [block17,List.forall_mem_cons]
  exact ⟨valid544,⟨valid545,⟨valid546,⟨valid547,⟨valid548,⟨valid549,⟨valid550,⟨valid551,⟨valid552,⟨valid553,⟨valid554,⟨valid555,⟨valid556,⟨valid557,⟨valid558,⟨valid559,⟨valid560,⟨valid561,⟨valid562,⟨valid563,⟨valid564,⟨valid565,⟨valid566,⟨valid567,⟨valid568,⟨valid569,⟨valid570,⟨valid571,⟨valid572,⟨valid573,⟨valid574,⟨valid575,(by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end «2610.05164v2».Certificates.Compact.ContactValues

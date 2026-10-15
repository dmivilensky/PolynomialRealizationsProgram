import «2610.05164v2».Certificates.Compact.ContactBatches.Batch000
import «2610.05164v2».Certificates.Compact.ContactCoverage
import «2610.05164v2».Certificates.Compact.ReferenceTrajectoryIndex

/-!
Article: 2610.05164v2, Section 4.1.
Correspondence000.
Use: `«2610.05164v2».Certificates.Compact.ContactValues.validBlock0` feeds
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
theorem valid0 : ValidPanel panel0 := ⟨modelCheck0,residualCheck0,
  ReferenceTrajectory.leftBlock0_subset (List.mem_of_getElem? (show ReferenceResiduals.block0[0]?=some panel0.left from rfl)),
  ReferenceTrajectory.rightBlock157_subset (List.mem_of_getElem? (show ReferenceResiduals.block157[6]?=some panel0.right from rfl))⟩
theorem valid1 : ValidPanel panel1 := ⟨modelCheck1,residualCheck1,
  ReferenceTrajectory.leftBlock0_subset (List.mem_of_getElem? (show ReferenceResiduals.block0[0]?=some panel1.left from rfl)),
  ReferenceTrajectory.rightBlock157_subset (List.mem_of_getElem? (show ReferenceResiduals.block157[5]?=some panel1.right from rfl))⟩
theorem valid2 : ValidPanel panel2 := ⟨modelCheck2,residualCheck2,
  ReferenceTrajectory.leftBlock0_subset (List.mem_of_getElem? (show ReferenceResiduals.block0[1]?=some panel2.left from rfl)),
  ReferenceTrajectory.rightBlock157_subset (List.mem_of_getElem? (show ReferenceResiduals.block157[4]?=some panel2.right from rfl))⟩
theorem valid3 : ValidPanel panel3 := ⟨modelCheck3,residualCheck3,
  ReferenceTrajectory.leftBlock0_subset (List.mem_of_getElem? (show ReferenceResiduals.block0[2]?=some panel3.left from rfl)),
  ReferenceTrajectory.rightBlock157_subset (List.mem_of_getElem? (show ReferenceResiduals.block157[3]?=some panel3.right from rfl))⟩
theorem valid4 : ValidPanel panel4 := ⟨modelCheck4,residualCheck4,
  ReferenceTrajectory.leftBlock0_subset (List.mem_of_getElem? (show ReferenceResiduals.block0[3]?=some panel4.left from rfl)),
  ReferenceTrajectory.rightBlock157_subset (List.mem_of_getElem? (show ReferenceResiduals.block157[2]?=some panel4.right from rfl))⟩
theorem valid5 : ValidPanel panel5 := ⟨modelCheck5,residualCheck5,
  ReferenceTrajectory.leftBlock0_subset (List.mem_of_getElem? (show ReferenceResiduals.block0[4]?=some panel5.left from rfl)),
  ReferenceTrajectory.rightBlock157_subset (List.mem_of_getElem? (show ReferenceResiduals.block157[1]?=some panel5.right from rfl))⟩
theorem valid6 : ValidPanel panel6 := ⟨modelCheck6,residualCheck6,
  ReferenceTrajectory.leftBlock0_subset (List.mem_of_getElem? (show ReferenceResiduals.block0[5]?=some panel6.left from rfl)),
  ReferenceTrajectory.rightBlock157_subset (List.mem_of_getElem? (show ReferenceResiduals.block157[0]?=some panel6.right from rfl))⟩
theorem valid7 : ValidPanel panel7 := ⟨modelCheck7,residualCheck7,
  ReferenceTrajectory.leftBlock0_subset (List.mem_of_getElem? (show ReferenceResiduals.block0[6]?=some panel7.left from rfl)),
  ReferenceTrajectory.rightBlock156_subset (List.mem_of_getElem? (show ReferenceResiduals.block156[15]?=some panel7.right from rfl))⟩
theorem valid8 : ValidPanel panel8 := ⟨modelCheck8,residualCheck8,
  ReferenceTrajectory.leftBlock0_subset (List.mem_of_getElem? (show ReferenceResiduals.block0[7]?=some panel8.left from rfl)),
  ReferenceTrajectory.rightBlock156_subset (List.mem_of_getElem? (show ReferenceResiduals.block156[14]?=some panel8.right from rfl))⟩
theorem valid9 : ValidPanel panel9 := ⟨modelCheck9,residualCheck9,
  ReferenceTrajectory.leftBlock0_subset (List.mem_of_getElem? (show ReferenceResiduals.block0[8]?=some panel9.left from rfl)),
  ReferenceTrajectory.rightBlock156_subset (List.mem_of_getElem? (show ReferenceResiduals.block156[13]?=some panel9.right from rfl))⟩
theorem valid10 : ValidPanel panel10 := ⟨modelCheck10,residualCheck10,
  ReferenceTrajectory.leftBlock0_subset (List.mem_of_getElem? (show ReferenceResiduals.block0[9]?=some panel10.left from rfl)),
  ReferenceTrajectory.rightBlock156_subset (List.mem_of_getElem? (show ReferenceResiduals.block156[12]?=some panel10.right from rfl))⟩
theorem valid11 : ValidPanel panel11 := ⟨modelCheck11,residualCheck11,
  ReferenceTrajectory.leftBlock0_subset (List.mem_of_getElem? (show ReferenceResiduals.block0[10]?=some panel11.left from rfl)),
  ReferenceTrajectory.rightBlock156_subset (List.mem_of_getElem? (show ReferenceResiduals.block156[11]?=some panel11.right from rfl))⟩
theorem valid12 : ValidPanel panel12 := ⟨modelCheck12,residualCheck12,
  ReferenceTrajectory.leftBlock0_subset (List.mem_of_getElem? (show ReferenceResiduals.block0[11]?=some panel12.left from rfl)),
  ReferenceTrajectory.rightBlock156_subset (List.mem_of_getElem? (show ReferenceResiduals.block156[10]?=some panel12.right from rfl))⟩
theorem valid13 : ValidPanel panel13 := ⟨modelCheck13,residualCheck13,
  ReferenceTrajectory.leftBlock0_subset (List.mem_of_getElem? (show ReferenceResiduals.block0[12]?=some panel13.left from rfl)),
  ReferenceTrajectory.rightBlock156_subset (List.mem_of_getElem? (show ReferenceResiduals.block156[9]?=some panel13.right from rfl))⟩
theorem valid14 : ValidPanel panel14 := ⟨modelCheck14,residualCheck14,
  ReferenceTrajectory.leftBlock0_subset (List.mem_of_getElem? (show ReferenceResiduals.block0[13]?=some panel14.left from rfl)),
  ReferenceTrajectory.rightBlock156_subset (List.mem_of_getElem? (show ReferenceResiduals.block156[8]?=some panel14.right from rfl))⟩
theorem valid15 : ValidPanel panel15 := ⟨modelCheck15,residualCheck15,
  ReferenceTrajectory.leftBlock0_subset (List.mem_of_getElem? (show ReferenceResiduals.block0[14]?=some panel15.left from rfl)),
  ReferenceTrajectory.rightBlock156_subset (List.mem_of_getElem? (show ReferenceResiduals.block156[7]?=some panel15.right from rfl))⟩
theorem valid16 : ValidPanel panel16 := ⟨modelCheck16,residualCheck16,
  ReferenceTrajectory.leftBlock0_subset (List.mem_of_getElem? (show ReferenceResiduals.block0[15]?=some panel16.left from rfl)),
  ReferenceTrajectory.rightBlock156_subset (List.mem_of_getElem? (show ReferenceResiduals.block156[6]?=some panel16.right from rfl))⟩
theorem valid17 : ValidPanel panel17 := ⟨modelCheck17,residualCheck17,
  ReferenceTrajectory.leftBlock1_subset (List.mem_of_getElem? (show ReferenceResiduals.block1[0]?=some panel17.left from rfl)),
  ReferenceTrajectory.rightBlock156_subset (List.mem_of_getElem? (show ReferenceResiduals.block156[5]?=some panel17.right from rfl))⟩
theorem valid18 : ValidPanel panel18 := ⟨modelCheck18,residualCheck18,
  ReferenceTrajectory.leftBlock1_subset (List.mem_of_getElem? (show ReferenceResiduals.block1[1]?=some panel18.left from rfl)),
  ReferenceTrajectory.rightBlock156_subset (List.mem_of_getElem? (show ReferenceResiduals.block156[4]?=some panel18.right from rfl))⟩
theorem valid19 : ValidPanel panel19 := ⟨modelCheck19,residualCheck19,
  ReferenceTrajectory.leftBlock1_subset (List.mem_of_getElem? (show ReferenceResiduals.block1[2]?=some panel19.left from rfl)),
  ReferenceTrajectory.rightBlock156_subset (List.mem_of_getElem? (show ReferenceResiduals.block156[3]?=some panel19.right from rfl))⟩
theorem valid20 : ValidPanel panel20 := ⟨modelCheck20,residualCheck20,
  ReferenceTrajectory.leftBlock1_subset (List.mem_of_getElem? (show ReferenceResiduals.block1[3]?=some panel20.left from rfl)),
  ReferenceTrajectory.rightBlock156_subset (List.mem_of_getElem? (show ReferenceResiduals.block156[2]?=some panel20.right from rfl))⟩
theorem valid21 : ValidPanel panel21 := ⟨modelCheck21,residualCheck21,
  ReferenceTrajectory.leftBlock1_subset (List.mem_of_getElem? (show ReferenceResiduals.block1[4]?=some panel21.left from rfl)),
  ReferenceTrajectory.rightBlock156_subset (List.mem_of_getElem? (show ReferenceResiduals.block156[1]?=some panel21.right from rfl))⟩
theorem valid22 : ValidPanel panel22 := ⟨modelCheck22,residualCheck22,
  ReferenceTrajectory.leftBlock1_subset (List.mem_of_getElem? (show ReferenceResiduals.block1[5]?=some panel22.left from rfl)),
  ReferenceTrajectory.rightBlock156_subset (List.mem_of_getElem? (show ReferenceResiduals.block156[0]?=some panel22.right from rfl))⟩
theorem valid23 : ValidPanel panel23 := ⟨modelCheck23,residualCheck23,
  ReferenceTrajectory.leftBlock1_subset (List.mem_of_getElem? (show ReferenceResiduals.block1[6]?=some panel23.left from rfl)),
  ReferenceTrajectory.rightBlock155_subset (List.mem_of_getElem? (show ReferenceResiduals.block155[15]?=some panel23.right from rfl))⟩
theorem valid24 : ValidPanel panel24 := ⟨modelCheck24,residualCheck24,
  ReferenceTrajectory.leftBlock1_subset (List.mem_of_getElem? (show ReferenceResiduals.block1[7]?=some panel24.left from rfl)),
  ReferenceTrajectory.rightBlock155_subset (List.mem_of_getElem? (show ReferenceResiduals.block155[14]?=some panel24.right from rfl))⟩
theorem valid25 : ValidPanel panel25 := ⟨modelCheck25,residualCheck25,
  ReferenceTrajectory.leftBlock1_subset (List.mem_of_getElem? (show ReferenceResiduals.block1[8]?=some panel25.left from rfl)),
  ReferenceTrajectory.rightBlock155_subset (List.mem_of_getElem? (show ReferenceResiduals.block155[13]?=some panel25.right from rfl))⟩
theorem valid26 : ValidPanel panel26 := ⟨modelCheck26,residualCheck26,
  ReferenceTrajectory.leftBlock1_subset (List.mem_of_getElem? (show ReferenceResiduals.block1[9]?=some panel26.left from rfl)),
  ReferenceTrajectory.rightBlock155_subset (List.mem_of_getElem? (show ReferenceResiduals.block155[12]?=some panel26.right from rfl))⟩
theorem valid27 : ValidPanel panel27 := ⟨modelCheck27,residualCheck27,
  ReferenceTrajectory.leftBlock1_subset (List.mem_of_getElem? (show ReferenceResiduals.block1[10]?=some panel27.left from rfl)),
  ReferenceTrajectory.rightBlock155_subset (List.mem_of_getElem? (show ReferenceResiduals.block155[11]?=some panel27.right from rfl))⟩
theorem valid28 : ValidPanel panel28 := ⟨modelCheck28,residualCheck28,
  ReferenceTrajectory.leftBlock1_subset (List.mem_of_getElem? (show ReferenceResiduals.block1[11]?=some panel28.left from rfl)),
  ReferenceTrajectory.rightBlock155_subset (List.mem_of_getElem? (show ReferenceResiduals.block155[10]?=some panel28.right from rfl))⟩
theorem valid29 : ValidPanel panel29 := ⟨modelCheck29,residualCheck29,
  ReferenceTrajectory.leftBlock1_subset (List.mem_of_getElem? (show ReferenceResiduals.block1[12]?=some panel29.left from rfl)),
  ReferenceTrajectory.rightBlock155_subset (List.mem_of_getElem? (show ReferenceResiduals.block155[9]?=some panel29.right from rfl))⟩
theorem valid30 : ValidPanel panel30 := ⟨modelCheck30,residualCheck30,
  ReferenceTrajectory.leftBlock1_subset (List.mem_of_getElem? (show ReferenceResiduals.block1[13]?=some panel30.left from rfl)),
  ReferenceTrajectory.rightBlock155_subset (List.mem_of_getElem? (show ReferenceResiduals.block155[8]?=some panel30.right from rfl))⟩
theorem valid31 : ValidPanel panel31 := ⟨modelCheck31,residualCheck31,
  ReferenceTrajectory.leftBlock1_subset (List.mem_of_getElem? (show ReferenceResiduals.block1[14]?=some panel31.left from rfl)),
  ReferenceTrajectory.rightBlock155_subset (List.mem_of_getElem? (show ReferenceResiduals.block155[7]?=some panel31.right from rfl))⟩
theorem validBlock0 : ∀ p∈block0,ValidPanel p := by
  simp only [block0,List.forall_mem_cons]
  exact ⟨valid0,⟨valid1,⟨valid2,⟨valid3,⟨valid4,⟨valid5,⟨valid6,⟨valid7,⟨valid8,⟨valid9,⟨valid10,⟨valid11,⟨valid12,⟨valid13,⟨valid14,⟨valid15,⟨valid16,⟨valid17,⟨valid18,⟨valid19,⟨valid20,⟨valid21,⟨valid22,⟨valid23,⟨valid24,⟨valid25,⟨valid26,⟨valid27,⟨valid28,⟨valid29,⟨valid30,⟨valid31,(by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end «2610.05164v2».Certificates.Compact.ContactValues

import «2610.05164v2».Certificates.Compact.ContactBatches.Batch004
import «2610.05164v2».Certificates.Compact.ContactCoverage
import «2610.05164v2».Certificates.Compact.ReferenceTrajectoryIndex

/-!
Article: 2610.05164v2, Section 4.1.
Correspondence004.
Use: `«2610.05164v2».Certificates.Compact.ContactValues.validBlock4` feeds
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
theorem valid128 : ValidPanel panel128 := ⟨modelCheck128,residualCheck128,
  ReferenceTrajectory.leftBlock5_subset (List.mem_of_getElem? (show ReferenceResiduals.block5[1]?=some panel128.left from rfl)),
  ReferenceTrajectory.rightBlock149_subset (List.mem_of_getElem? (show ReferenceResiduals.block149[6]?=some panel128.right from rfl))⟩
theorem valid129 : ValidPanel panel129 := ⟨modelCheck129,residualCheck129,
  ReferenceTrajectory.leftBlock5_subset (List.mem_of_getElem? (show ReferenceResiduals.block5[2]?=some panel129.left from rfl)),
  ReferenceTrajectory.rightBlock149_subset (List.mem_of_getElem? (show ReferenceResiduals.block149[5]?=some panel129.right from rfl))⟩
theorem valid130 : ValidPanel panel130 := ⟨modelCheck130,residualCheck130,
  ReferenceTrajectory.leftBlock5_subset (List.mem_of_getElem? (show ReferenceResiduals.block5[2]?=some panel130.left from rfl)),
  ReferenceTrajectory.rightBlock149_subset (List.mem_of_getElem? (show ReferenceResiduals.block149[4]?=some panel130.right from rfl))⟩
theorem valid131 : ValidPanel panel131 := ⟨modelCheck131,residualCheck131,
  ReferenceTrajectory.leftBlock5_subset (List.mem_of_getElem? (show ReferenceResiduals.block5[3]?=some panel131.left from rfl)),
  ReferenceTrajectory.rightBlock149_subset (List.mem_of_getElem? (show ReferenceResiduals.block149[3]?=some panel131.right from rfl))⟩
theorem valid132 : ValidPanel panel132 := ⟨modelCheck132,residualCheck132,
  ReferenceTrajectory.leftBlock5_subset (List.mem_of_getElem? (show ReferenceResiduals.block5[4]?=some panel132.left from rfl)),
  ReferenceTrajectory.rightBlock149_subset (List.mem_of_getElem? (show ReferenceResiduals.block149[2]?=some panel132.right from rfl))⟩
theorem valid133 : ValidPanel panel133 := ⟨modelCheck133,residualCheck133,
  ReferenceTrajectory.leftBlock5_subset (List.mem_of_getElem? (show ReferenceResiduals.block5[5]?=some panel133.left from rfl)),
  ReferenceTrajectory.rightBlock149_subset (List.mem_of_getElem? (show ReferenceResiduals.block149[1]?=some panel133.right from rfl))⟩
theorem valid134 : ValidPanel panel134 := ⟨modelCheck134,residualCheck134,
  ReferenceTrajectory.leftBlock5_subset (List.mem_of_getElem? (show ReferenceResiduals.block5[6]?=some panel134.left from rfl)),
  ReferenceTrajectory.rightBlock149_subset (List.mem_of_getElem? (show ReferenceResiduals.block149[0]?=some panel134.right from rfl))⟩
theorem valid135 : ValidPanel panel135 := ⟨modelCheck135,residualCheck135,
  ReferenceTrajectory.leftBlock5_subset (List.mem_of_getElem? (show ReferenceResiduals.block5[7]?=some panel135.left from rfl)),
  ReferenceTrajectory.rightBlock148_subset (List.mem_of_getElem? (show ReferenceResiduals.block148[15]?=some panel135.right from rfl))⟩
theorem valid136 : ValidPanel panel136 := ⟨modelCheck136,residualCheck136,
  ReferenceTrajectory.leftBlock5_subset (List.mem_of_getElem? (show ReferenceResiduals.block5[8]?=some panel136.left from rfl)),
  ReferenceTrajectory.rightBlock148_subset (List.mem_of_getElem? (show ReferenceResiduals.block148[14]?=some panel136.right from rfl))⟩
theorem valid137 : ValidPanel panel137 := ⟨modelCheck137,residualCheck137,
  ReferenceTrajectory.leftBlock5_subset (List.mem_of_getElem? (show ReferenceResiduals.block5[9]?=some panel137.left from rfl)),
  ReferenceTrajectory.rightBlock148_subset (List.mem_of_getElem? (show ReferenceResiduals.block148[13]?=some panel137.right from rfl))⟩
theorem valid138 : ValidPanel panel138 := ⟨modelCheck138,residualCheck138,
  ReferenceTrajectory.leftBlock5_subset (List.mem_of_getElem? (show ReferenceResiduals.block5[10]?=some panel138.left from rfl)),
  ReferenceTrajectory.rightBlock148_subset (List.mem_of_getElem? (show ReferenceResiduals.block148[12]?=some panel138.right from rfl))⟩
theorem valid139 : ValidPanel panel139 := ⟨modelCheck139,residualCheck139,
  ReferenceTrajectory.leftBlock5_subset (List.mem_of_getElem? (show ReferenceResiduals.block5[11]?=some panel139.left from rfl)),
  ReferenceTrajectory.rightBlock148_subset (List.mem_of_getElem? (show ReferenceResiduals.block148[11]?=some panel139.right from rfl))⟩
theorem valid140 : ValidPanel panel140 := ⟨modelCheck140,residualCheck140,
  ReferenceTrajectory.leftBlock5_subset (List.mem_of_getElem? (show ReferenceResiduals.block5[12]?=some panel140.left from rfl)),
  ReferenceTrajectory.rightBlock148_subset (List.mem_of_getElem? (show ReferenceResiduals.block148[10]?=some panel140.right from rfl))⟩
theorem valid141 : ValidPanel panel141 := ⟨modelCheck141,residualCheck141,
  ReferenceTrajectory.leftBlock5_subset (List.mem_of_getElem? (show ReferenceResiduals.block5[13]?=some panel141.left from rfl)),
  ReferenceTrajectory.rightBlock148_subset (List.mem_of_getElem? (show ReferenceResiduals.block148[9]?=some panel141.right from rfl))⟩
theorem valid142 : ValidPanel panel142 := ⟨modelCheck142,residualCheck142,
  ReferenceTrajectory.leftBlock5_subset (List.mem_of_getElem? (show ReferenceResiduals.block5[14]?=some panel142.left from rfl)),
  ReferenceTrajectory.rightBlock148_subset (List.mem_of_getElem? (show ReferenceResiduals.block148[8]?=some panel142.right from rfl))⟩
theorem valid143 : ValidPanel panel143 := ⟨modelCheck143,residualCheck143,
  ReferenceTrajectory.leftBlock5_subset (List.mem_of_getElem? (show ReferenceResiduals.block5[15]?=some panel143.left from rfl)),
  ReferenceTrajectory.rightBlock148_subset (List.mem_of_getElem? (show ReferenceResiduals.block148[7]?=some panel143.right from rfl))⟩
theorem valid144 : ValidPanel panel144 := ⟨modelCheck144,residualCheck144,
  ReferenceTrajectory.leftBlock6_subset (List.mem_of_getElem? (show ReferenceResiduals.block6[0]?=some panel144.left from rfl)),
  ReferenceTrajectory.rightBlock148_subset (List.mem_of_getElem? (show ReferenceResiduals.block148[6]?=some panel144.right from rfl))⟩
theorem valid145 : ValidPanel panel145 := ⟨modelCheck145,residualCheck145,
  ReferenceTrajectory.leftBlock6_subset (List.mem_of_getElem? (show ReferenceResiduals.block6[1]?=some panel145.left from rfl)),
  ReferenceTrajectory.rightBlock148_subset (List.mem_of_getElem? (show ReferenceResiduals.block148[5]?=some panel145.right from rfl))⟩
theorem valid146 : ValidPanel panel146 := ⟨modelCheck146,residualCheck146,
  ReferenceTrajectory.leftBlock6_subset (List.mem_of_getElem? (show ReferenceResiduals.block6[2]?=some panel146.left from rfl)),
  ReferenceTrajectory.rightBlock148_subset (List.mem_of_getElem? (show ReferenceResiduals.block148[4]?=some panel146.right from rfl))⟩
theorem valid147 : ValidPanel panel147 := ⟨modelCheck147,residualCheck147,
  ReferenceTrajectory.leftBlock6_subset (List.mem_of_getElem? (show ReferenceResiduals.block6[3]?=some panel147.left from rfl)),
  ReferenceTrajectory.rightBlock148_subset (List.mem_of_getElem? (show ReferenceResiduals.block148[3]?=some panel147.right from rfl))⟩
theorem valid148 : ValidPanel panel148 := ⟨modelCheck148,residualCheck148,
  ReferenceTrajectory.leftBlock6_subset (List.mem_of_getElem? (show ReferenceResiduals.block6[4]?=some panel148.left from rfl)),
  ReferenceTrajectory.rightBlock148_subset (List.mem_of_getElem? (show ReferenceResiduals.block148[2]?=some panel148.right from rfl))⟩
theorem valid149 : ValidPanel panel149 := ⟨modelCheck149,residualCheck149,
  ReferenceTrajectory.leftBlock6_subset (List.mem_of_getElem? (show ReferenceResiduals.block6[5]?=some panel149.left from rfl)),
  ReferenceTrajectory.rightBlock148_subset (List.mem_of_getElem? (show ReferenceResiduals.block148[1]?=some panel149.right from rfl))⟩
theorem valid150 : ValidPanel panel150 := ⟨modelCheck150,residualCheck150,
  ReferenceTrajectory.leftBlock6_subset (List.mem_of_getElem? (show ReferenceResiduals.block6[6]?=some panel150.left from rfl)),
  ReferenceTrajectory.rightBlock148_subset (List.mem_of_getElem? (show ReferenceResiduals.block148[0]?=some panel150.right from rfl))⟩
theorem valid151 : ValidPanel panel151 := ⟨modelCheck151,residualCheck151,
  ReferenceTrajectory.leftBlock6_subset (List.mem_of_getElem? (show ReferenceResiduals.block6[7]?=some panel151.left from rfl)),
  ReferenceTrajectory.rightBlock147_subset (List.mem_of_getElem? (show ReferenceResiduals.block147[15]?=some panel151.right from rfl))⟩
theorem valid152 : ValidPanel panel152 := ⟨modelCheck152,residualCheck152,
  ReferenceTrajectory.leftBlock6_subset (List.mem_of_getElem? (show ReferenceResiduals.block6[8]?=some panel152.left from rfl)),
  ReferenceTrajectory.rightBlock147_subset (List.mem_of_getElem? (show ReferenceResiduals.block147[14]?=some panel152.right from rfl))⟩
theorem valid153 : ValidPanel panel153 := ⟨modelCheck153,residualCheck153,
  ReferenceTrajectory.leftBlock6_subset (List.mem_of_getElem? (show ReferenceResiduals.block6[9]?=some panel153.left from rfl)),
  ReferenceTrajectory.rightBlock147_subset (List.mem_of_getElem? (show ReferenceResiduals.block147[13]?=some panel153.right from rfl))⟩
theorem valid154 : ValidPanel panel154 := ⟨modelCheck154,residualCheck154,
  ReferenceTrajectory.leftBlock6_subset (List.mem_of_getElem? (show ReferenceResiduals.block6[10]?=some panel154.left from rfl)),
  ReferenceTrajectory.rightBlock147_subset (List.mem_of_getElem? (show ReferenceResiduals.block147[12]?=some panel154.right from rfl))⟩
theorem valid155 : ValidPanel panel155 := ⟨modelCheck155,residualCheck155,
  ReferenceTrajectory.leftBlock6_subset (List.mem_of_getElem? (show ReferenceResiduals.block6[11]?=some panel155.left from rfl)),
  ReferenceTrajectory.rightBlock147_subset (List.mem_of_getElem? (show ReferenceResiduals.block147[11]?=some panel155.right from rfl))⟩
theorem valid156 : ValidPanel panel156 := ⟨modelCheck156,residualCheck156,
  ReferenceTrajectory.leftBlock6_subset (List.mem_of_getElem? (show ReferenceResiduals.block6[12]?=some panel156.left from rfl)),
  ReferenceTrajectory.rightBlock147_subset (List.mem_of_getElem? (show ReferenceResiduals.block147[10]?=some panel156.right from rfl))⟩
theorem valid157 : ValidPanel panel157 := ⟨modelCheck157,residualCheck157,
  ReferenceTrajectory.leftBlock6_subset (List.mem_of_getElem? (show ReferenceResiduals.block6[13]?=some panel157.left from rfl)),
  ReferenceTrajectory.rightBlock147_subset (List.mem_of_getElem? (show ReferenceResiduals.block147[9]?=some panel157.right from rfl))⟩
theorem valid158 : ValidPanel panel158 := ⟨modelCheck158,residualCheck158,
  ReferenceTrajectory.leftBlock6_subset (List.mem_of_getElem? (show ReferenceResiduals.block6[14]?=some panel158.left from rfl)),
  ReferenceTrajectory.rightBlock147_subset (List.mem_of_getElem? (show ReferenceResiduals.block147[8]?=some panel158.right from rfl))⟩
theorem valid159 : ValidPanel panel159 := ⟨modelCheck159,residualCheck159,
  ReferenceTrajectory.leftBlock6_subset (List.mem_of_getElem? (show ReferenceResiduals.block6[15]?=some panel159.left from rfl)),
  ReferenceTrajectory.rightBlock147_subset (List.mem_of_getElem? (show ReferenceResiduals.block147[7]?=some panel159.right from rfl))⟩
theorem validBlock4 : ∀ p∈block4,ValidPanel p := by
  simp only [block4,List.forall_mem_cons]
  exact ⟨valid128,⟨valid129,⟨valid130,⟨valid131,⟨valid132,⟨valid133,⟨valid134,⟨valid135,⟨valid136,⟨valid137,⟨valid138,⟨valid139,⟨valid140,⟨valid141,⟨valid142,⟨valid143,⟨valid144,⟨valid145,⟨valid146,⟨valid147,⟨valid148,⟨valid149,⟨valid150,⟨valid151,⟨valid152,⟨valid153,⟨valid154,⟨valid155,⟨valid156,⟨valid157,⟨valid158,⟨valid159,(by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end «2610.05164v2».Certificates.Compact.ContactValues

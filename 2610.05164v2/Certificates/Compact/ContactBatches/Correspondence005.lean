import «2610.05164v2».Certificates.Compact.ContactBatches.Batch005
import «2610.05164v2».Certificates.Compact.ContactCoverage
import «2610.05164v2».Certificates.Compact.ReferenceTrajectoryIndex

/-!
Article: 2610.05164v2, Section 4.1.
Correspondence005.
Use: `«2610.05164v2».Certificates.Compact.ContactValues.validBlock5` feeds
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
theorem valid160 : ValidPanel panel160 := ⟨modelCheck160,residualCheck160,
  ReferenceTrajectory.leftBlock7_subset (List.mem_of_getElem? (show ReferenceResiduals.block7[0]?=some panel160.left from rfl)),
  ReferenceTrajectory.rightBlock147_subset (List.mem_of_getElem? (show ReferenceResiduals.block147[6]?=some panel160.right from rfl))⟩
theorem valid161 : ValidPanel panel161 := ⟨modelCheck161,residualCheck161,
  ReferenceTrajectory.leftBlock7_subset (List.mem_of_getElem? (show ReferenceResiduals.block7[1]?=some panel161.left from rfl)),
  ReferenceTrajectory.rightBlock147_subset (List.mem_of_getElem? (show ReferenceResiduals.block147[5]?=some panel161.right from rfl))⟩
theorem valid162 : ValidPanel panel162 := ⟨modelCheck162,residualCheck162,
  ReferenceTrajectory.leftBlock7_subset (List.mem_of_getElem? (show ReferenceResiduals.block7[2]?=some panel162.left from rfl)),
  ReferenceTrajectory.rightBlock147_subset (List.mem_of_getElem? (show ReferenceResiduals.block147[4]?=some panel162.right from rfl))⟩
theorem valid163 : ValidPanel panel163 := ⟨modelCheck163,residualCheck163,
  ReferenceTrajectory.leftBlock7_subset (List.mem_of_getElem? (show ReferenceResiduals.block7[3]?=some panel163.left from rfl)),
  ReferenceTrajectory.rightBlock147_subset (List.mem_of_getElem? (show ReferenceResiduals.block147[3]?=some panel163.right from rfl))⟩
theorem valid164 : ValidPanel panel164 := ⟨modelCheck164,residualCheck164,
  ReferenceTrajectory.leftBlock7_subset (List.mem_of_getElem? (show ReferenceResiduals.block7[4]?=some panel164.left from rfl)),
  ReferenceTrajectory.rightBlock147_subset (List.mem_of_getElem? (show ReferenceResiduals.block147[2]?=some panel164.right from rfl))⟩
theorem valid165 : ValidPanel panel165 := ⟨modelCheck165,residualCheck165,
  ReferenceTrajectory.leftBlock7_subset (List.mem_of_getElem? (show ReferenceResiduals.block7[5]?=some panel165.left from rfl)),
  ReferenceTrajectory.rightBlock147_subset (List.mem_of_getElem? (show ReferenceResiduals.block147[1]?=some panel165.right from rfl))⟩
theorem valid166 : ValidPanel panel166 := ⟨modelCheck166,residualCheck166,
  ReferenceTrajectory.leftBlock7_subset (List.mem_of_getElem? (show ReferenceResiduals.block7[6]?=some panel166.left from rfl)),
  ReferenceTrajectory.rightBlock147_subset (List.mem_of_getElem? (show ReferenceResiduals.block147[0]?=some panel166.right from rfl))⟩
theorem valid167 : ValidPanel panel167 := ⟨modelCheck167,residualCheck167,
  ReferenceTrajectory.leftBlock7_subset (List.mem_of_getElem? (show ReferenceResiduals.block7[7]?=some panel167.left from rfl)),
  ReferenceTrajectory.rightBlock146_subset (List.mem_of_getElem? (show ReferenceResiduals.block146[15]?=some panel167.right from rfl))⟩
theorem valid168 : ValidPanel panel168 := ⟨modelCheck168,residualCheck168,
  ReferenceTrajectory.leftBlock7_subset (List.mem_of_getElem? (show ReferenceResiduals.block7[8]?=some panel168.left from rfl)),
  ReferenceTrajectory.rightBlock146_subset (List.mem_of_getElem? (show ReferenceResiduals.block146[14]?=some panel168.right from rfl))⟩
theorem valid169 : ValidPanel panel169 := ⟨modelCheck169,residualCheck169,
  ReferenceTrajectory.leftBlock7_subset (List.mem_of_getElem? (show ReferenceResiduals.block7[9]?=some panel169.left from rfl)),
  ReferenceTrajectory.rightBlock146_subset (List.mem_of_getElem? (show ReferenceResiduals.block146[13]?=some panel169.right from rfl))⟩
theorem valid170 : ValidPanel panel170 := ⟨modelCheck170,residualCheck170,
  ReferenceTrajectory.leftBlock7_subset (List.mem_of_getElem? (show ReferenceResiduals.block7[10]?=some panel170.left from rfl)),
  ReferenceTrajectory.rightBlock146_subset (List.mem_of_getElem? (show ReferenceResiduals.block146[12]?=some panel170.right from rfl))⟩
theorem valid171 : ValidPanel panel171 := ⟨modelCheck171,residualCheck171,
  ReferenceTrajectory.leftBlock7_subset (List.mem_of_getElem? (show ReferenceResiduals.block7[11]?=some panel171.left from rfl)),
  ReferenceTrajectory.rightBlock146_subset (List.mem_of_getElem? (show ReferenceResiduals.block146[11]?=some panel171.right from rfl))⟩
theorem valid172 : ValidPanel panel172 := ⟨modelCheck172,residualCheck172,
  ReferenceTrajectory.leftBlock7_subset (List.mem_of_getElem? (show ReferenceResiduals.block7[12]?=some panel172.left from rfl)),
  ReferenceTrajectory.rightBlock146_subset (List.mem_of_getElem? (show ReferenceResiduals.block146[10]?=some panel172.right from rfl))⟩
theorem valid173 : ValidPanel panel173 := ⟨modelCheck173,residualCheck173,
  ReferenceTrajectory.leftBlock7_subset (List.mem_of_getElem? (show ReferenceResiduals.block7[13]?=some panel173.left from rfl)),
  ReferenceTrajectory.rightBlock146_subset (List.mem_of_getElem? (show ReferenceResiduals.block146[9]?=some panel173.right from rfl))⟩
theorem valid174 : ValidPanel panel174 := ⟨modelCheck174,residualCheck174,
  ReferenceTrajectory.leftBlock7_subset (List.mem_of_getElem? (show ReferenceResiduals.block7[14]?=some panel174.left from rfl)),
  ReferenceTrajectory.rightBlock146_subset (List.mem_of_getElem? (show ReferenceResiduals.block146[8]?=some panel174.right from rfl))⟩
theorem valid175 : ValidPanel panel175 := ⟨modelCheck175,residualCheck175,
  ReferenceTrajectory.leftBlock7_subset (List.mem_of_getElem? (show ReferenceResiduals.block7[15]?=some panel175.left from rfl)),
  ReferenceTrajectory.rightBlock146_subset (List.mem_of_getElem? (show ReferenceResiduals.block146[7]?=some panel175.right from rfl))⟩
theorem valid176 : ValidPanel panel176 := ⟨modelCheck176,residualCheck176,
  ReferenceTrajectory.leftBlock8_subset (List.mem_of_getElem? (show ReferenceResiduals.block8[0]?=some panel176.left from rfl)),
  ReferenceTrajectory.rightBlock146_subset (List.mem_of_getElem? (show ReferenceResiduals.block146[6]?=some panel176.right from rfl))⟩
theorem valid177 : ValidPanel panel177 := ⟨modelCheck177,residualCheck177,
  ReferenceTrajectory.leftBlock8_subset (List.mem_of_getElem? (show ReferenceResiduals.block8[1]?=some panel177.left from rfl)),
  ReferenceTrajectory.rightBlock146_subset (List.mem_of_getElem? (show ReferenceResiduals.block146[5]?=some panel177.right from rfl))⟩
theorem valid178 : ValidPanel panel178 := ⟨modelCheck178,residualCheck178,
  ReferenceTrajectory.leftBlock8_subset (List.mem_of_getElem? (show ReferenceResiduals.block8[2]?=some panel178.left from rfl)),
  ReferenceTrajectory.rightBlock146_subset (List.mem_of_getElem? (show ReferenceResiduals.block146[4]?=some panel178.right from rfl))⟩
theorem valid179 : ValidPanel panel179 := ⟨modelCheck179,residualCheck179,
  ReferenceTrajectory.leftBlock8_subset (List.mem_of_getElem? (show ReferenceResiduals.block8[3]?=some panel179.left from rfl)),
  ReferenceTrajectory.rightBlock146_subset (List.mem_of_getElem? (show ReferenceResiduals.block146[3]?=some panel179.right from rfl))⟩
theorem valid180 : ValidPanel panel180 := ⟨modelCheck180,residualCheck180,
  ReferenceTrajectory.leftBlock8_subset (List.mem_of_getElem? (show ReferenceResiduals.block8[4]?=some panel180.left from rfl)),
  ReferenceTrajectory.rightBlock146_subset (List.mem_of_getElem? (show ReferenceResiduals.block146[2]?=some panel180.right from rfl))⟩
theorem valid181 : ValidPanel panel181 := ⟨modelCheck181,residualCheck181,
  ReferenceTrajectory.leftBlock8_subset (List.mem_of_getElem? (show ReferenceResiduals.block8[5]?=some panel181.left from rfl)),
  ReferenceTrajectory.rightBlock146_subset (List.mem_of_getElem? (show ReferenceResiduals.block146[1]?=some panel181.right from rfl))⟩
theorem valid182 : ValidPanel panel182 := ⟨modelCheck182,residualCheck182,
  ReferenceTrajectory.leftBlock8_subset (List.mem_of_getElem? (show ReferenceResiduals.block8[6]?=some panel182.left from rfl)),
  ReferenceTrajectory.rightBlock146_subset (List.mem_of_getElem? (show ReferenceResiduals.block146[0]?=some panel182.right from rfl))⟩
theorem valid183 : ValidPanel panel183 := ⟨modelCheck183,residualCheck183,
  ReferenceTrajectory.leftBlock8_subset (List.mem_of_getElem? (show ReferenceResiduals.block8[7]?=some panel183.left from rfl)),
  ReferenceTrajectory.rightBlock145_subset (List.mem_of_getElem? (show ReferenceResiduals.block145[15]?=some panel183.right from rfl))⟩
theorem valid184 : ValidPanel panel184 := ⟨modelCheck184,residualCheck184,
  ReferenceTrajectory.leftBlock8_subset (List.mem_of_getElem? (show ReferenceResiduals.block8[8]?=some panel184.left from rfl)),
  ReferenceTrajectory.rightBlock145_subset (List.mem_of_getElem? (show ReferenceResiduals.block145[14]?=some panel184.right from rfl))⟩
theorem valid185 : ValidPanel panel185 := ⟨modelCheck185,residualCheck185,
  ReferenceTrajectory.leftBlock8_subset (List.mem_of_getElem? (show ReferenceResiduals.block8[9]?=some panel185.left from rfl)),
  ReferenceTrajectory.rightBlock145_subset (List.mem_of_getElem? (show ReferenceResiduals.block145[13]?=some panel185.right from rfl))⟩
theorem valid186 : ValidPanel panel186 := ⟨modelCheck186,residualCheck186,
  ReferenceTrajectory.leftBlock8_subset (List.mem_of_getElem? (show ReferenceResiduals.block8[10]?=some panel186.left from rfl)),
  ReferenceTrajectory.rightBlock145_subset (List.mem_of_getElem? (show ReferenceResiduals.block145[12]?=some panel186.right from rfl))⟩
theorem valid187 : ValidPanel panel187 := ⟨modelCheck187,residualCheck187,
  ReferenceTrajectory.leftBlock8_subset (List.mem_of_getElem? (show ReferenceResiduals.block8[11]?=some panel187.left from rfl)),
  ReferenceTrajectory.rightBlock145_subset (List.mem_of_getElem? (show ReferenceResiduals.block145[11]?=some panel187.right from rfl))⟩
theorem valid188 : ValidPanel panel188 := ⟨modelCheck188,residualCheck188,
  ReferenceTrajectory.leftBlock8_subset (List.mem_of_getElem? (show ReferenceResiduals.block8[12]?=some panel188.left from rfl)),
  ReferenceTrajectory.rightBlock145_subset (List.mem_of_getElem? (show ReferenceResiduals.block145[10]?=some panel188.right from rfl))⟩
theorem valid189 : ValidPanel panel189 := ⟨modelCheck189,residualCheck189,
  ReferenceTrajectory.leftBlock8_subset (List.mem_of_getElem? (show ReferenceResiduals.block8[13]?=some panel189.left from rfl)),
  ReferenceTrajectory.rightBlock145_subset (List.mem_of_getElem? (show ReferenceResiduals.block145[9]?=some panel189.right from rfl))⟩
theorem valid190 : ValidPanel panel190 := ⟨modelCheck190,residualCheck190,
  ReferenceTrajectory.leftBlock8_subset (List.mem_of_getElem? (show ReferenceResiduals.block8[14]?=some panel190.left from rfl)),
  ReferenceTrajectory.rightBlock145_subset (List.mem_of_getElem? (show ReferenceResiduals.block145[8]?=some panel190.right from rfl))⟩
theorem valid191 : ValidPanel panel191 := ⟨modelCheck191,residualCheck191,
  ReferenceTrajectory.leftBlock8_subset (List.mem_of_getElem? (show ReferenceResiduals.block8[15]?=some panel191.left from rfl)),
  ReferenceTrajectory.rightBlock145_subset (List.mem_of_getElem? (show ReferenceResiduals.block145[7]?=some panel191.right from rfl))⟩
theorem validBlock5 : ∀ p∈block5,ValidPanel p := by
  simp only [block5,List.forall_mem_cons]
  exact ⟨valid160,⟨valid161,⟨valid162,⟨valid163,⟨valid164,⟨valid165,⟨valid166,⟨valid167,⟨valid168,⟨valid169,⟨valid170,⟨valid171,⟨valid172,⟨valid173,⟨valid174,⟨valid175,⟨valid176,⟨valid177,⟨valid178,⟨valid179,⟨valid180,⟨valid181,⟨valid182,⟨valid183,⟨valid184,⟨valid185,⟨valid186,⟨valid187,⟨valid188,⟨valid189,⟨valid190,⟨valid191,(by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end «2610.05164v2».Certificates.Compact.ContactValues

import «2610.05164v2».Certificates.Compact.ContactBatches.Batch006
import «2610.05164v2».Certificates.Compact.ContactCoverage
import «2610.05164v2».Certificates.Compact.ReferenceTrajectoryIndex

/-!
Article: 2610.05164v2, Section 4.1.
Correspondence006.
Use: `«2610.05164v2».Certificates.Compact.ContactValues.validBlock6` feeds
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
theorem valid192 : ValidPanel panel192 := ⟨modelCheck192,residualCheck192,
  ReferenceTrajectory.leftBlock9_subset (List.mem_of_getElem? (show ReferenceResiduals.block9[0]?=some panel192.left from rfl)),
  ReferenceTrajectory.rightBlock145_subset (List.mem_of_getElem? (show ReferenceResiduals.block145[6]?=some panel192.right from rfl))⟩
theorem valid193 : ValidPanel panel193 := ⟨modelCheck193,residualCheck193,
  ReferenceTrajectory.leftBlock9_subset (List.mem_of_getElem? (show ReferenceResiduals.block9[1]?=some panel193.left from rfl)),
  ReferenceTrajectory.rightBlock145_subset (List.mem_of_getElem? (show ReferenceResiduals.block145[5]?=some panel193.right from rfl))⟩
theorem valid194 : ValidPanel panel194 := ⟨modelCheck194,residualCheck194,
  ReferenceTrajectory.leftBlock9_subset (List.mem_of_getElem? (show ReferenceResiduals.block9[2]?=some panel194.left from rfl)),
  ReferenceTrajectory.rightBlock145_subset (List.mem_of_getElem? (show ReferenceResiduals.block145[4]?=some panel194.right from rfl))⟩
theorem valid195 : ValidPanel panel195 := ⟨modelCheck195,residualCheck195,
  ReferenceTrajectory.leftBlock9_subset (List.mem_of_getElem? (show ReferenceResiduals.block9[3]?=some panel195.left from rfl)),
  ReferenceTrajectory.rightBlock145_subset (List.mem_of_getElem? (show ReferenceResiduals.block145[3]?=some panel195.right from rfl))⟩
theorem valid196 : ValidPanel panel196 := ⟨modelCheck196,residualCheck196,
  ReferenceTrajectory.leftBlock9_subset (List.mem_of_getElem? (show ReferenceResiduals.block9[4]?=some panel196.left from rfl)),
  ReferenceTrajectory.rightBlock145_subset (List.mem_of_getElem? (show ReferenceResiduals.block145[2]?=some panel196.right from rfl))⟩
theorem valid197 : ValidPanel panel197 := ⟨modelCheck197,residualCheck197,
  ReferenceTrajectory.leftBlock9_subset (List.mem_of_getElem? (show ReferenceResiduals.block9[5]?=some panel197.left from rfl)),
  ReferenceTrajectory.rightBlock145_subset (List.mem_of_getElem? (show ReferenceResiduals.block145[1]?=some panel197.right from rfl))⟩
theorem valid198 : ValidPanel panel198 := ⟨modelCheck198,residualCheck198,
  ReferenceTrajectory.leftBlock9_subset (List.mem_of_getElem? (show ReferenceResiduals.block9[6]?=some panel198.left from rfl)),
  ReferenceTrajectory.rightBlock145_subset (List.mem_of_getElem? (show ReferenceResiduals.block145[0]?=some panel198.right from rfl))⟩
theorem valid199 : ValidPanel panel199 := ⟨modelCheck199,residualCheck199,
  ReferenceTrajectory.leftBlock9_subset (List.mem_of_getElem? (show ReferenceResiduals.block9[7]?=some panel199.left from rfl)),
  ReferenceTrajectory.rightBlock144_subset (List.mem_of_getElem? (show ReferenceResiduals.block144[15]?=some panel199.right from rfl))⟩
theorem valid200 : ValidPanel panel200 := ⟨modelCheck200,residualCheck200,
  ReferenceTrajectory.leftBlock9_subset (List.mem_of_getElem? (show ReferenceResiduals.block9[8]?=some panel200.left from rfl)),
  ReferenceTrajectory.rightBlock144_subset (List.mem_of_getElem? (show ReferenceResiduals.block144[14]?=some panel200.right from rfl))⟩
theorem valid201 : ValidPanel panel201 := ⟨modelCheck201,residualCheck201,
  ReferenceTrajectory.leftBlock9_subset (List.mem_of_getElem? (show ReferenceResiduals.block9[9]?=some panel201.left from rfl)),
  ReferenceTrajectory.rightBlock144_subset (List.mem_of_getElem? (show ReferenceResiduals.block144[13]?=some panel201.right from rfl))⟩
theorem valid202 : ValidPanel panel202 := ⟨modelCheck202,residualCheck202,
  ReferenceTrajectory.leftBlock9_subset (List.mem_of_getElem? (show ReferenceResiduals.block9[10]?=some panel202.left from rfl)),
  ReferenceTrajectory.rightBlock144_subset (List.mem_of_getElem? (show ReferenceResiduals.block144[12]?=some panel202.right from rfl))⟩
theorem valid203 : ValidPanel panel203 := ⟨modelCheck203,residualCheck203,
  ReferenceTrajectory.leftBlock9_subset (List.mem_of_getElem? (show ReferenceResiduals.block9[11]?=some panel203.left from rfl)),
  ReferenceTrajectory.rightBlock144_subset (List.mem_of_getElem? (show ReferenceResiduals.block144[11]?=some panel203.right from rfl))⟩
theorem valid204 : ValidPanel panel204 := ⟨modelCheck204,residualCheck204,
  ReferenceTrajectory.leftBlock9_subset (List.mem_of_getElem? (show ReferenceResiduals.block9[12]?=some panel204.left from rfl)),
  ReferenceTrajectory.rightBlock144_subset (List.mem_of_getElem? (show ReferenceResiduals.block144[10]?=some panel204.right from rfl))⟩
theorem valid205 : ValidPanel panel205 := ⟨modelCheck205,residualCheck205,
  ReferenceTrajectory.leftBlock9_subset (List.mem_of_getElem? (show ReferenceResiduals.block9[13]?=some panel205.left from rfl)),
  ReferenceTrajectory.rightBlock144_subset (List.mem_of_getElem? (show ReferenceResiduals.block144[9]?=some panel205.right from rfl))⟩
theorem valid206 : ValidPanel panel206 := ⟨modelCheck206,residualCheck206,
  ReferenceTrajectory.leftBlock9_subset (List.mem_of_getElem? (show ReferenceResiduals.block9[14]?=some panel206.left from rfl)),
  ReferenceTrajectory.rightBlock144_subset (List.mem_of_getElem? (show ReferenceResiduals.block144[8]?=some panel206.right from rfl))⟩
theorem valid207 : ValidPanel panel207 := ⟨modelCheck207,residualCheck207,
  ReferenceTrajectory.leftBlock9_subset (List.mem_of_getElem? (show ReferenceResiduals.block9[15]?=some panel207.left from rfl)),
  ReferenceTrajectory.rightBlock144_subset (List.mem_of_getElem? (show ReferenceResiduals.block144[7]?=some panel207.right from rfl))⟩
theorem valid208 : ValidPanel panel208 := ⟨modelCheck208,residualCheck208,
  ReferenceTrajectory.leftBlock10_subset (List.mem_of_getElem? (show ReferenceResiduals.block10[0]?=some panel208.left from rfl)),
  ReferenceTrajectory.rightBlock144_subset (List.mem_of_getElem? (show ReferenceResiduals.block144[6]?=some panel208.right from rfl))⟩
theorem valid209 : ValidPanel panel209 := ⟨modelCheck209,residualCheck209,
  ReferenceTrajectory.leftBlock10_subset (List.mem_of_getElem? (show ReferenceResiduals.block10[1]?=some panel209.left from rfl)),
  ReferenceTrajectory.rightBlock144_subset (List.mem_of_getElem? (show ReferenceResiduals.block144[5]?=some panel209.right from rfl))⟩
theorem valid210 : ValidPanel panel210 := ⟨modelCheck210,residualCheck210,
  ReferenceTrajectory.leftBlock10_subset (List.mem_of_getElem? (show ReferenceResiduals.block10[2]?=some panel210.left from rfl)),
  ReferenceTrajectory.rightBlock144_subset (List.mem_of_getElem? (show ReferenceResiduals.block144[4]?=some panel210.right from rfl))⟩
theorem valid211 : ValidPanel panel211 := ⟨modelCheck211,residualCheck211,
  ReferenceTrajectory.leftBlock10_subset (List.mem_of_getElem? (show ReferenceResiduals.block10[3]?=some panel211.left from rfl)),
  ReferenceTrajectory.rightBlock144_subset (List.mem_of_getElem? (show ReferenceResiduals.block144[3]?=some panel211.right from rfl))⟩
theorem valid212 : ValidPanel panel212 := ⟨modelCheck212,residualCheck212,
  ReferenceTrajectory.leftBlock10_subset (List.mem_of_getElem? (show ReferenceResiduals.block10[4]?=some panel212.left from rfl)),
  ReferenceTrajectory.rightBlock144_subset (List.mem_of_getElem? (show ReferenceResiduals.block144[2]?=some panel212.right from rfl))⟩
theorem valid213 : ValidPanel panel213 := ⟨modelCheck213,residualCheck213,
  ReferenceTrajectory.leftBlock10_subset (List.mem_of_getElem? (show ReferenceResiduals.block10[5]?=some panel213.left from rfl)),
  ReferenceTrajectory.rightBlock144_subset (List.mem_of_getElem? (show ReferenceResiduals.block144[1]?=some panel213.right from rfl))⟩
theorem valid214 : ValidPanel panel214 := ⟨modelCheck214,residualCheck214,
  ReferenceTrajectory.leftBlock10_subset (List.mem_of_getElem? (show ReferenceResiduals.block10[6]?=some panel214.left from rfl)),
  ReferenceTrajectory.rightBlock144_subset (List.mem_of_getElem? (show ReferenceResiduals.block144[0]?=some panel214.right from rfl))⟩
theorem valid215 : ValidPanel panel215 := ⟨modelCheck215,residualCheck215,
  ReferenceTrajectory.leftBlock10_subset (List.mem_of_getElem? (show ReferenceResiduals.block10[7]?=some panel215.left from rfl)),
  ReferenceTrajectory.rightBlock143_subset (List.mem_of_getElem? (show ReferenceResiduals.block143[15]?=some panel215.right from rfl))⟩
theorem valid216 : ValidPanel panel216 := ⟨modelCheck216,residualCheck216,
  ReferenceTrajectory.leftBlock10_subset (List.mem_of_getElem? (show ReferenceResiduals.block10[8]?=some panel216.left from rfl)),
  ReferenceTrajectory.rightBlock143_subset (List.mem_of_getElem? (show ReferenceResiduals.block143[14]?=some panel216.right from rfl))⟩
theorem valid217 : ValidPanel panel217 := ⟨modelCheck217,residualCheck217,
  ReferenceTrajectory.leftBlock10_subset (List.mem_of_getElem? (show ReferenceResiduals.block10[9]?=some panel217.left from rfl)),
  ReferenceTrajectory.rightBlock143_subset (List.mem_of_getElem? (show ReferenceResiduals.block143[13]?=some panel217.right from rfl))⟩
theorem valid218 : ValidPanel panel218 := ⟨modelCheck218,residualCheck218,
  ReferenceTrajectory.leftBlock10_subset (List.mem_of_getElem? (show ReferenceResiduals.block10[10]?=some panel218.left from rfl)),
  ReferenceTrajectory.rightBlock143_subset (List.mem_of_getElem? (show ReferenceResiduals.block143[12]?=some panel218.right from rfl))⟩
theorem valid219 : ValidPanel panel219 := ⟨modelCheck219,residualCheck219,
  ReferenceTrajectory.leftBlock10_subset (List.mem_of_getElem? (show ReferenceResiduals.block10[11]?=some panel219.left from rfl)),
  ReferenceTrajectory.rightBlock143_subset (List.mem_of_getElem? (show ReferenceResiduals.block143[11]?=some panel219.right from rfl))⟩
theorem valid220 : ValidPanel panel220 := ⟨modelCheck220,residualCheck220,
  ReferenceTrajectory.leftBlock10_subset (List.mem_of_getElem? (show ReferenceResiduals.block10[12]?=some panel220.left from rfl)),
  ReferenceTrajectory.rightBlock143_subset (List.mem_of_getElem? (show ReferenceResiduals.block143[10]?=some panel220.right from rfl))⟩
theorem valid221 : ValidPanel panel221 := ⟨modelCheck221,residualCheck221,
  ReferenceTrajectory.leftBlock10_subset (List.mem_of_getElem? (show ReferenceResiduals.block10[13]?=some panel221.left from rfl)),
  ReferenceTrajectory.rightBlock143_subset (List.mem_of_getElem? (show ReferenceResiduals.block143[9]?=some panel221.right from rfl))⟩
theorem valid222 : ValidPanel panel222 := ⟨modelCheck222,residualCheck222,
  ReferenceTrajectory.leftBlock10_subset (List.mem_of_getElem? (show ReferenceResiduals.block10[14]?=some panel222.left from rfl)),
  ReferenceTrajectory.rightBlock143_subset (List.mem_of_getElem? (show ReferenceResiduals.block143[8]?=some panel222.right from rfl))⟩
theorem valid223 : ValidPanel panel223 := ⟨modelCheck223,residualCheck223,
  ReferenceTrajectory.leftBlock10_subset (List.mem_of_getElem? (show ReferenceResiduals.block10[15]?=some panel223.left from rfl)),
  ReferenceTrajectory.rightBlock143_subset (List.mem_of_getElem? (show ReferenceResiduals.block143[7]?=some panel223.right from rfl))⟩
theorem validBlock6 : ∀ p∈block6,ValidPanel p := by
  simp only [block6,List.forall_mem_cons]
  exact ⟨valid192,⟨valid193,⟨valid194,⟨valid195,⟨valid196,⟨valid197,⟨valid198,⟨valid199,⟨valid200,⟨valid201,⟨valid202,⟨valid203,⟨valid204,⟨valid205,⟨valid206,⟨valid207,⟨valid208,⟨valid209,⟨valid210,⟨valid211,⟨valid212,⟨valid213,⟨valid214,⟨valid215,⟨valid216,⟨valid217,⟨valid218,⟨valid219,⟨valid220,⟨valid221,⟨valid222,⟨valid223,(by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end «2610.05164v2».Certificates.Compact.ContactValues

import «2610.05164v2».Certificates.Compact.ContactBatches.Batch030
import «2610.05164v2».Certificates.Compact.ContactCoverage
import «2610.05164v2».Certificates.Compact.ReferenceTrajectoryIndex

/-!
Article: 2610.05164v2, Section 4.1.
Correspondence030.
Use: `«2610.05164v2».Certificates.Compact.ContactValues.validBlock30` feeds
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
theorem valid960 : ValidPanel panel960 := ⟨modelCheck960,residualCheck960,
  ReferenceTrajectory.leftBlock56_subset (List.mem_of_getElem? (show ReferenceResiduals.block56[1]?=some panel960.left from rfl)),
  ReferenceTrajectory.rightBlock97_subset (List.mem_of_getElem? (show ReferenceResiduals.block97[6]?=some panel960.right from rfl))⟩
theorem valid961 : ValidPanel panel961 := ⟨modelCheck961,residualCheck961,
  ReferenceTrajectory.leftBlock56_subset (List.mem_of_getElem? (show ReferenceResiduals.block56[2]?=some panel961.left from rfl)),
  ReferenceTrajectory.rightBlock97_subset (List.mem_of_getElem? (show ReferenceResiduals.block97[5]?=some panel961.right from rfl))⟩
theorem valid962 : ValidPanel panel962 := ⟨modelCheck962,residualCheck962,
  ReferenceTrajectory.leftBlock56_subset (List.mem_of_getElem? (show ReferenceResiduals.block56[3]?=some panel962.left from rfl)),
  ReferenceTrajectory.rightBlock97_subset (List.mem_of_getElem? (show ReferenceResiduals.block97[4]?=some panel962.right from rfl))⟩
theorem valid963 : ValidPanel panel963 := ⟨modelCheck963,residualCheck963,
  ReferenceTrajectory.leftBlock56_subset (List.mem_of_getElem? (show ReferenceResiduals.block56[4]?=some panel963.left from rfl)),
  ReferenceTrajectory.rightBlock97_subset (List.mem_of_getElem? (show ReferenceResiduals.block97[3]?=some panel963.right from rfl))⟩
theorem valid964 : ValidPanel panel964 := ⟨modelCheck964,residualCheck964,
  ReferenceTrajectory.leftBlock56_subset (List.mem_of_getElem? (show ReferenceResiduals.block56[5]?=some panel964.left from rfl)),
  ReferenceTrajectory.rightBlock97_subset (List.mem_of_getElem? (show ReferenceResiduals.block97[2]?=some panel964.right from rfl))⟩
theorem valid965 : ValidPanel panel965 := ⟨modelCheck965,residualCheck965,
  ReferenceTrajectory.leftBlock56_subset (List.mem_of_getElem? (show ReferenceResiduals.block56[6]?=some panel965.left from rfl)),
  ReferenceTrajectory.rightBlock97_subset (List.mem_of_getElem? (show ReferenceResiduals.block97[1]?=some panel965.right from rfl))⟩
theorem valid966 : ValidPanel panel966 := ⟨modelCheck966,residualCheck966,
  ReferenceTrajectory.leftBlock56_subset (List.mem_of_getElem? (show ReferenceResiduals.block56[7]?=some panel966.left from rfl)),
  ReferenceTrajectory.rightBlock97_subset (List.mem_of_getElem? (show ReferenceResiduals.block97[0]?=some panel966.right from rfl))⟩
theorem valid967 : ValidPanel panel967 := ⟨modelCheck967,residualCheck967,
  ReferenceTrajectory.leftBlock56_subset (List.mem_of_getElem? (show ReferenceResiduals.block56[8]?=some panel967.left from rfl)),
  ReferenceTrajectory.rightBlock96_subset (List.mem_of_getElem? (show ReferenceResiduals.block96[15]?=some panel967.right from rfl))⟩
theorem valid968 : ValidPanel panel968 := ⟨modelCheck968,residualCheck968,
  ReferenceTrajectory.leftBlock56_subset (List.mem_of_getElem? (show ReferenceResiduals.block56[9]?=some panel968.left from rfl)),
  ReferenceTrajectory.rightBlock96_subset (List.mem_of_getElem? (show ReferenceResiduals.block96[14]?=some panel968.right from rfl))⟩
theorem valid969 : ValidPanel panel969 := ⟨modelCheck969,residualCheck969,
  ReferenceTrajectory.leftBlock56_subset (List.mem_of_getElem? (show ReferenceResiduals.block56[10]?=some panel969.left from rfl)),
  ReferenceTrajectory.rightBlock96_subset (List.mem_of_getElem? (show ReferenceResiduals.block96[13]?=some panel969.right from rfl))⟩
theorem valid970 : ValidPanel panel970 := ⟨modelCheck970,residualCheck970,
  ReferenceTrajectory.leftBlock56_subset (List.mem_of_getElem? (show ReferenceResiduals.block56[11]?=some panel970.left from rfl)),
  ReferenceTrajectory.rightBlock96_subset (List.mem_of_getElem? (show ReferenceResiduals.block96[12]?=some panel970.right from rfl))⟩
theorem valid971 : ValidPanel panel971 := ⟨modelCheck971,residualCheck971,
  ReferenceTrajectory.leftBlock56_subset (List.mem_of_getElem? (show ReferenceResiduals.block56[12]?=some panel971.left from rfl)),
  ReferenceTrajectory.rightBlock96_subset (List.mem_of_getElem? (show ReferenceResiduals.block96[11]?=some panel971.right from rfl))⟩
theorem valid972 : ValidPanel panel972 := ⟨modelCheck972,residualCheck972,
  ReferenceTrajectory.leftBlock56_subset (List.mem_of_getElem? (show ReferenceResiduals.block56[13]?=some panel972.left from rfl)),
  ReferenceTrajectory.rightBlock96_subset (List.mem_of_getElem? (show ReferenceResiduals.block96[10]?=some panel972.right from rfl))⟩
theorem valid973 : ValidPanel panel973 := ⟨modelCheck973,residualCheck973,
  ReferenceTrajectory.leftBlock56_subset (List.mem_of_getElem? (show ReferenceResiduals.block56[14]?=some panel973.left from rfl)),
  ReferenceTrajectory.rightBlock96_subset (List.mem_of_getElem? (show ReferenceResiduals.block96[9]?=some panel973.right from rfl))⟩
theorem valid974 : ValidPanel panel974 := ⟨modelCheck974,residualCheck974,
  ReferenceTrajectory.leftBlock56_subset (List.mem_of_getElem? (show ReferenceResiduals.block56[15]?=some panel974.left from rfl)),
  ReferenceTrajectory.rightBlock96_subset (List.mem_of_getElem? (show ReferenceResiduals.block96[8]?=some panel974.right from rfl))⟩
theorem valid975 : ValidPanel panel975 := ⟨modelCheck975,residualCheck975,
  ReferenceTrajectory.leftBlock57_subset (List.mem_of_getElem? (show ReferenceResiduals.block57[0]?=some panel975.left from rfl)),
  ReferenceTrajectory.rightBlock96_subset (List.mem_of_getElem? (show ReferenceResiduals.block96[7]?=some panel975.right from rfl))⟩
theorem valid976 : ValidPanel panel976 := ⟨modelCheck976,residualCheck976,
  ReferenceTrajectory.leftBlock57_subset (List.mem_of_getElem? (show ReferenceResiduals.block57[1]?=some panel976.left from rfl)),
  ReferenceTrajectory.rightBlock96_subset (List.mem_of_getElem? (show ReferenceResiduals.block96[6]?=some panel976.right from rfl))⟩
theorem valid977 : ValidPanel panel977 := ⟨modelCheck977,residualCheck977,
  ReferenceTrajectory.leftBlock57_subset (List.mem_of_getElem? (show ReferenceResiduals.block57[2]?=some panel977.left from rfl)),
  ReferenceTrajectory.rightBlock96_subset (List.mem_of_getElem? (show ReferenceResiduals.block96[5]?=some panel977.right from rfl))⟩
theorem valid978 : ValidPanel panel978 := ⟨modelCheck978,residualCheck978,
  ReferenceTrajectory.leftBlock57_subset (List.mem_of_getElem? (show ReferenceResiduals.block57[3]?=some panel978.left from rfl)),
  ReferenceTrajectory.rightBlock96_subset (List.mem_of_getElem? (show ReferenceResiduals.block96[4]?=some panel978.right from rfl))⟩
theorem valid979 : ValidPanel panel979 := ⟨modelCheck979,residualCheck979,
  ReferenceTrajectory.leftBlock57_subset (List.mem_of_getElem? (show ReferenceResiduals.block57[4]?=some panel979.left from rfl)),
  ReferenceTrajectory.rightBlock96_subset (List.mem_of_getElem? (show ReferenceResiduals.block96[3]?=some panel979.right from rfl))⟩
theorem valid980 : ValidPanel panel980 := ⟨modelCheck980,residualCheck980,
  ReferenceTrajectory.leftBlock57_subset (List.mem_of_getElem? (show ReferenceResiduals.block57[5]?=some panel980.left from rfl)),
  ReferenceTrajectory.rightBlock96_subset (List.mem_of_getElem? (show ReferenceResiduals.block96[2]?=some panel980.right from rfl))⟩
theorem valid981 : ValidPanel panel981 := ⟨modelCheck981,residualCheck981,
  ReferenceTrajectory.leftBlock57_subset (List.mem_of_getElem? (show ReferenceResiduals.block57[6]?=some panel981.left from rfl)),
  ReferenceTrajectory.rightBlock96_subset (List.mem_of_getElem? (show ReferenceResiduals.block96[1]?=some panel981.right from rfl))⟩
theorem valid982 : ValidPanel panel982 := ⟨modelCheck982,residualCheck982,
  ReferenceTrajectory.leftBlock57_subset (List.mem_of_getElem? (show ReferenceResiduals.block57[7]?=some panel982.left from rfl)),
  ReferenceTrajectory.rightBlock96_subset (List.mem_of_getElem? (show ReferenceResiduals.block96[0]?=some panel982.right from rfl))⟩
theorem valid983 : ValidPanel panel983 := ⟨modelCheck983,residualCheck983,
  ReferenceTrajectory.leftBlock57_subset (List.mem_of_getElem? (show ReferenceResiduals.block57[8]?=some panel983.left from rfl)),
  ReferenceTrajectory.rightBlock95_subset (List.mem_of_getElem? (show ReferenceResiduals.block95[15]?=some panel983.right from rfl))⟩
theorem valid984 : ValidPanel panel984 := ⟨modelCheck984,residualCheck984,
  ReferenceTrajectory.leftBlock57_subset (List.mem_of_getElem? (show ReferenceResiduals.block57[9]?=some panel984.left from rfl)),
  ReferenceTrajectory.rightBlock95_subset (List.mem_of_getElem? (show ReferenceResiduals.block95[14]?=some panel984.right from rfl))⟩
theorem valid985 : ValidPanel panel985 := ⟨modelCheck985,residualCheck985,
  ReferenceTrajectory.leftBlock57_subset (List.mem_of_getElem? (show ReferenceResiduals.block57[10]?=some panel985.left from rfl)),
  ReferenceTrajectory.rightBlock95_subset (List.mem_of_getElem? (show ReferenceResiduals.block95[13]?=some panel985.right from rfl))⟩
theorem valid986 : ValidPanel panel986 := ⟨modelCheck986,residualCheck986,
  ReferenceTrajectory.leftBlock57_subset (List.mem_of_getElem? (show ReferenceResiduals.block57[11]?=some panel986.left from rfl)),
  ReferenceTrajectory.rightBlock95_subset (List.mem_of_getElem? (show ReferenceResiduals.block95[12]?=some panel986.right from rfl))⟩
theorem valid987 : ValidPanel panel987 := ⟨modelCheck987,residualCheck987,
  ReferenceTrajectory.leftBlock57_subset (List.mem_of_getElem? (show ReferenceResiduals.block57[12]?=some panel987.left from rfl)),
  ReferenceTrajectory.rightBlock95_subset (List.mem_of_getElem? (show ReferenceResiduals.block95[11]?=some panel987.right from rfl))⟩
theorem valid988 : ValidPanel panel988 := ⟨modelCheck988,residualCheck988,
  ReferenceTrajectory.leftBlock57_subset (List.mem_of_getElem? (show ReferenceResiduals.block57[13]?=some panel988.left from rfl)),
  ReferenceTrajectory.rightBlock95_subset (List.mem_of_getElem? (show ReferenceResiduals.block95[10]?=some panel988.right from rfl))⟩
theorem valid989 : ValidPanel panel989 := ⟨modelCheck989,residualCheck989,
  ReferenceTrajectory.leftBlock57_subset (List.mem_of_getElem? (show ReferenceResiduals.block57[14]?=some panel989.left from rfl)),
  ReferenceTrajectory.rightBlock95_subset (List.mem_of_getElem? (show ReferenceResiduals.block95[9]?=some panel989.right from rfl))⟩
theorem valid990 : ValidPanel panel990 := ⟨modelCheck990,residualCheck990,
  ReferenceTrajectory.leftBlock57_subset (List.mem_of_getElem? (show ReferenceResiduals.block57[15]?=some panel990.left from rfl)),
  ReferenceTrajectory.rightBlock95_subset (List.mem_of_getElem? (show ReferenceResiduals.block95[8]?=some panel990.right from rfl))⟩
theorem valid991 : ValidPanel panel991 := ⟨modelCheck991,residualCheck991,
  ReferenceTrajectory.leftBlock58_subset (List.mem_of_getElem? (show ReferenceResiduals.block58[0]?=some panel991.left from rfl)),
  ReferenceTrajectory.rightBlock95_subset (List.mem_of_getElem? (show ReferenceResiduals.block95[7]?=some panel991.right from rfl))⟩
theorem validBlock30 : ∀ p∈block30,ValidPanel p := by
  simp only [block30,List.forall_mem_cons]
  exact ⟨valid960,⟨valid961,⟨valid962,⟨valid963,⟨valid964,⟨valid965,⟨valid966,⟨valid967,⟨valid968,⟨valid969,⟨valid970,⟨valid971,⟨valid972,⟨valid973,⟨valid974,⟨valid975,⟨valid976,⟨valid977,⟨valid978,⟨valid979,⟨valid980,⟨valid981,⟨valid982,⟨valid983,⟨valid984,⟨valid985,⟨valid986,⟨valid987,⟨valid988,⟨valid989,⟨valid990,⟨valid991,(by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end «2610.05164v2».Certificates.Compact.ContactValues

import chebyshev2.Certificates.Compact.ContactBatches.Batch008
import chebyshev2.Certificates.Compact.ContactCoverage
import chebyshev2.Certificates.Compact.ReferenceTrajectoryIndex

/-!
Article: chebyshev2, Section 4.1.
Correspondence008.
Use: `chebyshev2.Certificates.Compact.ContactValues.validBlock8` feeds
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
theorem valid256 : ValidPanel panel256 := ⟨modelCheck256,residualCheck256,
  ReferenceTrajectory.leftBlock13_subset (List.mem_of_getElem? (show ReferenceResiduals.block13[0]?=some panel256.left from rfl)),
  ReferenceTrajectory.rightBlock141_subset (List.mem_of_getElem? (show ReferenceResiduals.block141[6]?=some panel256.right from rfl))⟩
theorem valid257 : ValidPanel panel257 := ⟨modelCheck257,residualCheck257,
  ReferenceTrajectory.leftBlock13_subset (List.mem_of_getElem? (show ReferenceResiduals.block13[1]?=some panel257.left from rfl)),
  ReferenceTrajectory.rightBlock141_subset (List.mem_of_getElem? (show ReferenceResiduals.block141[5]?=some panel257.right from rfl))⟩
theorem valid258 : ValidPanel panel258 := ⟨modelCheck258,residualCheck258,
  ReferenceTrajectory.leftBlock13_subset (List.mem_of_getElem? (show ReferenceResiduals.block13[2]?=some panel258.left from rfl)),
  ReferenceTrajectory.rightBlock141_subset (List.mem_of_getElem? (show ReferenceResiduals.block141[4]?=some panel258.right from rfl))⟩
theorem valid259 : ValidPanel panel259 := ⟨modelCheck259,residualCheck259,
  ReferenceTrajectory.leftBlock13_subset (List.mem_of_getElem? (show ReferenceResiduals.block13[3]?=some panel259.left from rfl)),
  ReferenceTrajectory.rightBlock141_subset (List.mem_of_getElem? (show ReferenceResiduals.block141[3]?=some panel259.right from rfl))⟩
theorem valid260 : ValidPanel panel260 := ⟨modelCheck260,residualCheck260,
  ReferenceTrajectory.leftBlock13_subset (List.mem_of_getElem? (show ReferenceResiduals.block13[4]?=some panel260.left from rfl)),
  ReferenceTrajectory.rightBlock141_subset (List.mem_of_getElem? (show ReferenceResiduals.block141[2]?=some panel260.right from rfl))⟩
theorem valid261 : ValidPanel panel261 := ⟨modelCheck261,residualCheck261,
  ReferenceTrajectory.leftBlock13_subset (List.mem_of_getElem? (show ReferenceResiduals.block13[5]?=some panel261.left from rfl)),
  ReferenceTrajectory.rightBlock141_subset (List.mem_of_getElem? (show ReferenceResiduals.block141[1]?=some panel261.right from rfl))⟩
theorem valid262 : ValidPanel panel262 := ⟨modelCheck262,residualCheck262,
  ReferenceTrajectory.leftBlock13_subset (List.mem_of_getElem? (show ReferenceResiduals.block13[6]?=some panel262.left from rfl)),
  ReferenceTrajectory.rightBlock141_subset (List.mem_of_getElem? (show ReferenceResiduals.block141[0]?=some panel262.right from rfl))⟩
theorem valid263 : ValidPanel panel263 := ⟨modelCheck263,residualCheck263,
  ReferenceTrajectory.leftBlock13_subset (List.mem_of_getElem? (show ReferenceResiduals.block13[7]?=some panel263.left from rfl)),
  ReferenceTrajectory.rightBlock140_subset (List.mem_of_getElem? (show ReferenceResiduals.block140[15]?=some panel263.right from rfl))⟩
theorem valid264 : ValidPanel panel264 := ⟨modelCheck264,residualCheck264,
  ReferenceTrajectory.leftBlock13_subset (List.mem_of_getElem? (show ReferenceResiduals.block13[8]?=some panel264.left from rfl)),
  ReferenceTrajectory.rightBlock140_subset (List.mem_of_getElem? (show ReferenceResiduals.block140[14]?=some panel264.right from rfl))⟩
theorem valid265 : ValidPanel panel265 := ⟨modelCheck265,residualCheck265,
  ReferenceTrajectory.leftBlock13_subset (List.mem_of_getElem? (show ReferenceResiduals.block13[9]?=some panel265.left from rfl)),
  ReferenceTrajectory.rightBlock140_subset (List.mem_of_getElem? (show ReferenceResiduals.block140[13]?=some panel265.right from rfl))⟩
theorem valid266 : ValidPanel panel266 := ⟨modelCheck266,residualCheck266,
  ReferenceTrajectory.leftBlock13_subset (List.mem_of_getElem? (show ReferenceResiduals.block13[10]?=some panel266.left from rfl)),
  ReferenceTrajectory.rightBlock140_subset (List.mem_of_getElem? (show ReferenceResiduals.block140[12]?=some panel266.right from rfl))⟩
theorem valid267 : ValidPanel panel267 := ⟨modelCheck267,residualCheck267,
  ReferenceTrajectory.leftBlock13_subset (List.mem_of_getElem? (show ReferenceResiduals.block13[11]?=some panel267.left from rfl)),
  ReferenceTrajectory.rightBlock140_subset (List.mem_of_getElem? (show ReferenceResiduals.block140[11]?=some panel267.right from rfl))⟩
theorem valid268 : ValidPanel panel268 := ⟨modelCheck268,residualCheck268,
  ReferenceTrajectory.leftBlock13_subset (List.mem_of_getElem? (show ReferenceResiduals.block13[12]?=some panel268.left from rfl)),
  ReferenceTrajectory.rightBlock140_subset (List.mem_of_getElem? (show ReferenceResiduals.block140[10]?=some panel268.right from rfl))⟩
theorem valid269 : ValidPanel panel269 := ⟨modelCheck269,residualCheck269,
  ReferenceTrajectory.leftBlock13_subset (List.mem_of_getElem? (show ReferenceResiduals.block13[13]?=some panel269.left from rfl)),
  ReferenceTrajectory.rightBlock140_subset (List.mem_of_getElem? (show ReferenceResiduals.block140[9]?=some panel269.right from rfl))⟩
theorem valid270 : ValidPanel panel270 := ⟨modelCheck270,residualCheck270,
  ReferenceTrajectory.leftBlock13_subset (List.mem_of_getElem? (show ReferenceResiduals.block13[14]?=some panel270.left from rfl)),
  ReferenceTrajectory.rightBlock140_subset (List.mem_of_getElem? (show ReferenceResiduals.block140[8]?=some panel270.right from rfl))⟩
theorem valid271 : ValidPanel panel271 := ⟨modelCheck271,residualCheck271,
  ReferenceTrajectory.leftBlock13_subset (List.mem_of_getElem? (show ReferenceResiduals.block13[15]?=some panel271.left from rfl)),
  ReferenceTrajectory.rightBlock140_subset (List.mem_of_getElem? (show ReferenceResiduals.block140[7]?=some panel271.right from rfl))⟩
theorem valid272 : ValidPanel panel272 := ⟨modelCheck272,residualCheck272,
  ReferenceTrajectory.leftBlock14_subset (List.mem_of_getElem? (show ReferenceResiduals.block14[0]?=some panel272.left from rfl)),
  ReferenceTrajectory.rightBlock140_subset (List.mem_of_getElem? (show ReferenceResiduals.block140[6]?=some panel272.right from rfl))⟩
theorem valid273 : ValidPanel panel273 := ⟨modelCheck273,residualCheck273,
  ReferenceTrajectory.leftBlock14_subset (List.mem_of_getElem? (show ReferenceResiduals.block14[1]?=some panel273.left from rfl)),
  ReferenceTrajectory.rightBlock140_subset (List.mem_of_getElem? (show ReferenceResiduals.block140[5]?=some panel273.right from rfl))⟩
theorem valid274 : ValidPanel panel274 := ⟨modelCheck274,residualCheck274,
  ReferenceTrajectory.leftBlock14_subset (List.mem_of_getElem? (show ReferenceResiduals.block14[2]?=some panel274.left from rfl)),
  ReferenceTrajectory.rightBlock140_subset (List.mem_of_getElem? (show ReferenceResiduals.block140[4]?=some panel274.right from rfl))⟩
theorem valid275 : ValidPanel panel275 := ⟨modelCheck275,residualCheck275,
  ReferenceTrajectory.leftBlock14_subset (List.mem_of_getElem? (show ReferenceResiduals.block14[3]?=some panel275.left from rfl)),
  ReferenceTrajectory.rightBlock140_subset (List.mem_of_getElem? (show ReferenceResiduals.block140[3]?=some panel275.right from rfl))⟩
theorem valid276 : ValidPanel panel276 := ⟨modelCheck276,residualCheck276,
  ReferenceTrajectory.leftBlock14_subset (List.mem_of_getElem? (show ReferenceResiduals.block14[4]?=some panel276.left from rfl)),
  ReferenceTrajectory.rightBlock140_subset (List.mem_of_getElem? (show ReferenceResiduals.block140[2]?=some panel276.right from rfl))⟩
theorem valid277 : ValidPanel panel277 := ⟨modelCheck277,residualCheck277,
  ReferenceTrajectory.leftBlock14_subset (List.mem_of_getElem? (show ReferenceResiduals.block14[5]?=some panel277.left from rfl)),
  ReferenceTrajectory.rightBlock140_subset (List.mem_of_getElem? (show ReferenceResiduals.block140[1]?=some panel277.right from rfl))⟩
theorem valid278 : ValidPanel panel278 := ⟨modelCheck278,residualCheck278,
  ReferenceTrajectory.leftBlock14_subset (List.mem_of_getElem? (show ReferenceResiduals.block14[6]?=some panel278.left from rfl)),
  ReferenceTrajectory.rightBlock140_subset (List.mem_of_getElem? (show ReferenceResiduals.block140[0]?=some panel278.right from rfl))⟩
theorem valid279 : ValidPanel panel279 := ⟨modelCheck279,residualCheck279,
  ReferenceTrajectory.leftBlock14_subset (List.mem_of_getElem? (show ReferenceResiduals.block14[7]?=some panel279.left from rfl)),
  ReferenceTrajectory.rightBlock139_subset (List.mem_of_getElem? (show ReferenceResiduals.block139[15]?=some panel279.right from rfl))⟩
theorem valid280 : ValidPanel panel280 := ⟨modelCheck280,residualCheck280,
  ReferenceTrajectory.leftBlock14_subset (List.mem_of_getElem? (show ReferenceResiduals.block14[8]?=some panel280.left from rfl)),
  ReferenceTrajectory.rightBlock139_subset (List.mem_of_getElem? (show ReferenceResiduals.block139[14]?=some panel280.right from rfl))⟩
theorem valid281 : ValidPanel panel281 := ⟨modelCheck281,residualCheck281,
  ReferenceTrajectory.leftBlock14_subset (List.mem_of_getElem? (show ReferenceResiduals.block14[9]?=some panel281.left from rfl)),
  ReferenceTrajectory.rightBlock139_subset (List.mem_of_getElem? (show ReferenceResiduals.block139[13]?=some panel281.right from rfl))⟩
theorem valid282 : ValidPanel panel282 := ⟨modelCheck282,residualCheck282,
  ReferenceTrajectory.leftBlock14_subset (List.mem_of_getElem? (show ReferenceResiduals.block14[10]?=some panel282.left from rfl)),
  ReferenceTrajectory.rightBlock139_subset (List.mem_of_getElem? (show ReferenceResiduals.block139[12]?=some panel282.right from rfl))⟩
theorem valid283 : ValidPanel panel283 := ⟨modelCheck283,residualCheck283,
  ReferenceTrajectory.leftBlock14_subset (List.mem_of_getElem? (show ReferenceResiduals.block14[11]?=some panel283.left from rfl)),
  ReferenceTrajectory.rightBlock139_subset (List.mem_of_getElem? (show ReferenceResiduals.block139[11]?=some panel283.right from rfl))⟩
theorem valid284 : ValidPanel panel284 := ⟨modelCheck284,residualCheck284,
  ReferenceTrajectory.leftBlock14_subset (List.mem_of_getElem? (show ReferenceResiduals.block14[12]?=some panel284.left from rfl)),
  ReferenceTrajectory.rightBlock139_subset (List.mem_of_getElem? (show ReferenceResiduals.block139[10]?=some panel284.right from rfl))⟩
theorem valid285 : ValidPanel panel285 := ⟨modelCheck285,residualCheck285,
  ReferenceTrajectory.leftBlock14_subset (List.mem_of_getElem? (show ReferenceResiduals.block14[13]?=some panel285.left from rfl)),
  ReferenceTrajectory.rightBlock139_subset (List.mem_of_getElem? (show ReferenceResiduals.block139[9]?=some panel285.right from rfl))⟩
theorem valid286 : ValidPanel panel286 := ⟨modelCheck286,residualCheck286,
  ReferenceTrajectory.leftBlock14_subset (List.mem_of_getElem? (show ReferenceResiduals.block14[14]?=some panel286.left from rfl)),
  ReferenceTrajectory.rightBlock139_subset (List.mem_of_getElem? (show ReferenceResiduals.block139[8]?=some panel286.right from rfl))⟩
theorem valid287 : ValidPanel panel287 := ⟨modelCheck287,residualCheck287,
  ReferenceTrajectory.leftBlock14_subset (List.mem_of_getElem? (show ReferenceResiduals.block14[15]?=some panel287.left from rfl)),
  ReferenceTrajectory.rightBlock139_subset (List.mem_of_getElem? (show ReferenceResiduals.block139[7]?=some panel287.right from rfl))⟩
theorem validBlock8 : ∀ p∈block8,ValidPanel p := by
  simp only [block8,List.forall_mem_cons]
  exact ⟨valid256,⟨valid257,⟨valid258,⟨valid259,⟨valid260,⟨valid261,⟨valid262,⟨valid263,⟨valid264,⟨valid265,⟨valid266,⟨valid267,⟨valid268,⟨valid269,⟨valid270,⟨valid271,⟨valid272,⟨valid273,⟨valid274,⟨valid275,⟨valid276,⟨valid277,⟨valid278,⟨valid279,⟨valid280,⟨valid281,⟨valid282,⟨valid283,⟨valid284,⟨valid285,⟨valid286,⟨valid287,(by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end chebyshev2.Certificates.Compact.ContactValues

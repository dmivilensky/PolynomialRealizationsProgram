import «2610.05164v2».Certificates.Compact.ContactBatches.Batch009
import «2610.05164v2».Certificates.Compact.ContactCoverage
import «2610.05164v2».Certificates.Compact.ReferenceTrajectoryIndex

/-!
Article: 2610.05164v2, Section 4.1.
Correspondence009.
Use: `«2610.05164v2».Certificates.Compact.ContactValues.validBlock9` feeds
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
theorem valid288 : ValidPanel panel288 := ⟨modelCheck288,residualCheck288,
  ReferenceTrajectory.leftBlock15_subset (List.mem_of_getElem? (show ReferenceResiduals.block15[0]?=some panel288.left from rfl)),
  ReferenceTrajectory.rightBlock139_subset (List.mem_of_getElem? (show ReferenceResiduals.block139[6]?=some panel288.right from rfl))⟩
theorem valid289 : ValidPanel panel289 := ⟨modelCheck289,residualCheck289,
  ReferenceTrajectory.leftBlock15_subset (List.mem_of_getElem? (show ReferenceResiduals.block15[1]?=some panel289.left from rfl)),
  ReferenceTrajectory.rightBlock139_subset (List.mem_of_getElem? (show ReferenceResiduals.block139[5]?=some panel289.right from rfl))⟩
theorem valid290 : ValidPanel panel290 := ⟨modelCheck290,residualCheck290,
  ReferenceTrajectory.leftBlock15_subset (List.mem_of_getElem? (show ReferenceResiduals.block15[2]?=some panel290.left from rfl)),
  ReferenceTrajectory.rightBlock139_subset (List.mem_of_getElem? (show ReferenceResiduals.block139[4]?=some panel290.right from rfl))⟩
theorem valid291 : ValidPanel panel291 := ⟨modelCheck291,residualCheck291,
  ReferenceTrajectory.leftBlock15_subset (List.mem_of_getElem? (show ReferenceResiduals.block15[3]?=some panel291.left from rfl)),
  ReferenceTrajectory.rightBlock139_subset (List.mem_of_getElem? (show ReferenceResiduals.block139[3]?=some panel291.right from rfl))⟩
theorem valid292 : ValidPanel panel292 := ⟨modelCheck292,residualCheck292,
  ReferenceTrajectory.leftBlock15_subset (List.mem_of_getElem? (show ReferenceResiduals.block15[4]?=some panel292.left from rfl)),
  ReferenceTrajectory.rightBlock139_subset (List.mem_of_getElem? (show ReferenceResiduals.block139[2]?=some panel292.right from rfl))⟩
theorem valid293 : ValidPanel panel293 := ⟨modelCheck293,residualCheck293,
  ReferenceTrajectory.leftBlock15_subset (List.mem_of_getElem? (show ReferenceResiduals.block15[5]?=some panel293.left from rfl)),
  ReferenceTrajectory.rightBlock139_subset (List.mem_of_getElem? (show ReferenceResiduals.block139[1]?=some panel293.right from rfl))⟩
theorem valid294 : ValidPanel panel294 := ⟨modelCheck294,residualCheck294,
  ReferenceTrajectory.leftBlock15_subset (List.mem_of_getElem? (show ReferenceResiduals.block15[6]?=some panel294.left from rfl)),
  ReferenceTrajectory.rightBlock139_subset (List.mem_of_getElem? (show ReferenceResiduals.block139[0]?=some panel294.right from rfl))⟩
theorem valid295 : ValidPanel panel295 := ⟨modelCheck295,residualCheck295,
  ReferenceTrajectory.leftBlock15_subset (List.mem_of_getElem? (show ReferenceResiduals.block15[7]?=some panel295.left from rfl)),
  ReferenceTrajectory.rightBlock138_subset (List.mem_of_getElem? (show ReferenceResiduals.block138[15]?=some panel295.right from rfl))⟩
theorem valid296 : ValidPanel panel296 := ⟨modelCheck296,residualCheck296,
  ReferenceTrajectory.leftBlock15_subset (List.mem_of_getElem? (show ReferenceResiduals.block15[8]?=some panel296.left from rfl)),
  ReferenceTrajectory.rightBlock138_subset (List.mem_of_getElem? (show ReferenceResiduals.block138[14]?=some panel296.right from rfl))⟩
theorem valid297 : ValidPanel panel297 := ⟨modelCheck297,residualCheck297,
  ReferenceTrajectory.leftBlock15_subset (List.mem_of_getElem? (show ReferenceResiduals.block15[9]?=some panel297.left from rfl)),
  ReferenceTrajectory.rightBlock138_subset (List.mem_of_getElem? (show ReferenceResiduals.block138[13]?=some panel297.right from rfl))⟩
theorem valid298 : ValidPanel panel298 := ⟨modelCheck298,residualCheck298,
  ReferenceTrajectory.leftBlock15_subset (List.mem_of_getElem? (show ReferenceResiduals.block15[10]?=some panel298.left from rfl)),
  ReferenceTrajectory.rightBlock138_subset (List.mem_of_getElem? (show ReferenceResiduals.block138[12]?=some panel298.right from rfl))⟩
theorem valid299 : ValidPanel panel299 := ⟨modelCheck299,residualCheck299,
  ReferenceTrajectory.leftBlock15_subset (List.mem_of_getElem? (show ReferenceResiduals.block15[11]?=some panel299.left from rfl)),
  ReferenceTrajectory.rightBlock138_subset (List.mem_of_getElem? (show ReferenceResiduals.block138[11]?=some panel299.right from rfl))⟩
theorem valid300 : ValidPanel panel300 := ⟨modelCheck300,residualCheck300,
  ReferenceTrajectory.leftBlock15_subset (List.mem_of_getElem? (show ReferenceResiduals.block15[12]?=some panel300.left from rfl)),
  ReferenceTrajectory.rightBlock138_subset (List.mem_of_getElem? (show ReferenceResiduals.block138[10]?=some panel300.right from rfl))⟩
theorem valid301 : ValidPanel panel301 := ⟨modelCheck301,residualCheck301,
  ReferenceTrajectory.leftBlock15_subset (List.mem_of_getElem? (show ReferenceResiduals.block15[13]?=some panel301.left from rfl)),
  ReferenceTrajectory.rightBlock138_subset (List.mem_of_getElem? (show ReferenceResiduals.block138[9]?=some panel301.right from rfl))⟩
theorem valid302 : ValidPanel panel302 := ⟨modelCheck302,residualCheck302,
  ReferenceTrajectory.leftBlock15_subset (List.mem_of_getElem? (show ReferenceResiduals.block15[14]?=some panel302.left from rfl)),
  ReferenceTrajectory.rightBlock138_subset (List.mem_of_getElem? (show ReferenceResiduals.block138[8]?=some panel302.right from rfl))⟩
theorem valid303 : ValidPanel panel303 := ⟨modelCheck303,residualCheck303,
  ReferenceTrajectory.leftBlock15_subset (List.mem_of_getElem? (show ReferenceResiduals.block15[15]?=some panel303.left from rfl)),
  ReferenceTrajectory.rightBlock138_subset (List.mem_of_getElem? (show ReferenceResiduals.block138[7]?=some panel303.right from rfl))⟩
theorem valid304 : ValidPanel panel304 := ⟨modelCheck304,residualCheck304,
  ReferenceTrajectory.leftBlock16_subset (List.mem_of_getElem? (show ReferenceResiduals.block16[0]?=some panel304.left from rfl)),
  ReferenceTrajectory.rightBlock138_subset (List.mem_of_getElem? (show ReferenceResiduals.block138[6]?=some panel304.right from rfl))⟩
theorem valid305 : ValidPanel panel305 := ⟨modelCheck305,residualCheck305,
  ReferenceTrajectory.leftBlock16_subset (List.mem_of_getElem? (show ReferenceResiduals.block16[1]?=some panel305.left from rfl)),
  ReferenceTrajectory.rightBlock138_subset (List.mem_of_getElem? (show ReferenceResiduals.block138[5]?=some panel305.right from rfl))⟩
theorem valid306 : ValidPanel panel306 := ⟨modelCheck306,residualCheck306,
  ReferenceTrajectory.leftBlock16_subset (List.mem_of_getElem? (show ReferenceResiduals.block16[2]?=some panel306.left from rfl)),
  ReferenceTrajectory.rightBlock138_subset (List.mem_of_getElem? (show ReferenceResiduals.block138[4]?=some panel306.right from rfl))⟩
theorem valid307 : ValidPanel panel307 := ⟨modelCheck307,residualCheck307,
  ReferenceTrajectory.leftBlock16_subset (List.mem_of_getElem? (show ReferenceResiduals.block16[3]?=some panel307.left from rfl)),
  ReferenceTrajectory.rightBlock138_subset (List.mem_of_getElem? (show ReferenceResiduals.block138[3]?=some panel307.right from rfl))⟩
theorem valid308 : ValidPanel panel308 := ⟨modelCheck308,residualCheck308,
  ReferenceTrajectory.leftBlock16_subset (List.mem_of_getElem? (show ReferenceResiduals.block16[4]?=some panel308.left from rfl)),
  ReferenceTrajectory.rightBlock138_subset (List.mem_of_getElem? (show ReferenceResiduals.block138[2]?=some panel308.right from rfl))⟩
theorem valid309 : ValidPanel panel309 := ⟨modelCheck309,residualCheck309,
  ReferenceTrajectory.leftBlock16_subset (List.mem_of_getElem? (show ReferenceResiduals.block16[5]?=some panel309.left from rfl)),
  ReferenceTrajectory.rightBlock138_subset (List.mem_of_getElem? (show ReferenceResiduals.block138[1]?=some panel309.right from rfl))⟩
theorem valid310 : ValidPanel panel310 := ⟨modelCheck310,residualCheck310,
  ReferenceTrajectory.leftBlock16_subset (List.mem_of_getElem? (show ReferenceResiduals.block16[6]?=some panel310.left from rfl)),
  ReferenceTrajectory.rightBlock138_subset (List.mem_of_getElem? (show ReferenceResiduals.block138[0]?=some panel310.right from rfl))⟩
theorem valid311 : ValidPanel panel311 := ⟨modelCheck311,residualCheck311,
  ReferenceTrajectory.leftBlock16_subset (List.mem_of_getElem? (show ReferenceResiduals.block16[7]?=some panel311.left from rfl)),
  ReferenceTrajectory.rightBlock137_subset (List.mem_of_getElem? (show ReferenceResiduals.block137[15]?=some panel311.right from rfl))⟩
theorem valid312 : ValidPanel panel312 := ⟨modelCheck312,residualCheck312,
  ReferenceTrajectory.leftBlock16_subset (List.mem_of_getElem? (show ReferenceResiduals.block16[8]?=some panel312.left from rfl)),
  ReferenceTrajectory.rightBlock137_subset (List.mem_of_getElem? (show ReferenceResiduals.block137[14]?=some panel312.right from rfl))⟩
theorem valid313 : ValidPanel panel313 := ⟨modelCheck313,residualCheck313,
  ReferenceTrajectory.leftBlock16_subset (List.mem_of_getElem? (show ReferenceResiduals.block16[9]?=some panel313.left from rfl)),
  ReferenceTrajectory.rightBlock137_subset (List.mem_of_getElem? (show ReferenceResiduals.block137[13]?=some panel313.right from rfl))⟩
theorem valid314 : ValidPanel panel314 := ⟨modelCheck314,residualCheck314,
  ReferenceTrajectory.leftBlock16_subset (List.mem_of_getElem? (show ReferenceResiduals.block16[10]?=some panel314.left from rfl)),
  ReferenceTrajectory.rightBlock137_subset (List.mem_of_getElem? (show ReferenceResiduals.block137[12]?=some panel314.right from rfl))⟩
theorem valid315 : ValidPanel panel315 := ⟨modelCheck315,residualCheck315,
  ReferenceTrajectory.leftBlock16_subset (List.mem_of_getElem? (show ReferenceResiduals.block16[11]?=some panel315.left from rfl)),
  ReferenceTrajectory.rightBlock137_subset (List.mem_of_getElem? (show ReferenceResiduals.block137[11]?=some panel315.right from rfl))⟩
theorem valid316 : ValidPanel panel316 := ⟨modelCheck316,residualCheck316,
  ReferenceTrajectory.leftBlock16_subset (List.mem_of_getElem? (show ReferenceResiduals.block16[12]?=some panel316.left from rfl)),
  ReferenceTrajectory.rightBlock137_subset (List.mem_of_getElem? (show ReferenceResiduals.block137[10]?=some panel316.right from rfl))⟩
theorem valid317 : ValidPanel panel317 := ⟨modelCheck317,residualCheck317,
  ReferenceTrajectory.leftBlock16_subset (List.mem_of_getElem? (show ReferenceResiduals.block16[13]?=some panel317.left from rfl)),
  ReferenceTrajectory.rightBlock137_subset (List.mem_of_getElem? (show ReferenceResiduals.block137[9]?=some panel317.right from rfl))⟩
theorem valid318 : ValidPanel panel318 := ⟨modelCheck318,residualCheck318,
  ReferenceTrajectory.leftBlock16_subset (List.mem_of_getElem? (show ReferenceResiduals.block16[14]?=some panel318.left from rfl)),
  ReferenceTrajectory.rightBlock137_subset (List.mem_of_getElem? (show ReferenceResiduals.block137[8]?=some panel318.right from rfl))⟩
theorem valid319 : ValidPanel panel319 := ⟨modelCheck319,residualCheck319,
  ReferenceTrajectory.leftBlock16_subset (List.mem_of_getElem? (show ReferenceResiduals.block16[15]?=some panel319.left from rfl)),
  ReferenceTrajectory.rightBlock137_subset (List.mem_of_getElem? (show ReferenceResiduals.block137[7]?=some panel319.right from rfl))⟩
theorem validBlock9 : ∀ p∈block9,ValidPanel p := by
  simp only [block9,List.forall_mem_cons]
  exact ⟨valid288,⟨valid289,⟨valid290,⟨valid291,⟨valid292,⟨valid293,⟨valid294,⟨valid295,⟨valid296,⟨valid297,⟨valid298,⟨valid299,⟨valid300,⟨valid301,⟨valid302,⟨valid303,⟨valid304,⟨valid305,⟨valid306,⟨valid307,⟨valid308,⟨valid309,⟨valid310,⟨valid311,⟨valid312,⟨valid313,⟨valid314,⟨valid315,⟨valid316,⟨valid317,⟨valid318,⟨valid319,(by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end «2610.05164v2».Certificates.Compact.ContactValues

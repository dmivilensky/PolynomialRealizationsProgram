import «2610.05164v2».Certificates.Compact.ContactBatches.Batch011
import «2610.05164v2».Certificates.Compact.ContactCoverage
import «2610.05164v2».Certificates.Compact.ReferenceTrajectoryIndex

/-!
Article: 2610.05164v2, Section 4.1.
Correspondence011.
Use: `«2610.05164v2».Certificates.Compact.ContactValues.validBlock11` feeds
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
theorem valid352 : ValidPanel panel352 := ⟨modelCheck352,residualCheck352,
  ReferenceTrajectory.leftBlock19_subset (List.mem_of_getElem? (show ReferenceResiduals.block19[0]?=some panel352.left from rfl)),
  ReferenceTrajectory.rightBlock135_subset (List.mem_of_getElem? (show ReferenceResiduals.block135[6]?=some panel352.right from rfl))⟩
theorem valid353 : ValidPanel panel353 := ⟨modelCheck353,residualCheck353,
  ReferenceTrajectory.leftBlock19_subset (List.mem_of_getElem? (show ReferenceResiduals.block19[1]?=some panel353.left from rfl)),
  ReferenceTrajectory.rightBlock135_subset (List.mem_of_getElem? (show ReferenceResiduals.block135[5]?=some panel353.right from rfl))⟩
theorem valid354 : ValidPanel panel354 := ⟨modelCheck354,residualCheck354,
  ReferenceTrajectory.leftBlock19_subset (List.mem_of_getElem? (show ReferenceResiduals.block19[2]?=some panel354.left from rfl)),
  ReferenceTrajectory.rightBlock135_subset (List.mem_of_getElem? (show ReferenceResiduals.block135[4]?=some panel354.right from rfl))⟩
theorem valid355 : ValidPanel panel355 := ⟨modelCheck355,residualCheck355,
  ReferenceTrajectory.leftBlock19_subset (List.mem_of_getElem? (show ReferenceResiduals.block19[3]?=some panel355.left from rfl)),
  ReferenceTrajectory.rightBlock135_subset (List.mem_of_getElem? (show ReferenceResiduals.block135[3]?=some panel355.right from rfl))⟩
theorem valid356 : ValidPanel panel356 := ⟨modelCheck356,residualCheck356,
  ReferenceTrajectory.leftBlock19_subset (List.mem_of_getElem? (show ReferenceResiduals.block19[4]?=some panel356.left from rfl)),
  ReferenceTrajectory.rightBlock135_subset (List.mem_of_getElem? (show ReferenceResiduals.block135[2]?=some panel356.right from rfl))⟩
theorem valid357 : ValidPanel panel357 := ⟨modelCheck357,residualCheck357,
  ReferenceTrajectory.leftBlock19_subset (List.mem_of_getElem? (show ReferenceResiduals.block19[5]?=some panel357.left from rfl)),
  ReferenceTrajectory.rightBlock135_subset (List.mem_of_getElem? (show ReferenceResiduals.block135[1]?=some panel357.right from rfl))⟩
theorem valid358 : ValidPanel panel358 := ⟨modelCheck358,residualCheck358,
  ReferenceTrajectory.leftBlock19_subset (List.mem_of_getElem? (show ReferenceResiduals.block19[6]?=some panel358.left from rfl)),
  ReferenceTrajectory.rightBlock135_subset (List.mem_of_getElem? (show ReferenceResiduals.block135[0]?=some panel358.right from rfl))⟩
theorem valid359 : ValidPanel panel359 := ⟨modelCheck359,residualCheck359,
  ReferenceTrajectory.leftBlock19_subset (List.mem_of_getElem? (show ReferenceResiduals.block19[7]?=some panel359.left from rfl)),
  ReferenceTrajectory.rightBlock134_subset (List.mem_of_getElem? (show ReferenceResiduals.block134[15]?=some panel359.right from rfl))⟩
theorem valid360 : ValidPanel panel360 := ⟨modelCheck360,residualCheck360,
  ReferenceTrajectory.leftBlock19_subset (List.mem_of_getElem? (show ReferenceResiduals.block19[8]?=some panel360.left from rfl)),
  ReferenceTrajectory.rightBlock134_subset (List.mem_of_getElem? (show ReferenceResiduals.block134[14]?=some panel360.right from rfl))⟩
theorem valid361 : ValidPanel panel361 := ⟨modelCheck361,residualCheck361,
  ReferenceTrajectory.leftBlock19_subset (List.mem_of_getElem? (show ReferenceResiduals.block19[9]?=some panel361.left from rfl)),
  ReferenceTrajectory.rightBlock134_subset (List.mem_of_getElem? (show ReferenceResiduals.block134[13]?=some panel361.right from rfl))⟩
theorem valid362 : ValidPanel panel362 := ⟨modelCheck362,residualCheck362,
  ReferenceTrajectory.leftBlock19_subset (List.mem_of_getElem? (show ReferenceResiduals.block19[10]?=some panel362.left from rfl)),
  ReferenceTrajectory.rightBlock134_subset (List.mem_of_getElem? (show ReferenceResiduals.block134[12]?=some panel362.right from rfl))⟩
theorem valid363 : ValidPanel panel363 := ⟨modelCheck363,residualCheck363,
  ReferenceTrajectory.leftBlock19_subset (List.mem_of_getElem? (show ReferenceResiduals.block19[11]?=some panel363.left from rfl)),
  ReferenceTrajectory.rightBlock134_subset (List.mem_of_getElem? (show ReferenceResiduals.block134[11]?=some panel363.right from rfl))⟩
theorem valid364 : ValidPanel panel364 := ⟨modelCheck364,residualCheck364,
  ReferenceTrajectory.leftBlock19_subset (List.mem_of_getElem? (show ReferenceResiduals.block19[12]?=some panel364.left from rfl)),
  ReferenceTrajectory.rightBlock134_subset (List.mem_of_getElem? (show ReferenceResiduals.block134[10]?=some panel364.right from rfl))⟩
theorem valid365 : ValidPanel panel365 := ⟨modelCheck365,residualCheck365,
  ReferenceTrajectory.leftBlock19_subset (List.mem_of_getElem? (show ReferenceResiduals.block19[13]?=some panel365.left from rfl)),
  ReferenceTrajectory.rightBlock134_subset (List.mem_of_getElem? (show ReferenceResiduals.block134[9]?=some panel365.right from rfl))⟩
theorem valid366 : ValidPanel panel366 := ⟨modelCheck366,residualCheck366,
  ReferenceTrajectory.leftBlock19_subset (List.mem_of_getElem? (show ReferenceResiduals.block19[14]?=some panel366.left from rfl)),
  ReferenceTrajectory.rightBlock134_subset (List.mem_of_getElem? (show ReferenceResiduals.block134[8]?=some panel366.right from rfl))⟩
theorem valid367 : ValidPanel panel367 := ⟨modelCheck367,residualCheck367,
  ReferenceTrajectory.leftBlock19_subset (List.mem_of_getElem? (show ReferenceResiduals.block19[15]?=some panel367.left from rfl)),
  ReferenceTrajectory.rightBlock134_subset (List.mem_of_getElem? (show ReferenceResiduals.block134[7]?=some panel367.right from rfl))⟩
theorem valid368 : ValidPanel panel368 := ⟨modelCheck368,residualCheck368,
  ReferenceTrajectory.leftBlock20_subset (List.mem_of_getElem? (show ReferenceResiduals.block20[0]?=some panel368.left from rfl)),
  ReferenceTrajectory.rightBlock134_subset (List.mem_of_getElem? (show ReferenceResiduals.block134[6]?=some panel368.right from rfl))⟩
theorem valid369 : ValidPanel panel369 := ⟨modelCheck369,residualCheck369,
  ReferenceTrajectory.leftBlock20_subset (List.mem_of_getElem? (show ReferenceResiduals.block20[1]?=some panel369.left from rfl)),
  ReferenceTrajectory.rightBlock134_subset (List.mem_of_getElem? (show ReferenceResiduals.block134[5]?=some panel369.right from rfl))⟩
theorem valid370 : ValidPanel panel370 := ⟨modelCheck370,residualCheck370,
  ReferenceTrajectory.leftBlock20_subset (List.mem_of_getElem? (show ReferenceResiduals.block20[2]?=some panel370.left from rfl)),
  ReferenceTrajectory.rightBlock134_subset (List.mem_of_getElem? (show ReferenceResiduals.block134[4]?=some panel370.right from rfl))⟩
theorem valid371 : ValidPanel panel371 := ⟨modelCheck371,residualCheck371,
  ReferenceTrajectory.leftBlock20_subset (List.mem_of_getElem? (show ReferenceResiduals.block20[3]?=some panel371.left from rfl)),
  ReferenceTrajectory.rightBlock134_subset (List.mem_of_getElem? (show ReferenceResiduals.block134[3]?=some panel371.right from rfl))⟩
theorem valid372 : ValidPanel panel372 := ⟨modelCheck372,residualCheck372,
  ReferenceTrajectory.leftBlock20_subset (List.mem_of_getElem? (show ReferenceResiduals.block20[4]?=some panel372.left from rfl)),
  ReferenceTrajectory.rightBlock134_subset (List.mem_of_getElem? (show ReferenceResiduals.block134[2]?=some panel372.right from rfl))⟩
theorem valid373 : ValidPanel panel373 := ⟨modelCheck373,residualCheck373,
  ReferenceTrajectory.leftBlock20_subset (List.mem_of_getElem? (show ReferenceResiduals.block20[5]?=some panel373.left from rfl)),
  ReferenceTrajectory.rightBlock134_subset (List.mem_of_getElem? (show ReferenceResiduals.block134[1]?=some panel373.right from rfl))⟩
theorem valid374 : ValidPanel panel374 := ⟨modelCheck374,residualCheck374,
  ReferenceTrajectory.leftBlock20_subset (List.mem_of_getElem? (show ReferenceResiduals.block20[6]?=some panel374.left from rfl)),
  ReferenceTrajectory.rightBlock134_subset (List.mem_of_getElem? (show ReferenceResiduals.block134[0]?=some panel374.right from rfl))⟩
theorem valid375 : ValidPanel panel375 := ⟨modelCheck375,residualCheck375,
  ReferenceTrajectory.leftBlock20_subset (List.mem_of_getElem? (show ReferenceResiduals.block20[7]?=some panel375.left from rfl)),
  ReferenceTrajectory.rightBlock133_subset (List.mem_of_getElem? (show ReferenceResiduals.block133[15]?=some panel375.right from rfl))⟩
theorem valid376 : ValidPanel panel376 := ⟨modelCheck376,residualCheck376,
  ReferenceTrajectory.leftBlock20_subset (List.mem_of_getElem? (show ReferenceResiduals.block20[8]?=some panel376.left from rfl)),
  ReferenceTrajectory.rightBlock133_subset (List.mem_of_getElem? (show ReferenceResiduals.block133[14]?=some panel376.right from rfl))⟩
theorem valid377 : ValidPanel panel377 := ⟨modelCheck377,residualCheck377,
  ReferenceTrajectory.leftBlock20_subset (List.mem_of_getElem? (show ReferenceResiduals.block20[9]?=some panel377.left from rfl)),
  ReferenceTrajectory.rightBlock133_subset (List.mem_of_getElem? (show ReferenceResiduals.block133[13]?=some panel377.right from rfl))⟩
theorem valid378 : ValidPanel panel378 := ⟨modelCheck378,residualCheck378,
  ReferenceTrajectory.leftBlock20_subset (List.mem_of_getElem? (show ReferenceResiduals.block20[10]?=some panel378.left from rfl)),
  ReferenceTrajectory.rightBlock133_subset (List.mem_of_getElem? (show ReferenceResiduals.block133[12]?=some panel378.right from rfl))⟩
theorem valid379 : ValidPanel panel379 := ⟨modelCheck379,residualCheck379,
  ReferenceTrajectory.leftBlock20_subset (List.mem_of_getElem? (show ReferenceResiduals.block20[11]?=some panel379.left from rfl)),
  ReferenceTrajectory.rightBlock133_subset (List.mem_of_getElem? (show ReferenceResiduals.block133[11]?=some panel379.right from rfl))⟩
theorem valid380 : ValidPanel panel380 := ⟨modelCheck380,residualCheck380,
  ReferenceTrajectory.leftBlock20_subset (List.mem_of_getElem? (show ReferenceResiduals.block20[12]?=some panel380.left from rfl)),
  ReferenceTrajectory.rightBlock133_subset (List.mem_of_getElem? (show ReferenceResiduals.block133[10]?=some panel380.right from rfl))⟩
theorem valid381 : ValidPanel panel381 := ⟨modelCheck381,residualCheck381,
  ReferenceTrajectory.leftBlock20_subset (List.mem_of_getElem? (show ReferenceResiduals.block20[13]?=some panel381.left from rfl)),
  ReferenceTrajectory.rightBlock133_subset (List.mem_of_getElem? (show ReferenceResiduals.block133[9]?=some panel381.right from rfl))⟩
theorem valid382 : ValidPanel panel382 := ⟨modelCheck382,residualCheck382,
  ReferenceTrajectory.leftBlock20_subset (List.mem_of_getElem? (show ReferenceResiduals.block20[14]?=some panel382.left from rfl)),
  ReferenceTrajectory.rightBlock133_subset (List.mem_of_getElem? (show ReferenceResiduals.block133[8]?=some panel382.right from rfl))⟩
theorem valid383 : ValidPanel panel383 := ⟨modelCheck383,residualCheck383,
  ReferenceTrajectory.leftBlock20_subset (List.mem_of_getElem? (show ReferenceResiduals.block20[15]?=some panel383.left from rfl)),
  ReferenceTrajectory.rightBlock133_subset (List.mem_of_getElem? (show ReferenceResiduals.block133[7]?=some panel383.right from rfl))⟩
theorem validBlock11 : ∀ p∈block11,ValidPanel p := by
  simp only [block11,List.forall_mem_cons]
  exact ⟨valid352,⟨valid353,⟨valid354,⟨valid355,⟨valid356,⟨valid357,⟨valid358,⟨valid359,⟨valid360,⟨valid361,⟨valid362,⟨valid363,⟨valid364,⟨valid365,⟨valid366,⟨valid367,⟨valid368,⟨valid369,⟨valid370,⟨valid371,⟨valid372,⟨valid373,⟨valid374,⟨valid375,⟨valid376,⟨valid377,⟨valid378,⟨valid379,⟨valid380,⟨valid381,⟨valid382,⟨valid383,(by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end «2610.05164v2».Certificates.Compact.ContactValues

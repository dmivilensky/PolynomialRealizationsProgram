import chebyshev2.Certificates.Compact.ContactBatches.Batch014
import chebyshev2.Certificates.Compact.ContactCoverage
import chebyshev2.Certificates.Compact.ReferenceTrajectoryIndex

/-!
Article: chebyshev2, Section 4.1.
Correspondence014.
Use: `chebyshev2.Certificates.Compact.ContactValues.validBlock14` feeds
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
theorem valid448 : ValidPanel panel448 := ⟨modelCheck448,residualCheck448,
  ReferenceTrajectory.leftBlock25_subset (List.mem_of_getElem? (show ReferenceResiduals.block25[0]?=some panel448.left from rfl)),
  ReferenceTrajectory.rightBlock129_subset (List.mem_of_getElem? (show ReferenceResiduals.block129[6]?=some panel448.right from rfl))⟩
theorem valid449 : ValidPanel panel449 := ⟨modelCheck449,residualCheck449,
  ReferenceTrajectory.leftBlock25_subset (List.mem_of_getElem? (show ReferenceResiduals.block25[1]?=some panel449.left from rfl)),
  ReferenceTrajectory.rightBlock129_subset (List.mem_of_getElem? (show ReferenceResiduals.block129[5]?=some panel449.right from rfl))⟩
theorem valid450 : ValidPanel panel450 := ⟨modelCheck450,residualCheck450,
  ReferenceTrajectory.leftBlock25_subset (List.mem_of_getElem? (show ReferenceResiduals.block25[2]?=some panel450.left from rfl)),
  ReferenceTrajectory.rightBlock129_subset (List.mem_of_getElem? (show ReferenceResiduals.block129[4]?=some panel450.right from rfl))⟩
theorem valid451 : ValidPanel panel451 := ⟨modelCheck451,residualCheck451,
  ReferenceTrajectory.leftBlock25_subset (List.mem_of_getElem? (show ReferenceResiduals.block25[3]?=some panel451.left from rfl)),
  ReferenceTrajectory.rightBlock129_subset (List.mem_of_getElem? (show ReferenceResiduals.block129[3]?=some panel451.right from rfl))⟩
theorem valid452 : ValidPanel panel452 := ⟨modelCheck452,residualCheck452,
  ReferenceTrajectory.leftBlock25_subset (List.mem_of_getElem? (show ReferenceResiduals.block25[4]?=some panel452.left from rfl)),
  ReferenceTrajectory.rightBlock129_subset (List.mem_of_getElem? (show ReferenceResiduals.block129[2]?=some panel452.right from rfl))⟩
theorem valid453 : ValidPanel panel453 := ⟨modelCheck453,residualCheck453,
  ReferenceTrajectory.leftBlock25_subset (List.mem_of_getElem? (show ReferenceResiduals.block25[5]?=some panel453.left from rfl)),
  ReferenceTrajectory.rightBlock129_subset (List.mem_of_getElem? (show ReferenceResiduals.block129[1]?=some panel453.right from rfl))⟩
theorem valid454 : ValidPanel panel454 := ⟨modelCheck454,residualCheck454,
  ReferenceTrajectory.leftBlock25_subset (List.mem_of_getElem? (show ReferenceResiduals.block25[6]?=some panel454.left from rfl)),
  ReferenceTrajectory.rightBlock129_subset (List.mem_of_getElem? (show ReferenceResiduals.block129[0]?=some panel454.right from rfl))⟩
theorem valid455 : ValidPanel panel455 := ⟨modelCheck455,residualCheck455,
  ReferenceTrajectory.leftBlock25_subset (List.mem_of_getElem? (show ReferenceResiduals.block25[7]?=some panel455.left from rfl)),
  ReferenceTrajectory.rightBlock128_subset (List.mem_of_getElem? (show ReferenceResiduals.block128[15]?=some panel455.right from rfl))⟩
theorem valid456 : ValidPanel panel456 := ⟨modelCheck456,residualCheck456,
  ReferenceTrajectory.leftBlock25_subset (List.mem_of_getElem? (show ReferenceResiduals.block25[8]?=some panel456.left from rfl)),
  ReferenceTrajectory.rightBlock128_subset (List.mem_of_getElem? (show ReferenceResiduals.block128[14]?=some panel456.right from rfl))⟩
theorem valid457 : ValidPanel panel457 := ⟨modelCheck457,residualCheck457,
  ReferenceTrajectory.leftBlock25_subset (List.mem_of_getElem? (show ReferenceResiduals.block25[9]?=some panel457.left from rfl)),
  ReferenceTrajectory.rightBlock128_subset (List.mem_of_getElem? (show ReferenceResiduals.block128[13]?=some panel457.right from rfl))⟩
theorem valid458 : ValidPanel panel458 := ⟨modelCheck458,residualCheck458,
  ReferenceTrajectory.leftBlock25_subset (List.mem_of_getElem? (show ReferenceResiduals.block25[10]?=some panel458.left from rfl)),
  ReferenceTrajectory.rightBlock128_subset (List.mem_of_getElem? (show ReferenceResiduals.block128[12]?=some panel458.right from rfl))⟩
theorem valid459 : ValidPanel panel459 := ⟨modelCheck459,residualCheck459,
  ReferenceTrajectory.leftBlock25_subset (List.mem_of_getElem? (show ReferenceResiduals.block25[11]?=some panel459.left from rfl)),
  ReferenceTrajectory.rightBlock128_subset (List.mem_of_getElem? (show ReferenceResiduals.block128[11]?=some panel459.right from rfl))⟩
theorem valid460 : ValidPanel panel460 := ⟨modelCheck460,residualCheck460,
  ReferenceTrajectory.leftBlock25_subset (List.mem_of_getElem? (show ReferenceResiduals.block25[12]?=some panel460.left from rfl)),
  ReferenceTrajectory.rightBlock128_subset (List.mem_of_getElem? (show ReferenceResiduals.block128[10]?=some panel460.right from rfl))⟩
theorem valid461 : ValidPanel panel461 := ⟨modelCheck461,residualCheck461,
  ReferenceTrajectory.leftBlock25_subset (List.mem_of_getElem? (show ReferenceResiduals.block25[13]?=some panel461.left from rfl)),
  ReferenceTrajectory.rightBlock128_subset (List.mem_of_getElem? (show ReferenceResiduals.block128[9]?=some panel461.right from rfl))⟩
theorem valid462 : ValidPanel panel462 := ⟨modelCheck462,residualCheck462,
  ReferenceTrajectory.leftBlock25_subset (List.mem_of_getElem? (show ReferenceResiduals.block25[14]?=some panel462.left from rfl)),
  ReferenceTrajectory.rightBlock128_subset (List.mem_of_getElem? (show ReferenceResiduals.block128[8]?=some panel462.right from rfl))⟩
theorem valid463 : ValidPanel panel463 := ⟨modelCheck463,residualCheck463,
  ReferenceTrajectory.leftBlock25_subset (List.mem_of_getElem? (show ReferenceResiduals.block25[15]?=some panel463.left from rfl)),
  ReferenceTrajectory.rightBlock128_subset (List.mem_of_getElem? (show ReferenceResiduals.block128[7]?=some panel463.right from rfl))⟩
theorem valid464 : ValidPanel panel464 := ⟨modelCheck464,residualCheck464,
  ReferenceTrajectory.leftBlock26_subset (List.mem_of_getElem? (show ReferenceResiduals.block26[0]?=some panel464.left from rfl)),
  ReferenceTrajectory.rightBlock128_subset (List.mem_of_getElem? (show ReferenceResiduals.block128[6]?=some panel464.right from rfl))⟩
theorem valid465 : ValidPanel panel465 := ⟨modelCheck465,residualCheck465,
  ReferenceTrajectory.leftBlock26_subset (List.mem_of_getElem? (show ReferenceResiduals.block26[1]?=some panel465.left from rfl)),
  ReferenceTrajectory.rightBlock128_subset (List.mem_of_getElem? (show ReferenceResiduals.block128[5]?=some panel465.right from rfl))⟩
theorem valid466 : ValidPanel panel466 := ⟨modelCheck466,residualCheck466,
  ReferenceTrajectory.leftBlock26_subset (List.mem_of_getElem? (show ReferenceResiduals.block26[2]?=some panel466.left from rfl)),
  ReferenceTrajectory.rightBlock128_subset (List.mem_of_getElem? (show ReferenceResiduals.block128[4]?=some panel466.right from rfl))⟩
theorem valid467 : ValidPanel panel467 := ⟨modelCheck467,residualCheck467,
  ReferenceTrajectory.leftBlock26_subset (List.mem_of_getElem? (show ReferenceResiduals.block26[3]?=some panel467.left from rfl)),
  ReferenceTrajectory.rightBlock128_subset (List.mem_of_getElem? (show ReferenceResiduals.block128[3]?=some panel467.right from rfl))⟩
theorem valid468 : ValidPanel panel468 := ⟨modelCheck468,residualCheck468,
  ReferenceTrajectory.leftBlock26_subset (List.mem_of_getElem? (show ReferenceResiduals.block26[4]?=some panel468.left from rfl)),
  ReferenceTrajectory.rightBlock128_subset (List.mem_of_getElem? (show ReferenceResiduals.block128[2]?=some panel468.right from rfl))⟩
theorem valid469 : ValidPanel panel469 := ⟨modelCheck469,residualCheck469,
  ReferenceTrajectory.leftBlock26_subset (List.mem_of_getElem? (show ReferenceResiduals.block26[5]?=some panel469.left from rfl)),
  ReferenceTrajectory.rightBlock128_subset (List.mem_of_getElem? (show ReferenceResiduals.block128[1]?=some panel469.right from rfl))⟩
theorem valid470 : ValidPanel panel470 := ⟨modelCheck470,residualCheck470,
  ReferenceTrajectory.leftBlock26_subset (List.mem_of_getElem? (show ReferenceResiduals.block26[6]?=some panel470.left from rfl)),
  ReferenceTrajectory.rightBlock128_subset (List.mem_of_getElem? (show ReferenceResiduals.block128[0]?=some panel470.right from rfl))⟩
theorem valid471 : ValidPanel panel471 := ⟨modelCheck471,residualCheck471,
  ReferenceTrajectory.leftBlock26_subset (List.mem_of_getElem? (show ReferenceResiduals.block26[7]?=some panel471.left from rfl)),
  ReferenceTrajectory.rightBlock127_subset (List.mem_of_getElem? (show ReferenceResiduals.block127[15]?=some panel471.right from rfl))⟩
theorem valid472 : ValidPanel panel472 := ⟨modelCheck472,residualCheck472,
  ReferenceTrajectory.leftBlock26_subset (List.mem_of_getElem? (show ReferenceResiduals.block26[8]?=some panel472.left from rfl)),
  ReferenceTrajectory.rightBlock127_subset (List.mem_of_getElem? (show ReferenceResiduals.block127[14]?=some panel472.right from rfl))⟩
theorem valid473 : ValidPanel panel473 := ⟨modelCheck473,residualCheck473,
  ReferenceTrajectory.leftBlock26_subset (List.mem_of_getElem? (show ReferenceResiduals.block26[9]?=some panel473.left from rfl)),
  ReferenceTrajectory.rightBlock127_subset (List.mem_of_getElem? (show ReferenceResiduals.block127[13]?=some panel473.right from rfl))⟩
theorem valid474 : ValidPanel panel474 := ⟨modelCheck474,residualCheck474,
  ReferenceTrajectory.leftBlock26_subset (List.mem_of_getElem? (show ReferenceResiduals.block26[10]?=some panel474.left from rfl)),
  ReferenceTrajectory.rightBlock127_subset (List.mem_of_getElem? (show ReferenceResiduals.block127[12]?=some panel474.right from rfl))⟩
theorem valid475 : ValidPanel panel475 := ⟨modelCheck475,residualCheck475,
  ReferenceTrajectory.leftBlock26_subset (List.mem_of_getElem? (show ReferenceResiduals.block26[11]?=some panel475.left from rfl)),
  ReferenceTrajectory.rightBlock127_subset (List.mem_of_getElem? (show ReferenceResiduals.block127[11]?=some panel475.right from rfl))⟩
theorem valid476 : ValidPanel panel476 := ⟨modelCheck476,residualCheck476,
  ReferenceTrajectory.leftBlock26_subset (List.mem_of_getElem? (show ReferenceResiduals.block26[12]?=some panel476.left from rfl)),
  ReferenceTrajectory.rightBlock127_subset (List.mem_of_getElem? (show ReferenceResiduals.block127[10]?=some panel476.right from rfl))⟩
theorem valid477 : ValidPanel panel477 := ⟨modelCheck477,residualCheck477,
  ReferenceTrajectory.leftBlock26_subset (List.mem_of_getElem? (show ReferenceResiduals.block26[13]?=some panel477.left from rfl)),
  ReferenceTrajectory.rightBlock127_subset (List.mem_of_getElem? (show ReferenceResiduals.block127[9]?=some panel477.right from rfl))⟩
theorem valid478 : ValidPanel panel478 := ⟨modelCheck478,residualCheck478,
  ReferenceTrajectory.leftBlock26_subset (List.mem_of_getElem? (show ReferenceResiduals.block26[14]?=some panel478.left from rfl)),
  ReferenceTrajectory.rightBlock127_subset (List.mem_of_getElem? (show ReferenceResiduals.block127[8]?=some panel478.right from rfl))⟩
theorem valid479 : ValidPanel panel479 := ⟨modelCheck479,residualCheck479,
  ReferenceTrajectory.leftBlock26_subset (List.mem_of_getElem? (show ReferenceResiduals.block26[15]?=some panel479.left from rfl)),
  ReferenceTrajectory.rightBlock127_subset (List.mem_of_getElem? (show ReferenceResiduals.block127[7]?=some panel479.right from rfl))⟩
theorem validBlock14 : ∀ p∈block14,ValidPanel p := by
  simp only [block14,List.forall_mem_cons]
  exact ⟨valid448,⟨valid449,⟨valid450,⟨valid451,⟨valid452,⟨valid453,⟨valid454,⟨valid455,⟨valid456,⟨valid457,⟨valid458,⟨valid459,⟨valid460,⟨valid461,⟨valid462,⟨valid463,⟨valid464,⟨valid465,⟨valid466,⟨valid467,⟨valid468,⟨valid469,⟨valid470,⟨valid471,⟨valid472,⟨valid473,⟨valid474,⟨valid475,⟨valid476,⟨valid477,⟨valid478,⟨valid479,(by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end chebyshev2.Certificates.Compact.ContactValues

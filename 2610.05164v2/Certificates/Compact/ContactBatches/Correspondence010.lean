import «2610.05164v2».Certificates.Compact.ContactBatches.Batch010
import «2610.05164v2».Certificates.Compact.ContactCoverage
import «2610.05164v2».Certificates.Compact.ReferenceTrajectoryIndex

/-!
Article: 2610.05164v2, Section 4.1.
Correspondence010.
Use: `«2610.05164v2».Certificates.Compact.ContactValues.validBlock10` feeds
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
theorem valid320 : ValidPanel panel320 := ⟨modelCheck320,residualCheck320,
  ReferenceTrajectory.leftBlock17_subset (List.mem_of_getElem? (show ReferenceResiduals.block17[0]?=some panel320.left from rfl)),
  ReferenceTrajectory.rightBlock137_subset (List.mem_of_getElem? (show ReferenceResiduals.block137[6]?=some panel320.right from rfl))⟩
theorem valid321 : ValidPanel panel321 := ⟨modelCheck321,residualCheck321,
  ReferenceTrajectory.leftBlock17_subset (List.mem_of_getElem? (show ReferenceResiduals.block17[1]?=some panel321.left from rfl)),
  ReferenceTrajectory.rightBlock137_subset (List.mem_of_getElem? (show ReferenceResiduals.block137[5]?=some panel321.right from rfl))⟩
theorem valid322 : ValidPanel panel322 := ⟨modelCheck322,residualCheck322,
  ReferenceTrajectory.leftBlock17_subset (List.mem_of_getElem? (show ReferenceResiduals.block17[2]?=some panel322.left from rfl)),
  ReferenceTrajectory.rightBlock137_subset (List.mem_of_getElem? (show ReferenceResiduals.block137[4]?=some panel322.right from rfl))⟩
theorem valid323 : ValidPanel panel323 := ⟨modelCheck323,residualCheck323,
  ReferenceTrajectory.leftBlock17_subset (List.mem_of_getElem? (show ReferenceResiduals.block17[3]?=some panel323.left from rfl)),
  ReferenceTrajectory.rightBlock137_subset (List.mem_of_getElem? (show ReferenceResiduals.block137[3]?=some panel323.right from rfl))⟩
theorem valid324 : ValidPanel panel324 := ⟨modelCheck324,residualCheck324,
  ReferenceTrajectory.leftBlock17_subset (List.mem_of_getElem? (show ReferenceResiduals.block17[4]?=some panel324.left from rfl)),
  ReferenceTrajectory.rightBlock137_subset (List.mem_of_getElem? (show ReferenceResiduals.block137[2]?=some panel324.right from rfl))⟩
theorem valid325 : ValidPanel panel325 := ⟨modelCheck325,residualCheck325,
  ReferenceTrajectory.leftBlock17_subset (List.mem_of_getElem? (show ReferenceResiduals.block17[5]?=some panel325.left from rfl)),
  ReferenceTrajectory.rightBlock137_subset (List.mem_of_getElem? (show ReferenceResiduals.block137[1]?=some panel325.right from rfl))⟩
theorem valid326 : ValidPanel panel326 := ⟨modelCheck326,residualCheck326,
  ReferenceTrajectory.leftBlock17_subset (List.mem_of_getElem? (show ReferenceResiduals.block17[6]?=some panel326.left from rfl)),
  ReferenceTrajectory.rightBlock137_subset (List.mem_of_getElem? (show ReferenceResiduals.block137[0]?=some panel326.right from rfl))⟩
theorem valid327 : ValidPanel panel327 := ⟨modelCheck327,residualCheck327,
  ReferenceTrajectory.leftBlock17_subset (List.mem_of_getElem? (show ReferenceResiduals.block17[7]?=some panel327.left from rfl)),
  ReferenceTrajectory.rightBlock136_subset (List.mem_of_getElem? (show ReferenceResiduals.block136[15]?=some panel327.right from rfl))⟩
theorem valid328 : ValidPanel panel328 := ⟨modelCheck328,residualCheck328,
  ReferenceTrajectory.leftBlock17_subset (List.mem_of_getElem? (show ReferenceResiduals.block17[8]?=some panel328.left from rfl)),
  ReferenceTrajectory.rightBlock136_subset (List.mem_of_getElem? (show ReferenceResiduals.block136[14]?=some panel328.right from rfl))⟩
theorem valid329 : ValidPanel panel329 := ⟨modelCheck329,residualCheck329,
  ReferenceTrajectory.leftBlock17_subset (List.mem_of_getElem? (show ReferenceResiduals.block17[9]?=some panel329.left from rfl)),
  ReferenceTrajectory.rightBlock136_subset (List.mem_of_getElem? (show ReferenceResiduals.block136[13]?=some panel329.right from rfl))⟩
theorem valid330 : ValidPanel panel330 := ⟨modelCheck330,residualCheck330,
  ReferenceTrajectory.leftBlock17_subset (List.mem_of_getElem? (show ReferenceResiduals.block17[10]?=some panel330.left from rfl)),
  ReferenceTrajectory.rightBlock136_subset (List.mem_of_getElem? (show ReferenceResiduals.block136[12]?=some panel330.right from rfl))⟩
theorem valid331 : ValidPanel panel331 := ⟨modelCheck331,residualCheck331,
  ReferenceTrajectory.leftBlock17_subset (List.mem_of_getElem? (show ReferenceResiduals.block17[11]?=some panel331.left from rfl)),
  ReferenceTrajectory.rightBlock136_subset (List.mem_of_getElem? (show ReferenceResiduals.block136[11]?=some panel331.right from rfl))⟩
theorem valid332 : ValidPanel panel332 := ⟨modelCheck332,residualCheck332,
  ReferenceTrajectory.leftBlock17_subset (List.mem_of_getElem? (show ReferenceResiduals.block17[12]?=some panel332.left from rfl)),
  ReferenceTrajectory.rightBlock136_subset (List.mem_of_getElem? (show ReferenceResiduals.block136[10]?=some panel332.right from rfl))⟩
theorem valid333 : ValidPanel panel333 := ⟨modelCheck333,residualCheck333,
  ReferenceTrajectory.leftBlock17_subset (List.mem_of_getElem? (show ReferenceResiduals.block17[13]?=some panel333.left from rfl)),
  ReferenceTrajectory.rightBlock136_subset (List.mem_of_getElem? (show ReferenceResiduals.block136[9]?=some panel333.right from rfl))⟩
theorem valid334 : ValidPanel panel334 := ⟨modelCheck334,residualCheck334,
  ReferenceTrajectory.leftBlock17_subset (List.mem_of_getElem? (show ReferenceResiduals.block17[14]?=some panel334.left from rfl)),
  ReferenceTrajectory.rightBlock136_subset (List.mem_of_getElem? (show ReferenceResiduals.block136[8]?=some panel334.right from rfl))⟩
theorem valid335 : ValidPanel panel335 := ⟨modelCheck335,residualCheck335,
  ReferenceTrajectory.leftBlock17_subset (List.mem_of_getElem? (show ReferenceResiduals.block17[15]?=some panel335.left from rfl)),
  ReferenceTrajectory.rightBlock136_subset (List.mem_of_getElem? (show ReferenceResiduals.block136[7]?=some panel335.right from rfl))⟩
theorem valid336 : ValidPanel panel336 := ⟨modelCheck336,residualCheck336,
  ReferenceTrajectory.leftBlock18_subset (List.mem_of_getElem? (show ReferenceResiduals.block18[0]?=some panel336.left from rfl)),
  ReferenceTrajectory.rightBlock136_subset (List.mem_of_getElem? (show ReferenceResiduals.block136[6]?=some panel336.right from rfl))⟩
theorem valid337 : ValidPanel panel337 := ⟨modelCheck337,residualCheck337,
  ReferenceTrajectory.leftBlock18_subset (List.mem_of_getElem? (show ReferenceResiduals.block18[1]?=some panel337.left from rfl)),
  ReferenceTrajectory.rightBlock136_subset (List.mem_of_getElem? (show ReferenceResiduals.block136[5]?=some panel337.right from rfl))⟩
theorem valid338 : ValidPanel panel338 := ⟨modelCheck338,residualCheck338,
  ReferenceTrajectory.leftBlock18_subset (List.mem_of_getElem? (show ReferenceResiduals.block18[2]?=some panel338.left from rfl)),
  ReferenceTrajectory.rightBlock136_subset (List.mem_of_getElem? (show ReferenceResiduals.block136[4]?=some panel338.right from rfl))⟩
theorem valid339 : ValidPanel panel339 := ⟨modelCheck339,residualCheck339,
  ReferenceTrajectory.leftBlock18_subset (List.mem_of_getElem? (show ReferenceResiduals.block18[3]?=some panel339.left from rfl)),
  ReferenceTrajectory.rightBlock136_subset (List.mem_of_getElem? (show ReferenceResiduals.block136[3]?=some panel339.right from rfl))⟩
theorem valid340 : ValidPanel panel340 := ⟨modelCheck340,residualCheck340,
  ReferenceTrajectory.leftBlock18_subset (List.mem_of_getElem? (show ReferenceResiduals.block18[4]?=some panel340.left from rfl)),
  ReferenceTrajectory.rightBlock136_subset (List.mem_of_getElem? (show ReferenceResiduals.block136[2]?=some panel340.right from rfl))⟩
theorem valid341 : ValidPanel panel341 := ⟨modelCheck341,residualCheck341,
  ReferenceTrajectory.leftBlock18_subset (List.mem_of_getElem? (show ReferenceResiduals.block18[5]?=some panel341.left from rfl)),
  ReferenceTrajectory.rightBlock136_subset (List.mem_of_getElem? (show ReferenceResiduals.block136[1]?=some panel341.right from rfl))⟩
theorem valid342 : ValidPanel panel342 := ⟨modelCheck342,residualCheck342,
  ReferenceTrajectory.leftBlock18_subset (List.mem_of_getElem? (show ReferenceResiduals.block18[6]?=some panel342.left from rfl)),
  ReferenceTrajectory.rightBlock136_subset (List.mem_of_getElem? (show ReferenceResiduals.block136[0]?=some panel342.right from rfl))⟩
theorem valid343 : ValidPanel panel343 := ⟨modelCheck343,residualCheck343,
  ReferenceTrajectory.leftBlock18_subset (List.mem_of_getElem? (show ReferenceResiduals.block18[7]?=some panel343.left from rfl)),
  ReferenceTrajectory.rightBlock135_subset (List.mem_of_getElem? (show ReferenceResiduals.block135[15]?=some panel343.right from rfl))⟩
theorem valid344 : ValidPanel panel344 := ⟨modelCheck344,residualCheck344,
  ReferenceTrajectory.leftBlock18_subset (List.mem_of_getElem? (show ReferenceResiduals.block18[8]?=some panel344.left from rfl)),
  ReferenceTrajectory.rightBlock135_subset (List.mem_of_getElem? (show ReferenceResiduals.block135[14]?=some panel344.right from rfl))⟩
theorem valid345 : ValidPanel panel345 := ⟨modelCheck345,residualCheck345,
  ReferenceTrajectory.leftBlock18_subset (List.mem_of_getElem? (show ReferenceResiduals.block18[9]?=some panel345.left from rfl)),
  ReferenceTrajectory.rightBlock135_subset (List.mem_of_getElem? (show ReferenceResiduals.block135[13]?=some panel345.right from rfl))⟩
theorem valid346 : ValidPanel panel346 := ⟨modelCheck346,residualCheck346,
  ReferenceTrajectory.leftBlock18_subset (List.mem_of_getElem? (show ReferenceResiduals.block18[10]?=some panel346.left from rfl)),
  ReferenceTrajectory.rightBlock135_subset (List.mem_of_getElem? (show ReferenceResiduals.block135[12]?=some panel346.right from rfl))⟩
theorem valid347 : ValidPanel panel347 := ⟨modelCheck347,residualCheck347,
  ReferenceTrajectory.leftBlock18_subset (List.mem_of_getElem? (show ReferenceResiduals.block18[11]?=some panel347.left from rfl)),
  ReferenceTrajectory.rightBlock135_subset (List.mem_of_getElem? (show ReferenceResiduals.block135[11]?=some panel347.right from rfl))⟩
theorem valid348 : ValidPanel panel348 := ⟨modelCheck348,residualCheck348,
  ReferenceTrajectory.leftBlock18_subset (List.mem_of_getElem? (show ReferenceResiduals.block18[12]?=some panel348.left from rfl)),
  ReferenceTrajectory.rightBlock135_subset (List.mem_of_getElem? (show ReferenceResiduals.block135[10]?=some panel348.right from rfl))⟩
theorem valid349 : ValidPanel panel349 := ⟨modelCheck349,residualCheck349,
  ReferenceTrajectory.leftBlock18_subset (List.mem_of_getElem? (show ReferenceResiduals.block18[13]?=some panel349.left from rfl)),
  ReferenceTrajectory.rightBlock135_subset (List.mem_of_getElem? (show ReferenceResiduals.block135[9]?=some panel349.right from rfl))⟩
theorem valid350 : ValidPanel panel350 := ⟨modelCheck350,residualCheck350,
  ReferenceTrajectory.leftBlock18_subset (List.mem_of_getElem? (show ReferenceResiduals.block18[14]?=some panel350.left from rfl)),
  ReferenceTrajectory.rightBlock135_subset (List.mem_of_getElem? (show ReferenceResiduals.block135[8]?=some panel350.right from rfl))⟩
theorem valid351 : ValidPanel panel351 := ⟨modelCheck351,residualCheck351,
  ReferenceTrajectory.leftBlock18_subset (List.mem_of_getElem? (show ReferenceResiduals.block18[15]?=some panel351.left from rfl)),
  ReferenceTrajectory.rightBlock135_subset (List.mem_of_getElem? (show ReferenceResiduals.block135[7]?=some panel351.right from rfl))⟩
theorem validBlock10 : ∀ p∈block10,ValidPanel p := by
  simp only [block10,List.forall_mem_cons]
  exact ⟨valid320,⟨valid321,⟨valid322,⟨valid323,⟨valid324,⟨valid325,⟨valid326,⟨valid327,⟨valid328,⟨valid329,⟨valid330,⟨valid331,⟨valid332,⟨valid333,⟨valid334,⟨valid335,⟨valid336,⟨valid337,⟨valid338,⟨valid339,⟨valid340,⟨valid341,⟨valid342,⟨valid343,⟨valid344,⟨valid345,⟨valid346,⟨valid347,⟨valid348,⟨valid349,⟨valid350,⟨valid351,(by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end «2610.05164v2».Certificates.Compact.ContactValues

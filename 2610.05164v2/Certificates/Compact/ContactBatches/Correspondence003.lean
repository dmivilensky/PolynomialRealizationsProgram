import «2610.05164v2».Certificates.Compact.ContactBatches.Batch003
import «2610.05164v2».Certificates.Compact.ContactCoverage
import «2610.05164v2».Certificates.Compact.ReferenceTrajectoryIndex

/-!
Article: 2610.05164v2, Section 4.1.
Correspondence003.
Use: `«2610.05164v2».Certificates.Compact.ContactValues.validBlock3` feeds
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
theorem valid96 : ValidPanel panel96 := ⟨modelCheck96,residualCheck96,
  ReferenceTrajectory.leftBlock4_subset (List.mem_of_getElem? (show ReferenceResiduals.block4[1]?=some panel96.left from rfl)),
  ReferenceTrajectory.rightBlock151_subset (List.mem_of_getElem? (show ReferenceResiduals.block151[6]?=some panel96.right from rfl))⟩
theorem valid97 : ValidPanel panel97 := ⟨modelCheck97,residualCheck97,
  ReferenceTrajectory.leftBlock4_subset (List.mem_of_getElem? (show ReferenceResiduals.block4[2]?=some panel97.left from rfl)),
  ReferenceTrajectory.rightBlock151_subset (List.mem_of_getElem? (show ReferenceResiduals.block151[5]?=some panel97.right from rfl))⟩
theorem valid98 : ValidPanel panel98 := ⟨modelCheck98,residualCheck98,
  ReferenceTrajectory.leftBlock4_subset (List.mem_of_getElem? (show ReferenceResiduals.block4[2]?=some panel98.left from rfl)),
  ReferenceTrajectory.rightBlock151_subset (List.mem_of_getElem? (show ReferenceResiduals.block151[4]?=some panel98.right from rfl))⟩
theorem valid99 : ValidPanel panel99 := ⟨modelCheck99,residualCheck99,
  ReferenceTrajectory.leftBlock4_subset (List.mem_of_getElem? (show ReferenceResiduals.block4[3]?=some panel99.left from rfl)),
  ReferenceTrajectory.rightBlock151_subset (List.mem_of_getElem? (show ReferenceResiduals.block151[3]?=some panel99.right from rfl))⟩
theorem valid100 : ValidPanel panel100 := ⟨modelCheck100,residualCheck100,
  ReferenceTrajectory.leftBlock4_subset (List.mem_of_getElem? (show ReferenceResiduals.block4[3]?=some panel100.left from rfl)),
  ReferenceTrajectory.rightBlock151_subset (List.mem_of_getElem? (show ReferenceResiduals.block151[2]?=some panel100.right from rfl))⟩
theorem valid101 : ValidPanel panel101 := ⟨modelCheck101,residualCheck101,
  ReferenceTrajectory.leftBlock4_subset (List.mem_of_getElem? (show ReferenceResiduals.block4[4]?=some panel101.left from rfl)),
  ReferenceTrajectory.rightBlock151_subset (List.mem_of_getElem? (show ReferenceResiduals.block151[1]?=some panel101.right from rfl))⟩
theorem valid102 : ValidPanel panel102 := ⟨modelCheck102,residualCheck102,
  ReferenceTrajectory.leftBlock4_subset (List.mem_of_getElem? (show ReferenceResiduals.block4[4]?=some panel102.left from rfl)),
  ReferenceTrajectory.rightBlock151_subset (List.mem_of_getElem? (show ReferenceResiduals.block151[0]?=some panel102.right from rfl))⟩
theorem valid103 : ValidPanel panel103 := ⟨modelCheck103,residualCheck103,
  ReferenceTrajectory.leftBlock4_subset (List.mem_of_getElem? (show ReferenceResiduals.block4[5]?=some panel103.left from rfl)),
  ReferenceTrajectory.rightBlock150_subset (List.mem_of_getElem? (show ReferenceResiduals.block150[15]?=some panel103.right from rfl))⟩
theorem valid104 : ValidPanel panel104 := ⟨modelCheck104,residualCheck104,
  ReferenceTrajectory.leftBlock4_subset (List.mem_of_getElem? (show ReferenceResiduals.block4[5]?=some panel104.left from rfl)),
  ReferenceTrajectory.rightBlock150_subset (List.mem_of_getElem? (show ReferenceResiduals.block150[14]?=some panel104.right from rfl))⟩
theorem valid105 : ValidPanel panel105 := ⟨modelCheck105,residualCheck105,
  ReferenceTrajectory.leftBlock4_subset (List.mem_of_getElem? (show ReferenceResiduals.block4[6]?=some panel105.left from rfl)),
  ReferenceTrajectory.rightBlock150_subset (List.mem_of_getElem? (show ReferenceResiduals.block150[13]?=some panel105.right from rfl))⟩
theorem valid106 : ValidPanel panel106 := ⟨modelCheck106,residualCheck106,
  ReferenceTrajectory.leftBlock4_subset (List.mem_of_getElem? (show ReferenceResiduals.block4[6]?=some panel106.left from rfl)),
  ReferenceTrajectory.rightBlock150_subset (List.mem_of_getElem? (show ReferenceResiduals.block150[12]?=some panel106.right from rfl))⟩
theorem valid107 : ValidPanel panel107 := ⟨modelCheck107,residualCheck107,
  ReferenceTrajectory.leftBlock4_subset (List.mem_of_getElem? (show ReferenceResiduals.block4[7]?=some panel107.left from rfl)),
  ReferenceTrajectory.rightBlock150_subset (List.mem_of_getElem? (show ReferenceResiduals.block150[11]?=some panel107.right from rfl))⟩
theorem valid108 : ValidPanel panel108 := ⟨modelCheck108,residualCheck108,
  ReferenceTrajectory.leftBlock4_subset (List.mem_of_getElem? (show ReferenceResiduals.block4[7]?=some panel108.left from rfl)),
  ReferenceTrajectory.rightBlock150_subset (List.mem_of_getElem? (show ReferenceResiduals.block150[10]?=some panel108.right from rfl))⟩
theorem valid109 : ValidPanel panel109 := ⟨modelCheck109,residualCheck109,
  ReferenceTrajectory.leftBlock4_subset (List.mem_of_getElem? (show ReferenceResiduals.block4[8]?=some panel109.left from rfl)),
  ReferenceTrajectory.rightBlock150_subset (List.mem_of_getElem? (show ReferenceResiduals.block150[9]?=some panel109.right from rfl))⟩
theorem valid110 : ValidPanel panel110 := ⟨modelCheck110,residualCheck110,
  ReferenceTrajectory.leftBlock4_subset (List.mem_of_getElem? (show ReferenceResiduals.block4[8]?=some panel110.left from rfl)),
  ReferenceTrajectory.rightBlock150_subset (List.mem_of_getElem? (show ReferenceResiduals.block150[8]?=some panel110.right from rfl))⟩
theorem valid111 : ValidPanel panel111 := ⟨modelCheck111,residualCheck111,
  ReferenceTrajectory.leftBlock4_subset (List.mem_of_getElem? (show ReferenceResiduals.block4[9]?=some panel111.left from rfl)),
  ReferenceTrajectory.rightBlock150_subset (List.mem_of_getElem? (show ReferenceResiduals.block150[7]?=some panel111.right from rfl))⟩
theorem valid112 : ValidPanel panel112 := ⟨modelCheck112,residualCheck112,
  ReferenceTrajectory.leftBlock4_subset (List.mem_of_getElem? (show ReferenceResiduals.block4[9]?=some panel112.left from rfl)),
  ReferenceTrajectory.rightBlock150_subset (List.mem_of_getElem? (show ReferenceResiduals.block150[6]?=some panel112.right from rfl))⟩
theorem valid113 : ValidPanel panel113 := ⟨modelCheck113,residualCheck113,
  ReferenceTrajectory.leftBlock4_subset (List.mem_of_getElem? (show ReferenceResiduals.block4[10]?=some panel113.left from rfl)),
  ReferenceTrajectory.rightBlock150_subset (List.mem_of_getElem? (show ReferenceResiduals.block150[5]?=some panel113.right from rfl))⟩
theorem valid114 : ValidPanel panel114 := ⟨modelCheck114,residualCheck114,
  ReferenceTrajectory.leftBlock4_subset (List.mem_of_getElem? (show ReferenceResiduals.block4[10]?=some panel114.left from rfl)),
  ReferenceTrajectory.rightBlock150_subset (List.mem_of_getElem? (show ReferenceResiduals.block150[4]?=some panel114.right from rfl))⟩
theorem valid115 : ValidPanel panel115 := ⟨modelCheck115,residualCheck115,
  ReferenceTrajectory.leftBlock4_subset (List.mem_of_getElem? (show ReferenceResiduals.block4[11]?=some panel115.left from rfl)),
  ReferenceTrajectory.rightBlock150_subset (List.mem_of_getElem? (show ReferenceResiduals.block150[3]?=some panel115.right from rfl))⟩
theorem valid116 : ValidPanel panel116 := ⟨modelCheck116,residualCheck116,
  ReferenceTrajectory.leftBlock4_subset (List.mem_of_getElem? (show ReferenceResiduals.block4[11]?=some panel116.left from rfl)),
  ReferenceTrajectory.rightBlock150_subset (List.mem_of_getElem? (show ReferenceResiduals.block150[2]?=some panel116.right from rfl))⟩
theorem valid117 : ValidPanel panel117 := ⟨modelCheck117,residualCheck117,
  ReferenceTrajectory.leftBlock4_subset (List.mem_of_getElem? (show ReferenceResiduals.block4[12]?=some panel117.left from rfl)),
  ReferenceTrajectory.rightBlock150_subset (List.mem_of_getElem? (show ReferenceResiduals.block150[1]?=some panel117.right from rfl))⟩
theorem valid118 : ValidPanel panel118 := ⟨modelCheck118,residualCheck118,
  ReferenceTrajectory.leftBlock4_subset (List.mem_of_getElem? (show ReferenceResiduals.block4[12]?=some panel118.left from rfl)),
  ReferenceTrajectory.rightBlock150_subset (List.mem_of_getElem? (show ReferenceResiduals.block150[0]?=some panel118.right from rfl))⟩
theorem valid119 : ValidPanel panel119 := ⟨modelCheck119,residualCheck119,
  ReferenceTrajectory.leftBlock4_subset (List.mem_of_getElem? (show ReferenceResiduals.block4[13]?=some panel119.left from rfl)),
  ReferenceTrajectory.rightBlock149_subset (List.mem_of_getElem? (show ReferenceResiduals.block149[15]?=some panel119.right from rfl))⟩
theorem valid120 : ValidPanel panel120 := ⟨modelCheck120,residualCheck120,
  ReferenceTrajectory.leftBlock4_subset (List.mem_of_getElem? (show ReferenceResiduals.block4[13]?=some panel120.left from rfl)),
  ReferenceTrajectory.rightBlock149_subset (List.mem_of_getElem? (show ReferenceResiduals.block149[14]?=some panel120.right from rfl))⟩
theorem valid121 : ValidPanel panel121 := ⟨modelCheck121,residualCheck121,
  ReferenceTrajectory.leftBlock4_subset (List.mem_of_getElem? (show ReferenceResiduals.block4[14]?=some panel121.left from rfl)),
  ReferenceTrajectory.rightBlock149_subset (List.mem_of_getElem? (show ReferenceResiduals.block149[13]?=some panel121.right from rfl))⟩
theorem valid122 : ValidPanel panel122 := ⟨modelCheck122,residualCheck122,
  ReferenceTrajectory.leftBlock4_subset (List.mem_of_getElem? (show ReferenceResiduals.block4[14]?=some panel122.left from rfl)),
  ReferenceTrajectory.rightBlock149_subset (List.mem_of_getElem? (show ReferenceResiduals.block149[12]?=some panel122.right from rfl))⟩
theorem valid123 : ValidPanel panel123 := ⟨modelCheck123,residualCheck123,
  ReferenceTrajectory.leftBlock4_subset (List.mem_of_getElem? (show ReferenceResiduals.block4[15]?=some panel123.left from rfl)),
  ReferenceTrajectory.rightBlock149_subset (List.mem_of_getElem? (show ReferenceResiduals.block149[11]?=some panel123.right from rfl))⟩
theorem valid124 : ValidPanel panel124 := ⟨modelCheck124,residualCheck124,
  ReferenceTrajectory.leftBlock4_subset (List.mem_of_getElem? (show ReferenceResiduals.block4[15]?=some panel124.left from rfl)),
  ReferenceTrajectory.rightBlock149_subset (List.mem_of_getElem? (show ReferenceResiduals.block149[10]?=some panel124.right from rfl))⟩
theorem valid125 : ValidPanel panel125 := ⟨modelCheck125,residualCheck125,
  ReferenceTrajectory.leftBlock5_subset (List.mem_of_getElem? (show ReferenceResiduals.block5[0]?=some panel125.left from rfl)),
  ReferenceTrajectory.rightBlock149_subset (List.mem_of_getElem? (show ReferenceResiduals.block149[9]?=some panel125.right from rfl))⟩
theorem valid126 : ValidPanel panel126 := ⟨modelCheck126,residualCheck126,
  ReferenceTrajectory.leftBlock5_subset (List.mem_of_getElem? (show ReferenceResiduals.block5[0]?=some panel126.left from rfl)),
  ReferenceTrajectory.rightBlock149_subset (List.mem_of_getElem? (show ReferenceResiduals.block149[8]?=some panel126.right from rfl))⟩
theorem valid127 : ValidPanel panel127 := ⟨modelCheck127,residualCheck127,
  ReferenceTrajectory.leftBlock5_subset (List.mem_of_getElem? (show ReferenceResiduals.block5[1]?=some panel127.left from rfl)),
  ReferenceTrajectory.rightBlock149_subset (List.mem_of_getElem? (show ReferenceResiduals.block149[7]?=some panel127.right from rfl))⟩
theorem validBlock3 : ∀ p∈block3,ValidPanel p := by
  simp only [block3,List.forall_mem_cons]
  exact ⟨valid96,⟨valid97,⟨valid98,⟨valid99,⟨valid100,⟨valid101,⟨valid102,⟨valid103,⟨valid104,⟨valid105,⟨valid106,⟨valid107,⟨valid108,⟨valid109,⟨valid110,⟨valid111,⟨valid112,⟨valid113,⟨valid114,⟨valid115,⟨valid116,⟨valid117,⟨valid118,⟨valid119,⟨valid120,⟨valid121,⟨valid122,⟨valid123,⟨valid124,⟨valid125,⟨valid126,⟨valid127,(by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end «2610.05164v2».Certificates.Compact.ContactValues

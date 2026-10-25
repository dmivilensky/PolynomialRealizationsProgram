import chebyshev2.Certificates.Compact.ContactBatches.Batch028
import chebyshev2.Certificates.Compact.ContactCoverage
import chebyshev2.Certificates.Compact.ReferenceTrajectoryIndex

/-!
Article: chebyshev2, Section 4.1.
Correspondence028.
Use: `chebyshev2.Certificates.Compact.ContactValues.validBlock28` feeds
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
theorem valid896 : ValidPanel panel896 := ⟨modelCheck896,residualCheck896,
  ReferenceTrajectory.leftBlock52_subset (List.mem_of_getElem? (show ReferenceResiduals.block52[1]?=some panel896.left from rfl)),
  ReferenceTrajectory.rightBlock101_subset (List.mem_of_getElem? (show ReferenceResiduals.block101[6]?=some panel896.right from rfl))⟩
theorem valid897 : ValidPanel panel897 := ⟨modelCheck897,residualCheck897,
  ReferenceTrajectory.leftBlock52_subset (List.mem_of_getElem? (show ReferenceResiduals.block52[2]?=some panel897.left from rfl)),
  ReferenceTrajectory.rightBlock101_subset (List.mem_of_getElem? (show ReferenceResiduals.block101[5]?=some panel897.right from rfl))⟩
theorem valid898 : ValidPanel panel898 := ⟨modelCheck898,residualCheck898,
  ReferenceTrajectory.leftBlock52_subset (List.mem_of_getElem? (show ReferenceResiduals.block52[3]?=some panel898.left from rfl)),
  ReferenceTrajectory.rightBlock101_subset (List.mem_of_getElem? (show ReferenceResiduals.block101[4]?=some panel898.right from rfl))⟩
theorem valid899 : ValidPanel panel899 := ⟨modelCheck899,residualCheck899,
  ReferenceTrajectory.leftBlock52_subset (List.mem_of_getElem? (show ReferenceResiduals.block52[4]?=some panel899.left from rfl)),
  ReferenceTrajectory.rightBlock101_subset (List.mem_of_getElem? (show ReferenceResiduals.block101[3]?=some panel899.right from rfl))⟩
theorem valid900 : ValidPanel panel900 := ⟨modelCheck900,residualCheck900,
  ReferenceTrajectory.leftBlock52_subset (List.mem_of_getElem? (show ReferenceResiduals.block52[5]?=some panel900.left from rfl)),
  ReferenceTrajectory.rightBlock101_subset (List.mem_of_getElem? (show ReferenceResiduals.block101[2]?=some panel900.right from rfl))⟩
theorem valid901 : ValidPanel panel901 := ⟨modelCheck901,residualCheck901,
  ReferenceTrajectory.leftBlock52_subset (List.mem_of_getElem? (show ReferenceResiduals.block52[6]?=some panel901.left from rfl)),
  ReferenceTrajectory.rightBlock101_subset (List.mem_of_getElem? (show ReferenceResiduals.block101[1]?=some panel901.right from rfl))⟩
theorem valid902 : ValidPanel panel902 := ⟨modelCheck902,residualCheck902,
  ReferenceTrajectory.leftBlock52_subset (List.mem_of_getElem? (show ReferenceResiduals.block52[7]?=some panel902.left from rfl)),
  ReferenceTrajectory.rightBlock101_subset (List.mem_of_getElem? (show ReferenceResiduals.block101[0]?=some panel902.right from rfl))⟩
theorem valid903 : ValidPanel panel903 := ⟨modelCheck903,residualCheck903,
  ReferenceTrajectory.leftBlock52_subset (List.mem_of_getElem? (show ReferenceResiduals.block52[8]?=some panel903.left from rfl)),
  ReferenceTrajectory.rightBlock100_subset (List.mem_of_getElem? (show ReferenceResiduals.block100[15]?=some panel903.right from rfl))⟩
theorem valid904 : ValidPanel panel904 := ⟨modelCheck904,residualCheck904,
  ReferenceTrajectory.leftBlock52_subset (List.mem_of_getElem? (show ReferenceResiduals.block52[9]?=some panel904.left from rfl)),
  ReferenceTrajectory.rightBlock100_subset (List.mem_of_getElem? (show ReferenceResiduals.block100[14]?=some panel904.right from rfl))⟩
theorem valid905 : ValidPanel panel905 := ⟨modelCheck905,residualCheck905,
  ReferenceTrajectory.leftBlock52_subset (List.mem_of_getElem? (show ReferenceResiduals.block52[10]?=some panel905.left from rfl)),
  ReferenceTrajectory.rightBlock100_subset (List.mem_of_getElem? (show ReferenceResiduals.block100[13]?=some panel905.right from rfl))⟩
theorem valid906 : ValidPanel panel906 := ⟨modelCheck906,residualCheck906,
  ReferenceTrajectory.leftBlock52_subset (List.mem_of_getElem? (show ReferenceResiduals.block52[11]?=some panel906.left from rfl)),
  ReferenceTrajectory.rightBlock100_subset (List.mem_of_getElem? (show ReferenceResiduals.block100[12]?=some panel906.right from rfl))⟩
theorem valid907 : ValidPanel panel907 := ⟨modelCheck907,residualCheck907,
  ReferenceTrajectory.leftBlock52_subset (List.mem_of_getElem? (show ReferenceResiduals.block52[12]?=some panel907.left from rfl)),
  ReferenceTrajectory.rightBlock100_subset (List.mem_of_getElem? (show ReferenceResiduals.block100[11]?=some panel907.right from rfl))⟩
theorem valid908 : ValidPanel panel908 := ⟨modelCheck908,residualCheck908,
  ReferenceTrajectory.leftBlock52_subset (List.mem_of_getElem? (show ReferenceResiduals.block52[13]?=some panel908.left from rfl)),
  ReferenceTrajectory.rightBlock100_subset (List.mem_of_getElem? (show ReferenceResiduals.block100[10]?=some panel908.right from rfl))⟩
theorem valid909 : ValidPanel panel909 := ⟨modelCheck909,residualCheck909,
  ReferenceTrajectory.leftBlock52_subset (List.mem_of_getElem? (show ReferenceResiduals.block52[14]?=some panel909.left from rfl)),
  ReferenceTrajectory.rightBlock100_subset (List.mem_of_getElem? (show ReferenceResiduals.block100[9]?=some panel909.right from rfl))⟩
theorem valid910 : ValidPanel panel910 := ⟨modelCheck910,residualCheck910,
  ReferenceTrajectory.leftBlock52_subset (List.mem_of_getElem? (show ReferenceResiduals.block52[15]?=some panel910.left from rfl)),
  ReferenceTrajectory.rightBlock100_subset (List.mem_of_getElem? (show ReferenceResiduals.block100[8]?=some panel910.right from rfl))⟩
theorem valid911 : ValidPanel panel911 := ⟨modelCheck911,residualCheck911,
  ReferenceTrajectory.leftBlock53_subset (List.mem_of_getElem? (show ReferenceResiduals.block53[0]?=some panel911.left from rfl)),
  ReferenceTrajectory.rightBlock100_subset (List.mem_of_getElem? (show ReferenceResiduals.block100[7]?=some panel911.right from rfl))⟩
theorem valid912 : ValidPanel panel912 := ⟨modelCheck912,residualCheck912,
  ReferenceTrajectory.leftBlock53_subset (List.mem_of_getElem? (show ReferenceResiduals.block53[1]?=some panel912.left from rfl)),
  ReferenceTrajectory.rightBlock100_subset (List.mem_of_getElem? (show ReferenceResiduals.block100[6]?=some panel912.right from rfl))⟩
theorem valid913 : ValidPanel panel913 := ⟨modelCheck913,residualCheck913,
  ReferenceTrajectory.leftBlock53_subset (List.mem_of_getElem? (show ReferenceResiduals.block53[2]?=some panel913.left from rfl)),
  ReferenceTrajectory.rightBlock100_subset (List.mem_of_getElem? (show ReferenceResiduals.block100[5]?=some panel913.right from rfl))⟩
theorem valid914 : ValidPanel panel914 := ⟨modelCheck914,residualCheck914,
  ReferenceTrajectory.leftBlock53_subset (List.mem_of_getElem? (show ReferenceResiduals.block53[3]?=some panel914.left from rfl)),
  ReferenceTrajectory.rightBlock100_subset (List.mem_of_getElem? (show ReferenceResiduals.block100[4]?=some panel914.right from rfl))⟩
theorem valid915 : ValidPanel panel915 := ⟨modelCheck915,residualCheck915,
  ReferenceTrajectory.leftBlock53_subset (List.mem_of_getElem? (show ReferenceResiduals.block53[4]?=some panel915.left from rfl)),
  ReferenceTrajectory.rightBlock100_subset (List.mem_of_getElem? (show ReferenceResiduals.block100[3]?=some panel915.right from rfl))⟩
theorem valid916 : ValidPanel panel916 := ⟨modelCheck916,residualCheck916,
  ReferenceTrajectory.leftBlock53_subset (List.mem_of_getElem? (show ReferenceResiduals.block53[5]?=some panel916.left from rfl)),
  ReferenceTrajectory.rightBlock100_subset (List.mem_of_getElem? (show ReferenceResiduals.block100[2]?=some panel916.right from rfl))⟩
theorem valid917 : ValidPanel panel917 := ⟨modelCheck917,residualCheck917,
  ReferenceTrajectory.leftBlock53_subset (List.mem_of_getElem? (show ReferenceResiduals.block53[6]?=some panel917.left from rfl)),
  ReferenceTrajectory.rightBlock100_subset (List.mem_of_getElem? (show ReferenceResiduals.block100[1]?=some panel917.right from rfl))⟩
theorem valid918 : ValidPanel panel918 := ⟨modelCheck918,residualCheck918,
  ReferenceTrajectory.leftBlock53_subset (List.mem_of_getElem? (show ReferenceResiduals.block53[7]?=some panel918.left from rfl)),
  ReferenceTrajectory.rightBlock100_subset (List.mem_of_getElem? (show ReferenceResiduals.block100[0]?=some panel918.right from rfl))⟩
theorem valid919 : ValidPanel panel919 := ⟨modelCheck919,residualCheck919,
  ReferenceTrajectory.leftBlock53_subset (List.mem_of_getElem? (show ReferenceResiduals.block53[8]?=some panel919.left from rfl)),
  ReferenceTrajectory.rightBlock99_subset (List.mem_of_getElem? (show ReferenceResiduals.block99[15]?=some panel919.right from rfl))⟩
theorem valid920 : ValidPanel panel920 := ⟨modelCheck920,residualCheck920,
  ReferenceTrajectory.leftBlock53_subset (List.mem_of_getElem? (show ReferenceResiduals.block53[9]?=some panel920.left from rfl)),
  ReferenceTrajectory.rightBlock99_subset (List.mem_of_getElem? (show ReferenceResiduals.block99[14]?=some panel920.right from rfl))⟩
theorem valid921 : ValidPanel panel921 := ⟨modelCheck921,residualCheck921,
  ReferenceTrajectory.leftBlock53_subset (List.mem_of_getElem? (show ReferenceResiduals.block53[10]?=some panel921.left from rfl)),
  ReferenceTrajectory.rightBlock99_subset (List.mem_of_getElem? (show ReferenceResiduals.block99[13]?=some panel921.right from rfl))⟩
theorem valid922 : ValidPanel panel922 := ⟨modelCheck922,residualCheck922,
  ReferenceTrajectory.leftBlock53_subset (List.mem_of_getElem? (show ReferenceResiduals.block53[11]?=some panel922.left from rfl)),
  ReferenceTrajectory.rightBlock99_subset (List.mem_of_getElem? (show ReferenceResiduals.block99[12]?=some panel922.right from rfl))⟩
theorem valid923 : ValidPanel panel923 := ⟨modelCheck923,residualCheck923,
  ReferenceTrajectory.leftBlock53_subset (List.mem_of_getElem? (show ReferenceResiduals.block53[12]?=some panel923.left from rfl)),
  ReferenceTrajectory.rightBlock99_subset (List.mem_of_getElem? (show ReferenceResiduals.block99[11]?=some panel923.right from rfl))⟩
theorem valid924 : ValidPanel panel924 := ⟨modelCheck924,residualCheck924,
  ReferenceTrajectory.leftBlock53_subset (List.mem_of_getElem? (show ReferenceResiduals.block53[13]?=some panel924.left from rfl)),
  ReferenceTrajectory.rightBlock99_subset (List.mem_of_getElem? (show ReferenceResiduals.block99[10]?=some panel924.right from rfl))⟩
theorem valid925 : ValidPanel panel925 := ⟨modelCheck925,residualCheck925,
  ReferenceTrajectory.leftBlock53_subset (List.mem_of_getElem? (show ReferenceResiduals.block53[14]?=some panel925.left from rfl)),
  ReferenceTrajectory.rightBlock99_subset (List.mem_of_getElem? (show ReferenceResiduals.block99[9]?=some panel925.right from rfl))⟩
theorem valid926 : ValidPanel panel926 := ⟨modelCheck926,residualCheck926,
  ReferenceTrajectory.leftBlock53_subset (List.mem_of_getElem? (show ReferenceResiduals.block53[15]?=some panel926.left from rfl)),
  ReferenceTrajectory.rightBlock99_subset (List.mem_of_getElem? (show ReferenceResiduals.block99[8]?=some panel926.right from rfl))⟩
theorem valid927 : ValidPanel panel927 := ⟨modelCheck927,residualCheck927,
  ReferenceTrajectory.leftBlock54_subset (List.mem_of_getElem? (show ReferenceResiduals.block54[0]?=some panel927.left from rfl)),
  ReferenceTrajectory.rightBlock99_subset (List.mem_of_getElem? (show ReferenceResiduals.block99[7]?=some panel927.right from rfl))⟩
theorem validBlock28 : ∀ p∈block28,ValidPanel p := by
  simp only [block28,List.forall_mem_cons]
  exact ⟨valid896,⟨valid897,⟨valid898,⟨valid899,⟨valid900,⟨valid901,⟨valid902,⟨valid903,⟨valid904,⟨valid905,⟨valid906,⟨valid907,⟨valid908,⟨valid909,⟨valid910,⟨valid911,⟨valid912,⟨valid913,⟨valid914,⟨valid915,⟨valid916,⟨valid917,⟨valid918,⟨valid919,⟨valid920,⟨valid921,⟨valid922,⟨valid923,⟨valid924,⟨valid925,⟨valid926,⟨valid927,(by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end chebyshev2.Certificates.Compact.ContactValues

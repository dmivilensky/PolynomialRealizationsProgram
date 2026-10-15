import «2610.05164v2».Certificates.Compact.ContactBatches.Batch029
import «2610.05164v2».Certificates.Compact.ContactCoverage
import «2610.05164v2».Certificates.Compact.ReferenceTrajectoryIndex

/-!
Article: 2610.05164v2, Section 4.1.
Correspondence029.
Use: `«2610.05164v2».Certificates.Compact.ContactValues.validBlock29` feeds
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
theorem valid928 : ValidPanel panel928 := ⟨modelCheck928,residualCheck928,
  ReferenceTrajectory.leftBlock54_subset (List.mem_of_getElem? (show ReferenceResiduals.block54[1]?=some panel928.left from rfl)),
  ReferenceTrajectory.rightBlock99_subset (List.mem_of_getElem? (show ReferenceResiduals.block99[6]?=some panel928.right from rfl))⟩
theorem valid929 : ValidPanel panel929 := ⟨modelCheck929,residualCheck929,
  ReferenceTrajectory.leftBlock54_subset (List.mem_of_getElem? (show ReferenceResiduals.block54[2]?=some panel929.left from rfl)),
  ReferenceTrajectory.rightBlock99_subset (List.mem_of_getElem? (show ReferenceResiduals.block99[5]?=some panel929.right from rfl))⟩
theorem valid930 : ValidPanel panel930 := ⟨modelCheck930,residualCheck930,
  ReferenceTrajectory.leftBlock54_subset (List.mem_of_getElem? (show ReferenceResiduals.block54[3]?=some panel930.left from rfl)),
  ReferenceTrajectory.rightBlock99_subset (List.mem_of_getElem? (show ReferenceResiduals.block99[4]?=some panel930.right from rfl))⟩
theorem valid931 : ValidPanel panel931 := ⟨modelCheck931,residualCheck931,
  ReferenceTrajectory.leftBlock54_subset (List.mem_of_getElem? (show ReferenceResiduals.block54[4]?=some panel931.left from rfl)),
  ReferenceTrajectory.rightBlock99_subset (List.mem_of_getElem? (show ReferenceResiduals.block99[3]?=some panel931.right from rfl))⟩
theorem valid932 : ValidPanel panel932 := ⟨modelCheck932,residualCheck932,
  ReferenceTrajectory.leftBlock54_subset (List.mem_of_getElem? (show ReferenceResiduals.block54[5]?=some panel932.left from rfl)),
  ReferenceTrajectory.rightBlock99_subset (List.mem_of_getElem? (show ReferenceResiduals.block99[2]?=some panel932.right from rfl))⟩
theorem valid933 : ValidPanel panel933 := ⟨modelCheck933,residualCheck933,
  ReferenceTrajectory.leftBlock54_subset (List.mem_of_getElem? (show ReferenceResiduals.block54[6]?=some panel933.left from rfl)),
  ReferenceTrajectory.rightBlock99_subset (List.mem_of_getElem? (show ReferenceResiduals.block99[1]?=some panel933.right from rfl))⟩
theorem valid934 : ValidPanel panel934 := ⟨modelCheck934,residualCheck934,
  ReferenceTrajectory.leftBlock54_subset (List.mem_of_getElem? (show ReferenceResiduals.block54[7]?=some panel934.left from rfl)),
  ReferenceTrajectory.rightBlock99_subset (List.mem_of_getElem? (show ReferenceResiduals.block99[0]?=some panel934.right from rfl))⟩
theorem valid935 : ValidPanel panel935 := ⟨modelCheck935,residualCheck935,
  ReferenceTrajectory.leftBlock54_subset (List.mem_of_getElem? (show ReferenceResiduals.block54[8]?=some panel935.left from rfl)),
  ReferenceTrajectory.rightBlock98_subset (List.mem_of_getElem? (show ReferenceResiduals.block98[15]?=some panel935.right from rfl))⟩
theorem valid936 : ValidPanel panel936 := ⟨modelCheck936,residualCheck936,
  ReferenceTrajectory.leftBlock54_subset (List.mem_of_getElem? (show ReferenceResiduals.block54[9]?=some panel936.left from rfl)),
  ReferenceTrajectory.rightBlock98_subset (List.mem_of_getElem? (show ReferenceResiduals.block98[14]?=some panel936.right from rfl))⟩
theorem valid937 : ValidPanel panel937 := ⟨modelCheck937,residualCheck937,
  ReferenceTrajectory.leftBlock54_subset (List.mem_of_getElem? (show ReferenceResiduals.block54[10]?=some panel937.left from rfl)),
  ReferenceTrajectory.rightBlock98_subset (List.mem_of_getElem? (show ReferenceResiduals.block98[13]?=some panel937.right from rfl))⟩
theorem valid938 : ValidPanel panel938 := ⟨modelCheck938,residualCheck938,
  ReferenceTrajectory.leftBlock54_subset (List.mem_of_getElem? (show ReferenceResiduals.block54[11]?=some panel938.left from rfl)),
  ReferenceTrajectory.rightBlock98_subset (List.mem_of_getElem? (show ReferenceResiduals.block98[12]?=some panel938.right from rfl))⟩
theorem valid939 : ValidPanel panel939 := ⟨modelCheck939,residualCheck939,
  ReferenceTrajectory.leftBlock54_subset (List.mem_of_getElem? (show ReferenceResiduals.block54[12]?=some panel939.left from rfl)),
  ReferenceTrajectory.rightBlock98_subset (List.mem_of_getElem? (show ReferenceResiduals.block98[11]?=some panel939.right from rfl))⟩
theorem valid940 : ValidPanel panel940 := ⟨modelCheck940,residualCheck940,
  ReferenceTrajectory.leftBlock54_subset (List.mem_of_getElem? (show ReferenceResiduals.block54[13]?=some panel940.left from rfl)),
  ReferenceTrajectory.rightBlock98_subset (List.mem_of_getElem? (show ReferenceResiduals.block98[10]?=some panel940.right from rfl))⟩
theorem valid941 : ValidPanel panel941 := ⟨modelCheck941,residualCheck941,
  ReferenceTrajectory.leftBlock54_subset (List.mem_of_getElem? (show ReferenceResiduals.block54[14]?=some panel941.left from rfl)),
  ReferenceTrajectory.rightBlock98_subset (List.mem_of_getElem? (show ReferenceResiduals.block98[9]?=some panel941.right from rfl))⟩
theorem valid942 : ValidPanel panel942 := ⟨modelCheck942,residualCheck942,
  ReferenceTrajectory.leftBlock54_subset (List.mem_of_getElem? (show ReferenceResiduals.block54[15]?=some panel942.left from rfl)),
  ReferenceTrajectory.rightBlock98_subset (List.mem_of_getElem? (show ReferenceResiduals.block98[8]?=some panel942.right from rfl))⟩
theorem valid943 : ValidPanel panel943 := ⟨modelCheck943,residualCheck943,
  ReferenceTrajectory.leftBlock55_subset (List.mem_of_getElem? (show ReferenceResiduals.block55[0]?=some panel943.left from rfl)),
  ReferenceTrajectory.rightBlock98_subset (List.mem_of_getElem? (show ReferenceResiduals.block98[7]?=some panel943.right from rfl))⟩
theorem valid944 : ValidPanel panel944 := ⟨modelCheck944,residualCheck944,
  ReferenceTrajectory.leftBlock55_subset (List.mem_of_getElem? (show ReferenceResiduals.block55[1]?=some panel944.left from rfl)),
  ReferenceTrajectory.rightBlock98_subset (List.mem_of_getElem? (show ReferenceResiduals.block98[6]?=some panel944.right from rfl))⟩
theorem valid945 : ValidPanel panel945 := ⟨modelCheck945,residualCheck945,
  ReferenceTrajectory.leftBlock55_subset (List.mem_of_getElem? (show ReferenceResiduals.block55[2]?=some panel945.left from rfl)),
  ReferenceTrajectory.rightBlock98_subset (List.mem_of_getElem? (show ReferenceResiduals.block98[5]?=some panel945.right from rfl))⟩
theorem valid946 : ValidPanel panel946 := ⟨modelCheck946,residualCheck946,
  ReferenceTrajectory.leftBlock55_subset (List.mem_of_getElem? (show ReferenceResiduals.block55[3]?=some panel946.left from rfl)),
  ReferenceTrajectory.rightBlock98_subset (List.mem_of_getElem? (show ReferenceResiduals.block98[4]?=some panel946.right from rfl))⟩
theorem valid947 : ValidPanel panel947 := ⟨modelCheck947,residualCheck947,
  ReferenceTrajectory.leftBlock55_subset (List.mem_of_getElem? (show ReferenceResiduals.block55[4]?=some panel947.left from rfl)),
  ReferenceTrajectory.rightBlock98_subset (List.mem_of_getElem? (show ReferenceResiduals.block98[3]?=some panel947.right from rfl))⟩
theorem valid948 : ValidPanel panel948 := ⟨modelCheck948,residualCheck948,
  ReferenceTrajectory.leftBlock55_subset (List.mem_of_getElem? (show ReferenceResiduals.block55[5]?=some panel948.left from rfl)),
  ReferenceTrajectory.rightBlock98_subset (List.mem_of_getElem? (show ReferenceResiduals.block98[2]?=some panel948.right from rfl))⟩
theorem valid949 : ValidPanel panel949 := ⟨modelCheck949,residualCheck949,
  ReferenceTrajectory.leftBlock55_subset (List.mem_of_getElem? (show ReferenceResiduals.block55[6]?=some panel949.left from rfl)),
  ReferenceTrajectory.rightBlock98_subset (List.mem_of_getElem? (show ReferenceResiduals.block98[1]?=some panel949.right from rfl))⟩
theorem valid950 : ValidPanel panel950 := ⟨modelCheck950,residualCheck950,
  ReferenceTrajectory.leftBlock55_subset (List.mem_of_getElem? (show ReferenceResiduals.block55[7]?=some panel950.left from rfl)),
  ReferenceTrajectory.rightBlock98_subset (List.mem_of_getElem? (show ReferenceResiduals.block98[0]?=some panel950.right from rfl))⟩
theorem valid951 : ValidPanel panel951 := ⟨modelCheck951,residualCheck951,
  ReferenceTrajectory.leftBlock55_subset (List.mem_of_getElem? (show ReferenceResiduals.block55[8]?=some panel951.left from rfl)),
  ReferenceTrajectory.rightBlock97_subset (List.mem_of_getElem? (show ReferenceResiduals.block97[15]?=some panel951.right from rfl))⟩
theorem valid952 : ValidPanel panel952 := ⟨modelCheck952,residualCheck952,
  ReferenceTrajectory.leftBlock55_subset (List.mem_of_getElem? (show ReferenceResiduals.block55[9]?=some panel952.left from rfl)),
  ReferenceTrajectory.rightBlock97_subset (List.mem_of_getElem? (show ReferenceResiduals.block97[14]?=some panel952.right from rfl))⟩
theorem valid953 : ValidPanel panel953 := ⟨modelCheck953,residualCheck953,
  ReferenceTrajectory.leftBlock55_subset (List.mem_of_getElem? (show ReferenceResiduals.block55[10]?=some panel953.left from rfl)),
  ReferenceTrajectory.rightBlock97_subset (List.mem_of_getElem? (show ReferenceResiduals.block97[13]?=some panel953.right from rfl))⟩
theorem valid954 : ValidPanel panel954 := ⟨modelCheck954,residualCheck954,
  ReferenceTrajectory.leftBlock55_subset (List.mem_of_getElem? (show ReferenceResiduals.block55[11]?=some panel954.left from rfl)),
  ReferenceTrajectory.rightBlock97_subset (List.mem_of_getElem? (show ReferenceResiduals.block97[12]?=some panel954.right from rfl))⟩
theorem valid955 : ValidPanel panel955 := ⟨modelCheck955,residualCheck955,
  ReferenceTrajectory.leftBlock55_subset (List.mem_of_getElem? (show ReferenceResiduals.block55[12]?=some panel955.left from rfl)),
  ReferenceTrajectory.rightBlock97_subset (List.mem_of_getElem? (show ReferenceResiduals.block97[11]?=some panel955.right from rfl))⟩
theorem valid956 : ValidPanel panel956 := ⟨modelCheck956,residualCheck956,
  ReferenceTrajectory.leftBlock55_subset (List.mem_of_getElem? (show ReferenceResiduals.block55[13]?=some panel956.left from rfl)),
  ReferenceTrajectory.rightBlock97_subset (List.mem_of_getElem? (show ReferenceResiduals.block97[10]?=some panel956.right from rfl))⟩
theorem valid957 : ValidPanel panel957 := ⟨modelCheck957,residualCheck957,
  ReferenceTrajectory.leftBlock55_subset (List.mem_of_getElem? (show ReferenceResiduals.block55[14]?=some panel957.left from rfl)),
  ReferenceTrajectory.rightBlock97_subset (List.mem_of_getElem? (show ReferenceResiduals.block97[9]?=some panel957.right from rfl))⟩
theorem valid958 : ValidPanel panel958 := ⟨modelCheck958,residualCheck958,
  ReferenceTrajectory.leftBlock55_subset (List.mem_of_getElem? (show ReferenceResiduals.block55[15]?=some panel958.left from rfl)),
  ReferenceTrajectory.rightBlock97_subset (List.mem_of_getElem? (show ReferenceResiduals.block97[8]?=some panel958.right from rfl))⟩
theorem valid959 : ValidPanel panel959 := ⟨modelCheck959,residualCheck959,
  ReferenceTrajectory.leftBlock56_subset (List.mem_of_getElem? (show ReferenceResiduals.block56[0]?=some panel959.left from rfl)),
  ReferenceTrajectory.rightBlock97_subset (List.mem_of_getElem? (show ReferenceResiduals.block97[7]?=some panel959.right from rfl))⟩
theorem validBlock29 : ∀ p∈block29,ValidPanel p := by
  simp only [block29,List.forall_mem_cons]
  exact ⟨valid928,⟨valid929,⟨valid930,⟨valid931,⟨valid932,⟨valid933,⟨valid934,⟨valid935,⟨valid936,⟨valid937,⟨valid938,⟨valid939,⟨valid940,⟨valid941,⟨valid942,⟨valid943,⟨valid944,⟨valid945,⟨valid946,⟨valid947,⟨valid948,⟨valid949,⟨valid950,⟨valid951,⟨valid952,⟨valid953,⟨valid954,⟨valid955,⟨valid956,⟨valid957,⟨valid958,⟨valid959,(by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end «2610.05164v2».Certificates.Compact.ContactValues

import chebyshev2.Certificates.Compact.ContactBatches.Batch031
import chebyshev2.Certificates.Compact.ContactCoverage
import chebyshev2.Certificates.Compact.ReferenceTrajectoryIndex

/-!
Article: chebyshev2, Section 4.1.
Correspondence031.
Use: `chebyshev2.Certificates.Compact.ContactValues.validBlock31` feeds
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
theorem valid992 : ValidPanel panel992 := ⟨modelCheck992,residualCheck992,
  ReferenceTrajectory.leftBlock58_subset (List.mem_of_getElem? (show ReferenceResiduals.block58[1]?=some panel992.left from rfl)),
  ReferenceTrajectory.rightBlock95_subset (List.mem_of_getElem? (show ReferenceResiduals.block95[6]?=some panel992.right from rfl))⟩
theorem valid993 : ValidPanel panel993 := ⟨modelCheck993,residualCheck993,
  ReferenceTrajectory.leftBlock58_subset (List.mem_of_getElem? (show ReferenceResiduals.block58[2]?=some panel993.left from rfl)),
  ReferenceTrajectory.rightBlock95_subset (List.mem_of_getElem? (show ReferenceResiduals.block95[5]?=some panel993.right from rfl))⟩
theorem valid994 : ValidPanel panel994 := ⟨modelCheck994,residualCheck994,
  ReferenceTrajectory.leftBlock58_subset (List.mem_of_getElem? (show ReferenceResiduals.block58[3]?=some panel994.left from rfl)),
  ReferenceTrajectory.rightBlock95_subset (List.mem_of_getElem? (show ReferenceResiduals.block95[4]?=some panel994.right from rfl))⟩
theorem valid995 : ValidPanel panel995 := ⟨modelCheck995,residualCheck995,
  ReferenceTrajectory.leftBlock58_subset (List.mem_of_getElem? (show ReferenceResiduals.block58[4]?=some panel995.left from rfl)),
  ReferenceTrajectory.rightBlock95_subset (List.mem_of_getElem? (show ReferenceResiduals.block95[3]?=some panel995.right from rfl))⟩
theorem valid996 : ValidPanel panel996 := ⟨modelCheck996,residualCheck996,
  ReferenceTrajectory.leftBlock58_subset (List.mem_of_getElem? (show ReferenceResiduals.block58[5]?=some panel996.left from rfl)),
  ReferenceTrajectory.rightBlock95_subset (List.mem_of_getElem? (show ReferenceResiduals.block95[2]?=some panel996.right from rfl))⟩
theorem valid997 : ValidPanel panel997 := ⟨modelCheck997,residualCheck997,
  ReferenceTrajectory.leftBlock58_subset (List.mem_of_getElem? (show ReferenceResiduals.block58[6]?=some panel997.left from rfl)),
  ReferenceTrajectory.rightBlock95_subset (List.mem_of_getElem? (show ReferenceResiduals.block95[1]?=some panel997.right from rfl))⟩
theorem valid998 : ValidPanel panel998 := ⟨modelCheck998,residualCheck998,
  ReferenceTrajectory.leftBlock58_subset (List.mem_of_getElem? (show ReferenceResiduals.block58[7]?=some panel998.left from rfl)),
  ReferenceTrajectory.rightBlock95_subset (List.mem_of_getElem? (show ReferenceResiduals.block95[0]?=some panel998.right from rfl))⟩
theorem valid999 : ValidPanel panel999 := ⟨modelCheck999,residualCheck999,
  ReferenceTrajectory.leftBlock58_subset (List.mem_of_getElem? (show ReferenceResiduals.block58[8]?=some panel999.left from rfl)),
  ReferenceTrajectory.rightBlock94_subset (List.mem_of_getElem? (show ReferenceResiduals.block94[15]?=some panel999.right from rfl))⟩
theorem valid1000 : ValidPanel panel1000 := ⟨modelCheck1000,residualCheck1000,
  ReferenceTrajectory.leftBlock58_subset (List.mem_of_getElem? (show ReferenceResiduals.block58[9]?=some panel1000.left from rfl)),
  ReferenceTrajectory.rightBlock94_subset (List.mem_of_getElem? (show ReferenceResiduals.block94[14]?=some panel1000.right from rfl))⟩
theorem valid1001 : ValidPanel panel1001 := ⟨modelCheck1001,residualCheck1001,
  ReferenceTrajectory.leftBlock58_subset (List.mem_of_getElem? (show ReferenceResiduals.block58[10]?=some panel1001.left from rfl)),
  ReferenceTrajectory.rightBlock94_subset (List.mem_of_getElem? (show ReferenceResiduals.block94[13]?=some panel1001.right from rfl))⟩
theorem valid1002 : ValidPanel panel1002 := ⟨modelCheck1002,residualCheck1002,
  ReferenceTrajectory.leftBlock58_subset (List.mem_of_getElem? (show ReferenceResiduals.block58[11]?=some panel1002.left from rfl)),
  ReferenceTrajectory.rightBlock94_subset (List.mem_of_getElem? (show ReferenceResiduals.block94[12]?=some panel1002.right from rfl))⟩
theorem valid1003 : ValidPanel panel1003 := ⟨modelCheck1003,residualCheck1003,
  ReferenceTrajectory.leftBlock58_subset (List.mem_of_getElem? (show ReferenceResiduals.block58[12]?=some panel1003.left from rfl)),
  ReferenceTrajectory.rightBlock94_subset (List.mem_of_getElem? (show ReferenceResiduals.block94[11]?=some panel1003.right from rfl))⟩
theorem valid1004 : ValidPanel panel1004 := ⟨modelCheck1004,residualCheck1004,
  ReferenceTrajectory.leftBlock58_subset (List.mem_of_getElem? (show ReferenceResiduals.block58[13]?=some panel1004.left from rfl)),
  ReferenceTrajectory.rightBlock94_subset (List.mem_of_getElem? (show ReferenceResiduals.block94[10]?=some panel1004.right from rfl))⟩
theorem valid1005 : ValidPanel panel1005 := ⟨modelCheck1005,residualCheck1005,
  ReferenceTrajectory.leftBlock58_subset (List.mem_of_getElem? (show ReferenceResiduals.block58[14]?=some panel1005.left from rfl)),
  ReferenceTrajectory.rightBlock94_subset (List.mem_of_getElem? (show ReferenceResiduals.block94[9]?=some panel1005.right from rfl))⟩
theorem valid1006 : ValidPanel panel1006 := ⟨modelCheck1006,residualCheck1006,
  ReferenceTrajectory.leftBlock58_subset (List.mem_of_getElem? (show ReferenceResiduals.block58[15]?=some panel1006.left from rfl)),
  ReferenceTrajectory.rightBlock94_subset (List.mem_of_getElem? (show ReferenceResiduals.block94[8]?=some panel1006.right from rfl))⟩
theorem valid1007 : ValidPanel panel1007 := ⟨modelCheck1007,residualCheck1007,
  ReferenceTrajectory.leftBlock59_subset (List.mem_of_getElem? (show ReferenceResiduals.block59[0]?=some panel1007.left from rfl)),
  ReferenceTrajectory.rightBlock94_subset (List.mem_of_getElem? (show ReferenceResiduals.block94[7]?=some panel1007.right from rfl))⟩
theorem valid1008 : ValidPanel panel1008 := ⟨modelCheck1008,residualCheck1008,
  ReferenceTrajectory.leftBlock59_subset (List.mem_of_getElem? (show ReferenceResiduals.block59[1]?=some panel1008.left from rfl)),
  ReferenceTrajectory.rightBlock94_subset (List.mem_of_getElem? (show ReferenceResiduals.block94[6]?=some panel1008.right from rfl))⟩
theorem valid1009 : ValidPanel panel1009 := ⟨modelCheck1009,residualCheck1009,
  ReferenceTrajectory.leftBlock59_subset (List.mem_of_getElem? (show ReferenceResiduals.block59[2]?=some panel1009.left from rfl)),
  ReferenceTrajectory.rightBlock94_subset (List.mem_of_getElem? (show ReferenceResiduals.block94[5]?=some panel1009.right from rfl))⟩
theorem valid1010 : ValidPanel panel1010 := ⟨modelCheck1010,residualCheck1010,
  ReferenceTrajectory.leftBlock59_subset (List.mem_of_getElem? (show ReferenceResiduals.block59[3]?=some panel1010.left from rfl)),
  ReferenceTrajectory.rightBlock94_subset (List.mem_of_getElem? (show ReferenceResiduals.block94[4]?=some panel1010.right from rfl))⟩
theorem valid1011 : ValidPanel panel1011 := ⟨modelCheck1011,residualCheck1011,
  ReferenceTrajectory.leftBlock59_subset (List.mem_of_getElem? (show ReferenceResiduals.block59[4]?=some panel1011.left from rfl)),
  ReferenceTrajectory.rightBlock94_subset (List.mem_of_getElem? (show ReferenceResiduals.block94[3]?=some panel1011.right from rfl))⟩
theorem valid1012 : ValidPanel panel1012 := ⟨modelCheck1012,residualCheck1012,
  ReferenceTrajectory.leftBlock59_subset (List.mem_of_getElem? (show ReferenceResiduals.block59[5]?=some panel1012.left from rfl)),
  ReferenceTrajectory.rightBlock94_subset (List.mem_of_getElem? (show ReferenceResiduals.block94[2]?=some panel1012.right from rfl))⟩
theorem valid1013 : ValidPanel panel1013 := ⟨modelCheck1013,residualCheck1013,
  ReferenceTrajectory.leftBlock59_subset (List.mem_of_getElem? (show ReferenceResiduals.block59[6]?=some panel1013.left from rfl)),
  ReferenceTrajectory.rightBlock94_subset (List.mem_of_getElem? (show ReferenceResiduals.block94[1]?=some panel1013.right from rfl))⟩
theorem valid1014 : ValidPanel panel1014 := ⟨modelCheck1014,residualCheck1014,
  ReferenceTrajectory.leftBlock59_subset (List.mem_of_getElem? (show ReferenceResiduals.block59[7]?=some panel1014.left from rfl)),
  ReferenceTrajectory.rightBlock94_subset (List.mem_of_getElem? (show ReferenceResiduals.block94[0]?=some panel1014.right from rfl))⟩
theorem valid1015 : ValidPanel panel1015 := ⟨modelCheck1015,residualCheck1015,
  ReferenceTrajectory.leftBlock59_subset (List.mem_of_getElem? (show ReferenceResiduals.block59[8]?=some panel1015.left from rfl)),
  ReferenceTrajectory.rightBlock93_subset (List.mem_of_getElem? (show ReferenceResiduals.block93[15]?=some panel1015.right from rfl))⟩
theorem valid1016 : ValidPanel panel1016 := ⟨modelCheck1016,residualCheck1016,
  ReferenceTrajectory.leftBlock59_subset (List.mem_of_getElem? (show ReferenceResiduals.block59[9]?=some panel1016.left from rfl)),
  ReferenceTrajectory.rightBlock93_subset (List.mem_of_getElem? (show ReferenceResiduals.block93[14]?=some panel1016.right from rfl))⟩
theorem valid1017 : ValidPanel panel1017 := ⟨modelCheck1017,residualCheck1017,
  ReferenceTrajectory.leftBlock59_subset (List.mem_of_getElem? (show ReferenceResiduals.block59[10]?=some panel1017.left from rfl)),
  ReferenceTrajectory.rightBlock93_subset (List.mem_of_getElem? (show ReferenceResiduals.block93[13]?=some panel1017.right from rfl))⟩
theorem valid1018 : ValidPanel panel1018 := ⟨modelCheck1018,residualCheck1018,
  ReferenceTrajectory.leftBlock59_subset (List.mem_of_getElem? (show ReferenceResiduals.block59[11]?=some panel1018.left from rfl)),
  ReferenceTrajectory.rightBlock93_subset (List.mem_of_getElem? (show ReferenceResiduals.block93[12]?=some panel1018.right from rfl))⟩
theorem valid1019 : ValidPanel panel1019 := ⟨modelCheck1019,residualCheck1019,
  ReferenceTrajectory.leftBlock59_subset (List.mem_of_getElem? (show ReferenceResiduals.block59[12]?=some panel1019.left from rfl)),
  ReferenceTrajectory.rightBlock93_subset (List.mem_of_getElem? (show ReferenceResiduals.block93[11]?=some panel1019.right from rfl))⟩
theorem valid1020 : ValidPanel panel1020 := ⟨modelCheck1020,residualCheck1020,
  ReferenceTrajectory.leftBlock59_subset (List.mem_of_getElem? (show ReferenceResiduals.block59[13]?=some panel1020.left from rfl)),
  ReferenceTrajectory.rightBlock93_subset (List.mem_of_getElem? (show ReferenceResiduals.block93[10]?=some panel1020.right from rfl))⟩
theorem valid1021 : ValidPanel panel1021 := ⟨modelCheck1021,residualCheck1021,
  ReferenceTrajectory.leftBlock59_subset (List.mem_of_getElem? (show ReferenceResiduals.block59[14]?=some panel1021.left from rfl)),
  ReferenceTrajectory.rightBlock93_subset (List.mem_of_getElem? (show ReferenceResiduals.block93[9]?=some panel1021.right from rfl))⟩
theorem valid1022 : ValidPanel panel1022 := ⟨modelCheck1022,residualCheck1022,
  ReferenceTrajectory.leftBlock59_subset (List.mem_of_getElem? (show ReferenceResiduals.block59[15]?=some panel1022.left from rfl)),
  ReferenceTrajectory.rightBlock93_subset (List.mem_of_getElem? (show ReferenceResiduals.block93[8]?=some panel1022.right from rfl))⟩
theorem valid1023 : ValidPanel panel1023 := ⟨modelCheck1023,residualCheck1023,
  ReferenceTrajectory.leftBlock60_subset (List.mem_of_getElem? (show ReferenceResiduals.block60[0]?=some panel1023.left from rfl)),
  ReferenceTrajectory.rightBlock93_subset (List.mem_of_getElem? (show ReferenceResiduals.block93[7]?=some panel1023.right from rfl))⟩
theorem validBlock31 : ∀ p∈block31,ValidPanel p := by
  simp only [block31,List.forall_mem_cons]
  exact ⟨valid992,⟨valid993,⟨valid994,⟨valid995,⟨valid996,⟨valid997,⟨valid998,⟨valid999,⟨valid1000,⟨valid1001,⟨valid1002,⟨valid1003,⟨valid1004,⟨valid1005,⟨valid1006,⟨valid1007,⟨valid1008,⟨valid1009,⟨valid1010,⟨valid1011,⟨valid1012,⟨valid1013,⟨valid1014,⟨valid1015,⟨valid1016,⟨valid1017,⟨valid1018,⟨valid1019,⟨valid1020,⟨valid1021,⟨valid1022,⟨valid1023,(by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end chebyshev2.Certificates.Compact.ContactValues

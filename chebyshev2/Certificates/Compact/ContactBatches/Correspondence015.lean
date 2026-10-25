import chebyshev2.Certificates.Compact.ContactBatches.Batch015
import chebyshev2.Certificates.Compact.ContactCoverage
import chebyshev2.Certificates.Compact.ReferenceTrajectoryIndex

/-!
Article: chebyshev2, Section 4.1.
Correspondence015.
Use: `chebyshev2.Certificates.Compact.ContactValues.validBlock15` feeds
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
theorem valid480 : ValidPanel panel480 := ⟨modelCheck480,residualCheck480,
  ReferenceTrajectory.leftBlock27_subset (List.mem_of_getElem? (show ReferenceResiduals.block27[0]?=some panel480.left from rfl)),
  ReferenceTrajectory.rightBlock127_subset (List.mem_of_getElem? (show ReferenceResiduals.block127[6]?=some panel480.right from rfl))⟩
theorem valid481 : ValidPanel panel481 := ⟨modelCheck481,residualCheck481,
  ReferenceTrajectory.leftBlock27_subset (List.mem_of_getElem? (show ReferenceResiduals.block27[1]?=some panel481.left from rfl)),
  ReferenceTrajectory.rightBlock127_subset (List.mem_of_getElem? (show ReferenceResiduals.block127[5]?=some panel481.right from rfl))⟩
theorem valid482 : ValidPanel panel482 := ⟨modelCheck482,residualCheck482,
  ReferenceTrajectory.leftBlock27_subset (List.mem_of_getElem? (show ReferenceResiduals.block27[2]?=some panel482.left from rfl)),
  ReferenceTrajectory.rightBlock127_subset (List.mem_of_getElem? (show ReferenceResiduals.block127[4]?=some panel482.right from rfl))⟩
theorem valid483 : ValidPanel panel483 := ⟨modelCheck483,residualCheck483,
  ReferenceTrajectory.leftBlock27_subset (List.mem_of_getElem? (show ReferenceResiduals.block27[3]?=some panel483.left from rfl)),
  ReferenceTrajectory.rightBlock127_subset (List.mem_of_getElem? (show ReferenceResiduals.block127[3]?=some panel483.right from rfl))⟩
theorem valid484 : ValidPanel panel484 := ⟨modelCheck484,residualCheck484,
  ReferenceTrajectory.leftBlock27_subset (List.mem_of_getElem? (show ReferenceResiduals.block27[4]?=some panel484.left from rfl)),
  ReferenceTrajectory.rightBlock127_subset (List.mem_of_getElem? (show ReferenceResiduals.block127[2]?=some panel484.right from rfl))⟩
theorem valid485 : ValidPanel panel485 := ⟨modelCheck485,residualCheck485,
  ReferenceTrajectory.leftBlock27_subset (List.mem_of_getElem? (show ReferenceResiduals.block27[5]?=some panel485.left from rfl)),
  ReferenceTrajectory.rightBlock127_subset (List.mem_of_getElem? (show ReferenceResiduals.block127[1]?=some panel485.right from rfl))⟩
theorem valid486 : ValidPanel panel486 := ⟨modelCheck486,residualCheck486,
  ReferenceTrajectory.leftBlock27_subset (List.mem_of_getElem? (show ReferenceResiduals.block27[6]?=some panel486.left from rfl)),
  ReferenceTrajectory.rightBlock127_subset (List.mem_of_getElem? (show ReferenceResiduals.block127[0]?=some panel486.right from rfl))⟩
theorem valid487 : ValidPanel panel487 := ⟨modelCheck487,residualCheck487,
  ReferenceTrajectory.leftBlock27_subset (List.mem_of_getElem? (show ReferenceResiduals.block27[7]?=some panel487.left from rfl)),
  ReferenceTrajectory.rightBlock126_subset (List.mem_of_getElem? (show ReferenceResiduals.block126[15]?=some panel487.right from rfl))⟩
theorem valid488 : ValidPanel panel488 := ⟨modelCheck488,residualCheck488,
  ReferenceTrajectory.leftBlock27_subset (List.mem_of_getElem? (show ReferenceResiduals.block27[8]?=some panel488.left from rfl)),
  ReferenceTrajectory.rightBlock126_subset (List.mem_of_getElem? (show ReferenceResiduals.block126[14]?=some panel488.right from rfl))⟩
theorem valid489 : ValidPanel panel489 := ⟨modelCheck489,residualCheck489,
  ReferenceTrajectory.leftBlock27_subset (List.mem_of_getElem? (show ReferenceResiduals.block27[9]?=some panel489.left from rfl)),
  ReferenceTrajectory.rightBlock126_subset (List.mem_of_getElem? (show ReferenceResiduals.block126[13]?=some panel489.right from rfl))⟩
theorem valid490 : ValidPanel panel490 := ⟨modelCheck490,residualCheck490,
  ReferenceTrajectory.leftBlock27_subset (List.mem_of_getElem? (show ReferenceResiduals.block27[10]?=some panel490.left from rfl)),
  ReferenceTrajectory.rightBlock126_subset (List.mem_of_getElem? (show ReferenceResiduals.block126[12]?=some panel490.right from rfl))⟩
theorem valid491 : ValidPanel panel491 := ⟨modelCheck491,residualCheck491,
  ReferenceTrajectory.leftBlock27_subset (List.mem_of_getElem? (show ReferenceResiduals.block27[11]?=some panel491.left from rfl)),
  ReferenceTrajectory.rightBlock126_subset (List.mem_of_getElem? (show ReferenceResiduals.block126[11]?=some panel491.right from rfl))⟩
theorem valid492 : ValidPanel panel492 := ⟨modelCheck492,residualCheck492,
  ReferenceTrajectory.leftBlock27_subset (List.mem_of_getElem? (show ReferenceResiduals.block27[12]?=some panel492.left from rfl)),
  ReferenceTrajectory.rightBlock126_subset (List.mem_of_getElem? (show ReferenceResiduals.block126[10]?=some panel492.right from rfl))⟩
theorem valid493 : ValidPanel panel493 := ⟨modelCheck493,residualCheck493,
  ReferenceTrajectory.leftBlock27_subset (List.mem_of_getElem? (show ReferenceResiduals.block27[13]?=some panel493.left from rfl)),
  ReferenceTrajectory.rightBlock126_subset (List.mem_of_getElem? (show ReferenceResiduals.block126[9]?=some panel493.right from rfl))⟩
theorem valid494 : ValidPanel panel494 := ⟨modelCheck494,residualCheck494,
  ReferenceTrajectory.leftBlock27_subset (List.mem_of_getElem? (show ReferenceResiduals.block27[14]?=some panel494.left from rfl)),
  ReferenceTrajectory.rightBlock126_subset (List.mem_of_getElem? (show ReferenceResiduals.block126[8]?=some panel494.right from rfl))⟩
theorem valid495 : ValidPanel panel495 := ⟨modelCheck495,residualCheck495,
  ReferenceTrajectory.leftBlock27_subset (List.mem_of_getElem? (show ReferenceResiduals.block27[15]?=some panel495.left from rfl)),
  ReferenceTrajectory.rightBlock126_subset (List.mem_of_getElem? (show ReferenceResiduals.block126[7]?=some panel495.right from rfl))⟩
theorem valid496 : ValidPanel panel496 := ⟨modelCheck496,residualCheck496,
  ReferenceTrajectory.leftBlock28_subset (List.mem_of_getElem? (show ReferenceResiduals.block28[0]?=some panel496.left from rfl)),
  ReferenceTrajectory.rightBlock126_subset (List.mem_of_getElem? (show ReferenceResiduals.block126[6]?=some panel496.right from rfl))⟩
theorem valid497 : ValidPanel panel497 := ⟨modelCheck497,residualCheck497,
  ReferenceTrajectory.leftBlock28_subset (List.mem_of_getElem? (show ReferenceResiduals.block28[1]?=some panel497.left from rfl)),
  ReferenceTrajectory.rightBlock126_subset (List.mem_of_getElem? (show ReferenceResiduals.block126[5]?=some panel497.right from rfl))⟩
theorem valid498 : ValidPanel panel498 := ⟨modelCheck498,residualCheck498,
  ReferenceTrajectory.leftBlock28_subset (List.mem_of_getElem? (show ReferenceResiduals.block28[2]?=some panel498.left from rfl)),
  ReferenceTrajectory.rightBlock126_subset (List.mem_of_getElem? (show ReferenceResiduals.block126[4]?=some panel498.right from rfl))⟩
theorem valid499 : ValidPanel panel499 := ⟨modelCheck499,residualCheck499,
  ReferenceTrajectory.leftBlock28_subset (List.mem_of_getElem? (show ReferenceResiduals.block28[3]?=some panel499.left from rfl)),
  ReferenceTrajectory.rightBlock126_subset (List.mem_of_getElem? (show ReferenceResiduals.block126[3]?=some panel499.right from rfl))⟩
theorem valid500 : ValidPanel panel500 := ⟨modelCheck500,residualCheck500,
  ReferenceTrajectory.leftBlock28_subset (List.mem_of_getElem? (show ReferenceResiduals.block28[4]?=some panel500.left from rfl)),
  ReferenceTrajectory.rightBlock126_subset (List.mem_of_getElem? (show ReferenceResiduals.block126[2]?=some panel500.right from rfl))⟩
theorem valid501 : ValidPanel panel501 := ⟨modelCheck501,residualCheck501,
  ReferenceTrajectory.leftBlock28_subset (List.mem_of_getElem? (show ReferenceResiduals.block28[5]?=some panel501.left from rfl)),
  ReferenceTrajectory.rightBlock126_subset (List.mem_of_getElem? (show ReferenceResiduals.block126[1]?=some panel501.right from rfl))⟩
theorem valid502 : ValidPanel panel502 := ⟨modelCheck502,residualCheck502,
  ReferenceTrajectory.leftBlock28_subset (List.mem_of_getElem? (show ReferenceResiduals.block28[6]?=some panel502.left from rfl)),
  ReferenceTrajectory.rightBlock126_subset (List.mem_of_getElem? (show ReferenceResiduals.block126[0]?=some panel502.right from rfl))⟩
theorem valid503 : ValidPanel panel503 := ⟨modelCheck503,residualCheck503,
  ReferenceTrajectory.leftBlock28_subset (List.mem_of_getElem? (show ReferenceResiduals.block28[7]?=some panel503.left from rfl)),
  ReferenceTrajectory.rightBlock125_subset (List.mem_of_getElem? (show ReferenceResiduals.block125[15]?=some panel503.right from rfl))⟩
theorem valid504 : ValidPanel panel504 := ⟨modelCheck504,residualCheck504,
  ReferenceTrajectory.leftBlock28_subset (List.mem_of_getElem? (show ReferenceResiduals.block28[8]?=some panel504.left from rfl)),
  ReferenceTrajectory.rightBlock125_subset (List.mem_of_getElem? (show ReferenceResiduals.block125[14]?=some panel504.right from rfl))⟩
theorem valid505 : ValidPanel panel505 := ⟨modelCheck505,residualCheck505,
  ReferenceTrajectory.leftBlock28_subset (List.mem_of_getElem? (show ReferenceResiduals.block28[9]?=some panel505.left from rfl)),
  ReferenceTrajectory.rightBlock125_subset (List.mem_of_getElem? (show ReferenceResiduals.block125[13]?=some panel505.right from rfl))⟩
theorem valid506 : ValidPanel panel506 := ⟨modelCheck506,residualCheck506,
  ReferenceTrajectory.leftBlock28_subset (List.mem_of_getElem? (show ReferenceResiduals.block28[10]?=some panel506.left from rfl)),
  ReferenceTrajectory.rightBlock125_subset (List.mem_of_getElem? (show ReferenceResiduals.block125[12]?=some panel506.right from rfl))⟩
theorem valid507 : ValidPanel panel507 := ⟨modelCheck507,residualCheck507,
  ReferenceTrajectory.leftBlock28_subset (List.mem_of_getElem? (show ReferenceResiduals.block28[11]?=some panel507.left from rfl)),
  ReferenceTrajectory.rightBlock125_subset (List.mem_of_getElem? (show ReferenceResiduals.block125[11]?=some panel507.right from rfl))⟩
theorem valid508 : ValidPanel panel508 := ⟨modelCheck508,residualCheck508,
  ReferenceTrajectory.leftBlock28_subset (List.mem_of_getElem? (show ReferenceResiduals.block28[12]?=some panel508.left from rfl)),
  ReferenceTrajectory.rightBlock125_subset (List.mem_of_getElem? (show ReferenceResiduals.block125[10]?=some panel508.right from rfl))⟩
theorem valid509 : ValidPanel panel509 := ⟨modelCheck509,residualCheck509,
  ReferenceTrajectory.leftBlock28_subset (List.mem_of_getElem? (show ReferenceResiduals.block28[13]?=some panel509.left from rfl)),
  ReferenceTrajectory.rightBlock125_subset (List.mem_of_getElem? (show ReferenceResiduals.block125[9]?=some panel509.right from rfl))⟩
theorem valid510 : ValidPanel panel510 := ⟨modelCheck510,residualCheck510,
  ReferenceTrajectory.leftBlock28_subset (List.mem_of_getElem? (show ReferenceResiduals.block28[14]?=some panel510.left from rfl)),
  ReferenceTrajectory.rightBlock125_subset (List.mem_of_getElem? (show ReferenceResiduals.block125[8]?=some panel510.right from rfl))⟩
theorem valid511 : ValidPanel panel511 := ⟨modelCheck511,residualCheck511,
  ReferenceTrajectory.leftBlock28_subset (List.mem_of_getElem? (show ReferenceResiduals.block28[15]?=some panel511.left from rfl)),
  ReferenceTrajectory.rightBlock125_subset (List.mem_of_getElem? (show ReferenceResiduals.block125[7]?=some panel511.right from rfl))⟩
theorem validBlock15 : ∀ p∈block15,ValidPanel p := by
  simp only [block15,List.forall_mem_cons]
  exact ⟨valid480,⟨valid481,⟨valid482,⟨valid483,⟨valid484,⟨valid485,⟨valid486,⟨valid487,⟨valid488,⟨valid489,⟨valid490,⟨valid491,⟨valid492,⟨valid493,⟨valid494,⟨valid495,⟨valid496,⟨valid497,⟨valid498,⟨valid499,⟨valid500,⟨valid501,⟨valid502,⟨valid503,⟨valid504,⟨valid505,⟨valid506,⟨valid507,⟨valid508,⟨valid509,⟨valid510,⟨valid511,(by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end chebyshev2.Certificates.Compact.ContactValues

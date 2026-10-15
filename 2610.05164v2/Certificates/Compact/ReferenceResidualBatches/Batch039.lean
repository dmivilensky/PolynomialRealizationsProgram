import «2610.05164v2».Certificates.Compact.ReferenceResidualBatches.Data039

/-!
Article: 2610.05164v2, Section 4.1.
Batch039.
Use: `«2610.05164v2».Certificates.Compact.ReferenceResiduals.checks157` feeds
`«2610.05164v2».Certificates.Compact.ReferenceResiduals.checks` (checks).
Proof chain: `«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement` —
2610.05164v2, Theorem 1.2, factor 1.000013; Unconditional uniform gain comparison with the retained
numerical factor.
-/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 0
set_option maxRecDepth 200000
namespace «2610.05164v2».Certificates.Compact.ReferenceResiduals
open «2610.05164v2».Numerics.IntegerCertificate
theorem rowCheck2496 : ResidualCell.check scale ops piBounds eta row2496=true := by decide +kernel
theorem rowCheck2497 : ResidualCell.check scale ops piBounds eta row2497=true := by decide +kernel
theorem rowCheck2498 : ResidualCell.check scale ops piBounds eta row2498=true := by decide +kernel
theorem rowCheck2499 : ResidualCell.check scale ops piBounds eta row2499=true := by decide +kernel
theorem rowCheck2500 : ResidualCell.check scale ops piBounds eta row2500=true := by decide +kernel
theorem rowCheck2501 : ResidualCell.check scale ops piBounds eta row2501=true := by decide +kernel
theorem rowCheck2502 : ResidualCell.check scale ops piBounds eta row2502=true := by decide +kernel
theorem rowCheck2503 : ResidualCell.check scale ops piBounds eta row2503=true := by decide +kernel
theorem rowCheck2504 : ResidualCell.check scale ops piBounds eta row2504=true := by decide +kernel
theorem rowCheck2505 : ResidualCell.check scale ops piBounds eta row2505=true := by decide +kernel
theorem rowCheck2506 : ResidualCell.check scale ops piBounds eta row2506=true := by decide +kernel
theorem rowCheck2507 : ResidualCell.check scale ops piBounds eta row2507=true := by decide +kernel
theorem rowCheck2508 : ResidualCell.check scale ops piBounds eta row2508=true := by decide +kernel
theorem rowCheck2509 : ResidualCell.check scale ops piBounds eta row2509=true := by decide +kernel
theorem rowCheck2510 : ResidualCell.check scale ops piBounds eta row2510=true := by decide +kernel
theorem rowCheck2511 : ResidualCell.check scale ops piBounds eta row2511=true := by decide +kernel
theorem rowCheck2512 : ResidualCell.check scale ops piBounds eta row2512=true := by decide +kernel
theorem rowCheck2513 : ResidualCell.check scale ops piBounds eta row2513=true := by decide +kernel
theorem rowCheck2514 : ResidualCell.check scale ops piBounds eta row2514=true := by decide +kernel
theorem rowCheck2515 : ResidualCell.check scale ops piBounds eta row2515=true := by decide +kernel
theorem rowCheck2516 : ResidualCell.check scale ops piBounds eta row2516=true := by decide +kernel
theorem rowCheck2517 : ResidualCell.check scale ops piBounds eta row2517=true := by decide +kernel
theorem rowCheck2518 : ResidualCell.check scale ops piBounds eta row2518=true := by decide +kernel
theorem checks156 : block156.all (ResidualCell.check scale ops piBounds eta)=true := by
  simp only [block156,List.all_cons,List.all_nil,Bool.and_true,Bool.and_eq_true]
  exact ⟨rowCheck2496,⟨rowCheck2497,⟨rowCheck2498,⟨rowCheck2499,⟨rowCheck2500,⟨rowCheck2501,⟨rowCheck2502,⟨rowCheck2503,⟨rowCheck2504,⟨rowCheck2505,⟨rowCheck2506,⟨rowCheck2507,⟨rowCheck2508,⟨rowCheck2509,⟨rowCheck2510,rowCheck2511⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem checks157 : block157.all (ResidualCell.check scale ops piBounds eta)=true := by
  simp only [block157,List.all_cons,List.all_nil,Bool.and_true,Bool.and_eq_true]
  exact ⟨rowCheck2512,⟨rowCheck2513,⟨rowCheck2514,⟨rowCheck2515,⟨rowCheck2516,⟨rowCheck2517,rowCheck2518⟩⟩⟩⟩⟩⟩
end «2610.05164v2».Certificates.Compact.ReferenceResiduals

import krylov.Correction.DeepData
import krylov.Information.PreQuadraticInstance
import krylov.Information.KnownBasePlanar

/-!
Article: main_krylov, prop:deep, exact original affine source family.
Use: fix the literal rational four-dimensional source matrices, derive
their strict spectral budgets and transport the actual full family into
its genuine physical oracle scenario with the printed positive base.
Source: the original seven rational rows, exact two-block Frobenius norms,
proved spectral comparison and genuine relative form congruence invariance.
-/

namespace krylov.Correction
noncomputable section
open Matrix Finset krylov.Reference krylov.Methods krylov.Secant krylov.Stability krylov.LinearAlgebra
open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator MatrixOrder

/-- The original four-dimensional diagonal reference with eigenvalues 1, 4, 9 and 16.
Use: Fix the genuine positive reference of the source unbounded-family proposition.
Article: main_krylov, prop:deep, original four-dimensional affine source family. -/
def deepReference : Matrix (Fin 4) (Fin 4) ℝ := diagonal ![1,4,9,16]

/-- The explicit positive diagonal square root of the original four-dimensional reference.
Use: Connect the actual canonical certificate coefficients to real physical matrices.
Article: main_krylov, prop:deep, original four-dimensional affine source family. -/
def deepRoot : Matrix (Fin 4) (Fin 4) ℝ := diagonal ![1,2,3,4]

/-- The exact original diagonal reference is positive definite.
Use: Prove the genuine base metric before applying its canonical congruences.
Article: main_krylov, prop:deep, original four-dimensional affine source family.
Proof: Each of its four real diagonal entries is strictly positive. -/
theorem deepReference_posDef : deepReference.PosDef := by
  apply Matrix.posDef_diagonal_iff.mpr
  intro i
  fin_cases i <;> norm_num [deepReference]

/-- The exact explicit source square root is positive definite.
Use: Identify the explicit rational diagonal with the genuine positive functional-calculus root.
Article: main_krylov, prop:deep, original four-dimensional affine source family.
Proof: Each of the four displayed diagonal root entries is strictly positive. -/
theorem deepRoot_posDef : deepRoot.PosDef := by
  apply Matrix.posDef_diagonal_iff.mpr
  intro i
  fin_cases i <;> norm_num [deepRoot]

/-- The square of the explicit positive diagonal root is exactly the original source reference.
Use: Keep the true physical coordinate change equal to the printed rational one.
Article: main_krylov, prop:deep, original four-dimensional affine source family.
Proof: Multiply the actual two diagonal forms and verify their four exact squared entries. -/
theorem deepRoot_square : deepRoot*deepRoot=deepReference := by
  simp only [deepRoot,deepReference,diagonal_mul_diagonal]
  congr 1
  funext i
  fin_cases i <;> norm_num

/-- The genuine positive metric root of the original reference equals its exact rational diagonal root.
Use: Eliminate any assumed physical/canonical representation from the numerical source family.
Article: main_krylov, prop:deep, original four-dimensional affine source family.
Proof: Use the proved exact square and the standard positive-root square identity in continuous functional calculus. -/
theorem deepReference_root : metricRoot deepReference=deepRoot := by
  rw [metricRoot,← deepRoot_square,CFC.sqrt_mul_self deepRoot deepRoot_posDef.posSemidef.nonneg]

/-- The exact original perturbation budget one thousandth.
Use: Retain the printed primitive source scale exactly in every certificate.
Article: main_krylov, prop:deep, original four-dimensional affine source family. -/
def deepBudget : ℝ := 1/1000

/-- The original rational budget is strictly positive.
Use: Use strict scalar multiplication when deriving every primitive budget margin.
Article: main_krylov, prop:deep, original four-dimensional affine source family.
Proof: Normalize the exact rational one-thousandth inequality. -/
theorem deepBudget_pos : 0<deepBudget := by norm_num [deepBudget]

/-- The genuine original initial gradient formed by the positive reference root from the printed four canonical coordinates.
Use: Fix the actual unbounded-family execution input independently of all generated numerical data.
Article: main_krylov, prop:deep, original four-dimensional affine source family. -/
def deepInitial : EuclideanSpace ℝ (Fin 4) :=
  cgOperator deepRoot (WithLp.toLp 2 ![1,1,deepBudget^4,deepBudget^4])

/-- The original canonical increment family with its genuine affine first increment and two fixed later increments.
Use: Specify the exact source family before its real physical transport.
Article: main_krylov, prop:deep, original four-dimensional affine source family. -/
def deepIncrement (s : ℝ) (k : ℕ) : Matrix (Fin 4) (Fin 4) ℝ :=
  if k=0 then deepBudget • ((1-s) • deepSeed 0+s • deepSeed 1)
  else if k=1 then deepBudget • deepSeed 2
  else if k=2 then deepBudget • deepSeed 3 else 0

/-- The original independent canonical correction defects with zero first defect and the two fixed printed later coefficients.
Use: Retain the real correction operators of the source RFC execution.
Article: main_krylov, prop:deep, original four-dimensional affine source family. -/
def deepCorrection (k : ℕ) : Matrix (Fin 4) (Fin 4) ℝ :=
  if k=1 then deepBudget • deepSeed 4 else if k=2 then deepBudget • deepSeed 5 else 0

/-- The exact independent original canonical terminal perturbation.
Use: Use the actual final correction operator in the singular-model family.
Article: main_krylov, prop:deep, original four-dimensional affine source family. -/
def deepTerminal : Matrix (Fin 4) (Fin 4) ℝ := deepBudget • deepSeed 6

/-- Every actual canonical increment in the original affine family is symmetric.
Use: Prove source symmetry uniformly in the genuine real family parameter.
Article: main_krylov, prop:deep, original four-dimensional affine source family.
Proof: Real scalar multiplication and addition preserve the proved symmetry of the actual seven seed matrices. -/
theorem deepIncrement_isSymm (s : ℝ) (k : ℕ) : (deepIncrement s k).IsSymm := by
  unfold deepIncrement
  split_ifs
  · exact (((deepSeed_isSymm 0).smul (1-s)).add ((deepSeed_isSymm 1).smul s)).smul deepBudget
  · exact (deepSeed_isSymm 2).smul deepBudget
  · exact (deepSeed_isSymm 3).smul deepBudget
  · exact Matrix.isSymm_zero

/-- Every actual original independent correction defect is symmetric.
Use: Verify the source correction symmetry before any execution or certificate.
Article: main_krylov, prop:deep, original four-dimensional affine source family.
Proof: Each genuine nonzero branch is a real scalar multiple of its proved symmetric literal seed. -/
theorem deepCorrection_isSymm (k : ℕ) : (deepCorrection k).IsSymm := by
  unfold deepCorrection
  split_ifs
  · exact (deepSeed_isSymm 4).smul deepBudget
  · exact (deepSeed_isSymm 5).smul deepBudget
  · exact Matrix.isSymm_zero

/-- The original canonical terminal perturbation is symmetric.
Use: Verify the genuine terminal source operator symmetry.
Article: main_krylov, prop:deep, original four-dimensional affine source family.
Proof: Scalar multiplication preserves the proved symmetry of the actual terminal seed. -/
theorem deepTerminal_isSymm : deepTerminal.IsSymm := (deepSeed_isSymm 6).smul deepBudget

/-- Every original scaled literal seed has strict spectral budget below the printed perturbation budget.
Use: Verify the strict primitive budget claim using actual matrix norms.
Article: main_krylov, prop:deep, original four-dimensional affine source family.
Proof: Multiply the genuine strict unit seed bound by the positive original budget. -/
theorem deepSeed_budget (i : Fin 7) : ‖deepBudget • deepSeed i‖<deepBudget := by
  rw [norm_smul,Real.norm_of_nonneg deepBudget_pos.le]
  exact (mul_lt_mul_of_pos_left (deepSeed_norm_lt_one i) deepBudget_pos).trans_eq (mul_one _)

/-- Every original canonical increment has strict budget below one thousandth uniformly over the entire actual affine parameter interval.
Use: Verify the original independent increment budgets rather than generated interval assumptions.
Article: main_krylov, prop:deep, original four-dimensional affine source family.
Proof: The affine first branch has the proved strict convex seed bound, the next two use their exact strict seed margins, and every later branch is zero. -/
theorem deepIncrement_budget (s : ℝ) (hs : s∈Set.Icc 0 1) (k : ℕ) : ‖deepIncrement s k‖<deepBudget := by
  unfold deepIncrement
  split_ifs
  · rw [norm_smul,Real.norm_of_nonneg deepBudget_pos.le]
    exact (mul_lt_mul_of_pos_left (deep_convex_seed_norm_lt_one s hs) deepBudget_pos).trans_eq (mul_one _)
  · exact deepSeed_budget 2
  · exact deepSeed_budget 3
  · simpa only [norm_zero] using deepBudget_pos

/-- Every original independent canonical correction defect has strict budget below one thousandth.
Use: Verify every real correction perturbation in the genuine source family.
Article: main_krylov, prop:deep, original four-dimensional affine source family.
Proof: The two nonzero branches satisfy the exact strict scaled-seed bound; the zero branches use positivity of the original budget. -/
theorem deepCorrection_budget (k : ℕ) : ‖deepCorrection k‖<deepBudget := by
  unfold deepCorrection
  split_ifs
  · exact deepSeed_budget 4
  · exact deepSeed_budget 5
  · simpa only [norm_zero] using deepBudget_pos

/-- The actual original terminal canonical perturbation satisfies its strict primitive spectral budget.
Use: Verify the genuine last correction perturbation margin independently of all enclosures.
Article: main_krylov, prop:deep, original four-dimensional affine source family.
Proof: Apply the exact strict scaled-seed estimate to the literal terminal matrix. -/
theorem deepTerminal_budget : ‖deepTerminal‖<deepBudget := deepSeed_budget 6


/-- The genuine original canonical source scenario with identity base and all printed increment and correction coefficients.
Use: Represent the entire actual affine physical family in one original scenario structure.
Article: main_krylov, prop:deep, original four-dimensional affine source family. -/
def deepCanonicalScenario (s : ℝ) : krylov.Information.Scenario 4 where
  base := 1
  increment := deepIncrement s
  terminal := deepTerminal
  correction := deepCorrection

/-- The actual original physical affine source family obtained by the genuine inverse-root form transport.
Use: Execute real RFC against the source matrices after verified canonical transport.
Article: main_krylov, prop:deep, original four-dimensional affine source family. -/
def deepScenario (s : ℝ) : krylov.Information.Scenario 4 :=
  (deepCanonicalScenario s).inPhysical (metricRoot deepReference)⁻¹

/-- Every actual canonical member of the original affine family satisfies all original source admissibility budgets with exactly known identity base.
Use: Establish genuine source membership before any numerical gate or determinant certificate.
Article: main_krylov, prop:deep, original four-dimensional affine source family.
Proof: At the identity the actual relative budget is the real spectral norm. The independently proved strict increment, correction and terminal budgets imply every original admissibility constraint. -/
theorem deepCanonicalScenario_admissible (s : ℝ) (hs : s∈Set.Icc 0 1) :
    (deepCanonicalScenario s).Admissible 3 1 0 (fun _ => deepBudget) deepBudget deepBudget := by
  -- Check the true identity-base relative budgets before performing any physical transport.
  refine ⟨Matrix.PosDef.one,?_,?_,deepTerminal_isSymm,?_,?_⟩
  · change krylov.Secant.relativeBudget 1 (1-1)≤(0 : ℝ)
    simp only [sub_self,krylov.Information.relativeBudget_one,norm_zero,le_refl]
  · intro k _
    exact ⟨deepIncrement_isSymm s k,by
      change krylov.Secant.relativeBudget 1 (deepIncrement s k)≤deepBudget
      rw [krylov.Information.relativeBudget_one]
      exact (deepIncrement_budget s hs k).le⟩
  · change krylov.Secant.relativeBudget 1 deepTerminal≤deepBudget
    rw [krylov.Information.relativeBudget_one]
    exact deepTerminal_budget.le
  · intro k _
    exact ⟨deepCorrection_isSymm k,by
      change krylov.Secant.relativeBudget 1 (deepCorrection k)≤deepBudget
      rw [krylov.Information.relativeBudget_one]
      exact (deepCorrection_budget k).le⟩

/-- Every real physical member of the original affine family has exactly the printed positive base.
Use: Keep the actual unbounded family at the original fixed diagonal reference.
Article: main_krylov, prop:deep, original four-dimensional affine source family.
Proof: The genuine inverse-root transport of the identity is precisely the original physical reference. -/
theorem deepScenario_base (s : ℝ) : (deepScenario s).base=deepReference :=
  krylov.Information.inverseRootForm_one deepReference deepReference_posDef

/-- Every actual original physical affine family member satisfies all original source symmetry, known-base and individual spectral-budget constraints.
Use: Insert the genuine source family into the real admissible class without an assumed budget certificate.
Article: main_krylov, prop:deep, original four-dimensional affine source family.
Proof: Transport the completely verified canonical scenario through its genuine nonsingular inverse-root form and recover the exact original positive reference. -/
theorem deepScenario_admissible (s : ℝ) (hs : s∈Set.Icc 0 1) :
    (deepScenario s).Admissible 3 deepReference 0 (fun _ => deepBudget) deepBudget deepBudget := by
  have ht := (deepCanonicalScenario s).inPhysical_admissible 3 1 (metricRoot deepReference)⁻¹
    Matrix.PosDef.one (Matrix.isUnit_nonsing_inv_det _ (metricRoot_det_unit deepReference deepReference_posDef))
    0 (fun _ => deepBudget) deepBudget deepBudget (deepCanonicalScenario_admissible s hs)
  rw [krylov.Information.inverseRootForm_one deepReference deepReference_posDef] at ht
  exact ht

/-- The real physical source increment has exactly the original canonical affine increment under the genuine relative normalization.
Use: Link the actual oracle family to its literal certificate coefficients.
Article: main_krylov, prop:deep, original four-dimensional affine source family.
Proof: The proved positive inverse-root congruence cancellation recovers the original canonical increment exactly. -/
theorem deepScenario_increment_relative (s : ℝ) (k : ℕ) :
    relativeOperator deepReference ((deepScenario s).increment k)=deepIncrement s k :=
  krylov.Information.relativeOperator_inverseRootForm deepReference _ deepReference_posDef

/-- The actual physical terminal perturbation has exactly its original canonical seed.
Use: Identify the true final correction operator used in the certificate.
Article: main_krylov, prop:deep, original four-dimensional affine source family.
Proof: Cancel the same genuine positive inverse-root physical form transport. -/
theorem deepScenario_terminal_relative (s : ℝ) :
    relativeOperator deepReference (deepScenario s).terminal=deepTerminal :=
  krylov.Information.relativeOperator_inverseRootForm deepReference _ deepReference_posDef

/-- Every actual independent physical correction perturbation has precisely its original canonical source coefficient.
Use: Keep the true executed correction defects tied to the literal numerical family.
Article: main_krylov, prop:deep, original four-dimensional affine source family.
Proof: The real inverse-root relative form cancels the physical congruence exactly. -/
theorem deepScenario_correction_relative (s : ℝ) (k : ℕ) :
    relativeOperator deepReference ((deepScenario s).correction k)=deepCorrection k :=
  krylov.Information.relativeOperator_inverseRootForm deepReference _ deepReference_posDef

/-- The actual physical increment family is affine in the original real parameter with the two genuine endpoint physical increments.
Use: Verify that the constructed original source family is truly affine.
Article: main_krylov, prop:deep, original four-dimensional affine source family.
Proof: The first canonical branch has the displayed affine coefficients, and every fixed later branch satisfies the same affine identity. Linear physical inverse-form transport preserves that exact identity. -/
theorem deepScenario_increment_affine (s : ℝ) (k : ℕ) :
    (deepScenario s).increment k=(1-s) • (deepScenario 0).increment k+s • (deepScenario 1).increment k := by
  -- Use exact scalar source identities before applying the genuine linear physical form map.
  change krylov.Information.inverseFormMap (metricRoot deepReference)⁻¹ (deepIncrement s k)=_
  have he : deepIncrement s k=(1-s) • deepIncrement 0 k+s • deepIncrement 1 k := by
    unfold deepIncrement
    split_ifs <;> module
  rw [he,map_add,map_smul,map_smul]
  rfl

end
end krylov.Correction

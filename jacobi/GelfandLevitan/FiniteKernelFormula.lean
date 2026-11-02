import jacobi.GelfandLevitan.FiniteCoefficients

/-!
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
The genuine finite GL transformation kernel is exactly the original
finite combination sum_i a_i(t)h_i(s), with a obtained from the actual
invertible original Gram system. The statement is proved for the
original reconstruction, not introduced as a definition of a new kernel.
Use: finiteTransformationKernel_feature_formula identifies the actual reconstructed finite K with the original finite coefficient formula used for differentiation.
-/
namespace jacobi.GelfandLevitan
noncomputable section
open Real Set Filter jacobi.Reference
open scoped Topology InnerProductSpace
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] realSolution coefficientVector normingRatio norming

/-- The actual original finite spectral source kernel is exactly the weighted sum of its genuine target and reference features.
Use: finiteTransformationKernel_feature_formula identifies the actual reconstructed finite K with the original finite coefficient formula used for differentiation.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
Proof: evaluate the original finite spectral kernel, preserving its physical half coordinate. The two Bool features are precisely the original positive target and negative reference terms of each literal kernelTerm. -/
theorem finiteKernelRows_feature_formula (a : ℝ) (ha : -1<a) (N : ℕ) (t : HalfInterval) (r : Interval) :
    finiteKernelRows a ha N t r=∑ i : FeatureIndex N,finiteFeatureWeight a ha i*
      realSolution a (finiteFeatureEnergy a ha i) t*realSolution a (finiteFeatureEnergy a ha i) (halfTime r) := by
  -- The finite two-feature index keeps repeated original energies and all their true signed weights.
  change finiteKernelMap a ha N (halfInclusion t,r)=_
  rw [finiteKernelMap_apply,← Fin.sum_univ_eq_sum_range]
  simp only [FeatureIndex,Fintype.sum_prod_type,Fintype.sum_bool]
  apply Finset.sum_congr rfl
  intro k _
  change kernelTerm a ha k (min (t:ℝ) (1/2)) (halfTime r)=_
  rw [min_eq_left t.property.2,kernelTerm]
  simp only [finiteFeatureWeight,finiteFeatureEnergy,Bool.false_eq_true,ite_true,ite_false]
  ring

/-- The actual original finite Hilbert source row has exactly its original signed feature expansion.
Use: the genuine reconstruction pairing is evaluated term by term in finiteTransformationKernel_feature_formula, with its actual original L2 source coefficients.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
Proof: the proved original finite row expansion is the two-feature sum, with its true positive and negative weights; combine the identical finite indexings by real module arithmetic. -/
theorem finiteKernelRowVector_feature_formula (a : ℝ) (ha : -1<a) (N : ℕ) (s : HalfInterval) :
    finiteKernelRowVector a ha N s=∑ i : FeatureIndex N,
      (finiteFeatureWeight a ha i*realSolution a (finiteFeatureEnergy a ha i) s) • coefficientVector a ha (finiteFeatureEnergy a ha i) := by
  rw [finiteKernelRowVector_expansion,← Fin.sum_univ_eq_sum_range]
  simp only [FeatureIndex,Fintype.sum_prod_type,Fintype.sum_bool]
  apply Finset.sum_congr rfl
  intro k _
  simp only [finiteFeatureWeight,finiteFeatureEnergy,Bool.false_eq_true,ite_true,ite_false]
  module

/-- The actual original finite coefficient is the original weighted selected value plus the true inverse-row source coefficient, with its exact reconstruction sign.
Use: identifies the independently defined original finite-system inverse coefficients with the coefficients of the actual original K^(N) reconstruction.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
Proof: evaluate the actual finite coefficient system, replace genuine synthesis by its proved original inverse row, and move the true physical projection in the original Hilbert pairing using the actual inverse-row support. The genuine coefficient-vector integral gives the displayed identity. -/
theorem finiteFeatureCoefficients_value (a : ℝ) (ha : -1<a) (N : ℕ) (t : HalfInterval)
    (hA : IsUnit (finiteCompressedPositive a ha N t)) (hB : IsUnit (finiteFeatureSystem a ha N t)) (i : FeatureIndex N) :
    finiteFeatureCoefficients a ha N t i= -finiteFeatureWeight a ha i*
      (realSolution a (finiteFeatureEnergy a ha i) t+realCoefficient a (finiteSolutionRow a ha N t:Space) (finiteFeatureEnergy a ha i)) := by
  -- The original finite inverse equation, not an assumed coefficient formula, fixes every actual reconstruction coefficient.
  have he := congrArg (fun y : FeatureIndex N→ℝ => y i) (finiteFeatureCoefficients_equation a ha N t hB)
  change finiteFeatureCoefficients a ha N t i+finiteFeatureWeight a ha i*
    inner ℝ (finiteFeatureVector a ha t i) (finiteFeatureSynthesis a ha N t (finiteFeatureCoefficients a ha N t))=
      -(finiteFeatureWeight a ha i*realSolution a (finiteFeatureEnergy a ha i) t) at he
  rw [← finiteSolutionRow_feature_representation a ha N t hA hB] at he
  have hinner : inner ℝ (finiteFeatureVector a ha t i) (finiteSolutionRow a ha N t)=
      realCoefficient a (finiteSolutionRow a ha N t:Space) (finiteFeatureEnergy a ha i) := by
    calc
      _ = inner ℝ (coefficientVector a ha (finiteFeatureEnergy a ha i))
          (cutoffProjection t (finiteSolutionRow a ha N t)) := cutoffProjection_symmetric (t:ℝ) _ _
      _ = _ := by rw [finiteSolutionRow_projected a ha N t hA,coefficientVector_inner]
  rw [hinner] at he
  linarith

/-- The original reconstructed finite GL kernel is exactly its genuine finite-system coefficient expansion in the original selected solutions.
Use: the subsequent finite spatial derivatives and Darboux differential identity concern this same actual finite kernel, whose genuine uniform limit is the original K.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
Proof: expand the actual finite source and reconstruction Hilbert row. Pair the original feature vectors with the actual finite inverse row, then use the independently proved genuine finite-system coefficient identity. Real finite-sum algebra gives the original displayed kernel formula. -/
theorem finiteTransformationKernel_feature_formula (a : ℝ) (ha : -1<a) (N : ℕ) (t s : HalfInterval)
    (hA : IsUnit (finiteCompressedPositive a ha N t)) (hB : IsUnit (finiteFeatureSystem a ha N t)) :
    finiteTransformationKernel a ha N t s=∑ i : FeatureIndex N,
      finiteFeatureCoefficients a ha N t i*realSolution a (finiteFeatureEnergy a ha i) s := by
  -- Every term on both sides is the original finite spectral reconstruction or its actual original finite-system inverse coefficient.
  rw [finiteTransformationKernel,finiteKernelRows_feature_formula,finiteKernelRowVector_feature_formula,sum_inner]
  have hhalf : halfTime (halfInclusion s)=(s:ℝ) := min_eq_left s.property.2
  simp_rw [hhalf]
  rw [← Finset.sum_neg_distrib,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [real_inner_smul_left (coefficientVector a ha (finiteFeatureEnergy a ha i)) (finiteSolutionRow a ha N t)
      (finiteFeatureWeight a ha i*realSolution a (finiteFeatureEnergy a ha i) s),
    coefficientVector_inner,finiteFeatureCoefficients_value a ha N t hA hB i]
  ring

/-- The genuine original finite-kernel coefficient formula holds uniformly in physical endpoints for all sufficiently long original spectral prefixes, with both inverse conditions proved.
Use: the original finite differential calculation can use its actual finite matrix coefficients without adding any stability, finite-unit or feature-independence premise to the source theorem.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
Proof: intersect the independently proved actual finite GL and finite-system inverse thresholds and apply the exact original coefficient formula at every physical point. -/
theorem finiteTransformationKernel_feature_formula_eventually (a : ℝ) (ha : -1<a) :
    ∀ᶠ N : ℕ in atTop,∀ t s : HalfInterval,finiteTransformationKernel a ha N t s=
      ∑ i : FeatureIndex N,finiteFeatureCoefficients a ha N t i*realSolution a (finiteFeatureEnergy a ha i) s := by
  obtain ⟨B,_hB,hFinite⟩ := finiteCompressedPositive_isUnit a ha
  filter_upwards [hFinite,finiteFeatureSystem_isUnit a ha] with N hN hSystem t s
  exact finiteTransformationKernel_feature_formula a ha N t s (hN t).1 (hSystem t)

end
end jacobi.GelfandLevitan

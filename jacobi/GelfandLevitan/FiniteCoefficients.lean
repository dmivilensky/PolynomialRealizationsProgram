import jacobi.GelfandLevitan.FiniteGram
import jacobi.GelfandLevitan.FiniteIntegralEquation

/-!
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
The actual finite inverse GL row is the original feature synthesis of
the genuine finite-system inverse coefficients. The source, compressed
operator and coefficient system are all the original spectral data.
Both inverse hypotheses are discharged eventually and uniformly.
Use: the actual finite feature system is solved with precisely this original source vector to recover the genuine GL inverse row.
-/
namespace jacobi.GelfandLevitan
noncomputable section
open Real Set Filter jacobi.Reference
open scoped Topology
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] coefficientVector normingRatio norming realSolution

/-- The original weighted finite selected-solution values at their genuine physical endpoint.
Use: the actual finite feature system is solved with precisely this original source vector to recover the genuine GL inverse row.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
-/
def finiteFeatureSource (a : ℝ) (ha : -1<a) (N : ℕ) (t : ℝ) : FeatureIndex N→ℝ :=
  fun i => finiteFeatureWeight a ha i*realSolution a (finiteFeatureEnergy a ha i) t

/-- The actual finite-system inverse coefficients of the original transformation kernel.
Use: finiteSolutionRow_feature_representation identifies their genuine feature synthesis with the original finite GL inverse row, and finite kernel differentiation uses this same finite-system representation.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
-/
def finiteFeatureCoefficients (a : ℝ) (ha : -1<a) (N : ℕ) (t : ℝ) : FeatureIndex N→ℝ :=
  -(Ring.inverse (finiteFeatureSystem a ha N t) (finiteFeatureSource a ha N t))

/-- The original finite compressed source row is exactly synthesis of the actual original weighted selected-solution values.
Use: the finite-system inverse has the same original right-hand side as the genuine finite GL inverse equation.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
Proof: expand the actual finite source row into its original two spectral features. The genuine physical projection commutes with the finite sum and scalar multiplication; the unchanged two-feature source synthesis is the same original expression. -/
theorem finiteFeatureSource_synthesis (a : ℝ) (ha : -1<a) (N : ℕ) (t : HalfInterval) :
    finiteFeatureSynthesis a ha N t (finiteFeatureSource a ha N t)=
      cutoffProjection t (finiteKernelRowVector a ha N t) := by
  -- The feature representation preserves all original target and reference indices, including coincident energies.
  rw [finiteFeatureSynthesis_apply,finiteKernelRowVector_expansion,map_sum,← Fin.sum_univ_eq_sum_range]
  simp only [FeatureIndex,Fintype.sum_prod_type,Fintype.sum_bool]
  apply Finset.sum_congr rfl
  intro k _
  simp only [finiteFeatureSource,finiteFeatureWeight,finiteFeatureEnergy,finiteFeatureVector,
    Bool.false_eq_true,ite_true,ite_false,map_sub,map_smul]
  module

/-- The original finite feature synthesis intertwines the genuine compressed GL pencil and its actual finite coefficient system.
Use: synthesizing the original finite-system inverse solves the same genuine finite Hilbert equation as finiteSolutionRow.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
Proof: substitute the independently proved actual feature factorization and distribute the same synthesis map over the original identity-plus-product expression. -/
theorem finiteFeatureSystem_intertwine (a : ℝ) (ha : -1<a) (N : ℕ) (t : ℝ) (y : FeatureIndex N→ℝ) :
    finiteCompressedPositive a ha N t (finiteFeatureSynthesis a ha N t y)=
      finiteFeatureSynthesis a ha N t (finiteFeatureSystem a ha N t y) := by
  rw [← finiteFeatureFactorization]
  change finiteFeatureSynthesis a ha N t y+
    finiteFeatureSynthesis a ha N t (finiteFeatureAnalysis a ha N t (finiteFeatureSynthesis a ha N t y))=
      finiteFeatureSynthesis a ha N t (y+finiteFeatureAnalysis a ha N t (finiteFeatureSynthesis a ha N t y))
  rw [map_add]

/-- The genuine finite-system inverse coefficients solve their exact original finite Gram system.
Use: finiteSolutionRow_feature_representation identifies their true synthesis with the already constructed actual finite inverse GL row.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
Proof: evaluate the actual right inverse of the independently invertible original finite feature system at its genuine original source vector. -/
theorem finiteFeatureCoefficients_equation (a : ℝ) (ha : -1<a) (N : ℕ) (t : ℝ)
    (hu : IsUnit (finiteFeatureSystem a ha N t)) :
    finiteFeatureSystem a ha N t (finiteFeatureCoefficients a ha N t)= -finiteFeatureSource a ha N t := by
  rw [finiteFeatureCoefficients,map_neg]
  exact congrArg (fun U : (FeatureIndex N→ℝ) →L[ℝ] (FeatureIndex N→ℝ) => -(U (finiteFeatureSource a ha N t)))
    (Ring.mul_inverse_cancel _ hu)

/-- The actual original finite GL inverse row is exactly synthesis of its genuine original finite Gram-system inverse coefficients.
Use: converts the already proved actual finite GL integral solution into the original finite-dimensional coefficient representation needed for the genuine finite differential equation.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
Proof: the genuine synthesized coefficient vector solves the actual finite GL Hilbert equation by the original source identity and exact intertwining. The proved actual finite GL operator is a unit, so its injectivity identifies the two original inverse solutions. -/
theorem finiteSolutionRow_feature_representation (a : ℝ) (ha : -1<a) (N : ℕ) (t : HalfInterval)
    (hA : IsUnit (finiteCompressedPositive a ha N t)) (hB : IsUnit (finiteFeatureSystem a ha N t)) :
    finiteSolutionRow a ha N t=finiteFeatureSynthesis a ha N t (finiteFeatureCoefficients a ha N t) := by
  apply (ContinuousLinearMap.isUnit_iff_bijective.mp hA).1
  rw [finiteSolutionRow_equation a ha N t hA,finiteFeatureSystem_intertwine,
    finiteFeatureCoefficients_equation a ha N t hB,map_neg,finiteFeatureSource_synthesis]

/-- The original finite-system representation of the genuine finite inverse GL rows holds for all sufficiently long original spectral prefixes at every actual physical endpoint, with both inverse conditions discharged.
Use: original finite kernel differentiation can use the same genuine finite coefficients uniformly over the entire physical half interval.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
Proof: intersect the independently proved original finite compressed and coefficient-system unit thresholds, then apply the exact genuine inverse-row representation at each original physical endpoint. -/
theorem finiteSolutionRow_feature_representation_eventually (a : ℝ) (ha : -1<a) :
    ∀ᶠ N : ℕ in atTop,∀ t : HalfInterval,
      finiteSolutionRow a ha N t=finiteFeatureSynthesis a ha N t (finiteFeatureCoefficients a ha N t) := by
  obtain ⟨B,_hB,hFinite⟩ := finiteCompressedPositive_isUnit a ha
  filter_upwards [hFinite,finiteFeatureSystem_isUnit a ha] with N hN hSystem t
  exact finiteSolutionRow_feature_representation a ha N t (hN t).1 (hSystem t)

end
end jacobi.GelfandLevitan

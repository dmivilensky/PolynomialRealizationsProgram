import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Tactic

/-!
Article: 2610.05164v2, Theorem 2.3.
The kernel identity is proved for actual elements of L2, including x=y.
Use: `«2610.05164v2».Continuum.featureProjection_norm` feeds
`«2610.05164v2».Continuum.densityOperator_integrable` (density Operator integrable).
Proof chain: `«2610.05164v2».Packing.packed_spectral_distance` — 2610.05164v2, Theorem 2.3; Block
packing, exact masses/energy and spectral distance.
-/
namespace «2610.05164v2».Continuum
noncomputable section
open Set MeasureTheory Real
open scoped InnerProductSpace

/--
A concrete L2 realization of the exponential Gram kernel. It avoids choosing Sobolev
representatives when constructing the integral operators.

Use: `«2610.05164v2».Continuum.feature` uses this definition in the displayed construction of
`feature`. Its inputs and component formulas are fixed by that definition.

Article: 2610.05164v2, Theorem 2.4 via
`«2610.05164v2».Continuum.kernelEigenvalue_square_integral`.
-/
def rawFeature (x : ℝ) : ℝ → ℝ := (Iic x).indicator (fun t => sqrt 2 * exp (t - x))

/--
Measurability of the displayed map: `Measurable (rawFeature x)`.

Use: `«2610.05164v2».Continuum.rawFeature_memLp` uses this measurability result to establish
the precise assertion is `MemLp (rawFeature x) 2 volume`.

Article: 2610.05164v2, Theorem 2.4 via
`«2610.05164v2».Continuum.kernelEigenvalue_square_integral`.

Proof: The displayed proof term instantiates the cited result with exactly the parameters and
hypotheses of this assertion.
-/
theorem rawFeature_measurable (x : ℝ) : Measurable (rawFeature x) :=
  (by fun_prop : Measurable (fun t : ℝ => sqrt 2 * exp (t - x))).indicator measurableSet_Iic

/--
Exact identity `rawFeature x t * rawFeature y t = 2 * exp (-x - y) * (Iic (min x y)).indicator
(fun t => exp (2 * t)) t`.

Use: `«2610.05164v2».Continuum.feature_inner` rewrites with this identity to establish exact
identity `inner ℝ (feature x) (feature y) = exp (-|x - y|)`.

Article: 2610.05164v2, Theorem 2.4 via
`«2610.05164v2».Continuum.kernelEigenvalue_square_integral`.

Proof: Separate `t ≤ x` from its negation; prove the goal under each of these mutually
exclusive hypotheses.
-/
theorem rawFeature_product (x y t : ℝ) : rawFeature x t * rawFeature y t =
    2 * exp (-x - y) * (Iic (min x y)).indicator (fun t => exp (2 * t)) t := by
  -- Separate `t ≤ x` from its negation; prove the goal under each of these mutually exclusive
  -- hypotheses.
  by_cases hx : t ≤ x <;> by_cases hy : t ≤ y
  · simp only [rawFeature, indicator_of_mem (show t ∈ Iic x from hx),
      indicator_of_mem (show t ∈ Iic y from hy),
      indicator_of_mem (show t ∈ Iic (min x y) from le_min hx hy)]
    rw [show sqrt 2 * exp (t - x) * (sqrt 2 * exp (t - y)) =
      sqrt 2 ^ 2 * (exp (t - x) * exp (t - y)) by ring,
      sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), ← exp_add, mul_assoc, ← exp_add]
    congr 2
    ring
  · simp [rawFeature, hx, hy]
  · simp [rawFeature, hx, hy]
  · simp [rawFeature, hx, hy]

/--
Integrability of the displayed function: `Integrable (fun t => rawFeature x t * rawFeature y
t)`.

Use: `«2610.05164v2».Continuum.rawFeature_memLp` uses this integrability result to establish
the precise assertion is `MemLp (rawFeature x) 2 volume`.

Article: 2610.05164v2, Theorem 2.4 via
`«2610.05164v2».Continuum.kernelEigenvalue_square_integral`.

Proof: Use the identities/estimates `«2610.05164v2».Continuum.rawFeature_product` with the
arguments shown in the proof.
-/
theorem rawFeature_product_integrable (x y : ℝ) : Integrable (fun t => rawFeature x t * rawFeature y t) := by
  simp_rw [rawFeature_product]
  exact ((integrableOn_exp_mul_Iic (by norm_num : (0 : ℝ) < 2) (min x y)).integrable_indicator
    measurableSet_Iic).const_mul _

/--
The precise assertion is `MemLp (rawFeature x) 2 volume`.

Use: `«2610.05164v2».Continuum.feature` uses this assertion in the displayed construction of
`feature`. Its inputs and component formulas are fixed by that definition.

Article: 2610.05164v2, Theorem 2.4 via
`«2610.05164v2».Continuum.kernelEigenvalue_square_integral`.

Proof: Use the identities/estimates `«2610.05164v2».Continuum.rawFeature_measurable`,
`«2610.05164v2».Continuum.rawFeature_product_integrable` with the arguments shown in the proof.
-/
theorem rawFeature_memLp (x : ℝ) : MemLp (rawFeature x) 2 volume := by
  apply (memLp_two_iff_integrable_sq (rawFeature_measurable x).aestronglyMeasurable).mpr
  simpa only [pow_two] using rawFeature_product_integrable x x

/--
Defines `FeatureSpace` of type `` by `Lp ℝ 2 (volume : Measure ℝ)`.

Use: `«2610.05164v2».Continuum.atomicMatrix_operator` uses this definition to establish exact
identity `Matrix.toEuclideanCLM (𝕜 := ℝ) (n := ι) (atomicMatrix w y) = (familySynthesis
(weightedFeature w y)).adjoint ∘L familySynthesis (weightedFeature w y)`.

Article: 2610.05164v2, Theorem 2.3 via `«2610.05164v2».Packing.packed_spectral_distance`.
-/
abbrev FeatureSpace := Lp ℝ 2 (volume : Measure ℝ)
/--
Defines `feature` of type `FeatureSpace` by `(rawFeature_memLp x).toLp (rawFeature x)`.

Use: `«2610.05164v2».Continuum.feature_distance_bound` uses this definition to establish the
stated quantitative bound `‖feature x - feature y‖ ^ 2 ≤ 2 * |x - y|`.

Article: 2610.05164v2, Theorem 2.4 via
`«2610.05164v2».Continuum.kernelEigenvalue_square_integral`.
-/
def feature (x : ℝ) : FeatureSpace := (rawFeature_memLp x).toLp (rawFeature x)

/--
The precise assertion is `feature x =ᵐ[volume] rawFeature x`.

Use: `«2610.05164v2».Continuum.feature_inner` uses this identity to establish the identity
`inner ℝ (feature x) (feature y) = exp (-|x - y|)`.

Article: 2610.05164v2, Theorem 2.4 via
`«2610.05164v2».Continuum.kernelEigenvalue_square_integral`.

Proof: Use the identities/estimates `«2610.05164v2».Continuum.rawFeature_memLp` with the
arguments shown in the proof.
-/
theorem feature_coe (x : ℝ) : feature x =ᵐ[volume] rawFeature x := (rawFeature_memLp x).coeFn_toLp

/--
The kernel identity is proved for actual elements of L2, including x=y.

Exact identity `inner ℝ (feature x) (feature y) = exp (-|x - y|)`.

Use: `«2610.05164v2».Continuum.feature_distance_sq` rewrites with this identity to establish
exact identity `‖feature x - feature y‖ ^ 2 = 2 * (1 - exp (-|x - y|))`.

Article: 2610.05164v2, Theorem 2.4 via
`«2610.05164v2».Continuum.kernelEigenvalue_square_integral`.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection. Identify the summands/integrands on their required
domain before replacing the sum or integral.
-/
theorem feature_inner (x y : ℝ) : inner ℝ (feature x) (feature y) = exp (-|x - y|) := by
  -- Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
  -- at an arbitrary point in that intersection.
  rw [L2.inner_def]
  have he : (fun t => inner ℝ (feature x t) (feature y t)) =ᵐ[volume]
      (fun t => rawFeature x t * rawFeature y t) := by
    filter_upwards [feature_coe x, feature_coe y] with t hx hy
    simp [hx, hy, mul_comm]
  rw [integral_congr_ae he]
  simp_rw [rawFeature_product]
  rw [integral_const_mul, integral_indicator measurableSet_Iic,
    integral_exp_mul_Iic (by norm_num : (0 : ℝ) < 2)]
  have hm : -x - y + 2 * min x y = -|x - y| := by
    rcases le_total x y with h | h
    · rw [min_eq_left h, abs_of_nonpos (sub_nonpos.mpr h)]; ring
    · rw [min_eq_right h, abs_of_nonneg (sub_nonneg.mpr h)]; ring
  rw [show 2 * exp (-x - y) * (exp (2 * min x y) / 2) =
      exp (-x - y) * exp (2 * min x y) by ring, ← exp_add, hm]

/--
Exact identity `‖feature x‖ = 1`.

Use: `«2610.05164v2».Continuum.featureProjection_norm` rewrites with this identity to establish
exact identity `‖featureProjection x‖ = 1`.

Article: 2610.05164v2, Theorem 2.4 via
`«2610.05164v2».Continuum.kernelEigenvalue_square_integral`.

Proof: Use the identities/estimates `«2610.05164v2».Continuum.feature_inner` with the arguments
shown in the proof.
-/
theorem feature_norm (x : ℝ) : ‖feature x‖ = 1 := by
  have h := feature_inner x x
  rw [real_inner_self_eq_norm_sq] at h
  simp only [sub_self, abs_zero, neg_zero, exp_zero] at h
  nlinarith [norm_nonneg (feature x)]

/--
Exact identity `‖feature x - feature y‖ ^ 2 = 2 * (1 - exp (-|x - y|))`.

Use: `«2610.05164v2».Continuum.feature_distance_bound` rewrites with this identity to establish
the stated quantitative bound `‖feature x - feature y‖ ^ 2 ≤ 2 * |x - y|`.

Article: 2610.05164v2, Theorem 2.4 via
`«2610.05164v2».Continuum.kernelEigenvalue_square_integral`.

Proof: Use the identities/estimates `«2610.05164v2».Continuum.feature_norm`,
`«2610.05164v2».Continuum.feature_inner` with the arguments shown in the proof.
-/
theorem feature_distance_sq (x y : ℝ) :
    ‖feature x - feature y‖ ^ 2 = 2 * (1 - exp (-|x - y|)) := by
  rw [norm_sub_sq_real, feature_norm, feature_norm, feature_inner]
  ring

/--
The stated quantitative bound `‖feature x - feature y‖ ^ 2 ≤ 2 * |x - y|`.

Use: `«2610.05164v2».Continuum.feature_continuous` uses this bound to establish continuity of
the displayed function: `Continuous feature`.

Article: 2610.05164v2, Theorem 2.4 via
`«2610.05164v2».Continuum.kernelEigenvalue_square_integral`.

Proof: Use the identities/estimates `«2610.05164v2».Continuum.feature_distance_sq` with the
arguments shown in the proof.
-/
theorem feature_distance_bound (x y : ℝ) : ‖feature x - feature y‖ ^ 2 ≤ 2 * |x - y| := by
  rw [feature_distance_sq]
  linarith [one_sub_le_exp_neg |x - y|]

/--
Continuity of the displayed function: `Continuous feature`.

Use: `«2610.05164v2».Continuum.densityOperator_hasSum_trace` uses this continuity result to
establish the value of a convergent infinite sum: `HasSum (fun i => inner ℝ (b i)
(densityOperator m (b i))) (∫ x, m x)`.

Article: 2610.05164v2, Theorem 2.4 via
`«2610.05164v2».Continuum.kernelEigenvalue_square_integral`.

Proof: Use the identities/estimates `«2610.05164v2».Continuum.feature_distance_bound` with the
arguments shown in the proof.
-/
theorem feature_continuous : Continuous feature := by
  -- Use the identities/estimates `«2610.05164v2».Continuum.feature_distance_bound` with the
  -- arguments shown in the proof.
  apply Metric.continuous_iff.mpr
  intro y ε hε
  refine ⟨ε ^ 2 / 2, by positivity, ?_⟩
  intro x hx
  rw [Real.dist_eq] at hx
  rw [dist_eq_norm]
  have h := feature_distance_bound x y
  nlinarith [norm_nonneg (feature x - feature y)]

/--
Defines `featureProjection` of type `FeatureSpace →L[ℝ] FeatureSpace` by
`InnerProductSpace.rankOne ℝ (feature x) (feature x)`.

Use: `«2610.05164v2».Continuum.featureProjection_norm` rewrites with this definition to
establish exact identity `‖featureProjection x‖ = 1`.

Article: 2610.05164v2, Theorem 2.3 via `«2610.05164v2».Packing.packed_spectral_distance`.
-/
def featureProjection (x : ℝ) : FeatureSpace →L[ℝ] FeatureSpace :=
  InnerProductSpace.rankOne ℝ (feature x) (feature x)

/--
Exact identity `‖featureProjection x‖ = 1`.

Use: `«2610.05164v2».Continuum.densityOperator_integrable` rewrites with this identity to
establish integrability of the displayed function: `Integrable (fun x => m x •
featureProjection x)`.

Article: 2610.05164v2, Theorem 2.3 via `«2610.05164v2».Packing.packed_spectral_distance`.

Proof: Use the identities/estimates `«2610.05164v2».Continuum.feature_norm` with the arguments
shown in the proof.
-/
theorem featureProjection_norm (x : ℝ) : ‖featureProjection x‖ = 1 := by simp [featureProjection, feature_norm]

end
end «2610.05164v2».Continuum

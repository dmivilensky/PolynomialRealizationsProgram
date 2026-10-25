import chebyshev2.HalfLine.GreenSolution

/-!
Article: chebyshev2, Theorem 3.3.
Weighted Vector.
Use: `chebyshev2.HalfLine.vector_weighted_inner` feeds
`chebyshev2.HalfLine.responseQuadratic_eq_nonlinear` (The all-scale ODE/resolvent bridge,
including s=0 without cancellation).
Proof chain: `chebyshev2.HalfLine.commonMeasure_ode_probability` — chebyshev2, Theorem 3.3; A
common compact probability measure for all scales.
-/
namespace chebyshev2.HalfLine
noncomputable section
open Set MeasureTheory Real Filter chebyshev2.Continuum chebyshev2.GroundState
open scoped InnerProductSpace
set_option backward.isDefEq.respectTransparency false

/--
The stated quantitative bound `MemLp (fun t => sqrt (leftDensity m x t)*y t) 2 volume`.

Use: `chebyshev2.HalfLine.weightedVector` uses this identity in the displayed construction
of `weightedVector`. Its inputs and component formulas are fixed by that definition.

Article: chebyshev2, Theorem 3.3 via `chebyshev2.HalfLine.commonMeasure_ode_probability`.

Proof: Separate `t < x` from its negation; prove the goal under each of these mutually
exclusive hypotheses.
-/
theorem weighted_memLp {m y : ℝ → ℝ} (hm : Integrable m) (hn : ∀ t, 0 ≤ m t)
    (x : ℝ) (hy : AEStronglyMeasurable y volume) {C : ℝ}
    (hC : ∀ t < x, ‖y t‖ ≤ C) : MemLp (fun t => sqrt (leftDensity m x t)*y t) 2 volume := by
  -- Separate `t < x` from its negation; prove the goal under each of these mutually exclusive
  -- hypotheses.
  apply (sqrtDensity_memLp (leftDensity_integrable hm x) (leftDensity_nonneg hn x)).of_le_mul
  · exact (continuous_sqrt.comp_aestronglyMeasurable
      (leftDensity_integrable hm x).aestronglyMeasurable).mul hy
  · exact Eventually.of_forall (fun t => by
      change ‖sqrt (leftDensity m x t)*y t‖ ≤ C*‖sqrt (leftDensity m x t)‖
      by_cases ht : t < x
      · rw [norm_mul, mul_comm C]
        exact mul_le_mul_of_nonneg_left (hC t ht) (norm_nonneg _)
      · simp [leftDensity,ht])

/--
Defines `weightedVector` of type `FeatureSpace` by `(weighted_memLp hm hn x hy hC).toLp (fun t
=> sqrt (leftDensity m x t)*y t)`.

Use: `chebyshev2.HalfLine.operator_weightedVector` uses this definition to establish exact
identity `operator hm hn x (weightedVector hm hn x hy hC)=ᵐ[volume] (fun t => sqrt (leftDensity
m x t)*greenSolution x (fun z => leftDensity m x z*y z) t)`.

Article: chebyshev2, Theorem 3.3 via `chebyshev2.HalfLine.commonMeasure_ode_probability`.
-/
def weightedVector {m y : ℝ → ℝ} (hm : Integrable m) (hn : ∀ t, 0 ≤ m t)
    (x : ℝ) (hy : AEStronglyMeasurable y volume) {C : ℝ} (hC : ∀ t < x, ‖y t‖ ≤ C) : FeatureSpace :=
  (weighted_memLp hm hn x hy hC).toLp (fun t => sqrt (leftDensity m x t)*y t)

/--
Exact identity `weightedVector hm hn x hy hC=ᵐ[volume] (fun t => sqrt (leftDensity m x t)*y
t)`.

Use: `chebyshev2.HalfLine.operator_weightedVector` uses this identity to establish exact
identity `operator hm hn x (weightedVector hm hn x hy hC)=ᵐ[volume] (fun t => sqrt (leftDensity
m x t)*greenSolution x (fun z => leftDensity m x z*y z) t)`.

Article: chebyshev2, Theorem 3.3 via `chebyshev2.HalfLine.commonMeasure_ode_probability`.

Proof: Use the identities/estimates `chebyshev2.HalfLine.weighted_memLp` with the arguments
shown in the proof.
-/
theorem weightedVector_coe {m y : ℝ → ℝ} (hm : Integrable m) (hn : ∀ t, 0 ≤ m t)
    (x : ℝ) (hy : AEStronglyMeasurable y volume) {C : ℝ} (hC : ∀ t < x, ‖y t‖ ≤ C) :
    weightedVector hm hn x hy hC=ᵐ[volume] (fun t => sqrt (leftDensity m x t)*y t) :=
  (weighted_memLp hm hn x hy hC).coeFn_toLp

/--
Integrability of the displayed function: `Integrable (fun t => leftDensity m x t*y t)`.

Use: `chebyshev2.HalfLine.operator_weightedVector` rewrites with this integrability result
to establish the identity `operator hm hn x (weightedVector hm hn x hy hC)=ᵐ[volume] (fun t
=> sqrt (leftDensity m x t)*greenSolution x (fun z => leftDensity m x z*y z) t)`.

Article: chebyshev2, Theorem 3.3 via `chebyshev2.HalfLine.commonMeasure_filter`.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection.
-/
theorem weighted_forcing_integrable {m y : ℝ → ℝ} (hm : Integrable m) (hn : ∀ t, 0 ≤ m t)
    (x : ℝ) (hy : AEStronglyMeasurable y volume) {C : ℝ} (hC : ∀ t < x, ‖y t‖ ≤ C) :
    Integrable (fun t => leftDensity m x t*y t) := by
  apply (synthesis_coefficient_integrable (leftDensity_integrable hm x) (leftDensity_nonneg hn x)
    (weightedVector hm hn x hy hC)).congr
  filter_upwards [weightedVector_coe hm hn x hy hC] with t ht
  rw [ht]
  rw [← mul_assoc, ← sq, sq_sqrt (leftDensity_nonneg hn x t)]

/--
Exact identity `operator hm hn x (weightedVector hm hn x hy hC)=ᵐ[volume] (fun t => sqrt
(leftDensity m x t)*greenSolution x (fun z => leftDensity m x z*y z) t)`.

Use: `chebyshev2.HalfLine.pencil_of_green_equation` uses this identity to establish exact
identity `(ContinuousLinearMap.id ℝ FeatureSpace+s • operator hm hn x) (weightedVector hm hn x
hy hC)=vector hm hn x`.

Article: chebyshev2, Theorem 3.3 via `chebyshev2.HalfLine.commonMeasure_ode_probability`.

Proof: Separate `z < x` from its negation; prove the goal under each of these mutually
exclusive hypotheses. Intersect the eventual or almost-everywhere hypotheses, then prove the
asserted relation at an arbitrary point in that intersection. Identify the summands/integrands
on their required domain before replacing the sum or integral.
-/
theorem operator_weightedVector {m y : ℝ → ℝ} (hm : Integrable m) (hn : ∀ t, 0 ≤ m t)
    (x : ℝ) (hy : AEStronglyMeasurable y volume) {C : ℝ} (hC : ∀ t < x, ‖y t‖ ≤ C) :
    operator hm hn x (weightedVector hm hn x hy hC)=ᵐ[volume]
      (fun t => sqrt (leftDensity m x t)*greenSolution x (fun z => leftDensity m x z*y z) t) := by
  -- Separate `z < x` from its negation; prove the goal under each of these mutually exclusive
  -- hypotheses.
  filter_upwards [operator_coe hm hn x (weightedVector hm hn x hy hC)] with t ht
  rw [ht, greenSolution_integral (weighted_forcing_integrable hm hn x hy hC)]
  congr 1
  have he : (fun z => green x t z*sqrt (leftDensity m x z)*weightedVector hm hn x hy hC z)=ᵐ[volume]
      (Iio x).indicator (fun z => green x t z*(leftDensity m x z*y z)) := by
    filter_upwards [weightedVector_coe hm hn x hy hC] with z hz
    rw [hz]
    by_cases hx : z < x
    · rw [indicator_of_mem (show z ∈ Iio x from hx)]
      calc
        _ = green x t z*(sqrt (leftDensity m x z)^2*y z) := by ring
        _ = _ := by rw [sq_sqrt (leftDensity_nonneg hn x z)]
    · simp [leftDensity,hx]
  rw [integral_congr_ae he, integral_indicator measurableSet_Iio]

/--
The precise assertion is `inner ℝ (vector hm hn x) (weightedVector hm hn x hy hC)= ∫ t in Iio
x, exp (t-x)*(m t*y t)`.

Use: `chebyshev2.HalfLine.groundQuadratic_eq_coordinate` rewrites with this identity to
establish exact identity `groundQuadratic G x=G.q x`.

Article: chebyshev2, Theorem 3.3 via `chebyshev2.HalfLine.commonMeasure_ode_probability`.

Proof: Separate `t < x` from its negation; prove the goal under each of these mutually
exclusive hypotheses. Intersect the eventual or almost-everywhere hypotheses, then prove the
asserted relation at an arbitrary point in that intersection. Identify the summands/integrands
on their required domain before replacing the sum or integral.
-/
theorem vector_weighted_inner {m y : ℝ → ℝ} (hm : Integrable m) (hn : ∀ t, 0 ≤ m t)
    (x : ℝ) (hy : AEStronglyMeasurable y volume) {C : ℝ} (hC : ∀ t < x, ‖y t‖ ≤ C) :
    inner ℝ (vector hm hn x) (weightedVector hm hn x hy hC)=
      ∫ t in Iio x, exp (t-x)*(m t*y t) := by
  -- Separate `t < x` from its negation; prove the goal under each of these mutually exclusive
  -- hypotheses.
  rw [L2.inner_def, ← integral_indicator measurableSet_Iio]
  apply integral_congr_ae
  filter_upwards [vector_coe_density hm hn x, weightedVector_coe hm hn x hy hC] with t hv hw
  rw [hv,hw]
  simp only [RCLike.inner_apply,conj_trivial]
  by_cases ht : t < x
  · rw [indicator_of_mem (show t ∈ Iio x from ht)]
    simp only [leftDensity,indicator_of_mem (show t ∈ Iio x from ht)]
    calc
      _ = exp (t-x)*(sqrt (m t)^2*y t) := by ring
      _ = _ := by rw [sq_sqrt (hn t)]
  · simp [leftDensity,ht]

end
end chebyshev2.HalfLine

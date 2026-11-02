import krylov.Strings.SpectralSpace
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

/-!
Article: main_krylov, thm:value, reciprocal-total-mass spectral weight.
Use: construct the actual unit boundary vector from the distinguished atom,
its bounded trace, and the constant mode in L²(dM). Compute the genuine
orthogonal projection weight onto constants as reciprocal total mass.
Source: mathlib L² indicator inner products and one-dimensional projection.
-/

namespace krylov.Strings.Spectral
noncomputable section
open Set Filter MeasureTheory
open scoped Topology

/-- The actual left boundary vector has unit norm because the mass at zero
is exactly one. It is an L² function, not a separately supplied unit vector. -/
def boundaryVector (M : Mass) : MassHilbert M :=
  indicatorConstLp 2 (measurableSet_singleton 0) (by simp) (1 : ℂ)

theorem boundaryVector_norm (M : Mass) : ‖boundaryVector M‖ = 1 := by
  simp [boundaryVector, norm_indicatorConstLp (by norm_num : (2 : ENNReal) ≠ 0)
    (by norm_num : (2 : ENNReal) ≠ ⊤), Measure.real]

theorem boundaryVector_ne_zero (M : Mass) : boundaryVector M ≠ 0 := by
  intro h
  have hn := boundaryVector_norm M
  rw [h, norm_zero] at hn
  exact zero_ne_one hn

instance massHilbert_nontrivial (M : Mass) : Nontrivial (MassHilbert M) :=
  nontrivial_of_ne (boundaryVector M) 0 (boundaryVector_ne_zero M)

/-- Cumulative mass tends to zero at the artificial negative infinity. -/
theorem cumulative_tendsto_atBot_zero (M : Mass) : Tendsto M.cumulative atBot (𝓝 0) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_lt_atBot (0 : ℝ)] with x hx
  exact (M.negative x hx).symm

/-- A proved finite cumulative limit is the actual full Stieltjes mass,
including the distinguished unit origin atom. -/
theorem totalMass_of_cumulative_limit (M : Mass) {m : ℝ}
    (hm : Tendsto M.cumulative atTop (𝓝 m)) : M.measure univ = ENNReal.ofReal m := by
  simpa only [Mass.measure, sub_zero] using
    M.cumulative.measure_univ (cumulative_tendsto_atBot_zero M) hm

theorem finiteMass_of_cumulative_limit (M : Mass) {m : ℝ}
    (hm : Tendsto M.cumulative atTop (𝓝 m)) : IsFiniteMeasure M.measure :=
  ⟨by rw [totalMass_of_cumulative_limit M hm]; exact ENNReal.ofReal_lt_top⟩

/-- A finite limiting total mass includes at least the distinguished unit atom. -/
theorem one_le_cumulative_limit (M : Mass) {m : ℝ}
    (hm : Tendsto M.cumulative atTop (𝓝 m)) : 1 ≤ m := by
  apply ge_of_tendsto hm
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
  exact M.one_le hx

/-- The actual real total mass is the proved finite cumulative limit. -/
theorem real_totalMass_of_cumulative_limit (M : Mass) {m : ℝ}
    (hm : Tendsto M.cumulative atTop (𝓝 m)) : M.measure.real univ = m := by
  rw [Measure.real, totalMass_of_cumulative_limit M hm,
    ENNReal.toReal_ofReal (zero_le_one.trans (one_le_cumulative_limit M hm))]

/-- The bounded actual origin trace on the mass Hilbert space. -/
def boundaryTrace (M : Mass) : MassHilbert M →L[ℂ] ℂ := innerSL ℂ (boundaryVector M)

/-- The Hilbert trace is the true origin value of every L² representative,
since changes on a set of mass zero cannot change the unit atom. -/
theorem boundaryTrace_apply (M : Mass) (u : MassHilbert M) : boundaryTrace M u = u 0 := by
  rw [boundaryTrace, innerSL_apply_apply, boundaryVector, L2.inner_indicatorConstLp_one,
    integral_singleton]
  simp [Measure.real]

theorem boundaryTrace_norm (M : Mass) : ‖boundaryTrace M‖ = 1 := by
  simp [boundaryTrace, boundaryVector_norm]

/-- The actual constant mode, when the total string mass is finite. -/
def constantVector (M : Mass) [IsFiniteMeasure M.measure] : MassHilbert M :=
  indicatorConstLp 2 MeasurableSet.univ (measure_ne_top _ _) (1 : ℂ)

theorem constantVector_norm_sq (M : Mass) [IsFiniteMeasure M.measure] :
    ‖constantVector M‖ ^ 2 = M.measure.real univ := by
  have he := L2.inner_indicatorConstLp_one_indicatorConstLp_one (𝕜 := ℂ) (μ := M.measure)
    MeasurableSet.univ MeasurableSet.univ
  have hs := congrArg Complex.re he
  change (inner ℂ (constantVector M) (constantVector M)).re = _ at hs
  have hreal : RCLike.re (inner ℂ (constantVector M) (constantVector M)) = M.measure.real univ := by
    simpa using hs
  rw [inner_self_eq_norm_sq] at hreal
  exact hreal

theorem boundaryTrace_constant (M : Mass) [IsFiniteMeasure M.measure] :
    boundaryTrace M (constantVector M) = 1 := by
  change inner ℂ (boundaryVector M) (constantVector M) = 1
  rw [boundaryVector, constantVector, L2.inner_indicatorConstLp_one_indicatorConstLp_one]
  simp [Measure.real]

theorem constant_inner_boundary (M : Mass) [IsFiniteMeasure M.measure] :
    inner ℂ (constantVector M) (boundaryVector M) = 1 := by
  rw [← inner_conj_symm]
  simpa [boundaryTrace] using congrArg star (boundaryTrace_constant M)

/-- The exact reciprocal total-mass weight is a proved orthogonal projection
computation in the true mass Hilbert space. Identification with the principal
spectral atom follows only after construction of the true string resolvent. -/
theorem constant_projection_weight (M : Mass) [IsFiniteMeasure M.measure] :
    ‖(ℂ ∙ constantVector M).orthogonalProjectionOnto (boundaryVector M)‖ ^ 2 =
      (M.measure.real univ)⁻¹ := by
  have hnorm : 1 ≤ ‖constantVector M‖ := by
    have he := norm_inner_le_norm (𝕜 := ℂ) (constantVector M) (boundaryVector M)
    simpa only [constant_inner_boundary, norm_one, boundaryVector_norm, mul_one] using he
  have hmass : 0 < M.measure.real univ := by
    rw [← constantVector_norm_sq]
    positivity
  change ‖(ℂ ∙ constantVector M).starProjection (boundaryVector M)‖ ^ 2 = _
  rw [Submodule.starProjection_singleton, constant_inner_boundary, constantVector_norm_sq,
    norm_smul, norm_div, norm_one]
  change (1 / ‖(M.measure.real univ : ℂ)‖ * ‖constantVector M‖) ^ 2 = _
  rw [Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hmass, mul_pow, constantVector_norm_sq]
  field_simp

end
end krylov.Strings.Spectral

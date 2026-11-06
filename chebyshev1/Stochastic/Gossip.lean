import chebyshev1.Stochastic.IndependentCovariance
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
Independent edge dropout, with active edges divided by their activation
probability. Its exact covariance factor is `p / (1-p)`.
-/
namespace chebyshev1.Stochastic
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators

variable {Ω ι : Type*} [MeasurableSpace Ω]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- The centered relative error of a rescaled active edge. -/
def dropoutNoise (p : ℝ) (A : Set Ω) (ω : Ω) : ℝ :=
  A.indicator (1 : Ω → ℝ) ω / (1-p) - 1

theorem dropoutNoise_integrable (p : ℝ) {A : Set Ω} (hA : MeasurableSet A) :
    Integrable (dropoutNoise p A) μ := by
  exact (((integrable_const (1 : ℝ)).indicator hA).div_const _).sub (integrable_const _)

theorem dropoutNoise_mean (p : ℝ) {A : Set Ω} (hA : MeasurableSet A)
    (hprob : μ.real A = 1-p) (hp : p < 1) :
    (∫ ω, dropoutNoise p A ω ∂μ) = 0 := by
  change (∫ ω, A.indicator 1 ω / (1-p) - 1 ∂μ) = 0
  have hact : Integrable (A.indicator (1 : Ω → ℝ)) μ :=
    (integrable_const (1 : ℝ)).indicator hA
  rw [integral_sub
    (hact.div_const _) (integrable_const _),
    integral_div, integral_indicator_one hA, hprob]
  simp [ne_of_gt (sub_pos.mpr hp)]

omit [MeasurableSpace Ω] in
private theorem dropoutNoise_sq (p : ℝ) (A : Set Ω) (ω : Ω) :
    dropoutNoise p A ω ^ 2 =
      ((1-p)⁻¹ ^ 2 - 2*(1-p)⁻¹) * A.indicator (1 : Ω → ℝ) ω + 1 := by
  by_cases hω : ω ∈ A
  · simp only [dropoutNoise, Set.indicator_of_mem hω, Pi.one_apply, div_eq_mul_inv,
      one_mul, mul_one]
    ring
  · simp only [dropoutNoise, Set.indicator_of_notMem hω, zero_div, zero_sub,
      even_two.neg_pow, one_pow, mul_zero, zero_add]

theorem dropoutNoise_sq_integrable (p : ℝ) {A : Set Ω} (hA : MeasurableSet A) :
    Integrable (fun ω => dropoutNoise p A ω ^ 2) μ := by
  simp_rw [dropoutNoise_sq]
  exact (((integrable_const (1 : ℝ)).indicator hA).const_mul _).add (integrable_const _)

theorem dropoutNoise_variance (p : ℝ) {A : Set Ω} (hA : MeasurableSet A)
    (hprob : μ.real A = 1-p) (hp : p < 1) :
    (∫ ω, dropoutNoise p A ω ^ 2 ∂μ) = p/(1-p) := by
  simp_rw [dropoutNoise_sq]
  have hact : Integrable (A.indicator (1 : Ω → ℝ)) μ :=
    (integrable_const (1 : ℝ)).indicator hA
  rw [integral_add (hact.const_mul _)
      (integrable_const _), integral_const_mul, integral_indicator_one hA, hprob]
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
  have hq : 1-p ≠ 0 := ne_of_gt (sub_pos.mpr hp)
  field_simp [hq]
  ring

omit [IsProbabilityMeasure μ] in
theorem dropoutNoise_independent {A : ι → Set Ω} (hA : iIndepSet A μ) (p : ℝ) :
    iIndepFun (fun i => dropoutNoise p (A i)) μ := by
  have hi : iIndepFun (fun i => (A i).indicator (1 : Ω → ℝ)) μ :=
    hA.iIndepFun_indicator
  change iIndepFun (fun i ω => (A i).indicator 1 ω / (1-p) - 1) μ
  exact hi.comp (fun _ x => x/(1-p)-1) (by intro i; fun_prop)

variable [Fintype ι] [DecidableEq ι]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Exact one-step edge-dropout covariance in every deterministic output direction. -/
theorem dropout_sum_secondMoment (p : ℝ) (hp : p < 1) (A : ι → Set Ω)
    (hA : ∀ i, MeasurableSet (A i)) (hind : iIndepSet A μ)
    (hprob : ∀ i, μ.real (A i) = 1-p) (v : ι → E) :
    (∫ ω, ‖∑ i, dropoutNoise p (A i) ω • v i‖ ^ 2 ∂μ) =
      p/(1-p) * ∑ i, ‖v i‖ ^ 2 := by
  rw [integral_independent_centered_sum_norm_sq (dropoutNoise_independent hind p)
    (fun i => ((measurable_const.indicator (hA i)).div_const _).sub_const _)
    (fun i => dropoutNoise_integrable p (hA i))
    (fun i => dropoutNoise_sq_integrable p (hA i))
    (fun i => dropoutNoise_mean p (hA i) (hprob i) hp)]
  simp_rw [dropoutNoise_variance p (hA _) (hprob _) hp]
  exact (Finset.mul_sum ..).symm

end
end chebyshev1.Stochastic

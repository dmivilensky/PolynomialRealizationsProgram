import Mathlib.Probability.Independence.Integration
import Mathlib.Analysis.InnerProductSpace.Basic

/-! Exact covariance of a finite sum of independent centered scalar noises. -/
namespace chebyshev1.Stochastic
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators RealInnerProductSpace

variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]
variable {μ : Measure Ω} [IsProbabilityMeasure μ] {z : ι → Ω → ℝ}

omit [Fintype ι] [IsProbabilityMeasure μ] in
private theorem integrable_pair (hz : iIndepFun z μ)
    (hi : ∀ i, Integrable (z i) μ) (hi2 : ∀ i, Integrable (fun ω => z i ω ^ 2) μ)
    (i j : ι) : Integrable (fun ω => z i ω * z j ω) μ := by
  by_cases h : i = j
  · subst j
    simpa only [sq] using hi2 i
  · exact (hz.indepFun h).integrable_mul (hi i) (hi j)

omit [Fintype ι] [IsProbabilityMeasure μ] in
theorem integral_independent_centered_pair (hz : iIndepFun z μ)
    (hm : ∀ i, Measurable (z i)) (hmean : ∀ i, ∫ ω, z i ω ∂μ = 0)
    (i j : ι) :
    (∫ ω, z i ω * z j ω ∂μ) = if i = j then ∫ ω, z i ω ^ 2 ∂μ else 0 := by
  by_cases h : i = j
  · subst j
    simp [sq]
  · rw [ite_eq_right_iff.mpr (fun h' => (h h').elim),
      (hz.indepFun h).integral_fun_mul_eq_mul_integral (hm i).aestronglyMeasurable
      (hm j).aestronglyMeasurable, hmean, zero_mul]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

omit [IsProbabilityMeasure μ] in
theorem integral_independent_centered_sum_norm_sq (hz : iIndepFun z μ)
    (hm : ∀ i, Measurable (z i)) (hi : ∀ i, Integrable (z i) μ)
    (hi2 : ∀ i, Integrable (fun ω => z i ω ^ 2) μ)
    (hmean : ∀ i, ∫ ω, z i ω ∂μ = 0) (v : ι → E) :
    (∫ ω, ‖∑ i, z i ω • v i‖ ^ 2 ∂μ) =
      ∑ i, (∫ ω, z i ω ^ 2 ∂μ) * ‖v i‖ ^ 2 := by
  have hint : ∀ i j, Integrable (fun ω => (z i ω * z j ω) * ⟪v i, v j⟫) μ := by
    intro i j
    exact (integrable_pair hz hi hi2 i j).mul_const _
  have heq : (fun ω => ‖∑ i, z i ω • v i‖ ^ 2) =
      (fun ω => ∑ i, ∑ j, (z i ω * z j ω) * ⟪v i, v j⟫) := by
    funext ω
    rw [← real_inner_self_eq_norm_sq]
    simp_rw [sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [heq, integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hint i j))]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum _ (fun j _ => hint i j)]
  simp_rw [integral_mul_const, integral_independent_centered_pair hz hm hmean]
  simp

end
end chebyshev1.Stochastic

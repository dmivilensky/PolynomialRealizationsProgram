import krylov.Asymptotics.UpperLimitAlgebra

/-!
Article: main_krylov, thm:limit, the one-sided logarithmic error.
Use: interpret the printed upper big-O assertion as an actual big-O bound
on the positive part of the optimized excess. Finite cycles may grow
arbitrarily; only their condition number must diverge.
Source: the literal finite-kappa upper bound and its proved remainder.
-/

namespace krylov.Asymptotics
noncomputable section
open Real Filter Set
open krylov.Design krylov.ContinuumControl
open scoped Topology

private theorem excess_isBigO_of_upper {α : Type*} {l : Filter α}
    {I : α → chebyshev1.SpectralInterval} {V : α → ℝ} {γ B : ℝ} {σ : ℝ → ℝ}
    (hκ : Tendsto (fun a ↦ (I a).kappa) l atTop) (hγ : 0 < γ) (hB : 0 ≤ B)
    (hf : 0 ≤ feedbackValue γ σ 1) (hV : ∀ a, V a ≤ finiteDesignUpper (I a) γ B σ) :
    (fun a ↦ max (designSpacing (I a) * V a - feedbackValue γ σ 1) 0) =O[l]
      (fun a ↦ designSpacing (I a) * log (1 / designSpacing (I a))) := by
  apply Asymptotics.IsBigO.of_bound (upperRemainderConstant γ B)
  have hθ := designSpacing_tendsto_zero hκ
  filter_upwards [(tendsto_order.1 hθ).2 (exp (-1)) (exp_pos _)] with a ha
  have hb := upperRemainder_bound (I a) hγ hB ha.le
  have hv := (mul_le_mul_of_nonneg_left (hV a) (designSpacing_pos (I a)).le).trans
    (finiteDesignUpper_scaled_le (I a) hf)
  have hm : max (designSpacing (I a) * V a - feedbackValue γ σ 1) 0 ≤ upperRemainder (I a) γ B :=
    max_le (by linarith) hb.1
  have hg : 0 ≤ designSpacing (I a) * log (1 / designSpacing (I a)) := by
    have hp := designSpacing_pos (I a)
    have hsmall := ha.le.trans (exp_le_one_iff.mpr (by norm_num : (-1 : ℝ) ≤ 0))
    exact mul_nonneg hp.le (log_nonneg ((one_le_div hp).2 hsmall))
  rw [Real.norm_of_nonneg (le_max_right _ _), Real.norm_of_nonneg hg]
  exact hm.trans hb.2

/-- The literal upper-error assertion for the actual infinite optimum,
with its exact theta log(1/theta) order. -/
theorem infinitePowerValue_positive_excess_isBigO {α : Type*} {l : Filter α}
    {I : α → chebyshev1.SpectralInterval} {γ B : ℝ} {σ : ℝ → ℝ}
    (hκ : Tendsto (fun a ↦ (I a).kappa) l atTop) (hγ : 0 < γ) (hγ₁ : γ ≤ 1) (hB : 0 ≤ B)
    (hgraph : ∀ r ≥ 1, FeedbackGraphAt γ σ r)
    (hlog : ∀ r ≥ 1, 0 ≤ logSlope σ r ∧ logSlope σ r ≤ B) :
    (fun a ↦ max (designSpacing (I a) * infinitePowerValue (I a) γ - feedbackValue γ σ 1) 0) =O[l]
      (fun a ↦ designSpacing (I a) * log (1 / designSpacing (I a))) :=
  excess_isBigO_of_upper hκ hγ hB (feedbackValue_pos hγ le_rfl (hgraph 1 le_rfl).positive).le
    (fun a ↦ infinitePowerValue_sharp_upper (I a) hγ hγ₁ hB hgraph hlog)

/-- The same actual upper-error estimate holds uniformly for any chosen
finite cycle lengths, including empty finite criteria. -/
theorem optimalValue_positive_excess_isBigO {α : Type*} {l : Filter α}
    {I : α → chebyshev1.SpectralInterval} {M : α → ℕ} {γ B : ℝ} {σ : ℝ → ℝ}
    (hκ : Tendsto (fun a ↦ (I a).kappa) l atTop) (hγ : 0 < γ) (hγ₁ : γ ≤ 1) (hB : 0 ≤ B)
    (hgraph : ∀ r ≥ 1, FeedbackGraphAt γ σ r)
    (hlog : ∀ r ≥ 1, 0 ≤ logSlope σ r ∧ logSlope σ r ≤ B) :
    (fun a ↦ max (designSpacing (I a) * optimalValue (I a) (M a) (fun _ ↦ 1) γ - feedbackValue γ σ 1) 0) =O[l]
      (fun a ↦ designSpacing (I a) * log (1 / designSpacing (I a))) :=
  excess_isBigO_of_upper hκ hγ hB (feedbackValue_pos hγ le_rfl (hgraph 1 le_rfl).positive).le
    (fun a ↦ optimalValue_sharp_upper (I a) (M a) hγ hγ₁ hB hgraph hlog)

end
end krylov.Asymptotics

import nesterov.Momentum.QHM
import nesterov.Quadratic.Rate

/-!
Article: §2 tuning domain and Remark `rem:twostep`.
Use: separate the physical parameter domain from quadratic stability, and prove
the inverse translation from gradient correction without losing its strict step.
-/
namespace nesterov.Momentum
noncomputable section

structure Tuning where
  beta : ℝ
  tau : ℝ
  stepSize : ℝ
  beta_nonneg : 0≤beta
  beta_lt_one : beta<1
  tau_nonneg : 0≤tau
  step_pos : 0<stepSize

def Tuning.Stable (q : Tuning) (μ L : ℝ) : Prop :=
  Quadratic.Stable μ L q.beta q.tau q.stepSize

theorem Tuning.stable_iff (q : Tuning) {μ L : ℝ} (hμ : 0<μ) (hμL : μ<L) :
    q.Stable μ L ↔ q.stepSize*L*(1+2*q.tau)<2*(1+q.beta) :=
  Quadratic.stable_iff hμ hμL q.step_pos q.beta_nonneg q.beta_lt_one q.tau_nonneg

/-- Exact inverse of h₁=h(1+τ), h₂=hτ on the stated gradient-correction domain. -/
theorem gradientCorrection_parameters {h₁ h₂ : ℝ} (h₂₀ : 0≤h₂) (h₂₁ : h₂<h₁) :
    0<h₁-h₂ ∧ 0≤h₂/(h₁-h₂) ∧
      (h₁-h₂)*(1+h₂/(h₁-h₂))=h₁ ∧
      (h₁-h₂)*(h₂/(h₁-h₂))=h₂ := by
  have hp : 0<h₁-h₂ := sub_pos.mpr h₂₁
  refine ⟨hp,div_nonneg h₂₀ hp.le,?_,?_⟩
  · rw [mul_add,mul_one,mul_div_cancel₀ _ (ne_of_gt hp)]
    ring
  · exact mul_div_cancel₀ _ (ne_of_gt hp)

end
end nesterov.Momentum

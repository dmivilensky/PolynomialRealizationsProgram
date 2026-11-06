import nesterov.Optimal.ProductScale

/-! Actual-family O(σ) bound on every band with ξ≤bσ. -/
namespace nesterov.TwoStep
noncomputable section
open Filter
open scoped Topology

namespace Scaling
variable {A : Type*} {l : Filter A} {θ y τ : ℝ} (F : Scaling A l θ y τ)

theorem characteristic_product_bound_at_scale (c b : ℝ) (hb : 0<b)
    {σ : A→ℝ} (hscale : ∀ᶠ a in l,F.epsilon a≤σ a) :
    ∃ C : ℝ,0<C ∧ ∀ᶠ a in l,∀ ω : ℝ,
      1-Real.cos ω≤b*σ a →
      ‖Spread.product (F.tuning a) (F.epsilon a^2) 1 (1-c*F.epsilon a) ω‖≤
        C*σ a := by
  let M : ℝ := 2+|θ|+|y|+|τ|
  have hM : 1≤M := by dsimp [M];linarith [abs_nonneg θ,abs_nonneg y,abs_nonneg τ]
  have hMp : 0<M := by linarith
  have hθM : |θ|<M := by dsimp [M];linarith [abs_nonneg y,abs_nonneg τ]
  have hyM : |y|<M := by dsimp [M];linarith [abs_nonneg θ,abs_nonneg τ]
  have hτM : |τ|<M := by dsimp [M];linarith [abs_nonneg θ,abs_nonneg y]
  refine ⟨layerProductConstant c b M,?_,?_⟩
  · unfold layerProductConstant
    positivity
  · filter_upwards [F.epsilon_pos,F.epsilon_zero.eventually (eventually_lt_nhds (by norm_num : (0:ℝ)<1)),
      F.theta_tendsto.abs.eventually (eventually_lt_nhds hθM),
      F.step_tendsto.abs.eventually (eventually_lt_nhds hyM),
      F.tau_tendsto.abs.eventually (eventually_lt_nhds hτM),F.beta_eq,hscale]
      with a he he1 ht hy htau hbeta hscale
    intro ω hω
    unfold Spread.product
    rw [hbeta]
    exact product_bound_at_scale_of_compact he he1.le hscale hb hM ht.le hy.le htau.le ω hω
end Scaling
end
end nesterov.TwoStep

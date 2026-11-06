import nesterov.Robust.Rates
import nesterov.Momentum.Execution

/-! At the right design endpoint, the actual query sequence follows
gradient descent, including its first query and all later horizons. -/
namespace nesterov.Robust.Design
noncomputable section
variable (D : Robust.Design) (hG : D.kappa*(1-D.rho)=1)
include hG

theorem gd_step : D.step=1-D.rho^2 := by
  unfold step
  calc
    _=(D.kappa*(1-D.rho))*((1-D.rho)*(1+D.rho)) := by ring
    _=1-D.rho^2 := by rw [hG];ring

theorem gd_beta : D.beta=D.rho^2 := by
  unfold beta
  apply (div_eq_iff (show D.kappa-1≠0 by linarith [D.kappa_gt_one])).mpr
  linear_combination -D.rho^2*hG

theorem gd_query_step : D.step*(1+D.tau)=1 := by
  have hs := D.step_tau
  rw [D.gd_step hG,D.gd_beta hG] at hs
  rw [mul_add,mul_one,D.step_tau,D.gd_step hG,D.gd_beta hG]
  ring

theorem gd_pole : D.beta=D.tau/(1+D.tau) := by
  have hp := D.gd_query_step hG
  apply (eq_div_iff (show 1+D.tau≠0 by linarith [D.tau_nonneg])).mpr
  rw [←D.step_tau]
  calc
    _=D.tau*(D.step*(1+D.tau)) := by ring
    _=D.tau := by rw [hp,mul_one]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem gd_queries (g : E→E) (x₀ : E) (n : ℕ) :
    Momentum.queryIterate g D.beta D.tau D.step x₀ (n+1)=
      Momentum.queryIterate g D.beta D.tau D.step x₀ n-
        g (Momentum.queryIterate g D.beta D.tau D.step x₀ n) := by
  induction n with
  | zero =>
    rw [Momentum.queryIterate_one,Momentum.queryIterate_zero,D.gd_query_step hG,one_smul]
  | succ n ih =>
    rw [show n+1+1=n+2 by omega,Momentum.queryIterate_recurrence,D.gd_query_step hG,
      one_smul,D.step_tau]
    rw [ih]
    module

end
end nesterov.Robust.Design

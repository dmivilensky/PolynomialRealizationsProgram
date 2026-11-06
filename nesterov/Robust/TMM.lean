import nesterov.Robust.Rates
import nesterov.Flow.Constants

/-! TMM is the left endpoint of the robust design interval. Its finite
condition-number factor and physical coefficients are literal identities. -/
namespace nesterov.Robust
noncomputable section
open Set Filter
open scoped Topology

def tmmDesign (κ : ℝ) (hκ : 1<κ) : Design :=
  ofInterval κ (1-1/Real.sqrt κ) hκ (by
    refine ⟨le_rfl,?_⟩
    have hs : 0<Real.sqrt κ := Real.sqrt_pos.mpr (by linarith)
    have hsκ : Real.sqrt κ≤κ := Real.sqrt_le_self_iff.mpr (Or.inr hκ.le)
    have hi := one_div_le_one_div_of_le hs hsκ
    linarith)

theorem tmm_design_equality (κ : ℝ) (hκ : 1<κ) :
    (tmmDesign κ hκ).kappa*(1-(tmmDesign κ hκ).rho)^2=1 := by
  change κ*(1-(1-1/Real.sqrt κ))^2=1
  rw [sub_sub_cancel,div_pow,one_pow,Real.sq_sqrt (by linarith : 0≤κ)]
  exact mul_one_div_cancel (by linarith : κ≠0)

namespace Design
variable (D : Design) (hT : D.kappa*(1-D.rho)^2=1)
include hT

theorem tmm_step : D.step=1+D.rho := by
  unfold step
  rw [hT,one_mul]

theorem tmm_zL : D.zL=-D.rho := by
  rw [zL,D.tmm_step hT]
  ring

theorem tmm_kappa : D.kappa=1/(1-D.rho)^2 := by
  exact (eq_div_iff (sq_pos_of_pos D.gap_pos).ne').mpr hT

theorem tmm_beta : D.beta=D.rho^2/(2-D.rho) := by
  unfold beta
  apply (div_eq_div_iff (show D.kappa-1≠0 by linarith [D.kappa_gt_one])
    (show 2-D.rho≠0 by linarith [D.rho_lt_one])).mpr
  linear_combination -D.rho^2*hT

theorem tmm_tau : D.tau=D.rho^2/((1+D.rho)*(2-D.rho)) := by
  have hs := D.step_tau
  rw [D.tmm_step hT,D.tmm_beta hT] at hs
  have hp : 1+D.rho≠0 := by linarith [D.rho_pos]
  apply (eq_div_iff (mul_ne_zero hp (show 2-D.rho≠0 by linarith [D.rho_lt_one]))).mpr
  have he := (eq_div_iff (show 2-D.rho≠0 by linarith [D.rho_lt_one])).mp hs
  nlinarith

theorem tmm_deficit : 1/2-D.tau=
    (1-D.rho)*(2+3*D.rho)/(2*(2+D.rho-D.rho^2)) := by
  rw [D.tmm_tau hT]
  have hp : 1+D.rho≠0 := by linarith [D.rho_pos]
  have ht : 2-D.rho≠0 := by linarith [D.rho_lt_one]
  have hd : 2+D.rho-D.rho^2=(1+D.rho)*(2-D.rho) := by ring
  rw [hd]
  field_simp [hp,ht]
  ring

theorem tmm_tau_lt_half : D.tau<1/2 := by
  have he := D.tmm_deficit hT
  have hp : 0<2+D.rho-D.rho^2 := by
    have hh := mul_pos (show 0<1+D.rho by linarith [D.rho_pos])
      (show 0<2-D.rho by linarith [D.rho_lt_one])
    nlinarith
  have hh : 0<(1-D.rho)*(2+3*D.rho)/(2*(2+D.rho-D.rho^2)) := by
    apply div_pos
    · exact mul_pos D.gap_pos (by linarith [D.rho_pos])
    · positivity
  linarith

theorem tmm_zero_symbol (ω : ℝ) :
    ((1-TwoStep.circle D.rho ω)*Quadratic.characteristic D.beta D.tau D.step (1/D.kappa)
      (TwoStep.circle D.rho ω)*star (Quadratic.characteristic D.beta D.tau D.step 1
        (TwoStep.circle D.rho ω))).re=0 := by
  rw [D.design_symbol,hT,sub_self,mul_zero,zero_mul,zero_mul]

end Design

theorem tmm_exact_rates (κ : ℝ) (hκ : 1<κ) :
    Momentum.momentumRate (tmmDesign κ hκ).beta (tmmDesign κ hκ).tau
      (tmmDesign κ hκ).step (tmmDesign κ hκ).step_pos.ne' (1/κ) 1=1-1/Real.sqrt κ ∧
    Momentum.momentumRestRate (tmmDesign κ hκ).beta (tmmDesign κ hκ).tau
      (tmmDesign κ hκ).step (tmmDesign κ hκ).step_pos.ne' (1/κ) 1=1-1/Real.sqrt κ ∧
    Quadratic.quadraticRate (1/κ) 1 (tmmDesign κ hκ).beta (tmmDesign κ hκ).tau
      (tmmDesign κ hκ).step=1-1/Real.sqrt κ :=
  (tmmDesign κ hκ).exact_rates

end
end nesterov.Robust

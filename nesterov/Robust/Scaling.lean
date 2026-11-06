import nesterov.Robust.Rates
import nesterov.Momentum.Scaling

/-! Exact transfer of robust momentum to arbitrary positive smoothness L,
including both literal initialized rates and the scalar quadratic maximum. -/
namespace nesterov.Robust.Design
noncomputable section
open Set
variable (D : Robust.Design) {L : ℝ} (hL : 0<L)

def scaledTuning : Momentum.Tuning where
  beta := D.beta
  tau := D.tau
  stepSize := D.step/L
  beta_nonneg := D.beta_nonneg
  beta_lt_one := D.beta_lt_one
  tau_nonneg := D.tau_nonneg
  step_pos := div_pos D.step_pos hL

theorem scaled_characteristic (lam : ℝ) (z : ℂ) :
    Quadratic.characteristic D.beta D.tau (D.step/L) lam z=
      Quadratic.characteristic D.beta D.tau D.step (lam/L) z := by
  unfold Quadratic.characteristic Quadratic.queryPolynomial
  push_cast
  ring

theorem scaled_exact_rates :
    Momentum.momentumRate D.beta D.tau (D.step/L) (div_pos D.step_pos hL).ne' (L/D.kappa) L=D.rho ∧
      Momentum.momentumRestRate D.beta D.tau (D.step/L) (div_pos D.step_pos hL).ne' (L/D.kappa) L=D.rho ∧
      Quadratic.quadraticRate (L/D.kappa) L D.beta D.tau (D.step/L)=D.rho := by
  have hs : D.step/L*L=D.step := div_mul_cancel₀ _ hL.ne'
  have hμ : (L/D.kappa)/L=1/D.kappa := by field_simp
  have hf := Momentum.momentumRate_normalized D.beta D.tau (D.step/L) (L/D.kappa) L
    (div_pos D.step_pos hL).ne' hL
  simp only [hs,hμ,D.exact_rates.1] at hf
  have hr := Momentum.momentumRestRate_normalized D.beta D.tau (D.step/L) (L/D.kappa) L
    (div_pos D.step_pos hL).ne' hL
  simp only [hs,hμ,D.exact_rates.2.1] at hr
  have hμp : 0<L/D.kappa := div_pos hL D.kappa_pos
  have hμL : L/D.kappa<L := (div_lt_self hL D.kappa_gt_one)
  have hroot : Quadratic.characteristic D.beta D.tau (D.step/L) (L/D.kappa) (D.rho:ℂ)=0 := by
    rw [D.scaled_characteristic,hμ]
    exact D.root_design
  have hqlo := Quadratic.root_norm_le_rate_general hμL.le (left_mem_Icc.mpr hμL.le) hroot
  have hqhi := Momentum.quadraticRate_le_momentumRate (β:=D.beta) (τ:=D.tau)
    (div_pos D.step_pos hL).ne' hμp hμL
  rw [←hf] at hqhi
  have hnorm : ‖(D.rho:ℂ)‖=D.rho := by
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos D.rho_pos]
  rw [hnorm] at hqlo
  exact ⟨hf.symm,hr.symm,le_antisymm hqhi hqlo⟩

theorem scaled_stable : (D.scaledTuning hL).Stable (L/D.kappa) L := by
  apply (Quadratic.stable_iff_quadraticRate_lt_one
    (show L/D.kappa≤L from (div_lt_self hL D.kappa_gt_one).le)).mpr
  change Quadratic.quadraticRate (L/D.kappa) L D.beta D.tau (D.step/L)<1
  rw [(D.scaled_exact_rates hL).2.2]
  exact D.rho_lt_one

end
end nesterov.Robust.Design

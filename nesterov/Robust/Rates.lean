import nesterov.Robust.Characteristics
import nesterov.Phase.Separate
import nesterov.Realization.RestQuadratic

/-! Exact actual full, from-rest and quadratic factors at every finite
condition number in the robust-momentum design interval. -/
namespace nesterov.Robust.Design
noncomputable section
open Set
variable (D : Robust.Design)

theorem roots_mu_lt {r : ℝ} (hr : D.rho<r) {z : ℂ}
    (hz : Quadratic.characteristic D.beta D.tau D.step (1/D.kappa) z=0) : ‖z‖<r := by
  rw [D.characteristic_mu,mul_eq_zero,sub_eq_zero,sub_eq_zero] at hz
  rcases hz with rfl|rfl
  · simpa only [Complex.norm_real,Real.norm_eq_abs,abs_of_pos D.rho_pos] using hr
  · rw [norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos D.rho_pos]
    have hh : D.rho^2<D.rho := by nlinarith [D.rho_pos,D.rho_lt_one]
    exact hh.trans hr

theorem positive_circle {r : ℝ} (hr : D.rho<r) (hr1 : r<1)
    {z : ℂ} (hz : ‖z‖=r) :
    0<((1-z)*Quadratic.characteristic D.beta D.tau D.step (1/D.kappa) z*
      star (Quadratic.characteristic D.beta D.tau D.step 1 z)).re := by
  have he : TwoStep.circle r z.arg=z := by
    simpa only [TwoStep.circle,polyak.Waves.z,mul_zero,Real.exp_zero,one_mul,Complex.ofReal_zero,zero_add,hz]
      using Complex.norm_mul_exp_arg_mul_I z
  rw [←he,D.symbol_circle]
  exact Robust.symbol_pos D.rho_pos D.rho_lt_one hr hr1 D.zL_bounds
    ⟨sub_nonneg.mpr (Real.cos_le_one _),by linarith [Real.neg_one_le_cos z.arg]⟩

theorem rate_lt_radius {r : ℝ} (hr : D.rho<r) (hr1 : r<1) :
    Momentum.momentumRate D.beta D.tau D.step D.step_pos.ne' (1/D.kappa) 1<r := by
  exact (Phase.separate D.tuning D.mu_pos D.mu_lt_one
    ⟨D.rho_pos.trans hr,hr1⟩ (fun _ hz=>D.positive_circle hr hr1 hz)
    (fun _ hz=>D.roots_mu_lt hr hz)).2.2.2

theorem rate_le :
    Momentum.momentumRate D.beta D.tau D.step D.step_pos.ne' (1/D.kappa) 1≤D.rho := by
  by_contra hn
  have hρrate : D.rho<Momentum.momentumRate D.beta D.tau D.step D.step_pos.ne'
      (1/D.kappa) 1 := lt_of_not_ge hn
  obtain ⟨r,hr,hrm⟩ := exists_between (lt_min hρrate D.rho_lt_one)
  exact (D.rate_lt_radius hr (hrm.trans_le (min_le_right _ _))).not_ge
    (hrm.le.trans (min_le_left _ _))

theorem root_design :
    Quadratic.characteristic D.beta D.tau D.step (1/D.kappa) (D.rho:ℂ)=0 := by
  rw [D.characteristic_mu,sub_self,zero_mul]

theorem quadratic_rate_ge :
    D.rho≤Quadratic.quadraticRate (1/D.kappa) 1 D.beta D.tau D.step := by
  have h := Quadratic.root_norm_le_rate_general D.mu_lt_one.le
    (left_mem_Icc.mpr D.mu_lt_one.le) D.root_design
  simpa only [Complex.norm_real,Real.norm_eq_abs,abs_of_pos D.rho_pos] using h

theorem exact_rates :
    Momentum.momentumRate D.beta D.tau D.step D.step_pos.ne' (1/D.kappa) 1=D.rho ∧
      Momentum.momentumRestRate D.beta D.tau D.step D.step_pos.ne' (1/D.kappa) 1=D.rho ∧
      Quadratic.quadraticRate (1/D.kappa) 1 D.beta D.tau D.step=D.rho := by
  have hqf := Momentum.quadraticRate_le_momentumRate (β:=D.beta) (τ:=D.tau) D.step_pos.ne' D.mu_pos D.mu_lt_one
  have hqr := Momentum.quadraticRate_le_momentumRestRate (β:=D.beta) (τ:=D.tau)
    D.step_pos D.mu_pos D.mu_lt_one
  have hrf := Momentum.restRate_le_momentumRate (β:=D.beta) (τ:=D.tau)
    D.step_pos.ne' D.mu_pos D.mu_lt_one
  have hlow := D.quadratic_rate_ge
  have hupp := D.rate_le
  exact ⟨le_antisymm hupp (hlow.trans hqf),
    le_antisymm (hrf.trans hupp) (hlow.trans hqr),
    le_antisymm (hqf.trans hupp) hlow⟩

end
end nesterov.Robust.Design

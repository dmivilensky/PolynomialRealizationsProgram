import nesterov.Robust.Model
import nesterov.Robust.Algebra

/-! Exact endpoint characteristic factors and circle symbols. -/
namespace nesterov.Robust.Design
noncomputable section
open Set
variable (D : Robust.Design)

theorem S_mu : Quadratic.S D.beta D.tau D.step (1/D.kappa)=D.rho+D.rho^2 := by
  unfold Quadratic.S beta tau step
  have hk : D.kappa-1≠0 := by linarith [D.kappa_gt_one]
  have hr : 1-D.rho≠0 := D.gap_pos.ne'
  have hp : 1+D.rho≠0 := by linarith [D.rho_pos]
  field_simp [hk,hr,hp,D.kappa_pos.ne']
  ring

theorem Q_mu : Quadratic.Q D.beta D.tau D.step (1/D.kappa)=D.rho^3 := by
  unfold Quadratic.Q beta tau step
  have hk : D.kappa-1≠0 := by linarith [D.kappa_gt_one]
  have hr : 1-D.rho≠0 := D.gap_pos.ne'
  have hp : 1+D.rho≠0 := by linarith [D.rho_pos]
  field_simp [hk,hr,hp,D.kappa_pos.ne']

theorem S_L : Quadratic.S D.beta D.tau D.step 1=D.zL := by
  unfold Quadratic.S zL
  nlinarith [D.step_tau]

theorem Q_L : Quadratic.Q D.beta D.tau D.step 1=0 := by
  unfold Quadratic.Q
  nlinarith [D.step_tau]

theorem characteristic_mu (z : ℂ) :
    Quadratic.characteristic D.beta D.tau D.step (1/D.kappa) z=
      (z-(D.rho:ℂ))*(z-(D.rho:ℂ)^2) := by
  rw [Quadratic.characteristic_eq,D.S_mu,D.Q_mu]
  push_cast
  ring

theorem characteristic_L (z : ℂ) :
    Quadratic.characteristic D.beta D.tau D.step 1 z=z*(z-(D.zL:ℂ)) := by
  rw [Quadratic.characteristic_eq,D.S_L,D.Q_L]
  push_cast
  ring

theorem symbol_circle (r ω : ℝ) :
    ((1-TwoStep.circle r ω)*Quadratic.characteristic D.beta D.tau D.step (1/D.kappa)
      (TwoStep.circle r ω)*star (Quadratic.characteristic D.beta D.tau D.step 1
        (TwoStep.circle r ω))).re=Robust.symbol r D.rho D.zL (1-Real.cos ω) := by
  simp only [Quadratic.characteristic_eq,D.S_mu,D.S_L,D.Q_mu,D.Q_L]
  change ((1-TwoStep.circle r ω)*TwoStep.quad (D.rho+D.rho^2) (D.rho^3)
    (TwoStep.circle r ω)*star (TwoStep.quad D.zL 0 (TwoStep.circle r ω))).re=_
  rw [TwoStep.lagOne_cubic]
  dsimp only [Robust.symbol,TwoStep.P3]
  ring

theorem design_symbol (ω : ℝ) :
    ((1-TwoStep.circle D.rho ω)*Quadratic.characteristic D.beta D.tau D.step (1/D.kappa)
      (TwoStep.circle D.rho ω)*star (Quadratic.characteristic D.beta D.tau D.step 1
        (TwoStep.circle D.rho ω))).re=
      D.rho^3*(1+D.rho)*(1-D.kappa*(1-D.rho)^2)*
        (1-Real.cos ω)*((1-D.rho)^2+2*D.rho*(1-Real.cos ω)) := by
  rw [D.symbol_circle,Robust.symbol_on_design]
  unfold zL step
  ring

theorem design_symbol_nonneg (ω : ℝ) :
    0≤((1-TwoStep.circle D.rho ω)*Quadratic.characteristic D.beta D.tau D.step (1/D.kappa)
      (TwoStep.circle D.rho ω)*star (Quadratic.characteristic D.beta D.tau D.step 1
        (TwoStep.circle D.rho ω))).re := by
  rw [D.design_symbol]
  have hρ := D.rho_pos.le
  have hgap : 0≤1-D.kappa*(1-D.rho)^2 := sub_nonneg.mpr D.lower
  have hξ : 0≤1-Real.cos ω := sub_nonneg.mpr (Real.cos_le_one _)
  positivity

end
end nesterov.Robust.Design

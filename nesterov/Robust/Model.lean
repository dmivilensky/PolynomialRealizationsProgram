import nesterov.Momentum.Parameters
import nesterov.Slow.Kappa

/-! The literal robust-momentum design interval and its admissible tuning,
normalized by L=1 and μ=1/κ. -/
namespace nesterov.Robust
noncomputable section
open Set

structure Design where
  kappa : ℝ
  rho : ℝ
  kappa_gt_one : 1<kappa
  rho_pos : 0<rho
  rho_lt_one : rho<1
  lower : kappa*(1-rho)^2≤1
  upper : 1≤kappa*(1-rho)

theorem design_interval {κ ρ : ℝ} (hκ : 1<κ)
    (hρ : ρ∈Icc (1-1/Real.sqrt κ) (1-1/κ)) :
    0<ρ ∧ ρ<1 ∧ κ*(1-ρ)^2≤1 ∧ 1≤κ*(1-ρ) := by
  have hκp : 0<κ := by linarith
  have hs : 1<Real.sqrt κ := Real.lt_sqrt_of_sq_lt (by simpa using hκ)
  have hinv : 1/Real.sqrt κ<1 := (div_lt_one (by linarith)).mpr hs
  have hρp : 0<ρ := by linarith [hρ.1]
  have hρ1 : ρ<1 := by linarith [one_div_pos.mpr hκp,hρ.2]
  refine ⟨hρp,hρ1,?_,?_⟩
  · have hh : (1-ρ)^2≤(1/Real.sqrt κ)^2 :=
      pow_le_pow_left₀ (by linarith) (by linarith [hρ.1]) 2
    have hm := mul_le_mul_of_nonneg_left hh hκp.le
    have he : κ*(1/Real.sqrt κ)^2=1 := by
      rw [div_pow,one_pow,Real.sq_sqrt hκp.le]
      exact mul_one_div_cancel hκp.ne'
    linarith
  · have hh : 1/κ≤1-ρ := by linarith [hρ.2]
    have hm := mul_le_mul_of_nonneg_left hh hκp.le
    simpa only [mul_one_div_cancel hκp.ne'] using hm

def ofInterval (κ ρ : ℝ) (hκ : 1<κ)
    (hρ : ρ∈Icc (1-1/Real.sqrt κ) (1-1/κ)) : Design where
  kappa := κ
  rho := ρ
  kappa_gt_one := hκ
  rho_pos := (design_interval hκ hρ).1
  rho_lt_one := (design_interval hκ hρ).2.1
  lower := (design_interval hκ hρ).2.2.1
  upper := (design_interval hκ hρ).2.2.2

namespace Design
variable (D : Design)

theorem kappa_pos : 0<D.kappa := by linarith [D.kappa_gt_one]
theorem gap_pos : 0<1-D.rho := sub_pos.mpr D.rho_lt_one

def beta : ℝ := D.kappa*D.rho^3/(D.kappa-1)
def tau : ℝ := D.rho^3/((D.kappa-1)*(1-D.rho)^2*(1+D.rho))
def step : ℝ := D.kappa*(1-D.rho)^2*(1+D.rho)
def zL : ℝ := 1-D.step

theorem beta_nonneg : 0≤D.beta := by
  unfold beta
  have hk := D.kappa_gt_one
  have hr := D.rho_pos
  positivity

theorem beta_lt_one : D.beta<1 := by
  have hr := D.rho_pos
  have hr1 := D.rho_lt_one
  have hρ3 : D.rho^3<D.rho := by
    have hh := mul_pos hr (sub_pos.mpr hr1)
    nlinarith
  apply (div_lt_one (by linarith [D.kappa_gt_one])).mpr
  have hh := mul_lt_mul_of_pos_left hρ3 D.kappa_pos
  have hu := D.upper
  change D.kappa*D.rho^3<D.kappa-1
  nlinarith

theorem tau_nonneg : 0≤D.tau := by
  unfold tau
  have hk := D.kappa_gt_one
  have hr := D.rho_pos
  positivity

theorem step_pos : 0<D.step := by
  unfold step
  exact mul_pos (mul_pos D.kappa_pos (sq_pos_of_pos D.gap_pos)) (by linarith [D.rho_pos])

def tuning : Momentum.Tuning where
  beta := D.beta
  tau := D.tau
  stepSize := D.step
  beta_nonneg := D.beta_nonneg
  beta_lt_one := D.beta_lt_one
  tau_nonneg := D.tau_nonneg
  step_pos := D.step_pos

theorem step_tau : D.step*D.tau=D.beta := by
  unfold step tau beta
  have hk : D.kappa-1≠0 := by linarith [D.kappa_gt_one]
  have hr : 1-D.rho≠0 := D.gap_pos.ne'
  have hp : 1+D.rho≠0 := by linarith [D.rho_pos]
  field_simp [hk,hr,hp]

theorem step_le : D.step≤1+D.rho := by
  have hh := mul_le_mul_of_nonneg_right D.lower (show 0≤1+D.rho by linarith [D.rho_pos])
  simpa only [step,one_mul] using hh

theorem zL_bounds : D.zL∈Icc (-D.rho) D.rho := by
  constructor
  · unfold zL
    linarith [D.step_le]
  · have hm := mul_le_mul_of_nonneg_right D.upper
      (mul_nonneg D.gap_pos.le (show 0≤1+D.rho by linarith [D.rho_pos]))
    have he : D.kappa*(1-D.rho)*((1-D.rho)*(1+D.rho))=D.step := by unfold step;ring
    rw [he] at hm
    unfold zL
    have hprod := mul_nonneg D.rho_pos.le D.gap_pos.le
    nlinarith

theorem mu_pos : 0<1/D.kappa := one_div_pos.mpr D.kappa_pos
theorem mu_lt_one : 1/D.kappa<1 := (div_lt_one D.kappa_pos).mpr D.kappa_gt_one

theorem stable : D.tuning.Stable (1/D.kappa) 1 := by
  apply (D.tuning.stable_iff D.mu_pos D.mu_lt_one).mpr
  change D.step*1*(1+2*D.tau)<2*(1+D.beta)
  have hh := D.step_tau
  have hstep : D.step<2 := D.step_le.trans_lt (by linarith [D.rho_lt_one])
  nlinarith

end Design
end
end nesterov.Robust

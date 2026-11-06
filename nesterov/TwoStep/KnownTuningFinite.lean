import nesterov.TwoStep.KnownTuningGerms
import nesterov.TwoStep.Phase

/-! Finite-condition-number convergence of the Nesterov tunings used below. -/
namespace nesterov.TwoStep.KnownTunings
noncomputable section
open Set

private theorem concave_quadratic_pos {a b d x : ℝ} (hd : d≤0)
    (h₀ : 0<a) (h₂ : 0<a+2*b+4*d) (hx : x∈Icc (0:ℝ) 2) :
    0<a+b*x+d*x^2 := by
  have hrem : 0≤d*x*(x-2) := mul_nonneg_of_nonpos_of_nonpos
    (mul_nonpos_of_nonpos_of_nonneg hd hx.1) (by linarith [hx.2])
  have hlin : 0<(1-x/2)*a+(x/2)*(a+2*b+4*d) := by
    by_cases hx2 : x=2
    · subst x
      simpa using h₂
    · have hxlt : x<2 := lt_of_le_of_ne hx.2 hx2
      have hp : 0<1-x/2 := by linarith
      exact add_pos_of_pos_of_nonneg (mul_pos hp h₀)
        (mul_nonneg (by linarith [hx.1]) h₂.le)
  nlinarith

theorem nesterov_stable (q : Momentum.Tuning) {μ L : ℝ}
    (hμ : 0<μ) (hμL : μ<L) (hτ : q.tau=q.beta) (hstep : q.stepSize*L≤4/3) :
    q.Stable μ L := by
  apply (q.stable_iff hμ hμL).mpr
  rw [hτ]
  have hh := mul_le_mul_of_nonneg_right hstep (show 0≤1+2*q.beta by linarith [q.beta_nonneg])
  nlinarith [q.beta_lt_one]

/-- Concavity of the exact lag-one quadratic proves full-class convergence
for the three Nesterov step sizes, including the proposed optimal tuning. -/
theorem nesterov_rate_lt_one (q : Momentum.Tuning) {μ L : ℝ}
    (hμ : 0<μ) (hμL : μ<L) (hτ : q.tau=q.beta)
    (hstep1 : 1≤q.stepSize*L) (hstep : q.stepSize*L≤4/3) :
    Momentum.momentumRate q.beta q.tau q.stepSize q.step_pos.ne' μ L<1 := by
  have hs := nesterov_stable q hμ hμL hτ hstep
  apply positive_Ltau_rate q hμ hμL hs
  intro ξ hξ
  have h₀ := Ltau_zero_pos (τ:=q.tau) q.beta_lt_one (mul_pos q.step_pos hμ)
    (mul_lt_mul_of_pos_left hμL q.step_pos)
  have h₂ := stable_Ltau_two_pos q hμ hμL hs
  have hd : A2 q.beta q.tau (q.stepSize*L)≤0 := by
    unfold A2
    rw [hτ]
    nlinarith [mul_le_mul_of_nonneg_left hstep1 q.beta_nonneg]
  rw [Ltau_zero] at h₀
  change 0<A0 q.beta (q.stepSize*μ) (q.stepSize*L)+
    A1 q.beta q.tau (q.stepSize*μ) (q.stepSize*L)*2+A2 q.beta q.tau (q.stepSize*L)*2^2 at h₂
  have h₂' : 0<A0 q.beta (q.stepSize*μ) (q.stepSize*L)+
    2*A1 q.beta q.tau (q.stepSize*μ) (q.stepSize*L)+4*A2 q.beta q.tau (q.stepSize*L) := by nlinarith
  exact concave_quadratic_pos hd h₀ h₂' ⟨hξ.1.le,hξ.2⟩

def optimalNesterovTuning (κ : ℝ) (hκ : 6≤κ) : Momentum.Tuning where
  beta := 1-Real.sqrt (6/κ)
  tau := 1-Real.sqrt (6/κ)
  stepSize := 4/3
  beta_nonneg := by
    have hκp : 0<κ := by linarith
    have hs : Real.sqrt (6/κ)≤1 := Real.sqrt_le_one.mpr ((div_le_one hκp).mpr hκ)
    linarith
  beta_lt_one := by
    have hs : 0<Real.sqrt (6/κ) := Real.sqrt_pos.mpr (div_pos (by norm_num) (by linarith))
    linarith
  tau_nonneg := by
    have hκp : 0<κ := by linarith
    have hs : Real.sqrt (6/κ)≤1 := Real.sqrt_le_one.mpr ((div_le_one hκp).mpr hκ)
    linarith
  step_pos := by norm_num

/-- The source optimal Nesterov tuning is stable and linearly convergent at
every stated finite condition number κ≥6, before taking its asymptotic limit. -/
theorem optimalNesterov_finite (κ : ℝ) (hκ : 6≤κ) :
    (optimalNesterovTuning κ hκ).Stable (1/κ) 1 ∧
      Momentum.momentumRate (optimalNesterovTuning κ hκ).beta
        (optimalNesterovTuning κ hκ).tau (4/3) (by norm_num) (1/κ) 1<1 := by
  have hκp : 0<κ := by linarith
  have hμ : 0<1/κ := one_div_pos.mpr hκp
  have hμL : 1/κ<1 := (div_lt_one hκp).mpr (by linarith)
  exact ⟨nesterov_stable _ hμ hμL rfl (by norm_num [optimalNesterovTuning]),
    nesterov_rate_lt_one _ hμ hμL rfl (by norm_num [optimalNesterovTuning])
      (by norm_num [optimalNesterovTuning])⟩

end
end nesterov.TwoStep.KnownTunings

import chebyshev1.Prefix.RatioAlgorithm
import chebyshev1.Chebyshev.DriftBudget

/-! The prefix recurrence tends to the optimal heavy-ball coefficients. -/
namespace chebyshev1
noncomputable section
open Real Filter
open scoped Topology

private theorem tanh_rescaled (x : ℝ) :
    tanh x = (1 - exp (-2*x)) / (1 + exp (-2*x)) := by
  have he : exp (-2*x) = exp (-x) / exp x := by
    rw [← exp_sub]
    congr 1
    ring
  rw [tanh_eq, he]
  field_simp

private theorem tanh_nat_limit (a : ℝ) (ha : 0 < a) :
    Tendsto (fun n : ℕ => tanh ((n : ℝ)*a)) atTop (𝓝 1) := by
  have hn : Tendsto (fun n : ℕ => (n : ℝ)*a) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_mul_const ha
  have hexp : Tendsto (fun n : ℕ => exp (-2*((n : ℝ)*a))) atTop (𝓝 0) :=
    tendsto_exp_atBot.comp (hn.const_mul_atTop_of_neg (by norm_num : (-2 : ℝ) < 0))
  have hh := ((tendsto_const_nhds (x := (1 : ℝ))).sub hexp).div
    ((tendsto_const_nhds (x := (1 : ℝ))).add hexp) (by norm_num)
  simp only [sub_zero, add_zero, div_one] at hh
  apply hh.congr
  intro n
  exact (tanh_rescaled ((n : ℝ)*a)).symm

private theorem cosh_ratio_identity (x a : ℝ) :
    cosh x / cosh (x+a) = 1 / (cosh a + tanh x*sinh a) := by
  have he : cosh a + tanh x*sinh a = cosh (x+a)/cosh x := by
    rw [cosh_add, tanh_eq_sinh_div_cosh]
    field_simp
  rw [he, one_div_div]

namespace Prefix

/-- The hyperbolic decay parameter is the usual optimal heavy-ball square-root ratio. -/
theorem exp_neg_arcosh_eta (I : SpectralInterval) :
    exp (-arcosh I.eta) = (sqrt I.L - sqrt I.mu) / (sqrt I.L + sqrt I.mu) := by
  have hL : 0 < I.L := I.mu_pos.trans I.mu_lt_L
  have hsL := sqrt_nonneg I.L
  have hsm := sqrt_nonneg I.mu
  have hsum : 0 < sqrt I.L + sqrt I.mu := by positivity
  have hd : I.L - I.mu ≠ 0 := I.delta_pos.ne'
  have hLs := sq_sqrt hL.le
  have hms := sq_sqrt I.mu_pos.le
  have hdelta : I.delta = (sqrt I.L-sqrt I.mu)*(sqrt I.L+sqrt I.mu) := by
    dsimp [SpectralInterval.delta]
    nlinarith
  have hsquare : I.eta^2 - 1 = (2*sqrt I.L*sqrt I.mu/I.delta)^2 := by
    dsimp [SpectralInterval.eta, SpectralInterval.delta]
    field_simp [hd]
    nlinarith [hLs, hms]
  have hroot : sqrt (I.eta^2-1) = 2*sqrt I.L*sqrt I.mu/I.delta := by
    rw [hsquare, sqrt_sq (div_nonneg (by positivity) I.delta_pos.le)]
  have he : I.eta + sqrt (I.eta^2-1) = (sqrt I.L+sqrt I.mu)^2/I.delta := by
    rw [hroot]
    dsimp [SpectralInterval.eta, SpectralInterval.delta]
    field_simp [hd]
    nlinarith
  rw [exp_neg, exp_arcosh I.eta_gt_one.le, he, inv_div, hdelta]
  field_simp [hsum.ne']

theorem den_ratio_limit (I : SpectralInterval) :
    Tendsto (fun n : ℕ => I.den n / I.den (n+1)) atTop
      (𝓝 (exp (-arcosh I.eta))) := by
  let a := arcosh I.eta
  have ha : 0 < a := arcosh_pos I.eta_gt_one
  have hh := (tendsto_const_nhds (x := (1 : ℝ))).div
    ((tendsto_const_nhds (x := cosh a)).add ((tanh_nat_limit a ha).mul_const (sinh a)))
    (by rw [one_mul, cosh_add_sinh]; exact (exp_pos a).ne')
  simp only [one_mul, cosh_add_sinh, one_div, ← exp_neg] at hh
  apply hh.congr
  intro n
  rw [I.den_cosh_arcosh, I.den_cosh_arcosh]
  simp only [Pi.div_apply, Nat.cast_add, Nat.cast_one]
  change 1 / (cosh a + tanh ((n : ℝ)*a)*sinh a) =
    cosh ((n : ℝ)*a)/cosh (((n : ℝ)+1)*a)
  rw [add_mul, one_mul, cosh_ratio_identity]

theorem beta_heavyBall_limit (I : SpectralInterval) :
    Tendsto (fun n : ℕ => beta I (n+1)) atTop (𝓝 (exp (-arcosh I.eta)^2)) := by
  have hh := (den_ratio_limit I).mul ((den_ratio_limit I).comp (tendsto_add_atTop_nat 1))
  convert hh using 1
  · funext n
    simp only [beta, Nat.add_sub_cancel, Function.comp_def]
    field_simp [I.den_ne (n+1)]
  · ring

theorem gamma_heavyBall_limit (I : SpectralInterval) :
    Tendsto (fun n : ℕ => gamma I (n+1)) atTop
      (𝓝 (4*exp (-arcosh I.eta)/I.delta)) := by
  have hh := ((den_ratio_limit I).comp (tendsto_add_atTop_nat 1)).const_mul (4/I.delta)
  convert hh using 1
  · funext n
    simp only [gamma, Function.comp_def]
    ring
  · ring

/-- The actual momentum coefficients tend to Polyak's optimal value. -/
theorem beta_optimal_limit (I : SpectralInterval) :
    Tendsto (fun n : ℕ => beta I (n+1)) atTop
      (𝓝 (((sqrt I.L - sqrt I.mu)/(sqrt I.L + sqrt I.mu))^2)) := by
  simpa only [exp_neg_arcosh_eta I] using beta_heavyBall_limit I

/-- The actual gradient coefficients tend to Polyak's optimal stepsize. -/
theorem gamma_optimal_limit (I : SpectralInterval) :
    Tendsto (fun n : ℕ => gamma I (n+1)) atTop
      (𝓝 (4/(sqrt I.L + sqrt I.mu)^2)) := by
  have he : 4*exp (-arcosh I.eta)/I.delta = 4/(sqrt I.L + sqrt I.mu)^2 := by
    rw [exp_neg_arcosh_eta]
    have hL : 0 < I.L := I.mu_pos.trans I.mu_lt_L
    have hs : 0 < sqrt I.L + sqrt I.mu := by positivity
    have hLs := sq_sqrt hL.le
    have hms := sq_sqrt I.mu_pos.le
    have hd : I.delta = (sqrt I.L-sqrt I.mu)*(sqrt I.L+sqrt I.mu) := by
      dsimp [SpectralInterval.delta]
      nlinarith
    have hdne := I.delta_pos.ne'
    rw [hd] at hdne ⊢
    field_simp [hs.ne', (mul_ne_zero_iff.mp hdne).1]
  simpa only [he] using gamma_heavyBall_limit I

end Prefix
end
end chebyshev1

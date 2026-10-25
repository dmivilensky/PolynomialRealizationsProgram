import polyak.Levels.Program.SourceBijection
import polyak.Levels.Program.PhaseFloors
import polyak.Levels.Chart.Coefficients

/-! Literal source density, endpoint and Laurent-polynomial identities. -/
noncomputable section
open scoped BigOperators
namespace polyak.Levels

theorem sourceDensity_eq_norm_g_minus_2is (q : General.Tuning) (ω : Frequency) :
    sourceDensity q ω=‖((sourceG q ω:ℝ):ℂ)-2*Complex.I*((angleMultiplier q ω).im:ℂ)‖ := by
  rw [sourceDensity_eq_norm,← General.Tuning.real_im_factor]
  rfl

theorem sourceDensity_eq_ab_norm (q : General.Tuning) (ω : Frequency) :
    sourceDensity q ω=‖q.a (Waves.z 0 ω)‖*‖q.b (Waves.z 0 ω)‖/q.B^2 := by
  have hz : Waves.z 0 (ω:ℝ)≠0 := Complex.exp_ne_zero _
  have hnorm : Complex.normSq (Waves.z 0 (ω:ℝ))=1 := by
    simpa only [pow_one,mul_zero,Real.exp_zero] using Waves.normSq_z_pow 0 (ω:ℝ) 1
  rw [sourceDensity_eq_norm,angleMultiplier_eq,q.factor hz,hnorm]
  simp only [Complex.ofReal_one,mul_one,norm_div,norm_mul,norm_neg,norm_star,norm_pow,
    Complex.norm_real,Real.norm_eq_abs,abs_of_pos q.B_pos]

theorem Curve.lag_at_pi_zpow (Θ : Curve) (n : ℤ) :
    Θ.lag n frequencyPi = -1+(-1:ℝ)^n := by rw [Θ.lag_at_pi,Real.cos_int_mul_pi]

theorem zfMultiplier_zpow (F : Finset ℤ) (a : ℤ→ℝ) (γ ω:ℝ) :
    zfMultiplier F a γ ω=(γ:ℂ)+(∑n∈F,(a n:ℂ)*(1-(Complex.exp ((ω:ℂ)*Complex.I))^n)) := by
  unfold zfMultiplier
  congr 1
  apply Finset.sum_congr rfl
  intro n _
  have he : ((((n:ℝ)*ω:ℝ):ℂ)*Complex.I)=(n:ℂ)*((ω:ℂ)*Complex.I) := by push_cast; ring
  rw [he,Complex.exp_int_mul]

theorem tuningCurve_eq_of_coefficients_eq {q q' : General.Tuning}
    (h : Chart.coefficients q=Chart.coefficients q') : tuningCurve q=tuningCurve q' := by
  apply tuningCurve_eq_of_Xi_eq
  intro c _
  rw [← Chart.eval_coefficients,← Chart.eval_coefficients,h]

theorem threshold_spectral_iff_of_coefficients_eq {q q' : General.Tuning}
    (h : Chart.coefficients q=Chart.coefficients q') :
    (∃ν:Spectral.Spectrum,Waves.MixtureFeasible ν (Waves.multiplierMap q.A q.B q.beta 0) 0 0) ↔
      (∃ν:Spectral.Spectrum,Waves.MixtureFeasible ν (Waves.multiplierMap q'.A q'.B q'.beta 0) 0 0) := by
  rw [threshold_spectral_iff_fp,threshold_spectral_iff_fp,tuningCurve_eq_of_coefficients_eq h]

end polyak.Levels

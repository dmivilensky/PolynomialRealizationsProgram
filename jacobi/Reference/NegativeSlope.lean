import jacobi.Reference.NegativeEnergy

/-!
Article: jacobi, Appendix C.1 (negative-energy bounds).
Its quarter-point initial bound follows from the previously proved
energy of the same reference wave, without an asymptotic initial state.
Source: variation of constants for the original reference equation.
Use: its actual first-order equation and weighted integral estimate prove the midpoint logarithmic derivative asymptotic in NegativeQuotient.
-/
namespace jacobi.Reference
noncomputable section
open Real Set MeasureTheory Filter _root_.Complex
set_option backward.isDefEq.respectTransparency false

/-- The genuine real negative-energy slope defect f'-y*f for the original reference wave.
Use: its actual first-order equation and weighted integral estimate prove the midpoint logarithmic derivative asymptotic in NegativeQuotient.
Article: jacobi, Appendix C.1 (negative-energy bounds).
-/
def negativeSlopeDefect (a y t : ℝ) : ℝ :=
  (waveSlope a (Complex.I*(y:ℂ)) t).re-y*(wave a (Complex.I*(y:ℂ)) t).re

/-- The actual negative-energy slope defect has its genuine first-order derivative throughout the physical interior.
Use: differentiates its true integrating factor in negativeSlopeDefect_integral.
Article: jacobi, Appendix C.1 (negative-energy bounds).
Source: the first-order equation D'=Q_gamma*f-y*D obtained from f''=(y^2+Q_gamma)*f.
Proof: take the real parts of the proved genuine wave and slope
derivatives. The actual reference equation cancels the y^2 term
after the true imaginary-frequency square is evaluated. -/
theorem negativeSlopeDefect_hasDerivAt {a : ℝ} (ha : -1<a) (y : ℝ) {t : ℝ}
    (ht : t∈Ioo (0:ℝ) 1) :
    HasDerivAt (negativeSlopeDefect a y)
      (singularPotential a t*(wave a (Complex.I*(y:ℂ)) t).re-y*negativeSlopeDefect a y t) t := by
  -- Every derivative belongs to the actual original wave; the real-part map is a genuine continuous linear map.
  have hf := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t (wave_hasDerivAt a (Complex.I*(y:ℂ)) ht)
  have hd := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t (waveSlope_hasDerivAt a (Complex.I*(y:ℂ)) ht)
  have he := waveAcceleration_frequency ha (Complex.I*(y:ℂ)) ht
  rw [mul_pow,Complex.I_sq] at he
  have hre := congrArg Complex.re he
  simp only [mul_re,sub_re,sub_im,ofReal_re,ofReal_im,neg_mul,one_mul,neg_re,neg_im,
    zero_sub,pow_two,mul_im,zero_mul,mul_zero,sub_zero,add_zero] at hre
  convert! hd.sub (hf.const_mul y) using 1
  dsimp [negativeSlopeDefect]
  linear_combination -hre

/-- The actual slope defect has a genuine weighted derivative with the original potential as its sole forcing term.
Use: applies the fundamental theorem of calculus on the physical interval in negativeSlopeDefect_integral.
Article: jacobi, Appendix C.1 (negative-energy bounds).
Source: the integrating-factor identity (exp(y*t)*D)'=exp(y*t)*Q_gamma*f.
Proof: differentiate the true exponential times the proved defect; its two y*D terms cancel exactly. -/
theorem weightedSlopeDefect_hasDerivAt {a : ℝ} (ha : -1<a) (y : ℝ) {t : ℝ}
    (ht : t∈Ioo (0:ℝ) 1) :
    HasDerivAt (fun s : ℝ => Real.exp (y*s)*negativeSlopeDefect a y s)
      (Real.exp (y*t)*singularPotential a t*(wave a (Complex.I*(y:ℂ)) t).re) t := by
  convert! ((((hasDerivAt_id t).const_mul y).exp).mul (negativeSlopeDefect_hasDerivAt ha y ht)) using 1
  simp only [id_eq]
  ring

/-- The genuine integrating-factor identity holds for the actual reference slope defect across the quarter-to-midpoint interval.
Use: bounds the midpoint quotient by the actual quarter-point state and the integrable potential forcing in NegativeQuotient.
Article: jacobi, Appendix C.1 (negative-energy bounds).
Source: the fundamental theorem of calculus for the true integrating-factor derivative.
Proof: the literal potential is continuous away from the physical
endpoints, and the actual wave is differentiable there. Its forcing is
therefore genuinely integrable on the compact interval. Apply the
community interval fundamental theorem to the proved derivative. -/
theorem negativeSlopeDefect_integral {a : ℝ} (ha : -1<a) (y : ℝ) :
    (∫ s in (1/4:ℝ)..(1/2:ℝ),Real.exp (y*s)*singularPotential a s*(wave a (Complex.I*(y:ℂ)) s).re)=
      Real.exp (y/2)*negativeSlopeDefect a y (1/2)-Real.exp (y/4)*negativeSlopeDefect a y (1/4) := by
  -- The potential is used only on a compact interval strictly inside the original physical domain.
  have hregion {s : ℝ} (hs : s∈uIcc (1/4:ℝ) (1/2)) : s∈Ioo (0:ℝ) 1 := by
    rw [uIcc_of_le (by norm_num : (1/4:ℝ)≤1/2)] at hs
    constructor <;> linarith [hs.1,hs.2]
  have hc : ContinuousOn (fun s : ℝ =>
      Real.exp (y*s)*singularPotential a s*(wave a (Complex.I*(y:ℂ)) s).re) (uIcc (1/4:ℝ) (1/2)) := by
    intro s hs
    have ht := hregion hs
    have hQ : ContinuousAt (singularPotential a) s := by
      unfold singularPotential potential
      fun_prop (disch := exact pow_ne_zero 2 (sine_pos ht).ne')
    exact ((by fun_prop : ContinuousAt (fun r : ℝ => Real.exp (y*r)) s).mul hQ).mul
      (Complex.continuous_re.continuousAt.comp (wave_hasDerivAt a _ ht).continuousAt) |>.continuousWithinAt
  have hi := hc.intervalIntegrable (μ := volume)
  have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s hs => weightedSlopeDefect_hasDerivAt ha y (hregion hs)) hi
  simpa only [mul_one_div] using hh

/-- The actual quarter-point slope defect has a uniform high-frequency bound from the genuine reference state energy.
Use: bounds the decaying initial term of the midpoint logarithmic derivative in NegativeQuotient.
Article: jacobi, Appendix C.1 (midpoint characteristics and negative-axis normalization).
Proof: the actual initial time lies before 1/4 for y>=1. The proved
high-frequency energy bounds both genuine state coordinates after
normalization by y. Take square roots and use the true complex norm
triangle inequality before taking the real part of f'-y*f. -/
theorem negativeSlopeDefect_quarter_bound {a : ℝ} (ha : -1<a) :
    ∃ C : ℝ,0<C ∧ ∀ y : ℝ,1≤y →
      |negativeSlopeDefect a y (1/4)|≤C*y*y^(-gamma a)*Real.exp (y/4) := by
  -- The original energy has its already proved endpoint normalization; no independent large-y normalization is assumed.
  obtain ⟨B,hB,hbound⟩ := waveEnergy_high_bound ha
  refine ⟨2*Real.sqrt B,by positivity,fun y hy => ?_⟩
  have hyp : 0<y := lt_of_lt_of_le zero_lt_one hy
  have hn : ‖Complex.I*(y:ℂ)‖=y := by
    rw [norm_mul,Complex.norm_I,one_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hyp]
  have ht : initialTime (Complex.I*(y:ℂ))≤1/4 := by
    unfold initialTime
    rw [hn]
    apply (div_le_iff₀ (by positivity : 0<4*Real.pi*y)).mpr
    nlinarith [mul_le_mul_of_nonneg_left hy Real.pi_pos.le,Real.two_le_pi]
  have hb := hbound (Complex.I*(y:ℂ)) (by rw [hn]; exact hy) (1/4:ℝ) (by norm_num) ht
  simp only [hn,Complex.mul_im,Complex.I_re,Complex.I_im,Complex.ofReal_re,
    Complex.ofReal_im,zero_mul,one_mul,zero_add,abs_of_pos hyp] at hb
  let R : ℝ := Real.sqrt B*y^(-gamma a)*Real.exp (y/4)
  have hR : 0≤R := by dsimp [R]; positivity
  have hsq : B*(y^(-gamma a)*Real.exp ((1/4)*y))^2=R^2 := by
    dsimp [R]
    simp only [mul_pow,Real.sq_sqrt hB.le]
    rw [show (1/4:ℝ)*y=y/4 by ring]
    ring
  rw [hsq] at hb
  have hvalue : ‖wave a (Complex.I*(y:ℂ)) (1/4)‖≤R := by
    apply (sq_le_sq₀ (norm_nonneg _) hR).mp
    apply le_trans ?_ hb
    unfold waveEnergy frequencyEnergy
    exact le_add_of_nonneg_right (by positivity)
  have hslope : ‖waveSlope a (Complex.I*(y:ℂ)) (1/4)‖≤y*R := by
    have hpart : (‖waveSlope a (Complex.I*(y:ℂ)) (1/4)‖/y)^2≤R^2 := by
      apply le_trans ?_ hb
      unfold waveEnergy frequencyEnergy
      rw [hn,div_pow]
      exact le_add_of_nonneg_left (sq_nonneg _)
    simpa only [mul_comm] using (div_le_iff₀ hyp).mp ((sq_le_sq₀ (by positivity) hR).mp hpart)
  calc
    _ ≤ |(waveSlope a (Complex.I*(y:ℂ)) (1/4)).re|+y*|(wave a (Complex.I*(y:ℂ)) (1/4)).re| := by
      dsimp [negativeSlopeDefect]
      simpa only [abs_mul,abs_of_pos hyp] using abs_sub
        (waveSlope a (Complex.I*(y:ℂ)) (1/4)).re (y*(wave a (Complex.I*(y:ℂ)) (1/4)).re)
    _ ≤ y*R+y*R := add_le_add ((Complex.abs_re_le_norm _).trans hslope)
      (mul_le_mul_of_nonneg_left ((Complex.abs_re_le_norm _).trans hvalue) hyp.le)
    _ = _ := by dsimp [R]; ring

end
end jacobi.Reference

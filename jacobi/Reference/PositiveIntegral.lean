import jacobi.Reference.BetaRepresentation
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
Article: jacobi, Appendix C.1 (negative-energy bounds).
Source: positivity of Lebesgue integration and the exponential cosine formula.
Use: gives a positive, integrable majorant for every literal complex-frequency integrand and the positive negative-energy integral.
-/
namespace jacobi.Reference
noncomputable section
open Real Set MeasureTheory _root_.Complex
set_option backward.isDefEq.respectTransparency false

/-- The original real sine-power density before multiplication by the cosine.
Use: gives a positive, integrable majorant for every literal complex-frequency integrand and the positive negative-energy integral.
Article: jacobi, Appendix C.1 (negative-energy bounds).
-/
def sineWeight (g t s : ℝ) : ℝ :=
  (Real.sin (Real.pi*s)*Real.sin (Real.pi*(t-s))/Real.pi^2)^(g-1)

/-- The actual sine-power density is nonnegative over the closed physical integration interval.
Use: the exact cosine majorant can be multiplied by the same density in wave_cosine_domination.
Article: jacobi, Appendix C.1 (negative-energy bounds).
Proof: both sine arguments lie between zero and pi, and real powers of nonnegative bases are nonnegative. -/
theorem sineWeight_nonneg (g : ℝ) {t : ℝ} (ht : t∈Ioo (0:ℝ) 1)
    {s : ℝ} (hs : s∈Icc (0:ℝ) t) : 0≤sineWeight g t s := by
  have hsin (r : ℝ) (hr : r∈Icc (0:ℝ) t) : 0≤Real.sin (Real.pi*r) := by
    apply Real.sin_nonneg_of_mem_Icc
    exact ⟨mul_nonneg Real.pi_pos.le hr.1,by nlinarith [hr.2,ht.2,Real.pi_pos]⟩
  exact Real.rpow_nonneg (div_nonneg
    (mul_nonneg (hsin s hs) (hsin (t-s) ⟨sub_nonneg.mpr hs.2,by linarith [hs.1]⟩)) (sq_nonneg _)) _

/-- The original sine-power density is strictly positive at every interior integration point.
Use: proves strict positivity of the actual zero-frequency and negative-energy reference functions by genuine integration.
Article: jacobi, Appendix C.1 (negative-energy bounds).
Proof: both sine factors have arguments strictly between zero and pi, and every real power of a positive base is positive. -/
theorem sineWeight_pos (g : ℝ) {t : ℝ} (ht : t∈Ioo (0:ℝ) 1)
    {s : ℝ} (hs : s∈Ioo (0:ℝ) t) : 0<sineWeight g t s := by
  apply Real.rpow_pos_of_pos
  have hsin (r : ℝ) (hr : r∈Ioo (0:ℝ) t) : 0<Real.sin (Real.pi*r) :=
    Real.sin_pos_of_pos_of_lt_pi (mul_pos Real.pi_pos hr.1) (by nlinarith [Real.pi_pos,hr.2,ht.2])
  exact div_pos (mul_pos (hsin s hs) (hsin (t-s) ⟨sub_pos.mpr hs.2,by linarith [hs.1]⟩))
    (sq_pos_of_pos Real.pi_pos)

/-- The actual positive sine-power density is genuinely integrable throughout the full source parameter range.
Use: supplies the real majorant integrability for exact cosine domination and hyperbolic-cosine positivity.
Article: jacobi, Appendix C.1 (negative-energy bounds).
Proof: take the actual real part of the proved convergent complex integral at zero frequency. -/
theorem sineWeight_integrable {g t : ℝ} (hg : 0<g) (ht : t∈Ioo (0:ℝ) 1) :
    IntervalIntegrable (sineWeight g t) volume 0 t := by
  rw [intervalIntegrable_iff]
  change Integrable (sineWeight g t) (volume.restrict (uIoc (0:ℝ) t))
  have h := Complex.reCLM.integrable_comp (sine_integrable hg ht (0:ℂ)).def'
  convert! h using 1
  funext s
  simp [sineWeight,sineIntegrand]

/-- The cosine at the actual imaginary frequency is exactly the real hyperbolic cosine, with no square-root branch restriction.
Use: changes the defining integral of wave at omega=i*y into its strictly positive real integral.
Article: jacobi, Appendix C.1 (negative-energy bounds).
Source: the classical exponential definitions of cosine and hyperbolic cosine.
Proof: reassociate the two real factors before i, then use the community cos(z*i)=cosh(z) and real-inclusion identities. -/
theorem cosine_imaginary (r y : ℝ) :
    Complex.cos ((r:ℂ)*(Complex.I*(y:ℂ)))=(Real.cosh (r*y):ℂ) := by
  rw [show (r:ℂ)*(Complex.I*(y:ℂ))=((r*y:ℝ):ℂ)*Complex.I by push_cast; ring,
    Complex.cos_mul_I,Complex.ofReal_cosh]

/-- The literal zero-frequency beta integral is exactly the positive real weighted integral with its original outside normalization.
Use: identifies the real value in wave_cosine_domination and proves wave_zero_pos.
Article: jacobi, Appendix C.1 (negative-energy bounds).
Proof: the zero-frequency cosine equals one; real inclusion commutes with the actual integral and normalization arithmetic. -/
theorem betaWave_zero (a t : ℝ) :
    betaWave a 0 t=
      (((betaNormalization (gamma a))⁻¹*(Real.sin (Real.pi*t)/Real.pi)^(1-gamma a)*
        (∫ s in (0:ℝ)..t,sineWeight (gamma a) t s):ℝ):ℂ) := by
  simp only [betaWave,sineIntegrand,sineWeight,mul_zero,Complex.cos_zero,mul_one,
    intervalIntegral.integral_ofReal,Complex.ofReal_mul,Complex.ofReal_inv]

/-- The actual reference wave at imaginary frequency has its genuine positive real cosh integral with the exact beta normalization.
Use: proves wave_imaginary_pos for the same reference solution used in the GL construction.
Article: jacobi, Appendix C.1 (negative-energy bounds).
Proof: rewrite the actual imaginary cosine as the real hyperbolic cosine and commute real inclusion with the integral. -/
theorem betaWave_imaginary (a t y : ℝ) :
    betaWave a (Complex.I*(y:ℂ)) t=
      (((betaNormalization (gamma a))⁻¹*(Real.sin (Real.pi*t)/Real.pi)^(1-gamma a)*
        (∫ s in (0:ℝ)..t,sineWeight (gamma a) t s*Real.cosh ((t-2*s)*y)):ℝ):ℂ) := by
  unfold betaWave sineIntegrand
  simp_rw [cosine_imaginary,← Complex.ofReal_mul]
  rw [intervalIntegral.integral_ofReal]
  push_cast
  rfl

/-- The actual zero-frequency reference function is strictly positive at every physical interior point.
Use: supplies the strictly positive majorizing function in wave_cosine_domination and the denominator at negative energy.
Article: jacobi, Appendix C.1 (negative-energy bounds).
Proof: the real sine-power density has genuine convergence and strict
interior positivity. Its integral and both original outside factors
are strictly positive throughout alpha>-1. -/
theorem wave_zero_pos {a : ℝ} (ha : -1<a) {t : ℝ} (ht : t∈Ioo (0:ℝ) 1) :
    0<(wave a 0 t).re := by
  -- No positivity of the reference eigenvalues is used; this is the actual original zero-frequency integral.
  have hg : 0<gamma a := by linarith [(parameters ha).1]
  rw [wave_beta_integral ha 0 ⟨ht.1.le,ht.2⟩,betaWave_zero,Complex.ofReal_re]
  have hi := intervalIntegral.intervalIntegral_pos_of_pos_on (sineWeight_integrable hg ht)
    (fun s hs => sineWeight_pos (gamma a) ht hs) ht.1
  exact mul_pos (mul_pos (inv_pos.mpr (betaNormalization_pos hg))
    (Real.rpow_pos_of_pos (div_pos
      (Real.sin_pos_of_pos_of_lt_pi (mul_pos Real.pi_pos ht.1)
        (by nlinarith [Real.pi_pos,ht.2])) Real.pi_pos) _)) hi

/-- The actual reference function is strictly positive at every imaginary frequency and physical interior point.
Use: proves the positivity assertion of Negative-energy bounds and justifies all later reference quotients at z=c_0-y^2.
Article: jacobi, Appendix C.1 (negative-energy bounds).
Proof: multiply the genuinely integrable positive sine density by the
continuous strictly positive real cosh multiplier. Its integral and the
same two normalizing factors are strictly positive. -/
theorem wave_imaginary_pos {a : ℝ} (ha : -1<a) (y : ℝ) {t : ℝ} (ht : t∈Ioo (0:ℝ) 1) :
    0<(wave a (Complex.I*(y:ℂ)) t).re := by
  -- Actual integrability is proved before the strict integral comparison, including at singular endpoint exponents.
  have hg : 0<gamma a := by linarith [(parameters ha).1]
  rw [wave_beta_integral ha _ ⟨ht.1.le,ht.2⟩,betaWave_imaginary,Complex.ofReal_re]
  have hc : ContinuousOn (fun s : ℝ => Real.cosh ((t-2*s)*y)) (uIcc (0:ℝ) t) := by fun_prop
  have hi := intervalIntegral.intervalIntegral_pos_of_pos_on
    ((sineWeight_integrable hg ht).mul_continuousOn hc)
    (fun s hs => mul_pos (sineWeight_pos (gamma a) ht hs) (Real.cosh_pos _)) ht.1
  exact mul_pos (mul_pos (inv_pos.mpr (betaNormalization_pos hg))
    (Real.rpow_pos_of_pos (div_pos
      (Real.sin_pos_of_pos_of_lt_pi (mul_pos Real.pi_pos ht.1)
        (by nlinarith [Real.pi_pos,ht.2])) Real.pi_pos) _)) hi

end
end jacobi.Reference

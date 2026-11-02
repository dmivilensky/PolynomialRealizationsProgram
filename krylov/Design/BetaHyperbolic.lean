import krylov.Design.IntrinsicSubstitution
import Mathlib.Analysis.Complex.Trigonometric

/-!
Article: main_krylov, apC:lem:poisson, beta representation of hyperbolic transforms.
Use: prove the actual pointwise logistic-coordinate identities and integrability
for the oscillatory sech and sech-square transforms, then identify their
genuine improper integrals with convergent Euler beta integrals.
Source: Euler's beta integral and the actual intrinsic-coordinate identities
from the jacobi formalization. No residue or Fourier formula is assumed.
-/

namespace krylov.Design
noncomputable section
open MeasureTheory Real Set Filter jacobi.Young
open scoped Topology

/-- The source Fourier phase, with angular frequency xi and no hidden 2*pi factor.
Article: main_krylov, apC:lem:poisson. -/
def angularPhase (ξ x : ℝ) : ℂ := Complex.exp (-(ξ : ℂ) * (x : ℂ) * Complex.I)

/-- The actual angular Fourier phase has unit modulus.
Article: main_krylov, apC:lem:poisson. -/
theorem norm_angularPhase (ξ x : ℝ) : ‖angularPhase ξ x‖ = 1 := by
  simp [angularPhase, Complex.norm_exp, Complex.mul_re, Complex.mul_im]

/-- The original sech times its actual oscillatory phase is integrable.
Article: main_krylov, apC:lem:poisson. -/
theorem integrable_sech_angularPhase (ξ : ℝ) :
    Integrable (fun x : ℝ => (sech x : ℂ) * angularPhase ξ x) := by
  have hs : Continuous (fun x : ℝ => (sech x : ℂ)) :=
    Complex.continuous_ofReal.comp (Real.continuous_cosh.inv₀ (fun x => (Real.cosh_pos x).ne'))
  apply sech_integrable.mono' (hs.mul (by unfold angularPhase; fun_prop)).aestronglyMeasurable
  filter_upwards [] with x
  change ‖(sech x : ℂ) * angularPhase ξ x‖ ≤ sech x
  rw [norm_mul, norm_angularPhase, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (sech_pos x)]

/-- The original squared sech times the actual oscillatory phase is integrable.
Article: main_krylov, apC:lem:poisson. -/
theorem integrable_sechSquared_angularPhase (ξ : ℝ) :
    Integrable (fun x : ℝ => ((sech x : ℂ) ^ 2) * angularPhase ξ x) := by
  have hs : Continuous (fun x : ℝ => (sech x : ℂ)) :=
    Complex.continuous_ofReal.comp (Real.continuous_cosh.inv₀ (fun x => (Real.cosh_pos x).ne'))
  apply sech_sq_integrable.mono' ((hs.pow 2).mul (by unfold angularPhase; fun_prop)).aestronglyMeasurable
  filter_upwards [] with x
  change ‖(sech x : ℂ) ^ 2 * angularPhase ξ x‖ ≤ sech x ^ 2
  rw [norm_mul, norm_angularPhase, mul_one, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (sech_pos x)]

/-- The positive intrinsic coordinate has its exact logarithm on the real branch.
Article: main_krylov, apC:lem:poisson. -/
theorem log_intrinsic (x : ℝ) : log (intrinsic x) = x + log (sech x) - log 2 := by
  have he : intrinsic x = exp x * sech x / 2 := by linarith [exp_sech_intrinsic x]
  rw [he, Real.log_div (mul_ne_zero (exp_pos x).ne' (sech_pos x).ne') (by norm_num),
    Real.log_mul (exp_pos x).ne' (sech_pos x).ne', Real.log_exp]

/-- The positive complementary intrinsic coordinate has its exact logarithm on the real branch.
Article: main_krylov, apC:lem:poisson. -/
theorem log_one_sub_intrinsic (x : ℝ) : log (1 - intrinsic x) = -x + log (sech x) - log 2 := by
  have he : 1 - intrinsic x = exp (-x) * sech x / 2 := by linarith [exp_neg_sech_intrinsic x]
  rw [he, Real.log_div (mul_ne_zero (exp_pos (-x)).ne' (sech_pos x).ne') (by norm_num),
    Real.log_mul (exp_pos (-x)).ne' (sech_pos x).ne', Real.log_exp]

/-- The beta integrand with half-real-part exponents pulls back to the actual sech Fourier integrand.
Article: main_krylov, apC:lem:poisson.
Proof: both positive real logarithms are known exactly, so combine their
complex exponential powers before cancelling the genuine intrinsic Jacobian. -/
theorem beta_sech_pullback (ξ x : ℝ) :
    ((1 / 2 : ℝ) * sech x ^ 2) •
      ((intrinsic x : ℂ) ^ (((1 : ℂ) - (ξ : ℂ) * Complex.I) / 2 - 1) *
        (1 - (intrinsic x : ℂ)) ^ (((1 : ℂ) + (ξ : ℂ) * Complex.I) / 2 - 1)) =
      (sech x : ℂ) * angularPhase ξ x := by
  have hu := intrinsic_mem x
  have h0 : (intrinsic x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hu.1.ne'
  have h1 : 1 - (intrinsic x : ℂ) ≠ 0 := by
    exact_mod_cast (sub_pos.mpr hu.2).ne'
  have hlu : Complex.log (intrinsic x : ℂ) = (x : ℂ) + (log (sech x) : ℂ) - (log 2 : ℂ) := by
    rw [← Complex.ofReal_log hu.1.le, log_intrinsic]
    push_cast
    rfl
  have hlv : Complex.log (1 - (intrinsic x : ℂ)) = -(x : ℂ) + (log (sech x) : ℂ) - (log 2 : ℂ) := by
    rw [show (1 : ℂ) - (intrinsic x : ℂ) = ((1 - intrinsic x : ℝ) : ℂ) by push_cast; rfl,
      ← Complex.ofReal_log (sub_pos.mpr hu.2).le, log_one_sub_intrinsic]
    push_cast
    rfl
  rw [Complex.cpow_def_of_ne_zero h0, Complex.cpow_def_of_ne_zero h1, ← Complex.exp_add,
    hlu, hlv]
  have hexp : ((x : ℂ) + (log (sech x) : ℂ) - (log 2 : ℂ)) *
      (((1 : ℂ) - (ξ : ℂ) * Complex.I) / 2 - 1) +
      (-(x : ℂ) + (log (sech x) : ℂ) - (log 2 : ℂ)) *
      (((1 : ℂ) + (ξ : ℂ) * Complex.I) / 2 - 1) =
      ((log 2 - log (sech x) : ℝ) : ℂ) + (-(ξ : ℂ) * (x : ℂ) * Complex.I) := by
    push_cast
    ring
  rw [hexp, Complex.exp_add, ← Complex.ofReal_exp, Real.exp_sub,
    Real.exp_log (by norm_num : (0 : ℝ) < 2), Real.exp_log (sech_pos x)]
  change (((1 / 2 : ℝ) * sech x ^ 2 : ℝ) : ℂ) *
    (((2 / sech x : ℝ) : ℂ) * angularPhase ξ x) = _
  push_cast
  field_simp [Complex.ofReal_ne_zero.mpr (sech_pos x).ne']

/-- The beta integrand with unit-real-part exponents pulls back to half the actual squared-sech Fourier integrand.
Article: main_krylov, apC:lem:poisson. -/
theorem beta_sechSquared_pullback (ξ x : ℝ) :
    ((1 / 2 : ℝ) * sech x ^ 2) •
      ((intrinsic x : ℂ) ^ (((2 : ℂ) - (ξ : ℂ) * Complex.I) / 2 - 1) *
        (1 - (intrinsic x : ℂ)) ^ (((2 : ℂ) + (ξ : ℂ) * Complex.I) / 2 - 1)) =
      (1 / 2 : ℂ) * ((sech x : ℂ) ^ 2 * angularPhase ξ x) := by
  have hu := intrinsic_mem x
  have h0 : (intrinsic x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hu.1.ne'
  have h1 : 1 - (intrinsic x : ℂ) ≠ 0 := by exact_mod_cast (sub_pos.mpr hu.2).ne'
  have hlu : Complex.log (intrinsic x : ℂ) = (x : ℂ) + (log (sech x) : ℂ) - (log 2 : ℂ) := by
    rw [← Complex.ofReal_log hu.1.le, log_intrinsic]
    push_cast
    rfl
  have hlv : Complex.log (1 - (intrinsic x : ℂ)) = -(x : ℂ) + (log (sech x) : ℂ) - (log 2 : ℂ) := by
    rw [show (1 : ℂ) - (intrinsic x : ℂ) = ((1 - intrinsic x : ℝ) : ℂ) by push_cast; rfl,
      ← Complex.ofReal_log (sub_pos.mpr hu.2).le, log_one_sub_intrinsic]
    push_cast
    rfl
  rw [Complex.cpow_def_of_ne_zero h0, Complex.cpow_def_of_ne_zero h1, ← Complex.exp_add,
    hlu, hlv]
  have hexp : ((x : ℂ) + (log (sech x) : ℂ) - (log 2 : ℂ)) *
      (((2 : ℂ) - (ξ : ℂ) * Complex.I) / 2 - 1) +
      (-(x : ℂ) + (log (sech x) : ℂ) - (log 2 : ℂ)) *
      (((2 : ℂ) + (ξ : ℂ) * Complex.I) / 2 - 1) = -(ξ : ℂ) * (x : ℂ) * Complex.I := by ring
  rw [hexp]
  change (((1 / 2 : ℝ) * sech x ^ 2 : ℝ) : ℂ) * angularPhase ξ x = _
  push_cast
  ring

end
end krylov.Design

import krylov.Design.HyperbolicTransforms
import Mathlib.Analysis.Fourier.FourierTransform

/-!
Article: main_krylov, apC:lem:poisson, the exact mathlib Fourier convention.
Use: bridge the proved angular-frequency hyperbolic transforms to mathlib's
2*pi convention and to the actual positively rescaled profiles used by Poisson.
Source: actual Lebesgue scaling and the independently proved Euler-beta transforms.
-/

namespace krylov.Design
noncomputable section
open Real Filter MeasureTheory jacobi.Young
open scoped FourierTransform

/-- Mathlib's normalized Fourier integral uses the source angular phase at frequency 2*pi*w.
Article: main_krylov, apC:lem:poisson. -/
theorem fourier_eq_angular_integral (f : ℝ → ℂ) (w : ℝ) :
    𝓕 f w = ∫ x : ℝ, f x * angularPhase (2 * π * w) x := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [smul_eq_mul, mul_comm]
  congr 1
  unfold angularPhase
  congr 1
  push_cast
  ring

/-- The actual angular Fourier integral obeys positive physical scaling.
Article: main_krylov, apC:lem:poisson.
Proof: reuse the genuine whole-line Lebesgue change of variables; its phase rescales algebraically. -/
theorem angular_integral_scale (f : ℝ → ℂ) {θ : ℝ} (hθ : 0 < θ) (ξ : ℝ) :
    (∫ x : ℝ, f (θ * x) * angularPhase ξ x) =
      (θ : ℂ)⁻¹ * ∫ y : ℝ, f y * angularPhase (ξ / θ) y := by
  have he : (fun x : ℝ => f (θ * x) * angularPhase ξ x) =
      (fun x : ℝ => (fun y : ℝ => f y * angularPhase (ξ / θ) y) (θ * x)) := by
    funext x
    congr 1
    unfold angularPhase
    congr 1
    push_cast
    field_simp [Complex.ofReal_ne_zero.mpr hθ.ne']
  rw [he]
  have hs := Measure.integral_comp_mul_left (fun y : ℝ => f y * angularPhase (ξ / θ) y) θ
  rw [abs_of_pos (inv_pos.mpr hθ)] at hs
  simpa only [Complex.real_smul, Complex.ofReal_inv] using! hs

/-- The actual scaled hyperbolic secant has the exact normalized Fourier transform.
Article: main_krylov, apC:lem:poisson.
Proof: actual measure scaling, angular-frequency beta evaluation, and the precise 2*pi dictionary. -/
theorem fourier_scaled_sech {θ : ℝ} (hθ : 0 < θ) (w : ℝ) :
    𝓕 (fun x : ℝ => (sech (θ * x) : ℂ)) w =
      ((π / θ : ℝ) : ℂ) * (sech (π ^ 2 * w / θ) : ℂ) := by
  rw [fourier_eq_angular_integral, angular_integral_scale (fun y => (sech y : ℂ)) hθ,
    integral_sech_angularPhase]
  have ha : π * (2 * π * w / θ) / 2 = π ^ 2 * w / θ := by ring
  rw [ha, sech]
  push_cast
  ring

/-- At zero frequency, the actual scaled squared-secant Fourier transform is 2/theta.
Article: main_krylov, apC:lem:poisson, the zero Poisson mode. -/
theorem fourier_scaled_sechSquared_zero {θ : ℝ} (hθ : 0 < θ) :
    𝓕 (fun x : ℝ => (sech (θ * x) : ℂ) ^ 2) 0 = ((2 / θ : ℝ) : ℂ) := by
  rw [fourier_eq_angular_integral, angular_integral_scale (fun y => (sech y : ℂ) ^ 2) hθ]
  norm_num only [mul_zero, zero_div, integral_sechSquared_angularPhase_zero]
  push_cast
  ring

/-- Away from zero, the actual scaled squared-secant Fourier transform has the exact weighted-cosecant formula.
Article: main_krylov, apC:lem:poisson, the nonzero Poisson modes. -/
theorem fourier_scaled_sechSquared {θ w : ℝ} (hθ : 0 < θ) (hw : w ≠ 0) :
    𝓕 (fun x : ℝ => (sech (θ * x) : ℂ) ^ 2) w =
      ((2 * π ^ 2 / θ ^ 2 * (w / sinh (π ^ 2 * w / θ)) : ℝ) : ℂ) := by
  rw [fourier_eq_angular_integral, angular_integral_scale (fun y => (sech y : ℂ) ^ 2) hθ,
    integral_sechSquared_angularPhase (div_ne_zero (mul_ne_zero
      (mul_ne_zero (by norm_num) Real.pi_ne_zero) hw) hθ.ne')]
  have ha : π * (2 * π * w / θ) / 2 = π ^ 2 * w / θ := by ring
  rw [ha]
  push_cast
  field_simp

end
end krylov.Design

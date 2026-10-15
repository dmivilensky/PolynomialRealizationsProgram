import «2610.05164v2».SineContinuum.ThetaFour
import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation

/-!
Article: 2610.05164v2, Proposition 2.
Poisson inversion exchanges the signed and half-characteristic theta constants.
Use: `«2610.05164v2».SineContinuum.thetaFour_positive` feeds
`«2610.05164v2».SineContinuum.thetaModulus_lt_one` (theta Modulus lt one).
Proof chain: `«2610.05164v2».LocalObstruction.sine_green_scale_tail` — 2610.05164v2, Theorem 6.1; No
locally sharp C1 bound from finitely many spectral observations.
Source: Stein and Shakarchi, Fourier Analysis; NIST Digital Library of Mathematical Functions,
Chapter 20 — Poisson summation and Jacobi theta identities. The needed form is proved here.
-/
namespace «2610.05164v2».SineContinuum
noncomputable section
open Real
set_option backward.isDefEq.respectTransparency false

/--
Poisson inversion for theta_3, using the community Gaussian Fourier theorem.

Exact identity `thetaThree v = (sqrt v)⁻¹*thetaThree v⁻¹`.

Use: `«2610.05164v2».SineContinuum.thetaModulus_inversion` rewrites with this identity to
establish exact identity `thetaModulus v⁻¹ = thetaFour v^2/thetaThree v^2`.

Article: 2610.05164v2, Proposition 2 via `«2610.05164v2».SineContinuum.n_theta`.

Source: Stein and Shakarchi, Fourier Analysis; NIST Digital Library of Mathematical Functions,
Chapter 20 — Poisson summation and Jacobi theta identities.

Proof: Identify the summands/integrands on their required domain before replacing the sum or
integral.
-/
theorem thetaThree_inversion {v : ℝ} (hv : 0 < v) :
    thetaThree v = (sqrt v)⁻¹*thetaThree v⁻¹ := by
  -- Identify the summands/integrands on their required domain before replacing the sum or
  -- integral.
  have h := Real.tsum_exp_neg_mul_int_sq hv
  rw [← sqrt_eq_rpow,one_div] at h
  convert h using 1
  · apply tsum_congr
    intro j
    unfold gaussianThetaTerm
    congr 1
    ring
  · congr 1
    apply tsum_congr
    intro j
    unfold gaussianThetaTerm
    congr 1
    ring

/--
Exact identity `Complex.exp (-π*(v:ℂ)*(j:ℂ)^2+2*π*(Complex.I/2)*(j:ℂ)) = (thetaFourTerm v
j:ℂ)`.

Use: `«2610.05164v2».SineContinuum.thetaFour_inversion` rewrites with this identity to
establish exact identity `thetaFour v = (sqrt v)⁻¹*thetaTwo v⁻¹`.

Article: 2610.05164v2, Proposition 2 via `«2610.05164v2».SineContinuum.n_theta`.

Source: Stein and Shakarchi, Fourier Analysis; NIST Digital Library of Mathematical Functions,
Chapter 20 — Poisson summation and Jacobi theta identities.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
private theorem poisson_signed_term (v : ℝ) (j : ℤ) :
    Complex.exp (-π*(v:ℂ)*(j:ℂ)^2+2*π*(Complex.I/2)*(j:ℂ)) =
      (thetaFourTerm v j:ℂ) := by
  -- Rewrite the definitions and library identities explicitly named in the proof, then
  -- discharge the resulting algebraic or order relation.
  rw [show -π*(v:ℂ)*(j:ℂ)^2+2*π*(Complex.I/2)*(j:ℂ) =
    ((-π*(j:ℝ)^2*v:ℝ):ℂ)+(j:ℂ)*((π:ℂ)*Complex.I) by push_cast; ring]
  rw [Complex.exp_add,Complex.exp_int_mul,Complex.exp_pi_mul_I]
  simp only [thetaFourTerm,gaussianThetaTerm,add_zero,Complex.ofReal_mul,
    Complex.ofReal_zpow,Complex.ofReal_neg,Complex.ofReal_one,Complex.ofReal_exp]
  ring

/--
Poisson inversion exchanges the signed and half-characteristic theta constants.

Exact identity `thetaFour v = (sqrt v)⁻¹*thetaTwo v⁻¹`.

Use: `«2610.05164v2».SineContinuum.thetaFour_positive` rewrites with this identity to establish
the stated quantitative bound `0 < thetaFour v`.

Article: 2610.05164v2, Proposition 2 via `«2610.05164v2».SineContinuum.n_theta`.

Source: Stein and Shakarchi, Fourier Analysis; NIST Digital Library of Mathematical Functions,
Chapter 20 — Poisson summation and Jacobi theta identities.

Proof: Use the identities/estimates `«2610.05164v2».SineContinuum.gaussianTheta_add_one`,
`_private.«2610.05164v2».SineContinuum.ThetaPoisson.0.«2610.05164v2».SineContinuum.poisson_signed_term`
with the arguments shown in the proof.
-/
theorem thetaFour_inversion {v : ℝ} (hv : 0 < v) :
    thetaFour v = (sqrt v)⁻¹*thetaTwo v⁻¹ := by
  -- Use the identities/estimates `«2610.05164v2».SineContinuum.gaussianTheta_add_one`,
  -- `_private.«2610.05164v2».SineContinuum.ThetaPoisson.0.«2610.05164v2».SineContinuum.poisson_signed_term`
  -- with the arguments shown in the proof.
  have h := Complex.tsum_exp_neg_quadratic
    (a:=(v:ℂ)) (by simpa only [Complex.ofReal_re] using hv) (Complex.I/2)
  simp_rw [poisson_signed_term] at h
  have he (j : ℤ) : Complex.exp (-π/(v:ℂ)*((j:ℂ)+Complex.I*(Complex.I/2))^2) =
      (gaussianThetaTerm (-1/2) v⁻¹ j:ℂ) := by
    rw [show (j:ℂ)+Complex.I*(Complex.I/2) = (j:ℂ)-1/2 by
      rw [← mul_div_assoc,Complex.I_mul_I]; ring]
    rw [gaussianThetaTerm,Complex.ofReal_exp]
    congr 1
    push_cast
    ring
  simp_rw [he] at h
  have hp : (v:ℂ)^(1/2:ℂ) = ((sqrt v:ℝ):ℂ) := by
    rw [sqrt_eq_rpow,Complex.ofReal_cpow hv.le]
    norm_num
  rw [hp,← Complex.ofReal_tsum,← Complex.ofReal_tsum] at h
  have hg : gaussianTheta (-1/2) v⁻¹ = thetaTwo v⁻¹ := by
    have ht := gaussianTheta_add_one (-1/2) v⁻¹
    norm_num [thetaTwo] at ht ⊢
    exact ht.symm
  change ((thetaFour v:ℝ):ℂ) = _ at h
  rw [show (∑' j : ℤ, gaussianThetaTerm (-1/2) v⁻¹ j) = gaussianTheta (-1/2) v⁻¹ by rfl,hg] at h
  have hr : thetaFour v = 1/sqrt v*thetaTwo v⁻¹ := by exact_mod_cast h
  simpa only [one_div] using hr

/--
The stated quantitative bound `0 < thetaFour v`.

Use: `«2610.05164v2».SineContinuum.thetaModulus_lt_one` uses this bound to establish the stated
quantitative bound `thetaModulus v < 1`.

Article: 2610.05164v2, Proposition 2 via `«2610.05164v2».SineContinuum.n_theta`.

Source: Stein and Shakarchi, Fourier Analysis; NIST Digital Library of Mathematical Functions,
Chapter 20 — Poisson summation and Jacobi theta identities.

Proof: Use the identities/estimates `«2610.05164v2».SineContinuum.thetaFour_inversion`,
`«2610.05164v2».SineContinuum.gaussianTheta_positive` with the arguments shown in the proof.
-/
theorem thetaFour_positive {v : ℝ} (hv : 0 < v) : 0 < thetaFour v := by
  rw [thetaFour_inversion hv]
  exact mul_pos (inv_pos.mpr (sqrt_pos.mpr hv)) (gaussianTheta_positive _ (inv_pos.mpr hv))

end
end «2610.05164v2».SineContinuum

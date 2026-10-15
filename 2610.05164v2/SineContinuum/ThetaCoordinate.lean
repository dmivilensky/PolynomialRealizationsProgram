import «2610.05164v2».SineContinuum.ThetaComplement
import «2610.05164v2».SineContinuum.ThetaBounds

/-!
Article: 2610.05164v2, Proposition 2.
The sine profile, evaluated at the point selected by the Gaussian theta constants.
Use: `«2610.05164v2».SineContinuum.thetaPoint_profile` feeds `«2610.05164v2».SineContinuum.n_theta`
(Proposition 2, equation (10): the actual sine density has the literal theta formula).
Proof chain: `«2610.05164v2».LocalObstruction.sine_green_scale_tail` — 2610.05164v2, Theorem 6.1; No
locally sharp C1 bound from finitely many spectral observations.
Source: Stein and Shakarchi, Fourier Analysis; NIST Digital Library of Mathematical Functions,
Chapter 20 — Poisson summation and Jacobi theta identities. The needed form is proved here.
-/
namespace «2610.05164v2».SineContinuum
noncomputable section
open Real Set
set_option backward.isDefEq.respectTransparency false

/--
Defines `thetaPoint` of type `ℝ` by `2/π*arcsin (thetaModulus v)`.

Use:
`_private.«2610.05164v2».SineContinuum.ThetaCoordinate.0.«2610.05164v2».SineContinuum.thetaPoint_half`
uses this definition to establish the identity `π*thetaPoint v/2 = arcsin (thetaModulus v)`.

Article: 2610.05164v2, Proposition 2 via `«2610.05164v2».SineContinuum.n_theta`.

Source: Stein and Shakarchi, Fourier Analysis; NIST Digital Library of Mathematical Functions,
Chapter 20 — Poisson summation and Jacobi theta identities.
-/
def thetaPoint (v : ℝ) : ℝ := 2/π*arcsin (thetaModulus v)

/--
Membership in the specified domain/enclosure: `thetaPoint v ∈ Ioo (0:ℝ) 1`.

Use: `«2610.05164v2».SineContinuum.thetaPoint_coordinate` rewrites with this assertion to
establish exact identity `X (thetaPoint v) = -(1/2)*log v`.

Article: 2610.05164v2, Proposition 2 via `«2610.05164v2».SineContinuum.n_theta`.

Source: Stein and Shakarchi, Fourier Analysis; NIST Digital Library of Mathematical Functions,
Chapter 20 — Poisson summation and Jacobi theta identities.

Proof: Use the identities/estimates `«2610.05164v2».SineContinuum.thetaModulus_positive`,
`«2610.05164v2».SineContinuum.thetaModulus_lt_one` with the arguments shown in the proof.
-/
theorem thetaPoint_mem {v : ℝ} (hv : 0 < v) : thetaPoint v ∈ Ioo (0:ℝ) 1 := by
  have ha := arcsin_pos.mpr (thetaModulus_positive hv)
  have hb := arcsin_lt_pi_div_two.mpr (thetaModulus_lt_one hv)
  constructor
  · exact mul_pos (div_pos (by norm_num) pi_pos) ha
  · unfold thetaPoint
    rw [div_mul_eq_mul_div,div_lt_one pi_pos]
    linarith

/--
Exact identity `π*thetaPoint v/2 = arcsin (thetaModulus v)`.

Use: `«2610.05164v2».SineContinuum.thetaPoint_cos_half` rewrites with this identity to
establish exact identity `cos (π*thetaPoint v/2) = thetaModulus v⁻¹`.

Article: 2610.05164v2, Proposition 2 via `«2610.05164v2».SineContinuum.n_theta`.

Source: Stein and Shakarchi, Fourier Analysis; NIST Digital Library of Mathematical Functions,
Chapter 20 — Poisson summation and Jacobi theta identities.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
private theorem thetaPoint_half (v : ℝ) : π*thetaPoint v/2 = arcsin (thetaModulus v) := by
  unfold thetaPoint
  field_simp

/--
Exact identity `sin (π*thetaPoint v/2) = thetaModulus v`.

Use: `«2610.05164v2».SineContinuum.thetaPoint_profile` rewrites with this identity to establish
exact identity `SineJacobi.phi (thetaPoint v) = 2*v*thetaTwo v^2*thetaFour v^2`.

Article: 2610.05164v2, Proposition 2 via `«2610.05164v2».SineContinuum.n_theta`.

Source: Stein and Shakarchi, Fourier Analysis; NIST Digital Library of Mathematical Functions,
Chapter 20 — Poisson summation and Jacobi theta identities.

Proof: Use the identities/estimates
`_private.«2610.05164v2».SineContinuum.ThetaCoordinate.0.«2610.05164v2».SineContinuum.thetaPoint_half`,
`«2610.05164v2».SineContinuum.thetaModulus_positive`,
`«2610.05164v2».SineContinuum.thetaModulus_lt_one` with the arguments shown in the proof.
-/
theorem thetaPoint_sin_half {v : ℝ} (hv : 0 < v) :
    sin (π*thetaPoint v/2) = thetaModulus v := by
  rw [thetaPoint_half,sin_arcsin (by linarith [thetaModulus_positive hv]) (thetaModulus_lt_one hv).le]

/--
Exact identity `cos (π*thetaPoint v/2) = thetaModulus v⁻¹`.

Use: `«2610.05164v2».SineContinuum.thetaPoint_sin` rewrites with this identity to establish
exact identity `sin (π*thetaPoint v) = 2*thetaModulus v*thetaModulus v⁻¹`.

Article: 2610.05164v2, Proposition 2 via `«2610.05164v2».SineContinuum.n_theta`.

Source: Stein and Shakarchi, Fourier Analysis; NIST Digital Library of Mathematical Functions,
Chapter 20 — Poisson summation and Jacobi theta identities.

Proof: Use the identities/estimates
`_private.«2610.05164v2».SineContinuum.ThetaCoordinate.0.«2610.05164v2».SineContinuum.thetaPoint_half`,
`«2610.05164v2».SineContinuum.thetaModulus_complement_sqrt` with the arguments shown in the
proof.
-/
theorem thetaPoint_cos_half {v : ℝ} (hv : 0 < v) :
    cos (π*thetaPoint v/2) = thetaModulus v⁻¹ := by rw [thetaPoint_half,cos_arcsin,thetaModulus_complement_sqrt hv]

/--
Exact identity `sin (π*(1-thetaPoint v)/2) = thetaModulus v⁻¹`.

Use: `«2610.05164v2».SineContinuum.thetaPoint_profiles` rewrites with this identity to
establish exact identity `r (thetaPoint v) = v*l (thetaPoint v)`.

Article: 2610.05164v2, Proposition 2 via `«2610.05164v2».SineContinuum.n_theta`.

Source: Stein and Shakarchi, Fourier Analysis; NIST Digital Library of Mathematical Functions,
Chapter 20 — Poisson summation and Jacobi theta identities.

Proof: Use the identities/estimates `«2610.05164v2».SineContinuum.thetaPoint_cos_half` with the
arguments shown in the proof.
-/
theorem thetaPoint_sin_reflect {v : ℝ} (hv : 0 < v) :
    sin (π*(1-thetaPoint v)/2) = thetaModulus v⁻¹ := by
  rw [show π*(1-thetaPoint v)/2 = π/2-π*thetaPoint v/2 by ring,sin_pi_div_two_sub,
    thetaPoint_cos_half hv]

/--
Exact identity `sin (π*thetaPoint v) = 2*thetaModulus v*thetaModulus v⁻¹`.

Use: `«2610.05164v2».SineContinuum.thetaPoint_profile` rewrites with this identity to establish
exact identity `SineJacobi.phi (thetaPoint v) = 2*v*thetaTwo v^2*thetaFour v^2`.

Article: 2610.05164v2, Proposition 2 via `«2610.05164v2».SineContinuum.n_theta`.

Source: Stein and Shakarchi, Fourier Analysis; NIST Digital Library of Mathematical Functions,
Chapter 20 — Poisson summation and Jacobi theta identities.

Proof: Use the identities/estimates `«2610.05164v2».SineContinuum.thetaPoint_sin_half`,
`«2610.05164v2».SineContinuum.thetaPoint_cos_half` with the arguments shown in the proof.
-/
theorem thetaPoint_sin {v : ℝ} (hv : 0 < v) :
    sin (π*thetaPoint v) = 2*thetaModulus v*thetaModulus v⁻¹ := by
  rw [show π*thetaPoint v = 2*(π*thetaPoint v/2) by ring,sin_two_mul,
    thetaPoint_sin_half hv,thetaPoint_cos_half hv]

/--
The elliptic-coordinate ratio is exactly the theta time.

Exact identity `r (thetaPoint v) = v*l (thetaPoint v)`.

Use: `«2610.05164v2».SineContinuum.thetaPoint_coordinate` rewrites with this identity to
establish exact identity `X (thetaPoint v) = -(1/2)*log v`.

Article: 2610.05164v2, Proposition 2 via `«2610.05164v2».SineContinuum.n_theta`.

Source: Stein and Shakarchi, Fourier Analysis; NIST Digital Library of Mathematical Functions,
Chapter 20 — Poisson summation and Jacobi theta identities.

Proof: Use the identities/estimates `«2610.05164v2».SineContinuum.l_formula`,
`«2610.05164v2».SineJacobi.ellipticK_square`,
`«2610.05164v2».SineContinuum.thetaPoint_sin_half` with the arguments shown in the proof.
-/
theorem thetaPoint_profiles {v : ℝ} (hv : 0 < v) :
    r (thetaPoint v) = v*l (thetaPoint v) := by
  rw [r,l_formula,l_formula,«2610.05164v2».SineJacobi.ellipticK_square,
    «2610.05164v2».SineJacobi.ellipticK_square,thetaPoint_sin_half hv,thetaPoint_sin_reflect hv,
    theta_elliptic_ratio hv]
  rw [show π*(1-thetaPoint v) = π-π*thetaPoint v by ring,sin_pi_sub]
  ring

/--
Exact identity `X (thetaPoint v) = -(1/2)*log v`.

Use: `«2610.05164v2».SineContinuum.n_theta` rewrites with this identity to establish exact
identity `n x = thetaDensity x`.

Article: 2610.05164v2, Proposition 2 via `«2610.05164v2».SineContinuum.n_theta`.

Source: Stein and Shakarchi, Fourier Analysis; NIST Digital Library of Mathematical Functions,
Chapter 20 — Poisson summation and Jacobi theta identities.

Proof: Use the identities/estimates `«2610.05164v2».SineContinuum.thetaPoint_profiles`,
`«2610.05164v2».SineContinuum.l_positive`, `«2610.05164v2».SineContinuum.thetaPoint_mem` with
the arguments shown in the proof.
-/
theorem thetaPoint_coordinate {v : ℝ} (hv : 0 < v) :
    X (thetaPoint v) = -(1/2)*log v := by
  rw [X,thetaPoint_profiles hv,log_mul hv.ne' (l_positive (thetaPoint_mem hv)).ne']
  ring

/--
The sine profile, evaluated at the point selected by the Gaussian theta constants.

Exact identity `SineJacobi.phi (thetaPoint v) = 2*v*thetaTwo v^2*thetaFour v^2`.

Use: `«2610.05164v2».SineContinuum.n_theta` rewrites with this identity to establish exact
identity `n x = thetaDensity x`.

Article: 2610.05164v2, Proposition 2 via `«2610.05164v2».SineContinuum.n_theta`.

Source: Stein and Shakarchi, Fourier Analysis; NIST Digital Library of Mathematical Functions,
Chapter 20 — Poisson summation and Jacobi theta identities.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem thetaPoint_profile {v : ℝ} (hv : 0 < v) :
    SineJacobi.phi (thetaPoint v) = 2*v*thetaTwo v^2*thetaFour v^2 := by
  -- Clear the denominators using the available nonzero hypotheses, then verify the remaining
  -- algebraic identity.
  rw [phi_product,thetaPoint_profiles hv,l_formula,SineJacobi.ellipticK_square,
    thetaPoint_sin_half hv,theta_ellipticK hv]
  have hs : 0 ≤ sin (π*thetaPoint v) :=
    (sin_pos_of_mem_Ioo ⟨by nlinarith [pi_pos,(thetaPoint_mem hv).1],
      by nlinarith [pi_pos,(thetaPoint_mem hv).2]⟩).le
  have he := sq_sqrt hs
  rw [thetaPoint_sin hv,thetaModulus_inversion hv] at he
  rw [thetaPoint_sin hv,thetaModulus_inversion hv]
  unfold thetaModulus at he ⊢
  have h3 : thetaThree v ≠ 0 := (gaussianTheta_positive 0 hv).ne'
  field_simp [pi_ne_zero,h3] at *
  nlinarith [he]

end
end «2610.05164v2».SineContinuum

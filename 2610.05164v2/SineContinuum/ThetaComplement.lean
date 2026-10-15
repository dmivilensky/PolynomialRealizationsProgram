import «2610.05164v2».SineContinuum.ThetaModulus

/-!
Article: 2610.05164v2, Proposition 2.
The elliptic period ratio is exactly the positive theta time parameter.
Use: `«2610.05164v2».SineContinuum.theta_elliptic_ratio` feeds
`«2610.05164v2».SineContinuum.thetaPoint_profiles` (The elliptic-coordinate ratio is exactly the
theta time).
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
Poisson inversion turns the complementary modulus into reciprocal nome time.

Exact identity `thetaModulus v⁻¹ = thetaFour v^2/thetaThree v^2`.

Use: `«2610.05164v2».SineContinuum.thetaModulus_complement` rewrites with this identity to
establish exact identity `1-thetaModulus v^2 = thetaModulus v⁻¹^2`.

Article: 2610.05164v2, Proposition 2 via `«2610.05164v2».SineContinuum.n_theta`.

Source: Stein and Shakarchi, Fourier Analysis; NIST Digital Library of Mathematical Functions,
Chapter 20 — Poisson summation and Jacobi theta identities.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem thetaModulus_inversion {v : ℝ} (hv : 0 < v) :
    thetaModulus v⁻¹ = thetaFour v^2/thetaThree v^2 := by
  rw [thetaFour_inversion hv,thetaThree_inversion hv]
  unfold thetaModulus
  field_simp [(sqrt_pos.mpr hv).ne',(gaussianTheta_positive 0 (inv_pos.mpr hv)).ne']

/--
Exact identity `1-thetaModulus v^2 = thetaModulus v⁻¹^2`.

Use: `«2610.05164v2».SineContinuum.thetaModulus_complement_sqrt` rewrites with this identity to
establish exact identity `sqrt (1-thetaModulus v^2) = thetaModulus v⁻¹`.

Article: 2610.05164v2, Proposition 2 via `«2610.05164v2».SineContinuum.n_theta`.

Source: Stein and Shakarchi, Fourier Analysis; NIST Digital Library of Mathematical Functions,
Chapter 20 — Poisson summation and Jacobi theta identities.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem thetaModulus_complement {v : ℝ} (hv : 0 < v) :
    1-thetaModulus v^2 = thetaModulus v⁻¹^2 := by
  rw [thetaModulus_inversion hv]
  unfold thetaModulus
  have he := theta_quartic hv
  field_simp [(show thetaThree v ≠ 0 from (gaussianTheta_positive 0 hv).ne')]
  nlinarith [he]

/--
Exact identity `sqrt (1-thetaModulus v^2) = thetaModulus v⁻¹`.

Use: `«2610.05164v2».SineContinuum.thetaPoint_cos_half` rewrites with this identity to
establish exact identity `cos (π*thetaPoint v/2) = thetaModulus v⁻¹`.

Article: 2610.05164v2, Proposition 2 via `«2610.05164v2».SineContinuum.n_theta`.

Source: Stein and Shakarchi, Fourier Analysis; NIST Digital Library of Mathematical Functions,
Chapter 20 — Poisson summation and Jacobi theta identities.

Proof: Use the identities/estimates `«2610.05164v2».SineContinuum.thetaModulus_complement`,
`«2610.05164v2».SineContinuum.thetaModulus_positive` with the arguments shown in the proof.
-/
theorem thetaModulus_complement_sqrt {v : ℝ} (hv : 0 < v) :
    sqrt (1-thetaModulus v^2) = thetaModulus v⁻¹ := by rw [thetaModulus_complement hv,sqrt_sq (thetaModulus_positive (inv_pos.mpr hv)).le]

/--
The elliptic period ratio is exactly the positive theta time parameter.

Exact identity `«2606.16671v2».SineJacobi.ellipticK (thetaModulus v⁻¹) =
v*«2606.16671v2».SineJacobi.ellipticK (thetaModulus v)`.

Use: `«2610.05164v2».SineContinuum.thetaPoint_profiles` rewrites with this identity to
establish exact identity `r (thetaPoint v) = v*l (thetaPoint v)`.

Article: 2610.05164v2, Proposition 2 via `«2610.05164v2».SineContinuum.n_theta`.

Source: Stein and Shakarchi, Fourier Analysis; NIST Digital Library of Mathematical Functions,
Chapter 20 — Poisson summation and Jacobi theta identities.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem theta_elliptic_ratio {v : ℝ} (hv : 0 < v) :
    «2606.16671v2».SineJacobi.ellipticK (thetaModulus v⁻¹) =
      v*«2606.16671v2».SineJacobi.ellipticK (thetaModulus v) := by
  rw [theta_ellipticK (inv_pos.mpr hv),theta_ellipticK hv,thetaThree_inversion hv]
  have hs := sq_sqrt hv.le
  field_simp [(sqrt_pos.mpr hv).ne']
  nlinarith [hs]

end
end «2610.05164v2».SineContinuum

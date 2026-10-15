import «2610.05164v2».SineContinuum.ThetaLimits
import «2606.16671v2».SineJacobi.EllipticLanden

/-!
Article: 2610.05164v2, Proposition 2.
The complete elliptic integral equals pi/2 times theta_3 squared.
Use: `«2610.05164v2».SineContinuum.theta_ellipticK` feeds
`«2610.05164v2».SineContinuum.theta_elliptic_ratio` (The elliptic period ratio is exactly the
positive theta time parameter).
Proof chain: `«2610.05164v2».LocalObstruction.sine_green_scale_tail` — 2610.05164v2, Theorem 6.1; No
locally sharp C1 bound from finitely many spectral observations.
Source: Stein and Shakarchi, Fourier Analysis; NIST Digital Library of Mathematical Functions,
Chapter 20 — Poisson summation and Jacobi theta identities. The needed form is proved here.
-/
namespace «2610.05164v2».SineContinuum
noncomputable section
open Real Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/--
Defines `thetaModulus` of type `ℝ` by `thetaTwo v^2/thetaThree v^2`.

Use: `«2610.05164v2».SineContinuum.thetaModulus_landen` uses this definition to establish exact
identity `thetaModulus v = 2*sqrt (thetaModulus (2*v))/(1+thetaModulus (2*v))`.

Article: 2610.05164v2, Proposition 2 via `«2610.05164v2».SineContinuum.n_theta`.

Source: Stein and Shakarchi, Fourier Analysis; NIST Digital Library of Mathematical Functions,
Chapter 20 — Poisson summation and Jacobi theta identities.
-/
def thetaModulus (v : ℝ) : ℝ := thetaTwo v^2/thetaThree v^2

/--
The stated quantitative bound `0 < thetaModulus v`.

Use: `«2610.05164v2».SineContinuum.theta_elliptic_duplication` rewrites with this bound to
establish exact identity `«2606.16671v2».SineJacobi.ellipticK (thetaModulus v)/thetaThree v^2 =
«2606.16671v2».SineJacobi.ellipticK (thetaModulus (2*v))/thetaThree (2*v)^2`.

Article: 2610.05164v2, Proposition 2 via `«2610.05164v2».SineContinuum.n_theta`.

Source: Stein and Shakarchi, Fourier Analysis; NIST Digital Library of Mathematical Functions,
Chapter 20 — Poisson summation and Jacobi theta identities.

Proof: Use the identities/estimates `«2610.05164v2».SineContinuum.gaussianTheta_positive` with
the arguments shown in the proof.
-/
theorem thetaModulus_positive {v : ℝ} (hv : 0 < v) : 0 < thetaModulus v :=
  div_pos (sq_pos_of_pos (gaussianTheta_positive _ hv))
    (sq_pos_of_pos (gaussianTheta_positive _ hv))

/--
The stated quantitative bound `thetaModulus v < 1`.

Use: `«2610.05164v2».SineContinuum.theta_elliptic_duplication` rewrites with this bound to
establish exact identity `«2606.16671v2».SineJacobi.ellipticK (thetaModulus v)/thetaThree v^2 =
«2606.16671v2».SineJacobi.ellipticK (thetaModulus (2*v))/thetaThree (2*v)^2`.

Article: 2610.05164v2, Proposition 2 via `«2610.05164v2».SineContinuum.n_theta`.

Source: Stein and Shakarchi, Fourier Analysis; NIST Digital Library of Mathematical Functions,
Chapter 20 — Poisson summation and Jacobi theta identities.

Proof: Use the identities/estimates `«2610.05164v2».SineContinuum.gaussianTheta_positive`,
`«2610.05164v2».SineContinuum.thetaFour_positive`, `«2610.05164v2».SineContinuum.theta_quartic`
with the arguments shown in the proof.
-/
theorem thetaModulus_lt_one {v : ℝ} (hv : 0 < v) : thetaModulus v < 1 := by
  have h₃ : 0 < thetaThree v := gaussianTheta_positive _ hv
  have h₂ : 0 < thetaTwo v := gaussianTheta_positive _ hv
  have h₄ := thetaFour_positive hv
  have he := theta_quartic hv
  have hlt : thetaTwo v^2 < thetaThree v^2 := by
    nlinarith [sq_nonneg (thetaTwo v^2-thetaThree v^2),pow_pos h₄ 4]
  exact (div_lt_one (sq_pos_of_pos h₃)).mpr hlt

/--
Exact identity `sqrt (thetaModulus v) = thetaTwo v/thetaThree v`.

Use: `«2610.05164v2».SineContinuum.thetaModulus_landen` rewrites with this identity to
establish exact identity `thetaModulus v = 2*sqrt (thetaModulus (2*v))/(1+thetaModulus (2*v))`.

Article: 2610.05164v2, Proposition 2 via `«2610.05164v2».SineContinuum.n_theta`.

Source: Stein and Shakarchi, Fourier Analysis; NIST Digital Library of Mathematical Functions,
Chapter 20 — Poisson summation and Jacobi theta identities.

Proof: Use the identities/estimates `«2610.05164v2».SineContinuum.gaussianTheta_positive` with
the arguments shown in the proof.
-/
theorem thetaModulus_sqrt {v : ℝ} (hv : 0 < v) :
    sqrt (thetaModulus v) = thetaTwo v/thetaThree v := by
  rw [thetaModulus,← div_pow,sqrt_sq]
  exact (div_pos (gaussianTheta_positive _ hv) (gaussianTheta_positive _ hv)).le

/--
The theta modulus obeys exactly the Landen transformation reused from 2606.16671v2.

Exact identity `thetaModulus v = 2*sqrt (thetaModulus (2*v))/(1+thetaModulus (2*v))`.

Use: `«2610.05164v2».SineContinuum.theta_elliptic_duplication` rewrites with this identity to
establish exact identity `«2606.16671v2».SineJacobi.ellipticK (thetaModulus v)/thetaThree v^2 =
«2606.16671v2».SineJacobi.ellipticK (thetaModulus (2*v))/thetaThree (2*v)^2`.

Article: 2610.05164v2, Proposition 2 via `«2610.05164v2».SineContinuum.n_theta`.

Source: Stein and Shakarchi, Fourier Analysis; NIST Digital Library of Mathematical Functions,
Chapter 20 — Poisson summation and Jacobi theta identities.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem thetaModulus_landen {v : ℝ} (hv : 0 < v) :
    thetaModulus v = 2*sqrt (thetaModulus (2*v))/(1+thetaModulus (2*v)) := by
  -- Clear the denominators using the available nonzero hypotheses, then verify the remaining
  -- algebraic identity.
  have h2v : 0 < 2*v := by positivity
  rw [thetaModulus_sqrt h2v]
  unfold thetaModulus
  rw [thetaTwo_duplication hv,thetaThree_duplication hv]
  have ha : thetaThree (2*v) ≠ 0 := (gaussianTheta_positive 0 h2v).ne'
  have hd : thetaThree (2*v)^2+thetaTwo (2*v)^2 ≠ 0 :=
    (add_pos_of_pos_of_nonneg (sq_pos_of_pos (gaussianTheta_positive 0 h2v)) (sq_nonneg _)).ne'
  field_simp [ha,hd]

/--
The normalized elliptic integral is invariant under theta duplication.

Exact identity `«2606.16671v2».SineJacobi.ellipticK (thetaModulus v)/thetaThree v^2 =
«2606.16671v2».SineJacobi.ellipticK (thetaModulus (2*v))/thetaThree (2*v)^2`.

Use: `«2610.05164v2».SineContinuum.theta_ellipticK` uses this identity to establish exact
identity `«2606.16671v2».SineJacobi.ellipticK (thetaModulus v) = (π/2)*thetaThree v^2`.

Article: 2610.05164v2, Proposition 2 via `«2610.05164v2».SineContinuum.n_theta`.

Source: Stein and Shakarchi, Fourier Analysis; NIST Digital Library of Mathematical Functions,
Chapter 20 — Poisson summation and Jacobi theta identities.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem theta_elliptic_duplication {v : ℝ} (hv : 0 < v) :
    «2606.16671v2».SineJacobi.ellipticK (thetaModulus v)/thetaThree v^2 =
      «2606.16671v2».SineJacobi.ellipticK (thetaModulus (2*v))/thetaThree (2*v)^2 := by
  -- Clear the denominators using the available nonzero hypotheses, then verify the remaining
  -- algebraic identity.
  have h2v : 0 < 2*v := by positivity
  rw [thetaModulus_landen hv,«2606.16671v2».SineJacobi.ellipticK_landen
    (thetaModulus_positive h2v).le (thetaModulus_lt_one h2v),thetaThree_duplication hv]
  unfold thetaModulus
  have ha : thetaThree (2*v) ≠ 0 := (gaussianTheta_positive 0 h2v).ne'
  have hd : thetaThree (2*v)^2+thetaTwo (2*v)^2 ≠ 0 :=
    (add_pos_of_pos_of_nonneg (sq_pos_of_pos (gaussianTheta_positive 0 h2v)) (sq_nonneg _)).ne'
  field_simp [ha,hd]

/--
Convergence along the specified source filter to the specified limit: `Tendsto thetaModulus
atTop (𝓝 0)`.

Use: `«2610.05164v2».SineContinuum.theta_ellipticK` uses this limit to establish the identity
`«2606.16671v2».SineJacobi.ellipticK (thetaModulus v) = (π/2)*thetaThree v^2`.

Article: 2610.05164v2, Proposition 2 via `«2610.05164v2».SineContinuum.n_theta`.

Source: Stein and Shakarchi, Fourier Analysis; NIST Digital Library of Mathematical Functions,
Chapter 20 — Poisson summation and Jacobi theta identities.

Proof: Use the identities/estimates `«2610.05164v2».SineContinuum.thetaTwo_tendsto_zero`,
`«2610.05164v2».SineContinuum.thetaThree_tendsto_one` with the arguments shown in the proof.
-/
theorem thetaModulus_tendsto_zero : Tendsto thetaModulus atTop (𝓝 0) := by
  have h := (thetaTwo_tendsto_zero.pow 2).div (thetaThree_tendsto_one.pow 2) (by norm_num)
  convert h using 1
  · rfl
  · norm_num

/--
The complete elliptic integral equals pi/2 times theta_3 squared. The proof iterates the proved
Landen identity and takes the Gaussian limit.

Exact identity `«2606.16671v2».SineJacobi.ellipticK (thetaModulus v) = (π/2)*thetaThree v^2`.

Use: `«2610.05164v2».SineContinuum.thetaPoint_profile` rewrites with this identity to establish
exact identity `SineJacobi.phi (thetaPoint v) = 2*v*thetaTwo v^2*thetaFour v^2`.

Article: 2610.05164v2, Proposition 2 via `«2610.05164v2».SineContinuum.n_theta`.

Source: Stein and Shakarchi, Fourier Analysis; NIST Digital Library of Mathematical Functions,
Chapter 20 — Poisson summation and Jacobi theta identities.

Proof: Induct on `j`; the recursive step uses the previous-stage assertion.
-/
theorem theta_ellipticK {v : ℝ} (hv : 0 < v) :
    «2606.16671v2».SineJacobi.ellipticK (thetaModulus v) = (π/2)*thetaThree v^2 := by
  -- Induct on `j`; the recursive step uses the previous-stage assertion.
  let F (w : ℝ) := «2606.16671v2».SineJacobi.ellipticK (thetaModulus w)/thetaThree w^2
  -- Record the convergence hF with its source filter and target limit before taking limits in
  -- the subsequent identities/bounds.
  have hF : Tendsto F atTop (𝓝 (π/2)) := by
    have hK := («2606.16671v2».SineJacobi.ellipticK_continuousAt (k:=0) (by norm_num)).tendsto.comp
      thetaModulus_tendsto_zero
    convert hK.div (thetaThree_tendsto_one.pow 2) (by norm_num) using 1
    · rfl
    · simp
  have hi (j : ℕ) : F (2^j*v) = F v := by
    induction j with
    | zero => simp
    | succ j hj =>
      rw [pow_succ,show (2:ℝ)^j*2*v = 2*(2^j*v) by ring]
      exact (theta_elliptic_duplication (by positivity : 0<(2:ℝ)^j*v)).symm.trans hj
  -- Record the convergence hd with its source filter and target limit before taking limits in
  -- the subsequent identities/bounds.
  have hd : Tendsto (fun j : ℕ => (2:ℝ)^j*v) atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1:ℝ)<2)).atTop_mul_const hv
  have he : F v = π/2 := tendsto_nhds_unique
    (tendsto_const_nhds.congr' (Filter.Eventually.of_forall fun j => (hi j).symm)) (hF.comp hd)
  exact (div_eq_iff (sq_pos_of_pos (gaussianTheta_positive 0 hv)).ne').mp he

end
end «2610.05164v2».SineContinuum

import «2610.05164v2».SineContinuum.ThetaLattice
import «2610.05164v2».SineContinuum.GaussianTheta

/-!
Article: 2610.05164v2, Proposition 2.
Classical theta_2 duplication at a positive imaginary argument.
Use: `«2610.05164v2».SineContinuum.thetaTwo_duplication` feeds
`«2610.05164v2».SineContinuum.theta_quartic` (Jacobi's quartic identity, derived from three proved
quadratic identities).
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
Exact identity `gaussianThetaTerm a v (thetaLattice p).1*gaussianThetaTerm a v (thetaLattice
p).2 = gaussianThetaTerm (a+(p.1.val:ℝ)/2) (2*v) p.2.1 * gaussianThetaTerm ((p.1.val:ℝ)/2)
(2*v) p.2.2`.

Use: `«2610.05164v2».SineContinuum.gaussianTheta_duplication` uses this identity to establish
exact identity `gaussianTheta a v^2 = gaussianTheta a (2*v)*gaussianTheta 0 (2*v)+
gaussianTheta (a+1/2) (2*v)*gaussianTheta (1/2) (2*v)`.

Article: 2610.05164v2, Proposition 2 via `«2610.05164v2».SineContinuum.n_theta`.

Source: Stein and Shakarchi, Fourier Analysis; NIST Digital Library of Mathematical Functions,
Chapter 20 — Poisson summation and Jacobi theta identities.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem theta_rotated_gaussian (a v : ℝ) (p : Fin 2 × ℤ × ℤ) :
    gaussianThetaTerm a v (thetaLattice p).1*gaussianThetaTerm a v (thetaLattice p).2 =
      gaussianThetaTerm (a+(p.1.val:ℝ)/2) (2*v) p.2.1 *
        gaussianThetaTerm ((p.1.val:ℝ)/2) (2*v) p.2.2 := by
  -- Rewrite the definitions and library identities explicitly named in the proof, then
  -- discharge the resulting algebraic or order relation.
  unfold gaussianThetaTerm
  rw [← exp_add,← exp_add]
  congr 1
  change -π*((((p.2.1+p.2.2+(p.1.val:ℤ)):ℤ):ℝ)+a)^2*v +
    -π*(((p.2.1-p.2.2:ℤ):ℝ)+a)^2*v = _
  push_cast
  ring

/--
Gaussian theta duplication by an explicit even/odd lattice bijection.

Exact identity `gaussianTheta a v^2 = gaussianTheta a (2*v)*gaussianTheta 0 (2*v)+
gaussianTheta (a+1/2) (2*v)*gaussianTheta (1/2) (2*v)`.

Use: `«2610.05164v2».SineContinuum.thetaThree_duplication` uses this identity to establish
exact identity `thetaThree v^2 = thetaThree (2*v)^2+thetaTwo (2*v)^2`.

Article: 2610.05164v2, Proposition 2 via `«2610.05164v2».SineContinuum.n_theta`.

Source: Stein and Shakarchi, Fourier Analysis; NIST Digital Library of Mathematical Functions,
Chapter 20 — Poisson summation and Jacobi theta identities.

Proof: Identify the summands/integrands on their required domain before replacing the sum or
integral. Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem gaussianTheta_duplication (a : ℝ) {v : ℝ} (hv : 0 < v) :
    gaussianTheta a v^2 = gaussianTheta a (2*v)*gaussianTheta 0 (2*v)+
      gaussianTheta (a+1/2) (2*v)*gaussianTheta (1/2) (2*v) := by
  -- Identify the summands/integrands on their required domain before replacing the sum or
  -- integral.
  have hs := gaussianTheta_summable a hv
  have hp := hs.mul_of_nonneg hs (fun _ => (exp_pos _).le) (fun _ => (exp_pos _).le)
  -- Prove the summability hr needed for the later infinite-sum manipulations.
  have hr : Summable (fun p : Fin 2 × ℤ × ℤ =>
      gaussianThetaTerm (a+(p.1.val:ℝ)/2) (2*v) p.2.1 *
        gaussianThetaTerm ((p.1.val:ℝ)/2) (2*v) p.2.2) := by
    have h := thetaLattice.summable_iff.mpr hp
    convert h using 1
    funext p
    exact (theta_rotated_gaussian a v p).symm
  calc
    _ = ∑' p : ℤ × ℤ, gaussianThetaTerm a v p.1*gaussianThetaTerm a v p.2 := by
      rw [pow_two]
      exact hs.tsum_mul_tsum hs hp
    _ = ∑' p : Fin 2 × ℤ × ℤ,
        gaussianThetaTerm (a+(p.1.val:ℝ)/2) (2*v) p.2.1 *
          gaussianThetaTerm ((p.1.val:ℝ)/2) (2*v) p.2.2 := by
      rw [← thetaLattice.tsum_eq]
      exact tsum_congr (theta_rotated_gaussian a v)
    _ = ∑' r : Fin 2, gaussianTheta (a+(r.val:ℝ)/2) (2*v)*gaussianTheta ((r.val:ℝ)/2) (2*v) := by
      rw [hr.tsum_prod]
      apply tsum_congr
      intro r
      have h₁ := gaussianTheta_summable (a+(r.val:ℝ)/2) (mul_pos (by norm_num : (0:ℝ)<2) hv)
      have h₂ := gaussianTheta_summable ((r.val:ℝ)/2) (mul_pos (by norm_num : (0:ℝ)<2) hv)
      exact (h₁.tsum_mul_tsum h₂
        (h₁.mul_of_nonneg h₂ (fun _ => (exp_pos _).le) (fun _ => (exp_pos _).le))).symm
    _ = _ := by rw [tsum_fintype,Fin.sum_univ_two]; norm_num

/--
Classical theta_3 duplication at a positive imaginary argument.

Exact identity `thetaThree v^2 = thetaThree (2*v)^2+thetaTwo (2*v)^2`.

Use: `«2610.05164v2».SineContinuum.thetaModulus_landen` rewrites with this identity to
establish exact identity `thetaModulus v = 2*sqrt (thetaModulus (2*v))/(1+thetaModulus (2*v))`.

Article: 2610.05164v2, Proposition 2 via `«2610.05164v2».SineContinuum.n_theta`.

Source: Stein and Shakarchi, Fourier Analysis; NIST Digital Library of Mathematical Functions,
Chapter 20 — Poisson summation and Jacobi theta identities.

Proof: Use the identities/estimates `«2610.05164v2».SineContinuum.gaussianTheta_duplication`
with the arguments shown in the proof.
-/
theorem thetaThree_duplication {v : ℝ} (hv : 0 < v) :
    thetaThree v^2 = thetaThree (2*v)^2+thetaTwo (2*v)^2 := by simpa only [thetaThree,thetaTwo,zero_add,← pow_two] using gaussianTheta_duplication 0 hv

/--
Classical theta_2 duplication at a positive imaginary argument.

Exact identity `thetaTwo v^2 = 2*thetaThree (2*v)*thetaTwo (2*v)`.

Use: `«2610.05164v2».SineContinuum.thetaModulus_landen` rewrites with this identity to
establish exact identity `thetaModulus v = 2*sqrt (thetaModulus (2*v))/(1+thetaModulus (2*v))`.

Article: 2610.05164v2, Proposition 2 via `«2610.05164v2».SineContinuum.n_theta`.

Source: Stein and Shakarchi, Fourier Analysis; NIST Digital Library of Mathematical Functions,
Chapter 20 — Poisson summation and Jacobi theta identities.

Proof: Use the identities/estimates `«2610.05164v2».SineContinuum.gaussianTheta_duplication`,
`«2610.05164v2».SineContinuum.gaussianTheta_add_one` with the arguments shown in the proof.
-/
theorem thetaTwo_duplication {v : ℝ} (hv : 0 < v) :
    thetaTwo v^2 = 2*thetaThree (2*v)*thetaTwo (2*v) := by
  -- Use the identities/estimates `«2610.05164v2».SineContinuum.gaussianTheta_duplication`,
  -- `«2610.05164v2».SineContinuum.gaussianTheta_add_one` with the arguments shown in the
  -- proof.
  have h := gaussianTheta_duplication (1/2) hv
  rw [show (1/2:ℝ)+1/2 = 0+1 by norm_num,gaussianTheta_add_one] at h
  change thetaTwo v^2 = _ at h
  change thetaTwo v^2 = _
  rw [h]
  dsimp [thetaThree,thetaTwo]
  ring

end
end «2610.05164v2».SineContinuum

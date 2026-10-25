import chebyshev2.SineContinuum.ThetaDuplication

/-!
Article: chebyshev2, Proposition 2.
Jacobi's quartic identity, derived from three proved quadratic identities.
Use: `chebyshev2.SineContinuum.theta_quartic` feeds
`chebyshev2.SineContinuum.thetaModulus_lt_one` (theta Modulus lt one).
Proof chain: `chebyshev2.LocalObstruction.sine_green_scale_tail` — chebyshev2, Theorem 6.1; No
locally sharp C1 bound from finitely many spectral observations.
Source: Stein and Shakarchi, Fourier Analysis; NIST Digital Library of Mathematical Functions,
Chapter 20 — Poisson summation and Jacobi theta identities. The needed form is proved here.
-/
namespace chebyshev2.SineContinuum
noncomputable section
open Real
set_option backward.isDefEq.respectTransparency false

/--
Defines `thetaFourTerm` of type `ℝ` by `(-1:ℝ)^j*gaussianThetaTerm 0 v j`.

Use:
`_private.chebyshev2.SineContinuum.ThetaFour.0.chebyshev2.SineContinuum.rotated_signed`
uses this definition to establish the identity stated in that declaration.

Article: chebyshev2, Proposition 2 via `chebyshev2.SineContinuum.n_theta`.

Source: Stein and Shakarchi, Fourier Analysis; NIST Digital Library of Mathematical Functions,
Chapter 20 — Poisson summation and Jacobi theta identities.
-/
def thetaFourTerm (v : ℝ) (j : ℤ) : ℝ := (-1:ℝ)^j*gaussianThetaTerm 0 v j
/--
Defines `thetaFour` of type `ℝ` by `∑' j : ℤ, thetaFourTerm v j`.

Use: `chebyshev2.SineContinuum.thetaFour_duplication` uses this definition to establish
exact identity `thetaFour v^2 = thetaThree (2*v)^2-thetaTwo (2*v)^2`.

Article: chebyshev2, Proposition 2 via `chebyshev2.SineContinuum.n_theta`.

Source: Stein and Shakarchi, Fourier Analysis; NIST Digital Library of Mathematical Functions,
Chapter 20 — Poisson summation and Jacobi theta identities.
-/
def thetaFour (v : ℝ) : ℝ := ∑' j : ℤ, thetaFourTerm v j

/--
Exact identity `‖thetaFourTerm v j‖ = gaussianThetaTerm 0 v j`.

Use: `chebyshev2.SineContinuum.thetaFour_duplication` uses this identity to establish exact
identity `thetaFour v^2 = thetaThree (2*v)^2-thetaTwo (2*v)^2`.

Article: chebyshev2, Proposition 2 via `chebyshev2.SineContinuum.n_theta`.

Source: Stein and Shakarchi, Fourier Analysis; NIST Digital Library of Mathematical Functions,
Chapter 20 — Poisson summation and Jacobi theta identities.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem thetaFourTerm_norm (v : ℝ) (j : ℤ) :
    ‖thetaFourTerm v j‖ = gaussianThetaTerm 0 v j := by simp [thetaFourTerm,Real.norm_eq_abs,gaussianThetaTerm]

/--
Summability of the displayed sequence: `Summable (thetaFourTerm v)`.

Use: `chebyshev2.SineContinuum.thetaFour_duplication` uses this summability result to
establish exact identity `thetaFour v^2 = thetaThree (2*v)^2-thetaTwo (2*v)^2`.

Article: chebyshev2, Proposition 2 via `chebyshev2.SineContinuum.n_theta`.

Source: Stein and Shakarchi, Fourier Analysis; NIST Digital Library of Mathematical Functions,
Chapter 20 — Poisson summation and Jacobi theta identities.

Proof: Use the identities/estimates `chebyshev2.SineContinuum.thetaFourTerm_norm`,
`chebyshev2.SineContinuum.gaussianTheta_summable` with the arguments shown in the proof.
-/
theorem thetaFour_summable {v : ℝ} (hv : 0 < v) : Summable (thetaFourTerm v) := by
  apply Summable.of_norm
  simpa only [thetaFourTerm_norm] using gaussianTheta_summable 0 hv

/--
The signed Gaussian theta constant is exactly the article's sigma_2.

Exact identity `thetaFour v = sigma₂ (exp (-π*v))`.

Use: `chebyshev2.SineContinuum.n_theta` rewrites with this identity to establish exact
identity `n x = thetaDensity x`.

Article: chebyshev2, Proposition 2 via `chebyshev2.SineContinuum.n_theta`.

Source: Stein and Shakarchi, Fourier Analysis; NIST Digital Library of Mathematical Functions,
Chapter 20 — Poisson summation and Jacobi theta identities.

Proof: Use the identities/estimates `chebyshev2.SineContinuum.sigma₂_summable` with the
arguments shown in the proof.
-/
theorem thetaFour_sigma₂ {v : ℝ} (hv : 0 < v) :
    thetaFour v = sigma₂ (exp (-π*v)) := by
  -- Use the identities/estimates `chebyshev2.SineContinuum.sigma₂_summable` with the
  -- arguments shown in the proof.
  have hq : exp (-π*v) < 1 := exp_lt_one_iff.mpr (by nlinarith [pi_pos,hv])
  have ht (j : ℕ) : (-1:ℝ)^(j+1)*exp (-π*v)^((j+1)^2) =
      thetaFourTerm v ((j:ℤ)+1) := by
    simp only [thetaFourTerm,gaussianThetaTerm,add_zero,← exp_nat_mul]
    congr 2
    push_cast
    ring
  have hs : HasSum (fun j : ℕ => thetaFourTerm v ((j:ℤ)+1))
      (∑' j : ℕ, (-1:ℝ)^(j+1)*exp (-π*v)^((j+1)^2)) := by
    simpa only [ht] using (sigma₂_summable (exp_pos _).le hq).hasSum
  have hn (j : ℕ) : thetaFourTerm v (-((j:ℤ)+1)) = thetaFourTerm v ((j:ℤ)+1) := by
    unfold thetaFourTerm gaussianThetaTerm
    rw [zpow_neg,← inv_zpow,inv_neg_one]
    congr 2
    push_cast
    ring
  have hs' : HasSum (fun j : ℕ => thetaFourTerm v (-((j:ℤ)+1)))
      (∑' j : ℕ, (-1:ℝ)^(j+1)*exp (-π*v)^((j+1)^2)) := by
    simpa only [hn] using hs
  have h := hs.of_add_one_of_neg_add_one hs'
  change (∑' j : ℤ, thetaFourTerm v j) = _
  rw [h.tsum_eq]
  simp only [thetaFourTerm,gaussianThetaTerm,zpow_zero,Int.cast_zero,zero_add,
    zero_pow (by norm_num : 2 ≠ 0),mul_zero,zero_mul,exp_zero,one_mul]
  unfold sigma₂
  ring

/--
Exact identity `thetaFourTerm v (thetaLattice p).1*thetaFourTerm v (thetaLattice p).2 =
(-1:ℝ)^(p.1.val)* (gaussianThetaTerm ((p.1.val:ℝ)/2) (2*v) p.2.1 * gaussianThetaTerm
((p.1.val:ℝ)/2) (2*v) p.2.2)`.

Use: `chebyshev2.SineContinuum.thetaFour_duplication` uses this identity to establish exact
identity `thetaFour v^2 = thetaThree (2*v)^2-thetaTwo (2*v)^2`.

Article: chebyshev2, Proposition 2 via `chebyshev2.SineContinuum.n_theta`.

Source: Stein and Shakarchi, Fourier Analysis; NIST Digital Library of Mathematical Functions,
Chapter 20 — Poisson summation and Jacobi theta identities.

Proof: Use the identities/estimates `chebyshev2.SineContinuum.theta_rotated_gaussian` with
the arguments shown in the proof.
-/
private theorem rotated_signed (v : ℝ) (p : Fin 2 × ℤ × ℤ) :
    thetaFourTerm v (thetaLattice p).1*thetaFourTerm v (thetaLattice p).2 =
      (-1:ℝ)^(p.1.val)*
        (gaussianThetaTerm ((p.1.val:ℝ)/2) (2*v) p.2.1 *
          gaussianThetaTerm ((p.1.val:ℝ)/2) (2*v) p.2.2) := by
  -- Use the identities/estimates `chebyshev2.SineContinuum.theta_rotated_gaussian` with
  -- the arguments shown in the proof.
  have hs : (-1:ℝ)^(thetaLattice p).1 * (-1:ℝ)^(thetaLattice p).2 = (-1:ℝ)^p.1.val := by
    rw [← zpow_add₀ (by norm_num : (-1:ℝ) ≠ 0)]
    change (-1:ℝ)^((p.2.1+p.2.2+(p.1.val:ℤ))+(p.2.1-p.2.2)) = _
    rw [show (p.2.1+p.2.2+(p.1.val:ℤ))+(p.2.1-p.2.2) = 2*p.2.1+(p.1.val:ℤ) by ring,
      zpow_add₀ (by norm_num : (-1:ℝ) ≠ 0),zpow_mul]
    norm_num
  calc
    _ = ((-1:ℝ)^(thetaLattice p).1 * (-1:ℝ)^(thetaLattice p).2) *
        (gaussianThetaTerm 0 v (thetaLattice p).1*gaussianThetaTerm 0 v (thetaLattice p).2) := by
      unfold thetaFourTerm; ring
    _ = _ := by rw [hs,theta_rotated_gaussian]; simp only [zero_add]

/--
The signed theta duplication identity, proved by the same lattice bijection.

Exact identity `thetaFour v^2 = thetaThree (2*v)^2-thetaTwo (2*v)^2`.

Use: `chebyshev2.SineContinuum.theta_quartic` uses this identity to establish exact
identity `thetaThree v^4 = thetaFour v^4+thetaTwo v^4`.

Article: chebyshev2, Proposition 2 via `chebyshev2.SineContinuum.n_theta`.

Source: Stein and Shakarchi, Fourier Analysis; NIST Digital Library of Mathematical Functions,
Chapter 20 — Poisson summation and Jacobi theta identities.

Proof: Identify the summands/integrands on their required domain before replacing the sum or
integral. Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem thetaFour_duplication {v : ℝ} (hv : 0 < v) :
    thetaFour v^2 = thetaThree (2*v)^2-thetaTwo (2*v)^2 := by
  -- Identify the summands/integrands on their required domain before replacing the sum or
  -- integral.
  have hs := thetaFour_summable hv
  -- Prove the summability hn needed for the later infinite-sum manipulations.
  have hn : Summable (fun j : ℤ => ‖thetaFourTerm v j‖) := by
    simpa only [thetaFourTerm_norm] using gaussianTheta_summable 0 hv
  have hp := summable_mul_of_summable_norm hn hn
  -- Prove the summability hr needed for the later infinite-sum manipulations.
  have hr : Summable (fun p : Fin 2 × ℤ × ℤ => (-1:ℝ)^p.1.val *
      (gaussianThetaTerm ((p.1.val:ℝ)/2) (2*v) p.2.1 *
        gaussianThetaTerm ((p.1.val:ℝ)/2) (2*v) p.2.2)) := by
    have h := thetaLattice.summable_iff.mpr hp
    convert h using 1
    funext p
    exact (rotated_signed v p).symm
  calc
    _ = ∑' p : ℤ × ℤ, thetaFourTerm v p.1*thetaFourTerm v p.2 := by
      rw [pow_two]; exact hs.tsum_mul_tsum hs hp
    _ = ∑' p : Fin 2 × ℤ × ℤ, (-1:ℝ)^p.1.val *
        (gaussianThetaTerm ((p.1.val:ℝ)/2) (2*v) p.2.1 *
          gaussianThetaTerm ((p.1.val:ℝ)/2) (2*v) p.2.2) := by
      rw [← thetaLattice.tsum_eq]
      exact tsum_congr (rotated_signed v)
    _ = ∑' r : Fin 2, (-1:ℝ)^r.val * gaussianTheta ((r.val:ℝ)/2) (2*v)^2 := by
      rw [hr.tsum_prod]
      apply tsum_congr
      intro r
      dsimp only
      rw [tsum_mul_left]
      congr 1
      have h := gaussianTheta_summable ((r.val:ℝ)/2) (mul_pos (by norm_num : (0:ℝ)<2) hv)
      exact (h.tsum_mul_tsum h
        (h.mul_of_nonneg h (fun _ => (exp_pos _).le) (fun _ => (exp_pos _).le))).symm.trans
        (pow_two _).symm
    _ = _ := by
      rw [tsum_fintype,Fin.sum_univ_two]
      simp [thetaThree,thetaTwo,sub_eq_add_neg]

/--
Jacobi's quartic identity, derived from three proved quadratic identities.

Exact identity `thetaThree v^4 = thetaFour v^4+thetaTwo v^4`.

Use: `chebyshev2.SineContinuum.thetaModulus_complement` uses this identity to establish
exact identity `1-thetaModulus v^2 = thetaModulus v⁻¹^2`.

Article: chebyshev2, Proposition 2 via `chebyshev2.SineContinuum.n_theta`.

Source: Stein and Shakarchi, Fourier Analysis; NIST Digital Library of Mathematical Functions,
Chapter 20 — Poisson summation and Jacobi theta identities.

Proof: Use the identities/estimates `chebyshev2.SineContinuum.thetaThree_duplication`,
`chebyshev2.SineContinuum.thetaTwo_duplication`,
`chebyshev2.SineContinuum.thetaFour_duplication` with the arguments shown in the proof.
-/
theorem theta_quartic {v : ℝ} (hv : 0 < v) :
    thetaThree v^4 = thetaFour v^4+thetaTwo v^4 := by
  -- Use the identities/estimates `chebyshev2.SineContinuum.thetaThree_duplication`,
  -- `chebyshev2.SineContinuum.thetaTwo_duplication`,
  -- `chebyshev2.SineContinuum.thetaFour_duplication` with the arguments shown in the
  -- proof.
  have h₃ := thetaThree_duplication hv
  have h₂ := thetaTwo_duplication hv
  have h₄ := thetaFour_duplication hv
  calc
    _ = (thetaThree (2*v)^2+thetaTwo (2*v)^2)^2 := by rw [← h₃]; ring
    _ = (thetaThree (2*v)^2-thetaTwo (2*v)^2)^2+
        (2*thetaThree (2*v)*thetaTwo (2*v))^2 := by ring
    _ = _ := by rw [← h₄,← h₂]; ring

end
end chebyshev2.SineContinuum

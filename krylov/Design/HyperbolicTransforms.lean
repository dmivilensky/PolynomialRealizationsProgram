import krylov.Design.BetaHyperbolic

/-!
Article: main_krylov, apC:lem:poisson, exact hyperbolic Fourier transforms.
Use: evaluate the genuine integrable angular-frequency transforms through
Euler beta integrals and Gamma reflection. The squared-secant transform keeps
its actual value two at the removable zero-frequency singularity.
Source: Euler beta--Gamma identity and reflection formula, both imported from
mathlib, after the independently proved actual improper substitution.
-/

namespace krylov.Design
noncomputable section
open MeasureTheory Real Set Filter jacobi.Young
open scoped Topology

/-- The actual sech transform is the convergent beta integral with half-real-part parameters.
Article: main_krylov, apC:lem:poisson. -/
theorem integral_sech_angularPhase_eq_beta (ξ : ℝ) :
    (∫ x : ℝ, (sech x : ℂ) * angularPhase ξ x) =
      Complex.betaIntegral (((1 : ℂ) - (ξ : ℂ) * Complex.I) / 2)
        (((1 : ℂ) + (ξ : ℂ) * Complex.I) / 2) := by
  let z : ℂ := ((1 : ℂ) - (ξ : ℂ) * Complex.I) / 2
  let w : ℂ := ((1 : ℂ) + (ξ : ℂ) * Complex.I) / 2
  let g : ℝ → ℂ := fun t => (t : ℂ) ^ (z - 1) * (1 - (t : ℂ)) ^ (w - 1)
  have hi : IntervalIntegrable g volume 0 1 := Complex.betaIntegral_convergent
    (by norm_num [z, Complex.div_re]) (by norm_num [w, Complex.div_re])
  have hp (x : ℝ) : ((1 / 2 : ℝ) * sech x ^ 2) • g (intrinsic x) =
      (sech x : ℂ) * angularPhase ξ x := beta_sech_pullback ξ x
  have hint : Integrable (fun x : ℝ => ((1 / 2 : ℝ) * sech x ^ 2) • g (intrinsic x)) :=
    (integrable_sech_angularPhase ξ).congr (Eventually.of_forall (fun x => (hp x).symm))
  have h := integral_intrinsic_substitution g hi (betaIntegrand_continuousOn z w) hint
  rw [integral_congr_ae (Eventually.of_forall hp)] at h
  exact h

/-- The actual squared-sech transform is twice its convergent unit-real-part beta integral.
Article: main_krylov, apC:lem:poisson. -/
theorem integral_sechSquared_angularPhase_eq_beta (ξ : ℝ) :
    (∫ x : ℝ, (sech x : ℂ) ^ 2 * angularPhase ξ x) =
      2 * Complex.betaIntegral (((2 : ℂ) - (ξ : ℂ) * Complex.I) / 2)
        (((2 : ℂ) + (ξ : ℂ) * Complex.I) / 2) := by
  let z : ℂ := ((2 : ℂ) - (ξ : ℂ) * Complex.I) / 2
  let w : ℂ := ((2 : ℂ) + (ξ : ℂ) * Complex.I) / 2
  let g : ℝ → ℂ := fun t => (t : ℂ) ^ (z - 1) * (1 - (t : ℂ)) ^ (w - 1)
  have hi : IntervalIntegrable g volume 0 1 := Complex.betaIntegral_convergent
    (by norm_num [z, Complex.div_re]) (by norm_num [w, Complex.div_re])
  have hp (x : ℝ) : ((1 / 2 : ℝ) * sech x ^ 2) • g (intrinsic x) =
      (1 / 2 : ℂ) * ((sech x : ℂ) ^ 2 * angularPhase ξ x) := beta_sechSquared_pullback ξ x
  have hint : Integrable (fun x : ℝ => ((1 / 2 : ℝ) * sech x ^ 2) • g (intrinsic x)) :=
    ((integrable_sechSquared_angularPhase ξ).const_mul (1 / 2 : ℂ)).congr
      (Eventually.of_forall (fun x => (hp x).symm))
  have h := integral_intrinsic_substitution g hi (betaIntegrand_continuousOn z w) hint
  rw [integral_congr_ae (Eventually.of_forall hp), integral_const_mul] at h
  change (∫ x : ℝ, (sech x : ℂ) ^ 2 * angularPhase ξ x) = 2 * ∫ t in (0 : ℝ)..1, g t
  linear_combination (2 : ℂ) * h

/-- The exact genuine angular-frequency sech Fourier transform.
Article: main_krylov, apC:lem:poisson, hat(sech)(xi)=pi*sech(pi*xi/2).
Proof: the true beta representation, Gamma reflection, and sin(pi/2-i*y)=cosh(y). -/
theorem integral_sech_angularPhase (ξ : ℝ) :
    (∫ x : ℝ, (sech x : ℂ) * angularPhase ξ x) =
      (π : ℂ) / (Real.cosh (π * ξ / 2) : ℂ) := by
  rw [integral_sech_angularPhase_eq_beta, Complex.betaIntegral_eq_Gamma_mul_div _ _
    (by norm_num [Complex.div_re]) (by norm_num [Complex.div_re])]
  have hsum : ((1 : ℂ) - (ξ : ℂ) * Complex.I) / 2 +
      ((1 : ℂ) + (ξ : ℂ) * Complex.I) / 2 = 1 := by ring
  have hw : ((1 : ℂ) + (ξ : ℂ) * Complex.I) / 2 =
      1 - (((1 : ℂ) - (ξ : ℂ) * Complex.I) / 2) := by ring
  rw [hsum, Complex.Gamma_one, div_one, hw, Complex.Gamma_mul_Gamma_one_sub]
  congr 1
  rw [show (π : ℂ) * (((1 : ℂ) - (ξ : ℂ) * Complex.I) / 2) =
      (π : ℂ) / 2 - ((π * ξ / 2 : ℝ) : ℂ) * Complex.I by push_cast; ring,
    Complex.sin_sub, Complex.sin_pi_div_two, Complex.cos_pi_div_two,
    one_mul, zero_mul, sub_zero, Complex.cos_mul_I, ← Complex.ofReal_cosh]

/-- The actual squared-sech transform has value two at zero angular frequency.
Article: main_krylov, apC:lem:poisson, the removable zero-frequency value. -/
theorem integral_sechSquared_angularPhase_zero :
    (∫ x : ℝ, (sech x : ℂ) ^ 2 * angularPhase 0 x) = 2 := by
  rw [integral_sechSquared_angularPhase_eq_beta]
  norm_num [Complex.betaIntegral_eval_one_right (by norm_num : (0 : ℝ) < (1 : ℂ).re)]

/-- The exact genuine nonzero angular-frequency squared-sech Fourier transform.
Article: main_krylov, apC:lem:poisson, hat(sech^2)(xi)=pi*xi/sinh(pi*xi/2).
Proof: Gamma recurrence reduces its true beta integral to Euler reflection at i*xi/2. -/
theorem integral_sechSquared_angularPhase {ξ : ℝ} (hξ : ξ ≠ 0) :
    (∫ x : ℝ, (sech x : ℂ) ^ 2 * angularPhase ξ x) =
      ((π * ξ : ℝ) : ℂ) / (Real.sinh (π * ξ / 2) : ℂ) := by
  rw [integral_sechSquared_angularPhase_eq_beta, Complex.betaIntegral_eq_Gamma_mul_div _ _
    (by norm_num [Complex.div_re]) (by norm_num [Complex.div_re])]
  let u : ℂ := (ξ : ℂ) * Complex.I / 2
  have hu : u ≠ 0 := div_ne_zero (mul_ne_zero (Complex.ofReal_ne_zero.mpr hξ) Complex.I_ne_zero) (by norm_num)
  have hz : ((2 : ℂ) - (ξ : ℂ) * Complex.I) / 2 = 1 - u := by dsimp [u]; ring
  have hw : ((2 : ℂ) + (ξ : ℂ) * Complex.I) / 2 = u + 1 := by dsimp [u]; ring
  have hsum : ((2 : ℂ) - (ξ : ℂ) * Complex.I) / 2 +
      ((2 : ℂ) + (ξ : ℂ) * Complex.I) / 2 = 2 := by ring
  have hG2 : Complex.Gamma 2 = 1 := by
    norm_num [show (2 : ℂ) = 1 + 1 by norm_num, Complex.Gamma_add_one 1 (by norm_num), Complex.Gamma_one]
  rw [hsum, hG2, div_one, hz, hw, Complex.Gamma_add_one u hu]
  have hr : Complex.Gamma (1 - u) * (u * Complex.Gamma u) =
      u * (Complex.Gamma u * Complex.Gamma (1 - u)) := by ring
  rw [hr, Complex.Gamma_mul_Gamma_one_sub]
  have hs : Complex.sin ((π : ℂ) * u) = (Real.sinh (π * ξ / 2) : ℂ) * Complex.I := by
    rw [show (π : ℂ) * u = ((π * ξ / 2 : ℝ) : ℂ) * Complex.I by dsimp [u]; push_cast; ring,
      Complex.sin_mul_I, ← Complex.ofReal_sinh]
  rw [hs]
  dsimp [u]
  push_cast
  field_simp

end
end krylov.Design

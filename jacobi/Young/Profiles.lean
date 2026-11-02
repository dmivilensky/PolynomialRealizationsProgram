import jacobi.Young.Hyperbolic
import jacobi.Variational.Problem

/-!
Article: jacobi, Equation (3.3) (exact U density and full spectrum).
The literal density (1/4)sech^4 has the exact mass, root mass and energy in the
article. These calculations use the proved whole-line hyperbolic integrals;
no numerical certificate or assumed profile integral occurs.
Use: an actual candidate for the root-mass and mass-relaxed variational problems.
-/
namespace jacobi.Young
noncomputable section
open MeasureTheory Real jacobi.Variational
open scoped ENNReal

/-- The distinguished equality density appearing at the common point U.
Use: an actual candidate for the root-mass and mass-relaxed variational problems.
Article: jacobi, Equation (3.3) (exact U density and full spectrum).
-/
def distinguished (x : ℝ) : ℝ := (1/4 : ℝ)*sech x^4

/-- The square root of m_U is exactly sech^2/2.
Use: computes its root mass and the coordinate derivative in its spectral realization.
Article: jacobi, Equation (3.3) (exact U density and full spectrum).
Proof: the proposed root is nonnegative and its square is the actual density. -/
theorem distinguished_sqrt (x : ℝ) : Real.sqrt (distinguished x) = (1/2 : ℝ)*sech x^2 := by
  have hd : 0 ≤ distinguished x := by unfold distinguished; positivity
  apply (Real.sqrt_eq_iff_eq_sq hd (by positivity)).mpr
  dsimp [distinguished]
  ring

/-- The real-power energy integrand of m_U is exactly sech^6/8.
Use: computes the actual energy 2/15 rather than an auxiliary polynomial integral.
Article: jacobi, Equation (3.3) (exact U density and full spectrum).
Proof: write the 3/2 power as the density times its positive square root. -/
theorem distinguished_power (x : ℝ) : distinguished x^(3/2 : ℝ) = (1/8 : ℝ)*sech x^6 := by
  have hp : 0 < distinguished x := mul_pos (by norm_num) (pow_pos (sech_pos x) 4)
  rw [show (3/2 : ℝ) = 1+1/2 by norm_num, Real.rpow_add hp,
    Real.rpow_one, ← Real.sqrt_eq_rpow, distinguished_sqrt]
  dsimp [distinguished]
  ring

/-- The literal distinguished profile belongs to the common finite-energy domain.
Use: the equality candidate has no outstanding admissibility assumptions.
Article: jacobi, Equation (3.3) (exact U density and full spectrum).
Proof: continuity and positivity are explicit; integrability follows from the
proved fourth and sixth hyperbolic-power integrals. -/
def distinguishedDensity : Density where
  value := distinguished
  measurable := by
    exact (continuous_const.mul
      ((Real.continuous_cosh.inv₀ (fun x => (Real.cosh_pos x).ne')).pow 4)).measurable
  nonneg x := by unfold distinguished; positivity
  integrable := by
    change Integrable (fun x => (1/4 : ℝ)*sech x^4)
    exact (sech_even_integrable 1).const_mul (1/4 : ℝ)
  energy_integrable := by
    simp_rw [distinguished_power]
    exact (sech_even_integrable 2).const_mul (1/8 : ℝ)

/-- The distinguished profile has the exact mass 1/3.
Use: identifies the mass at the common Young point.
Article: jacobi, Equation (3.3) (exact U density and full spectrum).
Proof: multiply the proved integral sech^4=4/3 by 1/4. -/
theorem distinguished_mass : distinguishedDensity.mass = 1/3 := by
  change (∫ x, (1/4 : ℝ)*sech x^4) = _
  rw [integral_const_mul, integral_sech_four]
  norm_num

/-- The distinguished profile has root mass exactly one.
Use: proves the extra root-mass constraint at the equality point.
Article: jacobi, Equation (3.3) (exact U density and full spectrum).
Proof: use the actual square root sech^2/2 and its exact integral; identify the
extended root mass through the nonnegative Bochner-to-Lebesgue integral theorem. -/
theorem distinguished_rootMass : distinguishedDensity.rootMass = 1 := by
  -- The square root is integrable, so its extended integral has no infinite or junk case.
  have hi : Integrable (fun x => Real.sqrt (distinguished x)) := by
    simp_rw [distinguished_sqrt]
    exact sech_sq_integrable.const_mul (1/2 : ℝ)
  have he : (∫ x, Real.sqrt (distinguished x)) = 1 := by
    simp_rw [distinguished_sqrt]
    rw [integral_const_mul, integral_sech_sq]
    norm_num
  change (∫⁻ x, ENNReal.ofReal (Real.sqrt (distinguished x))) = 1
  rw [← ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall fun x => Real.sqrt_nonneg _), he]
  norm_num

/-- The actual energy of m_U is exactly 2/15.
Use: the attaining value in the sharp second-moment calibration.
Article: jacobi, Equation (3.3) (exact U density and full spectrum).
Proof: integrate the actual 3/2 power sech^6/8 and use its proved integral 16/15. -/
theorem distinguished_energy : distinguishedDensity.energy = 2/15 := by
  change (∫ x, distinguished x^(3/2 : ℝ)) = _
  simp_rw [distinguished_power]
  rw [integral_const_mul, integral_sech_six]
  norm_num

/-- The distinguished profile has finite extended cost exactly 2/15.
Use: inserts the explicit candidate into the ENNReal variational infima.
Article: jacobi, Equation (3.3) (exact U density and full spectrum).
Proof: substitute the actual energy calculation in the cost definition. -/
theorem distinguished_cost : distinguishedDensity.cost = (2/15 : ℝ≥0∞) := by
  rw [Density.cost, distinguished_energy]
  norm_num [ENNReal.ofReal_div_of_pos]

end
end jacobi.Young

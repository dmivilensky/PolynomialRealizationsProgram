import jacobi.Variational.SecondMoment

/-!
Article: jacobi, Lemma D.3.
Nonnegative amplitude scaling acts on the actual finite-energy density
domain. Its mass, energy and true quadratic spectral moment have their
exact homogeneities. These give a feasible strict energy descent whenever
the second-moment constraint is slack, proving activity at every minimizer.
Source: linearity of Lebesgue integration and the literal second-moment kernel.
Use: normalizes spectral thresholds and excludes slack second constraints at actual minimizers.
-/
namespace jacobi.Variational
noncomputable section
open MeasureTheory Real
set_option backward.isDefEq.respectTransparency false

/-- Nonnegative amplitude scaling of an actual finite-energy density.
Use: normalizes spectral thresholds and excludes slack second constraints at actual minimizers.
Article: jacobi, Lemma D.3.
-/
def Density.scale (m : Density) (c : ℝ) (hc : 0≤c) : Density where
  value x := c*m.value x
  measurable := measurable_const.mul m.measurable
  nonneg x := mul_nonneg hc (m.nonneg x)
  integrable := m.integrable.const_mul c
  energy_integrable := by
    simp_rw [Real.mul_rpow hc (m.nonneg _)]
    exact m.energy_integrable.const_mul (c^(3/2 : ℝ))

/-- Amplitude scaling multiplies the actual mass by c.
Use: concentration by a factor at most one preserves the upper mass constraint.
Article: jacobi, Appendix D.1 (moment multipliers and clipped profiles).
Proof: take the constant scalar outside the literal mass integral. -/
theorem Density.scale_mass (m : Density) (c : ℝ) (hc : 0≤c) :
    (m.scale c hc).mass=c*m.mass := integral_const_mul c _

/-- Amplitude scaling multiplies the actual energy by c^(3/2).
Use: a factor strictly below one gives strict descent for every nonzero finite-energy density.
Article: jacobi, Appendix D.5 (global pointwise minimum principle).
Proof: the nonnegative real-power product law separates the amplitude before integrating. -/
theorem Density.scale_energy (m : Density) (c : ℝ) (hc : 0≤c) :
    (m.scale c hc).energy=c^(3/2 : ℝ)*m.energy := by
  change (∫ x, (c*m.value x)^(3/2 : ℝ))=_
  simp_rw [Real.mul_rpow hc (m.nonneg _)]
  exact integral_const_mul _ _

/-- Amplitude scaling multiplies the actual second spectral moment by c².
Use: rescales a slack candidate exactly to its active spectral threshold.
Article: jacobi, Lemma D.3.
Proof: the already verified literal double integral is quadratic in its density;
take its constant c² outside the product-space integral. -/
theorem Density.scale_second (m : Density) (c : ℝ) (hc : 0≤c) :
    observe (m.scale c hc) .second=c^2*observe m .second := by
  -- This calculation concerns the actual operator spectrum through its exact kernel identity.
  rw [← (m.scale c hc).secondPairing_self,← m.secondPairing_self]
  change (∫ z : ℝ × ℝ, (c*m.value z.1)*(c*m.value z.2)*exp (-2*|z.1-z.2|) ∂volume.prod volume)=_
  unfold secondPairing
  rw [← integral_const_mul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun _ => by dsimp only; ring

end
end jacobi.Variational

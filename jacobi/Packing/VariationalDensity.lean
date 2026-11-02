import jacobi.Packing.Spectrum
import jacobi.Variational.Problem

/-!
Article: jacobi, Proposition 6.1.
The actual packed function belongs to the finite-energy variational domain.
Its mass, extended root mass, energy and spectrum are identified with the
already proved packing formulas. This connects the geometric construction
to the exact admissible sets used by the continuum transfer theorem.
Source: finite interval packing and compact-support Lp integrability in mathlib.
Use: supplies energy and square-root integrability before using their exact packing identities.
-/
namespace jacobi.Packing
noncomputable section
open chebyshev1 chebyshev2 MeasureTheory Real Set jacobi.Variational
open scoped BigOperators ENNReal
set_option backward.isDefEq.respectTransparency false
variable {N : ℕ}

/-- Every positive power of the actual packed density is integrable.
Use: supplies energy and square-root integrability before using their exact packing identities.
Article: jacobi, Proposition 6.1.
Proof: the packed density is measurable, compactly supported and bounded by
the finite sum of squared cell heights. Positive powers preserve these properties. -/
theorem density_rpow_integrable (J : Jacobi N) (hc : opNorm J.matrix < 1) (hN : 0 < N)
    {p : ℝ} (hp : 0 < p) : Integrable (fun x => density J hc hN x^p) := by
  -- Compact support gives finite-measure support, so a uniform power bound gives L1 membership.
  let B := (packing J hc).blocks hN
  have hcont : Continuous (fun v : ℝ => v^p) := Real.continuous_rpow_const hp.le
  have hs : HasCompactSupport (fun x => density J hc hN x^p) :=
    (density_properties J hc hN).2.2.2.comp_left (g := fun v : ℝ => v^p) (Real.zero_rpow hp.ne')
  apply memLp_one_iff_integrable.mp
  apply hs.memLp_of_bound (hcont.measurable.comp (density_properties J hc hN).1).aestronglyMeasurable
    ((∑ i : Fin N, B.height i^2)^p)
  exact Filter.Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs,abs_of_nonneg (rpow_nonneg ((density_properties J hc hN).2.1 x) _)]
    exact rpow_le_rpow ((density_properties J hc hN).2.1 x) (B.closedDensity_bound x) hp.le

/-- The actual packed density as a member of the common finite-energy variational domain.
Use: an arbitrary contractive finite Jacobi matrix gives an actual continuum competitor for Transfer.
Article: jacobi, Proposition 6.1.
-/
def variationalDensity (J : Jacobi N) (hc : opNorm J.matrix < 1) (hN : 0 < N) : Density where
  value := density J hc hN
  measurable := (density_properties J hc hN).1
  nonneg := (density_properties J hc hN).2.1
  integrable := (density_properties J hc hN).2.2.1
  energy_integrable := density_rpow_integrable J hc hN (by norm_num : (0 : ℝ) < 3/2)

/-- The variational density has the exact packed mass, normalized root mass and scaled finite energy.
Use: meets the actual stronger continuum constraints for every finite fibre member.
Article: jacobi, Proposition 6.1.
Proof: use the proved real packing integrals; square-root integrability
identifies its extended integral with ofReal(1). -/
theorem variationalDensity_integrals (J : Jacobi N) (hc : opNorm J.matrix < 1) (hN : 0 < N) :
    (variationalDensity J hc hN).mass=mass J ∧
    (variationalDensity J hc hN).rootMass=1 ∧
    (variationalDensity J hc hN).energy=J.energy/(N : ℝ)^3 := by
  -- Integrability is proved before converting the root integral, so its real value cannot be a junk value.
  obtain ⟨hM,hr,hE⟩ := volume_identities J hc hN
  refine ⟨hM,?_,hE⟩
  have hi : Integrable (fun x => sqrt (density J hc hN x)) := by
    simp_rw [Real.sqrt_eq_rpow]
    exact density_rpow_integrable J hc hN (by norm_num : (0 : ℝ) < 1/2)
  change (∫⁻ x, ENNReal.ofReal (sqrt (density J hc hN x)))=1
  rw [← ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall (fun _ => sqrt_nonneg _)),
    hr,ENNReal.ofReal_one]

/-- The variational density uses the very same actual spectrum as the proved geometric packing bound.
Use: applies spectral error estimates to the actual continuum constraints without a proxy spectrum.
Article: jacobi, Proposition 6.1.
Proof: both sides are the existing actual kernel eigenvalues of the identical density. -/
theorem variationalDensity_spectrum (J : Jacobi N) (hc : opNorm J.matrix < 1) (hN : 0 < N) :
    (variationalDensity J hc hN).spectrum=packedEigenvalue J hc hN := rfl

end
end jacobi.Packing

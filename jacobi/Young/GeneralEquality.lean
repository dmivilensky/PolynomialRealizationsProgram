import jacobi.Young.GeneralRigidity
import jacobi.Young.Equality
import jacobi.Young.GeneralDensity

/-!
Article: jacobi, Section 3.2 (sharp Young inequality).
The nonnegative product-space second moment is used literally, including
sources initially allowed to have infinite mass. Equality itself proves
finite mass, so the existing complete ODE classification applies. Conversely
every positive translated sech-fourth profile attains equality. Thus the
domain of the equality statement is the entire finite-energy source domain.
Use: transfers the full-domain equality theorem back to the original finite-mass operator formulation.
-/
namespace jacobi.Young
noncomputable section
open Real MeasureTheory Filter jacobi.Variational
open scoped ENNReal
set_option backward.isDefEq.respectTransparency false

/-- The actual spectral second moment equals its extended nonnegative double integral.
Use: transfers the full-domain equality theorem back to the original finite-mass operator formulation.
Article: jacobi, Section 3.2 (sharp Young inequality).
Proof: identify the real double integral with the actual spectral moment and
use nonnegativity and absolute integrability to pass to its ENNReal integral. -/
theorem density_second_lintegral (m : Density) :
    (∫⁻ z : ℝ × ℝ, ENNReal.ofReal (m.value z.1*m.value z.2*exp (-2*|z.1-z.2|)) ∂volume.prod volume)=
      ENNReal.ofReal (observe m .second) := by
  -- The existing actual second-moment identity supplies spectral multiplicities, not a model sequence.
  have hi := second_integrand_integrable m.integrable m.integrable m.measurable m.measurable
  have h := ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall fun z =>
    mul_nonneg (mul_nonneg (m.nonneg z.1) (m.nonneg z.2)) (exp_pos _).le)
  change ENNReal.ofReal (secondPairing m.value m.value)=_ at h
  rw [m.secondPairing_self] at h
  exact h.symm

/-- Positive energy implies positive mass whenever the actual source mass is finite.
Use: applies the established nonzero finite-mass equality classification after equality proves integrability.
Article: jacobi, Section 3.2 (sharp Young inequality).
Proof: a nonnegative integrable density of zero mass vanishes almost everywhere, forcing zero energy. -/
theorem mass_pos_of_energy_pos (m : Density) (hE : 0<m.energy) : 0<m.mass := by
  -- Nonvanishing is measured almost everywhere, so isolated null-set values cause no exception.
  apply lt_of_le_of_ne (integral_nonneg m.nonneg)
  intro hz
  have hae := (integral_eq_zero_iff_of_nonneg m.nonneg m.integrable).mp hz.symm
  have he : m.energy=0 := by
    change (∫ x, m.value x^(3/2 : ℝ))=0
    have h : (fun x => m.value x^(3/2 : ℝ))=ᵐ[volume] (0 : ℝ → ℝ) := by
      filter_upwards [hae] with x hx
      simp only [hx,Pi.zero_apply,Real.zero_rpow (by norm_num : (3/2 : ℝ)≠0)]
    simpa only [Pi.zero_apply,integral_zero] using integral_congr_ae h
  exact hE.ne' he

/-- Exact finite-mass restriction of a full-domain source after its integrability is established.
Use: invokes the existing operator and profile theorems without copying their proofs.
Article: jacobi, Section 3.2 (sharp Young inequality).
-/
def EnergySource.toDensity (m : EnergySource) (hi : Integrable m.value) : Density where
  value := m.value
  measurable := m.measurable
  nonneg := m.nonneg
  integrable := hi
  energy_integrable := m.energy_integrable

/-- The full-domain Green moment is the actual ordered spectral moment when the mass is finite.
Use: the unrestricted equality proof transfers directly to the verified finite-mass classification.
Article: jacobi, Section 3.2 (sharp Young inequality).
Proof: both moments equal the same literal nonnegative double integral;
the finite nonnegative ofReal embedding is injective. -/
theorem EnergySource.second_eq_spectral (m : EnergySource) (hi : Integrable m.value) :
    m.second=observe (m.toDensity hi) .second := by
  -- All normalizations are retained through the single product-space integral.
  have h : ENNReal.ofReal m.second=ENNReal.ofReal (observe (m.toDensity hi) .second) :=
    m.second_lintegral.symm.trans (density_second_lintegral (m.toDensity hi))
  have h' := congrArg ENNReal.toReal h
  have hm0 : 0≤m.second := integral_nonneg fun x => mul_nonneg (m.nonneg x) (m.green_nonneg x)
  have hq0 : 0≤observe (m.toDensity hi) .second := tsum_nonneg (fun _ => sq_nonneg _)
  rwa [ENNReal.toReal_ofReal hm0,ENNReal.toReal_ofReal hq0] at h'

/-- Full printed equality classification for every nonzero finite-energy source, including initially infinite mass.
Use: completes the unrestricted equality assertion of Sharp Young and removes all finite-mass qualifications.
Article: jacobi, Section 3.2 (sharp Young inequality).
Proof: equality of the literal extended double integral gives the polynomial
sharp equality. The actual Riesz potential and cubic rigidity force finite
mass, so the existing complete ODE classification applies. Conversely the
classified profile is integrable and the existing actual attainer proves equality. -/
theorem sharp_young_general_eq_iff (m : EnergySource) (hE : 0<m.energy) :
    (∫⁻ z : ℝ × ℝ, ENNReal.ofReal (m.value z.1*m.value z.2*exp (-2*|z.1-z.2|)) ∂volume.prod volume)=
        ENNReal.ofReal ((5/18 : ℝ)^(1/3 : ℝ)*m.energy^(4/3 : ℝ)) ↔
      ∃ b x₀ : ℝ, 0<b ∧ m.value=ᵐ[volume] (fun x => b*sech (x-x₀)^4) := by
  -- Full-domain equality proves the missing L1 property before any finite-mass operator is used.
  constructor
  · intro he
    rw [m.second_lintegral] at he
    have hr := congrArg ENNReal.toReal he
    rw [ENNReal.toReal_ofReal (m.second_pos hE).le,ENNReal.toReal_ofReal (by positivity)] at hr
    have hp : 18*m.second^3=5*m.energy^4 := by
      have hc : ((5/18 : ℝ)^(1/3 : ℝ))^3=5/18 := by
        simpa only [Nat.cast_one,pow_one] using third_power_cube (by norm_num : (0:ℝ)≤5/18) 1
      have hpow : (m.energy^(4/3 : ℝ))^3=m.energy^4 := by
        simpa only [Nat.cast_ofNat] using third_power_cube hE.le 4
      have h := congrArg (fun r : ℝ => r^3) hr
      rw [mul_pow,hc,hpow] at h
      linarith
    have hi := m.integrable_of_young_equality hE hp
    let q := m.toDensity hi
    have hqE : 0<q.energy := hE
    have hqP : 18*(observe q .second)^3=5*q.energy^4 := by
      rw [← m.second_eq_spectral hi]
      exact hp
    exact young_equality_necessary q (mass_pos_of_energy_pos q hqE) hqP
  · rintro ⟨b,x₀,hb,hae⟩
    have hi : Integrable m.value := ((equalityFamily b hb.le).translate x₀).integrable.congr hae.symm
    let q := m.toDensity hi
    have hqE : 0<q.energy := hE
    have hqY := (sharp_young_eq_iff q (mass_pos_of_energy_pos q hqE)).mpr ⟨b,x₀,hb,hae⟩
    change (∫⁻ z : ℝ × ℝ, ENNReal.ofReal (q.value z.1*q.value z.2*exp (-2*|z.1-z.2|)) ∂volume.prod volume)=_
    rw [density_second_lintegral q,hqY]
    rfl

/-- Nonvanishing almost everywhere is precisely the relevant positive-energy condition.
Use: the complete theorem uses the article's nonzero-density convention without an extra energy premise.
Article: jacobi, Section 3.2 (sharp Young inequality).
Proof: a nonnegative integrable power with zero integral vanishes almost
everywhere, and a positive real power vanishes only at a zero base. -/
theorem EnergySource.energy_pos_of_not_ae_zero (m : EnergySource)
    (h0 : ¬m.value=ᵐ[volume] (0 : ℝ → ℝ)) : 0<m.energy := by
  -- Isolated nonzero values on null sets are correctly identified with the zero density.
  apply lt_of_le_of_ne (integral_nonneg (fun x => Real.rpow_nonneg (m.nonneg x) _))
  intro hz
  have he : (∫ x, m.value x^(3/2 : ℝ))=0 := hz.symm
  have hae := (integral_eq_zero_iff_of_nonneg (fun x => Real.rpow_nonneg (m.nonneg x) _)
    m.energy_integrable).mp he
  apply h0
  filter_upwards [hae] with x hx
  exact (Real.rpow_eq_zero (m.nonneg x) (by norm_num : (3/2 : ℝ)≠0)).mp hx

/-- The complete sharp Young theorem in exactly the full measurable finite-energy domain of the article.
Use: the source-facing theorem packages the global inequality and all nonzero equality cases together.
Article: jacobi, Section 3.2 (sharp Young inequality).
Proof: the proved nonnegative product-integral bound supplies the inequality.
For a nonzero source, positivity of energy and the Riesz-based rigidity
argument supply the full if-and-only-if equality classification. -/
theorem sharp_young_complete {m : ℝ → ℝ} (hm : Measurable m) (hn : ∀ x, 0≤m x)
    (hE : Integrable (fun x => m x^(3/2 : ℝ))) :
    (∫⁻ z : ℝ × ℝ, ENNReal.ofReal (m z.1*m z.2*exp (-2*|z.1-z.2|)) ∂volume.prod volume)≤
        ENNReal.ofReal ((5/18 : ℝ)^(1/3 : ℝ)*(∫ x, m x^(3/2 : ℝ))^(4/3 : ℝ)) ∧
    (¬m=ᵐ[volume] (0 : ℝ → ℝ) →
      ((∫⁻ z : ℝ × ℝ, ENNReal.ofReal (m z.1*m z.2*exp (-2*|z.1-z.2|)) ∂volume.prod volume)=
          ENNReal.ofReal ((5/18 : ℝ)^(1/3 : ℝ)*(∫ x, m x^(3/2 : ℝ))^(4/3 : ℝ)) ↔
        ∃ b x₀ : ℝ, 0<b ∧ m=ᵐ[volume] (fun x => b*sech (x-x₀)^4))) := by
  let s : EnergySource := ⟨m,hm,hn,hE⟩
  refine ⟨sharp_young_general hm hn hE,fun h0 => ?_⟩
  exact sharp_young_general_eq_iff s (s.energy_pos_of_not_ae_zero h0)

end
end jacobi.Young

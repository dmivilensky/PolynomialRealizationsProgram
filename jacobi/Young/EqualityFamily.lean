import jacobi.Young.Profiles
import jacobi.Young.Convolution

/-!
Article: jacobi, Section 3.2 (sharp Young inequality).
The explicit sech^4 family has its actual spectral second moment computed
from the verified kernel integral. All admissibility calculations below are
exact and do not assume sharp Young or existence of a minimizer.
Use: constructs the full Young candidate family in the actual variational domain.
-/
namespace jacobi.Young
noncomputable section
open MeasureTheory Real jacobi.Variational chebyshev2.Continuum
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- The real-power energy integrand for every nonnegative equality-family amplitude.
Use: constructs the full Young candidate family in the actual variational domain.
Article: jacobi, Section 3.2 (sharp Young inequality).
Proof: multiply real powers on nonnegative bases and combine the fourth power with 3/2. -/
theorem equalityFamily_power {b : ℝ} (hb : 0 ≤ b) (x : ℝ) :
    (b*sech x^4)^(3/2 : ℝ) = b^(3/2 : ℝ)*sech x^6 := by
  rw [Real.mul_rpow hb (pow_nonneg (sech_pos x).le _),
    ← Real.rpow_natCast_mul (sech_pos x).le]
  norm_num

/-- Every nonnegative amplitude gives an actual finite-energy density.
Use: proves feasibility and attainment once the sharp lower inequality is established.
Article: jacobi, Theorem D.5.
-/
def equalityFamily (b : ℝ) (hb : 0 ≤ b) : Density where
  value x := b*sech x^4
  measurable := (continuous_const.mul
    ((Real.continuous_cosh.inv₀ (fun x => (Real.cosh_pos x).ne')).pow 4)).measurable
  nonneg x := mul_nonneg hb (pow_nonneg (sech_pos x).le _)
  integrable := by
    exact (show Integrable (fun x : ℝ => sech x^4) from by simpa using sech_even_integrable 1).const_mul b
  energy_integrable := by
    simp_rw [equalityFamily_power hb]
    exact (show Integrable (fun x : ℝ => sech x^6) from by simpa using sech_even_integrable 2).const_mul _

/-- Actual mass of every Young equality profile.
Use: checks the mass constraint in the Young and elliptic regimes.
Article: jacobi, Section 3.2 (sharp Young inequality).
Proof: integrate the explicit fourth power of sech. -/
theorem equalityFamily_mass {b : ℝ} (hb : 0 ≤ b) : (equalityFamily b hb).mass = 4*b/3 := by
  change (∫ x, b*sech x^4) = _
  rw [integral_const_mul, integral_sech_four]
  ring

/-- Actual energy of every Young equality profile.
Use: evaluates the candidate at the exact second-moment threshold.
Article: jacobi, Equation (3.3) (exact U density and full spectrum).
Proof: integrate the proved real-power energy integrand. -/
theorem equalityFamily_energy {b : ℝ} (hb : 0 ≤ b) :
    (equalityFamily b hb).energy = (16/15 : ℝ)*b^(3/2 : ℝ) := by
  change (∫ x, (b*sech x^4)^(3/2 : ℝ)) = _
  simp_rw [equalityFamily_power hb]
  rw [integral_const_mul, integral_sech_six]
  ring

/-- The actual second kernel moment of the full Young equality family.
Use: checks the exact spectral constraint, rather than a modeled moment.
Article: jacobi, Section 3.2 (sharp Young inequality).
Proof: identify the actual spectral moment with its double integral and insert
the proved convolution exp(-2|.|)*sech^4=(2/3)sech^2. -/
theorem equalityFamily_second {b : ℝ} (hb : 0 ≤ b) :
    observe (equalityFamily b hb) .second = (32/45 : ℝ)*b^2 := by
  -- The spectrum is the existing actual kernel spectrum of this very density.
  rw [observe, L1Source.spectrum, kernelEigenvalue_square_integral]
  change (∫ x, ∫ y, (b*sech x^4)*(b*sech y^4)*Real.exp (-2*|x-y|)) = _
  have he (x : ℝ) : (∫ y, (b*sech x^4)*(b*sech y^4)*Real.exp (-2*|x-y|)) =
      (2/3 : ℝ)*b^2*sech x^6 := by
    calc
      _ = (b^2*sech x^4)*(∫ y, Real.exp (-2*|x-y|)*sech y^4) := by
        rw [← integral_const_mul]
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun y => by dsimp only; ring
      _ = _ := by rw [sech_four_convolution]; ring
  simp_rw [he]
  rw [integral_const_mul, integral_sech_six]
  ring

/-- All Young equality profiles have second moment divided by squared mass equal to 2/5.
Use: separates the two calibration regimes and excludes equality in the elliptic regime.
Article: jacobi, Section 3.2 (sharp Young inequality).
Proof: substitute the two exact profile calculations and simplify. -/
theorem equalityFamily_ratio {b : ℝ} (hb : 0 ≤ b) :
    observe (equalityFamily b hb) .second = (2/5 : ℝ)*(equalityFamily b hb).mass^2 := by
  rw [equalityFamily_second, equalityFamily_mass]
  ring

/-- No Young equality profile can satisfy a genuinely elliptic pair of mass/moment constraints.
Use: the contradiction required for strict improvement over the Young bound.
Article: jacobi, Equation (3.3) (exact U density and full spectrum).
Proof: mass at most M forces the equality profile's second moment at most (2/5)M^2. -/
theorem equalityFamily_infeasible {b M T : ℝ} (hb : 0 ≤ b)
    (hregime : 2*M^2 < 5*T) :
    ¬ ((equalityFamily b hb).mass ≤ M ∧ T ≤ observe (equalityFamily b hb) .second) := by
  rintro ⟨hm, ht⟩
  rw [equalityFamily_ratio] at ht
  have hm0 : 0 ≤ (equalityFamily b hb).mass := integral_nonneg (equalityFamily b hb).nonneg
  have hs := mul_self_le_mul_self hm0 hm
  nlinarith

/-- The actual distinguished density has second spectral moment exactly 2/45.
Use: proves its second-moment admissibility at the common point U.
Article: jacobi, Theorem D.5.
Proof: specialize the full family calculation to amplitude 1/4. -/
theorem distinguished_second : observe distinguishedDensity .second = 2/45 := by
  have h := equalityFamily_second (b := (1/4 : ℝ)) (by norm_num)
  change observe distinguishedDensity .second = _ at h
  norm_num at h
  exact h

/-- The explicit Young candidate satisfies the actual mass and spectral constraints
throughout the Young regime, including the zero-threshold endpoint.
Use: proves nonemptiness and the attaining candidate's upper bound independently
of the still separate global sharp inequality.
Article: jacobi, Theorem D.5.
Proof: use b²=45T_2/32 in the exact moment and mass formulas; the regime
condition is precisely the resulting squared mass inequality. -/
theorem young_candidate_feasible {M T : ℝ} (hM : 0 ≤ M) (hT : 0 ≤ T)
    (hregime : 5*T ≤ 2*M^2) :
    ∃ m : Density, m.mass ≤ M ∧ observe m .second=T ∧
      m.energy=(16/15 : ℝ)*(sqrt (45*T/32))^(3/2 : ℝ) := by
  -- The candidate is a genuine density, with the observation evaluated on its actual spectrum.
  let b := sqrt (45*T/32)
  have hb : 0 ≤ b := sqrt_nonneg _
  have hb2 : b^2=45*T/32 := sq_sqrt (by positivity)
  refine ⟨equalityFamily b hb,?_,?_,equalityFamily_energy hb⟩
  · rw [equalityFamily_mass]
    nlinarith
  · rw [equalityFamily_second,hb2]
    ring

/-- The root-free second-moment infimum is bounded by the explicit Young candidate.
Use: the feasible half of the sharp calibration, before proving the matching lower bound.
Article: jacobi, Section 3.2 (sharp Young inequality).
Proof: place the actual candidate in the admissible set defining the infimum. -/
theorem relaxed_second_upper {M T : ℝ} (hM : 0 ≤ M) (hT : 0 ≤ T)
    (hregime : 5*T ≤ 2*M^2) :
    relaxedInfimum {Observation.second} M (fun _ => T) ≤
      ENNReal.ofReal ((16/15 : ℝ)*(sqrt (45*T/32))^(3/2 : ℝ)) := by
  -- Infimum membership uses the proved kernel moment, rather than an assumed constraint certificate.
  obtain ⟨m,hm,ht,he⟩ := young_candidate_feasible hM hT hregime
  apply sInf_le
  refine ⟨m,⟨hm,?_⟩,?_⟩
  · intro i hi
    have hi' : i = Observation.second := Set.mem_singleton_iff.mp hi
    subst i
    exact ht.ge
  · rw [Density.cost,he]

end
end jacobi.Young

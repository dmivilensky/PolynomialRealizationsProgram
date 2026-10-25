import chebyshev2.Calibration.BaseContinuity
import chebyshev2.Packing.OperatorObservations
import chebyshev2.Finite.Optimal

/-!
Article: chebyshev2, Proposition 6.
Proposition 6: continuum lower bound, including infinite energy, and transfer to arbitrary elements
of the full finite fiber.
Use: `chebyshev2.Calibration.Data.packed_energy_ge_base` feeds
`chebyshev2.Calibration.Data.greenConstant_ge_referenceBase` (The finite-fiber conclusion e ≥
B*, with the same constant as in (21)).
Proof chain: `chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement` —
chebyshev2, Theorem 1.2, factor 1.000013; Unconditional uniform gain comparison with the retained
numerical factor.
-/
namespace chebyshev2.Calibration
noncomputable section
open Set MeasureTheory Filter Real chebyshev2.GroundState chebyshev2.Continuum
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/--
Exact identity `(sqrt x)^3=x^(3/2:ℝ)`.

Use: `chebyshev2.Calibration.Data.one_determinant_lower_bound` rewrites with this identity
to prove the bound `ENNReal.ofReal (C.base (groundParameter hm hn)
(logDeterminant (kernelEigenvalue hm hn) (C.sigma*groundParameter hm hn))) ≤ ∫⁻ x,
ENNReal.ofReal (m x^(3/2:ℝ))`.

Article: chebyshev2, Theorem 3.6 via
`chebyshev2.DualCertificate.Data.uniform_finite_lower_bound`.

Proof: Expand/rewrite the named definitions and identities appearing in the tactic block; the
remaining goal is a direct simplification or algebraic consequence.
-/
theorem sqrt_cube_eq_rpow {x : ℝ} (hx : 0 ≤ x) : (sqrt x)^3=x^(3/2:ℝ) := by
  rw [sqrt_eq_rpow,← rpow_natCast,← rpow_mul hx]
  norm_num

/--
Integrability of the displayed function: `Integrable (fun x => (sqrt (m x))^3)`.

Use: `chebyshev2.Calibration.Data.packed_energy_ge_base` uses this integrability result to
establish the stated quantitative bound `C.base (packedCoupling J hN ht)
(chebyshev2.Packing.packedLogDeterminant J hN ht (C.sigma*packedCoupling J hN ht)) ≤
J.normalizedEnergy`.

Article: chebyshev2, Theorem 3.6 via
`chebyshev2.DualCertificate.Data.relaxed_energy_ge_value`.

Proof: Expand/rewrite the named definitions and identities appearing in the tactic block; the
remaining goal is a direct simplification or algebraic consequence.
-/
theorem sqrt_cube_integrable_of_bounded {m : ℝ → ℝ} (hm : Integrable m)
    (hn : ∀ x, 0 ≤ m x) {B : ℝ} (hB : ∀ x, m x ≤ B) : Integrable (fun x => (sqrt (m x))^3) := by
  -- Expand/rewrite the named definitions and identities appearing in the tactic block; the
  -- remaining goal is a direct simplification or algebraic consequence.
  have hi := hm.mul_bdd (continuous_sqrt.comp_aestronglyMeasurable hm.aestronglyMeasurable)
    (Eventually.of_forall (fun x => by
      rw [Real.norm_of_nonneg (sqrt_nonneg _)]
      exact sqrt_le_sqrt (hB x)))
  apply hi.congr
  exact Eventually.of_forall (fun x => by
    change m x*sqrt (m x)=(sqrt (m x))^3
    calc
      m x*sqrt (m x)=(sqrt (m x))^2*sqrt (m x) :=
        congrArg (fun z => z*sqrt (m x)) (sq_sqrt (hn x)).symm
      _=(sqrt (m x))^3 := by ring)

namespace Data
variable (C : Data)

/--
Infinite energies are handled as Lebesgue integrals in ℝ≥0∞, rather than relying on the
totalized real Bochner integral.

The stated quantitative bound `ENNReal.ofReal (C.base (groundParameter hm hn) (logDeterminant
(kernelEigenvalue hm hn) (C.sigma*groundParameter hm hn))) ≤ ∫⁻ x, ENNReal.ofReal (m
x^(3/2:ℝ))`.

Use: `chebyshev2.Calibration.ReferenceData.selfConsistent_minimum` uses this bound to
establish the stated quantitative bound `ENNReal.ofReal (∫ x, (sqrt (R.density x))^3) ≤ ∫⁻ x,
ENNReal.ofReal (m x^(3/2:ℝ))`.

Article: chebyshev2, Proposition 6.

Proof: Separate `Integrable (fun x => (sqrt (m x))^3)` from its negation; prove the goal under
each of these mutually exclusive hypotheses. Identify the summands/integrands on their required
domain before replacing the sum or integral.
-/
theorem one_determinant_lower_bound {m : ℝ → ℝ} (hm : Integrable m)
    (hn : ∀ x, 0 ≤ m x) (hM : (∫ x, m x)=1) :
    ENNReal.ofReal (C.base (groundParameter hm hn)
      (logDeterminant (kernelEigenvalue hm hn) (C.sigma*groundParameter hm hn))) ≤
        ∫⁻ x, ENNReal.ofReal (m x^(3/2:ℝ)) := by
  -- Separate `Integrable (fun x => (sqrt (m x))^3)` from its negation; prove the goal under
  -- each of these mutually exclusive hypotheses.
  have hne : ¬ m =ᵐ[volume] 0 := by
    intro he
    have hz := integral_congr_ae he
    simp only [Pi.zero_apply,integral_zero] at hz
    linarith
  let G := Classical.choice (ground_state hm hn hne)
  by_cases hE : Integrable (fun x => (sqrt (m x))^3)
  · have h := ENNReal.ofReal_le_ofReal (C.energy_ge_base G hM hE)
    rw [ofReal_integral_eq_lintegral_ofReal hE (Eventually.of_forall (fun x => by positivity))] at h
    simp_rw [sqrt_cube_eq_rpow (hn _)] at h
    exact h
  · have htop : (∫⁻ x, ENNReal.ofReal ((sqrt (m x))^3))=⊤ := by
      apply eq_top_iff.mpr
      apply not_lt.mp
      intro hfinite
      apply hE
      refine ⟨(continuous_sqrt.pow 3).comp_aestronglyMeasurable hm.aestronglyMeasurable,?_⟩
      apply (hasFiniteIntegral_iff_norm _).mpr
      simpa only [Real.norm_of_nonneg (pow_nonneg (sqrt_nonneg _) 3)] using hfinite
    simp_rw [sqrt_cube_eq_rpow (hn _)] at htop
    rw [htop]
    exact le_top

variable {N : ℕ} (J : chebyshev2.Jacobi N) (hN : 0 < N) (ht : J.Terminal)

/--
Defines `packedCoupling` of type `ℝ` by `2/chebyshev2.Packing.packedEigenvalue J hN ht 0`.

Use: `chebyshev2.Calibration.Data.packedCoupling_positive` uses this definition to
establish the stated quantitative bound `0 < packedCoupling J hN ht`.

Article: chebyshev2, Theorem E.1 via
`chebyshev2.DualCertificate.Data.packed_value_tendsto`.
-/
def packedCoupling : ℝ := 2/chebyshev2.Packing.packedEigenvalue J hN ht 0

/--
The stated quantitative bound `0 < packedCoupling J hN ht`.

Use: `chebyshev2.Calibration.Data.packedObservation_tendsto` uses this bound to establish
the limit stated in that declaration.

Article: chebyshev2, Theorem E.1 via
`chebyshev2.DualCertificate.Data.packed_value_tendsto`.

Proof: Use the identities/estimates `chebyshev2.Packing.packedEigenvalue_zero_pos` with the
arguments shown in the proof.
-/
theorem packedCoupling_positive : 0 < packedCoupling J hN ht :=
  div_pos (by norm_num) (chebyshev2.Packing.packedEigenvalue_zero_pos J hN ht)

/--
Every finite matrix is allowed, including singleton and reducible blocks.

The stated quantitative bound `C.base (packedCoupling J hN ht)
(chebyshev2.Packing.packedLogDeterminant J hN ht (C.sigma*packedCoupling J hN ht)) ≤
J.normalizedEnergy`.

Use: `chebyshev2.Calibration.Data.greenConstant_ge_referenceBase` uses this bound to
establish the stated quantitative bound `C.referenceBase ≤ greenConstant`.

Article: chebyshev2, Theorem 1.2, retained factor 1.000013 via
`chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement`.

Proof: Identify the summands/integrands on their required domain before replacing the sum or
integral. Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem packed_energy_ge_base :
    C.base (packedCoupling J hN ht)
      (chebyshev2.Packing.packedLogDeterminant J hN ht (C.sigma*packedCoupling J hN ht)) ≤
      J.normalizedEnergy := by
  -- Identify the summands/integrands on their required domain before replacing the sum or
  -- integral.
  let P := chebyshev2.Packing.packing J hN ht
  let hm := (P.blocks hN).closedDensity_integrable
  let hn := (P.blocks hN).closedDensity_nonneg
  have hM : (∫ x, (P.blocks hN).closedDensity x)=1 := P.density_mass hN ht
  have hne : ¬ (P.blocks hN).closedDensity =ᵐ[volume] 0 := by
    intro he
    have hz := integral_congr_ae he
    simp only [Pi.zero_apply,integral_zero] at hz
    linarith
  let G := Classical.choice (ground_state hm hn hne)
  have h := C.energy_ge_base G hM
    (sqrt_cube_integrable_of_bounded hm hn ((P.blocks hN).closedDensity_bound))
  have he : (fun x => (sqrt ((P.blocks hN).closedDensity x))^3)=
      fun x => chebyshev2.Packing.packedDensity J hN ht x^(3/2:ℝ) :=
    funext (fun x => sqrt_cube_eq_rpow (hn x))
  rw [he,chebyshev2.Packing.packedDensity_energy J hN ht] at h
  exact h

end Data
end
end chebyshev2.Calibration

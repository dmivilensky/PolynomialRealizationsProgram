import chebyshev2.Residual.SpectralBound
import chebyshev2.Calibration.OneDeterminant
import chebyshev2.Filters.Relaxation
import chebyshev2.Filters.LinearEnergy
import chebyshev2.Calibration.FiniteTransfer

/-!
Article: chebyshev2, Theorem 3.6.
Analytic integration backend for Theorem 3.6(i).
Use: `chebyshev2.DualCertificate.AnalyticData.energy_ge_value` feeds
`chebyshev2.DualCertificate.AnalyticData.relaxed_energy_ge_target` (Theorem 3.6(i), once the
state criterion has been supplied).
Proof chain: `chebyshev2.DualCertificate.Data.uniform_finite_lower_bound` — chebyshev2,
Theorem 3.6; admissible certificates imply continuum, finite-fiber and gain bounds.
-/
namespace chebyshev2.DualCertificate
noncomputable section
open Set MeasureTheory Real chebyshev2.Calibration chebyshev2.Filters chebyshev2.GroundState
open chebyshev2.Residual chebyshev2.Continuum
set_option backward.isDefEq.respectTransparency false

/--
Analytic dual-certificate data: calibration, observation prices, a C¹ state potential and equal
endpoint potential values. Admissibility remains a separate pointwise inequality required by
the energy theorem.

Use: `chebyshev2.DualCertificate.AnalyticData.Admissible` uses this record of data and
proof obligations in the displayed construction of `Admissible`. Its inputs and component
formulas are fixed by that definition.

Article: chebyshev2, Theorem 3.6 via
`chebyshev2.DualCertificate.Data.admissible_analytic`.
-/
structure AnalyticData where
  /-- The contact calibration used by the analytic certificate. -/
  calibration : Data
  /-- Coefficient of the first fixed log-determinant observation. -/
  ξ₀ : ℝ
  /-- Coefficient of the second fixed log-determinant observation. -/
  ξ₁ : ℝ
  /-- Coefficient of the square-trace observation. -/
  χ : ℝ
  /-- Coefficient of the normalization term in the certificate value. -/
  τ : ℝ
  /-- Piecewise regular price for each positive ground parameter. -/
  price : (κ : ℝ) → 0<κ → Price
  /-- State potential depending on the ground parameter; its derivative enters the pointwise dual inequality. -/
  potential : ℝ → State → ℝ
  /-- The potential is C¹ for every positive ground parameter, permitting its derivative along the actual state flow. -/
  smooth : ∀ κ, 0<κ → ContDiff ℝ 1 (potential κ)
  /-- The potential takes the same value at both asymptotic state endpoints, so its integrated derivative contributes zero. -/
  boundary : ∀ κ, 0<κ → potential κ (0,0,0,0)=potential κ (2,0,0,2)

/--
Defines `scales` of type `chebyshev2.StateRegion.Scales` by `⟨κ,32,32,hκ,by norm_num,by
norm_num⟩`.

Use: `chebyshev2.DualCertificate.AnalyticData.Admissible` uses this definition in the
displayed construction of `Admissible`. Its inputs and component formulas are fixed by that
definition.

Article: chebyshev2, Theorem 3.6 via
`chebyshev2.DualCertificate.Data.admissible_analytic`.
-/
def scales {κ : ℝ} (hκ : 0<κ) : chebyshev2.StateRegion.Scales :=
  ⟨κ,32,32,hκ,by norm_num,by norm_num⟩

namespace AnalyticData
variable (A : AnalyticData)

/--
Defines `Admissible` of type `Prop`. The displayed construction fixes its component data; its
proof fields enforce the listed compatibility properties.

Use: `chebyshev2.DualCertificate.AnalyticData.relaxed_energy_ge_target` uses this
definition to prove the bound `A.targetValue ≤ ∫ x, (sqrt (m.value
x))^3`.

Article: chebyshev2, Theorem 3.6 via
`chebyshev2.DualCertificate.Data.admissible_analytic`.
-/
def Admissible {κ : ℝ} (hκ : 0<κ) : Prop :=
  (∀ Y ∈ (scales hκ).states, 0<Y.1 → Y.1<2 →
    conjugate (A.calibration.amplitude κ Y.1)
      (A.calibration.stateComparisonMultiplier hκ A.ξ₀ A.ξ₁ A.χ Y-
        (A.price κ hκ).value Y.1-bPotential κ (A.potential κ) Y) ≤
      criterionRhs κ (A.calibration.amplitude κ Y.1) (Q Y.1)
        ((A.price κ hκ).value Y.1) A.τ (bPotential κ (A.potential κ) Y)
          (dPotential (A.potential κ) Y)) ∧
  (∀ Y ∈ (scales hκ).states, Y.1=0 ∨ Y.1=2 →
    0≤A.calibration.stateResidual hκ A.ξ₀ A.ξ₁ A.χ A.τ (A.price κ hκ)
      (A.potential κ) Y 0)

/--
Defines `comparisonH` of type `ℝ` by `logDeterminant (kernelEigenvalue
((A.calibration.comparisonSpeed hκ).density_integrable hκ) ((A.calibration.comparisonSpeed
hκ).density_nonneg hκ)) s`.

Use: `chebyshev2.DualCertificate.AnalyticData.value` uses this definition in the displayed
construction of `value`. Its inputs and component formulas are fixed by that definition.

Article: chebyshev2, Theorem E.1 via
`chebyshev2.DualCertificate.Data.packed_value_tendsto`.
-/
def comparisonH {κ : ℝ} (hκ : 0<κ) (s : ℝ) : ℝ :=
  logDeterminant (kernelEigenvalue
    ((A.calibration.comparisonSpeed hκ).density_integrable hκ)
    ((A.calibration.comparisonSpeed hκ).density_nonneg hκ)) s

/--
Defines `comparisonS` of type `ℝ` by `∫ x, (linear ((A.calibration.comparisonSpeed
hκ).density_integrable hκ) ((A.calibration.comparisonSpeed hκ).density_nonneg hκ) x)^2`.

Use: `chebyshev2.DualCertificate.AnalyticData.value` uses this definition in the displayed
construction of `value`. Its inputs and component formulas are fixed by that definition.

Article: chebyshev2, Theorem E.1 via
`chebyshev2.DualCertificate.Data.packed_value_tendsto`.
-/
def comparisonS {κ : ℝ} (hκ : 0<κ) : ℝ :=
  ∫ x, (linear ((A.calibration.comparisonSpeed hκ).density_integrable hκ)
    ((A.calibration.comparisonSpeed hκ).density_nonneg hκ) x)^2

/--
Formula (30), with the observations kept as explicit real arguments.

Use: `chebyshev2.DualCertificate.AnalyticData.energy_ge_value` uses this definition to
establish the bound stated in that declaration.

Article: chebyshev2, Theorem E.1 via
`chebyshev2.DualCertificate.Data.packed_value_tendsto`.
-/
def value {κ : ℝ} (hκ : 0<κ) (H₀ H₁ Hσ S : ℝ) : ℝ :=
  A.calibration.base κ Hσ+A.ξ₀*(H₀-A.comparisonH hκ 32)+
    A.ξ₁*(H₁-A.comparisonH hκ 64)+A.χ*(S-A.comparisonS hκ)-
      priceCost κ A.τ (A.price κ hκ).value

/--
Defines `targetValue` of type `ℝ` by `A.value (κ := Real.pi^2/4) (div_pos (sq_pos_of_pos
pi_pos) (by norm_num)) (log (cosh (sqrt 32))) (log (cosh (sqrt 64))) (log (cosh (sqrt
(A.calibration.sigma*(Real.pi^2/4))))) ((Real.pi^2/4)^2/6)`.

Use: `chebyshev2.DualCertificate.AnalyticData.relaxed_energy_ge_target` uses this
definition to prove the bound `A.targetValue ≤ ∫ x, (sqrt (m.value
x))^3`.

Article: chebyshev2, Theorem 3.6 via
`chebyshev2.DualCertificate.Data.relaxed_energy_ge_value`.
-/
def targetValue : ℝ :=
  A.value (κ := Real.pi^2/4) (div_pos (sq_pos_of_pos pi_pos) (by norm_num))
    (log (cosh (sqrt 32))) (log (cosh (sqrt 64)))
    (log (cosh (sqrt (A.calibration.sigma*(Real.pi^2/4))))) ((Real.pi^2/4)^2/6)

/--
The stated quantitative bound `A.value G.coupling_positive (logDeterminant (kernelEigenvalue hm
hn) 32) (logDeterminant (kernelEigenvalue hm hn) 64) (logDeterminant (kernelEigenvalue hm hn)
(A.calibration.sigma*groundParameter hm hn)) (∫ x, (linear hm hn x)^2) ≤ ∫ x, (sqrt (m x))^3`.

Use: `chebyshev2.DualCertificate.AnalyticData.relaxed_energy_ge_target` uses this bound to
establish the stated quantitative bound `A.targetValue ≤ ∫ x, (sqrt (m.value x))^3`.

Article: chebyshev2, Theorem 3.6 via
`chebyshev2.DualCertificate.Data.relaxed_energy_ge_value`.

Proof: Use the identities/estimates
`chebyshev2.GroundState.GroundWitness.coupling_positive`,
`chebyshev2.Calibration.Data.energy_ge_spectral_bound`,
`chebyshev2.Residual.pointwise_criterion` with the arguments shown in the proof.
-/
theorem energy_ge_value {m : ℝ → ℝ} {hm : Integrable m} {hn : ∀ x, 0≤m x}
    (G : GroundWitness hm hn) (ha : A.Admissible G.coupling_positive)
    (hM : (∫ x, m x)=1) (hE : Integrable (fun x => (sqrt (m x))^3)) :
    A.value G.coupling_positive
      (logDeterminant (kernelEigenvalue hm hn) 32)
      (logDeterminant (kernelEigenvalue hm hn) 64)
      (logDeterminant (kernelEigenvalue hm hn) (A.calibration.sigma*groundParameter hm hn))
      (∫ x, (linear hm hn x)^2) ≤ ∫ x, (sqrt (m x))^3 := by
  -- Use the identities/estimates `chebyshev2.GroundState.GroundWitness.coupling_positive`,
  -- `chebyshev2.Calibration.Data.energy_ge_spectral_bound`,
  -- `chebyshev2.Residual.pointwise_criterion` with the arguments shown in the proof.
  have h := A.calibration.energy_ge_spectral_bound G A.ξ₀ A.ξ₁ A.χ A.τ
    (A.price _ G.coupling_positive) (A.smooth _ G.coupling_positive)
    (A.boundary _ G.coupling_positive) hM hE
    (fun Y hY h₀ h₂ n hn => (pointwise_criterion G.coupling_positive.ne' _ _ _ _ _ _ _).2
      (ha.1 Y hY h₀ h₂) n hn) ha.2
  convert h using 1
  dsimp [value,comparisonH,comparisonS,Data.determinantDifference,Data.traceDifference]
  ring

/--
Theorem 3.6(i), once the state criterion has been supplied. No finite energy assumption is
added to the literal compact bounded relaxed class.

The stated quantitative bound `A.targetValue ≤ ∫ x, (sqrt (m.value x))^3`.

Use: `chebyshev2.DualCertificate.Data.relaxed_energy_ge_value` uses this bound to establish
the stated quantitative bound `D.analytic.targetValue≤∫ x,(sqrt (m.value x))^3`.

Article: chebyshev2, Theorem 3.6 via
`chebyshev2.DualCertificate.Data.relaxed_energy_ge_value`.

Proof: Identify the summands/integrands on their required domain before replacing the sum or
integral.
-/
theorem relaxed_energy_ge_target (m : CompactDensity)
    (hm : m ∈ CompactDensity.relaxed A.calibration.sigma)
    (ha : A.Admissible (κ := Real.pi^2/4) (div_pos (sq_pos_of_pos pi_pos) (by norm_num))) :
    A.targetValue ≤ ∫ x, (sqrt (m.value x))^3 := by
  -- Identify the summands/integrands on their required domain before replacing the sum or
  -- integral.
  obtain ⟨hk,h₀,h₁,hσ,hS⟩ := (m.relaxed_iff A.calibration.sigma).mp hm
  dsimp only [CompactDensity.coupling,CompactDensity.H,CompactDensity.spectrum]
    at hk h₀ h₁ hσ hS
  have hne : ¬m.value=ᵐ[volume] 0 := by
    intro he
    have hi := integral_congr_ae he
    simp only [Pi.zero_apply,integral_zero,m.mass_one] at hi
    norm_num at hi
  let G := Classical.choice (ground_state m.integrable m.nonneg hne)
  obtain ⟨B,hB⟩ := m.bounded
  have hE := sqrt_cube_integrable_of_bounded m.integrable m.nonneg hB
  have hak : A.Admissible G.coupling_positive := by
    simpa only [hk] using ha
  have h := A.energy_ge_value G hak m.mass_one hE
  have hs : (∫ x, (linear m.integrable m.nonneg x)^2)=(Real.pi^2/4)^2/6 := by
    rw [linear_square_trace m.integrable m.nonneg]
    rw [hk,hS]
    ring
  rw [hs,h₀,h₁,hσ] at h
  simpa only [targetValue,hk] using h

end AnalyticData
end
end chebyshev2.DualCertificate

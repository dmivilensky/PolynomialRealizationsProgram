import chebyshev2.Comparison.ProfileCalibration

/-!
Article: chebyshev2, Proposition 8.
The calibration case of the general comparison-profile theorem (Lemma 12).
Use: `chebyshev2.Calibration.Data.signed_determinant_comparison` feeds
`chebyshev2.Calibration.Data.comparisonDefect_integral` (comparison Defect integral).
Proof chain: `chebyshev2.Calibration.Data.energy_ge_spectral_bound` — chebyshev2, Theorem 3.5;
Pointwise cubic-conjugate criterion, gauge invariance and regular price.
-/
namespace chebyshev2.Calibration.Data
noncomputable section
open Set MeasureTheory Real chebyshev2.GroundState chebyshev2.Filters chebyshev2.Comparison
set_option backward.isDefEq.respectTransparency false
variable (C : chebyshev2.Calibration.Data) {m : ℝ → ℝ} {hm : Integrable m}
  {hn : ∀ x, 0 ≤ m x} (G : GroundWitness hm hn)
variable {s : ℝ} (hs : 0 ≤ s)
include hs

/--
The precise assertion is `chebyshev2.Continuum.logDeterminant
(chebyshev2.Continuum.kernelEigenvalue hm hn) s- chebyshev2.Continuum.logDeterminant
(chebyshev2.Continuum.kernelEigenvalue ((C.comparisonSpeed
G.coupling_positive).density_integrable G.coupling_positive) ((C.comparisonSpeed
G.coupling_positive).density_nonneg G.coupling_positive)) s= ∫ x, C.comparisonA
G.coupling_positive s (G.q x) (nonlinear s m x)* (m x-(C.amplitude (groundParameter hm hn) (G.q
x))^2)`.

Use: `chebyshev2.Calibration.Data.comparisonDefect_integral` rewrites with this identity to
establish the precise assertion is `(∫ x, C.comparisonDefect G ξ₀ ξ₁ χ x)=
ξ₀*C.determinantDifference G 32+ξ₁*C.determinantDifference G 64+χ*C.traceDifference G`.

Article: chebyshev2, Theorem 3.5 via
`chebyshev2.Calibration.Data.energy_ge_spectral_bound`.

Proof: Use the identities/estimates
`chebyshev2.GroundState.GroundWitness.coupling_positive`,
`chebyshev2.PrescribedSpeed.SpeedData.density_integrable`,
`chebyshev2.PrescribedSpeed.SpeedData.density_nonneg` with the arguments shown in the
proof.
-/
theorem signed_determinant_comparison :
    chebyshev2.Continuum.logDeterminant (chebyshev2.Continuum.kernelEigenvalue hm hn) s-
      chebyshev2.Continuum.logDeterminant
        (chebyshev2.Continuum.kernelEigenvalue
          ((C.comparisonSpeed G.coupling_positive).density_integrable G.coupling_positive)
          ((C.comparisonSpeed G.coupling_positive).density_nonneg G.coupling_positive)) s=
      ∫ x, C.comparisonA G.coupling_positive s (G.q x) (nonlinear s m x)*
        (m x-(C.amplitude (groundParameter hm hn) (G.q x))^2) := by
  -- Use the identities/estimates `chebyshev2.GroundState.GroundWitness.coupling_positive`,
  -- `chebyshev2.PrescribedSpeed.SpeedData.density_integrable`,
  -- `chebyshev2.PrescribedSpeed.SpeedData.density_nonneg` with the arguments shown in the
  -- proof.
  have h := Profile.signed_determinant_comparison G (C.comparisonProfile G.coupling_positive) hs
  have hobs : chebyshev2.Continuum.logDeterminant
      (chebyshev2.Continuum.kernelEigenvalue
        (((C.comparisonProfile G.coupling_positive).speedData G.coupling_positive).density_integrable G.coupling_positive)
        (((C.comparisonProfile G.coupling_positive).speedData G.coupling_positive).density_nonneg G.coupling_positive)) s=
      chebyshev2.Continuum.logDeterminant
        (chebyshev2.Continuum.kernelEigenvalue
          ((C.comparisonSpeed G.coupling_positive).density_integrable G.coupling_positive)
          ((C.comparisonSpeed G.coupling_positive).density_nonneg G.coupling_positive)) s := by
    congr 1
    apply chebyshev2.Continuum.kernelEigenvalue_congr
    exact C.comparisonProfile_density G.coupling_positive
  rw [hobs,C.comparisonProfile_A G.coupling_positive] at h
  exact h

end
end chebyshev2.Calibration.Data

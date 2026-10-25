import chebyshev2.Comparison.ProfileCalibration
import chebyshev2.Comparison.DeterminantComparison

/-!
Article: chebyshev2, Proposition 8.
The calibration case of the general comparison-profile theorem (Lemma 12).
Use: `chebyshev2.Calibration.Data.signed_trace_comparison` feeds
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

/--
The precise assertion is `(∫ x, (linear hm hn x)^2)- (∫ x, (linear ((C.comparisonSpeed
G.coupling_positive).density_integrable G.coupling_positive) ((C.comparisonSpeed
G.coupling_positive).density_nonneg G.coupling_positive) x)^2)= ∫ x, C.comparisonA0
G.coupling_positive (G.q x) (linear hm hn x)* (m x-(C.amplitude (groundParameter hm hn) (G.q
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
theorem signed_trace_comparison :
    (∫ x, (linear hm hn x)^2)-
      (∫ x, (linear ((C.comparisonSpeed G.coupling_positive).density_integrable G.coupling_positive)
        ((C.comparisonSpeed G.coupling_positive).density_nonneg G.coupling_positive) x)^2)=
      ∫ x, C.comparisonA0 G.coupling_positive (G.q x) (linear hm hn x)*
        (m x-(C.amplitude (groundParameter hm hn) (G.q x))^2) := by
  -- Use the identities/estimates `chebyshev2.GroundState.GroundWitness.coupling_positive`,
  -- `chebyshev2.PrescribedSpeed.SpeedData.density_integrable`,
  -- `chebyshev2.PrescribedSpeed.SpeedData.density_nonneg` with the arguments shown in the
  -- proof.
  have h := Profile.signed_trace_comparison G (C.comparisonProfile G.coupling_positive)
  have hlin : linear
      (((C.comparisonProfile G.coupling_positive).speedData G.coupling_positive).density_integrable G.coupling_positive)
      (((C.comparisonProfile G.coupling_positive).speedData G.coupling_positive).density_nonneg G.coupling_positive)=
      linear ((C.comparisonSpeed G.coupling_positive).density_integrable G.coupling_positive)
        ((C.comparisonSpeed G.coupling_positive).density_nonneg G.coupling_positive) := by
    apply linear_congr
    exact C.comparisonProfile_density G.coupling_positive
  rw [hlin,C.comparisonProfile_A0 G.coupling_positive] at h
  exact h

end
end chebyshev2.Calibration.Data

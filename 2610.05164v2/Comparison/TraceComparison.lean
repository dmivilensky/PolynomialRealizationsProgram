import «2610.05164v2».Comparison.ProfileCalibration
import «2610.05164v2».Comparison.DeterminantComparison

/-!
Article: 2610.05164v2, Proposition 8.
The calibration case of the general comparison-profile theorem (Lemma 12).
Use: `«2610.05164v2».Calibration.Data.signed_trace_comparison` feeds
`«2610.05164v2».Calibration.Data.comparisonDefect_integral` (comparison Defect integral).
Proof chain: `«2610.05164v2».Calibration.Data.energy_ge_spectral_bound` — 2610.05164v2, Theorem 3.5;
Pointwise cubic-conjugate criterion, gauge invariance and regular price.
-/
namespace «2610.05164v2».Calibration.Data
noncomputable section
open Set MeasureTheory Real «2610.05164v2».GroundState «2610.05164v2».Filters «2610.05164v2».Comparison
set_option backward.isDefEq.respectTransparency false
variable (C : «2610.05164v2».Calibration.Data) {m : ℝ → ℝ} {hm : Integrable m}
  {hn : ∀ x, 0 ≤ m x} (G : GroundWitness hm hn)

/--
The precise assertion is `(∫ x, (linear hm hn x)^2)- (∫ x, (linear ((C.comparisonSpeed
G.coupling_positive).density_integrable G.coupling_positive) ((C.comparisonSpeed
G.coupling_positive).density_nonneg G.coupling_positive) x)^2)= ∫ x, C.comparisonA0
G.coupling_positive (G.q x) (linear hm hn x)* (m x-(C.amplitude (groundParameter hm hn) (G.q
x))^2)`.

Use: `«2610.05164v2».Calibration.Data.comparisonDefect_integral` rewrites with this identity to
establish the precise assertion is `(∫ x, C.comparisonDefect G ξ₀ ξ₁ χ x)=
ξ₀*C.determinantDifference G 32+ξ₁*C.determinantDifference G 64+χ*C.traceDifference G`.

Article: 2610.05164v2, Theorem 3.5 via
`«2610.05164v2».Calibration.Data.energy_ge_spectral_bound`.

Proof: Use the identities/estimates
`«2610.05164v2».GroundState.GroundWitness.coupling_positive`,
`«2610.05164v2».PrescribedSpeed.SpeedData.density_integrable`,
`«2610.05164v2».PrescribedSpeed.SpeedData.density_nonneg` with the arguments shown in the
proof.
-/
theorem signed_trace_comparison :
    (∫ x, (linear hm hn x)^2)-
      (∫ x, (linear ((C.comparisonSpeed G.coupling_positive).density_integrable G.coupling_positive)
        ((C.comparisonSpeed G.coupling_positive).density_nonneg G.coupling_positive) x)^2)=
      ∫ x, C.comparisonA0 G.coupling_positive (G.q x) (linear hm hn x)*
        (m x-(C.amplitude (groundParameter hm hn) (G.q x))^2) := by
  -- Use the identities/estimates `«2610.05164v2».GroundState.GroundWitness.coupling_positive`,
  -- `«2610.05164v2».PrescribedSpeed.SpeedData.density_integrable`,
  -- `«2610.05164v2».PrescribedSpeed.SpeedData.density_nonneg` with the arguments shown in the
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
end «2610.05164v2».Calibration.Data

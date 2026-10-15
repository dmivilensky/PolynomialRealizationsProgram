import «2610.05164v2».Comparison.ProfileCalibration

/-!
Article: 2610.05164v2, Proposition 8.
The calibration case of the general comparison-profile theorem (Lemma 12).
Use: `«2610.05164v2».Calibration.Data.signed_determinant_comparison` feeds
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
variable {s : ℝ} (hs : 0 ≤ s)
include hs

/--
The precise assertion is `«2610.05164v2».Continuum.logDeterminant
(«2610.05164v2».Continuum.kernelEigenvalue hm hn) s- «2610.05164v2».Continuum.logDeterminant
(«2610.05164v2».Continuum.kernelEigenvalue ((C.comparisonSpeed
G.coupling_positive).density_integrable G.coupling_positive) ((C.comparisonSpeed
G.coupling_positive).density_nonneg G.coupling_positive)) s= ∫ x, C.comparisonA
G.coupling_positive s (G.q x) (nonlinear s m x)* (m x-(C.amplitude (groundParameter hm hn) (G.q
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
theorem signed_determinant_comparison :
    «2610.05164v2».Continuum.logDeterminant («2610.05164v2».Continuum.kernelEigenvalue hm hn) s-
      «2610.05164v2».Continuum.logDeterminant
        («2610.05164v2».Continuum.kernelEigenvalue
          ((C.comparisonSpeed G.coupling_positive).density_integrable G.coupling_positive)
          ((C.comparisonSpeed G.coupling_positive).density_nonneg G.coupling_positive)) s=
      ∫ x, C.comparisonA G.coupling_positive s (G.q x) (nonlinear s m x)*
        (m x-(C.amplitude (groundParameter hm hn) (G.q x))^2) := by
  -- Use the identities/estimates `«2610.05164v2».GroundState.GroundWitness.coupling_positive`,
  -- `«2610.05164v2».PrescribedSpeed.SpeedData.density_integrable`,
  -- `«2610.05164v2».PrescribedSpeed.SpeedData.density_nonneg` with the arguments shown in the
  -- proof.
  have h := Profile.signed_determinant_comparison G (C.comparisonProfile G.coupling_positive) hs
  have hobs : «2610.05164v2».Continuum.logDeterminant
      («2610.05164v2».Continuum.kernelEigenvalue
        (((C.comparisonProfile G.coupling_positive).speedData G.coupling_positive).density_integrable G.coupling_positive)
        (((C.comparisonProfile G.coupling_positive).speedData G.coupling_positive).density_nonneg G.coupling_positive)) s=
      «2610.05164v2».Continuum.logDeterminant
        («2610.05164v2».Continuum.kernelEigenvalue
          ((C.comparisonSpeed G.coupling_positive).density_integrable G.coupling_positive)
          ((C.comparisonSpeed G.coupling_positive).density_nonneg G.coupling_positive)) s := by
    congr 1
    apply «2610.05164v2».Continuum.kernelEigenvalue_congr
    exact C.comparisonProfile_density G.coupling_positive
  rw [hobs,C.comparisonProfile_A G.coupling_positive] at h
  exact h

end
end «2610.05164v2».Calibration.Data

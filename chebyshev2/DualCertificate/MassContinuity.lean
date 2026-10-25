import chebyshev2.Comparison.MassRatioContinuity
import chebyshev2.Residual.RegularPriceCost

/-!
Article: chebyshev2, Theorem 3.6.
Continuity of the actual comparison mass appearing in (31) and (32).
Use: `chebyshev2.Calibration.Data.comparisonMass_continuous` feeds
`chebyshev2.DualCertificate.Data.priceCost_continuous` (price Cost continuous).
Proof chain: `chebyshev2.DualCertificate.Data.uniform_finite_lower_bound` — chebyshev2,
Theorem 3.6; admissible certificates imply continuum, finite-fiber and gain bounds.
-/
namespace chebyshev2.Calibration.Data
noncomputable section
open Set Filter MeasureTheory Real
open scoped Topology
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
variable (C : chebyshev2.Calibration.Data)

 /--
Continuity of the displayed function: `Continuous (fun κ : Ioi (0:ℝ) => ∫ x,
C.comparisonDensity κ.property x)`.

Use: `chebyshev2.DualCertificate.Data.priceCost_continuous` uses this continuity result to
establish continuity of the displayed function: `Continuous (fun κ : Ioi (0:ℝ) => priceCost κ
(D.τ:ℝ) (D.price κ.property).value)`.

Article: chebyshev2, Theorem E.1 via
`chebyshev2.DualCertificate.Data.packed_value_tendsto`.

Proof: Pass the established inequalities to the limit using the displayed filter convergence.
-/
theorem comparisonMass_continuous :
    Continuous (fun κ : Ioi (0:ℝ) => ∫ x, C.comparisonDensity κ.property x) := by
  -- Pass the established inequalities to the limit using the displayed filter convergence.
  rw [continuous_iff_continuousAt]
  intro k
  -- Record the convergence hratio with its source filter and target limit before taking limits
  -- in the subsequent identities/bounds.
  have hratio : Tendsto (fun κ : Ioi (0:ℝ) => ∫ q in Ioo (0:ℝ) 2, C.amplitudeRatio κ q)
      (𝓝 k) (𝓝 (∫ q in Ioo (0:ℝ) 2, C.amplitudeRatio k q)) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    have hz := (C.amplitudeRatio_L1_tendsto k.property).comp continuous_subtype_val.continuousAt.tendsto
    apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) _ hz
    apply Eventually.of_forall
    intro κ
    rw [← integral_sub (C.amplitudeRatio_integrable κ.property) (C.amplitudeRatio_integrable k.property)]
    simpa only [Real.norm_eq_abs,Function.comp_apply] using norm_integral_le_integral_norm
      (f := fun q => C.amplitudeRatio κ q-C.amplitudeRatio k q)
      (μ := volume.restrict (Ioo (0:ℝ) 2))
  simpa only [C.comparisonDensity_mass,amplitudeRatio,ContinuousAt] using hratio

end
end chebyshev2.Calibration.Data

import chebyshev2.Comparison.RatioContinuity

/-!
Article: chebyshev2, Lemma 10.
L1 continuity of the mass ratio κν²/d.
Use: `chebyshev2.Calibration.Data.massRatio_L1_tendsto` feeds
`chebyshev2.Calibration.Data.linearError_tendsto` (linear Error tendsto).
Proof chain: `chebyshev2.DualCertificate.Data.admissible_stable` — chebyshev2, Theorem E.1;
Stability of strict admissibility and uniform transfer of the certificate value.
-/
namespace chebyshev2.Calibration.Data
noncomputable section
open Set MeasureTheory Filter Real chebyshev2.Calibration
open scoped Topology
set_option backward.isDefEq.respectTransparency false
variable (C : chebyshev2.Calibration.Data)

/--
Defines `massRatio` of type `ℝ` by `κ*C.amplitudeRatio κ q`.

Use: `chebyshev2.Calibration.Data.massRatio_L1_tendsto` uses this definition to establish
convergence along the specified source filter to the specified limit: `Tendsto (fun κ => ∫ q in
Ioo (0:ℝ) 2, |C.massRatio κ q-C.massRatio k q|) (𝓝 k) (𝓝 0)`.

Article: chebyshev2, Theorem E.1 via
`chebyshev2.DualCertificate.Data.packed_value_tendsto`.
-/
def massRatio (κ q : ℝ) : ℝ := κ*C.amplitudeRatio κ q

/--
Integrability on the stated domain: `IntegrableOn (C.massRatio κ) (Ioo (0:ℝ) 2)`.

Use: `chebyshev2.Calibration.Data.massRatio_L1_tendsto` uses this integrability result to
establish convergence along the specified source filter to the specified limit: `Tendsto (fun κ
=> ∫ q in Ioo (0:ℝ) 2, |C.massRatio κ q-C.massRatio k q|) (𝓝 k) (𝓝 0)`.

Article: chebyshev2, Theorem E.1 via
`chebyshev2.DualCertificate.Data.packed_value_tendsto`.

Proof: Use the identities/estimates `chebyshev2.Calibration.Data.amplitudeRatio_integrable`
with the arguments shown in the proof.
-/
theorem massRatio_integrable {κ : ℝ} (hκ : 0 < κ) :
    IntegrableOn (C.massRatio κ) (Ioo (0:ℝ) 2) :=
  (C.amplitudeRatio_integrable hκ).const_mul κ

/--
Membership in the specified domain/enclosure: `C.massRatio κ q ∈ Icc (0:ℝ) (3/2)`.

Use: `chebyshev2.Calibration.Data.massRatio_L1_tendsto` uses this assertion to establish
convergence along the specified source filter to the specified limit: `Tendsto (fun κ => ∫ q in
Ioo (0:ℝ) 2, |C.massRatio κ q-C.massRatio k q|) (𝓝 k) (𝓝 0)`.

Article: chebyshev2, Theorem E.1 via
`chebyshev2.DualCertificate.Data.packed_value_tendsto`.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem massRatio_bounds {κ q : ℝ} (hκ : 0 < κ) (hq : q ∈ Ioo (0:ℝ) 2) :
    C.massRatio κ q ∈ Icc (0:ℝ) (3/2) := by
  refine ⟨mul_nonneg hκ.le (div_nonneg (sq_nonneg _) (C.speed_positive hκ hq).le),?_⟩
  have h := mul_le_mul_of_nonneg_left (C.amplitude_square_div_speed hκ hq).le hκ.le
  have he : κ*(3/(2*κ))=3/2 := by field_simp
  change C.massRatio κ q ≤ _ at h
  linarith

/--
Convergence along the specified source filter to the specified limit: `Tendsto (fun κ => ∫ q in
Ioo (0:ℝ) 2, |C.massRatio κ q-C.massRatio k q|) (𝓝 k) (𝓝 0)`.

Use: `chebyshev2.Calibration.Data.linearError_tendsto` uses this limit to establish
convergence along the specified source filter to the specified limit: `Tendsto (fun κ =>
C.linearError κ k) (𝓝 k) (𝓝 0)`.

Article: chebyshev2, Theorem E.1 via
`chebyshev2.DualCertificate.Data.packed_value_tendsto`.

Proof: Use the identities/estimates `chebyshev2.Calibration.Data.massRatio_integrable`,
`chebyshev2.Calibration.Data.massRatio_bounds`,
`chebyshev2.Calibration.Data.amplitude_continuousOn` with the arguments shown in the proof.
Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation at an
arbitrary point in that intersection.
-/
theorem massRatio_L1_tendsto {k : ℝ} (hk : 0 < k) :
    Tendsto (fun κ => ∫ q in Ioo (0:ℝ) 2, |C.massRatio κ q-C.massRatio k q|)
      (𝓝 k) (𝓝 0) := by
  -- Apply the dominated-convergence/Lp transfer after supplying the domination and
  -- pointwise-limit hypotheses.
  have hnear : ∀ᶠ κ in 𝓝 k, 0 < κ := isOpen_Ioi.mem_nhds hk
  have hm : ∀ᶠ κ in 𝓝 k, AEStronglyMeasurable
      (fun q => |C.massRatio κ q-C.massRatio k q|) (volume.restrict (Ioo (0:ℝ) 2)) := by
    filter_upwards [hnear] with κ hκ
    exact ((C.massRatio_integrable hκ).aestronglyMeasurable.sub
      (C.massRatio_integrable hk).aestronglyMeasurable).norm
  have hb : ∀ᶠ κ in 𝓝 k, ∀ᵐ q ∂volume.restrict (Ioo (0:ℝ) 2),
      ‖|C.massRatio κ q-C.massRatio k q|‖ ≤ (3:ℝ) := by
    filter_upwards [hnear] with κ hκ
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with q hq
    have h1 := C.massRatio_bounds hκ hq
    have h2 := C.massRatio_bounds hk hq
    rw [Real.norm_eq_abs,abs_abs]
    exact (abs_sub _ _).trans (by rw [abs_of_nonneg h1.1,abs_of_nonneg h2.1]; linarith [h1.2,h2.2])
  have hl : ∀ᵐ q ∂volume.restrict (Ioo (0:ℝ) 2),
      Tendsto (fun κ => |C.massRatio κ q-C.massRatio k q|) (𝓝 k) (𝓝 0) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with q hq
    -- Establish continuity hac before using the function at limits or in calculus arguments.
    have hac : ContinuousAt (fun κ => C.amplitude κ q) k :=
      (C.amplitude_continuousOn.comp (continuous_id.prodMk continuous_const).continuousOn
        (fun κ hκ => ⟨hκ,⟨hq.1.le,hq.2.le⟩⟩)).continuousAt (isOpen_Ioi.mem_nhds hk)
    -- Establish continuity hsc before using the function at limits or in calculus arguments.
    have hsc : ContinuousAt (fun κ => C.speed κ q) k :=
      (continuousAt_id.mul (hac.pow 2)).sub continuousAt_const
    -- Record the convergence h with its source filter and target limit before taking limits in
    -- the subsequent identities/bounds.
    have h : Tendsto (fun κ => C.massRatio κ q) (𝓝 k) (𝓝 (C.massRatio k q)) :=
      (continuousAt_id.mul ((hac.pow 2).div hsc (C.speed_positive hk hq).ne')).tendsto
    simpa only [sub_self,abs_zero] using (h.sub_const (C.massRatio k q)).abs
  have h := tendsto_integral_filter_of_dominated_convergence (fun _ => (3:ℝ)) hm hb
    (integrableOn_const (C := (3:ℝ)) (s := Ioo (0:ℝ) 2) (by simp)) hl
  simpa only [integral_zero] using h

end
end chebyshev2.Calibration.Data

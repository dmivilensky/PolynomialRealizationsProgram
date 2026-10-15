import «2610.05164v2».Comparison.ReciprocalContinuity

/-!
Article: 2610.05164v2, Lemma 11.
The bounded amplitude/speed ratio is continuous in L1 at every positive parameter.
Use: `«2610.05164v2».Calibration.Data.amplitudeRatio_L1_tendsto` feeds
`«2610.05164v2».Calibration.Data.comparisonMass_continuous` (comparison Mass continuous).
Proof chain: `«2610.05164v2».DualCertificate.Data.uniform_finite_lower_bound` — 2610.05164v2,
Theorem E.1; Stability of strict admissibility and uniform transfer of the certificate value.
-/
namespace «2610.05164v2».Calibration.Data
noncomputable section
open Set MeasureTheory Filter Real «2610.05164v2».Calibration
open scoped Topology
set_option backward.isDefEq.respectTransparency false
variable (C : «2610.05164v2».Calibration.Data)

/--
Defines `amplitudeRatio` of type `ℝ` by `(C.amplitude κ q)^2/C.speed κ q`.

Use: `«2610.05164v2».Calibration.Data.amplitudeRatio_L1_tendsto` uses this definition to
establish convergence along the specified source filter to the specified limit: `Tendsto (fun κ
=> ∫ q in Ioo (0:ℝ) 2, |C.amplitudeRatio κ q-C.amplitudeRatio k q|) (𝓝 k) (𝓝 0)`.

Article: 2610.05164v2, Theorem E.1 via
`«2610.05164v2».DualCertificate.Data.packed_value_tendsto`.
-/
def amplitudeRatio (κ q : ℝ) : ℝ := (C.amplitude κ q)^2/C.speed κ q

/--
Integrability on the stated domain: `IntegrableOn (C.amplitudeRatio κ) (Ioo (0:ℝ) 2)`.

Use: `«2610.05164v2».Calibration.Data.amplitudeRatio_L1_tendsto` uses this integrability result
to establish convergence along the specified source filter to the specified limit: `Tendsto
(fun κ => ∫ q in Ioo (0:ℝ) 2, |C.amplitudeRatio κ q-C.amplitudeRatio k q|) (𝓝 k) (𝓝 0)`.

Article: 2610.05164v2, Theorem E.1 via
`«2610.05164v2».DualCertificate.Data.packed_value_tendsto`.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection.
-/
theorem amplitudeRatio_integrable {κ : ℝ} (hκ : 0 < κ) :
    IntegrableOn (C.amplitudeRatio κ) (Ioo (0:ℝ) 2) := by
  -- Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
  -- at an arbitrary point in that intersection.
  apply (integrableOn_const (C := 3/(2*κ)) (s := Ioo (0:ℝ) 2) (by simp)).mono'
  · apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioo
    exact (((C.amplitude_continuousOn_fixed hκ).mono Ioo_subset_Icc_self).pow 2).div
      ((((C.amplitude_continuousOn_fixed hκ).mono Ioo_subset_Icc_self).pow 2).const_mul κ |>.sub
        (by unfold Q; fun_prop)) (fun q hq => (C.speed_positive hκ hq).ne')
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with q hq
    dsimp only [amplitudeRatio]
    rw [Real.norm_of_nonneg (div_nonneg (sq_nonneg _) (C.speed_positive hκ hq).le)]
    exact (C.amplitude_square_div_speed hκ hq).le

/--
Convergence along the specified source filter to the specified limit: `Tendsto (fun κ => ∫ q in
Ioo (0:ℝ) 2, |C.amplitudeRatio κ q-C.amplitudeRatio k q|) (𝓝 k) (𝓝 0)`.

Use: `«2610.05164v2».Calibration.Data.comparisonMass_continuous` uses this limit to establish
continuity of the displayed function: `Continuous (fun κ : Ioi (0:ℝ) => ∫ x,
C.comparisonDensity κ.property x)`.

Article: 2610.05164v2, Theorem E.1 via
`«2610.05164v2».DualCertificate.Data.packed_value_tendsto`.

Proof: Use the identities/estimates
`«2610.05164v2».Calibration.Data.amplitudeRatio_integrable`,
`«2610.05164v2».Calibration.Data.amplitude_square_div_speed`,
`«2610.05164v2».Calibration.Data.speed_positive` with the arguments shown in the proof.
Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation at an
arbitrary point in that intersection.
-/
theorem amplitudeRatio_L1_tendsto {k : ℝ} (hk : 0 < k) :
    Tendsto (fun κ => ∫ q in Ioo (0:ℝ) 2, |C.amplitudeRatio κ q-C.amplitudeRatio k q|)
      (𝓝 k) (𝓝 0) := by
  -- Apply the dominated-convergence/Lp transfer after supplying the domination and
  -- pointwise-limit hypotheses.
  have hnear : ∀ᶠ κ in 𝓝 k, k/2 < κ := lt_mem_nhds (show k/2 < k by linarith)
  have hm : ∀ᶠ κ in 𝓝 k, AEStronglyMeasurable
      (fun q => |C.amplitudeRatio κ q-C.amplitudeRatio k q|) (volume.restrict (Ioo (0:ℝ) 2)) := by
    filter_upwards [hnear] with κ hκ
    exact ((C.amplitudeRatio_integrable (by linarith)).aestronglyMeasurable.sub
      (C.amplitudeRatio_integrable hk).aestronglyMeasurable).norm
  have hb : ∀ᶠ κ in 𝓝 k, ∀ᵐ q ∂volume.restrict (Ioo (0:ℝ) 2),
      ‖|C.amplitudeRatio κ q-C.amplitudeRatio k q|‖ ≤ 6/k := by
    filter_upwards [hnear] with κ hκ
    have hp : 0 < κ := by linarith
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with q hq
    have h1 := (C.amplitude_square_div_speed hp hq).le
    have h2 := (C.amplitude_square_div_speed hk hq).le
    have h3 : 3/(2*κ) ≤ 3/k := (div_le_div_iff₀ (by positivity) hk).2 (by linarith)
    have h4 : 3/(2*k) ≤ 3/k := (div_le_div_iff₀ (by positivity) hk).2 (by linarith)
    rw [Real.norm_eq_abs,abs_abs]
    calc
      _ ≤ |C.amplitudeRatio κ q|+|C.amplitudeRatio k q| := abs_sub _ _
      _ ≤ 6/k := by
        dsimp only [amplitudeRatio]
        rw [abs_of_nonneg (div_nonneg (sq_nonneg _) (C.speed_positive hp hq).le),
          abs_of_nonneg (div_nonneg (sq_nonneg _) (C.speed_positive hk hq).le)]
        change C.amplitudeRatio κ q+C.amplitudeRatio k q ≤ _
        change C.amplitudeRatio κ q ≤ _ at h1
        change C.amplitudeRatio k q ≤ _ at h2
        have he : 3/k+3/k=6/k := by ring
        linarith
  have hl : ∀ᵐ q ∂volume.restrict (Ioo (0:ℝ) 2),
      Tendsto (fun κ => |C.amplitudeRatio κ q-C.amplitudeRatio k q|) (𝓝 k) (𝓝 0) := by
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
    have h : Tendsto (fun κ => C.amplitudeRatio κ q) (𝓝 k) (𝓝 (C.amplitudeRatio k q)) :=
      ((hac.pow 2).div hsc (C.speed_positive hk hq).ne').tendsto
    simpa only [sub_self,abs_zero] using (h.sub_const (C.amplitudeRatio k q)).abs
  have h := tendsto_integral_filter_of_dominated_convergence (fun _ => 6/k) hm hb
    (integrableOn_const (C := 6/k) (s := Ioo (0:ℝ) 2) (by simp)) hl
  simpa only [integral_zero] using h

end
end «2610.05164v2».Calibration.Data

import «2610.05164v2».Calibration.Reciprocal

/-!
Article: 2610.05164v2, Lemma 10.
Lemma 10: continuity of the reciprocal speed in L1(0,2), including the singular endpoints, by a
common integrable Q^(-2/3) majorant.
Use: `«2610.05164v2».Calibration.Data.reciprocalSpeed_L1_tendsto` feeds
`«2610.05164v2».Calibration.Data.linearError_tendsto` (linear Error tendsto).
Proof chain: `«2610.05164v2».DualCertificate.Data.admissible_stable` — 2610.05164v2, Theorem E.1;
Stability of strict admissibility and uniform transfer of the certificate value.
-/
namespace «2610.05164v2».Calibration.Data
noncomputable section
open Set MeasureTheory Filter Real
open scoped Topology
set_option backward.isDefEq.respectTransparency false
variable (C : «2610.05164v2».Calibration.Data)

/--
Defines `reciprocalCoefficient` of type `ℝ` by `(2/3*κ*(2*C.b/κ)^(2/3:ℝ))⁻¹`.

Use: `«2610.05164v2».Calibration.Data.reciprocalCoefficient_continuousAt` uses this definition
to establish continuity at the stated point: `ContinuousAt C.reciprocalCoefficient k`.

Article: 2610.05164v2, Theorem E.1 via `«2610.05164v2».DualCertificate.Data.admissible_stable`.
-/
def reciprocalCoefficient (κ : ℝ) : ℝ := (2/3*κ*(2*C.b/κ)^(2/3:ℝ))⁻¹

/--
Continuity at the stated point: `ContinuousAt C.reciprocalCoefficient k`.

Use: `«2610.05164v2».Calibration.Data.reciprocalSpeed_L1_tendsto` uses this continuity result
to establish convergence along the specified source filter to the specified limit: `Tendsto
(fun κ => ∫ q in Ioo (0:ℝ) 2, |(C.speed κ q)⁻¹-(C.speed k q)⁻¹|) (𝓝 k) (𝓝 0)`.

Article: 2610.05164v2, Theorem E.1 via `«2610.05164v2».DualCertificate.Data.admissible_stable`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem reciprocalCoefficient_continuousAt {k : ℝ} (hk : 0 < k) :
    ContinuousAt C.reciprocalCoefficient k := by
  -- Rewrite the definitions and library identities explicitly named in the proof, then
  -- discharge the resulting algebraic or order relation.
  have hb := C.b_positive
  unfold reciprocalCoefficient
  apply ContinuousAt.inv₀
  · exact ((continuousAt_const.mul continuousAt_id).mul
      ((continuousAt_const.div continuousAt_id hk.ne').rpow_const
        (by right; norm_num)))
  · positivity

/--
Convergence along the specified source filter to the specified limit: `Tendsto (fun κ =>
(C.speed κ q)⁻¹) (𝓝 k) (𝓝 (C.speed k q)⁻¹)`.

Use: `«2610.05164v2».Calibration.Data.reciprocalSpeed_L1_tendsto` uses this limit to establish
convergence along the specified source filter to the specified limit: `Tendsto (fun κ => ∫ q in
Ioo (0:ℝ) 2, |(C.speed κ q)⁻¹-(C.speed k q)⁻¹|) (𝓝 k) (𝓝 0)`.

Article: 2610.05164v2, Theorem E.1 via
`«2610.05164v2».DualCertificate.Data.packed_value_tendsto`.

Proof: Use the identities/estimates `«2610.05164v2».Calibration.Data.amplitude_continuousOn`,
`«2610.05164v2».Calibration.Data.speed_positive` with the arguments shown in the proof.
-/
theorem reciprocalSpeed_tendsto {k q : ℝ} (hk : 0 < k) (hq : q ∈ Ioo (0:ℝ) 2) :
    Tendsto (fun κ => (C.speed κ q)⁻¹) (𝓝 k) (𝓝 (C.speed k q)⁻¹) := by
  -- Establish continuity ha before using the function at limits or in calculus arguments.
  have ha : ContinuousOn (fun κ => C.amplitude κ q) (Ioi (0:ℝ)) :=
    C.amplitude_continuousOn.comp (continuous_id.prodMk continuous_const).continuousOn
      (fun κ hκ => ⟨hκ,⟨hq.1.le,hq.2.le⟩⟩)
  have hac := ha.continuousAt (isOpen_Ioi.mem_nhds hk)
  -- Establish continuity hsc before using the function at limits or in calculus arguments.
  have hsc : ContinuousAt (fun κ => C.speed κ q) k :=
    (continuousAt_id.mul (hac.pow 2)).sub continuousAt_const
  exact (hsc.inv₀ (C.speed_positive hk hq).ne').tendsto

/--
Convergence along the specified source filter to the specified limit: `Tendsto (fun κ => ∫ q in
Ioo (0:ℝ) 2, |(C.speed κ q)⁻¹-(C.speed k q)⁻¹|) (𝓝 k) (𝓝 0)`.

Use: `«2610.05164v2».Calibration.Data.filterError_tendsto` uses this limit to establish
convergence along the specified source filter to the specified limit: `Tendsto (fun κ =>
C.filterError κ k s) (𝓝 k) (𝓝 0)`.

Article: 2610.05164v2, Theorem E.1 via
`«2610.05164v2».DualCertificate.Data.packed_value_tendsto`.

Proof: Use the identities/estimates
`«2610.05164v2».Calibration.Data.reciprocalCoefficient_continuousAt`,
`«2610.05164v2».Calibration.Data.reciprocal_integrable`,
`«2610.05164v2».Calibration.Data.reciprocal_bound` with the arguments shown in the proof.
Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation at an
arbitrary point in that intersection.
-/
theorem reciprocalSpeed_L1_tendsto {k : ℝ} (hk : 0 < k) :
    Tendsto (fun κ => ∫ q in Ioo (0:ℝ) 2, |(C.speed κ q)⁻¹-(C.speed k q)⁻¹|)
      (𝓝 k) (𝓝 0) := by
  -- Apply the dominated-convergence/Lp transfer after supplying the domination and
  -- pointwise-limit hypotheses.
  let M := C.reciprocalCoefficient k+1
  have hM : 0 ≤ M := by
    have hb := C.b_positive
    dsimp [M,reciprocalCoefficient]
    positivity
  have he : ∀ᶠ κ in 𝓝 k, 0 < κ ∧ C.reciprocalCoefficient κ ≤ M := by
    filter_upwards [isOpen_Ioi.mem_nhds hk,
      (C.reciprocalCoefficient_continuousAt hk).eventually
        (gt_mem_nhds (show C.reciprocalCoefficient k<M by dsimp [M]; linarith))] with κ hκ hb
    exact ⟨hκ,hb.le⟩
  have hmk : C.reciprocalCoefficient k ≤ M := by dsimp [M]; linarith
  have hmeas : ∀ᶠ κ in 𝓝 k, AEStronglyMeasurable
      (fun q => |(C.speed κ q)⁻¹-(C.speed k q)⁻¹|) (volume.restrict (Ioo (0:ℝ) 2)) := by
    filter_upwards [he] with κ hκ
    exact ((C.reciprocal_integrable hκ.1).aestronglyMeasurable.sub
      (C.reciprocal_integrable hk).aestronglyMeasurable).norm
  have hb : ∀ᶠ κ in 𝓝 k, ∀ᵐ q ∂volume.restrict (Ioo (0:ℝ) 2),
      ‖|(C.speed κ q)⁻¹-(C.speed k q)⁻¹|‖ ≤ 2*M*(«2610.05164v2».Calibration.Q q)^(-(2/3:ℝ)) := by
    filter_upwards [he] with κ hκ
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with q hq
    rw [Real.norm_eq_abs,abs_abs]
    have ha := C.reciprocal_bound hκ.1 hq
    have hc := C.reciprocal_bound hk hq
    have hp : 0 ≤ («2610.05164v2».Calibration.Q q)^(-(2/3:ℝ)) :=
      rpow_nonneg («2610.05164v2».Calibration.Q_positive hq).le _
    have h1 := mul_le_mul_of_nonneg_right hκ.2 hp
    have h2 := mul_le_mul_of_nonneg_right hmk hp
    change (C.speed κ q)⁻¹ ≤ C.reciprocalCoefficient κ*(«2610.05164v2».Calibration.Q q)^(-(2/3:ℝ)) at ha
    change (C.speed k q)⁻¹ ≤ C.reciprocalCoefficient k*(«2610.05164v2».Calibration.Q q)^(-(2/3:ℝ)) at hc
    calc
      _ ≤ |(C.speed κ q)⁻¹|+|(C.speed k q)⁻¹| := abs_sub _ _
      _ ≤ 2*M*(«2610.05164v2».Calibration.Q q)^(-(2/3:ℝ)) := by
        rw [abs_of_nonneg (inv_nonneg.mpr (C.speed_positive hκ.1 hq).le),
          abs_of_nonneg (inv_nonneg.mpr (C.speed_positive hk hq).le)]
        linarith
  have hl : ∀ᵐ q ∂volume.restrict (Ioo (0:ℝ) 2),
      Tendsto (fun κ => |(C.speed κ q)⁻¹-(C.speed k q)⁻¹|) (𝓝 k) (𝓝 (0:ℝ)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with q hq
    simpa only [sub_self,abs_zero] using
      ((C.reciprocalSpeed_tendsto hk hq).sub_const ((C.speed k q)⁻¹)).abs
  have h := tendsto_integral_filter_of_dominated_convergence
    (fun q => 2*M*(«2610.05164v2».Calibration.Q q)^(-(2/3:ℝ))) hmeas hb
    («2610.05164v2».Calibration.Q_negative_two_thirds_integrable.const_mul (2*M)) hl
  simpa only [integral_zero] using h

end
end «2610.05164v2».Calibration.Data

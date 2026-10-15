import «2610.05164v2».Comparison.FilterStability
import «2610.05164v2».Comparison.MassRatioContinuity

/-!
Article: 2610.05164v2, Lemma 11.
Uniform parameter stability of the actual linear comparison filter.
Use: `«2610.05164v2».Calibration.Data.linearError_tendsto` feeds
`«2610.05164v2».Calibration.Data.leftLinear_joint_continuous` (left Linear joint continuous).
Proof chain: `«2610.05164v2».DualCertificate.Data.admissible_stable` — 2610.05164v2, Theorem E.1;
Stability of strict admissibility and uniform transfer of the certificate value.
-/
namespace «2610.05164v2».Calibration.Data
noncomputable section
open Set MeasureTheory Filter Real «2610.05164v2».Calibration «2610.05164v2».Comparison «2610.05164v2».Filters
open scoped Topology
set_option backward.isDefEq.respectTransparency false
variable (C : «2610.05164v2».Calibration.Data) {κ k : ℝ} (hκ : 0 < κ) (hk : 0 < k)

/--
Continuity of the displayed function: `Continuous (C.leftLinear hκ)`.

Use: `«2610.05164v2».Calibration.Data.leftLinear_parameter_bound` uses this continuity result
to prove the bound `|C.leftLinear hκ q-C.leftLinear hk q| ≤
C.linearError κ k`.

Article: 2610.05164v2, Theorem E.1 via
`«2610.05164v2».DualCertificate.Data.packed_value_tendsto`.

Proof: Use the identities/estimates `«2610.05164v2».Filters.causal_continuous`,
`«2610.05164v2».PrescribedSpeed.SpeedData.density_integrable`,
`«2610.05164v2».PrescribedSpeed.SpeedData.X_continuous` with the arguments shown in the proof.
-/
theorem leftLinear_continuous : Continuous (C.leftLinear hκ) :=
  continuous_const.mul ((causal_continuous (by norm_num : (0:ℝ) ≤ 2)
    ((C.comparisonSpeed hκ).density_integrable hκ)).comp (C.comparisonSpeed hκ).X_continuous)

/--
Defines `linearError` of type `ℝ` by `(∫ q in Ioo (0:ℝ) 2, |C.massRatio κ q-C.massRatio k q|)+
4*(∫ q in Ioo (0:ℝ) 2, |(C.speed κ q)⁻¹-(C.speed k q)⁻¹|)`.

Use: `«2610.05164v2».Calibration.Data.linearError_tendsto` uses this definition to establish
convergence along the specified source filter to the specified limit: `Tendsto (fun κ =>
C.linearError κ k) (𝓝 k) (𝓝 0)`.

Article: 2610.05164v2, Theorem E.1 via
`«2610.05164v2».DualCertificate.Data.packed_value_tendsto`.
-/
def linearError (κ k : ℝ) : ℝ :=
  (∫ q in Ioo (0:ℝ) 2, |C.massRatio κ q-C.massRatio k q|)+
    4*(∫ q in Ioo (0:ℝ) 2, |(C.speed κ q)⁻¹-(C.speed k q)⁻¹|)

/--
The stated quantitative bound `|C.leftLinear hκ q-C.leftLinear hk q| ≤ C.linearError κ k`.

Use: `«2610.05164v2».Calibration.Data.leftLinear_joint_continuous` uses this bound to establish
continuity of the displayed function: `Continuous (fun p : Ioi (0:ℝ) × Icc (0:ℝ) 2 =>
C.leftLinear p.1.property p.2)`.

Article: 2610.05164v2, Theorem E.1 via
`«2610.05164v2».DualCertificate.Data.packed_value_tendsto`.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection.
-/
theorem leftLinear_parameter_bound {q : ℝ} (hq : q ∈ Icc (0:ℝ) 2) :
    |C.leftLinear hκ q-C.leftLinear hk q| ≤ C.linearError κ k := by
  -- Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
  -- at an arbitrary point in that intersection.
  let r := C.leftLinear hk
  let f := fun q => C.leftLinear hκ q-r q
  let c := fun q => (2)/C.speed κ q
  let e := fun q => (C.massRatio κ q-C.massRatio k q)-
    (2*r q)*((C.speed κ q)⁻¹-(C.speed k q)⁻¹)
  let B := (4:ℝ)
  let A := fun q => |C.massRatio κ q-C.massRatio k q|
  let D := fun q => |(C.speed κ q)⁻¹-(C.speed k q)⁻¹|
  -- Establish iA as the integrability justification for the later integral estimates or
  -- changes of order.
  have iA : IntegrableOn A (Ioo (0:ℝ) 2) :=
    ((C.massRatio_integrable hκ).sub (C.massRatio_integrable hk)).norm
  -- Establish iD as the integrability justification for the later integral estimates or
  -- changes of order.
  have iD : IntegrableOn D (Ioo (0:ℝ) 2) :=
    ((C.reciprocal_integrable hκ).sub (C.reciprocal_integrable hk)).norm
  have hpoly : ∀ᵐ q ∂volume.restrict (Ioo (0:ℝ) 2), ‖2*r q‖ ≤ B := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with q hq
    have hr := C.leftLinear_bounds hk ⟨hq.1.le,hq.2.le⟩
    have hb : 0 ≤ 2*r q ∧ 2*r q ≤ 4 := ⟨by dsimp [r]; linarith [hr.1],by dsimp [r]; linarith [hr.2,hq.2]⟩
    rw [Real.norm_of_nonneg hb.1]
    exact hb.2
  -- Establish iE as the integrability justification for the later integral estimates or
  -- changes of order.
  have iE : IntegrableOn e (Ioo (0:ℝ) 2) :=
    ((C.massRatio_integrable hκ).sub (C.massRatio_integrable hk)).sub
      (((C.reciprocal_integrable hκ).sub (C.reciprocal_integrable hk)).bdd_mul
        ((continuous_const.mul (C.leftLinear_continuous hk)).aestronglyMeasurable.restrict) hpoly)
  have he : IntervalIntegrable e volume 0 2 :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num : (0:ℝ) ≤ 2)).2 iE
  have hf : AbsolutelyContinuousOnInterval f 0 2 := (C.leftLinear_ac hκ).sub (C.leftLinear_ac hk)
  have h0 : f 0=0 := by dsimp [f,r]; rw [C.leftLinear_zero hκ,C.leftLinear_zero hk,sub_self]
  have hc : ∀ q ∈ Ioo (0:ℝ) 2, 0 ≤ c q := by
    intro q hq
    exact div_nonneg (by norm_num) (C.speed_positive hκ hq).le
  have hd : ∀ᵐ q, q ∈ Ioo (0:ℝ) 2 → HasDerivAt f (-c q*f q+e q) q := by
    apply Eventually.of_forall
    intro q hq
    convert (C.leftLinear_derivative hκ hq).sub (C.leftLinear_derivative hk hq) using 1
    dsimp [c,f,e,r,massRatio,amplitudeRatio]
    ring
  have hb := abs_le_integral_forcing hf he h0 hc hd hq
  have hmajor : ∀ q ∈ Ioo (0:ℝ) 2, |e q| ≤ A q+B*D q := by
    intro q hq
    have hr := C.leftLinear_bounds hk ⟨hq.1.le,hq.2.le⟩
    have hp : 0 ≤ 2*r q ∧ 2*r q ≤ B := ⟨by dsimp [r]; linarith [hr.1],by dsimp [r,B]; linarith [hr.2,hq.2]⟩
    calc
      _ ≤ |(C.massRatio κ q-C.massRatio k q)|+
        |(2*r q)*((C.speed κ q)⁻¹-(C.speed k q)⁻¹)| := abs_sub _ _
      _ ≤ A q+B*D q := by
        rw [abs_mul,abs_of_nonneg hp.1]
        exact add_le_add le_rfl (mul_le_mul_of_nonneg_right hp.2 (abs_nonneg _))
  have hle : (fun q => |e q|) ≤ᵐ[volume.restrict (Icc (0:ℝ) q)] (fun q => A q+B*D q) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc,
      ae_restrict_of_ae (show ∀ᵐ t : ℝ, t ≠ 0 ∧ t ≠ 2 by
        filter_upwards [show ∀ᵐ t : ℝ, t ≠ 0 by simp [ae_iff],
          show ∀ᵐ t : ℝ, t ≠ 2 by simp [ae_iff]] with t h0 h2
        exact ⟨h0,h2⟩)]
      with t ht hn
    exact hmajor t ⟨lt_of_le_of_ne ht.1 (Ne.symm hn.1),lt_of_le_of_ne (ht.2.trans hq.2) hn.2⟩
  have iN : IntervalIntegrable (fun q => A q+B*D q) volume 0 2 :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num : (0:ℝ) ≤ 2)).2
      (iA.add (iD.const_mul B))
  have hsub : uIcc (0:ℝ) q ⊆ uIcc (0:ℝ) 2 := by
    rw [uIcc_of_le hq.1,uIcc_of_le (by norm_num : (0:ℝ) ≤ 2)]
    exact Icc_subset_Icc le_rfl hq.2
  apply hb.trans
  apply (intervalIntegral.integral_mono_ae_restrict hq.1 (he.norm.mono_set hsub)
    (iN.mono_set hsub) hle).trans
  have hnon : 0 ≤ᵐ[volume.restrict (Ioc (0:ℝ) 2)] (fun q => A q+B*D q) :=
    Eventually.of_forall (fun q => by dsimp [A,D,B]; positivity)
  have h := intervalIntegral.integral_mono_interval le_rfl hq.1 hq.2 hnon iN
  convert h using 1
  rw [intervalIntegral.integral_add
    ((intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num : (0:ℝ) ≤ 2)).2 iA)
    ((intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num : (0:ℝ) ≤ 2)).2 (iD.const_mul B)),
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 2),
    intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 2),
    integral_Ioc_eq_integral_Ioo,integral_Ioc_eq_integral_Ioo]
  rfl

include hk in
/--
Convergence along the specified source filter to the specified limit: `Tendsto (fun κ =>
C.linearError κ k) (𝓝 k) (𝓝 0)`.

Use: `«2610.05164v2».Calibration.Data.leftLinear_joint_continuous` uses this limit to establish
continuity of the displayed function: `Continuous (fun p : Ioi (0:ℝ) × Icc (0:ℝ) 2 =>
C.leftLinear p.1.property p.2)`.

Article: 2610.05164v2, Theorem E.1 via
`«2610.05164v2».DualCertificate.Data.packed_value_tendsto`.

Proof: Use the identities/estimates `«2610.05164v2».Calibration.Data.massRatio_L1_tendsto`,
`«2610.05164v2».Calibration.Data.reciprocalSpeed_L1_tendsto` with the arguments shown in the
proof.
-/
theorem linearError_tendsto : Tendsto (fun κ => C.linearError κ k) (𝓝 k) (𝓝 0) := by
  simpa only [linearError,mul_zero,add_zero] using
    (C.massRatio_L1_tendsto hk).add ((C.reciprocalSpeed_L1_tendsto hk).const_mul 4)

end
end «2610.05164v2».Calibration.Data

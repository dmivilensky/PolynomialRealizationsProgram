import «2610.05164v2».Comparison.LeftFilters
import «2610.05164v2».Comparison.RatioContinuity
import «2610.05164v2».Comparison.DampedFlow

/-!
Article: 2610.05164v2, Lemma 11.
Uniform parameter stability of the comparison filters.
Use: `«2610.05164v2».Calibration.Data.filterError_tendsto` feeds
`«2610.05164v2».Calibration.Data.leftFilter_joint_continuous` (left Filter joint continuous).
Proof chain: `«2610.05164v2».DualCertificate.Data.admissible_stable` — 2610.05164v2, Theorem E.1;
Stability of strict admissibility and uniform transfer of the certificate value.
-/
namespace «2610.05164v2».Calibration.Data
noncomputable section
open Set MeasureTheory Filter Real «2610.05164v2».Calibration «2610.05164v2».Comparison «2610.05164v2».Filters
open scoped Topology
set_option backward.isDefEq.respectTransparency false
variable (C : «2610.05164v2».Calibration.Data) {κ k s : ℝ} (hκ : 0 < κ) (hk : 0 < k) (hs : 0 ≤ s)
include hs

/--
Continuity of the displayed function: `Continuous (C.leftFilter hκ s)`.

Use: `«2610.05164v2».Calibration.Data.leftFilter_parameter_bound` uses this continuity result
to prove the bound `|C.leftFilter hκ s q-C.leftFilter hk s q| ≤
C.filterError κ k s`.

Article: 2610.05164v2, Theorem E.1 via
`«2610.05164v2».DualCertificate.Data.packed_value_tendsto`.

Proof: Use the identities/estimates `«2610.05164v2».Filters.nonlinear_continuous`,
`«2610.05164v2».PrescribedSpeed.SpeedData.density_integrable`,
`«2610.05164v2».PrescribedSpeed.SpeedData.density_nonneg` with the arguments shown in the
proof.
-/
theorem leftFilter_continuous : Continuous (C.leftFilter hκ s) :=
  (nonlinear_continuous ((C.comparisonSpeed hκ).density_integrable hκ)
    ((C.comparisonSpeed hκ).density_nonneg hκ) hs).comp (C.comparisonSpeed hκ).X_continuous

/--
The stated quantitative bound `0 ≤ 2*C.leftFilter hk s q+(C.leftFilter hk s q)^2 ∧
2*C.leftFilter hk s q+(C.leftFilter hk s q)^2 ≤ 2*(2*s/k)+(2*s/k)^2`.

Use: `«2610.05164v2».Calibration.Data.leftFilter_parameter_bound` uses this bound to establish
the stated quantitative bound `|C.leftFilter hκ s q-C.leftFilter hk s q| ≤ C.filterError κ k
s`.

Article: 2610.05164v2, Theorem E.1 via
`«2610.05164v2».DualCertificate.Data.packed_value_tendsto`.

Proof: Use the identities/estimates `«2610.05164v2».Calibration.Data.leftFilter_bounds` with
the arguments shown in the proof.
-/
theorem leftFilter_polynomial_bound {q : ℝ} (hq : q ∈ Icc (0:ℝ) 2) :
    0 ≤ 2*C.leftFilter hk s q+(C.leftFilter hk s q)^2 ∧
    2*C.leftFilter hk s q+(C.leftFilter hk s q)^2 ≤ 2*(2*s/k)+(2*s/k)^2 := by
  -- Use the identities/estimates `«2610.05164v2».Calibration.Data.leftFilter_bounds` with the
  -- arguments shown in the proof.
  have hb := C.leftFilter_bounds hk hs hq
  have hr : C.leftFilter hk s q ≤ 2*s/k := by
    have h := mul_le_mul_of_nonneg_left hq.2 (div_nonneg hs hk.le)
    calc
      _ ≤ s/k*q := hb.2
      _ ≤ s/k*2 := h
      _ = 2*s/k := by ring
  exact ⟨add_nonneg (mul_nonneg (by norm_num) hb.1) (sq_nonneg _),add_le_add (mul_le_mul_of_nonneg_left hr (by norm_num))
    (pow_le_pow_left₀ hb.1 hr 2)⟩

/--
Defines `filterError` of type `ℝ` by `s*(∫ q in Ioo (0:ℝ) 2, |C.amplitudeRatio κ
q-C.amplitudeRatio k q|)+ (2*(2*s/k)+(2*s/k)^2)*(∫ q in Ioo (0:ℝ) 2, |(C.speed κ q)⁻¹-(C.speed
k q)⁻¹|)`.

Use: `«2610.05164v2».Calibration.Data.filterError_tendsto` uses this definition to establish
convergence along the specified source filter to the specified limit: `Tendsto (fun κ =>
C.filterError κ k s) (𝓝 k) (𝓝 0)`.

Article: 2610.05164v2, Theorem E.1 via
`«2610.05164v2».DualCertificate.Data.packed_value_tendsto`.
-/
def filterError (κ k s : ℝ) : ℝ :=
  s*(∫ q in Ioo (0:ℝ) 2, |C.amplitudeRatio κ q-C.amplitudeRatio k q|)+
    (2*(2*s/k)+(2*s/k)^2)*(∫ q in Ioo (0:ℝ) 2, |(C.speed κ q)⁻¹-(C.speed k q)⁻¹|)

/--
The stated quantitative bound `|C.leftFilter hκ s q-C.leftFilter hk s q| ≤ C.filterError κ k
s`.

Use: `«2610.05164v2».Calibration.Data.leftFilter_joint_continuous` uses this bound to establish
continuity of the displayed function: `Continuous (fun p : Ioi (0:ℝ) × Icc (0:ℝ) 2 =>
C.leftFilter p.1.property s p.2)`.

Article: 2610.05164v2, Theorem E.1 via
`«2610.05164v2».DualCertificate.Data.packed_value_tendsto`.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection.
-/
theorem leftFilter_parameter_bound {q : ℝ} (hq : q ∈ Icc (0:ℝ) 2) :
    |C.leftFilter hκ s q-C.leftFilter hk s q| ≤ C.filterError κ k s := by
  -- Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
  -- at an arbitrary point in that intersection.
  let r := C.leftFilter hk s
  let f := fun q => C.leftFilter hκ s q-r q
  let c := fun q => (2+C.leftFilter hκ s q+r q)/C.speed κ q
  let e := fun q => s*(C.amplitudeRatio κ q-C.amplitudeRatio k q)-
    (2*r q+(r q)^2)*((C.speed κ q)⁻¹-(C.speed k q)⁻¹)
  let B := 2*(2*s/k)+(2*s/k)^2
  let A := fun q => |C.amplitudeRatio κ q-C.amplitudeRatio k q|
  let D := fun q => |(C.speed κ q)⁻¹-(C.speed k q)⁻¹|
  -- Establish iA as the integrability justification for the later integral estimates or
  -- changes of order.
  have iA : IntegrableOn A (Ioo (0:ℝ) 2) :=
    ((C.amplitudeRatio_integrable hκ).sub (C.amplitudeRatio_integrable hk)).norm
  -- Establish iD as the integrability justification for the later integral estimates or
  -- changes of order.
  have iD : IntegrableOn D (Ioo (0:ℝ) 2) :=
    ((C.reciprocal_integrable hκ).sub (C.reciprocal_integrable hk)).norm
  have hpoly : ∀ᵐ q ∂volume.restrict (Ioo (0:ℝ) 2), ‖2*r q+(r q)^2‖ ≤ B := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with q hq
    have hb := C.leftFilter_polynomial_bound hk hs ⟨hq.1.le,hq.2.le⟩
    rw [Real.norm_of_nonneg hb.1]
    exact hb.2
  -- Establish iE as the integrability justification for the later integral estimates or
  -- changes of order.
  have iE : IntegrableOn e (Ioo (0:ℝ) 2) :=
    (((C.amplitudeRatio_integrable hκ).sub (C.amplitudeRatio_integrable hk)).const_mul s).sub
      (((C.reciprocal_integrable hκ).sub (C.reciprocal_integrable hk)).bdd_mul
        (((continuous_const.mul (C.leftFilter_continuous hk hs)).add
          ((C.leftFilter_continuous hk hs).pow 2)).aestronglyMeasurable.restrict) hpoly)
  have he : IntervalIntegrable e volume 0 2 :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num : (0:ℝ) ≤ 2)).2 iE
  have hf : AbsolutelyContinuousOnInterval f 0 2 := (C.leftFilter_ac hκ hs).sub (C.leftFilter_ac hk hs)
  have h0 : f 0=0 := by dsimp [f,r]; rw [C.leftFilter_zero hκ hs,C.leftFilter_zero hk hs,sub_self]
  have hc : ∀ q ∈ Ioo (0:ℝ) 2, 0 ≤ c q := by
    intro q hq
    exact div_nonneg (by
      have h1 := (C.leftFilter_bounds hκ hs ⟨hq.1.le,hq.2.le⟩).1
      have h2 := (C.leftFilter_bounds hk hs ⟨hq.1.le,hq.2.le⟩).1
      dsimp [r]; linarith) (C.speed_positive hκ hq).le
  have hd : ∀ᵐ q, q ∈ Ioo (0:ℝ) 2 → HasDerivAt f (-c q*f q+e q) q := by
    apply Eventually.of_forall
    intro q hq
    convert (C.leftFilter_derivative hκ hs hq).sub (C.leftFilter_derivative hk hs hq) using 1
    dsimp [c,f,e,r,amplitudeRatio]
    ring
  have hb := abs_le_integral_forcing hf he h0 hc hd hq
  have hmajor : ∀ q ∈ Ioo (0:ℝ) 2, |e q| ≤ s*A q+B*D q := by
    intro q hq
    have hp := C.leftFilter_polynomial_bound hk hs ⟨hq.1.le,hq.2.le⟩
    calc
      _ ≤ |s*(C.amplitudeRatio κ q-C.amplitudeRatio k q)|+
        |(2*r q+(r q)^2)*((C.speed κ q)⁻¹-(C.speed k q)⁻¹)| := abs_sub _ _
      _ ≤ s*A q+B*D q := by
        rw [abs_mul,abs_of_nonneg hs,abs_mul,abs_of_nonneg hp.1]
        exact add_le_add le_rfl (mul_le_mul_of_nonneg_right hp.2 (abs_nonneg _))
  have hle : (fun q => |e q|) ≤ᵐ[volume.restrict (Icc (0:ℝ) q)] (fun q => s*A q+B*D q) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc,
      ae_restrict_of_ae (show ∀ᵐ t : ℝ, t ≠ 0 ∧ t ≠ 2 by
        filter_upwards [show ∀ᵐ t : ℝ, t ≠ 0 by simp [ae_iff],
          show ∀ᵐ t : ℝ, t ≠ 2 by simp [ae_iff]] with t h0 h2
        exact ⟨h0,h2⟩)]
      with t ht hn
    exact hmajor t ⟨lt_of_le_of_ne ht.1 (Ne.symm hn.1),lt_of_le_of_ne (ht.2.trans hq.2) hn.2⟩
  have iN : IntervalIntegrable (fun q => s*A q+B*D q) volume 0 2 :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num : (0:ℝ) ≤ 2)).2
      ((iA.const_mul s).add (iD.const_mul B))
  have hsub : uIcc (0:ℝ) q ⊆ uIcc (0:ℝ) 2 := by
    rw [uIcc_of_le hq.1,uIcc_of_le (by norm_num : (0:ℝ) ≤ 2)]
    exact Icc_subset_Icc le_rfl hq.2
  apply hb.trans
  apply (intervalIntegral.integral_mono_ae_restrict hq.1 (he.norm.mono_set hsub)
    (iN.mono_set hsub) hle).trans
  have hnon : 0 ≤ᵐ[volume.restrict (Ioc (0:ℝ) 2)] (fun q => s*A q+B*D q) :=
    Eventually.of_forall (fun q => by dsimp [A,D,B]; positivity)
  have h := intervalIntegral.integral_mono_interval le_rfl hq.1 hq.2 hnon iN
  convert h using 1
  rw [intervalIntegral.integral_add
    ((intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num : (0:ℝ) ≤ 2)).2 (iA.const_mul s))
    ((intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num : (0:ℝ) ≤ 2)).2 (iD.const_mul B)),
    intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul,
    intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 2),
    intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 2),
    integral_Ioc_eq_integral_Ioo,integral_Ioc_eq_integral_Ioo]
  rfl

include hk in
omit hs in
/--
Convergence along the specified source filter to the specified limit: `Tendsto (fun κ =>
C.filterError κ k s) (𝓝 k) (𝓝 0)`.

Use: `«2610.05164v2».Calibration.Data.leftFilter_joint_continuous` uses this limit to establish
continuity of the displayed function: `Continuous (fun p : Ioi (0:ℝ) × Icc (0:ℝ) 2 =>
C.leftFilter p.1.property s p.2)`.

Article: 2610.05164v2, Theorem E.1 via
`«2610.05164v2».DualCertificate.Data.packed_value_tendsto`.

Proof: Use the identities/estimates
`«2610.05164v2».Calibration.Data.amplitudeRatio_L1_tendsto`,
`«2610.05164v2».Calibration.Data.reciprocalSpeed_L1_tendsto` with the arguments shown in the
proof.
-/
theorem filterError_tendsto : Tendsto (fun κ => C.filterError κ k s) (𝓝 k) (𝓝 0) := by
  simpa only [filterError,mul_zero,add_zero] using
    ((C.amplitudeRatio_L1_tendsto hk).const_mul s).add
      ((C.reciprocalSpeed_L1_tendsto hk).const_mul (2*(2*s/k)+(2*s/k)^2))

end
end «2610.05164v2».Calibration.Data

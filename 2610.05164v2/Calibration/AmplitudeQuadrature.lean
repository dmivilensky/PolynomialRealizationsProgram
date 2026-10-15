import «2610.05164v2».Comparison.Symmetry
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
Article: 2610.05164v2, Section 4.1.
Amplitude Quadrature.
Use: `«2610.05164v2».Calibration.Data.amplitude_integral_cubic` feeds
`«2610.05164v2».Certificates.Compact.AmplitudeValues.integral_cubic` (integral cubic).
Proof chain: `«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement` —
2610.05164v2, Theorem 1.2, factor 1.000013; Unconditional uniform gain comparison with the retained
numerical factor.
-/
namespace «2610.05164v2».Calibration.Data
noncomputable section
open Set MeasureTheory
set_option autoImplicit false

/--
The precise assertion is `(∫ q in (0:ℝ)..2,C.amplitude κ q)= ∫ t in (0:ℝ)..1,6*t^2*C.amplitude
κ (t^3)`.

Use: `«2610.05164v2».Certificates.Compact.AmplitudeValues.integral_cubic` uses this identity to
establish the precise assertion is `(∫ q in (0:ℝ)..2,calibration.amplitude (Real.pi^2/4) q)= ∫
t in (0:ℝ)..1,integrand t`.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.

Proof: Use the identities/estimates
`«2610.05164v2».Calibration.Data.amplitude_continuousOn_fixed`,
`«2610.05164v2».Calibration.Data.amplitude_reflection` with the arguments shown in the proof.
-/
theorem amplitude_integral_cubic (C : Data) {κ : ℝ} (hκ : 0<κ)
    (hΓ : ∀ q∈Icc (0:ℝ) 2,C.Gamma (2-q)=C.Gamma q) :
    (∫ q in (0:ℝ)..2,C.amplitude κ q)=
      ∫ t in (0:ℝ)..1,6*t^2*C.amplitude κ (t^3) := by
  -- Use the identities/estimates
  -- `«2610.05164v2».Calibration.Data.amplitude_continuousOn_fixed`,
  -- `«2610.05164v2».Calibration.Data.amplitude_reflection` with the arguments shown in the
  -- proof.
  have hc := C.amplitude_continuousOn_fixed hκ
  have hi : IntervalIntegrable (C.amplitude κ) volume 0 2 :=
    ContinuousOn.intervalIntegrable (by
      simpa only [uIcc_of_le (by norm_num : (0:ℝ)≤2)] using hc)
  have hl : IntervalIntegrable (C.amplitude κ) volume 0 1 :=
    hi.mono_set (by
      simp only [uIcc_of_le (by norm_num : (0:ℝ)≤1),
        uIcc_of_le (by norm_num : (0:ℝ)≤2)]
      intro q hq
      exact ⟨hq.1,hq.2.trans (by norm_num)⟩)
  have hr : IntervalIntegrable (C.amplitude κ) volume 1 2 :=
    hi.mono_set (by
      simp only [uIcc_of_le (by norm_num : (1:ℝ)≤2),
        uIcc_of_le (by norm_num : (0:ℝ)≤2)]
      intro q hq
      exact ⟨(by norm_num : (0:ℝ)≤1).trans hq.1,hq.2⟩)
  have href := intervalIntegral.integral_comp_sub_left
    (a := (0:ℝ)) (b := 1) (C.amplitude κ) 2
  have he : (∫ q in (0:ℝ)..1,C.amplitude κ (2-q))=
      ∫ q in (0:ℝ)..1,C.amplitude κ q := by
    apply intervalIntegral.integral_congr
    intro q _
    exact C.amplitude_reflection hκ hΓ q
  rw [he] at href
  norm_num only [sub_zero,show (2:ℝ)-1=1 by norm_num] at href
  have hcubic := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
    (f := fun t : ℝ => t^3) (f' := fun t => 3*t^2)
    (g := C.amplitude κ) (a := 0) (b := 1)
    (by fun_prop)
    (fun t _ => by convert! (hasDerivAt_id t).pow 3 using 1; norm_num)
    (fun t _ => by positivity)
  norm_num only [zero_pow (by decide : 3≠0),one_pow] at hcubic
  -- Establish continuity hcc before using the function at limits or in calculus arguments.
  have hcc : ContinuousOn (fun t : ℝ => C.amplitude κ (t^3)*(3*t^2))
      (Icc (0:ℝ) 1) :=
    (hc.comp (continuous_pow 3).continuousOn (by
      intro t ht
      exact ⟨pow_nonneg ht.1 3,(pow_le_one₀ ht.1 ht.2).trans (by norm_num)⟩)).mul
      ((continuous_const.mul (continuous_id.pow 2)).continuousOn)
  have hci : IntervalIntegrable (fun t : ℝ => C.amplitude κ (t^3)*(3*t^2)) volume 0 1 :=
    ContinuousOn.intervalIntegrable (by simpa only [uIcc_of_le zero_le_one] using hcc)
  rw [← intervalIntegral.integral_add_adjacent_intervals hl hr,← href,← hcubic]
  simp only [Function.comp_def]
  rw [← intervalIntegral.integral_add hci hci]
  apply intervalIntegral.integral_congr
  intro t _
  ring

end
end «2610.05164v2».Calibration.Data

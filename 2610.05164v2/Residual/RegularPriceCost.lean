import «2610.05164v2».Calibration.Reciprocal
import «2610.05164v2».Residual.Price

/-!
Article: 2610.05164v2, Lemma 16.
Theorem 3.5, equation (26), for the constructed comparison density.
Use: `«2610.05164v2».Calibration.Data.regularPrice_cost` feeds
`«2610.05164v2».Calibration.Data.regularPriceData_cost` (regular Price Data cost).
Proof chain: `«2610.05164v2».DualCertificate.Data.uniform_finite_lower_bound` — 2610.05164v2,
Theorem E.1; Stability of strict admissibility and uniform transfer of the certificate value.
-/
namespace «2610.05164v2».Calibration.Data
noncomputable section
open Set MeasureTheory Real «2610.05164v2».PrescribedSpeed «2610.05164v2».Residual
set_option backward.isDefEq.respectTransparency false
variable (C : «2610.05164v2».Calibration.Data) {κ : ℝ} (hκ : 0 < κ)
include hκ

/--
Exact identity `(∫ x, C.comparisonDensity hκ x)=∫ q in Ioo (0:ℝ) 2, (C.amplitude κ q)^2/C.speed
κ q`.

Use: `«2610.05164v2».Calibration.Data.Q_div_speed_mass` uses this identity to establish the
precise assertion is `(∫ q in Ioo (0:ℝ) 2, «2610.05164v2».Calibration.Q q/C.speed κ q)= κ*(∫ x,
C.comparisonDensity hκ x)-2`.

Article: 2610.05164v2, Theorem E.1 via
`«2610.05164v2».DualCertificate.Data.packed_value_tendsto`.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem comparisonDensity_mass :
    (∫ x, C.comparisonDensity hκ x)=∫ q in Ioo (0:ℝ) 2, (C.amplitude κ q)^2/C.speed κ q := by
  -- Clear the denominators using the available nonzero hypotheses, then verify the remaining
  -- algebraic identity.
  have h := (C.comparisonSpeed hκ).density_moment (κ := κ) (r := 1) (by norm_num)
  simp only [rpow_one] at h
  convert h using 1
  · rfl
  · apply setIntegral_congr_fun measurableSet_Ioo
    intro q hq
    change (C.amplitude κ q)^2/C.speed κ q=
      ((C.speed κ q+q*(2-q))/κ)/C.speed κ q
    unfold speed «2610.05164v2».Calibration.Q
    field_simp
    ring

/--
Integrability on the stated domain: `IntegrableOn (fun q => (C.amplitude κ q)^2/C.speed κ q)
(Ioo (0:ℝ) 2)`.

Use: `«2610.05164v2».Calibration.Data.Q_div_speed_integrable` uses this integrability result to
establish integrability on the stated domain: `IntegrableOn (fun q =>
«2610.05164v2».Calibration.Q q/C.speed κ q) (Ioo (0:ℝ) 2)`.

Article: 2610.05164v2, Theorem E.1 via
`«2610.05164v2».DualCertificate.Data.packed_value_tendsto`.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection. Clear the denominators using the available nonzero
hypotheses, then verify the remaining algebraic identity.
-/
theorem amplitude_square_div_speed_integrable :
    IntegrableOn (fun q => (C.amplitude κ q)^2/C.speed κ q) (Ioo (0:ℝ) 2) := by
  -- Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
  -- at an arbitrary point in that intersection.
  have h := (C.comparisonSpeed hκ).density_moment_rhs_integrable hκ (r := 1) (by norm_num)
  simp only [rpow_one] at h
  apply h.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with q hq
  change ((C.speed κ q+q*(2-q))/κ)/C.speed κ q=(C.amplitude κ q)^2/C.speed κ q
  unfold speed «2610.05164v2».Calibration.Q
  field_simp
  ring

/--
Integrability on the stated domain: `IntegrableOn (fun q => «2610.05164v2».Calibration.Q
q/C.speed κ q) (Ioo (0:ℝ) 2)`.

Use: `«2610.05164v2».Calibration.Data.regularPrice_cost` rewrites with this integrability
result to establish `priceCost κ τ (C.regularPrice (κ := κ) τ e)= (∫ q
in Ioo (0:ℝ) 2, C.amplitude κ q*e q)/κ+ τ*(1-∫ x, C.comparisonDensity hκ x)`.

Article: 2610.05164v2, Theorem E.1 via
`«2610.05164v2».DualCertificate.Data.packed_value_tendsto`.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection. Clear the denominators using the available nonzero
hypotheses, then verify the remaining algebraic identity.
-/
theorem Q_div_speed_integrable : IntegrableOn (fun q => «2610.05164v2».Calibration.Q q/C.speed κ q)
    (Ioo (0:ℝ) 2) := by
  -- Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
  -- at an arbitrary point in that intersection.
  apply (((C.amplitude_square_div_speed_integrable hκ).const_mul κ).sub
    (integrableOn_const (C := (1:ℝ)) (s := Ioo (0:ℝ) 2) (by rw [volume_Ioo]; exact ENNReal.ofReal_ne_top))).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with q hq
  change κ*((C.amplitude κ q)^2/C.speed κ q)-1=«2610.05164v2».Calibration.Q q/C.speed κ q
  field_simp [(C.speed_positive hκ hq).ne']
  unfold speed
  ring

/--
The precise assertion is `(∫ q in Ioo (0:ℝ) 2, «2610.05164v2».Calibration.Q q/C.speed κ q)=
κ*(∫ x, C.comparisonDensity hκ x)-2`.

Use: `«2610.05164v2».Calibration.Data.regularPrice_cost` rewrites with this identity to
establish the precise assertion is `priceCost κ τ (C.regularPrice (κ := κ) τ e)= (∫ q in Ioo
(0:ℝ) 2, C.amplitude κ q*e q)/κ+ τ*(1-∫ x, C.comparisonDensity hκ x)`.

Article: 2610.05164v2, Theorem E.1 via
`«2610.05164v2».DualCertificate.Data.packed_value_tendsto`.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem Q_div_speed_mass :
    (∫ q in Ioo (0:ℝ) 2, «2610.05164v2».Calibration.Q q/C.speed κ q)=
      κ*(∫ x, C.comparisonDensity hκ x)-2 := by
  -- Clear the denominators using the available nonzero hypotheses, then verify the remaining
  -- algebraic identity.
  have he : (∫ q in Ioo (0:ℝ) 2, «2610.05164v2».Calibration.Q q/C.speed κ q)=
      ∫ q in Ioo (0:ℝ) 2, κ*((C.amplitude κ q)^2/C.speed κ q)-1 := by
    apply setIntegral_congr_fun measurableSet_Ioo
    intro q hq
    field_simp [(C.speed_positive hκ hq).ne']
    unfold speed
    ring
  rw [he,integral_sub ((C.amplitude_square_div_speed_integrable hκ).const_mul κ)
    (integrableOn_const (C := (1:ℝ)) (s := Ioo (0:ℝ) 2) (by rw [volume_Ioo]; exact ENNReal.ofReal_ne_top)),integral_const_mul,
    ← C.comparisonDensity_mass hκ]
  simp

/--
Defines `regularPrice` of type `ℝ → ℝ` by `(Ioo (0:ℝ) 2).indicator (fun q =>
-τ*«2610.05164v2».Calibration.Q q/C.speed κ q+C.amplitude κ q*e q)`.

Use: `«2610.05164v2».Calibration.Data.regularPrice_cost` uses this definition to establish the
precise assertion is `priceCost κ τ (C.regularPrice (κ := κ) τ e)= (∫ q in Ioo (0:ℝ) 2,
C.amplitude κ q*e q)/κ+ τ*(1-∫ x, C.comparisonDensity hκ x)`.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.
-/
def regularPrice (τ : ℝ) (e : ℝ → ℝ) : ℝ → ℝ :=
  (Ioo (0:ℝ) 2).indicator (fun q => -τ*«2610.05164v2».Calibration.Q q/C.speed κ q+C.amplitude κ q*e q)

/--
No normalization of the comparison density is inserted: its actual mass is the correction
appearing in the published price cost.

The precise assertion is `priceCost κ τ (C.regularPrice (κ := κ) τ e)= (∫ q in Ioo (0:ℝ) 2,
C.amplitude κ q*e q)/κ+ τ*(1-∫ x, C.comparisonDensity hκ x)`.

Use: `«2610.05164v2».Calibration.Data.regularPriceData_cost` uses this identity to establish
the precise assertion is `priceCost κ τ (C.regularPriceData hκ τ e).value= (∫ q in Ioo (0:ℝ) 2,
C.amplitude κ q*e.value q)/κ+ τ*(1-∫ x, C.comparisonDensity hκ x)`.

Article: 2610.05164v2, Theorem E.1 via
`«2610.05164v2».DualCertificate.Data.packed_value_tendsto`.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem regularPrice_cost (τ : ℝ) (e : ℝ → ℝ)
    (he : IntegrableOn (fun q => C.amplitude κ q*e q) (Ioo (0:ℝ) 2)) :
    priceCost κ τ (C.regularPrice (κ := κ) τ e)=
      (∫ q in Ioo (0:ℝ) 2, C.amplitude κ q*e q)/κ+
        τ*(1-∫ x, C.comparisonDensity hκ x) := by
  -- Clear the denominators using the available nonzero hypotheses, then verify the remaining
  -- algebraic identity.
  unfold priceCost regularPrice
  rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 2),
    integral_Ioc_eq_integral_Ioo]
  have hid : (∫ q in Ioo (0:ℝ) 2, (Ioo (0:ℝ) 2).indicator
      (fun q => -τ*«2610.05164v2».Calibration.Q q/C.speed κ q+C.amplitude κ q*e q) q)=
      ∫ q in Ioo (0:ℝ) 2, -τ*(«2610.05164v2».Calibration.Q q/C.speed κ q)+C.amplitude κ q*e q := by
    apply setIntegral_congr_fun measurableSet_Ioo
    intro q hq
    rw [indicator_of_mem hq]
    ring
  rw [hid,integral_add ((C.Q_div_speed_integrable hκ).const_mul (-τ)) he,integral_const_mul,
    C.Q_div_speed_mass hκ]
  field_simp [hκ.ne']
  ring

end
end «2610.05164v2».Calibration.Data

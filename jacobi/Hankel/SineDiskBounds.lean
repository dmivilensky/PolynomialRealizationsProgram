import jacobi.Hankel.FrequencySine
import jacobi.Complex.TrigonometricRemainders

/-!
Article: jacobi, Lemma E.1.
All bounds concern the displayed rational comparison and standard
complex trigonometric functions. The Bessel cubic remainder is
added separately, before the actual simple-zero theorem is applied.
Use: frequencySineSlope_close retains a strict margin for the true Bessel zero-disk contraction.
-/
namespace jacobi.Hankel
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- The original complex cosine differs from one by at most one eighth throughout the genuine radius-one-quarter disk.
Use: frequencySineSlope_close retains a strict margin for the true Bessel zero-disk contraction.
Article: jacobi, Lemma E.1.
Source: Mathlib Complex.cos_bound, the Taylor remainder through degree two.
Proof: add the actual quadratic Taylor term to the community quartic remainder and evaluate its genuine radius-one-quarter majorant. -/
theorem cosine_quarter_disk {ζ : ℂ} (hζ : ‖ζ‖≤1/4) : ‖Complex.cos ζ-1‖≤1/8 := by
  -- The small numerical constant is proved for the genuine complex cosine on the entire disk.
  have hh := Complex.cos_bound (hζ.trans (by norm_num : (1/4:ℝ)≤1))
  have he : Complex.cos ζ-1=(Complex.cos ζ-(1-ζ^2/2))-(ζ^2/2) := by ring
  rw [he]
  apply (norm_sub_le _ _).trans
  have hterm : ‖ζ^2/(2:ℂ)‖=‖ζ‖^2/2 := by rw [norm_div,norm_pow]; norm_num
  rw [hterm]
  have hsq : ‖ζ‖^2≤(1/4:ℝ)^2 := pow_le_pow_left₀ (norm_nonneg _) hζ 2
  have hfour : ‖ζ‖^4≤(1/4:ℝ)^4 := pow_le_pow_left₀ (norm_nonneg _) hζ 4
  nlinarith

/-- The original sine and cosine have norm at most two on the entire genuine radius-one-quarter frequency disk.
Use: frequencySineSlope_close bounds every true rational perturbation uniformly on the same disk.
Article: jacobi, Lemma E.1.
Proof: the proved actual cosine increment bounds its norm by nine eighths. The actual sine is bounded by integrating that same derivative along the segment from zero, giving at most twice the genuine displacement. -/
theorem trigonometric_quarter_disk {ζ : ℂ} (hζ : ‖ζ‖≤1/4) :
    ‖Complex.sin ζ‖≤2 ∧ ‖Complex.cos ζ‖≤2 := by
  -- The same actual closed disk bounds the sine derivative throughout the mean-value segment.
  have hcos (z : ℂ) (hz : ‖z‖≤1/4) : ‖Complex.cos z‖≤2 := by
    have hh := norm_le_norm_sub_add (Complex.cos z) 1
    rw [norm_one] at hh
    linarith [cosine_quarter_disk hz]
  have hh := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (𝕜 := ℂ)
    (f := Complex.sin) (f' := Complex.cos) (C := 2)
    (fun z _ => (Complex.hasDerivAt_sin z).hasDerivWithinAt)
    (fun z hz => hcos z (by simpa only [Metric.mem_closedBall,dist_zero_right] using hz))
    (convex_closedBall (0:ℂ) (1/4))
    (by simp : (0:ℂ)∈Metric.closedBall (0:ℂ) (1/4))
    (by simpa only [Metric.mem_closedBall,dist_zero_right] using hζ)
  simp only [Complex.sin_zero,sub_zero] at hh
  exact ⟨hh.trans (by linarith),hcos ζ hζ⟩

/-- A genuine inverse-frequency coefficient has a uniform inverse-real-frequency bound, including every positive integer denominator power.
Use: frequencySineSlope_close bounds all original rational derivative perturbations by one common inverse-frequency majorant.
Article: jacobi, Lemma E.1.
Proof: the true frequency norm is at least x>=1, so its every positive integer power is also at least x; apply the exact complex quotient norm identity. -/
theorem frequency_quotient_bound {c z : ℂ} {A x p : ℝ} (hc : ‖c‖≤A)
    (hx : 1≤x) (hz : x≤‖z‖) (hp : 0<p) {n : ℕ} (hn : n≠0) :
    ‖c/((p:ℂ)*z^n)‖≤A/(p*x) := by
  have hpower : x≤‖z‖^n := hz.trans (le_self_pow₀ (hx.trans hz) hn)
  have hxp : 0<x := lt_of_lt_of_le zero_lt_one hx
  have hA : 0≤A := (norm_nonneg _).trans hc
  rw [norm_div,norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hp]
  exact (div_le_div_of_nonneg_left (norm_nonneg c) (mul_pos hp hxp)
    (mul_le_mul_of_nonneg_left hpower hp.le)).trans (div_le_div_of_nonneg_right hc (by positivity))

/-- The exact original Hankel sine derivative differs from one by an explicit strict-margin disk constant plus a uniform inverse-frequency term.
Use: the actual Bessel zero equation contracts once its independently proved cubic derivative error is added and the original frequency index exceeds one common cutoff.
Article: jacobi, Lemma E.1.
Proof: isolate cos(zeta)-1 and the four actual rational correction terms. The original sine and cosine have norm at most two, the genuine polynomial coefficient has norm at most B*(B+2), and every actual inverse frequency power is at most the same inverse x. -/
theorem frequencySineSlope_close {c q ζ : ℂ} {B x : ℝ} (hB : 0≤B) (hc : ‖c‖≤B)
    (hx : 1≤x) (hz : x≤‖q+ζ‖) (hζ : ‖ζ‖≤1/4) :
    ‖frequencySineSlope c q ζ-1‖≤1/8+(3*B*(B+2)/4+2*B)/x := by
  -- The actual derivative is written as the unit derivative plus its five genuinely bounded errors.
  have hpoly : ‖c*(c+2)‖≤B*(B+2) := by
    rw [norm_mul]
    have h2 : ‖c+2‖≤B+2 := (norm_add_le _ _).trans (by norm_num; exact hc)
    exact mul_le_mul hc h2 (norm_nonneg _) hB
  have h8 := frequency_quotient_bound hpoly hx hz (by norm_num : (0:ℝ)<8) (n := 2) (by norm_num)
  have h4 := frequency_quotient_bound hpoly hx hz (by norm_num : (0:ℝ)<4) (n := 3) (by norm_num)
  have h22 := frequency_quotient_bound hc hx hz (by norm_num : (0:ℝ)<2) (n := 2) (by norm_num)
  have h21 := frequency_quotient_bound hc hx hz (by norm_num : (0:ℝ)<2) (n := 1) (by norm_num)
  simp only [pow_one] at h21
  obtain ⟨hs,hcos⟩ := trigonometric_quarter_disk hζ
  have he : frequencySineSlope c q ζ-1=(Complex.cos ζ-1)-
      c*(c+2)/(8*(q+ζ)^2)*Complex.cos ζ+
      c*(c+2)/(4*(q+ζ)^3)*Complex.sin ζ+
      c/(2*(q+ζ)^2)*Complex.cos ζ+c/(2*(q+ζ))*Complex.sin ζ := by
    unfold frequencySineSlope
    ring
  have hb8 : ‖c*(c+2)/(8*(q+ζ)^2)*Complex.cos ζ‖≤B*(B+2)/(8*x)*2 := by
    rw [norm_mul]
    exact mul_le_mul h8 hcos (norm_nonneg _) (by positivity)
  have hb4 : ‖c*(c+2)/(4*(q+ζ)^3)*Complex.sin ζ‖≤B*(B+2)/(4*x)*2 := by
    rw [norm_mul]
    exact mul_le_mul h4 hs (norm_nonneg _) (by positivity)
  have hb22 : ‖c/(2*(q+ζ)^2)*Complex.cos ζ‖≤B/(2*x)*2 := by
    rw [norm_mul]
    exact mul_le_mul h22 hcos (norm_nonneg _) (by positivity)
  have hb21 : ‖c/(2*(q+ζ))*Complex.sin ζ‖≤B/(2*x)*2 := by
    rw [norm_mul]
    exact mul_le_mul h21 hs (norm_nonneg _) (by positivity)
  rw [he]
  exact ((norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans
    (add_le_add ((norm_add_le _ _).trans (add_le_add ((norm_sub_le _ _).trans
      (add_le_add (cosine_quarter_disk hζ) hb8)) hb4)) hb22)) hb21)).trans_eq (by ring)

end
end jacobi.Hankel

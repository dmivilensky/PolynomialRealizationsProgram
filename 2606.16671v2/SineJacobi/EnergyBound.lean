import «2606.16671v2».SineJacobi.ProfileEnergy
import «2606.16671v2».SineJacobi.EllipticBound
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
Article: 2606.16671v2, Theorem 5.2.
A purely analytic certificate sufficient for the strict comparison with the prefix method.
Use: `«2606.16671v2».SineJacobi.sineEnergy_lt_four_thirds` feeds
`«2606.16671v2».SineJacobi.leading_constant_lt_prefix` (leading constant lt prefix).
-/
namespace «2606.16671v2».SineJacobi
noncomputable section
open Real Set MeasureTheory

/--
The stated quantitative bound `sineProfile t^2 ≤ (2/Real.pi)*sin (Real.pi*t/2)`.

Use: `«2606.16671v2».SineJacobi.sineDensity_square_bound` uses this bound to establish the
stated quantitative bound `sineDensity t^2 ≤ 2*sin (Real.pi*t)`.

Article: 2606.16671v2, Theorem 5.2 via `«2606.16671v2».SineJacobi.sineEnergy_le_four_div_pi`.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem sineProfile_square_bound {t : ℝ} (ht : t ∈ Ioo (0:ℝ) 1) :
    sineProfile t^2 ≤ (2/Real.pi)*sin (Real.pi*t/2) := by
  -- Clear the denominators using the available nonzero hypotheses, then verify the remaining
  -- algebraic identity.
  have hsin := sin_pos_of_mem_Ioo
    (show Real.pi*t ∈ Ioo (0:ℝ) Real.pi from
      ⟨mul_pos pi_pos ht.1, by nlinarith [pi_pos, ht.2]⟩)
  have hcos : 0 < cos (Real.pi*t/2) := cos_pos_of_mem_Ioo
    ⟨by nlinarith [pi_pos, ht.1], by nlinarith [pi_pos, ht.2]⟩
  have hK := ellipticK_square_bound (profileModulus_lt_one ht)
  change ellipticK (sin (Real.pi*t/2))^2 ≤
    Real.pi^2/(4*sqrt (1-sin (Real.pi*t/2)^2)) at hK
  have hroot : sqrt (1-sin (Real.pi*t/2)^2) = cos (Real.pi*t/2) := by
    rw [show 1-sin (Real.pi*t/2)^2 = cos (Real.pi*t/2)^2 by
      nlinarith [sin_sq_add_cos_sq (Real.pi*t/2)], sqrt_sq hcos.le]
  rw [hroot] at hK
  have hs : sin (Real.pi*t) = 2*sin (Real.pi*t/2)*cos (Real.pi*t/2) := by
    rw [← sin_two_mul]
    congr 1; ring
  calc
    _ = (2/(Real.pi*sqrt Real.pi))^2*sin (Real.pi*t)*ellipticK (sin (Real.pi*t/2))^2 := by
      unfold sineProfile
      rw [mul_pow, mul_pow, sq_sqrt hsin.le]
    _ ≤ (2/(Real.pi*sqrt Real.pi))^2*sin (Real.pi*t)*
        (Real.pi^2/(4*cos (Real.pi*t/2))) :=
      mul_le_mul_of_nonneg_left hK (mul_nonneg (sq_nonneg _) hsin.le)
    _ = _ := by
      rw [hs]
      field_simp [pi_pos.ne', (sqrt_pos.mpr pi_pos).ne', hcos.ne']
      nlinarith [sq_sqrt pi_pos.le]

/--
The stated quantitative bound `sineDensity t^2 ≤ 2*sin (Real.pi*t)`.

Use: `«2606.16671v2».SineJacobi.sineEnergy_le_four_div_pi` uses this bound to establish the
stated quantitative bound `sineEnergy ≤ 4/Real.pi`.

Article: 2606.16671v2, Theorem 5.2 via `«2606.16671v2».SineJacobi.sineEnergy_le_four_div_pi`.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem sineDensity_square_bound {t : ℝ} (ht : t ∈ Ioo (0:ℝ) 1) :
    sineDensity t^2 ≤ 2*sin (Real.pi*t) := by
  -- Clear the denominators using the available nonzero hypotheses, then verify the remaining
  -- algebraic identity.
  have href : 1-t ∈ Ioo (0:ℝ) 1 := ⟨by linarith [ht.2], by linarith [ht.1]⟩
  have ha := sineProfile_square_bound ht
  have hb := sineProfile_square_bound href
  have hc : sin (Real.pi*(1-t)/2) = cos (Real.pi*t/2) := by
    rw [show Real.pi*(1-t)/2 = Real.pi/2-Real.pi*t/2 by ring, sin_pi_div_two_sub]
  rw [hc] at hb
  have hsinhalf : 0 < sin (Real.pi*t/2) := sin_pos_of_mem_Ioo
    ⟨by nlinarith [pi_pos, ht.1], by nlinarith [pi_pos, ht.2]⟩
  have hp := mul_le_mul ha hb (sq_nonneg _) (mul_nonneg (by positivity) hsinhalf.le)
  have hs : sin (Real.pi*t) = 2*sin (Real.pi*t/2)*cos (Real.pi*t/2) := by
    rw [← sin_two_mul]; congr 1; ring
  calc
    _ = Real.pi^2*(sineProfile t^2*sineProfile (1-t)^2) := by
      unfold sineDensity profileProduct; ring
    _ ≤ Real.pi^2*((2/Real.pi)*sin (Real.pi*t/2)*
        ((2/Real.pi)*cos (Real.pi*t/2))) := mul_le_mul_of_nonneg_left hp (sq_nonneg _)
    _ = _ := by rw [hs]; field_simp

/--
A purely analytic certificate sufficient for the strict comparison with the prefix method.

The stated quantitative bound `sineEnergy ≤ 4/Real.pi`.

Use: `«2606.16671v2».SineJacobi.sineEnergy_lt_four_thirds` uses this bound to establish the
stated quantitative bound `sineEnergy < (4/3:ℝ)`.

Article: 2606.16671v2, Theorem 5.2.

Proof: Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem sineEnergy_le_four_div_pi : sineEnergy ≤ 4/Real.pi := by
  -- Prove equality of functions by evaluating both sides at an arbitrary argument.
  have h2 : IntervalIntegrable (fun t => sineDensity t^2) volume 0 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num : (0:ℝ) ≤ 1)]
    change Integrable (fun t => sineDensity t^2) (volume.restrict (Ioo (0:ℝ) 1))
    convert (sineDensity_memLp 2).integrable_norm_pow (p := 2) (by norm_num) using 1
    funext t; simp only [Real.norm_eq_abs, sq_abs]
  -- Establish continuity hsin before using the function at limits or in calculus arguments.
  have hsin : Continuous (fun t : ℝ => 2*sin (Real.pi*t)) := by fun_prop
  have he := intervalIntegral.integral_mono_on_of_le_Ioo (μ := volume)
    (by norm_num : (0:ℝ) ≤ 1) h2 (hsin.intervalIntegrable 0 1)
    (fun t ht => sineDensity_square_bound ht)
  have hi : (∫ t in (0:ℝ)..1, 2*sin (Real.pi*t)) = 4/Real.pi := by
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_comp_mul_left _ pi_pos.ne',
      integral_sin]
    simp only [mul_one, mul_zero, cos_zero, cos_pi, sub_neg_eq_add, smul_eq_mul]
    ring
  exact he.trans_eq hi

/--
The stated quantitative bound `sineEnergy < (4/3:ℝ)`.

Use: `«2606.16671v2».SineJacobi.leading_constant_lt_prefix` uses this bound to establish the
stated quantitative bound `2*sqrt sineEnergy < 4/sqrt 3`.

Article: 2606.16671v2, Theorem 5.2.

Proof: Use the identities/estimates `«2606.16671v2».SineJacobi.sineEnergy_le_four_div_pi` with
the arguments shown in the proof.
-/
theorem sineEnergy_lt_four_thirds : sineEnergy < (4/3:ℝ) := by
  apply sineEnergy_le_four_div_pi.trans_lt
  exact (div_lt_div_iff₀ pi_pos (by norm_num : (0:ℝ) < 3)).mpr (by nlinarith [pi_gt_three])

end
end «2606.16671v2».SineJacobi

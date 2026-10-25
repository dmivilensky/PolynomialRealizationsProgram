import polyak.FareyPlateau.LargeCurvature.CircleDistance
import polyak.FareyPlateau.Symbols.Positivity
import Mathlib.RingTheory.Coprime.Basic

/-! The far-zone denominator bound for the actual three consecutive
lags in one coprime residue class. -/
noncomputable section
namespace polyak.FareyPlateau.LargeCurvature
open scoped BigOperators

def integerLag (n k : ℤ) : Fin 3 → ℤ := ![n - k, n, n + k]

theorem integerLag_cast (n k : ℤ) (i : Fin 3) :
    (integerLag n k i : ℝ) = lag n k i := by
  fin_cases i <;> simp [integerLag, lag]

theorem weighted_cosine_term (n : Fin 3 → ℤ) (w : Fin 3 → ℝ)
    (hw : ∀ i, 0 ≤ w i) (i : Fin 3) (x : ℝ) :
    w i * (1 - Real.cos ((n i : ℝ) * x)) ≤ Symbols.denominator n w x := by
  exact Finset.single_le_sum (f := fun j => w j * (1 - Real.cos ((n j : ℝ) * x))) (fun j _ => mul_nonneg (hw j)
    (sub_nonneg.mpr (Real.cos_le_one _))) (Finset.mem_univ i)

theorem denominator_distance_lower (n : Fin 3 → ℤ) (w : Fin 3 → ℝ)
    (hw : ∀ i, 0 ≤ w i) {i : Fin 3} {x η : ℝ} (hη : 0 ≤ η)
    (hi : (1 / 12 : ℝ) ≤ w i) (hd : η ≤ turnDistance ((n i : ℝ) * x)) :
    η^2 / (6 * Real.pi^2) ≤ Symbols.denominator n w x := by
  have hs : η^2 ≤ (turnDistance ((n i : ℝ) * x))^2 :=
    (sq_le_sq₀ hη (turnDistance_nonneg _)).mpr hd
  have hc := one_sub_cos_distance ((n i : ℝ) * x)
  have hmul := mul_le_mul_of_nonneg_right hi (sub_nonneg.mpr (Real.cos_le_one ((n i : ℝ) * x)))
  have hlow : η^2 / (6 * Real.pi^2) ≤ w i * (1 - Real.cos ((n i : ℝ) * x)) := by
    have hh := (div_le_div_of_nonneg_right hs (by positivity : (0 : ℝ) ≤ Real.pi^2))
    have he : 2 * (turnDistance ((n i : ℝ) * x))^2 / Real.pi^2 =
      2 * ((turnDistance ((n i : ℝ) * x))^2 / Real.pi^2) := by ring
    rw [he] at hc
    rw [show η^2 / (6 * Real.pi^2) = (η^2 / Real.pi^2) / 6 by ring]
    nlinarith [hc, hh, hmul]
  exact hlow.trans (weighted_cosine_term n w hw i x)

theorem near_period_grid {k : ℤ} {N ω : ℝ} (hk : 5 ≤ k) (hN : 3 * (k : ℝ) / 2 ≤ N)
    (hω : Real.pi / N ≤ ω ∧ ω ≤ Real.pi)
    (hnear : turnDistance ((k : ℝ) * ω) < Real.pi / N) :
    ∃ m : ℤ, 0 < m ∧ m < k ∧
      |ω - 2 * Real.pi * m / k| < Real.pi / ((k : ℝ) * N) := by
  have hkr : (5 : ℝ) ≤ k := by exact_mod_cast hk
  have hkp : 0 < (k : ℝ) := by linarith
  have hNp : 0 < N := by linarith
  have hbase : 0 < Real.pi / N := div_pos Real.pi_pos hNp
  let m := turnIndex ((k : ℝ) * ω)
  have hdist : |(k : ℝ) * ω - (m : ℝ) * (2 * Real.pi)| < Real.pi / N := hnear
  have hdist' := abs_lt.mp hdist
  have hl := mul_le_mul_of_nonneg_left hω.1 hkp.le
  have hu := mul_le_mul_of_nonneg_left hω.2 hkp.le
  have hmr : 0 < (m : ℝ) := by
    have hp := mul_pos (show 0 < (k : ℝ) - 1 by linarith) hbase
    have hturn : 0 < (m : ℝ) * (2 * Real.pi) := by nlinarith [hl, hdist'.2, hp]
    exact pos_of_mul_pos_left hturn (by positivity : 0 ≤ 2 * Real.pi)
  have hmkr : (m : ℝ) < k := by
    have hb : Real.pi / N ≤ Real.pi := div_le_self Real.pi_pos.le (by linarith)
    nlinarith [hu, hdist'.1, hb, Real.pi_pos]
  refine ⟨m, by exact_mod_cast hmr, by exact_mod_cast hmkr, ?_⟩
  have he : ω - 2 * Real.pi * (m : ℝ) / k =
      ((k : ℝ) * ω - (m : ℝ) * (2 * Real.pi)) / k := by field_simp
  rw [he, abs_div, abs_of_pos hkp]
  have hh := (div_lt_div_iff_of_pos_right hkp).mpr hdist
  convert hh using 1
  ring

theorem large_angle_denominator {k n : ℤ} {N ω : ℝ} (hk : 5 ≤ k)
    (hN : 3 * (k : ℝ) / 2 ≤ N) (hn : |(n : ℝ)| ≤ N)
    (hcop : IsCoprime k n) (w : Fin 3 → ℝ)
    (hw : ∀ i, (1 / 12 : ℝ) ≤ w i)
    (hω : Real.pi / N ≤ ω ∧ ω ≤ Real.pi) :
    1 / (24 * N^2) ≤ Symbols.denominator (integerLag n k) w ω := by
  have hkr : (5 : ℝ) ≤ k := by exact_mod_cast hk
  have hkp : 0 < (k : ℝ) := by linarith
  have hNp : 0 < N := by linarith
  have hw0 (i) : 0 ≤ w i := (by norm_num : (0 : ℝ) ≤ 1 / 12).trans (hw i)
  let η := Real.pi / (2 * N)
  have hη : 0 < η := div_pos Real.pi_pos (by positivity)
  by_cases hbig : 2 * η ≤ turnDistance ((k : ℝ) * ω)
  · have htriangle : turnDistance ((k : ℝ) * ω) ≤
        turnDistance (((n + k : ℤ) : ℝ) * ω) + turnDistance ((n : ℝ) * ω) := by
      have hh := turnDistance_sub_le (((n + k : ℤ) : ℝ) * ω) ((n : ℝ) * ω)
      have he : ((n + k : ℤ) : ℝ) * ω - (n : ℝ) * ω = (k : ℝ) * ω := by push_cast; ring
      rwa [he] at hh
    have hcase : η ≤ turnDistance ((n : ℝ) * ω) ∨
        η ≤ turnDistance (((n + k : ℤ) : ℝ) * ω) := by
      by_contra hh
      push Not at hh
      linarith
    rcases hcase with hm | hp
    · have hh := denominator_distance_lower (integerLag n k) w hw0 hη.le (hw 1) hm
      have he : η^2 / (6 * Real.pi^2) = 1 / (24 * N^2) := by dsimp [η]; field_simp; norm_num
      rwa [he] at hh
    · have hh := denominator_distance_lower (integerLag n k) w hw0 hη.le (hw 2) hp
      have he : η^2 / (6 * Real.pi^2) = 1 / (24 * N^2) := by dsimp [η]; field_simp; norm_num
      rwa [he] at hh
  · have hnear : turnDistance ((k : ℝ) * ω) < Real.pi / N := by
      have he : 2 * η = Real.pi / N := by dsimp [η]; ring
      rw [he] at hbig
      exact lt_of_not_ge hbig
    obtain ⟨m, hm0, hmk, hε⟩ := near_period_grid hk hN hω hnear
    have hmdvd : ¬k ∣ m := by
      intro hh
      have he := Int.le_of_dvd hm0 hh
      omega
    have hndvd : ¬k ∣ m * n := fun hh => hmdvd (hcop.dvd_of_dvd_mul_right hh)
    have hrat := rational_turnDistance_lower (by omega : 0 < k) hndvd
    have hdiff : |2 * Real.pi * ((m * n : ℤ) : ℝ) / k - (n : ℝ) * ω| < Real.pi / k := by
      have he : 2 * Real.pi * ((m * n : ℤ) : ℝ) / k - (n : ℝ) * ω =
          -(n : ℝ) * (ω - 2 * Real.pi * m / k) := by push_cast; ring
      rw [he, abs_mul, abs_neg]
      have hh := mul_lt_mul_of_pos_left hε (show 0 < N by linarith)
      have heN : N * (Real.pi / ((k : ℝ) * N)) = Real.pi / k := by field_simp
      rw [heN] at hh
      exact (mul_le_mul_of_nonneg_right hn (abs_nonneg _)).trans_lt hh
    have hclose := turnDistance_lipschitz (2 * Real.pi * ((m * n : ℤ) : ℝ) / k) ((n : ℝ) * ω)
    have hmid : Real.pi / (k : ℝ) ≤ turnDistance ((n : ℝ) * ω) := by
      have he : 2 * Real.pi / (k : ℝ) = 2 * (Real.pi / k) := by ring
      rw [he] at hrat
      linarith
    have hh := denominator_distance_lower (integerLag n k) w hw0
      (show 0 ≤ Real.pi / (k : ℝ) by positivity) (hw 1) hmid
    have hbound : 1 / (24 * N^2) ≤ (Real.pi / (k : ℝ))^2 / (6 * Real.pi^2) := by
      have he : (Real.pi / (k : ℝ))^2 / (6 * Real.pi^2) = 1 / (6 * (k : ℝ)^2) := by field_simp
      rw [he]
      apply one_div_le_one_div_of_le (by positivity)
      nlinarith
    exact hbound.trans hh

end polyak.FareyPlateau.LargeCurvature

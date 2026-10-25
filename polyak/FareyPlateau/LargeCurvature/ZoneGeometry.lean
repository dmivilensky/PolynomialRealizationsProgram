import polyak.FareyPlateau.LargeCurvature.MiddleZone
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-! The three-zone decomposition has uniform source-derived geometric
margins.  In particular the far-zone cosine distance is quantitative. -/
noncomputable section
namespace polyak.FareyPlateau.LargeCurvature
open Set

def zoneRadius (k N : ℝ) : ℝ := Real.pi / (k * N)
def sineMargin (k : ℝ) : ℝ := Real.sin (Real.pi / (2 * k))
def cosineMargin (ω d : ℝ) : ℝ :=
  min (Real.cos (ω - d) - Real.cos ω) (Real.cos ω - Real.cos (ω + d))

theorem sin_lower_on_trimmed_interval {t x : ℝ}
    (ht : 0 ≤ t) (htπ : t ≤ Real.pi / 2) (hx : t ≤ x ∧ x ≤ Real.pi - t) :
    Real.sin t ≤ Real.sin x := by
  by_cases hhalf : x ≤ Real.pi / 2
  · exact Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_pos]) hhalf hx.1
  · have he : Real.sin (Real.pi - x) = Real.sin x := by simp
    rw [← he]
    apply Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_pos])
      (by linarith) (by linarith [hx.2])

theorem zoneRadius_bounds {k N : ℝ} (hk : 5 ≤ k) (hN : 3 * k / 2 ≤ N) :
    0 < zoneRadius k N ∧ zoneRadius k N ≤ Real.pi / (2 * k) := by
  have hkp : 0 < k := by linarith
  have hNp : 0 < N := by linarith
  refine ⟨by unfold zoneRadius; positivity, ?_⟩
  unfold zoneRadius
  exact div_le_div_of_nonneg_left Real.pi_pos.le (by positivity) (by nlinarith)

theorem central_interval_trimmed {k N ω : ℝ} (hk : 5 ≤ k) (hN : 3 * k / 2 ≤ N)
    (hωl : 4 * Real.pi / k ≤ ω) (hωr : ω ≤ Real.pi - Real.pi / k) :
    Icc (ω - zoneRadius k N) (ω + zoneRadius k N) ⊆
      Icc (Real.pi / (2 * k)) (Real.pi - Real.pi / (2 * k)) := by
  have hd := zoneRadius_bounds hk hN
  have hp : 0 < Real.pi / k := div_pos Real.pi_pos (by linarith)
  have he : Real.pi / (2 * k) = (Real.pi / k) / 2 := by ring
  have he4 : 4 * Real.pi / k = 4 * (Real.pi / k) := by ring
  rw [he4] at hωl
  intro x hx
  rw [he] at hd ⊢
  exact ⟨by linarith [hx.1], by linarith [hx.2]⟩

theorem central_sine_lower {k N ω x : ℝ} (hk : 5 ≤ k) (hN : 3 * k / 2 ≤ N)
    (hωl : 4 * Real.pi / k ≤ ω) (hωr : ω ≤ Real.pi - Real.pi / k)
    (hx : x ∈ Icc (ω - zoneRadius k N) (ω + zoneRadius k N)) :
    sineMargin k ≤ Real.sin x := by
  have hh := central_interval_trimmed hk hN hωl hωr hx
  apply sin_lower_on_trimmed_interval (by positivity : 0 ≤ Real.pi / (2 * k))
    (div_le_div_of_nonneg_left Real.pi_pos.le (by norm_num) (by linarith)) hh

theorem cosineMargin_lower {k N ω : ℝ} (hk : 5 ≤ k) (hN : 3 * k / 2 ≤ N)
    (hωl : 4 * Real.pi / k ≤ ω) (hωr : ω ≤ Real.pi - Real.pi / k) :
    2 * sineMargin k / (k * N) ≤ cosineMargin ω (zoneRadius k N) := by
  let d := zoneRadius k N
  have hd := zoneRadius_bounds hk hN
  have hmidl := central_sine_lower hk hN hωl hωr
    (show ω - d / 2 ∈ Icc (ω - zoneRadius k N) (ω + zoneRadius k N) by dsimp [d]; constructor <;> linarith [hd.1])
  have hmidr := central_sine_lower hk hN hωl hωr
    (show ω + d / 2 ∈ Icc (ω - zoneRadius k N) (ω + zoneRadius k N) by dsimp [d]; constructor <;> linarith [hd.1])
  have hsh : 0 ≤ sineMargin k := by
    apply Real.sin_nonneg_of_nonneg_of_le_pi (by positivity)
    apply div_le_self Real.pi_pos.le
    linarith
  have hdhalf : d / 2 ≤ Real.pi / 2 := by
    have hp : Real.pi / (2 * k) ≤ Real.pi := div_le_self Real.pi_pos.le (by linarith)
    dsimp [d]
    linarith [hd.2]
  have hsin : d / Real.pi ≤ Real.sin (d / 2) := by
    have hh := Real.mul_le_sin (show 0 ≤ d / 2 by dsimp [d]; linarith [hd.1]) hdhalf
    convert hh using 1
    ring
  have hsin0 : 0 ≤ Real.sin (d / 2) := (div_nonneg (show 0 ≤ d by exact hd.1.le) Real.pi_pos.le).trans hsin
  have he₁ : Real.cos (ω - d) - Real.cos ω = 2 * Real.sin (ω - d / 2) * Real.sin (d / 2) := by
    rw [Real.cos_sub_cos]
    rw [show (ω - d + ω) / 2 = ω - d / 2 by ring,
      show (ω - d - ω) / 2 = -(d / 2) by ring, Real.sin_neg]
    ring
  have he₂ : Real.cos ω - Real.cos (ω + d) = 2 * Real.sin (ω + d / 2) * Real.sin (d / 2) := by
    rw [Real.cos_sub_cos]
    rw [show (ω + (ω + d)) / 2 = ω + d / 2 by ring,
      show (ω - (ω + d)) / 2 = -(d / 2) by ring, Real.sin_neg]
    ring
  have hb (v : ℝ) (hv : sineMargin k ≤ Real.sin v) :
      2 * sineMargin k / (k * N) ≤ 2 * Real.sin v * Real.sin (d / 2) := by
    have h₁ := mul_le_mul_of_nonneg_right hv hsin0
    have h₂ := mul_le_mul_of_nonneg_left hsin hsh
    have he : sineMargin k * (d / Real.pi) = sineMargin k / (k * N) := by
      dsimp [d, zoneRadius]
      field_simp
    rw [he] at h₂
    have hh := mul_le_mul_of_nonneg_left (h₂.trans h₁) (show (0 : ℝ) ≤ 2 by norm_num)
    convert hh using 1 <;> ring
  exact le_min (by rw [he₁]; exact hb _ hmidl) (by rw [he₂]; exact hb _ hmidr)

theorem cosine_distance_far {ω d x : ℝ} (hd : 0 < d)
    (hl : 0 ≤ ω - d) (hr : ω + d ≤ Real.pi)
    (hx : x ∈ Icc (0 : ℝ) Real.pi) (hfar : x ∉ Icc (ω - d) (ω + d)) :
    cosineMargin ω d ≤ |Real.cos x - Real.cos ω| := by
  have hn : x < ω - d ∨ ω + d < x := by
    simpa only [mem_Icc, not_and_or, not_le] using hfar
  rcases hn with h | h
  · have hc := Real.cos_le_cos_of_nonneg_of_le_pi hx.1 (by linarith [hr, hd]) h.le
    have he := min_le_left (Real.cos (ω - d) - Real.cos ω) (Real.cos ω - Real.cos (ω + d))
    change cosineMargin ω d ≤ _ at he
    linarith [le_abs_self (Real.cos x - Real.cos ω)]
  · have hc := Real.cos_le_cos_of_nonneg_of_le_pi (by linarith [hl, hd]) hx.2 h.le
    have he := min_le_right (Real.cos (ω - d) - Real.cos ω) (Real.cos ω - Real.cos (ω + d))
    change cosineMargin ω d ≤ _ at he
    linarith [neg_le_abs (Real.cos x - Real.cos ω)]

end polyak.FareyPlateau.LargeCurvature

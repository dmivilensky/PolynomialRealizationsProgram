import polyak.FareyPlateau.LargeCurvature.ZoneGeometry
import polyak.FareyPlateau.Ray.Slope

/-! The original four-term explicit cutoff, with its quantitative
consequences. No replacement by an unspecified sufficiently large bound. -/
noncomputable section
namespace polyak.FareyPlateau.LargeCurvature
open Real Ray

def slopeBound (k ω M : ℝ) : ℝ :=
  2 * Real.sin (Real.pi / k)^2 *
    (1 + M + (Real.cos (Real.pi / k) / Real.sin (Real.pi / k)) * |Real.cos ω / Real.sin ω|)
def lagBound (k ω M : ℝ) : ℝ := slopeBound k ω M + 3 * k / 2
def centralFactor (k h : ℝ) : ℝ := 1 + (h + 1)^2 / (sineMargin k)^2
def a1 (k ω h M : ℝ) : ℝ :=
  let N := lagBound k ω M
  let sh := sineMargin k
  max (max ((h + 2 + 2 * M) * k^2 * N^2 / (2 * sh^2))
    (12 * k^2 * N^4 / sh^2))
    (max ((1 + M)^2 / 4) (Real.pi * centralFactor k h * (9 * k^2 + 3 * Real.pi * k) / (16 * sh^2)))

@[fun_prop] theorem continuous_a1 (k ω h : ℝ) : Continuous (a1 k ω h) := by
  unfold a1 lagBound slopeBound
  fun_prop

theorem sineMargin_pos {k : ℝ} (hk : 5 ≤ k) : 0 < sineMargin k := by
  apply Real.sin_pos_of_pos_of_lt_pi (by positivity)
  exact div_lt_self Real.pi_pos (by linarith)

theorem slopeBound_nonneg {k ω M : ℝ} (hk : 5 ≤ k) (hM : 0 ≤ M) :
    0 ≤ slopeBound k ω M := by
  have hs : 0 ≤ Real.sin (Real.pi / k) := Real.sin_nonneg_of_nonneg_of_le_pi (by positivity)
    (div_le_self Real.pi_pos.le (by linarith))
  have hc : 0 ≤ Real.cos (Real.pi / k) := Real.cos_nonneg_of_mem_Icc
    ⟨by linarith [Real.pi_pos, div_pos Real.pi_pos (by linarith : 0 < k)],
      div_le_div_of_nonneg_left Real.pi_pos.le (by norm_num) (by linarith)⟩
  unfold slopeBound
  positivity

theorem lagBound_ge {k ω M : ℝ} (hk : 5 ≤ k) (hM : 0 ≤ M) :
    3 * k / 2 ≤ lagBound k ω M := by
  dsimp [lagBound]
  linarith [slopeBound_nonneg (ω := ω) hk hM]

theorem edgeSlope_bound {k ω M D : ℝ} (hk : 5 ≤ k) (_hM : 0 ≤ M) (hD : |D| ≤ M) :
    |edgeSlope ω (Real.pi / k) D| ≤ slopeBound k ω M := by
  have hs : 0 < Real.sin (Real.pi / k) := Real.sin_pos_of_pos_of_lt_pi
    (by positivity) (div_lt_self Real.pi_pos (by linarith))
  have hc : 0 ≤ Real.cos (Real.pi / k) := Real.cos_nonneg_of_mem_Icc
    ⟨by linarith [Real.pi_pos, div_pos Real.pi_pos (by linarith : 0 < k)],
      div_le_div_of_nonneg_left Real.pi_pos.le (by norm_num) (by linarith)⟩
  have hcot : 0 ≤ Real.cos (Real.pi / k) / Real.sin (Real.pi / k) := div_nonneg hc hs.le
  unfold edgeSlope slopeBound
  rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2 * Real.sin (Real.pi / k)^2)]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have hD' := abs_le.mp hD
  have hfactor : |1 + D| ≤ 1 + M := abs_le.mpr ⟨by linarith [hD'.1], by linarith [hD'.2]⟩
  have hsum := (abs_add_le (1 + D)
    ((Real.cos (Real.pi / k) / Real.sin (Real.pi / k)) * (Real.cos ω / Real.sin ω)))
  rw [abs_mul, abs_of_nonneg hcot] at hsum
  linarith

theorem a1_faces {k ω h M a : ℝ} (ha : a1 k ω h M < a) :
    (h + 2 + 2 * M) * k^2 * (lagBound k ω M)^2 / (2 * (sineMargin k)^2) < a ∧
      12 * k^2 * (lagBound k ω M)^4 / (sineMargin k)^2 < a ∧
      (1 + M)^2 / 4 < a ∧
      Real.pi * centralFactor k h * (9 * k^2 + 3 * Real.pi * k) /
        (16 * (sineMargin k)^2) < a := by
  exact ⟨(le_max_left _ _).trans_lt ((le_max_left _ _).trans_lt ha),
    (le_max_right _ _).trans_lt ((le_max_left _ _).trans_lt ha),
    (le_max_left _ _).trans_lt ((le_max_right _ _).trans_lt ha),
    (le_max_right _ _).trans_lt ((le_max_right _ _).trans_lt ha)⟩

theorem scaled_cosine_margin {k N sh ε a C : ℝ}
    (hk : 0 < k) (hN : 0 < N) (hsh : 0 < sh) (hap : 0 < a)
    (hε : 2 * sh / (k * N) ≤ ε)
    (ha : C * (k * N)^2 / (4 * sh^2) < a) : C < a * ε^2 := by
  have hεp : 0 < ε := (div_pos (by positivity) (mul_pos hk hN)).trans_le hε
  have hεmul := (div_le_iff₀ (mul_pos hk hN)).mp hε
  have hs : 4 * sh^2 ≤ ε^2 * (k * N)^2 := by nlinarith [sq_nonneg (ε * (k * N) - 2 * sh)]
  have hh := (div_lt_iff₀ (show 0 < 4 * sh^2 by positivity)).mp ha
  have hm := mul_le_mul_of_nonneg_left hs hap.le
  have hprod : C * (k * N)^2 < (a * ε^2) * (k * N)^2 := by nlinarith
  exact (mul_lt_mul_iff_of_pos_right (sq_pos_of_pos (mul_pos hk hN))).mp hprod

theorem cutoff_cosine_margins {k ω h M ε a : ℝ} (hk : 5 ≤ k) (hM : 0 ≤ M)
    (_hh : 0 ≤ h) (ha : a1 k ω h M < a)
    (hε : 2 * sineMargin k / (k * lagBound k ω M) ≤ ε) :
    2 * (h + 2 + 2 * M) < a * ε^2 ∧ 48 * (lagBound k ω M)^2 < a * ε^2 := by
  obtain ⟨h₁, h₂, h₃, _h₄⟩ := a1_faces ha
  have hN := lagBound_ge (ω := ω) hk hM
  have hNp : 0 < lagBound k ω M := by linarith
  have hap : 0 < a := lt_of_le_of_lt (by positivity : 0 ≤ (1 + M)^2 / 4) h₃
  have hsh := sineMargin_pos hk
  constructor
  · apply scaled_cosine_margin (by linarith) hNp hsh hap hε
    convert h₁ using 1
    ring
  · apply scaled_cosine_margin (by linarith) hNp hsh hap hε
    convert h₂ using 1
    ring

end polyak.FareyPlateau.LargeCurvature

import polyak.FareyPlateau.FanAnalysis.JetCalculus
import Mathlib.Analysis.Convex.Slope

/-! Convexity controls the complete signed lattice from finitely many local
tests. Lattice indices are unbounded and may grow at the reciprocal scale. -/
noncomputable section
namespace polyak.FareyPlateau.FanAnalysis
open Set

theorem convex_right_tail {s : Set ℝ} {f : ℝ → ℝ} (hf : ConvexOn ℝ s f)
    {a b x : ℝ} (ha : a ∈ s) (hx : x ∈ s) (hab : a < b) (hbx : b ≤ x)
    (hval : f a ≤ f b) : f b ≤ f x := by
  rcases eq_or_lt_of_le hbx with rfl | hbx
  · exact le_rfl
  have hs := hf.slope_mono_adjacent ha hx hab hbx
  have hfirst : 0 ≤ (f b - f a) / (b - a) := by
    exact div_nonneg (sub_nonneg.mpr hval) (sub_nonneg.mpr hab.le)
  have hlast := hfirst.trans hs
  have := (le_div_iff₀ (sub_pos.mpr hbx)).mp hlast
  linarith

theorem convex_left_tail {s : Set ℝ} {f : ℝ → ℝ} (hf : ConvexOn ℝ s f)
    {a b x : ℝ} (hx : x ∈ s) (hb : b ∈ s) (hxa : x ≤ a) (hab : a < b)
    (hval : f b ≤ f a) : f a ≤ f x := by
  rcases eq_or_lt_of_le hxa with rfl | hxa
  · exact le_rfl
  have hs := hf.slope_mono_adjacent hx hb hxa hab
  have hlast : (f b - f a) / (b - a) ≤ 0 := by
    exact div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hval) (sub_nonneg.mpr hab.le)
  have hfirst := hs.trans hlast
  have := (div_le_iff₀ (sub_pos.mpr hxa)).mp hfirst
  linarith

theorem convex_lattice_from_four {s : Set ℝ} {f : ℝ → ℝ}
    (hf : ConvexOn ℝ s f) {a h : ℝ} (hh : 0 < h)
    (hm1 : a - h ∈ s) (h2 : a + 2 * h ∈ s)
    (h0 : 0 < f a) (h1 : 0 < f (a + h))
    (hleft : f a ≤ f (a - h)) (hright : f (a + h) ≤ f (a + 2 * h))
    (n : ℤ) (hn : a + (n : ℝ) * h ∈ s) : 0 < f (a + (n : ℝ) * h) := by
  by_cases hn0 : n = 0
  · simpa only [hn0, Int.cast_zero, zero_mul, add_zero] using h0
  by_cases hn1 : n = 1
  · simpa only [hn1, Int.cast_one, one_mul] using h1
  have hcases : n ≤ -1 ∨ 2 ≤ n := by omega
  rcases hcases with hl | hr
  · have hln : (n : ℝ) ≤ -1 := by exact_mod_cast hl
    have hx : a + (n : ℝ) * h ≤ a - h := by nlinarith
    have ha : a ∈ s := by
      convert hf.1 hm1 h2 (show 0 ≤ (2 / 3 : ℝ) by norm_num)
        (show 0 ≤ (1 / 3 : ℝ) by norm_num) (by norm_num) using 1
      simp only [smul_eq_mul]
      ring
    exact h0.trans_le (hleft.trans (convex_left_tail hf (a := a - h) (b := a) hn ha hx (by linarith) hleft))
  · have hrn : (2 : ℝ) ≤ n := by exact_mod_cast hr
    have hx : a + 2 * h ≤ a + (n : ℝ) * h := by nlinarith
    have ha1 : a + h ∈ s := by
      convert hf.1 hm1 h2 (show 0 ≤ (1 / 3 : ℝ) by norm_num)
        (show 0 ≤ (2 / 3 : ℝ) by norm_num) (by norm_num) using 1
      simp only [smul_eq_mul]
      ring
    exact h1.trans_le (hright.trans
      (convex_right_tail hf ha1 hn (show a + h < a + 2 * h by linarith) hx hright))

theorem convex_lattice_from_neighbors {s : Set ℝ} {f : ℝ → ℝ}
    (hf : ConvexOn ℝ s f) {h : ℝ} (hh : 0 < h)
    (hleft : -h ∈ s) (hright : h ∈ s) (hzero : f 0 = 0)
    (hfleft : 0 < f (-h)) (hfright : 0 < f h)
    (n : ℤ) (hn : (n : ℝ) * h ∈ s) (hn0 : n ≠ 0) : 0 < f ((n : ℝ) * h) := by
  have hz : (0 : ℝ) ∈ s := by
    convert hf.1 hleft hright (show 0 ≤ (1 / 2 : ℝ) by norm_num)
      (show 0 ≤ (1 / 2 : ℝ) by norm_num) (by norm_num) using 1
    simp only [smul_eq_mul]
    ring
  rcases lt_or_gt_of_ne hn0 with hl | hr
  · have hnl : (n : ℝ) ≤ -1 := by exact_mod_cast (show n ≤ -1 by omega)
    have hx : (n : ℝ) * h ≤ -h := by nlinarith
    have hval : f 0 ≤ f (-h) := by rw [hzero]; exact hfleft.le
    exact hfleft.trans_le (convex_left_tail hf hn hz hx (show -h < 0 by linarith) hval)
  · have hnr : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
    have hx : h ≤ (n : ℝ) * h := by nlinarith
    have hval : f 0 ≤ f h := by rw [hzero]; exact hfright.le
    exact hfright.trans_le (convex_right_tail hf hz hn (show 0 < h from hh) hx hval)


end polyak.FareyPlateau.FanAnalysis

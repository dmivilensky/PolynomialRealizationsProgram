import polyak.General.Multipliers.Annulus
import polyak.General.Multipliers.NearOne
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

/-! The multiplier criterion acts on the literal source cubic H, with no
surrogate positivity assumption. -/
namespace polyak.General.Multipliers
noncomputable section
open Set

theorem ratio_normSq (A B M : ℂ) (hb : B ≠ 0) :
    (M*A*star B).re = Complex.normSq B*(M*A/B).re := by
  have he : M*A*star B = (Complex.normSq B : ℂ)*(M*A/B) := by
    rw [show (Complex.normSq B : ℂ)=B*star B from (Complex.mul_conj _).symm]
    field_simp
  rw [he, Complex.mul_re]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

theorem H_norm_arg (q : Tuning) {z : ℂ} (hb : q.b z ≠ 0) :
    q.H ‖z‖ (Real.cos (Complex.arg z)) =
      Complex.normSq (q.b z)*((1-z)*q.a z/q.b z).re := by
  rw [q.H_complex, Complex.norm_mul_exp_arg_mul_I]
  exact ratio_normSq _ _ _ hb

theorem source_inner_nonnegative (q : Tuning) {r : ℝ} (hr : q.rhoB < r)
    (hH : ∀ c ∈ Icc (-1 : ℝ) 1, 0 ≤ q.H r c) :
    ∀ z : ℂ, ‖z‖ = r → 0 ≤ ((1-z)*q.a z/q.b z).re := by
  intro z hz
  have hb := b_ne_zero_outside q (hz.symm ▸ hr)
  have h := H_norm_arg q hb
  rw [hz] at h
  have hnonneg := hH (Real.cos (Complex.arg z))
    ⟨Real.neg_one_le_cos _,Real.cos_le_one _⟩
  rw [h] at hnonneg
  exact nonneg_of_mul_nonneg_right hnonneg (Complex.normSq_pos.mpr hb)

theorem norm_radial (r w : ℝ) (hr : 0 ≤ r) :
    ‖(r:ℂ)*Complex.exp ((w:ℂ)*Complex.I)‖ = r := by
  rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg hr]

theorem source_inner_iff (q : Tuning) {r : ℝ} (hr : q.rhoB < r) :
    (∀ c ∈ Icc (-1 : ℝ) 1, 0 ≤ q.H r c) ↔
      ∀ z : ℂ, ‖z‖ = r → 0 ≤ ((1-z)*q.a z/q.b z).re := by
  refine ⟨source_inner_nonnegative q hr, ?_⟩
  intro h c hc
  have hr0 : 0 ≤ r := ((rootRadius_nonneg _ _).trans hr.le)
  let z : ℂ := (r:ℂ)*Complex.exp ((Real.arccos c:ℂ)*Complex.I)
  have hn : ‖z‖ = r := norm_radial r _ hr0
  have hb := b_ne_zero_outside q (hn.symm ▸ hr)
  rw [← Real.cos_arccos hc.1 hc.2, q.H_complex]
  rw [ratio_normSq _ _ _ hb]
  exact mul_nonneg (Complex.normSq_nonneg _) (h z hn)

theorem source_outer_nonnegative (q : Tuning)
    (hL : ∀ c ∈ Icc (-1 : ℝ) 1, 0 ≤ q.L c) :
    ∀ z : ℂ, ‖z‖ = 1 → 0 ≤ ((1-z)*q.a z/q.b z).re := by
  apply source_inner_nonnegative q ((le_max_right _ _).trans_lt q.rhoQ_lt_one)
  intro c hc
  rw [q.H_one]
  exact mul_nonneg (sub_nonneg.mpr hc.2) (hL c hc)

theorem source_outer_positive (q : Tuning)
    (hL : ∀ c ∈ Icc (-1 : ℝ) 1, 0 < q.L c) :
    ∀ z : ℂ, ‖z‖ = 1 → z ≠ 1 → 0 < ((1-z)*q.a z/q.b z).re := by
  intro z hz hz1
  have hb := q.b_ne_zero_of_one_le_norm hz.ge
  have hz0 : z ≠ 0 := norm_ne_zero_iff.mp (hz.trans_ne one_ne_zero)
  have hcos : Real.cos (Complex.arg z) < 1 := by
    apply lt_of_le_of_ne (Real.cos_le_one _)
    intro hc
    have hr : z.re = 1 := by simpa only [Complex.cos_arg hz0, hz, div_one] using hc
    have hn : Complex.normSq z = 1 := by rw [Complex.normSq_eq_norm_sq, hz]; norm_num
    have hi : z.im = 0 := by
      rw [Complex.normSq_apply, hr] at hn
      nlinarith [sq_nonneg z.im]
    exact hz1 (Complex.ext (by simpa using hr) (by simpa using hi))
  have hH : 0 < q.H 1 (Real.cos (Complex.arg z)) := by
    rw [q.H_one]
    exact mul_pos (sub_pos.mpr hcos) (hL _ ⟨Real.neg_one_le_cos _,Real.cos_le_one _⟩)
  have he := H_norm_arg q hb
  rw [hz] at he
  rw [he] at hH
  exact pos_of_mul_pos_right hH (Complex.normSq_nonneg _)

theorem source_rate_le_radius (q : Tuning)
    (hL : ∀ c ∈ Icc (-1 : ℝ) 1, 0 < q.L c)
    {r : ℝ} (hr : q.rhoB < r) (hr1 : r < 1)
    (hH : ∀ c ∈ Icc (-1 : ℝ) 1, 0 ≤ q.H r c) : q.rate ≤ r := by
  apply lower_rate_le_radius q {1} (fun _ => 1)
    (by simp) (by simp) (by simp) hr hr1
  · simpa [lowerRatio, polynomial] using source_inner_nonnegative q hr hH
  · simpa [lowerRatio, polynomial] using source_outer_positive q hL

theorem source_rate_lt_one (q : Tuning)
    (hL : ∀ c ∈ Icc (-1 : ℝ) 1, 0 < q.L c) : q.rate < 1 := by
  apply lower_rate_lt_one q {1} (fun _ => 1) (by simp) (by simp) (by simp)
  simpa [polynomial] using source_outer_positive q hL

theorem source_rate_le_one (q : Tuning)
    (hL : ∀ c ∈ Icc (-1 : ℝ) 1, 0 ≤ q.L c) : q.rate ≤ 1 := by
  apply lower_rate_le_one q {1} (fun _ => 1) (by simp) (by simp) (by simp)
  simpa [polynomial] using source_outer_nonnegative q hL

theorem exists_positive_ratio_inner_band (q : Tuning)
    (hL : ∀ c ∈ Icc (-1 : ℝ) 1, 0 < q.L c) :
    ∃ eta : ℝ, 0 < eta ∧ ∀ z : ℂ,
      1-eta ≤ ‖z‖ → ‖z‖ < 1 → 0 < ((1-z)*q.a z/q.b z).re := by
  obtain ⟨e,he,hband⟩ := exists_positive_inner_band q hL
  have hr1 : q.rhoB < 1 := (le_max_right _ _).trans_lt q.rhoQ_lt_one
  refine ⟨min e ((1-q.rhoB)/2), lt_min he (half_pos (sub_pos.mpr hr1)), ?_⟩
  intro z hz hz1
  have hmin := min_le_left e ((1-q.rhoB)/2)
  have hroot := min_le_right e ((1-q.rhoB)/2)
  have hb := b_ne_zero_outside q (by linarith : q.rhoB < ‖z‖)
  have hH := hband ‖z‖ (Real.cos (Complex.arg z)) (by linarith) hz1
    ⟨Real.neg_one_le_cos _,Real.cos_le_one _⟩
  rw [H_norm_arg q hb] at hH
  exact pos_of_mul_pos_right hH (Complex.normSq_nonneg _)

theorem source_radius_monotone (q : Tuning)
    (hL : ∀ c ∈ Icc (-1 : ℝ) 1, 0 ≤ q.L c)
    {r r' : ℝ} (hr : q.rhoB < r) (hrr : r ≤ r') (hr' : r' < 1)
    (hH : ∀ c ∈ Icc (-1 : ℝ) 1, 0 ≤ q.H r c) :
    ∀ c ∈ Icc (-1 : ℝ) 1, 0 ≤ q.H r' c := by
  rcases hrr.eq_or_lt with h | h
  · simpa only [← h] using hH
  apply (source_inner_iff q (hr.trans h)).2
  intro z hz
  have hh := lower_annulus_nonnegative q {1} (fun _ => 1) hr
    (by simpa [lowerRatio, polynomial] using source_inner_nonnegative q hr hH)
    (by simpa [lowerRatio, polynomial] using source_outer_nonnegative q hL)
    (subset_closure (show z ∈ annulus r 1 from ⟨hz.symm ▸ h,hz.symm ▸ hr'⟩))
  simpa [lowerRatio, polynomial] using hh

end
end polyak.General.Multipliers

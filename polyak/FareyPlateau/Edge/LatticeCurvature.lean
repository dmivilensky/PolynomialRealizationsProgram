import polyak.FareyPlateau.Edge.Jets

/-! The universal curvature obstruction uses every finite nonnegative
symbol on both tight classes. No restriction to the adjacent two-lag symbol
or to a bounded lag range occurs in this argument. -/
noncomputable section
namespace polyak.FareyPlateau.Edge
open scoped BigOperators

theorem integer_gap_product (m : ℤ) : 0 ≤ (m : ℝ) * ((m : ℝ) - 1) := by
  have hm : m ≤ 0 ∨ 1 ≤ m := by omega
  rcases hm with hm | hm
  · have hmR : (m : ℝ) ≤ 0 := by exact_mod_cast hm
    exact mul_nonneg_of_nonpos_of_nonpos hmR (by linarith)
  · have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
    exact mul_nonneg (by linarith) (by linarith)

theorem adjacent_lattice_product {n₁ k : ℝ} (m : ℤ) :
    0 ≤ (n₁ + (m : ℝ) * k - n₁) * (n₁ + (m : ℝ) * k - (n₁ + k)) := by
  have h := mul_nonneg (sq_nonneg k) (integer_gap_product m)
  nlinarith only [h]

theorem zero_class_product {k t : ℝ} (hk : 0 < k) (ht0 : 0 < t) (ht1 : t < 1)
    (m : ℤ) (hm : m ≠ 0) :
    0 < ((m : ℝ) * k) * ((m : ℝ) * k + k * (1 - 2 * t)) := by
  rcases lt_or_gt_of_ne hm with hm | hm
  · have hmR : (m : ℝ) ≤ -1 := by exact_mod_cast (show m ≤ -1 by omega)
    have hfirst : (m : ℝ) * k < 0 := mul_neg_of_neg_of_pos (by linarith) hk
    have hsecond : (m : ℝ) * k + k * (1 - 2 * t) < 0 := by
      have h := mul_nonpos_of_nonpos_of_nonneg (show (m : ℝ) + 1 ≤ 0 by linarith) hk.le
      nlinarith [mul_pos hk ht0]
    exact mul_pos_of_neg_of_neg hfirst hsecond
  · have hmR : (1 : ℝ) ≤ m := by exact_mod_cast (show 1 ≤ m by omega)
    have hfirst : 0 < (m : ℝ) * k := mul_pos (by linarith) hk
    have hsecond : 0 < (m : ℝ) * k + k * (1 - 2 * t) := by
      have h := mul_nonneg (show 0 ≤ (m : ℝ) - 1 by linarith) hk.le
      nlinarith [mul_pos hk (sub_pos.mpr ht1)]
    exact mul_pos hfirst hsecond

/-- A common affine lower support for the second jets of both tight classes.
Summing it annihilates the first jet of every tangent symbol. -/
theorem curvature_obstruction {ι : Type*} (N : Finset ι)
    (w first second : ι → ℝ) {n₁ k t S C d : ℝ}
    (hk : 0 < k) (ht0 : 0 < t) (ht1 : t < 1) (hS : 0 < S) (hC : 0 ≤ C)
    (hcurv : 2 * S * d ≤ C * k^2 * t * (1 - t))
    (hw : ∀ i ∈ N, 0 ≤ w i)
    (hclass : ∀ i ∈ N,
      (∃ m : ℤ, first i = S * (n₁ + (m : ℝ) * k - (n₁ + t * k)) ∧
        second i = C * (n₁ + (m : ℝ) * k) *
          (n₁ + (m : ℝ) * k - (n₁ + t * k)) - 2 * S * d) ∨
      (∃ m : ℤ, m ≠ 0 ∧ first i = -S * ((m : ℝ) * k) ∧
        second i = C * ((m : ℝ) * k) * ((m : ℝ) * k - (n₁ + t * k))))
    (htangent : ∑ i ∈ N, w i * first i = 0) :
    0 ≤ ∑ i ∈ N, w i * second i := by
  have hpoint (i : ι) (hi : i ∈ N) :
      0 ≤ S * second i - C * (n₁ + k - t * k) * first i := by
    rcases hclass i hi with ⟨m, hf, hs⟩ | ⟨m, hm, hf, hs⟩
    · rw [hf, hs]
      have hp := adjacent_lattice_product (n₁ := n₁) (k := k) m
      have hh := add_nonneg (mul_nonneg hC hp) (sub_nonneg.mpr hcurv)
      have hmul := mul_nonneg hS.le hh
      nlinarith only [hmul]
    · rw [hf, hs]
      have hp := zero_class_product hk ht0 ht1 m hm
      have hh := mul_nonneg hS.le (mul_nonneg hC hp.le)
      nlinarith only [hh]
  have hsum := Finset.sum_nonneg (fun i hi => mul_nonneg (hw i hi) (hpoint i hi))
  have he : (∑ i ∈ N, w i * (S * second i - C * (n₁ + k - t * k) * first i)) =
      S * (∑ i ∈ N, w i * second i) -
        C * (n₁ + k - t * k) * (∑ i ∈ N, w i * first i) := by
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [he, htangent, mul_zero, sub_zero] at hsum
  exact (mul_nonneg_iff_of_pos_left hS).mp hsum

end polyak.FareyPlateau.Edge

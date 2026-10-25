import polyak.FareyPlateau.LargeCurvature.FarDenominator

/-! Both frequency ranges of zone C: a quadratic denominator bound near
zero and global sine-numerator bounds for all the signed lags. -/
noncomputable section
namespace polyak.FareyPlateau.LargeCurvature
open scoped BigOperators

def sineNumerator (n : Fin 3 → ℤ) (w : Fin 3 → ℝ) (ω : ℝ) : ℝ :=
  ∑ i, w i * Real.sin ((n i : ℝ) * ω)

theorem sineNumerator_abs_le_one (n : Fin 3 → ℤ) (w : Fin 3 → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i = 1) (ω : ℝ) :
    |sineNumerator n w ω| ≤ 1 := by
  have hpoint (i) : |w i * Real.sin ((n i : ℝ) * ω)| ≤ w i := by
    rw [abs_mul, abs_of_nonneg (hw i)]
    exact mul_le_of_le_one_right (hw i) (Real.abs_sin_le_one _)
  exact (Finset.abs_sum_le_sum_abs _ _).trans
    ((Finset.sum_le_sum (fun i _ => hpoint i)).trans_eq hsum)

theorem sineNumerator_abs_le_linear (n : Fin 3 → ℤ) (w : Fin 3 → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i = 1) {N ω : ℝ}
    (hN : ∀ i, |(n i : ℝ)| ≤ N) (hω : 0 ≤ ω) : |sineNumerator n w ω| ≤ N * ω := by
  have hpoint (i) : |w i * Real.sin ((n i : ℝ) * ω)| ≤ w i * (N * ω) := by
    rw [abs_mul, abs_of_nonneg (hw i)]
    apply mul_le_mul_of_nonneg_left _ (hw i)
    calc
      _ ≤ |(n i : ℝ) * ω| := Real.abs_sin_le_abs
      _ = |(n i : ℝ)| * ω := by rw [abs_mul, abs_of_nonneg hω]
      _ ≤ N * ω := mul_le_mul_of_nonneg_right (hN i) hω
  have hh := (Finset.abs_sum_le_sum_abs
    (fun i : Fin 3 => w i * Real.sin ((n i : ℝ) * ω)) Finset.univ).trans
      (Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hpoint i))
  simpa only [sineNumerator, ← Finset.sum_mul, hsum, one_mul] using hh

theorem small_angle_denominator (n : Fin 3 → ℤ) (w : Fin 3 → ℝ)
    (hw : ∀ i, 0 ≤ w i) {k N ω : ℝ} (hNp : 0 < N)
    (hN : ∀ i, |(n i : ℝ)| ≤ N)
    (hmoment : k^2 / 6 ≤ ∑ i, w i * (n i : ℝ)^2)
    (hω : 0 ≤ ω ∧ ω ≤ Real.pi / N) :
    k^2 * ω^2 / (3 * Real.pi^2) ≤ Symbols.denominator n w ω := by
  have hsmall (i) : |(n i : ℝ) * ω| ≤ Real.pi := by
    rw [abs_mul, abs_of_nonneg hω.1]
    apply (mul_le_mul_of_nonneg_right (hN i) hω.1).trans
    have hh := mul_le_mul_of_nonneg_left hω.2 hNp.le
    simpa only [mul_div_cancel₀ _ hNp.ne'] using hh
  have hpoint (i) : 2 * w i * (n i : ℝ)^2 * ω^2 / Real.pi^2 ≤
      w i * (1 - Real.cos ((n i : ℝ) * ω)) := by
    have hh := mul_le_mul_of_nonneg_left (one_sub_cos_quadratic (hsmall i)) (hw i)
    convert hh using 1
    ring
  have hh := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hpoint i)
  have he : (∑ i, 2 * w i * (n i : ℝ)^2 * ω^2 / Real.pi^2) =
      (2 * ω^2 / Real.pi^2) * ∑ i, w i * (n i : ℝ)^2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [he] at hh
  have hm := mul_le_mul_of_nonneg_left hmoment (show 0 ≤ 2 * ω^2 / Real.pi^2 by positivity)
  have hscale : k^2 * ω^2 / (3 * Real.pi^2) = (2 * ω^2 / Real.pi^2) * (k^2 / 6) := by ring
  rw [hscale]
  exact hm.trans hh

end polyak.FareyPlateau.LargeCurvature

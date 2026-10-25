import polyak.Energy.Certificate
import Mathlib.Algebra.BigOperators.Intervals

/-!
Article: Appendix A, the function-value boundary terms in Lemma energy.
Use: an exact cancellation identity and a uniform endpoint-window bound.
Proof: finite interval telescoping, the minimizer value bound, and the triangle inequality.
-/

noncomputable section

namespace polyak.Energy

open Duality Spectral

/-- Article: E_k, the discounted squared-norm window. -/
def window (b : ℕ → ℝ) (w k : ℕ) : ℝ :=
  ∑ l ∈ Finset.Icc (k-w) (k+w), b l

/-- Article: boundary windows contain nonnegative energy. -/
theorem window_nonneg {b : ℕ → ℝ} (hb : ∀ k, 0 ≤ b k) (w k : ℕ) :
    0 ≤ window b w k := Finset.sum_nonneg (fun l _ => hb l)

/-- Article: shifting a finite interval changes only its two boundary intervals.
Proof: write the four interval sums as differences of initial sums. -/
theorem interval_shift_difference (h : ℕ → ℝ) {i j : ℕ} (hij : i ≤ j) (n : ℕ) :
    ((∑ k ∈ Finset.Icc i j, h (k+n)) - ∑ k ∈ Finset.Icc i j, h k) =
      (∑ k ∈ Finset.Ico (j+1) (j+1+n), h k) -
        ∑ k ∈ Finset.Ico i (i+n), h k := by
  rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_add']
  rw [Finset.sum_Ico_eq_sub h (by omega : i+n ≤ j+1+n),
    Finset.sum_Ico_eq_sub h (by omega : i ≤ j+1),
    Finset.sum_Ico_eq_sub h (by omega : j+1 ≤ j+1+n),
    Finset.sum_Ico_eq_sub h (by omega : i ≤ i+n)]
  ring

/-- Article: the left value boundary is contained in its energy window. -/
theorem abs_sum_left_boundary_le {b h : ℕ → ℝ} (hb : ∀ k, 0 ≤ b k)
    {i n w : ℕ} (hn : n ≤ w) (hh : ∀ l, l ≤ i+w → |h l| ≤ b l / 2) :
    |∑ l ∈ Finset.Ico i (i+n), h l| ≤ window b w i / 2 := by
  calc
    _ ≤ ∑ l ∈ Finset.Ico i (i+n), |h l| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ l ∈ Finset.Ico i (i+n), b l / 2 := by
      apply Finset.sum_le_sum
      intro l hl
      exact hh l (by have := Finset.mem_Ico.mp hl; omega)
    _ ≤ ∑ l ∈ Finset.Icc (i-w) (i+w), b l / 2 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro l hl
        have := Finset.mem_Ico.mp hl
        exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
      · intro l _ _
        exact div_nonneg (hb l) (by norm_num)
    _ = _ := (Finset.sum_div _ _ _).symm

/-- Article: the right value boundary is contained in its energy window. -/
theorem abs_sum_right_boundary_le {b h : ℕ → ℝ} (hb : ∀ k, 0 ≤ b k)
    {j n w : ℕ} (hn : n ≤ w) (hh : ∀ l, l ≤ j+w → |h l| ≤ b l / 2) :
    |∑ l ∈ Finset.Ico (j+1) (j+1+n), h l| ≤ window b w j / 2 := by
  calc
    _ ≤ ∑ l ∈ Finset.Ico (j+1) (j+1+n), |h l| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ l ∈ Finset.Ico (j+1) (j+1+n), b l / 2 := by
      apply Finset.sum_le_sum
      intro l hl
      exact hh l (by have := Finset.mem_Ico.mp hl; omega)
    _ ≤ ∑ l ∈ Finset.Icc (j-w) (j+w), b l / 2 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro l hl
        have := Finset.mem_Ico.mp hl
        exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
      · intro l _ _
        exact div_nonneg (hb l) (by norm_num)
    _ = _ := (Finset.sum_div _ _ _).symm

/-- Article: each lag's telescoped value contribution is controlled by endpoint energy.
Use: no bound depends on the length of the interior interval. -/
theorem abs_interval_shift_difference_le {b h : ℕ → ℝ} (hb : ∀ k, 0 ≤ b k)
    {i j n w : ℕ} (hij : i ≤ j) (hn : n ≤ w)
    (hh : ∀ l, l ≤ j+w → |h l| ≤ b l / 2) :
    |(∑ k ∈ Finset.Icc i j, h (k+n)) - ∑ k ∈ Finset.Icc i j, h k| ≤
      (window b w i + window b w j) / 2 := by
  rw [interval_shift_difference h hij n]
  calc
    _ ≤ |∑ k ∈ Finset.Ico (j+1) (j+1+n), h k| +
        |∑ k ∈ Finset.Ico i (i+n), h k| := abs_sub _ _
    _ ≤ window b w j / 2 + window b w i / 2 := by
      exact add_le_add (abs_sum_right_boundary_le hb hn hh)
        (abs_sum_left_boundary_le hb hn (fun l hl => hh l (by omega)))
    _ = _ := by ring

/-- Article: K_h in Lemma energy. Use: an explicit finite value-boundary constant. -/
def valueBoundaryConstant {m : C(Frequency, ℂ)} {t : ℝ}
    (cert : StrictCertificate m t) : ℝ :=
  ∑ n ∈ cert.lags, Real.exp (n*t) * |cert.α n - cert.β n|

/-- Article: K_h is nonnegative. -/
theorem valueBoundaryConstant_nonneg {m : C(Frequency, ℂ)} {t : ℝ}
    (cert : StrictCertificate m t) : 0 ≤ valueBoundaryConstant cert := by
  apply Finset.sum_nonneg
  intro n _
  positivity

/-- Article: the complete function-value boundary estimate in Lemma energy.
Proof: exact charge cancellation, interval telescoping and the minimizer value bound. -/
theorem abs_sum_certificateValue_le {m : C(Frequency, ℂ)} {t : ℝ}
    (cert : StrictCertificate m t) {b h : ℕ → ℝ} (hb : ∀ k, 0 ≤ b k)
    {i j w : ℕ} (hij : i ≤ j) (hw : ∀ n ∈ cert.lags, n ≤ w)
    (hh : ∀ l, l ≤ j+w → |h l| ≤ b l / 2) :
    |∑ k ∈ Finset.Icc i j, certificateValue cert h k| ≤
      valueBoundaryConstant cert * (window b w i + window b w j) := by
  rw [sum_certificateValue]
  calc
    _ ≤ ∑ n ∈ cert.lags, |2 * Real.exp (n*t) * (cert.α n-cert.β n) *
        ((∑ k ∈ Finset.Icc i j, h (k+n)) - ∑ k ∈ Finset.Icc i j, h k)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ n ∈ cert.lags, Real.exp (n*t) * |cert.α n-cert.β n| *
        (window b w i + window b w j) := by
      apply Finset.sum_le_sum
      intro n hn
      rw [abs_mul, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2),
        abs_of_pos (Real.exp_pos _)]
      have he := mul_le_mul_of_nonneg_left
        (abs_interval_shift_difference_le hb hij (hw n hn) hh)
        (show 0 ≤ 2 * Real.exp (n*t) * |cert.α n-cert.β n| by positivity)
      nlinarith [he]
    _ = _ := by rw [← Finset.sum_mul]; rfl

end polyak.Energy

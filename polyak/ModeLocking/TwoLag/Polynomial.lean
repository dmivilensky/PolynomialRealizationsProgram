import polyak.Farey.Certificates.TwoLag
import Mathlib.Algebra.Polynomial.Div

/-! The removable quotient `(1-T_K)/(1-c)` is an actual polynomial,
including its value at the endpoint. -/
noncomputable section
namespace polyak.ModeLocking.TwoLag
open Polynomial Set
open Spectral (chebT chebU)

private theorem exists_W (K : ℕ) : ∃ W : ℝ[X],
    Polynomial.Chebyshev.T ℝ (K : ℤ) - 1 = (X - 1) * W := by
  have h : (X - C (1 : ℝ)) ∣ Polynomial.Chebyshev.T ℝ (K : ℤ) - 1 :=
    Polynomial.dvd_iff_isRoot.mpr (by
      simp [Polynomial.IsRoot, Polynomial.Chebyshev.T_eval_one])
  obtain ⟨W, hW⟩ := h
  exact ⟨W, by simpa using hW⟩

/-- The polynomial quotient, defined without a singularity at `c=1`. -/
def Wpoly (K : ℕ) : ℝ[X] := Classical.choose (exists_W K)
def W (K : ℕ) (c : ℝ) : ℝ := (Wpoly K).eval c

theorem Wpoly_identity (K : ℕ) :
    (1 - X) * Wpoly K = 1 - Polynomial.Chebyshev.T ℝ (K : ℤ) := by
  have h := Classical.choose_spec (exists_W K)
  dsimp [Wpoly]
  linear_combination h

theorem W_identity (K : ℕ) (c : ℝ) : (1-c)*W K c = 1-chebT K c := by
  have h := congrArg (Polynomial.eval c) (Wpoly_identity K)
  simpa [W, chebT] using h

theorem W_quotient (K : ℕ) {c : ℝ} (hc : c ≠ 1) :
    W K c = (1-chebT K c)/(1-c) := by
  apply (eq_div_iff (sub_ne_zero.mpr (Ne.symm hc))).mpr
  simpa [mul_comm] using W_identity K c

theorem W_one (K : ℕ) : W K 1 = (K : ℝ)^2 := by
  have h := congrArg (fun p : ℝ[X] => p.derivative.eval 1) (Wpoly_identity K)
  simp only [Polynomial.derivative_mul, Polynomial.derivative_sub,
    Polynomial.derivative_one, Polynomial.derivative_X, Polynomial.eval_add,
    Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_one, Polynomial.eval_X,
    sub_self, zero_mul, add_zero, zero_sub, Polynomial.eval_neg,
    Polynomial.Chebyshev.derivative_T_eval_one] at h
  dsimp [W]
  simpa only [neg_mul, one_mul, Int.cast_natCast, neg_inj] using h

theorem chebT_le_one (K : ℕ) {c : ℝ} (hc : c ∈ Icc (-1 : ℝ) 1) :
    chebT K c ≤ 1 := by
  have h := Real.cos_arccos hc.1 hc.2
  rw [← h]
  exact (Polynomial.Chebyshev.T_real_cos _ _).le.trans (Real.cos_le_one _)

theorem W_nonneg (K : ℕ) {c : ℝ} (hc : c ∈ Icc (-1 : ℝ) 1) : 0 ≤ W K c := by
  rcases eq_or_lt_of_le hc.2 with h | h
  · rw [h, W_one]; positivity
  · rw [W_quotient K (ne_of_lt h)]
    exact div_nonneg (sub_nonneg.mpr (chebT_le_one K hc)) (sub_nonneg.mpr h.le)

/-- The explicit rational comparison curve of Proposition `twolagtangency`. -/
def Psi (K : ℕ) (r c : ℝ) : ℝ :=
  (1+c)*(1-r*chebU (K-1) c)/(1+r*W K c)

theorem Psi_den_pos (K : ℕ) {r c : ℝ} (hr : 0 ≤ r)
    (hc : c ∈ Icc (-1 : ℝ) 1) : 0 < 1+r*W K c :=
  add_pos_of_pos_of_nonneg zero_lt_one (mul_nonneg hr (W_nonneg K hc))

theorem Psi_neg_one (K : ℕ) (r : ℝ) : Psi K r (-1) = 0 := by
  simp [Psi]

theorem Psi_one {K : ℕ} (hK : 1 ≤ K) (r : ℝ) :
    Psi K r 1 = 2*(1-r*K)/(1+r*(K : ℝ)^2) := by
  have hu : chebU (K-1) 1 = (K : ℝ) := by
    simp only [chebU, Polynomial.Chebyshev.U_eval_one, Int.cast_natCast]
    rw [Nat.cast_sub hK]
    ring
  simp only [Psi, W_one, hu]
  norm_num

end polyak.ModeLocking.TwoLag

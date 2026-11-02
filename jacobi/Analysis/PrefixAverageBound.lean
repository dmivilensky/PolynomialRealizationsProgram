import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
Article: jacobi, Proposition C.3.
A uniformly small error remains small after averaging over an actual
preceding-row prefix. The true prefix count is at most the matrix size.
Use: replacing actual Cholesky coefficients and support values by their proved uniform limits contributes a vanishing actual Schur-row error.
-/
namespace jacobi.Analysis
noncomputable section

/-- A finite prefix average is bounded by the common absolute bound on
its actual entries when the prefix count is at most the normalization.
Use: replacing actual Cholesky coefficients and support values by their
proved uniform limits contributes a vanishing actual Schur-row error.
Article: jacobi, Proposition C.3.
Proof: take the absolute finite sum, apply its entry bound and retain
the genuine prefix count before dividing by the positive matrix size. -/
theorem prefix_average_bound {m:ℕ} {N C:ℝ} (hN:0<N) (hm:(m:ℝ)≤N)
    (hC:0≤C) (f:Fin m→ℝ) (hf:∀j, |f j|≤C) : |(∑j, f j)/N|≤C := by
  -- The count bound is used only after all original prefix terms are retained.
  rw [abs_div,abs_of_pos hN]
  apply (div_le_iff₀ hN).mpr
  calc
    _ ≤ ∑j, |f j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑_:Fin m, C := Finset.sum_le_sum (fun j _ => hf j)
    _ ≤ C*N := by
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
      exact (mul_le_mul_of_nonneg_right hm hC).trans_eq (mul_comm _ _)

end
end jacobi.Analysis

import chebyshev1.Jacobi.Prefix
import chebyshev1.Jacobi.SpectralWeights

/-! Equal first spectral weights of the classical prefix Jacobi matrix. -/
namespace chebyshev1.Background
noncomputable section
open Polynomial Polynomial.Chebyshev

theorem prefix_first_weights (n : ℕ)
    (B : SpectralBasis (Prefix.jacobiData.matrix 0 (n+1)))
    (hi : Function.Injective B.eigenvalues) (j : Fin (n+1)) :
    B.weight 0 j = 1/(n+1 : ℝ) := by
  have hsq : ∀ t, 0 ≤ Prefix.jacobiData.aSq t := by
    intro t
    simp only [Prefix.jacobiData]
    split_ifs <;> norm_num
  have hf := Prefix.jacobiData.spectral_weight_cofactor B hsq hi 0 j
  simp only [Fin.val_zero, JacobiData.leading_zero, eval_one, one_mul,
    Nat.zero_add, Nat.sub_zero] at hf
  have hder : (Prefix.jacobiData.leading (n+1)).derivative.eval (B.eigenvalues j) =
      ((1/2 : ℝ)^n) * (n+1) * (U ℝ n).eval (B.eigenvalues j) := by
    rw [Prefix.jacobi_leading, derivative_mul, derivative_C, zero_mul, zero_add,
      T_derivative_eq_U]
    simp only [eval_mul, eval_C, eval_intCast]
    push_cast
    simp only [add_sub_cancel_right]
    ring
  have hd : (Prefix.jacobiData.leading (n+1)).derivative.eval (B.eigenvalues j) ≠ 0 := by
    rw [JacobiData.leading, Prefix.jacobiData.block_eq_charpoly hsq]
    exact B.charpoly_derivative_ne hi j
  rw [Prefix.jacobi_interior 1 n (by omega), eval_mul, eval_C, hder] at hf
  rw [hder] at hd
  have hu : ((1/2 : ℝ)^n) * (U ℝ n).eval (B.eigenvalues j) ≠ 0 := by
    intro hz
    apply hd
    calc
      _ = (n+1)*(((1/2 : ℝ)^n) * (U ℝ n).eval (B.eigenvalues j)) := by ring
      _ = 0 := by rw [hz, mul_zero]
  apply (eq_div_iff (by positivity : (n+1 : ℝ) ≠ 0)).mpr
  apply (mul_right_inj' hu).mp
  calc
    _ = B.weight 0 j * (((1/2 : ℝ)^n) * (n+1) * (U ℝ n).eval (B.eigenvalues j)) := by ring
    _ = _ := hf.trans (by ring)

end
end chebyshev1.Background

import jacobi.Finite.Reflection

/-!
Article: jacobi, Theorem C.5.
The genuine positive-coupling spectral reflection is exactly minus
conjugation by the original alternating-sign diagonal matrix.
Use: reflect_matrix states the actual source matrix reflection, and the two-edge Gram analysis retains the resulting original polynomial parity.
-/
namespace jacobi.Finite
noncomputable section
open Real Matrix chebyshev1 chebyshev2

/-- The original alternating-sign diagonal matrix in physical finite coordinates.
Use: reflect_matrix states the actual source matrix reflection, and the two-edge Gram analysis retains the resulting original polynomial parity.
Article: jacobi, Theorem C.5.
-/
def alternatingMatrix (n : ℕ) : Matrix (Fin n) (Fin n) ℝ := diagonal (fun i => (-1:ℝ)^i.val)

/-- Every original alternating sign has square one.
Use: reflect_matrix checks the genuine diagonal entries of the original alternating conjugation.
Article: jacobi, Theorem C.5.
Proof: its square is the original even power of minus one. -/
theorem alternating_sq (m : ℕ) : ((-1:ℝ)^m)^2=1 := by
  rw [← pow_mul,Nat.mul_comm,pow_mul]
  norm_num

/-- The product of two original adjacent alternating signs is minus one.
Use: reflect_matrix preserves the actual positive original adjacent entries under the source's signed conjugation.
Article: jacobi, Theorem C.5.
Proof: the next sign is the negative of the preceding sign, whose square is one. -/
theorem alternating_adjacent (m : ℕ) : (-1:ℝ)^m*(-1:ℝ)^(m+1)= -1 := by
  rw [pow_succ,← mul_assoc,← pow_two,alternating_sq]
  ring

/-- The genuine positive-coupling reflection is exactly the article's original signed alternating matrix conjugation.
Use: Support.naturalChain_swap_matrix gives the printed actual matrix statement, and its genuine spectral measure reflects with the first site unchanged.
Article: jacobi, Appendix C.3 (positive coefficients, persymmetry and spectrum).
Proof: diagonal entries acquire a minus sign since their actual alternating sign has square one. Each genuine adjacent pair has opposite signs, retaining its positive original entry. Every other tridiagonal entry is zero on both sides. -/
theorem reflect_matrix {n : ℕ} (J : Jacobi n) :
    (reflect J).matrix= -(alternatingMatrix n*J.matrix*alternatingMatrix n) := by
  -- The exact physical entry calculation retains positive couplings and the genuine zero matrix bands.
  ext i j
  have hi := i.isLt
  simp only [jacobi.Finite.reflect,affine,Jacobi.matrix,JacobiData.matrix_apply,Nat.zero_add,
    alternatingMatrix,Matrix.diagonal_mul,Matrix.mul_diagonal,Matrix.neg_apply,
    neg_one_sq,one_mul,add_zero,ite_eq_left hi]
  split_ifs with h0 h1 h2
  · subst j
    rw [mul_right_comm,← pow_two,alternating_sq]
    ring
  · rw [← h1,mul_right_comm,alternating_adjacent]
    ring
  · rw [← h2,mul_right_comm,mul_comm ((-1:ℝ)^(j.val+1)) ((-1:ℝ)^j.val),alternating_adjacent]
    ring
  · ring

end
end jacobi.Finite

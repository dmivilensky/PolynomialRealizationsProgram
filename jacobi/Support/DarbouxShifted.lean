import jacobi.Support.DarbouxOriginal
import jacobi.Support.DarbouxCoefficients

/-!
Article: jacobi, Appendix C.3 (positive coefficients, persymmetry and spectrum).
The second actual rectangular Gram matrix is the smaller original
support chain with alpha increased by two. Together with the first
Gram identity this proves the complete original cosine spectrum by
endpoint deletion, including every exceptional parameter value.
Use: supportDarboux_shifted identifies every genuine upper adjacent entry of the smaller rectangular Gram matrix.
-/
namespace jacobi.Support
noncomputable section
open Real Matrix jacobi.Reference chebyshev2
set_option backward.isDefEq.respectTransparency false

/-- The actual cross-row factor product is the positive coupling of the original smaller alpha-shifted support chain.
Use: supportDarboux_shifted identifies every genuine upper adjacent entry of the smaller rectangular Gram matrix.
Article: jacobi, Appendix C.3 (positive coefficients, persymmetry and spectrum).
Proof: combine the two genuine nonnegative square roots and use the independently proved exact original shifted birth-product identity. -/
theorem shifted_factor_product {a b : ℝ} (ha : -1<a) (hb : -1<b) {n m : ℕ} (hm : m<n) :
    lowerFactor a b n m*upperFactor a b n (m+1)=
      Real.sqrt (coefficientA (a+2) b n m*coefficientC (a+2) b n (m+1)/4) := by
  rw [lowerFactor,upperFactor,← Real.sqrt_mul (div_nonneg
    (coefficientC_pos ha hb (by omega : 0<m+1) (by omega : m+1<n+1)).le (by norm_num))]
  rw [coefficient_darboux_product]
  congr 1
  ring

/-- The actual smaller rectangular Gram factor is exactly the original alpha-shifted support matrix subtracted from the same original upper endpoint.
Use: support_charpoly_deletion applies the community rectangular characteristic identity to the two actual Gram factorizations and proves the complete original cosine spectrum.
Article: jacobi, Appendix C.3 (positive coefficients, persymmetry and spectrum).
Source: endpoint Christoffel/Darboux deletion, with both actual finite matrices identified here.
Proof: both matrices are genuinely symmetric. The actual row diagonal is (A_m+C_(m+1))/2, which is the shifted original diagonal by the proved exact sine quotient identity. The overlapping adjacent factors give the actual shifted support coupling; separated row supports give all remaining zero entries. -/
theorem supportDarboux_shifted (a b : ℝ) (ha : -1<a) (hb : -1<b) (n : ℕ) :
    supportDarbouxFactor a b n*(supportDarbouxFactor a b n).transpose=
      Matrix.scalar (Fin n) (cos (gamma a*step a b (n+1)))-
        (naturalChain (a+2) b (by linarith) hb n).matrix := by
  -- The same original top endpoint is retained; only the actual smaller chain's alpha index shifts.
  let R := supportDarbouxFactor a b n
  let J := naturalChain (a+2) b (by linarith : -1<a+2) hb n
  let y := cos (gamma a*step a b (n+1))
  change R*R.transpose=Matrix.scalar _ y-J.matrix
  have hR : (R*R.transpose).IsSymm := by
    change (R*R.transpose).transpose=R*R.transpose
    rw [transpose_mul,transpose_transpose]
  have hJ : (Matrix.scalar (Fin n) y-J.matrix).IsSymm := by
    change (Matrix.scalar _ y-J.matrix).transpose=Matrix.scalar _ y-J.matrix
    rw [transpose_sub,Matrix.scalar_apply,Matrix.diagonal_transpose,J.matrix_isHermitian.isSymm]
  apply symmetric_tridiagonal_ext _ _ hR hJ
  · intro i
    have he := bidiagonal_rows_diagonal n (upperFactor a b n) (lowerFactor a b n) i
    change (R*R.transpose) i i=_ at he
    rw [he,upperFactor_sq ha hb i.isLt.le,lowerFactor_sq ha hb i.isLt,Matrix.sub_apply]
    simp only [Matrix.scalar_apply,Matrix.diagonal_apply_eq]
    change _=y-(naturalChain (a+2) b (by linarith) hb n).matrix i i
    rw [naturalChain_matrix_diagonal,diagonal,step_darboux]
    have h := coefficient_darboux_diagonal ha hb i.isLt
    dsimp only [y]
    linear_combination h/2
  · intro i j hij
    have he := bidiagonal_rows_upper n (upperFactor a b n) (lowerFactor a b n) i j hij
    change (R*R.transpose) i j=_ at he
    rw [he]
    have hne : i≠j := by intro h; have := congrArg Fin.val h; omega
    rw [Matrix.sub_apply]
    simp only [Matrix.scalar_apply,Matrix.diagonal_apply_ne _ hne]
    change _=0-(naturalChain (a+2) b (by linarith) hb n).matrix i j
    rw [naturalChain_matrix_upper _ _ _ _ i j hij]
    rw [← hij,neg_mul,shifted_factor_product ha hb i.isLt]
    ring
  · intro i j hij
    have he := bidiagonal_rows_far n (upperFactor a b n) (lowerFactor a b n) i j (Or.inl hij)
    change (R*R.transpose) i j=0 at he
    rw [he,Matrix.sub_apply]
    have hne : i≠j := by intro h; have := congrArg Fin.val h; omega
    simp only [Matrix.scalar_apply,Matrix.diagonal_apply_ne _ hne]
    change 0=0-(naturalChain (a+2) b (by linarith) hb n).matrix i j
    rw [naturalChain_matrix_far _ _ _ _ i j (Or.inl hij),sub_zero]

end
end jacobi.Support

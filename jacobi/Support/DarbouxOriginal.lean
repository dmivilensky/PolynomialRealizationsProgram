import jacobi.Support.DarbouxFactors
import jacobi.Support.BidiagonalProducts
import jacobi.Support.MatrixEntries
import jacobi.Support.TridiagonalExt

/-!
Article: jacobi, Appendix C.3 (positive coefficients, persymmetry and spectrum).
The original support matrix has its exact positive rectangular Darboux
factorization. The actual upper endpoint is deleted by the same factor;
the following shifted-matrix identity then determines the full spectrum.
Use: supportDarboux_shifted and the rectangular characteristic identity prove the original complete support spectrum with no generic-position or spectral premise.
-/
namespace jacobi.Support
noncomputable section
open Real Matrix jacobi.Reference chebyshev2
set_option backward.isDefEq.respectTransparency false

/-- The genuine rectangular support factor gives exactly the original shifted natural support matrix in every dimension and for every original parameter pair.
Use: supportDarboux_shifted and the rectangular characteristic identity prove the original complete support spectrum with no generic-position or spectral premise.
Article: jacobi, Appendix C.3 (positive coefficients, persymmetry and spectrum).
Source: finite endpoint Christoffel/Darboux factorization, proved here for the original coefficients.
Proof: both matrices are genuinely symmetric. The actual column diagonal is (A_m+C_m)/2, including the proved boundary zeros, and the unique overlap of adjacent columns is the negative original square-root coupling. All other actual column overlaps vanish. -/
theorem supportDarboux_original (a b : ℝ) (ha : -1<a) (hb : -1<b) (n : ℕ) :
    (supportDarbouxFactor a b n).transpose*supportDarbouxFactor a b n=
      Matrix.scalar (Fin (n+1)) (cos (gamma a*step a b (n+1)))-(naturalChain a b ha hb (n+1)).matrix := by
  -- Every entry is computed for the actual original finite matrix, and the original terminal-zero proof covers n=0 as well.
  let R := supportDarbouxFactor a b n
  let J := naturalChain a b ha hb (n+1)
  let y := cos (gamma a*step a b (n+1))
  change R.transpose*R=Matrix.scalar _ y-J.matrix
  have hR : (R.transpose*R).IsSymm := by
    change (R.transpose*R).transpose=R.transpose*R
    rw [transpose_mul,transpose_transpose]
  have hJ : (Matrix.scalar (Fin (n+1)) y-J.matrix).IsSymm := by
    change (Matrix.scalar _ y-J.matrix).transpose=Matrix.scalar _ y-J.matrix
    rw [transpose_sub,Matrix.scalar_apply,Matrix.diagonal_transpose,J.matrix_isHermitian.isSymm]
  apply symmetric_tridiagonal_ext _ _ hR hJ
  · intro i
    have he := bidiagonal_columns_diagonal n (upperFactor a b n) (lowerFactor a b n) i
    change (R.transpose*R) i i=_ at he
    rw [he]
    have hA : (if (i:ℕ)<n then (upperFactor a b n i)^2 else 0)=coefficientA a b (n+1) i/2 := by
      by_cases hi : (i:ℕ)<n
      · rw [ite_eq_left hi,upperFactor_sq ha hb hi.le]
      · have hn : (i:ℕ)=n := by omega
        rw [ite_eq_right hi,hn,← upperFactor_sq ha hb le_rfl,upperFactor_terminal a b ha hb n]
        norm_num
    have hC : (if 0<(i:ℕ) then (lowerFactor a b n ((i:ℕ)-1))^2 else 0)=coefficientC a b (n+1) i/2 := by
      by_cases hi : 0<(i:ℕ)
      · rw [ite_eq_left hi,lowerFactor_sq ha hb (by omega),Nat.sub_add_cancel hi]
      · have hz : (i:ℕ)=0 := by omega
        rw [ite_eq_right hi,hz,coefficientC_zero,zero_div]
    rw [hA,hC,Matrix.sub_apply]
    simp only [Matrix.scalar_apply,Matrix.diagonal_apply_eq]
    change _=y-(naturalChain a b ha hb (n+1)).matrix i i
    rw [naturalChain_matrix_diagonal]
    dsimp only [y,diagonal]
    ring
  · intro i j hij
    have he := bidiagonal_columns_upper n (upperFactor a b n) (lowerFactor a b n) i j hij
    change (R.transpose*R) i j=_ at he
    rw [he]
    have hne : i≠j := by intro h; have := congrArg Fin.val h; omega
    rw [Matrix.sub_apply]
    simp only [Matrix.scalar_apply,Matrix.diagonal_apply_ne _ hne]
    change _=0-(naturalChain a b ha hb (n+1)).matrix i j
    rw [naturalChain_matrix_upper a b ha hb i j hij,neg_mul,factor_product ha hb (by omega)]
    ring
  · intro i j hij
    have he := bidiagonal_columns_far n (upperFactor a b n) (lowerFactor a b n) i j (Or.inl hij)
    change (R.transpose*R) i j=0 at he
    rw [he,Matrix.sub_apply]
    have hne : i≠j := by intro h; have := congrArg Fin.val h; omega
    simp only [Matrix.scalar_apply,Matrix.diagonal_apply_ne _ hne]
    change 0=0-(naturalChain a b ha hb (n+1)).matrix i j
    rw [naturalChain_matrix_far a b ha hb i j (Or.inl hij),sub_zero]

end
end jacobi.Support

import jacobi.Finite.Reconstruction

/-!
Article: jacobi, Equation (1.3) (unique persymmetric realization and its weights).
The first-site spectral probabilities determine the whole irreducible Jacobi
matrix once its distinct eigenvalues are fixed. The proof reuses the cofactor
and inverse-continuant results from chebyshev1 rather than reconstructing them.
Source: de Boor and Golub, finite inverse spectral reconstruction.
Use: the spectral-weight chart and both inverse identities are independent of the chosen basis.
-/

namespace jacobi.Finite
noncomputable section
open chebyshev1 chebyshev2 Polynomial Matrix
set_option backward.isDefEq.respectTransparency false

/-- First-site weights are independent of eigenvector signs or basis choices at fixed simple nodes.
Use: the spectral-weight chart and both inverse identities are independent of the chosen basis.
Article: jacobi, Equation (1.3) (unique persymmetric realization and its weights).
Proof: both weights multiply the same nonzero characteristic derivative to give
the same endpoint cofactor. -/
theorem basis_weights_independent {n : ℕ} (J : Jacobi (n+1))
    (B C : SpectralBasis J.matrix) (he : B.eigenvalues = C.eigenvalues)
    (hi : Function.Injective B.eigenvalues) (k : Fin (n+1)) : B.weight 0 k = C.weight 0 k := by
  -- The cofactor and characteristic derivative do not depend on the signs of the chosen eigenvectors.
  have hiC : Function.Injective C.eigenvalues := he ▸ hi
  have hb := J.data.spectral_weight_cofactor B J.coupling_nonneg hi (0 : Fin (n+1)) k
  have hc := J.data.spectral_weight_cofactor C J.coupling_nonneg hiC (0 : Fin (n+1)) k
  simp only [Fin.val_zero, JacobiData.leading_zero, eval_one, one_mul, Nat.zero_add,
    Nat.sub_zero] at hb hc
  rw [← he] at hc
  have hd : (J.data.leading (n+1)).derivative.eval (B.eigenvalues k) ≠ 0 := by
    rw [JacobiData.leading, J.data.block_eq_charpoly J.coupling_nonneg]
    exact B.charpoly_derivative_ne hi k
  exact mul_right_cancel₀ hd (hb.trans hc.symm)

/-- Equal distinct spectral nodes and first-site weights determine the entire finite chain.
Use: the uniqueness direction of the open-simplex parametrization and the unique
persymmetric realization obtained from reciprocal derivative weights.
Article: jacobi, Equation (1.3) (unique persymmetric realization and its weights).
Proof: the first-site cofactor fixes the trailing characteristic polynomial at
every eigenvalue. Degree bounds identify that polynomial, after which the existing
inverse-continuant theorem recovers every finite coefficient and its canonical tails. -/
theorem unique_of_spectral_weights {n : ℕ} (J K : Jacobi (n+1)) (hJ : J.Irreducible)
    (BJ : SpectralBasis J.matrix) (BK : SpectralBasis K.matrix)
    (he : BJ.eigenvalues = BK.eigenvalues) (hi : Function.Injective BJ.eigenvalues)
    (hw : ∀ k, BJ.weight 0 k = BK.weight 0 k) : J = K := by
  have hP : J.data.leading (n+1) = K.data.leading (n+1) := by
    simp only [JacobiData.leading,
      J.data.block_eq_charpoly J.coupling_nonneg, K.data.block_eq_charpoly K.coupling_nonneg]
    change J.matrix.charpoly = K.matrix.charpoly
    rw [BJ.charpoly_factor, BK.charpoly_factor, he]
  have hiK : Function.Injective BK.eigenvalues := he ▸ hi
  -- Compare the actual endpoint cofactors at every distinct eigenvalue.
  have hval (k : Fin (n+1)) :
      (J.data.block 1 n - K.data.block 1 n).eval (BJ.eigenvalues k) = 0 := by
    have hj := J.data.spectral_weight_cofactor BJ J.coupling_nonneg hi (0 : Fin (n+1)) k
    have hk := K.data.spectral_weight_cofactor BK K.coupling_nonneg hiK (0 : Fin (n+1)) k
    simp only [Fin.val_zero, JacobiData.leading_zero, eval_one, one_mul, Nat.zero_add,
      Nat.sub_zero] at hj hk
    rw [← he, ← hP, ← hw k] at hk
    rw [eval_sub]
    exact sub_eq_zero.mpr (hj.symm.trans hk)
  have hdeg : (J.data.block 1 n - K.data.block 1 n).natDegree < n+1 := by
    apply lt_of_le_of_lt (natDegree_sub_le _ _)
    rw [J.data.block_natDegree J.coupling_nonneg, K.data.block_natDegree K.coupling_nonneg,
      max_self]
    omega
  have htail : J.data.block 1 n = K.data.block 1 n := sub_eq_zero.mp
    (Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero _ hi hval (by simpa using hdeg))
  -- The existing inverse-continuant theorem now recovers the coefficient arrays.
  have hc := J.data.block_pair_unique K.data J.coupling_nonneg K.coupling_nonneg n 0 0
    (fun s hs hsN => by simpa using hJ s hs (by omega)) hP htail
  have hb : J.data.b = K.data.b := by
    funext i
    by_cases hi : i ≤ n
    · simpa using hc.1 i hi
    · rw [J.diagonal_tail i (by omega), K.diagonal_tail i (by omega)]
  have ha : J.data.aSq = K.data.aSq := by
    funext i
    by_cases hi0 : i = 0
    · subst i
      rw [J.coupling_zero, K.coupling_zero]
    by_cases hi : i ≤ n
    · simpa using hc.2 i (by omega) hi
    · rw [J.coupling_tail i (by omega), K.coupling_tail i (by omega)]
  apply Jacobi.ext
  have hd (D E : JacobiData) (hb : D.b = E.b) (ha : D.aSq = E.aSq) : D = E := by
    cases D
    cases E
    simp_all
  exact hd _ _ hb ha

end
end jacobi.Finite

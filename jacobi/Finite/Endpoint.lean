import jacobi.Finite.ReversalWeights

/-!
Article: jacobi, Proposition C.3.
The signed endpoint identity is obtained from the off-diagonal cofactor, rather
than taking a square root of the squared identity. Retaining the sign is essential
for the alternating parity of persymmetric eigenvectors.
Source: the adjugate cofactor formula for a finite tridiagonal matrix.
Use: specializes to the two endpoints of a Jacobi chain.
-/
namespace jacobi.Finite
noncomputable section
open chebyshev1 chebyshev2 Matrix
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- The off-diagonal eigenvalue cofactor retains the signs of both eigenvector entries.
Use: specializes to the two endpoints of a Jacobi chain.
Article: jacobi, Proposition C.3.
Proof: at a simple eigenvalue all terms in the adjugate spectral expansion except
its own spectral column vanish. -/
theorem adjugate_eigenvalue_entry {N : ℕ} {A : Matrix (Fin N) (Fin N) ℝ}
    (B : SpectralBasis A) (i l k : Fin N) :
    (Matrix.scalar _ (B.eigenvalues k)-A).adjugate i l =
      B.Q i k * B.Q l k * A.charpoly.derivative.eval (B.eigenvalues k) := by
  -- Only the selected spectral column survives evaluation of the adjugate at its eigenvalue.
  rw [B.adjugate_shift, Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply]
  rw [Finset.sum_eq_single k]
  · rw [B.charpoly_derivative]
    ring
  · intro j _ hj
    have hz : (∏ t ∈ Finset.univ.erase j, (B.eigenvalues k-B.eigenvalues t)) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hj.symm, Finset.mem_univ k⟩)
      simp
    rw [hz, mul_zero, zero_mul]
  · simp

/-- The endpoint adjugate entry is the positive product of the internal couplings.
Use: determines the sign in the endpoint spectral identity.
Article: jacobi, Proposition C.3.
Proof: deleting the last row and first column leaves a lower triangular matrix
with diagonal -a_i; its n signs cancel the cofactor sign. -/
theorem endpoint_adjugate {n : ℕ} (J : Jacobi (n+1)) (x : ℝ) :
    (Matrix.scalar _ x-J.matrix).adjugate 0 (Fin.last n) =
      ∏ i : Fin n, Real.sqrt (J.data.aSq (i.val+1)) := by
  -- The deleted endpoint minor is lower triangular; its negative diagonal signs cancel the cofactor sign.
  let A := Matrix.scalar (Fin (n+1)) x-J.matrix
  let M := A.submatrix Fin.castSucc Fin.succ
  have ht : M.IsLowerTriangular := by
    intro i j hij
    have hv : i.val < j.val := hij
    have hne : i.castSucc ≠ j.succ := by intro he; have := congrArg Fin.val he; simp at this; omega
    change (if i.castSucc = j.succ then x else 0) - J.data.matrix 0 (n+1) i.castSucc j.succ = 0
    rw [ite_eq_right hne, JacobiData.matrix_apply, ite_eq_right hne]
    simp only [Fin.val_castSucc, Fin.val_succ, Nat.zero_add]
    have h1 : ¬ (i.val+1 = j.val+1) := by omega
    have h2 : ¬ (j.val+1+1 = i.val) := by omega
    rw [ite_eq_right h1, ite_eq_right h2, sub_zero]
  have hd (i : Fin n) : M i i = -Real.sqrt (J.data.aSq (i.val+1)) := by
    have hne : i.castSucc ≠ i.succ := by intro he; have := congrArg Fin.val he; simp at this
    simp [M, A, Matrix.scalar, hne, Jacobi.matrix,
      JacobiData.matrix_apply]
  rw [Matrix.adjugate_fin_succ_eq_det_submatrix]
  simp only [Fin.val_zero, Fin.val_last, Fin.succAbove_last, Fin.succAbove_zero]
  change (-1 : ℝ)^n * M.det = _
  rw [Matrix.det_of_isLowerTriangular M ht]
  simp_rw [hd]
  rw [Finset.prod_neg, Finset.card_univ, Fintype.card_fin]
  have hsign : (-1 : ℝ)^n * (-1)^n = 1 := by rw [← pow_add, ← two_mul, pow_mul]; simp
  rw [← mul_assoc, hsign, one_mul]

/-- The full signed endpoint residue identity for an arbitrary Jacobi fibre matrix.
Use: proves the alternating eigenvector parity at the unique persymmetric point.
Article: jacobi, Proposition C.3.
Proof: equate the spectral adjugate entry and the explicit endpoint cofactor. -/
theorem spectral_endpoint_signed {n : ℕ} (J : Jacobi (n+1)) (B : SpectralBasis J.matrix)
    (k : Fin (n+1)) :
    B.Q 0 k * B.Q (Fin.last n) k * J.matrix.charpoly.derivative.eval (B.eigenvalues k) =
      ∏ i : Fin n, Real.sqrt (J.data.aSq (i.val+1)) := by
  rw [← adjugate_eigenvalue_entry B 0 (Fin.last n) k, endpoint_adjugate]

end
end jacobi.Finite

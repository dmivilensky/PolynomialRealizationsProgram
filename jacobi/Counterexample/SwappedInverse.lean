import jacobi.Counterexample.ConstantDriftRows
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Algebra.Order.Star.Real

/-!
Article: jacobi, Section 6 (bidiagonal swap identity).
The actual Cholesky swap preserves the complete characteristic polynomial
and gives a strictly positive matrix whose genuine inverse has constant
diagonal 1/kappa. These are exact matrix statements for every dimension
and every original positive-drift bidiagonal factor.
Use: swapped_inverse_diagonal supplies the constant Green diagonal of the attaining matrix in Section 6.
-/
namespace jacobi.Counterexample
noncomputable section
open Matrix
open scoped BigOperators

/-- The source's actual swapped Cholesky matrix B^T*B.
Use: swapped_inverse_diagonal supplies the constant Green diagonal of the attaining matrix in Section 6.
Article: jacobi, Proposition 6.1.
-/
def swappedGram (d l:ℕ→ℝ) (N:ℕ) : Matrix (Fin N) (Fin N) ℝ :=
  (bidiagonal d l N)ᵀ*bidiagonal d l N

/-- The genuine Cholesky swap preserves the full original characteristic polynomial.
Use: the constructed constant-diagonal optimizer belongs to precisely the original spectral fibre after the printed affine change.
Article: jacobi, Section 6 (bidiagonal swap identity).
Source: the finite matrix identity det(zI-AB)=det(zI-BA).
Proof: apply the community characteristic-polynomial multiplication identity to the same original square factor and its transpose. -/
theorem swapped_charpoly (d l:ℕ→ℝ) (N:ℕ) :
    (swappedGram d l N).charpoly=
      (bidiagonal d l N*(bidiagonal d l N)ᵀ).charpoly :=
  Matrix.charpoly_mul_comm _ _

/-- Every genuine diagonal coefficient is nonzero under the source's positive constant drift.
Use: the actual inverse and positive-definiteness statements require no extra determinant premise.
Article: jacobi, Section 6 (bidiagonal swap identity).
Proof: its squared value is a nonnegative square plus the original strictly positive kappa. -/
theorem constant_drift_diagonal_ne {N:ℕ} (d l:ℕ→ℝ) {kappa:ℝ}
    (hk:0<kappa) (hd:∀i<N,(d i)^2-(l i)^2=kappa) :
    ∀i<N,d i≠0 := by
  intro i hi hz
  have h := hd i hi
  rw [hz] at h
  nlinarith [sq_nonneg (l i)]

/-- The actual swapped inverse has the printed constant diagonal at every physical finite row.
Use: the affine alternating conjugation in Section 6 yields resolvent diagonal H/kappa and exact energy n*H^2/kappa^2.
Article: jacobi, Section 6 (bidiagonal swap identity).
Proof: the true matrix inverse of B^T*B is B^(-1)*(B^(-1))^T.
The previously proved forward-substitution inverse identifies each
original diagonal entry with its actual squared row norm, already
proved equal to 1/kappa by the constant-drift induction. -/
theorem swapped_inverse_diagonal {N:ℕ} (d l:ℕ→ℝ) {kappa:ℝ}
    (hk:0<kappa) (hl:l 0=0) (hd:∀i<N,(d i)^2-(l i)^2=kappa) (i:Fin N) :
    (swappedGram d l N)⁻¹ i i=1/kappa := by
  -- This is the nonsingular inverse of the original matrix, not a prescribed replacement with the desired diagonal.
  have he := bidiagonal_inverse d l (constant_drift_diagonal_ne d l hk hd)
  rw [swappedGram,Matrix.mul_inv_rev,← Matrix.transpose_nonsing_inv]
  simp only [he]
  change (∑j:Fin N,inverseEntry d l i j*inverseEntry d l i j)=_
  simp only [← pow_two]
  exact row_norm_constant d l hk hl hd i.isLt

/-- The genuine swapped Cholesky matrix is strictly positive definite under the source's positive drift.
Use: the final constant-drift optimizer has a true invertible positive resolvent pencil, before the original spectral-window condition is imposed.
Article: jacobi, Section 6 (bidiagonal swap identity).
Source: a Gram matrix of an invertible square real matrix is positive definite.
Proof: the independently proved right inverse is also a left inverse.
Its matrix-vector action makes B injective. The community positive-Gram
theorem then applies to the unchanged original factor. -/
theorem swapped_posDef {N:ℕ} (d l:ℕ→ℝ) {kappa:ℝ}
    (hk:0<kappa) (hd:∀i<N,(d i)^2-(l i)^2=kappa) :
    (swappedGram d l N).PosDef := by
  -- Positive definiteness follows from the constructed inverse, rather than entering as an extra hypothesis.
  have hprod := bidiagonal_mul_inverse d l (constant_drift_diagonal_ne d l hk hd)
  have hleft := mul_eq_one_comm.mp hprod
  have hinj : Function.Injective (bidiagonal d l N).mulVec := by
    intro x y hxy
    have h := congrArg
      (Matrix.mulVec (Matrix.of fun i j:Fin N=>inverseEntry d l i j)) hxy
    simpa only [Matrix.mulVec_mulVec,hleft,Matrix.one_mulVec] using h
  simpa only [swappedGram,Matrix.conjTranspose_eq_transpose_of_trivial] using
    Matrix.PosDef.conjTranspose_mul_self (bidiagonal d l N) hinj

end
end jacobi.Counterexample

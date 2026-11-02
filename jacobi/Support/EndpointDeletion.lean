import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.Tactic

/-!
Article: jacobi, Appendix C.3 (positive coefficients, persymmetry and spectrum).
The community rectangular characteristic identity proves endpoint
Darboux deletion for actual finite matrices. The support application
discharges both Gram identities with its original sine coefficients.
Use: endpoint_charpoly_deletion translates Sylvester's genuine rectangular Gram identity back to the original Jacobi spectral variable.
-/
namespace jacobi.Support
noncomputable section
open Matrix Polynomial

/-- The actual shifted finite characteristic evaluated at the reflected spectral coordinate has its precise original determinant sign.
Use: endpoint_charpoly_deletion translates Sylvester's genuine rectangular Gram identity back to the original Jacobi spectral variable.
Article: jacobi, Appendix C.3 (positive coefficients, persymmetry and spectrum).
Source: the characteristic determinant and determinant of a negative matrix.
Proof: the genuine characteristic matrix at y-x is exactly minus the original characteristic matrix at x; its actual finite dimension determines the sign. -/
theorem shifted_charpoly_eval {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (y x : ℝ) :
    (Matrix.scalar (Fin n) y-A).charpoly.eval (y-x)=(-1:ℝ)^n*A.charpoly.eval x := by
  -- Both characteristic polynomials refer to the actual original finite matrices, rather than an asserted eigenvalue correspondence.
  rw [Matrix.eval_charpoly,Matrix.eval_charpoly]
  have he : Matrix.scalar (Fin n) (y-x)-(Matrix.scalar (Fin n) y-A)=
      -(Matrix.scalar (Fin n) x-A) := by
    ext i j
    simp only [Matrix.sub_apply,Matrix.neg_apply,Matrix.scalar_apply,Matrix.diagonal_apply]
    split_ifs <;> ring
  rw [he,Matrix.det_neg,Fintype.card_fin]

/-- The genuine two rectangular Darboux Gram factorizations delete exactly one actual original endpoint from the entire finite characteristic polynomial.
Use: naturalChain_charpoly_deletion applies this elementary result to the independently proved actual support factorizations and determines the complete original cosine spectrum inductively.
Article: jacobi, Appendix C.3 (positive coefficients, persymmetry and spectrum).
Source: Sylvester's determinant identity, mathlib Matrix.charpoly_mul_comm_of_le.
Proof: apply the proved rectangular characteristic identity to R^T,R. Evaluate at the original reflected spectral coordinate y-x and use the exact determinant signs. The genuine nonzero sign factor cancels, giving the original polynomial factor X-y. -/
theorem endpoint_charpoly_deletion {n : ℕ} (R : Matrix (Fin n) (Fin (n+1)) ℝ)
    (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (B : Matrix (Fin n) (Fin n) ℝ) (y : ℝ)
    (hA : R.transpose*R=Matrix.scalar (Fin (n+1)) y-A)
    (hB : R*R.transpose=Matrix.scalar (Fin n) y-B) :
    A.charpoly=(X-C y)*B.charpoly := by
  -- No eigenvalue hypothesis is used: the genuine complete characteristic equality follows from the two actual matrix products.
  have hc := Matrix.charpoly_mul_comm_of_le R.transpose R (by simp : Fintype.card (Fin n)≤Fintype.card (Fin (n+1)))
  simp only [Fintype.card_fin,Nat.add_sub_cancel_left,pow_one] at hc
  rw [hA,hB] at hc
  apply Polynomial.funext
  intro x
  have he := congrArg (fun P : ℝ[X] => P.eval (y-x)) hc
  simp only [Polynomial.eval_mul,Polynomial.eval_X,shifted_charpoly_eval,pow_succ] at he
  simp only [Polynomial.eval_mul,Polynomial.eval_sub,Polynomial.eval_X,Polynomial.eval_C]
  apply mul_left_cancel₀ (pow_ne_zero n (by norm_num : (-1:ℝ)≠0))
  linear_combination -he

end
end jacobi.Support

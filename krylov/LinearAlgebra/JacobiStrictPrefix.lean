import krylov.LinearAlgebra.JacobiKernel
import Mathlib.Algebra.Order.Star.Real
set_option autoImplicit false
/-!
Article: main_krylov, prop:phi(a), strict genuine Jacobi prefix spectral margin.
Use: obtain strict Ritz endpoint bounds from one actual additional active Jacobi site.
Source: positive semidefinite zero-form kernel equivalence and actual irreducible tridiagonal backward substitution.
-/

namespace krylov.LinearAlgebra
noncomputable section
open Matrix
open scoped BigOperators
variable {N : ℕ}

/-- The actual proper leading prefix of a positive semidefinite irreducible Jacobi matrix is positive definite.
Use: The actual proper leading prefix of a positive semidefinite irreducible Jacobi matrix is positive definite.
Article: main_krylov, prop:phi(a), strict genuine Jacobi prefix spectral margin.
Proof: Pad a hypothetical true zero-form vector by an actual zero final coordinate; positivity makes it a genuine whole null vector and the original adjacent rows force it to vanish. -/
theorem jacobi_strict_prefix (M : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) (hM : M.PosSemidef)
    (htri : ∀ i j : Fin (N+1),i.val+1 < j.val ∨ j.val+1 < i.val → M i j=0)
    (hedge : ∀ i j : Fin (N+1),i.val+1=j.val → M j i≠0) :
    (M.submatrix Fin.castSucc Fin.castSucc).PosDef := by
  -- Pad the genuine prefix zero-form vector by its actual zero last coordinate.
  let A := M.submatrix Fin.castSucc Fin.castSucc
  have hA : A.PosSemidef := hM.submatrix Fin.castSucc
  apply Matrix.PosDef.of_dotProduct_mulVec_pos hA.1
  intro x hx
  have hnonneg := hA.dotProduct_mulVec_nonneg x
  by_contra hn
  have hxform : star x ⬝ᵥ A *ᵥ x=0 := le_antisymm (le_of_not_gt hn) hnonneg
  let z : Fin (N+1) → ℝ := Fin.snoc x 0
  -- Its actual whole quadratic form equals the original prefix form exactly.
  have hzform : star z ⬝ᵥ M *ᵥ z=star x ⬝ᵥ A *ᵥ x := by
    simp only [dotProduct,Pi.star_apply,star_trivial,Matrix.mulVec]
    rw [Fin.sum_univ_castSucc]
    simp only [z,Fin.snoc_castSucc,Fin.snoc_last,zero_mul,add_zero]
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.snoc_castSucc,Fin.snoc_last,mul_zero,add_zero]
    rfl
  -- Positive semidefiniteness turns the true zero form into a real null vector before backward substitution.
  have hzk : M *ᵥ z=0 := hM.dotProduct_mulVec_zero_iff.mp (hzform.trans hxform)
  have hz : z=0 := tridiagonal_kernel_last M htri hedge z hzk (by
    intro i hi
    have he : i=Fin.last N := Fin.ext (by simpa using Nat.add_right_cancel hi)
    rw [he]
    exact Fin.snoc_last _ _)
  apply hx
  ext i
  have h := congrFun hz i.castSucc
  simpa only [z,Fin.snoc_castSucc,Pi.zero_apply] using h
end
end krylov.LinearAlgebra

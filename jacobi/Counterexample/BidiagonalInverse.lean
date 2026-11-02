import chebyshev2.Green.Bidiagonal
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
Article: jacobi, Section 6 (bidiagonal swap identity).
The inverse of the original lower bidiagonal Cholesky factor is
constructed by its literal row recursion. The full matrix inverse and
the lower-triangular support are proved, before squared row norms are
used to produce the source's constant inverse diagonal.
Use: bidiagonal_inverse identifies these explicit entries with B^(-1); row_norm_succ obtains the exact constant-drift recursion.
-/
namespace jacobi.Counterexample
noncomputable section
open Matrix
open scoped BigOperators

/-- The actual forward-substitution inverse row for the original bidiagonal coefficients.
Use: bidiagonal_inverse identifies these explicit entries with B^(-1); row_norm_succ obtains the exact constant-drift recursion.
Article: jacobi, Section 6 (bidiagonal swap identity).
-/
def inverseEntry (d l:ℕ→ℝ) : ℕ→ℕ→ℝ
  | 0,j => (if j=0 then 1 else 0)/d 0
  | i+1,j => ((if j=i+1 then 1 else 0)-l (i+1)*inverseEntry d l i j)/d (i+1)

/-- Every genuine inverse row vanishes strictly above its original diagonal.
Use: row_norm_succ eliminates the cross term against the new unit coordinate, exactly as in the source proof.
Article: jacobi, Section 6 (bidiagonal swap identity).
Proof: the zeroth row has singleton support; each next row combines its predecessor with the new coordinate vector. -/
theorem inverseEntry_support (d l:ℕ→ℝ) {i j:ℕ} (h:i<j) : inverseEntry d l i j=0 := by
  induction i with
  | zero => simp only [inverseEntry,ite_eq_right (by omega : j≠0),zero_div]
  | succ i ih =>
    rw [inverseEntry,ite_eq_right (by omega : j≠i+1),ih (by omega)]
    ring

/-- The original lower bidiagonal matrix on the stated finite physical interval.
Use: bidiagonal_inverse and swapped_inverse_diagonal retain the same original finite matrix throughout the swap argument.
Article: jacobi, Section 6 (bidiagonal swap identity).
-/
def bidiagonal (d l:ℕ→ℝ) (N:ℕ) : Matrix (Fin N) (Fin N) ℝ :=
  chebyshev2.Bidiagonal.matrix (fun i=>d i) (fun i=>l i)

/-- The explicit forward-substitution rows form a true right inverse of the original finite bidiagonal matrix.
Use: bidiagonal_inverse identifies the actual nonsingular inverse without assuming invertibility or triangularity of that inverse.
Article: jacobi, Section 6 (bidiagonal swap identity).
Proof: the earlier article's exact two-term row multiplication gives
the original forward-substitution equation. Cancel the genuine nonzero
diagonal in each positive row and in the zeroth row. -/
theorem bidiagonal_mul_inverse {N:ℕ} (d l:ℕ→ℝ) (hd:∀i<N,d i≠0) :
    bidiagonal d l N*(Matrix.of fun i j:Fin N=>inverseEntry d l i j)=1 := by
  -- Forward substitution proves invertibility rather than relying on an unverified inverse formula.
  classical
  ext i j
  change (∑k:Fin N,chebyshev2.Bidiagonal.matrix (fun i=>d i) (fun i=>l i) i k*
    inverseEntry d l k j)=(if i=j then 1 else 0)
  rw [chebyshev2.Bidiagonal.row_mul]
  dsimp only
  by_cases hi : 0 < i.val
  · rw [dite_eq_left hi]
    have he : inverseEntry d l i j=
        ((if j.val=i.val then 1 else 0)-l i*inverseEntry d l (i.val-1) j)/d i := by
      conv_lhs => rw [show i.val=(i.val-1)+1 by omega,inverseEntry]
      simp only [show i.val-1+1=i.val by omega]
    rw [he]
    have hj : j.val=i.val ↔ i=j := by rw [Fin.ext_iff]; exact eq_comm
    simp only [hj]
    field_simp [hd i i.isLt]
    ring
  · have hi0 : i.val=0 := by omega
    have hj : j.val=0 ↔ i=j := by rw [← hi0,Fin.ext_iff]; exact eq_comm
    rw [dite_eq_right hi,hi0,inverseEntry]
    simp only [hj]
    field_simp [hd 0 (by omega)]
    ring

/-- The original matrix inverse is exactly the proved forward-substitution construction.
Use: swapped_inverse_diagonal computes the actual inverse of B^T*B through its genuine inverse rows.
Article: jacobi, Section 6 (bidiagonal swap identity).
Proof: uniqueness of a right inverse over a finite square matrix applies to the independently proved original product BX=I. -/
theorem bidiagonal_inverse {N:ℕ} (d l:ℕ→ℝ) (hd:∀i<N,d i≠0) :
    (bidiagonal d l N)⁻¹=(fun i j:Fin N=>inverseEntry d l i j) :=
  Matrix.inv_eq_right_inv (bidiagonal_mul_inverse d l hd)

end
end jacobi.Counterexample

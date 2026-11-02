import jacobi.Finite.GreenEntries

/-!
The discrete Green factorization by a positive endpoint solution.
The inverse of the forward difference matrix is the upper cumulative-sum
matrix. Conjugating its weighted Gram matrix by the endpoint solution
gives the exact finite Green kernel as a tail sum of inverse conductances.
Use: StandardJacobi supplies the classical endpoint solution and estimates
these actual tail sums to obtain its uniform kernel and energy limits.
Article: jacobi, Theorem 5.4, Equation (5.9).
Article role: the weighted first-difference Green inverse.
Source: Meurant, A review on the inverse of symmetric tridiagonal and block tridiagonal matrices
(1992): tridiagonal Green factorization.
-/
namespace jacobi.Finite.StandardGreen
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Matrix

/-- The upper cumulative-sum matrix. Its rows sum from their index to
the last vertex; the absent final vertex has Dirichlet value zero.
Article: jacobi, Theorem 5.4, Equation (5.9).
Source: Meurant, A review on the inverse of symmetric tridiagonal and block tridiagonal matrices
(1992): tridiagonal Green factorization.
-/
def tailMatrix (N : ℕ) : Matrix (Fin N) (Fin N) ℝ :=
  fun i j => if i≤j then 1 else 0

/-- The forward one-step shift, with zero beyond the last vertex.
Article: jacobi, Theorem 5.4, Equation (5.9).
Source: Meurant, A review on the inverse of symmetric tridiagonal and block tridiagonal matrices
(1992): tridiagonal Green factorization.
-/
def shiftMatrix (N : ℕ) : Matrix (Fin N) (Fin N) ℝ :=
  fun i j => if i.val+1=j.val then 1 else 0

/-- The actual forward difference with the final zero boundary.
Article: jacobi, Theorem 5.4, Equation (5.9).
Source: Meurant, A review on the inverse of symmetric tridiagonal and block tridiagonal matrices
(1992): tridiagonal Green factorization.
-/
def differenceMatrix (N : ℕ) : Matrix (Fin N) (Fin N) ℝ := 1-shiftMatrix N

/-- Shifting a cumulative-sum row drops precisely its first entry.
Article: jacobi, Theorem 5.4, Equation (5.9).
Source: Meurant, A review on the inverse of symmetric tridiagonal and block tridiagonal matrices
(1992): tridiagonal Green factorization.
-/
theorem shift_mul_tail {N : ℕ} (i j : Fin N) :
    (shiftMatrix N*tailMatrix N) i j=if i<j then 1 else 0 := by
  rw [Matrix.mul_apply]
  by_cases hi : i.val+1<N
  · let k : Fin N := ⟨i.val+1,hi⟩
    have he (l : Fin N) : i.val+1=l.val ↔ l=k := by
      constructor
      · intro h; exact Fin.ext h.symm
      · rintro rfl; rfl
    simp only [shiftMatrix,he,ite_mul,one_mul,zero_mul,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
    simp only [tailMatrix,Fin.le_iff_val_le_val,Fin.lt_def]
    congr 1
  · have he (l : Fin N) : i.val+1≠l.val := by have hl:=l.isLt; omega
    have hj : ¬i<j := by have hj:=j.isLt; simp only [Fin.lt_def]; omega
    simp [shiftMatrix,he,hj]

/-- Forward difference followed by cumulative summation is exactly the
identity, including the empty and one-vertex chains.
Article: jacobi, Theorem 5.4, Equation (5.9).
Source: Meurant, A review on the inverse of symmetric tridiagonal and block tridiagonal matrices
(1992): tridiagonal Green factorization.
-/
theorem difference_mul_tail (N : ℕ) : differenceMatrix N*tailMatrix N=1 := by
  rw [differenceMatrix,Matrix.sub_mul,Matrix.one_mul]
  ext i j
  rw [Matrix.sub_apply,shift_mul_tail]
  simp only [tailMatrix,Matrix.one_apply]
  split_ifs <;> simp_all <;> omega

/-- The cumulative-sum matrix is the genuine nonsingular inverse of
the forward difference.
Article: jacobi, Theorem 5.4, Equation (5.9).
Source: Meurant, A review on the inverse of symmetric tridiagonal and block tridiagonal matrices
(1992): tridiagonal Green factorization.
-/
theorem difference_inv (N : ℕ) : (differenceMatrix N)⁻¹=tailMatrix N :=
  Matrix.inv_eq_right_inv (difference_mul_tail N)

/-- The weighted path Laplacian conjugated by the endpoint solution.
For an orthonormal Jacobi family this is exactly I-J.
Article: jacobi, Theorem 5.4, Equation (5.9).
Source: Meurant, A review on the inverse of symmetric tridiagonal and block tridiagonal matrices
(1992): tridiagonal Green factorization.
-/
def pencil {N : ℕ} (u c : Fin N → ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  diagonal (fun i => (u i)⁻¹)*(differenceMatrix N)ᵀ*diagonal c*
    differenceMatrix N*diagonal (fun i => (u i)⁻¹)

/-- A nonsingular diagonal matrix has the pointwise reciprocal diagonal.
This requires every entry to be nonzero; the nonsingular inverse of a
singular matrix would instead be the zero matrix.
Article: jacobi, Theorem 5.4, Equation (5.9).
Source: Meurant, A review on the inverse of symmetric tridiagonal and block tridiagonal matrices
(1992): tridiagonal Green factorization.
-/
theorem diagonal_inv {N : ℕ} (u : Fin N → ℝ) (hu : ∀ i,u i≠0) :
    (diagonal u)⁻¹=diagonal (fun i => (u i)⁻¹) := by
  apply Matrix.inv_eq_right_inv
  rw [Matrix.diagonal_mul_diagonal]
  simp only [mul_inv_cancel₀ (hu _)]
  exact Matrix.diagonal_one

/-- The whole inverse matrix factors into endpoint values and cumulative
inverse conductances. Every endpoint value and conductance must be nonzero.
Article: jacobi, Theorem 5.4, Equation (5.9).
Source: Meurant, A review on the inverse of symmetric tridiagonal and block tridiagonal matrices
(1992): tridiagonal Green factorization.
-/
theorem pencil_inv {N : ℕ} (u c : Fin N → ℝ) (hu : ∀ i,u i≠0) (hc : ∀ i,c i≠0) :
    (pencil u c)⁻¹=diagonal u*tailMatrix N*diagonal (fun i => (c i)⁻¹)*
      (tailMatrix N)ᵀ*diagonal u := by
  have hU : (diagonal (fun i => (u i)⁻¹))⁻¹=diagonal u := by
    rw [diagonal_inv _ (fun i => inv_ne_zero (hu i))]
    simp only [inv_inv]
  simp only [pencil,Matrix.mul_inv_rev,hU,diagonal_inv c hc,
    ← Matrix.transpose_nonsing_inv,difference_inv,Matrix.mul_assoc]

/-- The upper-triangular Green entries are precisely u_i u_j times the
tail sum of inverse conductances. No asymptotic approximation is involved.
Article: jacobi, Theorem 5.4, Equation (5.9).
Source: Meurant, A review on the inverse of symmetric tridiagonal and block tridiagonal matrices
(1992): tridiagonal Green factorization.
-/
theorem pencil_inv_entry {N : ℕ} (u c : Fin N → ℝ) (hu : ∀ i,u i≠0) (hc : ∀ i,c i≠0) (i j : Fin N) (hij : i≤j) :
    (pencil u c)⁻¹ i j=u i*u j*∑ l:Fin N,if j≤l then (c l)⁻¹ else 0 := by
  rw [pencil_inv u c hu hc,Matrix.mul_diagonal,Matrix.mul_apply]
  simp only [Matrix.mul_diagonal,Matrix.diagonal_mul,Matrix.transpose_apply]
  rw [Finset.mul_sum,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro l _
  by_cases hj : j≤l
  · have hi : i≤l := hij.trans hj
    simp [tailMatrix,hi,hj]
    ring
  · simp [tailMatrix,hj]

/-- An identified Jacobi pencil therefore has this exact Green formula.
The separate identification hypothesis is an equality of concrete matrices,
to be discharged by the orthonormal recurrence in StandardJacobi.
Article: jacobi, Theorem 5.4, Equation (5.9).
Source: Meurant, A review on the inverse of symmetric tridiagonal and block tridiagonal matrices
(1992): tridiagonal Green factorization.
-/
theorem green_entry {N : ℕ} (J : chebyshev2.Jacobi N) (u c : Fin N → ℝ)
    (hu : ∀ i,u i≠0) (hc : ∀ i,c i≠0) (h : 1-J.matrix=pencil u c) (i j : Fin N) (hij : i≤j) :
    J.green i j=u i*u j*∑ l:Fin N,if j≤l then (c l)⁻¹ else 0 := by
  rw [chebyshev2.Jacobi.green,h]
  exact pencil_inv_entry u c hu hc i j hij

end
end jacobi.Finite.StandardGreen

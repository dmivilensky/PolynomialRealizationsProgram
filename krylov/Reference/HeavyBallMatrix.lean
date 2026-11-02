import krylov.Realization.RawLDL
import krylov.Realization.RawCGCoefficients
set_option autoImplicit false
/-!
Article: main_krylov, prop:phi(b), genuine finite heavy-ball Jacobi matrix.
Use: construct the actual negative-residual orientation of the printed first-site heavy-ball matrix and derive all positive pivot domains from its real factorization.
Source: standard unit bidiagonal LDL factorization, reusing the proved actual weighted bidiagonal entry identity.
-/

namespace krylov.Reference
noncomputable section
open krylov.Realization Matrix chebyshev2
open scoped BigOperators

/-- The actual finite heavy-ball Jacobi matrix in normalized residual orientation.
Use: The actual finite heavy-ball Jacobi matrix in normalized residual orientation.
Article: main_krylov, prop:phi(b), genuine finite heavy-ball Jacobi matrix.
Proof: Use the printed first diagonal pivot, constant remaining diagonal and true negative adjacent edges. -/
def heavyBallMatrix (d q : ℝ) (N : ℕ) : Matrix (Fin N) (Fin N) ℝ :=
  fun i j => if i=j then if i.val=0 then d else d*(1+q^2)
    else if i.val+1=j.val ∨ j.val+1=i.val then -d*q else 0

/-- The actual heavy-ball Jacobi matrix has the true constant positive-pivot LDL factorization.
Use: The actual heavy-ball Jacobi matrix has the true constant positive-pivot LDL factorization.
Article: main_krylov, prop:phi(b), genuine finite heavy-ball Jacobi matrix.
Proof: Evaluate the genuine weighted bidiagonal Gram entries and compare every actual diagonal and adjacent site. -/
theorem heavyBallMatrix_ldl (d q : ℝ) (N : ℕ) :
    heavyBallMatrix d q N=Bidiagonal.matrix (fun _ => 1) (fun _ => -q)*
      Matrix.diagonal (fun _ => d)*(Bidiagonal.matrix (fun _ => 1) (fun _ => -q))ᵀ := by
  -- The actual LDL entry identity preserves the genuine special first diagonal as well as all true internal edges.
  ext i j
  rw [bidiagonal_ldl_apply]
  by_cases hij : i=j
  · subst j
    by_cases hi : i.val=0
    · simp [heavyBallMatrix,hi]
    · simp [heavyBallMatrix,hi,show 0 < i.val by omega]
      ring
  · by_cases h1 : i.val+1=j.val
    · simp [heavyBallMatrix,hij,h1]
    · by_cases h2 : j.val+1=i.val
      · simp [heavyBallMatrix,hij,h1,h2,mul_comm]
      · simp [heavyBallMatrix,hij,h1,h2]

/-- The actual unit lower heavy-ball bidiagonal factor has determinant one.
Use: The actual unit lower heavy-ball bidiagonal factor has determinant one.
Article: main_krylov, prop:phi(b), genuine finite heavy-ball Jacobi matrix.
Proof: Use its genuine lower triangular form and true unit diagonal. -/
theorem heavyBallLower_det (q : ℝ) (N : ℕ) :
    (Bidiagonal.matrix (fun _ : Fin N => (1:ℝ)) (fun _ => -q)).det=1 := by
  -- The actual lower triangular entries have genuine unit diagonal, so their determinant product equals one.
  have ht : (Bidiagonal.matrix (fun _ : Fin N => (1:ℝ)) (fun _ => -q)).IsLowerTriangular := by
    intro i j hij
    change i<j at hij
    have hv : i.val<j.val := hij
    simp [Bidiagonal.matrix,ne_of_lt hij,show j.val+1≠i.val by omega]
  rw [Matrix.det_of_isLowerTriangular _ ht]
  apply Finset.prod_eq_one
  intro i _
  simp [Bidiagonal.matrix]

/-- The actual heavy-ball Jacobi matrix is genuinely positive definite for every real coupling and positive pivot.
Use: The actual heavy-ball Jacobi matrix is genuinely positive definite for every real coupling and positive pivot.
Article: main_krylov, prop:phi(b), genuine finite heavy-ball Jacobi matrix.
Proof: The true constant positive diagonal is carried by a genuine invertible unit bidiagonal congruence. -/
theorem heavyBallMatrix_posDef (d q : ℝ) (hd : 0 < d) (N : ℕ) :
    (heavyBallMatrix d q N).PosDef := by
  -- The real unit bidiagonal determinant proves the actual positive congruence domain.
  let L := Bidiagonal.matrix (fun _ : Fin N => (1:ℝ)) (fun _ => -q)
  have hu : IsUnit Lᵀ := (Matrix.isUnit_iff_isUnit_det _).mpr (by
    rw [Matrix.det_transpose,heavyBallLower_det]
    exact isUnit_one)
  have hp := (Matrix.PosDef.diagonal (fun _ : Fin N => hd)).conjTranspose_mul_mul_same
    (B := Lᵀ) (Matrix.mulVec_injective_iff_isUnit.mpr hu)
  rw [heavyBallMatrix_ldl]
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial,Matrix.transpose_transpose,L] using hp

/-- The actual finite heavy-ball Jacobi determinant is exactly the genuine pivot power.
Use: The actual finite heavy-ball Jacobi determinant is exactly the genuine pivot power.
Article: main_krylov, prop:phi(b), genuine finite heavy-ball Jacobi matrix.
Proof: Take determinants of its true unit bidiagonal LDL factorization. -/
theorem heavyBallMatrix_det (d q : ℝ) (N : ℕ) :
    (heavyBallMatrix d q N).det=d^N := by
  rw [heavyBallMatrix_ldl,Matrix.det_mul,Matrix.det_mul,Matrix.det_transpose,
    heavyBallLower_det,one_mul,mul_one,Matrix.det_diagonal]
  simp

/-- Every true leading principal block is the actual shorter heavy-ball matrix with the same parameters.
Use: Every true leading principal block is the actual shorter heavy-ball matrix with the same parameters.
Article: main_krylov, prop:phi(b), genuine finite heavy-ball Jacobi matrix.
Proof: Read the original physical diagonal and adjacent entries at the genuine leading indices. -/
theorem heavyBallMatrix_prefix (d q : ℝ) (N m : ℕ) (hm : m≤N) :
    rawBlock (heavyBallMatrix d q N) 0 m (by omega)=heavyBallMatrix d q m := by
  ext i j
  simp [rawBlock,heavyBallMatrix,Fin.ext_iff]

/-- The actual heavy-ball matrix has a genuine three-diagonal band.
Use: The actual heavy-ball matrix has a genuine three-diagonal band.
Article: main_krylov, prop:phi(b), genuine finite heavy-ball Jacobi matrix.
Proof: Every real entry outside the true diagonal and adjacent sites is zero. -/
theorem heavyBallMatrix_tridiagonal (d q : ℝ) (N : ℕ) :
    ∀ i j : Fin N,i.val+1 < j.val ∨ j.val+1 < i.val → heavyBallMatrix d q N i j=0 := by
  intro i j hij
  simp [heavyBallMatrix,show i≠j by intro h;subst j;omega,
    show ¬ (i.val+1=j.val ∨ j.val+1=i.val) by omega]

/-- The actual heavy-ball matrix has strictly negative genuine adjacent edges for positive pivot and coupling.
Use: The actual heavy-ball matrix has strictly negative genuine adjacent edges for positive pivot and coupling.
Article: main_krylov, prop:phi(b), genuine finite heavy-ball Jacobi matrix.
Proof: Read the true adjacent entry and use the real positive parameter signs. -/
theorem heavyBallMatrix_adjacent_neg (d q : ℝ) (hd : 0 < d) (hq : 0 < q) (N : ℕ) :
    ∀ i j : Fin N,i.val+1=j.val → heavyBallMatrix d q N i j<0 := by
  intro i j hij
  rw [heavyBallMatrix,ite_eq_right (show i≠j by intro h;subst j;omega),ite_eq_left (Or.inl hij)]
  exact mul_neg_of_neg_of_pos (neg_neg_of_pos hd) hq
end
end krylov.Reference

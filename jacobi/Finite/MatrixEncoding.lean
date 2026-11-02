import jacobi.Finite.Fiber

/-!
Article: jacobi, Equation (1.3) (unique persymmetric realization and its weights).
Every real symmetric tridiagonal matrix with nonnegative adjacent entries is
represented by the existing finite Jacobi coefficient type. This bridge ensures
that the all-matrix formulation of Packing has precisely the advertised scope.
Use: applies the general packing construction to arbitrary tridiagonal input matrices.
-/

namespace jacobi.Finite
noncomputable section
open chebyshev1 chebyshev2 Matrix

variable {N : ℕ}

/-- Encode diagonal entries and squared adjacent entries, with canonical zero tails.
Use: applies the general packing construction to arbitrary tridiagonal input matrices.
Article: jacobi, Equation (1.3) (unique persymmetric realization and its weights).
-/
def fromMatrix (A : Matrix (Fin N) (Fin N) ℝ) : Jacobi N where
  data := {
    b := fun i => if hi : i < N then A ⟨i, hi⟩ ⟨i, hi⟩ else 0
    aSq := fun i => if hi : 0 < i ∧ i < N then
      (A ⟨i-1, by omega⟩ ⟨i, hi.2⟩)^2 else 0 }
  coupling_nonneg i := by dsimp; split_ifs <;> positivity
  coupling_zero := by simp
  diagonal_tail i hi := by simp [not_lt.mpr hi]
  coupling_tail i hi := by simp [not_lt.mpr hi]

/-- The coefficient encoding recovers exactly every admissible input matrix.
Use: transfers all Jacobi-typed conclusions to the literal matrix hypotheses of the article.
Article: jacobi, Equation (1.3) (unique persymmetric realization and its weights).
Proof: compare diagonal, upper adjacent, lower adjacent and all remaining entries;
nonnegative adjacent entries fix the square-root signs. -/
theorem fromMatrix_eq (A : Matrix (Fin N) (Fin N) ℝ) (hs : A.IsHermitian)
    (hp : ∀ i j : Fin N, i.val+1 = j.val → 0 ≤ A i j)
    (hz : ∀ i j : Fin N, i.val+1 < j.val ∨ j.val+1 < i.val → A i j = 0) :
    (fromMatrix A).matrix = A := by
  -- Check the diagonal and both adjacent diagonals separately; all remaining entries vanish.
  ext i j
  have hi := i.isLt
  have hj := j.isLt
  by_cases hij : i = j
  · subst j
    simp [Jacobi.matrix, JacobiData.matrix_apply, fromMatrix, hi]
  by_cases hu : i.val+1 = j.val
  · have hj0 : 0 < j.val := by omega
    have hprev : j.val-1 = i.val := by omega
    simp [Jacobi.matrix, JacobiData.matrix_apply, fromMatrix, hij, hu, hj, hj0, hprev]
    exact Real.sqrt_sq (hp i j hu)
  by_cases hl : j.val+1 = i.val
  · have hi0 : 0 < i.val := by omega
    have hprev : i.val-1 = j.val := by omega
    have he : A j i = A i j := hs.isSymm.apply _ _
    simp [Jacobi.matrix, JacobiData.matrix_apply, fromMatrix, hij, hu, hl, hi, hi0, hprev, he]
    simpa only [he] using Real.sqrt_sq (hp j i hl)
  · have he : A i j = 0 := hz i j (by
      have hn : i.val ≠ j.val := fun he => hij (Fin.ext he)
      omega)
    simp [Jacobi.matrix, JacobiData.matrix_apply, hij, hu, hl, he]

end
end jacobi.Finite

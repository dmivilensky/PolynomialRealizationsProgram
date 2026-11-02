import jacobi.Finite.WeightChart

/-!
Article: jacobi, Proposition C.3.
Every actual fibre element has the positively oriented polynomial eigenvectors
stated in the article. The basis is transported from the proved reconstruction,
so this introduces neither a recurrence hypothesis nor an unproved eigenbasis.
Source: finite Lanczos--Stieltjes reconstruction from the first-site measure.
Use: identifies polynomial asymptotics with physical eigenvector asymptotics.
-/
namespace jacobi.Finite
noncomputable section
open chebyshev1 chebyshev2 Polynomial Matrix
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- Reconstructed eigenvectors are square-root weights times the actual orthogonal polynomials.
Use: identifies polynomial asymptotics with physical eigenvector asymptotics.
Article: jacobi, Proposition C.3.
Proof: evaluate the already proved polynomial-basis identity at the spectral coordinate. -/
theorem DiscreteMeasure.eigenvectors_polynomial {N : ℕ} (M : DiscreteMeasure N) (i k : Fin N) :
    M.reconstructedBasis.Q i k = Real.sqrt (M.weight k) *
      (M.orthogonalPolynomial i).eval (M.node k) := by
  have h := congrArg (fun v : EuclideanSpace ℝ (Fin N) => v k) (M.evaluate_orthogonalPolynomial i)
  exact h.symm

/-- Every fibre element admits the article's eigenbasis with positive first components.
Use: applies the polynomial formula to arbitrary matrices, including the persymmetric one.
Article: jacobi, Proposition C.3.
Proof: the full inverse spectral theorem identifies the reconstructed matrix
with J; its explicit eigenbasis has precisely the prescribed positive probabilities. -/
theorem exists_polynomial_basis {n : ℕ} (S : Nodes (n+1)) (J : Fiber (n+1) S.polynomial) :
    ∃ B : SpectralBasis J.val.matrix, B.eigenvalues = S.value ∧
      (∀ k, 0 < B.Q 0 k) ∧
      ∀ i k, B.Q i k = Real.sqrt ((spectralWeights S J).val k) *
        ((S.measure (spectralWeights S J)).orthogonalPolynomial i).eval (S.value k) := by
  -- Transport the explicit reconstruction basis to the original matrix through the proved inverse identity.
  let M := S.measure (spectralWeights S J)
  have hJ : M.reconstructed.matrix = J.val.matrix :=
    congrArg (fun K : Fiber (n+1) S.polynomial => K.val.matrix) (reconstruct_spectralWeights S J)
  let B : SpectralBasis J.val.matrix := {
    Q := M.reconstructedBasis.Q
    eigenvalues := M.reconstructedBasis.eigenvalues
    transpose_mul := M.reconstructedBasis.transpose_mul
    mul_transpose := M.reconstructedBasis.mul_transpose
    diagonalize := by rw [← hJ]; exact M.reconstructedBasis.diagonalize }
  have hQ : B.Q = M.reconstructedBasis.Q := rfl
  have he : B.eigenvalues = M.reconstructedBasis.eigenvalues := rfl
  refine ⟨B, he, ?_, ?_⟩
  · intro k
    rw [hQ]
    change 0 < M.eigenvectors (0 : Fin (n+1)) k
    exact (Real.sqrt_pos.mpr (M.positive k)).trans_eq
      (M.eigenvectors_first (Nat.succ_pos n) k).symm
  · intro i k
    rw [hQ]
    exact M.eigenvectors_polynomial i k

end
end jacobi.Finite

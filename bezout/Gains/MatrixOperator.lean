import bezout.Gains.MatrixAdmissible
import bezout.Gains.Bounds

/-!
Article: bezout, Equation `eq:AN-op` and Theorem 4.1.
Use: the abstract Hilbert-space operator gain bounds the literal Euclidean
matrix operator norm of the actual physical derivative.
Proof: Euclidean matrix representation preserves the action and operator
norm, while real matrix symmetry and physical admissibility coincide.
-/

namespace bezout.History
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator
variable {N : ℕ} {d : Type} [Fintype d] [DecidableEq d]

/-- Euclidean matrix representation preserves the continuous physical operator. -/
theorem matrixEnd_continuous (H : Matrix d d ℝ) :
    LinearMap.toContinuousLinearMap (matrixEnd H) =
      (Matrix.toEuclideanCLM (n := d) (𝕜 := ℝ)) H := by
  ext v
  rfl

/-- A universal physical operator bound controls the literal Euclidean matrix
operator norm, including the symmetric perturbation restriction. -/
theorem matrixResponse_opNorm_le (h : bezout.History N)
    (I : chebyshev1.SpectralInterval) (symmetric : Bool) (C : ℝ)
    (hb : Gains.OperatorBound h I symmetric C) (H : Matrix d d ℝ)
    (hH : H.IsHermitian) (hs : spectrum ℝ H ⊆ Set.Icc I.mu I.L)
    (D : Fin N → Matrix d d ℝ)
    (hDsym : symmetric = true → ∀ s, (D s).IsHermitian)
    (hD : ∑ s, chebyshev1.opNorm (D s) ^ 2 ≤ 1) :
    chebyshev1.opNorm (h.matrixResponse H D) ≤ C := by
  change ‖(Matrix.toEuclideanCLM (n := d) (𝕜 := ℝ)) (h.matrixResponse H D)‖ ≤ C
  apply ContinuousLinearMap.opNorm_le_of_unit_norm (Gains.operatorBound_nonneg h I symmetric C hb)
  intro v hv
  change ‖matrixEnd (h.matrixResponse H D) v‖ ≤ C
  rw [h.matrixResponse_action]
  apply hb (EuclideanSpace ℝ d) (matrixEnd H) (matrixEnd_admissible I H hH hs)
    (fun s => matrixEnd (D s))
  · intro he s
    rw [matrixEnd_eq_toEuclideanLin, Matrix.isSymmetric_toEuclideanLin_iff]
    exact hDsym he s
  · simpa only [matrixEnd_continuous, Matrix.l2_opNorm_toEuclideanCLM, chebyshev1.opNorm] using hD
  · exact hv.le

end
end bezout.History

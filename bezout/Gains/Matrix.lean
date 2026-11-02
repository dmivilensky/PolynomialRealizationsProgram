import bezout.Gains.Variation
import bezout.Gains.Spectral
import chebyshev1.Spectral.OperatorNorm

/-!
Article: bezout, Theorem 4.1, physical matrix first variation.
Use: connects the derivative of actual oracle executions to both matrix
energy budgets and to the existing sharp Hilbert--Schmidt theory.
Proof: polynomial functional calculus commutes with the Euclidean matrix
representation; orthonormal spectral coordinates identify every insertion.
-/

namespace bezout.History
noncomputable section
open Polynomial
open scoped BigOperators Matrix
set_option backward.isDefEq.respectTransparency false
variable {N : ℕ} {d : Type*} [Fintype d] [DecidableEq d]

/-- A matrix acts on the actual Euclidean Hilbert space as a linear endomorphism. -/
def matrixEnd : Matrix d d ℝ →ₐ[ℝ] Module.End ℝ (EuclideanSpace ℝ d) where
  toRingHom := ContinuousLinearMap.toLinearMapRingHom.comp Matrix.toEuclideanCLM.toRingHom
  commutes' r := by
    change ((Matrix.toEuclideanCLM (n := d) (𝕜 := ℝ)) (algebraMap ℝ (Matrix d d ℝ) r)).toLinearMap = _
    rw [AlgHomClass.commutes]
    rfl

/-- Physical first variation written as the finite matrix insertion sum. -/
def matrixResponse (h : bezout.History N) (H : Matrix d d ℝ)
    (D : Fin N → Matrix d d ℝ) : Matrix d d ℝ :=
  ∑ s, aeval H (h.response s) * D s * aeval H (h.query s)

/-- The finite matrix formula is exactly the derivative acting on an initial vector. -/
theorem matrixResponse_action (h : bezout.History N) (H : Matrix d d ℝ)
    (D : Fin N → Matrix d d ℝ) (initial : EuclideanSpace ℝ d) :
    matrixEnd (h.matrixResponse H D) initial =
      h.firstVariation (matrixEnd H) (fun s => matrixEnd (D s)) initial := by
  simp only [matrixResponse, map_sum, LinearMap.sum_apply, map_mul, Module.End.mul_apply,
    firstVariation, variationNoise]
  apply Finset.sum_congr rfl
  intro s _
  rw [← Polynomial.aeval_algHom_apply matrixEnd H (h.response s),
    ← Polynomial.aeval_algHom_apply matrixEnd H (h.query s)]

/-- The matrix insertion formula is the derivative of the actual variable-Hessian terminal. -/
theorem hasDerivAt_matrix_output (h : bezout.History N) (H : Matrix d d ℝ)
    (D : Fin N → Matrix d d ℝ) (initial : EuclideanSpace ℝ d) :
    HasDerivAt (fun t => h.oracleOutput initial
      (perturbedOracle (matrixEnd H) (fun s => matrixEnd (D s)) t))
      (matrixEnd (h.matrixResponse H D) initial) 0 := by
  rw [h.matrixResponse_action]
  exact h.hasDerivAt_perturbed_output _ _ initial

/-- Extend a finite perturbation stream by zero after the last actual call. -/
def matrixDriftExtension (D : Fin N → Matrix d d ℝ) (s : ℕ) : Matrix d d ℝ :=
  if hs : s < N then D ⟨s, hs⟩ else 0

/-- In an eigenbasis each physical insertion acts entrywise by the separated kernel. -/
theorem diagonal_matrixResponse_entry (h : bezout.History N) (eig : d → ℝ)
    (D : Fin N → Matrix d d ℝ) (i j : d) :
    h.matrixResponse (Matrix.diagonal eig) D i j =
      ∑ s, Lower.physicalKernel h s (eig i) (eig j) * D s i j := by
  simp only [matrixResponse, Matrix.sum_apply, chebyshev1.aeval_diagonal,
    Matrix.diagonal_mul, Matrix.mul_diagonal, Lower.physicalKernel]
  apply Finset.sum_congr rfl
  intro s _
  ring

/-- Spectral coordinates of physical first variation agree with its diagonal formula. -/
theorem matrixResponse_coordinates (h : bezout.History N) (H : Matrix d d ℝ)
    (hH : H.IsHermitian) (D : Fin N → Matrix d d ℝ) :
    (chebyshev1.SpectralBasis.ofHermitian H hH).coordinates (h.matrixResponse H D) =
      h.matrixResponse (Matrix.diagonal (chebyshev1.SpectralBasis.ofHermitian H hH).eigenvalues)
        (fun s => (chebyshev1.SpectralBasis.ofHermitian H hH).coordinates (D s)) := by
  let B := chebyshev1.SpectralBasis.ofHermitian H hH
  have hsum (A : Fin N → Matrix d d ℝ) : B.coordinates (∑ s, A s) = ∑ s, B.coordinates (A s) := by
    simp only [chebyshev1.SpectralBasis.coordinates, Matrix.mul_sum, Matrix.sum_mul]
  rw [matrixResponse, hsum]
  unfold matrixResponse
  apply Finset.sum_congr rfl
  intro s _
  rw [B.coordinates_mul, B.coordinates_mul, chebyshev1.aeval_coordinates,
    chebyshev1.aeval_coordinates, chebyshev1.aeval_diagonal, chebyshev1.aeval_diagonal]
  rfl

/-- The physical matrix derivative is the insertion operator of the existing
realization theory. This equality holds for every symmetric admissible Hessian. -/
theorem matrixResponse_eq_realization (h : bezout.History N) (H : Matrix d d ℝ)
    (hH : H.IsHermitian) (D : Fin N → Matrix d d ℝ) :
    h.matrixResponse H D = h.realization.linearResponse N H (matrixDriftExtension D) := by
  let B := chebyshev1.SpectralBasis.ofHermitian H hH
  apply B.coordinates_injective
  rw [h.matrixResponse_coordinates]
  have hr := h.realization.linearResponse_coordinates B.Q H B.transpose_mul B.mul_transpose
    N (matrixDriftExtension D)
  rw [B.diagonalize] at hr
  change _ = B.Qᵀ * _ * B.Q
  rw [← hr]
  ext i j
  rw [h.diagonal_matrixResponse_entry, chebyshev1.Realization.diagonal_linearResponse_entry,
    Finset.sum_range]
  apply Finset.sum_congr rfl
  intro s _
  rw [h.realization_kernel]
  simp only [matrixDriftExtension, s.isLt, dite_true, Lower.physicalKernel,
    chebyshev1.SpectralBasis.coordinates]
  rfl

/-- The actual derivative obeys the sharp dimension-uniform Hilbert--Schmidt bound. -/
theorem hs_matrixResponse_bound (h : bezout.History N) (I : chebyshev1.SpectralInterval)
    (H : Matrix d d ℝ) (hH : H.IsHermitian) (hs : spectrum ℝ H ⊆ Set.Icc I.mu I.L)
    (D : Fin N → Matrix d d ℝ) :
    chebyshev1.hsNorm (h.matrixResponse H D) ≤
      h.spectralGain I * Real.sqrt (∑ s, chebyshev1.hsNorm (D s) ^ 2) := by
  rw [h.matrixResponse_eq_realization H hH D]
  simpa only [Finset.sum_range, matrixDriftExtension, Fin.isLt, dite_true, spectralGain] using
    h.realization.hsNorm_linearResponse_bound I N H hH hs (matrixDriftExtension D)

end
end bezout.History

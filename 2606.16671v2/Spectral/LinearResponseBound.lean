import «2606.16671v2».Spectral.Basis
import «2606.16671v2».Spectral.DiagonalResponse
import «2606.16671v2».Realization.Coordinates

/-!
Article: 2606.16671v2, Proposition 1.3.
The Hilbert–Schmidt upper bound of Proposition 1.3 for every symmetric Hessian.
Use: `«2606.16671v2».Realization.hsNorm_linearResponse_bound` feeds
`«2610.05164v2».Jacobi.gain_bound` (gain bound).
Source: mathlib, Mathlib.LinearAlgebra.Matrix.Hermitian and matrix norm theory — finite real
spectral theorem and Euclidean/Frobenius norm comparison. The needed form is proved here.
-/
namespace «2606.16671v2».Realization
noncomputable section
open scoped Matrix BigOperators
variable {ι d : Type*} [Fintype ι] [DecidableEq ι] [Fintype d] [DecidableEq d]

/--
The Hilbert–Schmidt upper bound of Proposition 1.3 for every symmetric Hessian.

The stated quantitative bound `hsNorm (R.linearResponse N H E) ≤ R.gain I N * Real.sqrt (∑ s ∈
Finset.range N, hsNorm (E s) ^ 2)`.

Use: `«2610.05164v2».Jacobi.gain_bound` uses this bound to establish the stated quantitative
bound `hsNorm ((J.recurrence I h).method.realization.linearResponse N H E) ≤ J.gain I h *
Real.sqrt (∑ s ∈ Finset.range N, hsNorm (E s)^2)`.

Article: 2606.16671v2, Proposition 1.3.

Source: mathlib, Mathlib.LinearAlgebra.Matrix.Hermitian and matrix norm theory — finite real
spectral theorem and Euclidean/Frobenius norm comparison.

Proof: Use the identities/estimates `«2606.16671v2».SpectralBasis.eigenvalues_mem_interval`,
`«2606.16671v2».Realization.diagonal_hsNorm_bound`,
`«2606.16671v2».hsNorm_orthogonal_conjugation` with the arguments shown in the proof.
-/
theorem hsNorm_linearResponse_bound (R : Realization ι) (I : SpectralInterval) (N : ℕ)
    (H : Matrix d d ℝ) (hH : H.IsHermitian) (hspec : spectrum ℝ H ⊆ Set.Icc I.mu I.L)
    (E : ℕ → Matrix d d ℝ) :
    hsNorm (R.linearResponse N H E) ≤
      R.gain I N * Real.sqrt (∑ s ∈ Finset.range N, hsNorm (E s) ^ 2) := by
  -- Use the identities/estimates `«2606.16671v2».SpectralBasis.eigenvalues_mem_interval`,
  -- `«2606.16671v2».Realization.diagonal_hsNorm_bound`,
  -- `«2606.16671v2».hsNorm_orthogonal_conjugation` with the arguments shown in the proof.
  let B := SpectralBasis.ofHermitian H hH
  have heig : ∀ i, B.eigenvalues i ∈ Set.Icc I.mu I.L :=
    fun i => SpectralBasis.eigenvalues_mem_interval I H hH hspec i
  have h := R.diagonal_hsNorm_bound I N B.eigenvalues heig (fun s => B.coordinates (E s))
  rw [← B.diagonalize] at h
  dsimp only [SpectralBasis.coordinates] at h
  rw [R.linearResponse_coordinates B.Q H B.transpose_mul B.mul_transpose] at h
  rw [hsNorm_orthogonal_conjugation B.Q _ B.transpose_mul B.mul_transpose] at h
  simpa only [hsNorm_orthogonal_conjugation B.Q _ B.transpose_mul B.mul_transpose] using h

end
end «2606.16671v2».Realization

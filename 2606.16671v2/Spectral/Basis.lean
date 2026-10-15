import «2606.16671v2».Spectral.HilbertSchmidt
import «2606.16671v2».Chebyshev.Normalization
import Mathlib.Analysis.Matrix.Spectrum

/-!
Article: 2606.16671v2, Proposition 1.3.
Existence uses the community library's finite-dimensional spectral theorem.
Use: `«2606.16671v2».SpectralBasis.eigenvalues_mem_interval` feeds
`«2606.16671v2».Realization.hsNorm_linearResponse_bound` (The Hilbert–Schmidt upper bound of
Proposition 1.3 for every symmetric Hessian).
Proof chain: `«2606.16671v2».Realization.hsNorm_linearResponse_bound` — 2606.16671v2, Proposition
1.3; Finite expansion, Hilbert–Schmidt bound and sharpness.
Source: mathlib, Mathlib.LinearAlgebra.Matrix.Hermitian and matrix norm theory — finite real
spectral theorem and Euclidean/Frobenius norm comparison. The needed form is proved here.
-/
namespace «2606.16671v2»
noncomputable section
open scoped Matrix
variable {d : Type*} [Fintype d] [DecidableEq d]

/--
An orthogonal diagonalization, with repeated eigenvalues kept as separate coordinates.

Use: `«2606.16671v2».SpectralBasis.coordinates` uses this record of data and proof obligations
in the displayed construction of `coordinates`. Its inputs and component formulas are fixed by
that definition.

Article: 2606.16671v2, Corollary 4.4 via `«2606.16671v2».Prefix.opNorm_linearResponse_le`.

Source: mathlib, Mathlib.LinearAlgebra.Matrix.Hermitian and matrix norm theory — finite real
spectral theorem and Euclidean/Frobenius norm comparison.
-/
structure SpectralBasis (H : Matrix d d ℝ) where
  /-- Orthogonal change-of-basis matrix whose columns are eigenvectors. -/
  Q : Matrix d d ℝ
  /-- Eigenvalue attached to each basis vector. -/
  eigenvalues : d → ℝ
  /-- The columns of Q are orthonormal. -/
  transpose_mul : Qᵀ * Q = 1
  /-- The eigenbasis is complete, so Q is also a right inverse to its transpose. -/
  mul_transpose : Q * Qᵀ = 1
  /-- The chosen basis turns H into the stated diagonal matrix. -/
  diagonalize : Qᵀ * H * Q = Matrix.diagonal eigenvalues

namespace SpectralBasis

/--
Existence uses the community library's finite-dimensional spectral theorem.

Use: `«2606.16671v2».SpectralBasis.eigenvalues_mem_interval` uses this definition to establish
membership in the specified domain/enclosure: `(ofHermitian H hH).eigenvalues i ∈ Set.Icc I.mu
I.L`.

Article: 2606.16671v2, Corollary 4.4 via `«2606.16671v2».Prefix.opNorm_linearResponse_le`.

Source: mathlib, Mathlib.LinearAlgebra.Matrix.Hermitian and matrix norm theory — finite real
spectral theorem and Euclidean/Frobenius norm comparison.
-/
def ofHermitian (H : Matrix d d ℝ) (hH : H.IsHermitian) : SpectralBasis H where
  Q := hH.eigenvectorUnitary
  eigenvalues := hH.eigenvalues
  transpose_mul := by
    simpa only [Unitary.coe_star, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] using
      Unitary.coe_star_mul_self hH.eigenvectorUnitary
  mul_transpose := by
    simpa only [Unitary.coe_star, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] using
      Unitary.coe_mul_star_self hH.eigenvectorUnitary
  diagonalize := by
    have h := hH.conjStarAlgAut_star_eigenvectorUnitary
    simpa [Unitary.conjStarAlgAut_star_apply, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial, Function.comp_def] using h

/--
Defines `coordinates` of type `Matrix d d ℝ` by `B.Qᵀ * E * B.Q`.

Use: `«2606.16671v2».SpectralBasis.coordinates_injective` uses this definition to establish the
precise assertion is `Function.Injective B.coordinates`.

Article: 2606.16671v2, Corollary 4.4 via `«2606.16671v2».Prefix.opNorm_linearResponse_le`.

Source: mathlib, Mathlib.LinearAlgebra.Matrix.Hermitian and matrix norm theory — finite real
spectral theorem and Euclidean/Frobenius norm comparison.
-/
def coordinates {H : Matrix d d ℝ} (B : SpectralBasis H) (E : Matrix d d ℝ) : Matrix d d ℝ :=
  B.Qᵀ * E * B.Q

/--
Exact identity `B.coordinates (A * C) = B.coordinates A * B.coordinates C`.

Use: `«2606.16671v2».JacobiData.linearResponse_blocks` rewrites with this identity to establish
exact identity `(J.realization I).linearResponse N H E = -(2 / (I.delta * J.den I N)) • ∑ s ∈
Finset.range N, aeval H (J.spectralBlock I (s + 1) (N - (s + 1))) * E s * aeval H
(J.spectralBlock I 0 s)`.

Article: 2606.16671v2, Corollary 4.4 via `«2606.16671v2».Prefix.opNorm_linearResponse_le`.

Source: mathlib, Mathlib.LinearAlgebra.Matrix.Hermitian and matrix norm theory — finite real
spectral theorem and Euclidean/Frobenius norm comparison.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem coordinates_mul {H : Matrix d d ℝ} (B : SpectralBasis H) (A C : Matrix d d ℝ) :
    B.coordinates (A * C) = B.coordinates A * B.coordinates C := by
  dsimp [coordinates]
  calc B.Qᵀ * (A * C) * B.Q = B.Qᵀ * A * (B.Q * B.Qᵀ) * C * B.Q := by
        rw [B.mul_transpose]; simp [Matrix.mul_assoc]
    _ = (B.Qᵀ * A * B.Q) * (B.Qᵀ * C * B.Q) := by simp [Matrix.mul_assoc]

/--
The precise assertion is `Function.Injective B.coordinates`.

Use: `«2606.16671v2».JacobiData.linearResponse_blocks` uses this assertion to establish exact
identity `(J.realization I).linearResponse N H E = -(2 / (I.delta * J.den I N)) • ∑ s ∈
Finset.range N, aeval H (J.spectralBlock I (s + 1) (N - (s + 1))) * E s * aeval H
(J.spectralBlock I 0 s)`.

Article: 2606.16671v2, Corollary 4.4 via `«2606.16671v2».Prefix.opNorm_linearResponse_le`.

Source: mathlib, Mathlib.LinearAlgebra.Matrix.Hermitian and matrix norm theory — finite real
spectral theorem and Euclidean/Frobenius norm comparison.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem coordinates_injective {H : Matrix d d ℝ} (B : SpectralBasis H) :
    Function.Injective B.coordinates := by
  -- Rewrite the definitions and library identities explicitly named in the proof, then
  -- discharge the resulting algebraic or order relation.
  intro A C h
  have hr (M : Matrix d d ℝ) : B.Q * B.coordinates M * B.Qᵀ = M := by
    dsimp [coordinates]
    calc B.Q * (B.Qᵀ * M * B.Q) * B.Qᵀ = (B.Q * B.Qᵀ) * M * (B.Q * B.Qᵀ) := by
          simp [Matrix.mul_assoc]
      _ = M := by rw [B.mul_transpose]; simp
  have he := congrArg (fun M => B.Q * M * B.Qᵀ) h
  simpa only [hr] using he

/--
Exact identity `hsNorm (B.coordinates E) = hsNorm E`.

Use: a standalone supporting identity for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: 2606.16671v2, Proposition 1.3.

Source: mathlib, Mathlib.LinearAlgebra.Matrix.Hermitian and matrix norm theory — finite real
spectral theorem and Euclidean/Frobenius norm comparison.

Proof: Use the identities/estimates `«2606.16671v2».hsNorm_orthogonal_conjugation` with the
arguments shown in the proof.
-/
theorem parseval {H : Matrix d d ℝ} (B : SpectralBasis H) (E : Matrix d d ℝ) :
    hsNorm (B.coordinates E) = hsNorm E :=
  hsNorm_orthogonal_conjugation B.Q E B.transpose_mul B.mul_transpose

/--
Membership in the specified domain/enclosure: `(ofHermitian H hH).eigenvalues i ∈ Set.Icc I.mu
I.L`.

Use: `«2606.16671v2».Realization.hsNorm_linearResponse_bound` uses this assertion to establish
the stated quantitative bound `hsNorm (R.linearResponse N H E) ≤ R.gain I N * Real.sqrt (∑ s ∈
Finset.range N, hsNorm (E s) ^ 2)`.

Article: 2606.16671v2, Proposition 1.3 via
`«2606.16671v2».Realization.hsNorm_linearResponse_bound`.

Source: mathlib, Mathlib.LinearAlgebra.Matrix.Hermitian and matrix norm theory — finite real
spectral theorem and Euclidean/Frobenius norm comparison.

Proof: The displayed proof term instantiates the cited result with exactly the parameters and
hypotheses of this assertion.
-/
theorem eigenvalues_mem_interval (I : SpectralInterval) (H : Matrix d d ℝ) (hH : H.IsHermitian)
    (h : spectrum ℝ H ⊆ Set.Icc I.mu I.L) (i : d) :
    (ofHermitian H hH).eigenvalues i ∈ Set.Icc I.mu I.L :=
  h (hH.eigenvalues_mem_spectrum_real i)

end SpectralBasis
end
end «2606.16671v2»

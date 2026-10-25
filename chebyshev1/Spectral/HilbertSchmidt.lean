import Mathlib.Analysis.Matrix.Normed
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
Article: chebyshev1, Proposition 1.3.
Parseval identity for the spectral change of coordinates.
Use: `chebyshev1.hsNorm_orthogonal_conjugation` feeds
`chebyshev1.Realization.hsNorm_linearResponse_bound` (The Hilbert–Schmidt upper bound of
Proposition 1.3 for every symmetric Hessian).
Proof chain: `chebyshev1.Realization.hsNorm_linearResponse_bound` — chebyshev1, Proposition
1.3; Finite expansion, Hilbert–Schmidt bound and sharpness.
Source: mathlib, Mathlib.LinearAlgebra.Matrix.Hermitian and matrix norm theory — finite real
spectral theorem and Euclidean/Frobenius norm comparison. The needed form is proved here.
-/
namespace chebyshev1
noncomputable section
open scoped BigOperators Matrix
variable {d : Type*} [Fintype d]

/--
Squared Hilbert–Schmidt norm in orthonormal coordinates.

Use: `chebyshev1.hsNorm` uses this definition in the displayed construction of `hsNorm`.
Its inputs and component formulas are fixed by that definition.

Article: chebyshev1, Proposition 1.3 via
`chebyshev1.Realization.hsNorm_linearResponse_bound`.

Source: mathlib, Mathlib.LinearAlgebra.Matrix.Hermitian and matrix norm theory — finite real
spectral theorem and Euclidean/Frobenius norm comparison.
-/
def hsSq (M : Matrix d d ℝ) : ℝ := ∑ i, ∑ j, (M i j) ^ 2
/--
Defines `hsNorm` of type `ℝ` by `Real.sqrt (hsSq M)`.

Use: `chebyshev1.hsNorm_orthogonal_conjugation` uses this definition to establish exact
identity `hsNorm (Qᵀ * M * Q) = hsNorm M`.

Article: chebyshev1, Proposition 1.3 via
`chebyshev1.Realization.hsNorm_linearResponse_bound`.

Source: mathlib, Mathlib.LinearAlgebra.Matrix.Hermitian and matrix norm theory — finite real
spectral theorem and Euclidean/Frobenius norm comparison.
-/
def hsNorm (M : Matrix d d ℝ) : ℝ := Real.sqrt (hsSq M)

/--
The stated quantitative bound `0 ≤ hsSq M`.

Use: `chebyshev1.hsNorm_sq` uses this bound to establish the identity `hsNorm M ^ 2 =
hsSq M`.

Article: chebyshev1, Proposition 1.3 via
`chebyshev1.Realization.hsNorm_linearResponse_bound`.

Source: mathlib, Mathlib.LinearAlgebra.Matrix.Hermitian and matrix norm theory — finite real
spectral theorem and Euclidean/Frobenius norm comparison.

Proof: The displayed proof term instantiates the cited result with exactly the parameters and
hypotheses of this assertion.
-/
theorem hsSq_nonneg (M : Matrix d d ℝ) : 0 ≤ hsSq M :=
  Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))
/--
The stated quantitative bound `0 ≤ hsNorm M`.

Use: `chebyshev1.Realization.diagonal_hsNorm_bound` uses this bound to establish the stated
quantitative bound `hsNorm (R.linearResponse N (Matrix.diagonal eig) E) ≤ R.gain I N *
Real.sqrt (∑ s ∈ Finset.range N, hsNorm (E s) ^ 2)`.

Article: chebyshev1, Proposition 1.3 via
`chebyshev1.Realization.hsNorm_linearResponse_bound`.

Source: mathlib, Mathlib.LinearAlgebra.Matrix.Hermitian and matrix norm theory — finite real
spectral theorem and Euclidean/Frobenius norm comparison.

Proof: The displayed proof term instantiates the cited result with exactly the parameters and
hypotheses of this assertion.
-/
theorem hsNorm_nonneg (M : Matrix d d ℝ) : 0 ≤ hsNorm M := Real.sqrt_nonneg _
/--
Exact identity `hsNorm M ^ 2 = hsSq M`.

Use: `chebyshev1.Realization.diagonal_hsNorm_bound` rewrites with this identity to
establish the stated quantitative bound `hsNorm (R.linearResponse N (Matrix.diagonal eig) E) ≤
R.gain I N * Real.sqrt (∑ s ∈ Finset.range N, hsNorm (E s) ^ 2)`.

Article: chebyshev1, Proposition 1.3 via
`chebyshev1.Realization.hsNorm_linearResponse_bound`.

Source: mathlib, Mathlib.LinearAlgebra.Matrix.Hermitian and matrix norm theory — finite real
spectral theorem and Euclidean/Frobenius norm comparison.

Proof: Use the identities/estimates `chebyshev1.hsSq_nonneg` with the arguments shown in
the proof.
-/
theorem hsNorm_sq (M : Matrix d d ℝ) : hsNorm M ^ 2 = hsSq M := Real.sq_sqrt (hsSq_nonneg M)

open scoped Matrix.Norms.Frobenius in
/--
Exact identity `hsNorm M = ‖M‖`.

Use: a standalone supporting identity for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: chebyshev1, Proposition 1.3.

Source: mathlib, Mathlib.LinearAlgebra.Matrix.Hermitian and matrix norm theory — finite real
spectral theorem and Euclidean/Frobenius norm comparison.

Proof: Expand/rewrite the named definitions and identities appearing in the tactic block; the
remaining goal is a direct simplification or algebraic consequence.
-/
theorem hsNorm_eq_frobenius (M : Matrix d d ℝ) : hsNorm M = ‖M‖ := by
  rw [Matrix.frobenius_norm_def]
  simp_rw [Real.rpow_two, Real.norm_eq_abs, sq_abs]
  rw [← Real.sqrt_eq_rpow]
  rfl

/--
Exact identity `hsSq M = Matrix.trace (Mᵀ * M)`.

Use: `chebyshev1.hsSq_orthogonal_left` rewrites with this identity to establish exact
identity `hsSq (Q * M) = hsSq M`.

Article: chebyshev1, Proposition 1.3 via
`chebyshev1.Realization.hsNorm_linearResponse_bound`.

Source: mathlib, Mathlib.LinearAlgebra.Matrix.Hermitian and matrix norm theory — finite real
spectral theorem and Euclidean/Frobenius norm comparison.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem hsSq_eq_trace (M : Matrix d d ℝ) : hsSq M = Matrix.trace (Mᵀ * M) := by
  simp only [hsSq, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply, pow_two]
  exact Finset.sum_comm

variable [DecidableEq d]

/--
Exact identity `hsSq (Q * M) = hsSq M`.

Use: `chebyshev1.hsNorm_orthogonal_conjugation` rewrites with this identity to establish
exact identity `hsNorm (Qᵀ * M * Q) = hsNorm M`.

Article: chebyshev1, Proposition 1.3 via
`chebyshev1.Realization.hsNorm_linearResponse_bound`.

Source: mathlib, Mathlib.LinearAlgebra.Matrix.Hermitian and matrix norm theory — finite real
spectral theorem and Euclidean/Frobenius norm comparison.

Proof: Use the identities/estimates `chebyshev1.hsSq_eq_trace` with the arguments shown in
the proof.
-/
theorem hsSq_orthogonal_left (Q M : Matrix d d ℝ) (hQ : Qᵀ * Q = 1) :
    hsSq (Q * M) = hsSq M := by
  rw [hsSq_eq_trace, hsSq_eq_trace, Matrix.transpose_mul]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc Qᵀ Q M, hQ, Matrix.one_mul]

/--
Exact identity `hsSq (M * Q) = hsSq M`.

Use: `chebyshev1.hsNorm_orthogonal_conjugation` rewrites with this identity to establish
exact identity `hsNorm (Qᵀ * M * Q) = hsNorm M`.

Article: chebyshev1, Proposition 1.3 via
`chebyshev1.Realization.hsNorm_linearResponse_bound`.

Source: mathlib, Mathlib.LinearAlgebra.Matrix.Hermitian and matrix norm theory — finite real
spectral theorem and Euclidean/Frobenius norm comparison.

Proof: Use the identities/estimates `chebyshev1.hsSq_eq_trace` with the arguments shown in
the proof.
-/
theorem hsSq_orthogonal_right (Q M : Matrix d d ℝ) (hQ : Q * Qᵀ = 1) :
    hsSq (M * Q) = hsSq M := by
  rw [hsSq_eq_trace, hsSq_eq_trace, Matrix.transpose_mul,
    ← Matrix.mul_assoc, Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc Q Qᵀ (Mᵀ * M), hQ, Matrix.one_mul]

/--
Parseval identity for the spectral change of coordinates.

Exact identity `hsNorm (Qᵀ * M * Q) = hsNorm M`.

Use: `chebyshev1.Realization.hsNorm_linearResponse_bound` rewrites with this identity to
establish the stated quantitative bound `hsNorm (R.linearResponse N H E) ≤ R.gain I N *
Real.sqrt (∑ s ∈ Finset.range N, hsNorm (E s) ^ 2)`.

Article: chebyshev1, Proposition 1.3 via
`chebyshev1.Realization.hsNorm_linearResponse_bound`.

Source: mathlib, Mathlib.LinearAlgebra.Matrix.Hermitian and matrix norm theory — finite real
spectral theorem and Euclidean/Frobenius norm comparison.

Proof: Use the identities/estimates `chebyshev1.hsSq_orthogonal_right`,
`chebyshev1.hsSq_orthogonal_left` with the arguments shown in the proof.
-/
theorem hsNorm_orthogonal_conjugation (Q M : Matrix d d ℝ)
    (_hleft : Qᵀ * Q = 1) (hright : Q * Qᵀ = 1) :
    hsNorm (Qᵀ * M * Q) = hsNorm M := by
  unfold hsNorm
  rw [hsSq_orthogonal_right Q _ hright, hsSq_orthogonal_left Qᵀ M]
  simpa using hright

end
end chebyshev1

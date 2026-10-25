import chebyshev1.Realization.SpectralPair
import chebyshev1.Realization.GainBounds
import chebyshev1.Spectral.HilbertSchmidt

/-!
Article: chebyshev1, Proposition 1.3.
Proposition 1.3's Hilbert–Schmidt estimate in diagonal spectral coordinates.
Use: `chebyshev1.Realization.diagonal_hsNorm_bound` feeds
`chebyshev1.Realization.hsNorm_linearResponse_bound` (The Hilbert–Schmidt upper bound of
Proposition 1.3 for every symmetric Hessian).
Proof chain: `chebyshev1.Realization.hsNorm_linearResponse_bound` — chebyshev1, Proposition
1.3; Finite expansion, Hilbert–Schmidt bound and sharpness.
Source: mathlib, Mathlib.LinearAlgebra.Matrix.Hermitian and matrix norm theory — finite real
spectral theorem and Euclidean/Frobenius norm comparison. The needed form is proved here.
-/
namespace chebyshev1.Realization
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
variable {ι d : Type*} [Fintype ι] [DecidableEq ι] [Fintype d] [DecidableEq d]

/--
Defines `coordinateProjector` of type `Matrix d d ℝ` by `Matrix.diagonal (Pi.single i 1)`.

Use:
`_private.chebyshev1.Spectral.DiagonalResponse.0.chebyshev1.Realization.projector_left`
rewrites with this definition to establish the identity `coordinateProjector i *
Matrix.diagonal eig = eig i • coordinateProjector i`.

Article: chebyshev1, Corollary 4.4 via `chebyshev1.Prefix.opNorm_linearResponse_le`.

Source: mathlib, Mathlib.LinearAlgebra.Matrix.Hermitian and matrix norm theory — finite real
spectral theorem and Euclidean/Frobenius norm comparison.
-/
private def coordinateProjector (i : d) : Matrix d d ℝ := Matrix.diagonal (Pi.single i 1)

/--
Exact identity `coordinateProjector i * Matrix.diagonal eig = eig i • coordinateProjector i`.

Use: `chebyshev1.Realization.diagonal_linearResponse_entry` uses this identity to establish
exact identity `R.linearResponse N (Matrix.diagonal eig) E i j = ∑ s ∈ Finset.range N, R.kernel
N s (eig i) (eig j) * E s i j`.

Article: chebyshev1, Corollary 4.4 via `chebyshev1.Prefix.opNorm_linearResponse_le`.

Source: mathlib, Mathlib.LinearAlgebra.Matrix.Hermitian and matrix norm theory — finite real
spectral theorem and Euclidean/Frobenius norm comparison.

Proof: Separate `k = i` from its negation; prove the goal under each of these mutually
exclusive hypotheses.
-/
private theorem projector_left (eig : d → ℝ) (i : d) :
    coordinateProjector i * Matrix.diagonal eig = eig i • coordinateProjector i := by
  -- Separate `k = i` from its negation; prove the goal under each of these mutually exclusive
  -- hypotheses.
  ext k l
  by_cases hk : k = i
  · subst k
    simp only [coordinateProjector, Matrix.diagonal_mul, Matrix.smul_apply, smul_eq_mul]
    simp [Matrix.diagonal, Pi.single_apply]
  · simp only [coordinateProjector, Matrix.diagonal_mul, Matrix.smul_apply, smul_eq_mul]
    simp [Matrix.diagonal, Pi.single_apply, hk]

/--
Exact identity `Matrix.diagonal eig * coordinateProjector i = eig i • coordinateProjector i`.

Use: `chebyshev1.Realization.diagonal_linearResponse_entry` uses this identity to establish
exact identity `R.linearResponse N (Matrix.diagonal eig) E i j = ∑ s ∈ Finset.range N, R.kernel
N s (eig i) (eig j) * E s i j`.

Article: chebyshev1, Corollary 4.4 via `chebyshev1.Prefix.opNorm_linearResponse_le`.

Source: mathlib, Mathlib.LinearAlgebra.Matrix.Hermitian and matrix norm theory — finite real
spectral theorem and Euclidean/Frobenius norm comparison.

Proof: Separate `k = i` from its negation; prove the goal under each of these mutually
exclusive hypotheses.
-/
private theorem projector_right (eig : d → ℝ) (i : d) :
    Matrix.diagonal eig * coordinateProjector i = eig i • coordinateProjector i := by
  ext k l
  by_cases hk : k = i
  · subst k
    simp only [coordinateProjector, Matrix.diagonal_mul, Matrix.smul_apply, smul_eq_mul]
  · simp only [coordinateProjector, Matrix.diagonal_mul, Matrix.smul_apply, smul_eq_mul]
    simp [Matrix.diagonal, Pi.single_apply, hk]

/--
First variation in an orthonormal eigenbasis, entry by entry.

Exact identity `R.linearResponse N (Matrix.diagonal eig) E i j = ∑ s ∈ Finset.range N, R.kernel
N s (eig i) (eig j) * E s i j`.

Use: `chebyshev1.Realization.diagonal_entry_bound` rewrites with this identity to establish
the stated quantitative bound `(R.linearResponse N (Matrix.diagonal eig) E i j) ^ 2 ≤ (R.gain I
N) ^ 2 * ∑ s ∈ Finset.range N, (E s i j) ^ 2`.

Article: chebyshev1, Corollary 4.4 via `chebyshev1.Prefix.opNorm_linearResponse_le`.

Source: mathlib, Mathlib.LinearAlgebra.Matrix.Hermitian and matrix norm theory — finite real
spectral theorem and Euclidean/Frobenius norm comparison.

Proof: Use the identities/estimates `chebyshev1.Realization.spectralPair_linearResponse`,
`_private.chebyshev1.Spectral.DiagonalResponse.0.chebyshev1.Realization.projector_left`,
`_private.chebyshev1.Spectral.DiagonalResponse.0.chebyshev1.Realization.projector_right`
with the arguments shown in the proof.
-/
theorem diagonal_linearResponse_entry (R : Realization ι) (N : ℕ) (eig : d → ℝ)
    (E : ℕ → Matrix d d ℝ) (i j : d) :
    R.linearResponse N (Matrix.diagonal eig) E i j =
      ∑ s ∈ Finset.range N, R.kernel N s (eig i) (eig j) * E s i j := by
  -- Apply
  -- `_private.chebyshev1.Spectral.DiagonalResponse.0.chebyshev1.Realization.coordinateProjector`,
  -- `chebyshev1.Realization.spectralPair_linearResponse`,
  -- `_private.chebyshev1.Spectral.DiagonalResponse.0.chebyshev1.Realization.projector_left`
  -- to the displayed hypotheses, then match the resulting expression to the goal.
  have h := R.spectralPair_linearResponse N (Matrix.diagonal eig)
    (coordinateProjector i) (coordinateProjector j) E (eig i) (eig j)
    (projector_left eig i) (projector_right eig j)
  have he := congrArg (fun M : Matrix d d ℝ => M i j) h
  simpa [coordinateProjector, Matrix.diagonal_mul, Matrix.mul_diagonal, Pi.single_apply,
    Matrix.smul_apply, Matrix.sum_apply] using he

/--
Cauchy–Schwarz on one spectral entry with the realization-level sharp coefficient.

The stated quantitative bound `(R.linearResponse N (Matrix.diagonal eig) E i j) ^ 2 ≤ (R.gain I
N) ^ 2 * ∑ s ∈ Finset.range N, (E s i j) ^ 2`.

Use: `chebyshev1.Realization.diagonal_hsSq_bound` uses this bound to establish the stated
quantitative bound `hsSq (R.linearResponse N (Matrix.diagonal eig) E) ≤ (R.gain I N) ^ 2 * ∑ s
∈ Finset.range N, hsSq (E s)`.

Article: chebyshev1, Proposition 1.3 via
`chebyshev1.Realization.hsNorm_linearResponse_bound`.

Source: mathlib, Mathlib.LinearAlgebra.Matrix.Hermitian and matrix norm theory — finite real
spectral theorem and Euclidean/Frobenius norm comparison.

Proof: Use the identities/estimates `chebyshev1.Realization.diagonal_linearResponse_entry`,
`chebyshev1.Realization.kernelNorm_le_gain`, `chebyshev1.Realization.gain_nonneg` with
the arguments shown in the proof.
-/
theorem diagonal_entry_bound (R : Realization ι) (I : SpectralInterval) (N : ℕ)
    (eig : d → ℝ) (heig : ∀ i, eig i ∈ Set.Icc I.mu I.L)
    (E : ℕ → Matrix d d ℝ) (i j : d) :
    (R.linearResponse N (Matrix.diagonal eig) E i j) ^ 2 ≤
      (R.gain I N) ^ 2 * ∑ s ∈ Finset.range N, (E s i j) ^ 2 := by
  -- Use the identities/estimates `chebyshev1.Realization.diagonal_linearResponse_entry`,
  -- `chebyshev1.Realization.kernelNorm_le_gain`, `chebyshev1.Realization.gain_nonneg`
  -- with the arguments shown in the proof.
  rw [diagonal_linearResponse_entry]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.range N)
    (fun s => R.kernel N s (eig i) (eig j)) (fun s => E s i j)
  have hnorm := R.kernelNorm_le_gain I N (heig i) (heig j)
  have hs : (∑ s ∈ Finset.range N, (R.kernel N s (eig i) (eig j)) ^ 2) ≤ (R.gain I N) ^ 2 := by
    have hsqrt : R.kernelNorm N (eig i) (eig j) ^ 2 =
        ∑ s ∈ Finset.range N, (R.kernel N s (eig i) (eig j)) ^ 2 :=
      Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
    have hn0 : 0 ≤ R.kernelNorm N (eig i) (eig j) := Real.sqrt_nonneg _
    have hsq := (sq_le_sq₀ hn0 (R.gain_nonneg I N)).mpr hnorm
    rw [hsqrt] at hsq
    exact hsq
  exact hcs.trans (mul_le_mul_of_nonneg_right hs (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))

/--
Proposition 1.3's Hilbert–Schmidt estimate in diagonal spectral coordinates.

The stated quantitative bound `hsSq (R.linearResponse N (Matrix.diagonal eig) E) ≤ (R.gain I N)
^ 2 * ∑ s ∈ Finset.range N, hsSq (E s)`.

Use: `chebyshev1.Realization.diagonal_hsNorm_bound` uses this bound to establish the stated
quantitative bound `hsNorm (R.linearResponse N (Matrix.diagonal eig) E) ≤ R.gain I N *
Real.sqrt (∑ s ∈ Finset.range N, hsNorm (E s) ^ 2)`.

Article: chebyshev1, Proposition 1.3 via
`chebyshev1.Realization.hsNorm_linearResponse_bound`.

Source: mathlib, Mathlib.LinearAlgebra.Matrix.Hermitian and matrix norm theory — finite real
spectral theorem and Euclidean/Frobenius norm comparison.

Proof: Identify the summands/integrands on their required domain before replacing the sum or
integral.
-/
theorem diagonal_hsSq_bound (R : Realization ι) (I : SpectralInterval) (N : ℕ)
    (eig : d → ℝ) (heig : ∀ i, eig i ∈ Set.Icc I.mu I.L)
    (E : ℕ → Matrix d d ℝ) :
    hsSq (R.linearResponse N (Matrix.diagonal eig) E) ≤
      (R.gain I N) ^ 2 * ∑ s ∈ Finset.range N, hsSq (E s) := by
  -- Identify the summands/integrands on their required domain before replacing the sum or
  -- integral.
  calc
    _ ≤ ∑ i, ∑ j, (R.gain I N) ^ 2 * ∑ s ∈ Finset.range N, (E s i j) ^ 2 :=
      Finset.sum_le_sum (fun i _ => Finset.sum_le_sum
        (fun j _ => diagonal_entry_bound R I N eig heig E i j))
    _ = _ := by
      simp only [hsSq, ← Finset.mul_sum]
      congr 1
      calc
        _ = ∑ i, ∑ s ∈ Finset.range N, ∑ j, (E s i j) ^ 2 := by
          apply Finset.sum_congr rfl
          intro i _
          rw [Finset.sum_comm]
        _ = _ := Finset.sum_comm

/--
The stated quantitative bound `hsNorm (R.linearResponse N (Matrix.diagonal eig) E) ≤ R.gain I N
* Real.sqrt (∑ s ∈ Finset.range N, hsNorm (E s) ^ 2)`.

Use: `chebyshev1.Realization.hsNorm_linearResponse_bound` uses this bound to establish the
stated quantitative bound `hsNorm (R.linearResponse N H E) ≤ R.gain I N * Real.sqrt (∑ s ∈
Finset.range N, hsNorm (E s) ^ 2)`.

Article: chebyshev1, Proposition 1.3 via
`chebyshev1.Realization.hsNorm_linearResponse_bound`.

Source: mathlib, Mathlib.LinearAlgebra.Matrix.Hermitian and matrix norm theory — finite real
spectral theorem and Euclidean/Frobenius norm comparison.

Proof: Use the identities/estimates `chebyshev1.Realization.diagonal_hsSq_bound`,
`chebyshev1.Realization.gain_nonneg`, `chebyshev1.hsNorm_nonneg` with the arguments
shown in the proof.
-/
theorem diagonal_hsNorm_bound (R : Realization ι) (I : SpectralInterval) (N : ℕ)
    (eig : d → ℝ) (heig : ∀ i, eig i ∈ Set.Icc I.mu I.L)
    (E : ℕ → Matrix d d ℝ) :
    hsNorm (R.linearResponse N (Matrix.diagonal eig) E) ≤
      R.gain I N * Real.sqrt (∑ s ∈ Finset.range N, hsNorm (E s) ^ 2) := by
  -- Use the identities/estimates `chebyshev1.Realization.diagonal_hsSq_bound`,
  -- `chebyshev1.Realization.gain_nonneg`, `chebyshev1.hsNorm_nonneg` with the
  -- arguments shown in the proof.
  have h := diagonal_hsSq_bound R I N eig heig E
  simp_rw [← hsNorm_sq] at h
  have ht : 0 ≤ ∑ s ∈ Finset.range N, hsNorm (E s) ^ 2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have he := Real.sq_sqrt ht
  have ha := R.gain_nonneg I N
  have hb := hsNorm_nonneg (R.linearResponse N (Matrix.diagonal eig) E)
  have hc := Real.sqrt_nonneg (∑ s ∈ Finset.range N, hsNorm (E s) ^ 2)
  apply (sq_le_sq₀ hb (mul_nonneg ha hc)).mp
  rw [mul_pow, he]
  exact h

end
end chebyshev1.Realization

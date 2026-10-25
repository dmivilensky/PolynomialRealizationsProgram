import chebyshev1.Spectral.LinearResponseBound

/-!
Article: chebyshev1, Proposition 1.3.
Proposition 1.3: no smaller nonnegative universal HS coefficient is possible.
Use: `chebyshev1.Realization.hs_constant_minimal` feeds `chebyshev2.Jacobi.gain_minimal`
(gain minimal).
Source: mathlib, Mathlib.LinearAlgebra.Matrix.Hermitian and matrix norm theory — finite real
spectral theorem and Euclidean/Frobenius norm comparison. The needed form is proved here.
-/
namespace chebyshev1
noncomputable section
open scoped Matrix BigOperators

/--
One matrix entry, mapping the second eigenmode into the first.

Use: `chebyshev1.Realization.witnessDrift` uses this definition in the displayed
construction of `witnessDrift`. Its inputs and component formulas are fixed by that definition.

Article: chebyshev1, Proposition 1.3 via `chebyshev1.Realization.hs_bound_attained`.

Source: mathlib, Mathlib.LinearAlgebra.Matrix.Hermitian and matrix norm theory — finite real
spectral theorem and Euclidean/Frobenius norm comparison.
-/
def spectralWitness (c : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![0, c; 0, 0]

/--
Exact identity `hsNorm (spectralWitness c) = |c|`.

Use: `chebyshev1.Realization.witness_input_norm` rewrites with this identity to establish
exact identity `Real.sqrt (∑ s ∈ Finset.range N, hsNorm (R.witnessDrift N lam nu s) ^ 2) =
R.kernelNorm N lam nu`.

Article: chebyshev1, Proposition 1.3 via `chebyshev1.Realization.hs_bound_attained`.

Source: mathlib, Mathlib.LinearAlgebra.Matrix.Hermitian and matrix norm theory — finite real
spectral theorem and Euclidean/Frobenius norm comparison.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem hsNorm_spectralWitness (c : ℝ) : hsNorm (spectralWitness c) = |c| := by simp [hsNorm, hsSq, spectralWitness, Fin.sum_univ_two, Real.sqrt_sq_eq_abs]

namespace Realization
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/--
Defines `witnessDrift` of type `Matrix (Fin 2) (Fin 2) ℝ` by `spectralWitness (R.kernel N s lam
nu)`.

Use: `chebyshev1.Realization.hs_bound_attained` uses this definition to establish the
identity stated in that declaration.

Article: chebyshev1, Proposition 1.3 via `chebyshev1.Realization.hs_bound_attained`.

Source: mathlib, Mathlib.LinearAlgebra.Matrix.Hermitian and matrix norm theory — finite real
spectral theorem and Euclidean/Frobenius norm comparison.
-/
def witnessDrift (R : Realization ι) (N : ℕ) (lam nu : ℝ) (s : ℕ) :
    Matrix (Fin 2) (Fin 2) ℝ := spectralWitness (R.kernel N s lam nu)

/--
Exact identity `R.linearResponse N (Matrix.diagonal ![lam, nu]) (R.witnessDrift N lam nu) =
spectralWitness (∑ s ∈ Finset.range N, (R.kernel N s lam nu) ^ 2)`.

Use: `chebyshev1.Realization.witness_output_norm` rewrites with this identity to establish
exact identity `hsNorm (R.linearResponse N (Matrix.diagonal ![lam, nu]) (R.witnessDrift N lam
nu)) = (R.kernelNorm N lam nu) ^ 2`.

Article: chebyshev1, Proposition 1.3 via `chebyshev1.Realization.hs_bound_attained`.

Source: mathlib, Mathlib.LinearAlgebra.Matrix.Hermitian and matrix norm theory — finite real
spectral theorem and Euclidean/Frobenius norm comparison.

Proof: Check each member of the finite index type; no case is omitted.
-/
theorem witness_response (R : Realization ι) (N : ℕ) (lam nu : ℝ) :
    R.linearResponse N (Matrix.diagonal ![lam, nu]) (R.witnessDrift N lam nu) =
      spectralWitness (∑ s ∈ Finset.range N, (R.kernel N s lam nu) ^ 2) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diagonal_linearResponse_entry, witnessDrift, spectralWitness, pow_two]

/--
Exact identity `Real.sqrt (∑ s ∈ Finset.range N, hsNorm (R.witnessDrift N lam nu s) ^ 2) =
R.kernelNorm N lam nu`.

Use: `chebyshev1.Realization.hs_bound_attained` rewrites with this identity to establish
the identity stated in that declaration.

Article: chebyshev1, Proposition 1.3 via `chebyshev1.Realization.hs_bound_attained`.

Source: mathlib, Mathlib.LinearAlgebra.Matrix.Hermitian and matrix norm theory — finite real
spectral theorem and Euclidean/Frobenius norm comparison.

Proof: Use the identities/estimates `chebyshev1.hsNorm_spectralWitness` with the arguments
shown in the proof.
-/
theorem witness_input_norm (R : Realization ι) (N : ℕ) (lam nu : ℝ) :
    Real.sqrt (∑ s ∈ Finset.range N, hsNorm (R.witnessDrift N lam nu s) ^ 2) =
      R.kernelNorm N lam nu := by
  simp only [witnessDrift, hsNorm_spectralWitness, sq_abs]
  rfl

/--
Exact identity `hsNorm (R.linearResponse N (Matrix.diagonal ![lam, nu]) (R.witnessDrift N lam
nu)) = (R.kernelNorm N lam nu) ^ 2`.

Use: `chebyshev1.Realization.hs_bound_attained` rewrites with this identity to establish
the identity stated in that declaration.

Article: chebyshev1, Proposition 1.3 via `chebyshev1.Realization.hs_bound_attained`.

Source: mathlib, Mathlib.LinearAlgebra.Matrix.Hermitian and matrix norm theory — finite real
spectral theorem and Euclidean/Frobenius norm comparison.

Proof: Use the identities/estimates `chebyshev1.Realization.witness_response`,
`chebyshev1.hsNorm_spectralWitness` with the arguments shown in the proof.
-/
theorem witness_output_norm (R : Realization ι) (N : ℕ) (lam nu : ℝ) :
    hsNorm (R.linearResponse N (Matrix.diagonal ![lam, nu]) (R.witnessDrift N lam nu)) =
      (R.kernelNorm N lam nu) ^ 2 := by
  rw [witness_response, hsNorm_spectralWitness,
    abs_of_nonneg (Finset.sum_nonneg (fun _ _ => sq_nonneg _))]
  exact (Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => sq_nonneg _))).symm

/--
The global attaining example from Appendix A.2, with no nonzero-gain assumption.

Use: `chebyshev1.Realization.hs_constant_minimal` uses this identity to establish the
stated quantitative bound `R.gain I N ≤ C`.

Article: chebyshev1, Proposition 1.3.

Source: mathlib, Mathlib.LinearAlgebra.Matrix.Hermitian and matrix norm theory — finite real
spectral theorem and Euclidean/Frobenius norm comparison.

Proof: Check each member of the finite index type; no case is omitted.
-/
theorem hs_bound_attained (R : Realization ι) (I : SpectralInterval) (N : ℕ) :
    ∃ H : Matrix (Fin 2) (Fin 2) ℝ, H.IsHermitian ∧ spectrum ℝ H ⊆ Set.Icc I.mu I.L ∧
      ∃ E : ℕ → Matrix (Fin 2) (Fin 2) ℝ,
        Real.sqrt (∑ s ∈ Finset.range N, hsNorm (E s) ^ 2) = R.gain I N ∧
        hsNorm (R.linearResponse N H E) = (R.gain I N) ^ 2 := by
  -- Check each member of the finite index type; no case is omitted.
  obtain ⟨lam, hl, nu, hn, he⟩ := R.gain_attained I N
  refine ⟨Matrix.diagonal ![lam, nu], ?_, ?_, R.witnessDrift N lam nu, ?_, ?_⟩
  · simp [Matrix.IsHermitian]
  · rw [spectrum_diagonal]
    rintro x ⟨i, rfl⟩
    fin_cases i
    · exact hl
    · exact hn
  · rw [witness_input_norm, he]
  · rw [witness_output_norm, he]

/--
Proposition 1.3: no smaller nonnegative universal HS coefficient is possible.

The stated quantitative bound `R.gain I N ≤ C`.

Use: `chebyshev2.Jacobi.gain_minimal` uses this bound to establish the stated quantitative
bound `J.gain I h ≤ C`.

Article: chebyshev1, Proposition 1.3.

Source: mathlib, Mathlib.LinearAlgebra.Matrix.Hermitian and matrix norm theory — finite real
spectral theorem and Euclidean/Frobenius norm comparison.

Proof: Separate `R.gain I N = 0` from its negation; prove the goal under each of these mutually
exclusive hypotheses.
-/
theorem hs_constant_minimal (R : Realization ι) (I : SpectralInterval) (N : ℕ)
    (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ (H : Matrix (Fin 2) (Fin 2) ℝ), H.IsHermitian →
      spectrum ℝ H ⊆ Set.Icc I.mu I.L → ∀ E : ℕ → Matrix (Fin 2) (Fin 2) ℝ,
        hsNorm (R.linearResponse N H E) ≤
          C * Real.sqrt (∑ s ∈ Finset.range N, hsNorm (E s) ^ 2)) : R.gain I N ≤ C := by
  -- Separate `R.gain I N = 0` from its negation; prove the goal under each of these mutually
  -- exclusive hypotheses.
  obtain ⟨H, hH, hs, E, he, ho⟩ := R.hs_bound_attained I N
  have hb := hbound H hH hs E
  rw [he, ho] at hb
  by_cases hz : R.gain I N = 0
  · simpa [hz] using hC
  · have hp : 0 < R.gain I N := lt_of_le_of_ne (R.gain_nonneg I N) (Ne.symm hz)
    nlinarith

end Realization
end
end chebyshev1

import «2606.16671v2».Spectral.OperatorNorm
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic

/-!
Article: 2606.16671v2, Lemma E.2.
The first spectral measure represents polynomial moments exactly.
Use: `«2606.16671v2».SpectralBasis.moment` feeds `«2606.16671v2».SineJacobi.spectral_moment` (The
first spectral measure of the explicit sine chain acts on every polynomial as the discrete sine
measure in E.2).
Proof chain: `«2606.16671v2».SineJacobi.leading_orthogonality` — 2606.16671v2, Lemma E.2;
Root-of-unity Rogers recurrence, Fourier coefficients and orthogonality.
Source: mathlib, Mathlib.LinearAlgebra.Matrix.Hermitian and matrix norm theory — finite real
spectral theorem and Euclidean/Frobenius norm comparison. The needed form is proved here.
-/
namespace «2606.16671v2».SpectralBasis
noncomputable section
open Polynomial
open scoped BigOperators Matrix
set_option backward.isDefEq.respectTransparency false
variable {d : Type*} [Fintype d] [DecidableEq d]
variable {H : Matrix d d ℝ} (B : SpectralBasis H)

/--
Defines `weight` of type `ℝ` by `(B.Q s j)^2`.

Use: `«2606.16671v2».SpectralBasis.adjugate_eigenvalue_diagonal` uses this definition to
establish exact identity `(Matrix.scalar d (B.eigenvalues j)-H).adjugate s s = B.weight s
j*H.charpoly.derivative.eval (B.eigenvalues j)`.

Article: 2606.16671v2, Theorem E.1 via `«2606.16671v2».SineJacobi.spectral_weight`.

Source: mathlib, Mathlib.LinearAlgebra.Matrix.Hermitian and matrix norm theory — finite real
spectral theorem and Euclidean/Frobenius norm comparison.
-/
def weight (s j : d) : ℝ := (B.Q s j)^2

/--
The stated quantitative bound `0 ≤ B.weight s j`.

Use: `«2606.16671v2».JacobiData.spectral_endpoint_positive` uses this bound to establish the
stated quantitative bound `0 < B.weight 0 j ∧ 0 < B.weight (Fin.last n) j`.

Article: 2606.16671v2, Theorem E.1 via `«2606.16671v2».SineJacobi.spectral_weight`.

Source: mathlib, Mathlib.LinearAlgebra.Matrix.Hermitian and matrix norm theory — finite real
spectral theorem and Euclidean/Frobenius norm comparison.

Proof: The displayed proof term instantiates the cited result with exactly the parameters and
hypotheses of this assertion.
-/
theorem weight_nonneg (s j : d) : 0 ≤ B.weight s j := sq_nonneg _

/--
Exact identity `∑ j, B.weight s j = 1`.

Use: `«2606.16671v2».JacobiData.persymmetric_of_spectral_weights` rewrites with this identity
to establish the identity `(J.matrix 0 (n+1)).submatrix Fin.rev Fin.rev = J.matrix 0 (n+1)`.

Article: 2606.16671v2, Theorem E.1 via `«2606.16671v2».SineJacobi.spectral_weight`.

Source: mathlib, Mathlib.LinearAlgebra.Matrix.Hermitian and matrix norm theory — finite real
spectral theorem and Euclidean/Frobenius norm comparison.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem weight_sum (s : d) : ∑ j, B.weight s j = 1 := by
  have he := congrArg (fun M : Matrix d d ℝ => M s s) B.mul_transpose
  simpa only [weight, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply_eq, pow_two] using he

/--
Exact identity `B.Q*Matrix.diagonal B.eigenvalues*B.Qᵀ = H`.

Use: `«2606.16671v2».SpectralBasis.adjugate_shift` rewrites with this identity to establish
exact identity `(Matrix.scalar d x-H).adjugate = B.Q * Matrix.diagonal (fun j => ∏ k ∈
Finset.univ.erase j, (x-B.eigenvalues k)) * B.Qᵀ`.

Article: 2606.16671v2, Lemma E.5 via `«2606.16671v2».JacobiData.spectral_weight_cofactor`.

Source: mathlib, Mathlib.LinearAlgebra.Matrix.Hermitian and matrix norm theory — finite real
spectral theorem and Euclidean/Frobenius norm comparison.

Proof: Expand/rewrite the named definitions and identities appearing in the tactic block; the
remaining goal is a direct simplification or algebraic consequence.
-/
theorem reconstruct : B.Q*Matrix.diagonal B.eigenvalues*B.Qᵀ = H := by
  rw [← B.diagonalize]
  calc _ = (B.Q*B.Qᵀ)*H*(B.Q*B.Qᵀ) := by simp only [Matrix.mul_assoc]
       _ = H := by rw [B.mul_transpose]; simp

/--
Exact identity `H.charpoly = ∏ j, (X-C (B.eigenvalues j))`.

Use: `«2606.16671v2».SpectralBasis.charpoly_derivative` rewrites with this identity to
establish exact identity `H.charpoly.derivative.eval (B.eigenvalues j) = ∏ k ∈
Finset.univ.erase j, (B.eigenvalues j-B.eigenvalues k)`.

Article: 2606.16671v2, Lemma E.5 via `«2606.16671v2».JacobiData.spectral_endpoint_product`.

Source: mathlib, Mathlib.LinearAlgebra.Matrix.Hermitian and matrix norm theory — finite real
spectral theorem and Euclidean/Frobenius norm comparison.

Proof: Expand/rewrite the named definitions and identities appearing in the tactic block; the
remaining goal is a direct simplification or algebraic consequence.
-/
theorem charpoly_factor : H.charpoly = ∏ j, (X-C (B.eigenvalues j)) := by
  rw [← Matrix.charpoly_diagonal, ← B.diagonalize, Matrix.charpoly_mul_comm,
    ← Matrix.mul_assoc, B.mul_transpose, Matrix.one_mul]

/--
Derivative at a labelled eigenvalue, without any analytic residue argument.

Exact identity `H.charpoly.derivative.eval (B.eigenvalues j) = ∏ k ∈ Finset.univ.erase j,
(B.eigenvalues j-B.eigenvalues k)`.

Use: `«2606.16671v2».SpectralBasis.adjugate_eigenvalue_diagonal` rewrites with this identity to
establish exact identity `(Matrix.scalar d (B.eigenvalues j)-H).adjugate s s = B.weight s
j*H.charpoly.derivative.eval (B.eigenvalues j)`.

Article: 2606.16671v2, Theorem E.1 via `«2606.16671v2».SineJacobi.spectral_weight`.

Source: mathlib, Mathlib.LinearAlgebra.Matrix.Hermitian and matrix norm theory — finite real
spectral theorem and Euclidean/Frobenius norm comparison.

Proof: Use the identities/estimates `«2606.16671v2».SpectralBasis.charpoly_factor` with the
arguments shown in the proof.
-/
theorem charpoly_derivative (j : d) : H.charpoly.derivative.eval (B.eigenvalues j) =
    ∏ k ∈ Finset.univ.erase j, (B.eigenvalues j-B.eigenvalues k) := by
  rw [B.charpoly_factor, ← Finset.mul_prod_erase Finset.univ (fun k => X-C (B.eigenvalues k))
    (Finset.mem_univ j), derivative_mul]
  simp [eval_prod]

/--
The precise assertion is `H.charpoly.derivative.eval (B.eigenvalues j) ≠ 0`.

Use: `«2606.16671v2».JacobiData.persymmetric_of_spectral_weights` uses this assertion to
establish exact identity `(J.matrix 0 (n+1)).submatrix Fin.rev Fin.rev = J.matrix 0 (n+1)`.

Article: 2606.16671v2, Theorem E.1 via `«2606.16671v2».SineJacobi.spectral_weight`.

Source: mathlib, Mathlib.LinearAlgebra.Matrix.Hermitian and matrix norm theory — finite real
spectral theorem and Euclidean/Frobenius norm comparison.

Proof: Use the identities/estimates `«2606.16671v2».SpectralBasis.charpoly_derivative` with the
arguments shown in the proof.
-/
theorem charpoly_derivative_ne (hi : Function.Injective B.eigenvalues) (j : d) :
    H.charpoly.derivative.eval (B.eigenvalues j) ≠ 0 := by
  rw [B.charpoly_derivative]
  exact Finset.prod_ne_zero_iff.mpr (fun k hk => sub_ne_zero.mpr
    (fun he => (Finset.mem_erase.mp hk).1 (hi he).symm))

/--
Exact identity `(Matrix.scalar d x-H).adjugate = B.Q * Matrix.diagonal (fun j => ∏ k ∈
Finset.univ.erase j, (x-B.eigenvalues k)) * B.Qᵀ`.

Use: `«2606.16671v2».SpectralBasis.adjugate_eigenvalue_diagonal` rewrites with this identity to
establish exact identity `(Matrix.scalar d (B.eigenvalues j)-H).adjugate s s = B.weight s
j*H.charpoly.derivative.eval (B.eigenvalues j)`.

Article: 2606.16671v2, Lemma E.5 via `«2606.16671v2».JacobiData.spectral_weight_cofactor`.

Source: mathlib, Mathlib.LinearAlgebra.Matrix.Hermitian and matrix norm theory — finite real
spectral theorem and Euclidean/Frobenius norm comparison.

Proof: Use the identities/estimates `«2606.16671v2».SpectralBasis.reconstruct` with the
arguments shown in the proof.
-/
theorem adjugate_shift (x : ℝ) :
    (Matrix.scalar d x-H).adjugate =
      B.Q * Matrix.diagonal (fun j => ∏ k ∈ Finset.univ.erase j, (x-B.eigenvalues k)) * B.Qᵀ := by
  -- Use the identities/estimates `«2606.16671v2».SpectralBasis.reconstruct` with the arguments
  -- shown in the proof.
  have hq : B.Q.adjugate = B.Q.det • B.Qᵀ := by
    have hh := congrArg (fun M : Matrix d d ℝ => M*B.Qᵀ) (Matrix.adjugate_mul B.Q)
    simpa only [Matrix.mul_assoc, B.mul_transpose, Matrix.mul_one, Matrix.smul_mul,
      Matrix.one_mul] using hh
  have hqt : B.Qᵀ.adjugate = B.Q.det • B.Q := by
    have hh := congrArg (fun M : Matrix d d ℝ => M*B.Q) (Matrix.adjugate_mul B.Qᵀ)
    simpa only [Matrix.mul_assoc, B.transpose_mul, Matrix.mul_one, Matrix.smul_mul,
      Matrix.one_mul, Matrix.det_transpose] using hh
  have hd : B.Q.det*B.Q.det = 1 := by
    have hh := congrArg Matrix.det B.mul_transpose
    simpa only [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] using hh
  have hs : Matrix.scalar d x-H =
      B.Q*Matrix.diagonal (fun j => x-B.eigenvalues j)*B.Qᵀ := by
    rw [show Matrix.diagonal (fun j => x-B.eigenvalues j) =
      Matrix.scalar d x-Matrix.diagonal B.eigenvalues by
        change Matrix.diagonal ((fun _ => x)-B.eigenvalues) =
          Matrix.diagonal (fun _ => x)-Matrix.diagonal B.eigenvalues
        exact (Matrix.diagonal_sub (fun _ => x) B.eigenvalues).symm]
    rw [Matrix.mul_sub, Matrix.sub_mul, B.reconstruct]
    simp [Matrix.scalar, Algebra.algebraMap_eq_smul_one,
      B.mul_transpose]
  rw [hs, Matrix.adjugate_mul_distrib, Matrix.adjugate_mul_distrib,
    Matrix.adjugate_diagonal, hq, hqt]
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hd, one_smul, Matrix.mul_assoc]

/--
A spectral weight is the diagonal cofactor divided by the characteristic derivative.

Exact identity `(Matrix.scalar d (B.eigenvalues j)-H).adjugate s s = B.weight s
j*H.charpoly.derivative.eval (B.eigenvalues j)`.

Use: `«2606.16671v2».JacobiData.spectral_weight_cofactor` uses this identity to establish exact
identity `B.weight s j*(J.leading (n+1)).derivative.eval (B.eigenvalues j) = (J.leading
s.val).eval (B.eigenvalues j)* (J.block (s.val+1) (n-s.val)).eval (B.eigenvalues j)`.

Article: 2606.16671v2, Lemma E.5 via `«2606.16671v2».JacobiData.spectral_weight_cofactor`.

Source: mathlib, Mathlib.LinearAlgebra.Matrix.Hermitian and matrix norm theory — finite real
spectral theorem and Euclidean/Frobenius norm comparison.

Proof: Use the identities/estimates `«2606.16671v2».SpectralBasis.adjugate_shift`,
`«2606.16671v2».SpectralBasis.charpoly_derivative` with the arguments shown in the proof.
-/
theorem adjugate_eigenvalue_diagonal (_hi : Function.Injective B.eigenvalues) (s j : d) :
    (Matrix.scalar d (B.eigenvalues j)-H).adjugate s s =
      B.weight s j*H.charpoly.derivative.eval (B.eigenvalues j) := by
  -- Use the identities/estimates `«2606.16671v2».SpectralBasis.adjugate_shift`,
  -- `«2606.16671v2».SpectralBasis.charpoly_derivative` with the arguments shown in the proof.
  rw [B.adjugate_shift, Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply]
  rw [Finset.sum_eq_single j]
  · rw [B.charpoly_derivative]
    unfold weight
    ring
  · intro k _ hk
    have hz : (∏ t ∈ Finset.univ.erase k, (B.eigenvalues j-B.eigenvalues t)) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hk.symm, Finset.mem_univ j⟩)
      simp
    rw [hz]
    ring
  · simp


/--
Exact identity `aeval H p = (ofHermitian H hH).Q* Matrix.diagonal (fun j => p.eval
((ofHermitian H hH).eigenvalues j))*(ofHermitian H hH).Qᵀ`.

Use: `«2606.16671v2».SpectralBasis.aeval_transpose` rewrites with this identity to establish
exact identity `(aeval H p)ᵀ = aeval H p`.

Article: 2606.16671v2, Lemma E.2 via `«2606.16671v2».SineJacobi.leading_orthogonality`.

Source: mathlib, Mathlib.LinearAlgebra.Matrix.Hermitian and matrix norm theory — finite real
spectral theorem and Euclidean/Frobenius norm comparison.

Proof: Use the identities/estimates `«2606.16671v2».aeval_coordinates` with the arguments shown
in the proof.
-/
theorem aeval_reconstruct (p : ℝ[X]) (hH : H.IsHermitian) :
    aeval H p = (ofHermitian H hH).Q*
      Matrix.diagonal (fun j => p.eval ((ofHermitian H hH).eigenvalues j))*(ofHermitian H hH).Qᵀ := by
  -- Use the identities/estimates `«2606.16671v2».aeval_coordinates` with the arguments shown
  -- in the proof.
  let A := ofHermitian H hH
  have hh := congrArg (fun M : Matrix d d ℝ => A.Q*M*A.Qᵀ) («2606.16671v2».aeval_coordinates p H hH)
  change A.Q*(A.Qᵀ*aeval H p*A.Q)*A.Qᵀ = _ at hh
  have he : A.Q*(A.Qᵀ*aeval H p*A.Q)*A.Qᵀ = aeval H p := by
    calc _ = (A.Q*A.Qᵀ)*aeval H p*(A.Q*A.Qᵀ) := by simp only [Matrix.mul_assoc]
         _ = _ := by rw [A.mul_transpose]; simp
  exact he.symm.trans hh

/--
Exact identity `(aeval H p)ᵀ = aeval H p`.

Use: `«2606.16671v2».JacobiData.leading_orthogonality` uses this identity to establish the
precise assertion is `let B`.

Article: 2606.16671v2, Lemma E.2 via `«2606.16671v2».SineJacobi.leading_orthogonality`.

Source: mathlib, Mathlib.LinearAlgebra.Matrix.Hermitian and matrix norm theory — finite real
spectral theorem and Euclidean/Frobenius norm comparison.

Proof: Use the identities/estimates `«2606.16671v2».SpectralBasis.aeval_reconstruct` with the
arguments shown in the proof.
-/
theorem aeval_transpose (p : ℝ[X]) (hH : H.IsHermitian) : (aeval H p)ᵀ = aeval H p := by
  rw [aeval_reconstruct p hH]
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.diagonal_transpose, Matrix.mul_assoc]

/--
The first spectral measure represents polynomial moments exactly.

Exact identity `(aeval H p) s s = ∑ j, (ofHermitian H hH).weight s j*p.eval ((ofHermitian H
hH).eigenvalues j)`.

Use: `«2606.16671v2».JacobiData.leading_orthogonality` uses this identity to establish the
precise assertion is `let B`.

Article: 2606.16671v2, Lemma E.2 via `«2606.16671v2».SineJacobi.leading_orthogonality`.

Source: mathlib, Mathlib.LinearAlgebra.Matrix.Hermitian and matrix norm theory — finite real
spectral theorem and Euclidean/Frobenius norm comparison.

Proof: Identify the summands/integrands on their required domain before replacing the sum or
integral.
-/
theorem moment (p : ℝ[X]) (hH : H.IsHermitian) (s : d) :
    (aeval H p) s s = ∑ j, (ofHermitian H hH).weight s j*p.eval ((ofHermitian H hH).eigenvalues j) := by
  rw [aeval_reconstruct p hH, Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply, weight]
  apply Finset.sum_congr rfl
  intro j _
  ring

end
end «2606.16671v2».SpectralBasis

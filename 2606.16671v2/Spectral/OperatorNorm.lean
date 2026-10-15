import «2606.16671v2».Spectral.Basis
import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
Article: 2606.16671v2, Corollary 5.4.
Spectral calculus bound for any polynomial, in the actual Euclidean operator norm.
Use: `«2606.16671v2».opNorm_residual_le` feeds `«2606.16671v2».Nonlinear.MethodFamily.transfer_le`
(The total finite drift bound used for nonlinear objectives).
Proof chain: `«2606.16671v2».Nonlinear.lipschitzHessian_error_le` — 2606.16671v2, Corollary 5.4;
Lipschitz-Hessian error bound for both methods.
Source: mathlib, Mathlib.LinearAlgebra.Matrix.Hermitian and matrix norm theory — finite real
spectral theorem and Euclidean/Frobenius norm comparison. The needed form is proved here.
-/
namespace «2606.16671v2»
noncomputable section
open scoped Matrix Matrix.Norms.L2Operator
open Polynomial
variable {d : Type*} [Fintype d] [DecidableEq d]

/--
The Euclidean operator norm, independent of other matrix norm scopes.

Use: `«2606.16671v2».opNorm_aeval_eq` rewrites with this definition to establish the identity
`opNorm (aeval H p) = ‖fun i => p.eval (hH.eigenvalues i)‖`.

Article: 2606.16671v2, Corollary 4.4 via `«2606.16671v2».Prefix.opNorm_linearResponse_le`.

Source: mathlib, Mathlib.LinearAlgebra.Matrix.Hermitian and matrix norm theory — finite real
spectral theorem and Euclidean/Frobenius norm comparison.
-/
def opNorm (M : Matrix d d ℝ) : ℝ := ‖M‖

/--
The stated quantitative bound `0 ≤ opNorm M`.

Use: `«2606.16671v2».JacobiData.opNorm_operatorWord_le` uses this bound to establish the stated
quantitative bound `opNorm (J.operatorWord I H E n times) ≤ delta ^ times.card *
J.partitionWeight n times`.

Article: 2606.16671v2, Corollary 4.4 via `«2606.16671v2».Prefix.opNorm_finiteDrift_le`.

Source: mathlib, Mathlib.LinearAlgebra.Matrix.Hermitian and matrix norm theory — finite real
spectral theorem and Euclidean/Frobenius norm comparison.

Proof: The displayed proof term instantiates the cited result with exactly the parameters and
hypotheses of this assertion.
-/
theorem opNorm_nonneg (M : Matrix d d ℝ) : 0 ≤ opNorm M := norm_nonneg M
/--
The stated quantitative bound `opNorm (A * B) ≤ opNorm A * opNorm B`.

Use: `«2606.16671v2».JacobiData.opNorm_operatorWord_le` uses this bound to establish the stated
quantitative bound `opNorm (J.operatorWord I H E n times) ≤ delta ^ times.card *
J.partitionWeight n times`.

Article: 2606.16671v2, Corollary 4.4 via `«2606.16671v2».Prefix.opNorm_finiteDrift_le`.

Source: mathlib, Mathlib.LinearAlgebra.Matrix.Hermitian and matrix norm theory — finite real
spectral theorem and Euclidean/Frobenius norm comparison.

Proof: The displayed proof term instantiates the cited result with exactly the parameters and
hypotheses of this assertion.
-/
theorem opNorm_mul_le (A B : Matrix d d ℝ) : opNorm (A * B) ≤ opNorm A * opNorm B :=
  Matrix.l2_opNorm_mul A B
/--
The stated quantitative bound `opNorm (A + B) ≤ opNorm A + opNorm B`.

Use: `«2606.16671v2».Nonlinear.MethodFamily.transfer_le` uses this bound to establish the
stated quantitative bound `opNorm (((family.data N).realization I).operatorTransfer N Hs) ≤
I.epsilon N * (T ℝ N).eval (1+2*delta/I.delta)`.

Article: 2606.16671v2, Corollary 5.4 via `«2606.16671v2».Nonlinear.lipschitzHessian_error_le`.

Source: mathlib, Mathlib.LinearAlgebra.Matrix.Hermitian and matrix norm theory — finite real
spectral theorem and Euclidean/Frobenius norm comparison.

Proof: The displayed proof term instantiates the cited result with exactly the parameters and
hypotheses of this assertion.
-/
theorem opNorm_add_le (A B : Matrix d d ℝ) : opNorm (A + B) ≤ opNorm A + opNorm B :=
  norm_add_le A B
/--
Exact identity `opNorm (c • A) = |c| * opNorm A`.

Use: `«2606.16671v2».JacobiData.opNorm_driftOrder_le` rewrites with this identity to establish
the stated quantitative bound `opNorm (J.driftOrder I N k H E) ≤ (2 / I.delta) ^ k / J.den I N
* delta ^ k * J.partitionBound N k`.

Article: 2606.16671v2, Corollary 4.4 via `«2606.16671v2».Prefix.opNorm_linearResponse_le`.

Source: mathlib, Mathlib.LinearAlgebra.Matrix.Hermitian and matrix norm theory — finite real
spectral theorem and Euclidean/Frobenius norm comparison.

Proof: The displayed proof term instantiates the cited result with exactly the parameters and
hypotheses of this assertion.
-/
theorem opNorm_smul (c : ℝ) (A : Matrix d d ℝ) : opNorm (c • A) = |c| * opNorm A :=
  norm_smul c A

/--
Exact identity `aeval (Matrix.diagonal v) p = Matrix.diagonal (fun i => p.eval (v i))`.

Use: `«2606.16671v2».aeval_coordinates` uses this identity to establish the identity
`(SpectralBasis.ofHermitian H hH).coordinates (aeval H p) = Matrix.diagonal (fun i => p.eval
(hH.eigenvalues i))`.

Article: 2606.16671v2, Corollary 4.4 via `«2606.16671v2».Prefix.opNorm_linearResponse_le`.

Source: mathlib, Mathlib.LinearAlgebra.Matrix.Hermitian and matrix norm theory — finite real
spectral theorem and Euclidean/Frobenius norm comparison.

Proof: Expand/rewrite the named definitions and identities appearing in the tactic block; the
remaining goal is a direct simplification or algebraic consequence.
-/
theorem aeval_diagonal (p : ℝ[X]) (v : d → ℝ) :
    aeval (Matrix.diagonal v) p = Matrix.diagonal (fun i => p.eval (v i)) := by
  have h := Polynomial.aeval_algHom_apply (Matrix.diagonalAlgHom (n := d) (α := ℝ) ℝ) v p
  simpa only [Matrix.diagonalAlgHom_apply, Polynomial.aeval_pi_apply,
    Polynomial.coe_aeval_eq_eval] using h

/--
Exact identity `opNorm (aeval H p) = ‖fun i => p.eval (hH.eigenvalues i)‖`.

Use: `«2606.16671v2».opNorm_aeval_le` rewrites with this identity to establish the stated
quantitative bound `opNorm (aeval H p) ≤ C`.

Article: 2606.16671v2, Corollary 4.4 via `«2606.16671v2».Prefix.opNorm_linearResponse_le`.

Source: mathlib, Mathlib.LinearAlgebra.Matrix.Hermitian and matrix norm theory — finite real
spectral theorem and Euclidean/Frobenius norm comparison.

Proof: Use the identities/estimates `«2606.16671v2».aeval_diagonal` with the arguments shown in
the proof.
-/
theorem opNorm_aeval_eq (p : ℝ[X]) (H : Matrix d d ℝ) (hH : H.IsHermitian) :
    opNorm (aeval H p) = ‖fun i => p.eval (hH.eigenvalues i)‖ := by
  conv_lhs => rw [hH.spectral_theorem, Polynomial.aeval_algHom_apply]
  simp only [Unitary.conjStarAlgAut_apply, Function.comp_def, RCLike.ofReal_real_eq_id,
    id_eq, aeval_diagonal, opNorm]
  rw [← Unitary.coe_star, CStarRing.norm_mul_coe_unitary,
    CStarRing.norm_coe_unitary_mul, Matrix.l2_opNorm_diagonal]

/--
Exact identity `(SpectralBasis.ofHermitian H hH).coordinates (aeval H p) = Matrix.diagonal (fun
i => p.eval (hH.eigenvalues i))`.

Use: `«2606.16671v2».JacobiData.linearResponse_blocks` uses this identity to establish exact
identity `(J.realization I).linearResponse N H E = -(2 / (I.delta * J.den I N)) • ∑ s ∈
Finset.range N, aeval H (J.spectralBlock I (s + 1) (N - (s + 1))) * E s * aeval H
(J.spectralBlock I 0 s)`.

Article: 2606.16671v2, Corollary 4.4 via `«2606.16671v2».Prefix.opNorm_linearResponse_le`.

Source: mathlib, Mathlib.LinearAlgebra.Matrix.Hermitian and matrix norm theory — finite real
spectral theorem and Euclidean/Frobenius norm comparison.

Proof: Use the identities/estimates `«2606.16671v2».aeval_diagonal` with the arguments shown in
the proof.
-/
theorem aeval_coordinates (p : ℝ[X]) (H : Matrix d d ℝ) (hH : H.IsHermitian) :
    (SpectralBasis.ofHermitian H hH).coordinates (aeval H p) =
      Matrix.diagonal (fun i => p.eval (hH.eigenvalues i)) := by
  -- Use the identities/estimates `«2606.16671v2».aeval_diagonal` with the arguments shown in
  -- the proof.
  have h := Polynomial.aeval_algHom_apply
    (Unitary.conjStarAlgAut ℝ (Matrix d d ℝ) (star hH.eigenvectorUnitary)) H p
  rw [hH.conjStarAlgAut_star_eigenvectorUnitary] at h
  simpa only [SpectralBasis.coordinates, SpectralBasis.ofHermitian,
    Unitary.conjStarAlgAut_star_apply, Function.comp_def, RCLike.ofReal_real_eq_id,
    id_eq, aeval_diagonal, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_eq_transpose_of_trivial] using h.symm

/--
Spectral calculus bound for any polynomial, in the actual Euclidean operator norm.

The stated quantitative bound `opNorm (aeval H p) ≤ C`.

Use: `«2606.16671v2».opNorm_residual_le` uses this bound to establish the stated quantitative
bound `opNorm (aeval H (I.residual N)) ≤ I.epsilon N`.

Article: 2606.16671v2, Corollary 4.4 via `«2606.16671v2».Prefix.opNorm_linearResponse_le`.

Source: mathlib, Mathlib.LinearAlgebra.Matrix.Hermitian and matrix norm theory — finite real
spectral theorem and Euclidean/Frobenius norm comparison.

Proof: Use the identities/estimates `«2606.16671v2».opNorm_aeval_eq` with the arguments shown
in the proof.
-/
theorem opNorm_aeval_le (p : ℝ[X]) (I : SpectralInterval) (H : Matrix d d ℝ)
    (hH : H.IsHermitian) (hspec : spectrum ℝ H ⊆ Set.Icc I.mu I.L)
    (C : ℝ) (hC : 0 ≤ C) (hp : ∀ x ∈ Set.Icc I.mu I.L, |p.eval x| ≤ C) :
    opNorm (aeval H p) ≤ C := by
  -- Use the identities/estimates `«2606.16671v2».opNorm_aeval_eq` with the arguments shown in
  -- the proof.
  rw [opNorm_aeval_eq p H hH]
  apply (pi_norm_le_iff_of_nonneg hC).mpr
  intro i
  exact hp _ (hspec (hH.eigenvalues_mem_spectrum_real i))

/--
The stated quantitative bound `opNorm (aeval H (I.residual N)) ≤ I.epsilon N`.

Use: `«2606.16671v2».Nonlinear.MethodFamily.transfer_le` uses this bound to establish the
stated quantitative bound `opNorm (((family.data N).realization I).operatorTransfer N Hs) ≤
I.epsilon N * (T ℝ N).eval (1+2*delta/I.delta)`.

Article: 2606.16671v2, Corollary 5.4 via `«2606.16671v2».Nonlinear.lipschitzHessian_error_le`.

Source: mathlib, Mathlib.LinearAlgebra.Matrix.Hermitian and matrix norm theory — finite real
spectral theorem and Euclidean/Frobenius norm comparison.

Proof: Use the identities/estimates `«2606.16671v2».opNorm_aeval_le`,
`«2606.16671v2».SpectralInterval.den_pos`, `«2606.16671v2».SpectralInterval.residual_abs_le`
with the arguments shown in the proof.
-/
theorem opNorm_residual_le (I : SpectralInterval) (N : ℕ) (H : Matrix d d ℝ)
    (hH : H.IsHermitian) (hspec : spectrum ℝ H ⊆ Set.Icc I.mu I.L) :
    opNorm (aeval H (I.residual N)) ≤ I.epsilon N :=
  opNorm_aeval_le _ I H hH hspec _ (div_nonneg zero_le_one (I.den_pos N).le)
    (fun _ hx => I.residual_abs_le N hx)

end
end «2606.16671v2»

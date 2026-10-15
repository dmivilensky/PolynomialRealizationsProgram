import «2606.16671v2».Jacobi.Prefix
import «2606.16671v2».Jacobi.EndpointBound

/-!
Article: 2606.16671v2, Corollary 4.4.
The attaining static shift for the prefix realization, simultaneously for all three errors.
Result: `«2606.16671v2».Prefix.static_shift_attained` supplies the stated article conclusion.
-/
namespace «2606.16671v2».Prefix
noncomputable section
open Polynomial Polynomial.Chebyshev

/--
The precise assertion is `jacobiData.EndpointMax N`.

Use: `«2606.16671v2».Prefix.opNorm_linearResponse_le` uses this assertion to establish the
stated quantitative bound `opNorm ((realization I).linearResponse N H E) ≤ 2 * (N : ℝ) ^ 2 *
I.epsilon N * delta / I.delta`.

Article: 2606.16671v2, Corollary 4.4 via `«2606.16671v2».Prefix.opNorm_linearResponse_le`.

Proof: Use the identities/estimates `«2606.16671v2».Prefix.jacobiBlock_endpoint_max` with the
arguments shown in the proof.
-/
theorem jacobi_endpointMax (N : ℕ) : jacobiData.EndpointMax N := by
  intro a n _ x hx
  have h := jacobiBlock_endpoint_max a n hx
  simp only [jacobiBlock, eval_mul, eval_C, abs_mul,
    abs_of_pos (pow_pos (by norm_num : (0 : ℝ) < 2) n)] at h
  exact (mul_le_mul_iff_right₀ (pow_pos (by norm_num : (0 : ℝ) < 2) n)).mp h

/--
The linear part of Corollary 4.4 for arbitrary, noncommuting drift.

The stated quantitative bound `opNorm ((realization I).linearResponse N H E) ≤ 2 * (N : ℝ) ^ 2
* I.epsilon N * delta / I.delta`.

Use: the ordered `Article` showcase checks this article-facing formulation directly.

Article: 2606.16671v2, Corollary 4.4.

Proof: Use the identities/estimates
`«2606.16671v2».JacobiData.opNorm_linearResponse_endpoint_le`,
`«2606.16671v2».Prefix.jacobi_admissible`, `«2606.16671v2».Prefix.jacobi_endpointMax` with the
arguments shown in the proof.
-/
theorem opNorm_linearResponse_le {d : Type*} [Fintype d] [DecidableEq d]
    (I : SpectralInterval) (N : ℕ) (H : Matrix d d ℝ) (hH : H.IsHermitian)
    (hspec : spectrum ℝ H ⊆ Set.Icc I.mu I.L) (E : ℕ → Matrix d d ℝ)
    (delta : ℝ) (hE : ∀ s < N, opNorm (E s) ≤ delta) :
    opNorm ((realization I).linearResponse N H E) ≤
      2 * (N : ℝ) ^ 2 * I.epsilon N * delta / I.delta := by
  -- Use the identities/estimates
  -- `«2606.16671v2».JacobiData.opNorm_linearResponse_endpoint_le`,
  -- `«2606.16671v2».Prefix.jacobi_admissible`, `«2606.16671v2».Prefix.jacobi_endpointMax` with
  -- the arguments shown in the proof.
  have h := jacobiData.opNorm_linearResponse_endpoint_le I (jacobi_admissible I N)
    (jacobi_endpointMax N)
    (by rw [jacobi_realization, residualPolynomial_eq]) H hH hspec E delta hE
  rwa [jacobi_realization] at h

/--
The attaining static shift for the prefix realization, simultaneously for all three errors.

Use: the ordered `Article` showcase checks this article-facing formulation directly.

Article: 2606.16671v2, Corollary 4.4.

Proof: Use the identities/estimates `«2606.16671v2».Realization.static_shift_attained`,
`«2606.16671v2».Prefix.residualPolynomial_eq` with the arguments shown in the proof.
-/
theorem static_shift_attained (I : SpectralInterval) (N : ℕ) (delta : ℝ) (hd : 0 ≤ delta) :
    opNorm ((realization I).operatorTransfer N (fun _ => scalarMatrix (I.mu - delta)) -
      aeval (scalarMatrix I.mu) (I.residual N)) =
        I.epsilon N * ((T ℝ N).eval (1 + 2 * delta / I.delta) - 1) ∧
    opNorm ((realization I).linearResponse N (scalarMatrix I.mu) (fun _ => scalarMatrix (-delta))) =
      2 * (N : ℝ) ^ 2 * I.epsilon N * delta / I.delta ∧
    opNorm ((realization I).driftRemainder N (scalarMatrix I.mu) (fun _ => scalarMatrix (-delta))) =
      I.epsilon N * ((T ℝ N).eval (1 + 2 * delta / I.delta) - 1 -
        2 * (N : ℝ) ^ 2 * delta / I.delta) :=
  (realization I).static_shift_attained I N (residualPolynomial_eq I N) delta hd

end
end «2606.16671v2».Prefix

import chebyshev1.Chebyshev.Polynomial

/-!
Article: chebyshev1, Theorem 1.4.
Endpoint Derivatives.
Use: `chebyshev1.SpectralInterval.residual_second_derivative_eval_mu` feeds
`chebyshev1.Stepsize.endpoint_square_sum` (The endpoint energy is independent of the ordering of
an exact schedule).
Proof chain: `chebyshev1.Stepsize.endpoint_square_sum` — chebyshev1, Theorem 1.4; Sharp
stepsize drift lower bound and asymptotics.
Source: NIST Digital Library of Mathematical Functions, Chapter 18 — Chebyshev endpoint derivatives.
The needed form is proved here.
-/
namespace chebyshev1.SpectralInterval
noncomputable section
open Polynomial Polynomial.Chebyshev
variable (I : SpectralInterval)

/--
Exact identity `I.eta - (2 / I.delta) * I.mu = 1`.

Use: `chebyshev1.SpectralInterval.residual_derivative_eval_mu` rewrites with this identity
to establish the identity `(I.residual N).derivative.eval I.mu = -(2 / I.delta) * I.epsilon N
* (N : ℝ) ^ 2`.

Article: chebyshev1, Corollary 4.4 via `chebyshev1.Prefix.opNorm_linearResponse_le`.

Source: NIST Digital Library of Mathematical Functions, Chapter 18 — Chebyshev endpoint
derivatives.

Proof: Use the identities/estimates `chebyshev1.SpectralInterval.z_eq`,
`chebyshev1.SpectralInterval.z_mu` with the arguments shown in the proof.
-/
private theorem affine_eval_mu :
    I.eta - (2 / I.delta) * I.mu = 1 := by rw [← I.z_eq, I.z_mu]

/--
Exact identity `(I.residual N).eval I.mu = I.epsilon N`.

Use: `chebyshev1.Realization.static_shift_lower_bounds_general` rewrites with this identity
to establish the identity stated in that declaration.

Article: chebyshev1, Corollary 4.4 via `chebyshev1.Prefix.static_shift_attained`.

Source: NIST Digital Library of Mathematical Functions, Chapter 18 — Chebyshev endpoint
derivatives.

Proof: Use the identities/estimates `chebyshev1.SpectralInterval.residual_eval`,
`chebyshev1.SpectralInterval.z_mu` with the arguments shown in the proof.
-/
theorem residual_eval_mu (N : ℕ) : (I.residual N).eval I.mu = I.epsilon N := by
  rw [I.residual_eval, I.z_mu, T_eval_one]
  rfl

/--
Exact identity `(I.residual N).derivative.eval I.mu = -(2 / I.delta) * I.epsilon N * (N : ℝ) ^
2`.

Use: `chebyshev1.JacobiData.opNorm_linearResponse_endpoint_le` rewrites with this identity
to prove the bound `opNorm ((J.realization I).linearResponse N H E) ≤ 2
* (N : ℝ) ^ 2 * I.epsilon N * delta / I.delta`.

Article: chebyshev1, Corollary 4.4 via `chebyshev1.Prefix.opNorm_linearResponse_le`.

Source: NIST Digital Library of Mathematical Functions, Chapter 18 — Chebyshev endpoint
derivatives.

Proof: Use the identities/estimates
`_private.chebyshev1.Chebyshev.EndpointDerivatives.0.chebyshev1.SpectralInterval.affine_eval_mu`
with the arguments shown in the proof.
-/
theorem residual_derivative_eval_mu (N : ℕ) :
    (I.residual N).derivative.eval I.mu = -(2 / I.delta) * I.epsilon N * (N : ℝ) ^ 2 := by
  simp [residual, derivative_comp, affine_eval_mu, derivative_T_eval_one,
    SpectralInterval.epsilon]
  ring

/--
Exact identity `(I.residual N).derivative.derivative.eval I.mu = (2 / I.delta) ^ 2 * I.epsilon
N * ((N : ℝ) ^ 2 * ((N : ℝ) ^ 2 - 1) / 3)`.

Use: `chebyshev1.Stepsize.endpoint_square_sum` rewrites with this identity to establish
exact identity `(∑ s ∈ Finset.range N, ((realization gamma).kernel N s I.mu I.mu) ^ 2) = (2 *
I.epsilon N / I.delta) ^ 2 * (((2 : ℝ) * N ^ 4 + N ^ 2) / 3)`.

Article: chebyshev1, Theorem 1.4 via `chebyshev1.Stepsize.endpoint_square_sum`.

Source: NIST Digital Library of Mathematical Functions, Chapter 18 — Chebyshev endpoint
derivatives.

Proof: Use the identities/estimates
`_private.chebyshev1.Chebyshev.EndpointDerivatives.0.chebyshev1.SpectralInterval.affine_eval_mu`
with the arguments shown in the proof.
-/
theorem residual_second_derivative_eval_mu (N : ℕ) :
    (I.residual N).derivative.derivative.eval I.mu =
      (2 / I.delta) ^ 2 * I.epsilon N * ((N : ℝ) ^ 2 * ((N : ℝ) ^ 2 - 1) / 3) := by
  -- Use the identities/estimates
  -- `_private.chebyshev1.Chebyshev.EndpointDerivatives.0.chebyshev1.SpectralInterval.affine_eval_mu`
  -- with the arguments shown in the proof.
  have hT : (T ℝ N).derivative.derivative.eval 1 =
      (N : ℝ) ^ 2 * ((N : ℝ) ^ 2 - 1) / 3 := by
    have h := iterate_derivative_T_eval_one_eq_div (𝔽 := ℝ) N 2
    simpa [Finset.prod_range_succ, Function.iterate_succ_apply'] using h
  simp [residual, derivative_comp, derivative_mul, affine_eval_mu, hT,
    SpectralInterval.epsilon]
  ring

end
end chebyshev1.SpectralInterval

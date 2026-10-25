import chebyshev1.Realization.StaticShift
import chebyshev1.Realization.Coordinates

/-!
Article: chebyshev1, Theorem 4.3.
All three lower bounds in 4.3(iv), on any Hessian containing the left endpoint.
Result: `chebyshev1.Realization.static_shift_lower_bounds_general` supplies the stated article
conclusion.
-/
namespace chebyshev1
noncomputable section
open Polynomial
open Polynomial.Chebyshev (T)
open scoped BigOperators Matrix
set_option backward.isDefEq.respectTransparency false
variable {d : Type*} [Fintype d] [DecidableEq d]

/--
The stated quantitative bound `|p.eval x| ≤ opNorm (aeval H p)`.

Use: `chebyshev1.Realization.static_shift_lower_bounds_general` uses this bound to
establish the identity stated in that declaration.

Article: chebyshev1, Theorem 4.3 via
`chebyshev1.Realization.static_shift_lower_bounds_general`.

Proof: Use the identities/estimates `chebyshev1.opNorm_aeval_eq` with the arguments shown
in the proof.
-/
theorem eval_abs_le_opNorm (p : ℝ[X]) (H : Matrix d d ℝ) (hH : H.IsHermitian)
    (x : ℝ) (hx : x ∈ spectrum ℝ H) : |p.eval x| ≤ opNorm (aeval H p) := by
  rw [hH.spectrum_real_eq_range_eigenvalues] at hx
  obtain ⟨i, rfl⟩ := hx
  rw [opNorm_aeval_eq p H hH]
  exact norm_le_pi_norm (fun i => p.eval (hH.eigenvalues i)) i

namespace Realization
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/--
Static shift differentiates the residual polynomial on every eigenspace.

Exact identity `R.linearResponse N H (fun _ => (-delta) • (1 : Matrix d d ℝ)) = (-delta) •
aeval H (R.residualPolynomial N).derivative`.

Use: `chebyshev1.Realization.static_remainder_polynomial` rewrites with this identity to
establish the identity stated in that declaration.

Article: chebyshev1, Theorem 4.3 via
`chebyshev1.Realization.static_shift_lower_bounds_general`.

Proof: Separate `i = j` from its negation; prove the goal under each of these mutually
exclusive hypotheses. Prove equality of functions by evaluating both sides at an arbitrary
argument.
-/
theorem static_linearResponse_general (R : Realization ι) (N : ℕ)
    (H : Matrix d d ℝ) (hH : H.IsHermitian) (delta : ℝ) :
    R.linearResponse N H (fun _ => (-delta) • (1 : Matrix d d ℝ)) =
      (-delta) • aeval H (R.residualPolynomial N).derivative := by
  -- Separate `i = j` from its negation; prove the goal under each of these mutually exclusive
  -- hypotheses.
  let B := SpectralBasis.ofHermitian H hH
  apply B.coordinates_injective
  have hc := R.linearResponse_coordinates B.Q H B.transpose_mul B.mul_transpose N
    (fun _ => (-delta) • (1 : Matrix d d ℝ))
  have he : (fun _ : ℕ => B.Qᵀ * ((-delta) • (1 : Matrix d d ℝ)) * B.Q) =
      (fun _ => (-delta) • (1 : Matrix d d ℝ)) := by
    funext s
    simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, B.transpose_mul]
  rw [B.diagonalize, he] at hc
  change _ = B.coordinates _ at hc
  rw [← hc]
  have hright : B.coordinates ((-delta) • aeval H (R.residualPolynomial N).derivative) =
      (-delta) • Matrix.diagonal (fun i => (R.residualPolynomial N).derivative.eval (hH.eigenvalues i)) := by
    change B.Qᵀ * _ * B.Q = _
    rw [Matrix.mul_smul, Matrix.smul_mul]
    exact congrArg (fun M : Matrix d d ℝ => (-delta) • M)
      (aeval_coordinates _ H hH)
  rw [hright]
  apply Matrix.ext
  intro i j
  rw [diagonal_linearResponse_entry]
  by_cases hij : i = j
  · subst j
    simp only [Matrix.smul_apply, Matrix.one_apply_eq, Matrix.diagonal_apply_eq, smul_eq_mul,
      mul_one]
    rw [← Finset.sum_mul, R.kernel_sum_derivative]
    dsimp [B, SpectralBasis.ofHermitian]
    ring
  · simp [Matrix.smul_apply, Matrix.one_apply_ne hij, hij]

/--
Exact identity `R.operatorTransfer N (fun _ => H-delta • (1 : Matrix d d ℝ)) = aeval H
((R.residualPolynomial N).comp (X-C delta))`.

Use: `chebyshev1.Realization.static_remainder_polynomial` rewrites with this identity to
establish the identity stated in that declaration.

Article: chebyshev1, Theorem 4.3 via
`chebyshev1.Realization.static_shift_lower_bounds_general`.

Proof: Use the identities/estimates `chebyshev1.Realization.operatorTransfer_eq_aeval` with
the arguments shown in the proof.
-/
theorem static_shift_polynomial (R : Realization ι) (N : ℕ) (H : Matrix d d ℝ) (delta : ℝ) :
    R.operatorTransfer N (fun _ => H-delta • (1 : Matrix d d ℝ)) =
      aeval H ((R.residualPolynomial N).comp (X-C delta)) := by
  rw [operatorTransfer_eq_aeval, aeval_comp]
  simp [Algebra.algebraMap_eq_smul_one]

/--
Exact identity `R.driftRemainder N H (fun _ => (-delta) • (1 : Matrix d d ℝ)) = aeval H
((R.residualPolynomial N).comp (X-C delta) - R.residualPolynomial N + C delta *
(R.residualPolynomial N).derivative)`.

Use: `chebyshev1.Realization.static_shift_lower_bounds_general` uses this identity to
establish the identity stated in that declaration.

Article: chebyshev1, Theorem 4.3 via
`chebyshev1.Realization.static_shift_lower_bounds_general`.

Proof: Use the identities/estimates
`chebyshev1.Realization.finiteDrift_polynomial_decomposition`,
`chebyshev1.Realization.static_linearResponse_general`,
`chebyshev1.Realization.static_shift_polynomial` with the arguments shown in the proof.
-/
theorem static_remainder_polynomial (R : Realization ι) (N : ℕ)
    (H : Matrix d d ℝ) (hH : H.IsHermitian) (delta : ℝ) :
    R.driftRemainder N H (fun _ => (-delta) • (1 : Matrix d d ℝ)) =
      aeval H ((R.residualPolynomial N).comp (X-C delta) - R.residualPolynomial N +
        C delta * (R.residualPolynomial N).derivative) := by
  -- Use the identities/estimates
  -- `chebyshev1.Realization.finiteDrift_polynomial_decomposition`,
  -- `chebyshev1.Realization.static_linearResponse_general`,
  -- `chebyshev1.Realization.static_shift_polynomial` with the arguments shown in the
  -- proof.
  have hd := R.finiteDrift_polynomial_decomposition N H
    (fun _ => (-delta) • (1 : Matrix d d ℝ))
  have he : (fun _ : ℕ => H+(-delta) • (1 : Matrix d d ℝ)) =
      (fun _ => H-delta • (1 : Matrix d d ℝ)) := by simp [neg_smul, sub_eq_add_neg]
  rw [he] at hd
  rw [R.static_shift_polynomial, R.static_linearResponse_general N H hH delta] at hd
  rw [map_add, map_sub, map_mul, aeval_C, Algebra.algebraMap_eq_smul_one, Matrix.smul_mul, Matrix.one_mul]
  simp only [neg_smul] at hd
  simp only [neg_smul]
  rw [eq_sub_of_add_eq' hd.symm]
  abel

/--
All three lower bounds in 4.3(iv), on any Hessian containing the left endpoint.

Use: the ordered `Article` showcase checks this article-facing formulation directly.

Article: chebyshev1, Theorem 4.3.

Proof: Use the identities/estimates `chebyshev1.SpectralInterval.z_eq`,
`chebyshev1.SpectralInterval.z_mu`, `chebyshev1.SpectralInterval.residual_eval` with
the arguments shown in the proof.
-/
theorem static_shift_lower_bounds_general (R : Realization ι) (I : SpectralInterval) (N : ℕ)
    (hfinal : R.residualPolynomial N = I.residual N) (H : Matrix d d ℝ) (hH : H.IsHermitian)
    (hmu : I.mu ∈ spectrum ℝ H) (delta : ℝ) :
    I.epsilon N*((T ℝ N).eval (1+2*delta/I.delta)-1) ≤
      opNorm (R.operatorTransfer N (fun _ => H-delta • (1 : Matrix d d ℝ)) - aeval H (I.residual N)) ∧
    2*(N:ℝ)^2*I.epsilon N*delta/I.delta ≤
      opNorm (R.linearResponse N H (fun _ => (-delta) • (1 : Matrix d d ℝ))) ∧
    I.epsilon N*((T ℝ N).eval (1+2*delta/I.delta)-1-2*(N:ℝ)^2*delta/I.delta) ≤
      opNorm (R.driftRemainder N H (fun _ => (-delta) • (1 : Matrix d d ℝ))) := by
  -- Use the identities/estimates `chebyshev1.SpectralInterval.z_eq`,
  -- `chebyshev1.SpectralInterval.z_mu`, `chebyshev1.SpectralInterval.residual_eval`
  -- with the arguments shown in the proof.
  have hz : I.z (I.mu-delta) = 1+2*delta/I.delta := by
    rw [I.z_eq, mul_sub]
    have hmu' := I.z_mu
    rw [I.z_eq] at hmu'
    rw [show I.eta-(2/I.delta*I.mu-2/I.delta*delta) =
      (I.eta-2/I.delta*I.mu)+2/I.delta*delta by ring, hmu']
    ring
  have hp : (I.residual N).eval (I.mu-delta) = I.epsilon N*(T ℝ N).eval (1+2*delta/I.delta) := by
    rw [I.residual_eval, hz]
    dsimp [SpectralInterval.epsilon]
    ring
  have bound (p : ℝ[X]) : p.eval I.mu ≤ opNorm (aeval H p) :=
    (le_abs_self _).trans (eval_abs_le_opNorm p H hH I.mu hmu)
  have ho : R.operatorTransfer N (fun _ => H-delta • (1 : Matrix d d ℝ)) - aeval H (I.residual N) =
      aeval H ((I.residual N).comp (X-C delta)-I.residual N) := by
    rw [R.static_shift_polynomial, hfinal, map_sub]
  have hl : R.linearResponse N H (fun _ => (-delta) • (1 : Matrix d d ℝ)) =
      aeval H (C (-delta)*(I.residual N).derivative) := by
    rw [R.static_linearResponse_general N H hH delta, hfinal]
    simp [Algebra.algebraMap_eq_smul_one]
  have hr := R.static_remainder_polynomial N H hH delta
  rw [hfinal] at hr
  rw [ho, hl, hr]
  refine ⟨?_, ?_, ?_⟩
  · convert bound ((I.residual N).comp (X-C delta)-I.residual N) using 1
    simp only [eval_sub, eval_comp, eval_X, eval_C, hp, I.residual_eval_mu]
    ring
  · convert bound (C (-delta)*(I.residual N).derivative) using 1
    simp only [eval_mul, eval_C, I.residual_derivative_eval_mu]
    ring
  · convert bound ((I.residual N).comp (X-C delta)-I.residual N+C delta*(I.residual N).derivative) using 1
    simp only [eval_add, eval_sub, eval_mul, eval_comp, eval_X, eval_C, hp,
      I.residual_eval_mu, I.residual_derivative_eval_mu]
    ring

end Realization
end
end chebyshev1

import «2606.16671v2».Spectral.OperatorNorm
import «2606.16671v2».Spectral.DiagonalResponse
import «2606.16671v2».Realization.Polynomial
import «2606.16671v2».Chebyshev.EndpointDerivatives
import «2606.16671v2».Chebyshev.OutsideBound
import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-!
Article: 2606.16671v2, Theorem 4.3.
All three Chebyshev drift expressions are attained on the same physical example.
Use: `«2606.16671v2».Realization.static_shift_attained` feeds
`«2606.16671v2».SineJacobi.static_shift_attained` (The three finite drift bounds are attained by the
same static scalar example).
-/
namespace «2606.16671v2»
noncomputable section
open Polynomial Polynomial.Chebyshev
open scoped BigOperators Matrix.Norms.Operator
set_option backward.isDefEq.respectTransparency false

/--
A one-dimensional physical Hessian; memory remains arbitrary.

Use: `«2606.16671v2».Realization.kernel_sum_derivative` rewrites with this definition to
establish exact identity `∑ s ∈ Finset.range N, R.kernel N s lam lam = (R.residualPolynomial
N).derivative.eval lam`.

Article: 2606.16671v2, Corollary 4.4 via `«2606.16671v2».Prefix.static_shift_attained`.
-/
def scalarMatrix (c : ℝ) : Matrix (Fin 1) (Fin 1) ℝ := Matrix.diagonal (fun _ => c)

/--
Exact identity `opNorm (scalarMatrix c) = |c|`.

Use: `«2606.16671v2».Realization.static_shift_admissible` rewrites with this identity to
establish exact identity `(scalarMatrix I.mu).IsHermitian ∧ spectrum ℝ (scalarMatrix I.mu) ⊆
Set.Icc I.mu I.L ∧ I.mu ∈ spectrum ℝ (scalarMatrix I.mu) ∧ opNorm (scalarMatrix (-delta)) =
delta`.

Article: 2606.16671v2, Corollary 4.4 via `«2606.16671v2».Prefix.static_shift_attained`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem opNorm_scalarMatrix (c : ℝ) : opNorm (scalarMatrix c) = |c| := by
  unfold opNorm scalarMatrix
  rw [Matrix.l2_opNorm_diagonal]
  simp

namespace Realization
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/--
The sum of all insertion kernels is the derivative under a static spectral shift.

Exact identity `∑ s ∈ Finset.range N, R.kernel N s lam lam = (R.residualPolynomial
N).derivative.eval lam`.

Use: `«2606.16671v2».Realization.static_linearResponse` rewrites with this identity to
establish exact identity `R.linearResponse N (scalarMatrix lam) (fun _ => scalarMatrix
(-delta)) = scalarMatrix (-delta * (R.residualPolynomial N).derivative.eval lam)`.

Article: 2606.16671v2, Corollary 4.4 via `«2606.16671v2».Prefix.opNorm_linearResponse_le`.

Proof: Check each member of the finite index type; no case is omitted.
-/
theorem kernel_sum_derivative (R : Realization ι) (N : ℕ) (lam : ℝ) :
    ∑ s ∈ Finset.range N, R.kernel N s lam lam = (R.residualPolynomial N).derivative.eval lam := by
  -- Check each member of the finite index type; no case is omitted.
  let L : Matrix (Fin 1) (Fin 1) ℝ →ₗ[ℝ] ℝ :=
    { toFun := fun M => M 0 0, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  have hd := L.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt 0
    (R.hasDerivAt_operatorTransfer N (scalarMatrix lam) (fun _ => 1))
  have hm (t : ℝ) : scalarMatrix lam + t • (1 : Matrix (Fin 1) (Fin 1) ℝ) =
      scalarMatrix (lam + t) := by ext i j; fin_cases i; fin_cases j; simp [scalarMatrix]
  have hp : HasDerivAt (fun t : ℝ => (R.residualPolynomial N).eval (lam + t))
      (∑ s ∈ Finset.range N, R.kernel N s lam lam) 0 := by
    convert! hd using 1
    · ext t
      change (R.residualPolynomial N).eval (lam + t) =
        R.operatorTransfer N (fun _ => scalarMatrix lam + t • 1) 0 0
      simp only [hm, operatorTransfer_eq_aeval]
      simp [scalarMatrix, aeval_diagonal]
    · simp [L, scalarMatrix, diagonal_linearResponse_entry]
  have hq := ((R.residualPolynomial N).hasDerivAt (lam + 0)).comp 0
    ((hasDerivAt_id (0 : ℝ)).const_add lam)
  simpa using hp.unique hq

/--
Exact identity `R.linearResponse N (scalarMatrix lam) (fun _ => scalarMatrix (-delta)) =
scalarMatrix (-delta * (R.residualPolynomial N).derivative.eval lam)`.

Use: `«2606.16671v2».Realization.static_shift_values` rewrites with this identity to establish
the identity stated in that declaration.

Article: 2606.16671v2, Corollary 4.4 via `«2606.16671v2».Prefix.static_shift_attained`.

Proof: Check each member of the finite index type; no case is omitted.
-/
theorem static_linearResponse (R : Realization ι) (N : ℕ) (lam delta : ℝ) :
    R.linearResponse N (scalarMatrix lam) (fun _ => scalarMatrix (-delta)) =
      scalarMatrix (-delta * (R.residualPolynomial N).derivative.eval lam) := by
  ext i j
  fin_cases i; fin_cases j
  simp only [scalarMatrix, diagonal_linearResponse_entry, Matrix.diagonal_apply_eq]
  rw [← Finset.sum_mul, R.kernel_sum_derivative]
  ring

/--
The finite and first-order values in the attaining example of Theorem 4.3(iv).

Use: `«2606.16671v2».Realization.static_shift_attained` uses this identity to establish the
identity stated in that declaration.

Article: 2606.16671v2, Corollary 4.4 via `«2606.16671v2».Prefix.static_shift_attained`.

Proof: Prove equality of functions by evaluating both sides at an arbitrary argument. Check
each member of the finite index type; no case is omitted.
-/
theorem static_shift_values (R : Realization ι) (I : SpectralInterval) (N : ℕ)
    (hfinal : R.residualPolynomial N = I.residual N) (delta : ℝ) :
    R.operatorTransfer N (fun _ => scalarMatrix (I.mu - delta)) -
        aeval (scalarMatrix I.mu) (I.residual N) =
      scalarMatrix (I.epsilon N * ((T ℝ N).eval (1 + 2 * delta / I.delta) - 1)) ∧
    R.linearResponse N (scalarMatrix I.mu) (fun _ => scalarMatrix (-delta)) =
      scalarMatrix (2 * (N : ℝ) ^ 2 * I.epsilon N * delta / I.delta) ∧
    R.driftRemainder N (scalarMatrix I.mu) (fun _ => scalarMatrix (-delta)) =
      scalarMatrix (I.epsilon N *
        ((T ℝ N).eval (1 + 2 * delta / I.delta) - 1 - 2 * (N : ℝ) ^ 2 * delta / I.delta)) := by
  -- Prove equality of functions by evaluating both sides at an arbitrary argument.
  have hz : I.z (I.mu - delta) = 1 + 2 * delta / I.delta := by
    rw [I.z_eq, mul_sub]
    have hz0 := I.z_mu
    rw [I.z_eq] at hz0
    rw [show I.eta - (2 / I.delta * I.mu - 2 / I.delta * delta) =
      (I.eta - 2 / I.delta * I.mu) + 2 / I.delta * delta by ring, hz0]
    ring
  have hout : R.operatorTransfer N (fun _ => scalarMatrix (I.mu - delta)) -
      aeval (scalarMatrix I.mu) (I.residual N) =
        scalarMatrix (I.epsilon N * ((T ℝ N).eval (1 + 2 * delta / I.delta) - 1)) := by
    rw [operatorTransfer_eq_aeval, hfinal]
    ext i j
    fin_cases i; fin_cases j
    simp only [scalarMatrix, aeval_diagonal, Matrix.sub_apply, Matrix.diagonal_apply_eq,
      I.residual_eval_mu, I.residual_eval, hz, SpectralInterval.epsilon]
    ring
  have hlin : R.linearResponse N (scalarMatrix I.mu) (fun _ => scalarMatrix (-delta)) =
      scalarMatrix (2 * (N : ℝ) ^ 2 * I.epsilon N * delta / I.delta) := by
    rw [static_linearResponse, hfinal, I.residual_derivative_eval_mu]
    congr 1
    ring
  refine ⟨hout, hlin, ?_⟩
  have hd := R.finiteDrift_polynomial_decomposition N (scalarMatrix I.mu)
    (fun _ => scalarMatrix (-delta))
  have hm : (fun _ : ℕ => scalarMatrix I.mu + scalarMatrix (-delta)) =
      (fun _ => scalarMatrix (I.mu - delta)) := by
    funext s; ext i j; fin_cases i; fin_cases j; simp [scalarMatrix]; ring
  rw [hm, hfinal, hlin] at hd
  have he : R.driftRemainder N (scalarMatrix I.mu) (fun _ => scalarMatrix (-delta)) =
      (R.operatorTransfer N (fun _ => scalarMatrix (I.mu - delta)) -
        aeval (scalarMatrix I.mu) (I.residual N)) -
        scalarMatrix (2 * (N : ℝ) ^ 2 * I.epsilon N * delta / I.delta) := by rw [hd]; abel
  rw [he, hout]
  ext i j
  fin_cases i; fin_cases j
  simp only [Matrix.sub_apply, scalarMatrix, Matrix.diagonal_apply_eq]
  ring

/--
Theorem 4.3(iv), explicit one-dimensional witnesses for all three lower bounds.

Use: a standalone supporting identity for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: 2606.16671v2, Theorem 4.3.

Proof: Use the identities/estimates `«2606.16671v2».Realization.static_shift_values`,
`«2606.16671v2».opNorm_scalarMatrix` with the arguments shown in the proof.
-/
theorem static_shift_lower_bounds (R : Realization ι) (I : SpectralInterval) (N : ℕ)
    (hfinal : R.residualPolynomial N = I.residual N) (delta : ℝ) :
    I.epsilon N * ((T ℝ N).eval (1 + 2 * delta / I.delta) - 1) ≤
      opNorm (R.operatorTransfer N (fun _ => scalarMatrix (I.mu - delta)) -
        aeval (scalarMatrix I.mu) (I.residual N)) ∧
    2 * (N : ℝ) ^ 2 * I.epsilon N * delta / I.delta ≤
      opNorm (R.linearResponse N (scalarMatrix I.mu) (fun _ => scalarMatrix (-delta))) ∧
    I.epsilon N * ((T ℝ N).eval (1 + 2 * delta / I.delta) - 1 -
        2 * (N : ℝ) ^ 2 * delta / I.delta) ≤
      opNorm (R.driftRemainder N (scalarMatrix I.mu) (fun _ => scalarMatrix (-delta))) := by
  -- Use the identities/estimates `«2606.16671v2».Realization.static_shift_values`,
  -- `«2606.16671v2».opNorm_scalarMatrix` with the arguments shown in the proof.
  obtain ⟨ho, hl, hr⟩ := R.static_shift_values I N hfinal delta
  rw [ho, hl, hr, opNorm_scalarMatrix, opNorm_scalarMatrix, opNorm_scalarMatrix]
  exact ⟨le_abs_self _, le_abs_self _, le_abs_self _⟩

/--
All three Chebyshev drift expressions are attained on the same physical example.

Use: `«2606.16671v2».Prefix.static_shift_attained` uses this identity to establish the identity
stated in that declaration.

Article: 2606.16671v2, Corollary 4.4 via `«2606.16671v2».Prefix.static_shift_attained`.

Proof: Use the identities/estimates `«2606.16671v2».Realization.static_shift_values`,
`«2606.16671v2».SpectralInterval.den_pos`, `«2606.16671v2».SpectralInterval.delta_pos` with the
arguments shown in the proof.
-/
theorem static_shift_attained (R : Realization ι) (I : SpectralInterval) (N : ℕ)
    (hfinal : R.residualPolynomial N = I.residual N) (delta : ℝ) (hd : 0 ≤ delta) :
    opNorm (R.operatorTransfer N (fun _ => scalarMatrix (I.mu - delta)) -
      aeval (scalarMatrix I.mu) (I.residual N)) =
        I.epsilon N * ((T ℝ N).eval (1 + 2 * delta / I.delta) - 1) ∧
    opNorm (R.linearResponse N (scalarMatrix I.mu) (fun _ => scalarMatrix (-delta))) =
      2 * (N : ℝ) ^ 2 * I.epsilon N * delta / I.delta ∧
    opNorm (R.driftRemainder N (scalarMatrix I.mu) (fun _ => scalarMatrix (-delta))) =
      I.epsilon N * ((T ℝ N).eval (1 + 2 * delta / I.delta) - 1 -
        2 * (N : ℝ) ^ 2 * delta / I.delta) := by
  -- Use the identities/estimates `«2606.16671v2».Realization.static_shift_values`,
  -- `«2606.16671v2».SpectralInterval.den_pos`, `«2606.16671v2».SpectralInterval.delta_pos`
  -- with the arguments shown in the proof.
  obtain ⟨ho, hl, hr⟩ := R.static_shift_values I N hfinal delta
  have he : 0 ≤ I.epsilon N := div_nonneg zero_le_one (I.den_pos N).le
  have hu : 0 ≤ 2 * delta / I.delta := div_nonneg (by positivity) I.delta_pos.le
  have hT := one_le_eval_T_real N (show 1 ≤ 1 + 2 * delta / I.delta by linarith)
  have ht := chebyshev_tangent_lower N (2 * delta / I.delta) hu
  rw [ho, hl, hr, opNorm_scalarMatrix, opNorm_scalarMatrix, opNorm_scalarMatrix]
  refine ⟨abs_of_nonneg (mul_nonneg he (by linarith)), abs_of_nonneg ?_, abs_of_nonneg ?_⟩
  · exact div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) he) hd)
      I.delta_pos.le
  · apply mul_nonneg he
    have heq : (N : ℝ) ^ 2 * (2 * delta / I.delta) =
        2 * (N : ℝ) ^ 2 * delta / I.delta := by ring
    rw [heq] at ht
    linarith

/--
Exact identity `(scalarMatrix I.mu).IsHermitian ∧ spectrum ℝ (scalarMatrix I.mu) ⊆ Set.Icc I.mu
I.L ∧ I.mu ∈ spectrum ℝ (scalarMatrix I.mu) ∧ opNorm (scalarMatrix (-delta)) = delta`.

Use: a standalone supporting identity for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: 2606.16671v2, Theorem 4.3.

Proof: Use the identities/estimates `«2606.16671v2».opNorm_scalarMatrix` with the arguments
shown in the proof.
-/
theorem static_shift_admissible (I : SpectralInterval) (delta : ℝ) (hd : 0 ≤ delta) :
    (scalarMatrix I.mu).IsHermitian ∧ spectrum ℝ (scalarMatrix I.mu) ⊆ Set.Icc I.mu I.L ∧
      I.mu ∈ spectrum ℝ (scalarMatrix I.mu) ∧ opNorm (scalarMatrix (-delta)) = delta := by
  -- Use the identities/estimates `«2606.16671v2».opNorm_scalarMatrix` with the arguments shown
  -- in the proof.
  refine ⟨by simp [scalarMatrix, Matrix.IsHermitian], ?_, ?_, ?_⟩
  · rw [scalarMatrix, spectrum_diagonal]
    rintro x ⟨i, rfl⟩
    exact ⟨le_rfl, I.mu_lt_L.le⟩
  · rw [scalarMatrix, spectrum_diagonal]
    exact ⟨0, rfl⟩
  · rw [opNorm_scalarMatrix, abs_neg, abs_of_nonneg hd]

end Realization
end
end «2606.16671v2»

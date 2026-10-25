import chebyshev1.Prefix.Basic

/-!
Article: chebyshev1, Theorem 2.1.
The independently defined algorithm and the generic realization have the same output.
Result: `chebyshev1.Prefix.quadraticError_eq_transfer` supplies the stated article conclusion.
-/
namespace chebyshev1.Prefix

noncomputable section
open Polynomial Polynomial.Chebyshev
open scoped Matrix BigOperators

variable (I : SpectralInterval)

/--
The precise assertion is `let M`.

Use: `chebyshev1.Prefix.residual_recurrence` rewrites with this assertion to establish
exact identity `I.residual (n + 2) = Polynomial.C (1 + beta I (n + 1)) * (1 - Polynomial.C (2 /
(I.L + I.mu)) * Polynomial.X) * I.residual (n + 1) - Polynomial.C (beta I (n + 1)) * I.residual
n`.

Article: chebyshev1, Theorem 2.2 via `chebyshev1.Prefix.kernel_succ`.

Proof: Induct on `n`; the recursive step uses the previous-stage assertion. Clear the
denominators using the available nonzero hypotheses, then verify the remaining algebraic
identity.
-/
theorem prefix_column (n : ℕ) (lam : ℝ) :
    let M := orderedProduct (fun s => (realization I).scalarStep s lam) (n + 1)
    M 0 0 = (T ℝ (n + 1)).eval (I.z lam) / I.den (n + 1) ∧
    M 1 0 = (T ℝ n).eval (I.z lam) / I.den n := by
  -- Induct on `n`; the recursive step uses the previous-stage assertion.
  induction n with
  | zero => simp [orderedProduct, scalarStep_zero]
  | succ n ih =>
    dsimp only at ih ⊢
    rw [orderedProduct_succ, scalarStep_succ]
    constructor
    · simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, ih.1, ih.2]
      have hc : (T ℝ ((n : ℤ) + 2)).eval (I.z lam) =
          2 * I.z lam * (T ℝ ((n : ℤ) + 1)).eval (I.z lam) -
            (T ℝ n).eval (I.z lam) := by simp [T_add_two]
      push_cast
      field_simp [I.den_ne n, I.den_ne (n + 1), I.den_ne (n + 2)]
      convert! hc.symm using 1
    · simpa [Matrix.mul_apply, Fin.sum_univ_two] using ih.1

/--
Theorem 2.1 in scalar form, for every prefix, including time zero.

Exact identity `(realization I).scalarTransfer n lam = (I.residual n).eval lam`.

Use: `chebyshev1.Prefix.residualPolynomial_eq` rewrites with this identity to establish
exact identity `(realization I).residualPolynomial n = I.residual n`.

Article: chebyshev1, Theorem 2.1 via `chebyshev1.Prefix.residualPolynomial_eq`.

Proof: Use the identities/estimates `chebyshev1.Prefix.scalarContract`,
`chebyshev1.SpectralInterval.residual_eval`, `chebyshev1.Prefix.prefix_column` with the
arguments shown in the proof.
-/
theorem scalar_exact (n : ℕ) (lam : ℝ) :
    (realization I).scalarTransfer n lam = (I.residual n).eval lam := by
  rw [Realization.scalarTransfer, scalarContract, I.residual_eval]
  cases n with
  | zero => simp [orderedProduct]
  | succ n => exact (prefix_column I n lam).1

/--
Exactness is a polynomial identity, not only agreement on the spectrum.

Exact identity `(realization I).residualPolynomial n = I.residual n`.

Use: `chebyshev1.Prefix.operator_exact` rewrites with this identity to establish exact
identity `(realization I).operatorTransfer n (fun _ => H) = Polynomial.aeval H (I.residual n)`.

Article: chebyshev1, Theorem 2.1.

Proof: Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem residualPolynomial_eq (n : ℕ) :
    (realization I).residualPolynomial n = I.residual n := by
  apply Polynomial.funext
  intro lam
  rw [Realization.residualPolynomial_eval, scalar_exact]

/--
The operator assertion of Theorem 2.1; no spectral theorem is needed.

Exact identity `(realization I).operatorTransfer n (fun _ => H) = Polynomial.aeval H
(I.residual n)`.

Use: `chebyshev1.Prefix.quadraticError_eq_transfer` rewrites with this identity to
establish exact identity `quadraticError I H e0 n = ((realization I).operatorTransfer n (fun _
=> H)).mulVec e0`.

Article: chebyshev1, Theorem 2.1.

Proof: Use the identities/estimates `chebyshev1.Realization.operatorTransfer_eq_aeval`,
`chebyshev1.Prefix.residualPolynomial_eq` with the arguments shown in the proof.
-/
theorem operator_exact {d : Type*} [Fintype d] [DecidableEq d]
    (n : ℕ) (H : Matrix d d ℝ) :
    (realization I).operatorTransfer n (fun _ => H) = Polynomial.aeval H (I.residual n) := by rw [Realization.operatorTransfer_eq_aeval, residualPolynomial_eq]

/--
Exact identity `I.residual 0 = 1`.

Use: `chebyshev1.Prefix.quadraticError_exact` uses this identity to establish exact
identity `quadraticError I H e0 n = (Polynomial.aeval H (I.residual n)).mulVec e0`.

Article: chebyshev1, Theorem 2.1 via `chebyshev1.Prefix.quadraticError_exact`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
@[simp] theorem residual_zero : I.residual 0 = 1 := by simp [SpectralInterval.residual]

/--
Exact identity `I.residual 1 = 1 - Polynomial.C (2 / (I.L + I.mu)) * Polynomial.X`.

Use: `chebyshev1.Prefix.quadraticError_exact` rewrites with this identity to establish
exact identity `quadraticError I H e0 n = (Polynomial.aeval H (I.residual n)).mulVec e0`.

Article: chebyshev1, Theorem 2.1 via `chebyshev1.Prefix.quadraticError_exact`.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity. Prove equality of functions by evaluating both sides at an arbitrary
argument.
-/
theorem residual_one : I.residual 1 =
    1 - Polynomial.C (2 / (I.L + I.mu)) * Polynomial.X := by
  -- Clear the denominators using the available nonzero hypotheses, then verify the remaining
  -- algebraic identity.
  apply Polynomial.funext
  intro lam
  rw [I.residual_eval]
  simp only [Nat.cast_one, T_one, Polynomial.eval_X, I.den_one, Polynomial.eval_sub,
    Polynomial.eval_one, Polynomial.eval_mul, Polynomial.eval_C]
  dsimp [SpectralInterval.z, SpectralInterval.eta]
  field_simp [ne_of_gt I.delta_pos, ne_of_gt I.sum_pos]

/--
Exact identity `I.residual (n + 2) = Polynomial.C (1 + beta I (n + 1)) * (1 - Polynomial.C (2 /
(I.L + I.mu)) * Polynomial.X) * I.residual (n + 1) - Polynomial.C (beta I (n + 1)) * I.residual
n`.

Use: `chebyshev1.Prefix.quadraticError_exact` rewrites with this identity to establish
exact identity `quadraticError I H e0 n = (Polynomial.aeval H (I.residual n)).mulVec e0`.

Article: chebyshev1, Theorem 2.1 via `chebyshev1.Prefix.quadraticError_exact`.

Proof: Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem residual_recurrence (n : ℕ) :
    I.residual (n + 2) =
      Polynomial.C (1 + beta I (n + 1)) *
        (1 - Polynomial.C (2 / (I.L + I.mu)) * Polynomial.X) * I.residual (n + 1) -
      Polynomial.C (beta I (n + 1)) * I.residual n := by
  -- Prove equality of functions by evaluating both sides at an arbitrary argument.
  apply Polynomial.funext
  intro lam
  simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_one, Polynomial.eval_X]
  rw [← scalar_exact, Realization.scalarTransfer, scalarContract,
    orderedProduct_succ, algorithmStep_succ]
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  rw [(prefix_column I n lam).1, (prefix_column I n lam).2,
    I.residual_eval, I.residual_eval]
  push_cast
  ring

/--
The actual error recurrence for a quadratic with Hessian `H`.

Use: `chebyshev1.Prefix.quadraticError_exact` rewrites with this definition to establish
exact identity `quadraticError I H e0 n = (Polynomial.aeval H (I.residual n)).mulVec e0`.

Article: chebyshev1, Theorem 2.1 via `chebyshev1.Prefix.quadraticError_exact`.
-/
def quadraticError {d : Type*} [Fintype d] [DecidableEq d]
    (H : Matrix d d ℝ) (e0 : d → ℝ) : ℕ → d → ℝ
  | 0 => e0
  | 1 => e0 - (2 / (I.L + I.mu)) • H.mulVec e0
  | n + 2 => (1 + beta I (n + 1)) •
      (quadraticError H e0 (n + 1) - (2 / (I.L + I.mu)) •
        H.mulVec (quadraticError H e0 (n + 1))) -
      beta I (n + 1) • quadraticError H e0 n

/--
The error recurrence in the uncollected gradient/momentum form of (2.1).

Exact identity `quadraticError I H e0 (n + 2) = quadraticError I H e0 (n + 1) + beta I (n + 1)
• (quadraticError I H e0 (n + 1) - quadraticError I H e0 n) - gamma I (n + 1) • H.mulVec
(quadraticError I H e0 (n + 1))`.

Use: a standalone supporting identity for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: chebyshev1, Theorem 2.1.

Proof: Use the identities/estimates `chebyshev1.Prefix.gamma_succ` with the arguments shown
in the proof.
-/
theorem quadraticError_update {d : Type*} [Fintype d] [DecidableEq d]
    (H : Matrix d d ℝ) (e0 : d → ℝ) (n : ℕ) :
    quadraticError I H e0 (n + 2) =
      quadraticError I H e0 (n + 1) + beta I (n + 1) •
        (quadraticError I H e0 (n + 1) - quadraticError I H e0 n) -
      gamma I (n + 1) • H.mulVec (quadraticError I H e0 (n + 1)) := by
  -- Use the identities/estimates `chebyshev1.Prefix.gamma_succ` with the arguments shown
  -- in the proof.
  rw [quadraticError, gamma_succ]
  module

/--
Theorem 2.1 for the iterates of the stated algorithm.

Exact identity `quadraticError I H e0 n = (Polynomial.aeval H (I.residual n)).mulVec e0`.

Use: `chebyshev1.Prefix.quadraticError_eq_transfer` rewrites with this identity to
establish exact identity `quadraticError I H e0 n = ((realization I).operatorTransfer n (fun _
=> H)).mulVec e0`.

Article: chebyshev1, Theorem 2.1.

Proof: Induct on `n`; the recursive step uses the previous-stage assertion.
-/
theorem quadraticError_exact {d : Type*} [Fintype d] [DecidableEq d]
    (H : Matrix d d ℝ) (e0 : d → ℝ) (n : ℕ) :
    quadraticError I H e0 n = (Polynomial.aeval H (I.residual n)).mulVec e0 := by
  -- Induct on `n`; the recursive step uses the previous-stage assertion.
  induction n using Nat.twoStepInduction with
  | zero => simp [quadraticError]
  | one =>
    rw [quadraticError, residual_one]
    simp [map_sub, map_mul, Polynomial.aeval_C, Polynomial.aeval_X,
      Algebra.algebraMap_eq_smul_one, Matrix.sub_mulVec, Matrix.smul_mulVec]
  | more n ih0 ih1 =>
    rw [quadraticError, ih0, ih1, residual_recurrence]
    simp only [map_sub, map_mul, Polynomial.aeval_C, Polynomial.aeval_X, map_one,
      Algebra.algebraMap_eq_smul_one, sub_mul, smul_mul_assoc, one_mul,
      Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.mulVec_mulVec, smul_sub]

/--
The independently defined algorithm and the generic realization have the same output.

Exact identity `quadraticError I H e0 n = ((realization I).operatorTransfer n (fun _ =>
H)).mulVec e0`.

Use: the ordered `Article` showcase checks this article-facing formulation directly.

Article: chebyshev1, Theorem 2.1.

Proof: Use the identities/estimates `chebyshev1.Prefix.operator_exact`,
`chebyshev1.Prefix.quadraticError_exact` with the arguments shown in the proof.
-/
theorem quadraticError_eq_transfer {d : Type*} [Fintype d] [DecidableEq d]
    (H : Matrix d d ℝ) (e0 : d → ℝ) (n : ℕ) :
    quadraticError I H e0 n = ((realization I).operatorTransfer n (fun _ => H)).mulVec e0 := by rw [operator_exact, quadraticError_exact]

end
end chebyshev1.Prefix

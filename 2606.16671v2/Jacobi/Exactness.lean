import «2606.16671v2».Jacobi.Basic

/-!
Article: 2606.16671v2, Theorem 4.1.
A nonzero scale of the terminal Chebyshev polynomial suffices.
Use: `«2606.16671v2».JacobiData.terminal_exact` feeds
`«2606.16671v2».SineJacobi.quadraticError_exact` (Terminal exactness for the independently defined
iterates of Algorithm 2).
-/
namespace «2606.16671v2».JacobiData
noncomputable section
open Polynomial Polynomial.Chebyshev
open scoped Matrix

variable (J : JacobiData) (I : SpectralInterval)

/--
The precise assertion is `J.den I n ≠ 0`.

Use: `«2606.16671v2».JacobiData.prefix_column` uses this assertion to establish the precise
assertion is `let M`.

Article: 2606.16671v2, Theorem E.1 via `«2606.16671v2».SineJacobi.kernel_abs_le_endpoint`.

Proof: The displayed proof term instantiates the cited result with exactly the parameters and
hypotheses of this assertion.
-/
theorem den_ne {N n : ℕ} (h : J.Admissible I N) (hn : n ≤ N) :
    J.den I n ≠ 0 := ne_of_gt (h n hn)

/--
Exact identity `(J.realization I).scalarStep (n + 1) lam = !![(I.z lam - J.b (n + 1)) * J.den I
(n + 1) / J.den I (n + 2), -(J.aSq (n + 1) * J.den I n / J.den I (n + 2)); 1, 0]`.

Use: `«2606.16671v2».JacobiData.prefix_column` rewrites with this identity to establish the
precise assertion is `let M`.

Article: 2606.16671v2, Theorem E.1 via `«2606.16671v2».SineJacobi.kernel_abs_le_endpoint`.

Proof: Check each member of the finite index type; no case is omitted.
-/
theorem scalarStep_succ (n : ℕ) (lam : ℝ) :
    (J.realization I).scalarStep (n + 1) lam =
      !![(I.z lam - J.b (n + 1)) * J.den I (n + 1) / J.den I (n + 2),
        -(J.aSq (n + 1) * J.den I n / J.den I (n + 2)); 1, 0] := by
  rw [realization, TwoTerm.scalarStep_succ]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [method, I.z_eq]
  ring

/--
The precise assertion is `let M`.

Use: `«2606.16671v2».JacobiData.scalar_exact` uses this assertion to establish the identity
`(J.realization I).scalarTransfer n lam = (J.residual I n).eval lam`.

Article: 2606.16671v2, Theorem E.1 via `«2606.16671v2».SineJacobi.kernel_abs_le_endpoint`.

Proof: Induct on `n`; the recursive step uses the previous-stage assertion. Clear the
denominators using the available nonzero hypotheses, then verify the remaining algebraic
identity.
-/
theorem prefix_column {N : ℕ} (h : J.Admissible I N) (n : ℕ)
    (hn : n + 1 ≤ N) (lam : ℝ) :
    let M := orderedProduct (fun s => (J.realization I).scalarStep s lam) (n + 1)
    M 0 0 = (J.leading (n + 1)).eval (I.z lam) / J.den I (n + 1) ∧
    M 1 0 = (J.leading n).eval (I.z lam) / J.den I n := by
  -- Induct on `n`; the recursive step uses the previous-stage assertion.
  induction n with
  | zero =>
    simp only [Nat.zero_add, realization, orderedProduct, TwoTerm.scalarStep_zero, Matrix.mul_one]
    constructor
    · simp only [method, den_zero, mul_one, leading_one, eval_sub, eval_X, eval_C,
        Matrix.of_apply, Matrix.cons_val_zero]
      rw [I.z_eq, den_one]
      field_simp [J.den_ne I h hn, show I.eta - J.b 0 ≠ 0 by simpa using J.den_ne I h hn]
      ring
    · simp [leading_zero]
  | succ n ih =>
    have hi := ih (by omega)
    dsimp only at hi ⊢
    rw [orderedProduct_succ, scalarStep_succ]
    constructor
    · simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, hi.1, hi.2]
      have hc : (J.leading (n + 2)).eval (I.z lam) =
          (I.z lam - J.b (n + 1)) * (J.leading (n + 1)).eval (I.z lam) -
            J.aSq (n + 1) * (J.leading n).eval (I.z lam) := by
        simp [leading, block]
      field_simp [J.den_ne I h (show n ≤ N by omega),
        J.den_ne I h (show n + 1 ≤ N by omega), J.den_ne I h hn]
      rw [hc]
      ring
    · simpa [Matrix.mul_apply, Fin.sum_univ_two] using hi.1

/--
The scalar form of Theorem 4.1, including the initial prefix.

Exact identity `(J.realization I).scalarTransfer n lam = (J.residual I n).eval lam`.

Use: `«2606.16671v2».JacobiData.residualPolynomial_eq` rewrites with this identity to establish
exact identity `(J.realization I).residualPolynomial n = J.residual I n`.

Article: 2606.16671v2, Theorem E.1 via `«2606.16671v2».SineJacobi.kernel_abs_le_endpoint`.

Proof: Use the identities/estimates `«2606.16671v2».TwoTerm.scalarContract`,
`«2606.16671v2».JacobiData.residual_eval`, `«2606.16671v2».JacobiData.prefix_column` with the
arguments shown in the proof.
-/
theorem scalar_exact {N : ℕ} (h : J.Admissible I N) (n : ℕ) (hn : n ≤ N) (lam : ℝ) :
    (J.realization I).scalarTransfer n lam = (J.residual I n).eval lam := by
  rw [Realization.scalarTransfer, realization, TwoTerm.scalarContract, residual_eval]
  cases n with
  | zero => simp [orderedProduct]
  | succ n => exact (J.prefix_column I h n hn lam).1

/--
Exact identity `(J.realization I).residualPolynomial n = J.residual I n`.

Use: `«2606.16671v2».JacobiData.operator_exact` rewrites with this identity to establish exact
identity `(J.realization I).operatorTransfer n (fun _ => H) = aeval H (J.residual I n)`.

Article: 2606.16671v2, Corollary 5.3 via `«2606.16671v2».SineJacobi.opNorm_linearResponse_le`.

Proof: Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem residualPolynomial_eq {N : ℕ} (h : J.Admissible I N) (n : ℕ) (hn : n ≤ N) :
    (J.realization I).residualPolynomial n = J.residual I n := by
  apply Polynomial.funext
  intro lam
  rw [Realization.residualPolynomial_eval, J.scalar_exact I h n hn]

/--
Exact identity `(J.realization I).operatorTransfer n (fun _ => H) = aeval H (J.residual I n)`.

Use: `«2606.16671v2».JacobiData.quadraticError_exact` rewrites with this identity to establish
exact identity `(J.method I).quadraticError H e0 n = (aeval H (J.residual I n)).mulVec e0`.

Article: 2606.16671v2, Corollary 4.4 via `«2606.16671v2».Prefix.opNorm_finiteDrift_le`.

Proof: Use the identities/estimates `«2606.16671v2».Realization.operatorTransfer_eq_aeval`,
`«2606.16671v2».JacobiData.residualPolynomial_eq` with the arguments shown in the proof.
-/
theorem operator_exact {d : Type*} [Fintype d] [DecidableEq d]
    {N : ℕ} (h : J.Admissible I N) (n : ℕ) (hn : n ≤ N) (H : Matrix d d ℝ) :
    (J.realization I).operatorTransfer n (fun _ => H) = aeval H (J.residual I n) := by rw [Realization.operatorTransfer_eq_aeval, J.residualPolynomial_eq I h n hn]

/--
Theorem 4.1 for the independently defined error recurrence of the algorithm.

Exact identity `(J.method I).quadraticError H e0 n = (aeval H (J.residual I n)).mulVec e0`.

Use: `«2606.16671v2».JacobiData.terminal_exact` rewrites with this identity to establish exact
identity `(J.method I).quadraticError H e0 N = (aeval H (I.residual N)).mulVec e0`.

Article: 2606.16671v2, Theorem 4.1.

Proof: Use the identities/estimates `«2606.16671v2».TwoTerm.quadraticError_eq_transfer`,
`«2606.16671v2».JacobiData.operator_exact` with the arguments shown in the proof.
-/
theorem quadraticError_exact {d : Type*} [Fintype d] [DecidableEq d]
    {N : ℕ} (h : J.Admissible I N) (n : ℕ) (hn : n ≤ N)
    (H : Matrix d d ℝ) (e0 : d → ℝ) :
    (J.method I).quadraticError H e0 n = (aeval H (J.residual I n)).mulVec e0 := by rw [TwoTerm.quadraticError_eq_transfer, ← realization, J.operator_exact I h n hn]

/--
A nonzero scale of the terminal Chebyshev polynomial suffices.

Exact identity `J.residual I N = I.residual N`.

Use: `«2606.16671v2».JacobiData.terminal_exact` rewrites with this identity to establish exact
identity `(J.method I).quadraticError H e0 N = (aeval H (I.residual N)).mulVec e0`.

Article: 2606.16671v2, Corollary 4.4 via `«2606.16671v2».Prefix.opNorm_finiteDrift_le`.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity. Prove equality of functions by evaluating both sides at an arbitrary
argument.
-/
theorem terminal_residual {N : ℕ} {c : ℝ} (hc : c ≠ 0)
    (hterminal : J.leading N = C c * T ℝ N) :
    J.residual I N = I.residual N := by
  -- Clear the denominators using the available nonzero hypotheses, then verify the remaining
  -- algebraic identity.
  apply Polynomial.funext
  intro lam
  rw [J.residual_eval, I.residual_eval]
  simp only [den, hterminal, eval_mul, eval_C, SpectralInterval.den]
  field_simp

/--
Exact identity `(J.method I).quadraticError H e0 N = (aeval H (I.residual N)).mulVec e0`.

Use: `«2606.16671v2».SineJacobi.quadraticError_exact` uses this identity to establish exact
identity `((data N).method I).quadraticError H e0 N = (aeval H (I.residual N)).mulVec e0`.

Article: 2606.16671v2, Theorem 4.1.

Proof: Use the identities/estimates `«2606.16671v2».JacobiData.quadraticError_exact`,
`«2606.16671v2».JacobiData.terminal_residual` with the arguments shown in the proof.
-/
theorem terminal_exact {d : Type*} [Fintype d] [DecidableEq d]
    {N : ℕ} (h : J.Admissible I N) {c : ℝ} (hc : c ≠ 0)
    (hterminal : J.leading N = C c * T ℝ N) (H : Matrix d d ℝ) (e0 : d → ℝ) :
    (J.method I).quadraticError H e0 N = (aeval H (I.residual N)).mulVec e0 := by rw [J.quadraticError_exact I h N le_rfl, J.terminal_residual I hc hterminal]

end
end «2606.16671v2».JacobiData

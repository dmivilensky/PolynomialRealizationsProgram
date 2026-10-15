import «2606.16671v2».TwoTerm.Basic

/-!
Article: 2606.16671v2, Theorem 4.1.
Quadratic.
Use: `«2606.16671v2».TwoTerm.quadraticError_eq_transfer` feeds
`«2606.16671v2».JacobiData.quadraticError_exact` (Theorem 4.1 for the independently defined error
recurrence of the algorithm).
Proof chain: `«2606.16671v2».JacobiData.quadraticError_exact` — 2606.16671v2, Theorem 4.1; Jacobi
recurrence, fixed point and terminal exactness.
-/
namespace «2606.16671v2».TwoTerm
noncomputable section
open Polynomial
open scoped Polynomial
variable (S : TwoTerm)

/--
Exact identity `S.realization.residualPolynomial 0 = 1`.

Use: `«2606.16671v2».TwoTerm.quadraticError_eq_transfer` rewrites with this identity to
establish exact identity `S.quadraticError H e0 n = (S.realization.operatorTransfer n (fun _ =>
H)).mulVec e0`.

Article: 2606.16671v2, Theorem 4.1 via `«2606.16671v2».JacobiData.quadraticError_exact`.

Proof: Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem residual_zero : S.realization.residualPolynomial 0 = 1 := by
  apply Polynomial.funext
  intro x
  simp [Realization.residualPolynomial_eval, Realization.scalarTransfer, orderedProduct]

/--
Exact identity `S.realization.residualPolynomial 1 = 1 - C (S.gamma 0) * X`.

Use: `«2606.16671v2».TwoTerm.quadraticError_eq_transfer` rewrites with this identity to
establish exact identity `S.quadraticError H e0 n = (S.realization.operatorTransfer n (fun _ =>
H)).mulVec e0`.

Article: 2606.16671v2, Theorem 4.1 via `«2606.16671v2».JacobiData.quadraticError_exact`.

Proof: Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem residual_one : S.realization.residualPolynomial 1 = 1 - C (S.gamma 0) * X := by
  apply Polynomial.funext
  intro x
  simp [Realization.residualPolynomial_eval, transfer_one]

/--
Exact identity `S.realization.residualPolynomial (n + 2) = (C (S.a (n + 1)) - C (S.gamma (n +
1)) * X) * S.realization.residualPolynomial (n + 1) + C (S.b (n + 1)) *
S.realization.residualPolynomial n`.

Use: `«2606.16671v2».TwoTerm.quadraticError_eq_transfer` rewrites with this identity to
establish exact identity `S.quadraticError H e0 n = (S.realization.operatorTransfer n (fun _ =>
H)).mulVec e0`.

Article: 2606.16671v2, Theorem 4.1 via `«2606.16671v2».JacobiData.quadraticError_exact`.

Proof: Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem residual_recurrence (n : ℕ) :
    S.realization.residualPolynomial (n + 2) =
      (C (S.a (n + 1)) - C (S.gamma (n + 1)) * X) * S.realization.residualPolynomial (n + 1) +
      C (S.b (n + 1)) * S.realization.residualPolynomial n := by
  apply Polynomial.funext
  intro x
  simp only [eval_add, eval_mul, eval_sub, eval_C, eval_X, Realization.residualPolynomial_eval]
  exact transfer_recurrence S n x

/--
Defines `quadraticError` by pattern matching with result type `ℕ → d → ℝ`. The displayed
branches determine the recursive cases and their returned values.

Use: `«2606.16671v2».TwoTerm.quadraticError_eq_transfer` rewrites with this definition to
establish exact identity `S.quadraticError H e0 n = (S.realization.operatorTransfer n (fun _ =>
H)).mulVec e0`.

Article: 2606.16671v2, Theorem 4.1 via `«2606.16671v2».JacobiData.quadraticError_exact`.
-/
def quadraticError {d : Type*} [Fintype d] [DecidableEq d]
    (H : Matrix d d ℝ) (e0 : d → ℝ) : ℕ → d → ℝ
  | 0 => e0
  | 1 => e0 - S.gamma 0 • H.mulVec e0
  | n + 2 => S.a (n + 1) • quadraticError H e0 (n + 1) +
      S.b (n + 1) • quadraticError H e0 n -
      S.gamma (n + 1) • H.mulVec (quadraticError H e0 (n + 1))

/--
Exact identity `S.quadraticError H e0 n = (S.realization.operatorTransfer n (fun _ =>
H)).mulVec e0`.

Use: `«2606.16671v2».JacobiData.quadraticError_exact` rewrites with this identity to establish
exact identity `(J.method I).quadraticError H e0 n = (aeval H (J.residual I n)).mulVec e0`.

Article: 2606.16671v2, Theorem 4.1 via `«2606.16671v2».JacobiData.quadraticError_exact`.

Proof: Induct on `n`; the recursive step uses the previous-stage assertion.
-/
theorem quadraticError_eq_transfer {d : Type*} [Fintype d] [DecidableEq d]
    (H : Matrix d d ℝ) (e0 : d → ℝ) (n : ℕ) :
    S.quadraticError H e0 n = (S.realization.operatorTransfer n (fun _ => H)).mulVec e0 := by
  -- Induct on `n`; the recursive step uses the previous-stage assertion.
  rw [Realization.operatorTransfer_eq_aeval]
  induction n using Nat.twoStepInduction with
  | zero => simp [quadraticError, residual_zero]
  | one =>
    rw [quadraticError, residual_one]
    simp [map_sub, map_mul, Polynomial.aeval_C, Polynomial.aeval_X,
      Algebra.algebraMap_eq_smul_one, Matrix.sub_mulVec, Matrix.smul_mulVec]
  | more n ih0 ih1 =>
    rw [quadraticError, ih0, ih1, residual_recurrence]
    simp only [map_add, map_sub, map_mul, Polynomial.aeval_C, Polynomial.aeval_X,
      Algebra.algebraMap_eq_smul_one, Matrix.sub_mul, smul_mul_assoc, one_mul,
      Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.mulVec_mulVec]
    abel

end
end «2606.16671v2».TwoTerm

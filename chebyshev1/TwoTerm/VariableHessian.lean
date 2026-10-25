import chebyshev1.TwoTerm.Operator

/-!
Article: chebyshev1, Corollary 5.4.
Only the queried Hessians are needed for a finite trajectory.
Use: `chebyshev1.TwoTerm.nonlinearError_eq_transfer_upto` feeds
`chebyshev1.Nonlinear.lipschitzHessian_error_le` (Corollary 5.4 in coordinates centered at the
stationary point).
Proof chain: `chebyshev1.Nonlinear.lipschitzHessian_error_le` — chebyshev1, Corollary 5.4;
Lipschitz-Hessian error bound for both methods.
-/
namespace chebyshev1.TwoTerm
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Matrix
variable (S : TwoTerm) {d : Type*} [Fintype d] [DecidableEq d]

/--
The actual two-term error recurrence with a different Hessian at each query.

Use: `chebyshev1.TwoTerm.nonlinearError_eq_transfer` uses this definition to establish
exact identity `S.nonlinearError g e0 n = (S.realization.operatorTransfer n H).mulVec e0`.

Article: chebyshev1, Corollary 5.4 via `chebyshev1.Nonlinear.lipschitzHessian_error_le`.
-/
def variableError (H : ℕ → Matrix d d ℝ) (e0 : d → ℝ) : ℕ → d → ℝ
  | 0 => e0
  | 1 => e0 - S.gamma 0 • (H 0).mulVec e0
  | n + 2 => S.a (n+1) • variableError H e0 (n+1) +
      S.b (n+1) • variableError H e0 n -
      S.gamma (n+1) • (H (n+1)).mulVec (variableError H e0 (n+1))

/--
Exact identity `orderedProduct (fun s => S.memoryStep s (H s)) (n+1) 1 0 = orderedProduct (fun
s => S.memoryStep s (H s)) n 0 0`.

Use: `chebyshev1.TwoTerm.memoryProduct_recurrence` rewrites with this identity to establish
the identity stated in that declaration.

Article: chebyshev1, Corollary 5.4 via `chebyshev1.Nonlinear.lipschitzHessian_error_le`.

Proof: Separate `n = 0` from its negation; prove the goal under each of these mutually
exclusive hypotheses.
-/
theorem memoryProduct_previous (H : ℕ → Matrix d d ℝ) (n : ℕ) :
    orderedProduct (fun s => S.memoryStep s (H s)) (n+1) 1 0 =
      orderedProduct (fun s => S.memoryStep s (H s)) n 0 0 := by
  -- Separate `n = 0` from its negation; prove the goal under each of these mutually exclusive
  -- hypotheses.
  rw [orderedProduct_succ, Matrix.mul_apply, Fin.sum_univ_two]
  have h10 : S.memoryStep n (H n) 1 0 = 1 := by
    by_cases hn : n = 0 <;> simp [memoryStep, hn]
  have h11 : S.memoryStep n (H n) 1 1 = 0 := by
    by_cases hn : n = 0 <;> simp [memoryStep, hn]
  rw [h10, h11, one_mul, zero_mul, add_zero]

/--
Exact identity `orderedProduct (fun s => S.memoryStep s (H s)) (n+2) 0 0 = (S.a (n+1) • 1 -
S.gamma (n+1) • H (n+1)) * orderedProduct (fun s => S.memoryStep s (H s)) (n+1) 0 0 + (S.b
(n+1) • 1) * orderedProduct (fun s => S.memoryStep s (H s)) n 0 0`.

Use: `chebyshev1.TwoTerm.variableError_eq_transfer` rewrites with this identity to
establish exact identity `S.variableError H e0 n = (S.realization.operatorTransfer n H).mulVec
e0`.

Article: chebyshev1, Corollary 5.4 via `chebyshev1.Nonlinear.lipschitzHessian_error_le`.

Proof: Use the identities/estimates `chebyshev1.orderedProduct_succ`,
`chebyshev1.TwoTerm.memoryProduct_previous` with the arguments shown in the proof.
-/
theorem memoryProduct_recurrence (H : ℕ → Matrix d d ℝ) (n : ℕ) :
    orderedProduct (fun s => S.memoryStep s (H s)) (n+2) 0 0 =
      (S.a (n+1) • 1 - S.gamma (n+1) • H (n+1)) *
        orderedProduct (fun s => S.memoryStep s (H s)) (n+1) 0 0 +
      (S.b (n+1) • 1) * orderedProduct (fun s => S.memoryStep s (H s)) n 0 0 := by
  rw [show n+2 = (n+1)+1 by omega, orderedProduct_succ, Matrix.mul_apply,
    Fin.sum_univ_two, S.memoryProduct_previous]
  congr 2

/--
Exact identity `S.variableError H e0 n = (S.realization.operatorTransfer n H).mulVec e0`.

Use: `chebyshev1.TwoTerm.nonlinearError_eq_transfer` rewrites with this identity to
establish exact identity `S.nonlinearError g e0 n = (S.realization.operatorTransfer n H).mulVec
e0`.

Article: chebyshev1, Corollary 5.4 via `chebyshev1.Nonlinear.lipschitzHessian_error_le`.

Proof: Induct on `n`; the recursive step uses the previous-stage assertion.
-/
theorem variableError_eq_transfer (H : ℕ → Matrix d d ℝ) (e0 : d → ℝ) (n : ℕ) :
    S.variableError H e0 n = (S.realization.operatorTransfer n H).mulVec e0 := by
  -- Induct on `n`; the recursive step uses the previous-stage assertion.
  simp only [operatorTransfer_eq_memory]
  induction n using Nat.twoStepInduction with
  | zero => simp [variableError]
  | one =>
    simp [variableError, orderedProduct_succ, memoryStep,
      Matrix.sub_mulVec, Matrix.smul_mulVec]
  | more n ih0 ih1 =>
    rw [variableError, ih0, ih1, S.memoryProduct_recurrence]
    simp only [Matrix.add_mulVec, Matrix.sub_mul, smul_mul_assoc, one_mul,
      Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.mulVec_mulVec]
    abel

/--
A nonlinear gradient oracle, written in error coordinates about a stationary point.

Use: `chebyshev1.TwoTerm.nonlinearError_eq_transfer` rewrites with this definition to
establish exact identity `S.nonlinearError g e0 n = (S.realization.operatorTransfer n H).mulVec
e0`.

Article: chebyshev1, Corollary 5.4 via `chebyshev1.Nonlinear.lipschitzHessian_error_le`.
-/
def nonlinearError (g : (d → ℝ) → d → ℝ) (e0 : d → ℝ) : ℕ → d → ℝ
  | 0 => e0
  | 1 => e0 - S.gamma 0 • g e0
  | n + 2 => S.a (n+1) • nonlinearError g e0 (n+1) +
      S.b (n+1) • nonlinearError g e0 n - S.gamma (n+1) • g (nonlinearError g e0 (n+1))

/--
Averaged Hessians linearize the entire nonlinear trajectory, including its memory.

Exact identity `S.nonlinearError g e0 n = (S.realization.operatorTransfer n H).mulVec e0`.

Use: a standalone supporting identity for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: chebyshev1, Corollary 5.4.

Proof: Induct on `n`; the recursive step uses the previous-stage assertion.
-/
theorem nonlinearError_eq_transfer (g : (d → ℝ) → d → ℝ) (e0 : d → ℝ)
    (H : ℕ → Matrix d d ℝ)
    (hg : ∀ s, g (S.nonlinearError g e0 s) = (H s).mulVec (S.nonlinearError g e0 s))
    (n : ℕ) :
    S.nonlinearError g e0 n = (S.realization.operatorTransfer n H).mulVec e0 := by
  -- Induct on `n`; the recursive step uses the previous-stage assertion.
  have he : ∀ n, S.nonlinearError g e0 n = S.variableError H e0 n := by
    intro n
    induction n using Nat.twoStepInduction with
    | zero => rfl
    | one => simpa only [nonlinearError, variableError] using
        congrArg (fun v => e0 - S.gamma 0 • v) (hg 0)
    | more n ih0 ih1 =>
      rw [nonlinearError, hg (n+1), ih0, ih1]
      rfl
  rw [he, S.variableError_eq_transfer]

/--
Only the queried Hessians are needed for a finite trajectory.

Exact identity `S.nonlinearError g e0 n = (S.realization.operatorTransfer n H).mulVec e0`.

Use: `chebyshev1.Nonlinear.lipschitzHessian_error_le` uses this identity to establish the
stated quantitative bound `‖errorTrajectory family I N g e0 N‖ ≤ I.epsilon N * (T ℝ N).eval
(1+rho*R/I.delta) * ‖e0‖`.

Article: chebyshev1, Corollary 5.4 via `chebyshev1.Nonlinear.lipschitzHessian_error_le`.

Proof: Induct on `n`; the recursive step uses the previous-stage assertion.
-/
theorem nonlinearError_eq_transfer_upto (g : (d → ℝ) → d → ℝ) (e0 : d → ℝ)
    (H : ℕ → Matrix d d ℝ) (N : ℕ)
    (hg : ∀ s < N, g (S.nonlinearError g e0 s) = (H s).mulVec (S.nonlinearError g e0 s))
    (n : ℕ) (hn : n ≤ N) :
    S.nonlinearError g e0 n = (S.realization.operatorTransfer n H).mulVec e0 := by
  -- Induct on `n`; the recursive step uses the previous-stage assertion.
  have he : ∀ n, n ≤ N → S.nonlinearError g e0 n = S.variableError H e0 n := by
    intro n
    induction n using Nat.twoStepInduction with
    | zero => intro _; rfl
    | one =>
      intro hn
      simpa only [nonlinearError, variableError] using
        congrArg (fun v => e0 - S.gamma 0 • v) (hg 0 (by omega))
    | more n ih0 ih1 =>
      intro hn
      rw [nonlinearError, hg (n+1) (by omega), ih0 (by omega), ih1 (by omega)]
      rfl
  rw [he n hn, S.variableError_eq_transfer]

end
end chebyshev1.TwoTerm

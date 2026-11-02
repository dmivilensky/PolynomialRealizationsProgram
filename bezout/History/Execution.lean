import bezout.History.Bezout
import Mathlib.Algebra.Polynomial.AlgebraMap

/-!
Article: bezout, Equations (3)--(5) and Theorem 2.1.
Use: arbitrary-dimensional physical executions, additive errors including
history-dependent errors, and nominal query/terminal polynomial semantics.
Proof: explicit causal execution and cancellation with the adjoint polynomial
resolvent. No spectral or probabilistic assumptions enter this algebraic layer.
-/

namespace bezout.History

open Polynomial
open scoped BigOperators Polynomial Matrix
noncomputable section
variable {N : ℕ} {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- A physical centered execution, retaining the actual queries and actual
oracle answers. Article: bezout, Equation (3). Use: the exact response theorem. -/
structure Execution (h : bezout.History N) (H : E →ₗ[ℝ] E)
    (initial : E) (noise : Fin N → E) where
  query : Fin N → E
  answer : Fin N → E
  query_eq : ∀ s, query s = initial - ∑ j, h.a s j • answer j
  answer_eq : ∀ s, answer s = H (query s) + noise s

/-- Actual answer recursion uses strictly earlier answers only.
Article: bezout, Equation (3). Use: existence of every noisy history execution. -/
def answers (h : bezout.History N) (H : E →ₗ[ℝ] E)
    (initial : E) (noise : Fin N → E) (s : Fin N) : E :=
  H (initial - ∑ j : Fin N,
    if _hj : j < s then h.a s j • answers h H initial noise j else 0) + noise s
termination_by s.val

/-- The answer recursion satisfies the unfiltered physical query equation.
Article: bezout, Equation (3). Use: the canonical execution. -/
theorem answers_eq (h : bezout.History N) (H : E →ₗ[ℝ] E)
    (initial : E) (noise : Fin N → E) (s : Fin N) :
    h.answers H initial noise s =
      H (initial - ∑ j, h.a s j • h.answers H initial noise j) + noise s := by
  rw [answers]
  congr 2
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : j < s
  · simp [hj]
  · simp [hj, h.triangular s j (le_of_not_gt hj)]

/-- Every noise stream has a canonical physical execution.
Article: bezout, Theorem 2.1. Use: attaining oracle-error constructions. -/
def run (h : bezout.History N) (H : E →ₗ[ℝ] E)
    (initial : E) (noise : Fin N → E) : h.Execution H initial noise where
  query s := initial - ∑ j, h.a s j • h.answers H initial noise j
  answer := h.answers H initial noise
  query_eq _ := rfl
  answer_eq s := h.answers_eq H initial noise s

/-- Causality makes physical execution unique for a given error stream.
Article: bezout, Theorem 2.1. Use: equivalence with low-memory realizations. -/
theorem execution_unique (h : bezout.History N) (H : E →ₗ[ℝ] E)
    (initial : E) (noise : Fin N → E)
    (u v : h.Execution H initial noise) : u = v := by
  have ha : u.answer = v.answer := by
    funext s
    induction s using (measure (fun s : Fin N => s.val)).wf.induction with
    | h s ih =>
      rw [u.answer_eq, v.answer_eq, u.query_eq, v.query_eq]
      congr 2
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      by_cases hj : j < s
      · rw [ih j hj]
      · simp [h.triangular s j (le_of_not_gt hj)]
  have hq : u.query = v.query := by
    funext s
    rw [u.query_eq, v.query_eq, ha]
  cases u
  cases v
  simp_all

/-- The physical terminal error selected by the prescribed output weights.
Article: bezout, Equation (3). Use: exact noisy terminal response. -/
def Execution.output {h : bezout.History N} {H : E →ₗ[ℝ] E}
    {initial : E} {noise : Fin N → E} (u : h.Execution H initial noise) : E :=
  initial - ∑ s, h.b s • u.answer s

/-- Nominal polynomial queries obey the same vector recurrence as the oracle.
Article: bezout, Theorem 2.1. Use: identify actual noiseless query states. -/
theorem query_action_recurrence (h : bezout.History N) (H : E →ₗ[ℝ] E)
    (initial : E) (s : Fin N) :
    (aeval H (h.query s)) initial = initial - ∑ j : Fin N,
      if j < s then h.a s j • H ((aeval H (h.query j)) initial) else 0 := by
  rw [h.query_recurrence]
  simp [Module.End.mul_apply, map_sum]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : j < s <;> simp [hj, Module.End.mul_apply]

/-- The polynomial query describes the actual noiseless physical query.
Article: bezout, Theorem 2.1. Use: the query factor in Hessian first variation. -/
theorem nominal_query (h : bezout.History N) (H : E →ₗ[ℝ] E)
    (initial : E) (u : h.Execution H initial (fun _ => 0)) (s : Fin N) :
    u.query s = (aeval H (h.query s)) initial := by
  induction s using (measure (fun s : Fin N => s.val)).wf.induction with
  | h s ih =>
    rw [u.query_eq, h.query_action_recurrence]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : j < s
    · simp [hj, u.answer_eq, ih j hj]
    · simp [hj, h.triangular s j (le_of_not_gt hj)]

/-- The adjoint polynomial row identity acts on arbitrary physical vectors.
Article: bezout, Appendix A. Use: cancellation of actual oracle answers. -/
theorem response_action (h : bezout.History N) (H : E →ₗ[ℝ] E)
    (j : Fin N) (v : E) :
    (aeval H (h.response j)) v +
      ∑ s, h.a s j • (aeval H (h.response s)) (H v) = -h.b j • v := by
  have hp := congrFun h.response_pencil j
  rw [pencil, Matrix.vecMul_add, Matrix.vecMul_one] at hp
  change h.response j + ∑ s, h.response s * h.coefficient s j = _ at hp
  have hv := congrArg (fun p : ℝ[X] => (aeval H p) v) hp
  simpa [coefficient, Module.End.mul_apply] using hv

/-- The terminal action is the identity plus the response to a common gradient.
Article: bezout, Appendix A. Use: exact physical additive response. -/
theorem terminal_action (h : bezout.History N) (H : E →ₗ[ℝ] E)
    (initial : E) :
    (aeval H h.terminal) initial =
      initial + ∑ s, (aeval H (h.response s)) (H initial) := by
  have hp : h.terminal = 1 + ∑ s, h.response s * X := by
    rw [h.terminal_eq_one_add_X_sum_response, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro s _
    ring
  have hv := congrArg (fun p : ℝ[X] => (aeval H p) initial) hp
  simpa [Module.End.mul_apply] using hv

/-- Exact terminal response to the errors in the actual physical oracle calls.
The error stream may have been selected from earlier answers: the theorem is
algebraic and imposes no temporal independence condition.
Article: bezout, Equation (4). Use: deterministic, stochastic and local gains. -/
theorem physical_response (h : bezout.History N) (H : E →ₗ[ℝ] E)
    (initial : E) (noise : Fin N → E) (u : h.Execution H initial noise) :
    u.output = (aeval H h.terminal) initial +
      ∑ s, (aeval H (h.response s)) (noise s) := by
  have hw (s : Fin N) : noise s = u.answer s - H (u.query s) := by
    rw [u.answer_eq]
    abel
  have hn : (∑ s, (aeval H (h.response s)) (noise s)) =
      (∑ s, (aeval H (h.response s)) (u.answer s)) -
      (∑ s, (aeval H (h.response s)) (H initial)) +
      ∑ s, ∑ j, h.a s j • (aeval H (h.response s)) (H (u.answer j)) := by
    simp_rw [hw, u.query_eq, map_sub, map_sum, map_smul]
    simp_rw [Finset.sum_sub_distrib]
    abel
  have hr : (∑ j, ((aeval H (h.response j)) (u.answer j) +
      ∑ s, h.a s j • (aeval H (h.response s)) (H (u.answer j)))) =
      - ∑ j, h.b j • u.answer j := by
    simp_rw [h.response_action, neg_smul, Finset.sum_neg_distrib]
  rw [h.terminal_action, hn, Finset.sum_comm]
  unfold Execution.output
  rw [Finset.sum_add_distrib] at hr
  rw [sub_eq_add_neg]
  rw [← hr]
  abel

/-- The noiseless physical terminal is exactly its residual polynomial.
Article: bezout, Theorem 2.1. Use: the Chebyshev-exact history class. -/
theorem nominal_output (h : bezout.History N) (H : E →ₗ[ℝ] E)
    (initial : E) (u : h.Execution H initial (fun _ => 0)) :
    u.output = (aeval H h.terminal) initial := by
  simpa using h.physical_response H initial (fun _ => 0) u

end
end bezout.History

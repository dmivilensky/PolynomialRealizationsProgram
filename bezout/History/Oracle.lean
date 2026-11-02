import bezout.History.Execution

/-!
Article: bezout, Equation (3) and Algorithms 1--2.
Use: canonical causal histories accept arbitrary time-dependent oracles;
linear Hessian perturbations, relative errors and low-memory realizations
are specializations of the same physical query/answer semantics.
Proof: well-founded recursion uses only strictly preceding physical answers.
-/

namespace bezout.History
noncomputable section
open scoped BigOperators
variable {N : ℕ} {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- Actual answers of a causal history for an arbitrary time-dependent oracle.
Use: variable Hessians and arbitrary-oracle-stream algorithm correspondence. -/
def oracleAnswers (h : bezout.History N) (initial : E)
    (oracle : Fin N → E → E) (s : Fin N) : E :=
  oracle s (initial - ∑ j : Fin N,
    if _hj : j < s then h.a s j • h.oracleAnswers initial oracle j else 0)
termination_by s.val

/-- Physical query reconstructed from answers already returned by the oracle. -/
def oracleQuery (h : bezout.History N) (initial : E)
    (oracle : Fin N → E → E) (s : Fin N) : E :=
  initial - ∑ j, h.a s j • h.oracleAnswers initial oracle j

/-- Physical output selected from the complete stream of actual oracle answers. -/
def oracleOutput (h : bezout.History N) (initial : E)
    (oracle : Fin N → E → E) : E :=
  initial - ∑ j, h.b j • h.oracleAnswers initial oracle j

/-- The unrestricted oracle recursion satisfies the exact physical call equation. -/
theorem oracleAnswers_eq (h : bezout.History N) (initial : E)
    (oracle : Fin N → E → E) (s : Fin N) :
    h.oracleAnswers initial oracle s = oracle s (h.oracleQuery initial oracle s) := by
  rw [oracleAnswers]
  congr 1
  unfold oracleQuery
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : j < s
  · simp [hj]
  · simp [hj, h.triangular s j (le_of_not_gt hj)]

/-- Any physical answer stream satisfying the causal oracle equations is canonical. -/
theorem oracleAnswers_unique (h : bezout.History N) (initial : E)
    (oracle : Fin N → E → E) (answers : Fin N → E)
    (ha : ∀ s, answers s = oracle s (initial - ∑ j, h.a s j • answers j)) :
    answers = h.oracleAnswers initial oracle := by
  funext s
  induction s using (measure (fun s : Fin N => s.val)).wf.induction with
  | h s ih =>
    rw [ha, h.oracleAnswers_eq]
    congr 1
    unfold oracleQuery
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : j < s
    · rw [ih j hj]
    · simp [h.triangular s j (le_of_not_gt hj)]

/-- Linear noisy oracles instantiate the already defined physical execution. -/
def oracleExecution (h : bezout.History N) (H : E →ₗ[ℝ] E)
    (initial : E) (noise : Fin N → E) : h.Execution H initial noise where
  query := h.oracleQuery initial (fun s y => H y + noise s)
  answer := h.oracleAnswers initial (fun s y => H y + noise s)
  query_eq _ := rfl
  answer_eq s := h.oracleAnswers_eq initial _ s

/-- The general-oracle and fixed-Hessian execution APIs produce exactly the same answers. -/
theorem oracleAnswers_linear (h : bezout.History N) (H : E →ₗ[ℝ] E)
    (initial : E) (noise : Fin N → E) :
    h.oracleAnswers initial (fun s y => H y + noise s) = h.answers H initial noise := by
  have he := h.execution_unique H initial noise (h.oracleExecution H initial noise)
    (h.run H initial noise)
  exact congrArg Execution.answer he

/-- The general-oracle and fixed-Hessian execution APIs have exactly the same output. -/
theorem oracleOutput_linear (h : bezout.History N) (H : E →ₗ[ℝ] E)
    (initial : E) (noise : Fin N → E) :
    h.oracleOutput initial (fun s y => H y + noise s) = (h.run H initial noise).output := by
  simp only [oracleOutput, h.oracleAnswers_linear, Execution.output, run]

end
end bezout.History

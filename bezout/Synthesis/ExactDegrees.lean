import bezout.History.Degrees
import bezout.Synthesis.History

/-!
Article: bezout, Theorem 2.1, exact degrees forced by a degree-N terminal.
Use: establishes that every terminal-exact physical history supplies a graded
query basis, so the constructive converse applies to the unrestricted class.
Proof: the highest query coefficient propagates only through the immediately
preceding call. The degree-N terminal forces the entire maximal causal path.
-/

namespace bezout.History
noncomputable section
open Polynomial
open scoped BigOperators
variable {N : ℕ}

/-- The highest coefficient of a query has only one maximal causal predecessor.
Use: propagates the nonvanishing terminal leading coefficient backwards. -/
theorem query_succ_coeff (h : bezout.History N) (k : ℕ) (hk : k + 1 < N) :
    (h.query ⟨k + 1, hk⟩).coeff (k + 1) =
      -h.a ⟨k + 1, hk⟩ ⟨k, by omega⟩ * (h.query ⟨k, by omega⟩).coeff k := by
  rw [h.query_recurrence]
  simp only [coeff_sub, coeff_one, Nat.succ_ne_zero, ite_false, zero_sub,
    coeff_X_mul, finsetSum_coeff]
  rw [neg_mul]
  apply congrArg Neg.neg
  calc
    _ = ∑ j : Fin N, if j < (⟨k + 1, hk⟩ : Fin N) then
        h.a ⟨k + 1, hk⟩ j * (h.query j).coeff k else 0 := by
      apply Finset.sum_congr rfl
      intro j _
      split_ifs <;> simp [coeff_C_mul]
    _ = _ := by
      rw [Finset.sum_eq_single (⟨k, by omega⟩ : Fin N)]
      · simp
      · intro j _ hj
        by_cases hjs : j < (⟨k + 1, hk⟩ : Fin N)
        · have hjk : j.val < k := by
            have hne : j.val ≠ k := by exact fun heq => hj (Fin.ext heq)
            change j.val < k + 1 at hjs
            omega
          have hz : (h.query j).coeff k = 0 := coeff_eq_zero_of_natDegree_lt
            ((h.query_natDegree_le j).trans_lt hjk)
          simp [hjs, hz]
        · simp [hjs]
      · simp

/-- The degree-N terminal leading coefficient comes only from the final query.
Use: starts the maximal-path nonvanishing induction. -/
theorem terminal_top_coeff (h : bezout.History (N + 1)) :
    h.terminal.coeff (N + 1) =
      -h.b (Fin.last N) * (h.query (Fin.last N)).coeff N := by
  rw [terminal]
  simp only [coeff_sub, coeff_one, Nat.succ_ne_zero, ite_false, zero_sub,
    coeff_X_mul, finsetSum_coeff, coeff_C_mul]
  rw [neg_mul]
  apply congrArg Neg.neg
  rw [Finset.sum_eq_single (Fin.last N)]
  · intro j _ hj
    have hjN : j.val < N := by
      have hne : j.val ≠ N := fun heq => hj (Fin.ext heq)
      have := j.isLt
      omega
    rw [coeff_eq_zero_of_natDegree_lt ((h.query_natDegree_le j).trans_lt hjN), mul_zero]
  · simp

/-- Full terminal degree forces the final physical output weight to be nonzero.
Use: initializes the backwards induction for exact physical-response degrees. -/
theorem last_weight_ne_zero (h : bezout.History (N + 1))
    (hdeg : h.terminal.natDegree = N + 1) : h.b (Fin.last N) ≠ 0 := by
  have ht : h.terminal ≠ 0 := by
    intro hz
    have := h.terminal_eval_zero
    rw [hz] at this
    simp at this
  have hc : h.terminal.coeff (N + 1) ≠ 0 := by
    have hc0 : h.terminal.coeff h.terminal.natDegree ≠ 0 := by
      rw [coeff_natDegree]
      exact leadingCoeff_ne_zero.mpr ht
    simpa only [hdeg] using hc0
  rw [h.terminal_top_coeff] at hc
  exact neg_ne_zero.mp (mul_ne_zero_iff.mp hc).1

/-- Every maximal query coefficient is nonzero when the terminal has full degree.
Use: proves the exact grading of every unrestricted terminal-exact history. -/
theorem query_top_coeff_ne_zero (h : bezout.History (N + 1))
    (hdeg : h.terminal.natDegree = N + 1) (s : Fin (N + 1)) :
    (h.query s).coeff s.val ≠ 0 := by
  have ht : h.terminal ≠ 0 := by
    intro hz
    have := h.terminal_eval_zero
    rw [hz] at this
    simp at this
  have hc : h.terminal.coeff (N + 1) ≠ 0 := by
    have hc0 : h.terminal.coeff h.terminal.natDegree ≠ 0 := by
      rw [coeff_natDegree]
      exact leadingCoeff_ne_zero.mpr ht
    simpa only [hdeg] using hc0
  rw [h.terminal_top_coeff] at hc
  have hlast : (h.query (Fin.last N)).coeff N ≠ 0 := (mul_ne_zero_iff.mp hc).2
  have hall : ∀ (k : ℕ) (hk : k ≤ N), (h.query ⟨k, Nat.lt_succ_of_le hk⟩).coeff k ≠ 0 := by
    intro k hk
    apply Nat.decreasingInduction (motive := fun k hk =>
      (h.query ⟨k, Nat.lt_succ_of_le hk⟩).coeff k ≠ 0) ?_ hlast hk
    intro j hj ih
    have hr := h.query_succ_coeff j (by omega)
    rw [hr] at ih
    exact (mul_ne_zero_iff.mp ih).2
  exact hall s.val (by omega)

/-- Exact query degrees follow from terminal degree, with no sign restriction.
Use: the forward grading assertion of Theorem 2.1. -/
theorem query_degree_eq (h : bezout.History N) (hN : 0 < N)
    (hdeg : h.terminal.natDegree = N) (s : Fin N) :
    (h.query s).degree = (s.val : WithBot ℕ) := by
  cases N with
  | zero => omega
  | succ n =>
    exact degree_eq_of_le_of_coeff_ne_zero
      (degree_le_of_natDegree_le (h.query_natDegree_le s)) (h.query_top_coeff_ne_zero hdeg s)

/-- All immediate causal links are nonzero for a full-degree terminal.
Use: the maximal-path argument for exact response degrees in Theorem 2.1. -/
theorem subdiagonal_ne_zero (h : bezout.History (N + 1))
    (hdeg : h.terminal.natDegree = N + 1) (k : ℕ) (hk : k + 1 < N + 1) :
    h.a ⟨k + 1, hk⟩ ⟨k, by omega⟩ ≠ 0 := by
  have hn := h.query_top_coeff_ne_zero hdeg (⟨k + 1, hk⟩ : Fin (N + 1))
  rw [h.query_succ_coeff k hk] at hn
  exact neg_ne_zero.mp (mul_ne_zero_iff.mp hn).1

/-- The actual queries of a full-degree terminal form a normalized graded family.
Use: makes the forward and converse realization constructions inverse. -/
def normalizedQueries (h : bezout.History N) (hN : 0 < N)
    (hdeg : h.terminal.natDegree = N) : bezout.NormalizedFamily N where
  poly := h.query
  degree_eq := h.query_degree_eq hN hdeg
  eval_zero := h.query_eval_zero

/-- The final oracle answer has the constant physical response `-b_last`.
Use: initializes the maximal-degree response path. -/
theorem response_last (h : bezout.History (N + 1)) :
    h.response (Fin.last N) = -C (h.b (Fin.last N)) := by
  rw [h.response_recurrence]
  have hz : (∑ s : Fin (N + 1), if Fin.last N < s then
      C (h.a s (Fin.last N)) * h.response s else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro s _
    have hs : ¬Fin.last N < s := by exact not_lt.mpr (Fin.le_last s)
    simp [hs]
  rw [hz, mul_zero, sub_zero]

/-- The highest response coefficient can propagate only through the next call.
Use: the backwards counterpart of the maximal query-coefficient identity. -/
theorem response_top_coeff (h : bezout.History (N + 1)) (k : ℕ) (hk : k < N) :
    (h.response ⟨k, by omega⟩).coeff (N - k) =
      -h.a ⟨k + 1, by omega⟩ ⟨k, by omega⟩ *
        (h.response ⟨k + 1, by omega⟩).coeff (N - (k + 1)) := by
  rw [h.response_recurrence]
  rw [show N - k = (N - (k + 1)) + 1 by omega]
  simp only [coeff_sub, coeff_neg, coeff_C, Nat.succ_ne_zero, ite_false,
    neg_zero, zero_sub, coeff_X_mul, finsetSum_coeff]
  rw [neg_mul]
  apply congrArg Neg.neg
  calc
    _ = ∑ s : Fin (N + 1), if (⟨k, by omega⟩ : Fin (N + 1)) < s then
        h.a s ⟨k, by omega⟩ * (h.response s).coeff (N - (k + 1)) else 0 := by
      apply Finset.sum_congr rfl
      intro s _
      split_ifs <;> simp [coeff_C_mul]
    _ = _ := by
      rw [Finset.sum_eq_single (⟨k + 1, by omega⟩ : Fin (N + 1))]
      · simp
      · intro s _ hs
        by_cases hks : (⟨k, by omega⟩ : Fin (N + 1)) < s
        · have hsk : k + 1 < s.val := by
            have hne : s.val ≠ k + 1 := fun heq => hs (Fin.ext heq)
            change k < s.val at hks
            omega
          have hz : (h.response s).coeff (N - (k + 1)) = 0 :=
            coeff_eq_zero_of_natDegree_lt ((h.response_natDegree_le s).trans_lt (by
              have := s.isLt
              omega))
          simp [hks, hz]
        · simp [hks]
      · simp

/-- Every physical response has a nonzero maximal-degree coefficient.
Use: exact response grading for all full-degree causal histories. -/
theorem response_top_coeff_ne_zero (h : bezout.History (N + 1))
    (hdeg : h.terminal.natDegree = N + 1) (s : Fin (N + 1)) :
    (h.response s).coeff (N - s.val) ≠ 0 := by
  have hlast : (h.response (Fin.last N)).coeff (N - N) ≠ 0 := by
    rw [h.response_last]
    simpa only [Nat.sub_self, coeff_neg, coeff_C_zero, neg_ne_zero] using
      h.last_weight_ne_zero hdeg
  have hall : ∀ (k : ℕ) (hk : k ≤ N),
      (h.response ⟨k, Nat.lt_succ_of_le hk⟩).coeff (N - k) ≠ 0 := by
    intro k hk
    apply Nat.decreasingInduction (motive := fun k hk =>
      (h.response ⟨k, Nat.lt_succ_of_le hk⟩).coeff (N - k) ≠ 0) ?_ hlast hk
    intro j hj ih
    rw [h.response_top_coeff j hj]
    exact mul_ne_zero (neg_ne_zero.mpr (h.subdiagonal_ne_zero hdeg j (by omega))) ih
  exact hall s.val (by omega)

/-- Exact physical response degrees follow from a full-degree terminal.
Use: completes both degree assertions in Theorem 2.1. -/
theorem response_degree_eq (h : bezout.History N) (hN : 0 < N)
    (hdeg : h.terminal.natDegree = N) (s : Fin N) :
    (h.response s).degree = ((N - 1 - s.val : ℕ) : WithBot ℕ) := by
  cases N with
  | zero => omega
  | succ n =>
    apply degree_eq_of_le_of_coeff_ne_zero
      (degree_le_of_natDegree_le (h.response_natDegree_le s))
    simpa only [Nat.add_sub_cancel] using h.response_top_coeff_ne_zero hdeg s

end
end bezout.History
